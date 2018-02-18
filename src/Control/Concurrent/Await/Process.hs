{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE InterruptibleFFI #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Control.Concurrent.Await.Process (
    ProcCmd(..),
    ProcStream(..),
    ProcFlags,
    closeFdsProcFlag,
    ProcSpec(..),
    ProcHandle,
    procInPipe,
    procOutPipe,
    procErrPipe,
    command,
    shell,
    exec,
    runProcess,
    signalProcess,
    aioExec,
    syncExec,
    ExitedUnsuccessfully(..),
    exitedSuccessfully,
    aioExecSuccessfully,
    syncExecSuccessfully
  ) where

import Prelude hiding (ioError)
import Data.Typeable
import Data.Word (Word64)
import Data.Foldable (forM_)
import Data.Flags.TH (bitmaskWrapper)
import Data.Flags
import Data.Heterogeneous.List
import Data.Capability
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BS8
import Data.ByteString.Char8 ()
import Control.Applicative (pure, (<$>), (<*>))
import Control.Monad (void, when, unless)
import Control.Monad.Base
import Control.Monad.Abort (onError_)
import Control.Monad.Exception
import Control.Concurrent.MVar
import Control.Concurrent.Event
import Control.Concurrent.Await
import Control.Concurrent.Await.OneShot
import Foreign.Ptr (Ptr, nullPtr)
import Foreign.Storable (Storable, peek, poke)
import Foreign.C.Types (CInt(..))
import Foreign.C.String (CString, withCString)
import Foreign.C.Error (eBADF, errnoToIOError)
import Foreign.Marshal.Alloc (alloca)
import Foreign.Marshal.Array (withArray0)
import System.Posix.Types (Fd, CPid(..))
import System.Posix.Process (ProcessStatus(..), getAnyProcessStatus)
import System.Posix.Signals (Signal, sigCHLD, Handler(..), installHandler)
import qualified System.Posix.Signals as POSIX
import System.Posix.IO (stdInput, stdOutput, stdError)
import System.IO.Unsafe (unsafePerformIO)
import System.Exit (ExitCode(..))

#include <hs.await.process.h>

data ProcCmd = ShellCmd ByteString
             | FileCmd FilePath [ByteString]
             deriving (Eq, Show)

data ProcStream = IgnoreStream
                | InheritStream
                | PipeStream
                | UseStream Fd
                deriving (Eq, Show)

$(bitmaskWrapper "ProcFlags" ''CInt [''Storable]
    [("closeFdsProcFlag", 1)])

data ProcSpec = ProcSpec { procCmd   ∷ ProcCmd
                         , procEnv   ∷ Maybe [(ByteString, ByteString)]
                         , procCwd   ∷ Maybe FilePath
                         , procIn    ∷ ProcStream
                         , procOut   ∷ ProcStream
                         , procErr   ∷ ProcStream
                         , procFlags ∷ ProcFlags
                         }
                deriving (Eq, Show)

data ProcHandle = ProcHandle
                    { procPid     ∷ !CPid
                    , procSerial  ∷ !Word64
                    , procResult  ∷ !(OneShot (ReadCap :*: WriteCap)
                                              ProcessStatus)
                    , procInPipe  ∷ !(Maybe Fd)
                    , procOutPipe ∷ !(Maybe Fd)
                    , procErrPipe ∷ !(Maybe Fd)
                    }

instance Eq ProcHandle where
  ph == ph' = procSerial ph == procSerial ph'
  {-# INLINE (==) #-}

command ∷ ProcCmd → ProcSpec
command cmd = ProcSpec { procCmd   = cmd
                       , procEnv   = Nothing
                       , procCwd   = Nothing
                       , procIn    = InheritStream
                       , procOut   = InheritStream
                       , procErr   = InheritStream
                       , procFlags = noFlags
                       }

shell ∷ ByteString → ProcSpec
shell cmd = command $ ShellCmd cmd

exec ∷ FilePath → [ByteString] → ProcSpec
exec file args = command $ FileCmd file args

withMaybeCString ∷ Maybe String → (CString → IO α) → IO α
withMaybeCString Nothing  f = f nullPtr
withMaybeCString (Just s) f = withCString s f

withByteStrings ∷ [ByteString] → (Ptr CString → IO α) → IO α
withByteStrings bss f = go bss []
  where go []          ss = withArray0 nullPtr (reverse ss) f
        go (bs : bss') ss = BS.useAsCString bs $ \pStr → go bss' (pStr : ss)

withMaybeByteStrings ∷ Maybe [ByteString] → (Ptr CString → IO α) → IO α
withMaybeByteStrings Nothing  f = f nullPtr
withMaybeByteStrings (Just s) f = withByteStrings s f

withProcStream ∷ ProcStream → Fd → (Ptr Fd → IO α) → IO α
withProcStream IgnoreStream   _  f = f nullPtr
withProcStream InheritStream  fd f = alloca $ \pFd → poke pFd fd >> f pFd
withProcStream PipeStream     _  f = alloca $ \pFd → poke pFd (-1) >> f pFd
withProcStream (UseStream fd) _  f
  | fd >= 0   = alloca $ \pFd → poke pFd fd >> f pFd
  | otherwise = ioError $ errnoToIOError "runProcess" eBADF Nothing Nothing

fdFromPtr ∷ ProcStream → Ptr Fd → IO (Maybe Fd)
fdFromPtr PipeStream pFd | pFd /= nullPtr = Just <$> peek pFd
fdFromPtr _          _                    = return Nothing

execLock ∷ MVar Word64
execLock = unsafePerformIO $ newMVar 0
{-# NOINLINE execLock #-}

reapMap ∷ MVar (IntMap (Either ProcessStatus ProcHandle))
reapMap = unsafePerformIO $ newMVar IM.empty
{-# NOINLINE reapMap #-}

reap ∷ IO ()
reap = try (getAnyProcessStatus False False) >>= \case
  Left (_ ∷ SomeException) → return ()
  Right Nothing → return ()
  Right (Just (pid, ps)) → do
    mPH ← do
      let key = fromIntegral pid
      rm ← takeMVar reapMap
      case IM.lookup key rm of
        Just (Right ph) → do
          putMVar reapMap $! IM.delete key rm
          return $ Just $ ph
        _ → do
          putMVar reapMap $! IM.insert key (Left ps) rm
          return Nothing
    forM_ mPH $ \ph → complete (procResult ph) ps
    reap

runProcess ∷ MonadBase IO μ ⇒ ProcSpec → μ ProcHandle
runProcess (ProcSpec {..}) = liftBase $ do
    withByteStrings (BS8.pack cmd : args) $ \pArgv →
      withMaybeByteStrings env $ \pEnv →
        withMaybeCString procCwd $ \pCwd → mask_ $ do
          serial ← takeMVar execLock
          when (serial == 0) $
            void $ installHandler sigCHLD (Catch reap) Nothing
                     `onError_` putMVar execLock 0
          (`finally` (putMVar execLock $! (serial + 1))) $ do
            ph ← withProcStream procIn stdInput $ \pIn →
                   withProcStream procOut stdOutput $ \pOut →
                     withProcStream procErr stdError $ \pErr →
                       ProcHandle
                         <$> c_runProcess pArgv pEnv pCwd
                                          pIn pOut pErr procFlags
                         <*> pure serial
                         <*> newOneShot
                         <*> fdFromPtr procIn  pIn
                         <*> fdFromPtr procOut pOut
                         <*> fdFromPtr procErr pErr
            let key = fromIntegral $ procPid ph
            rm ← takeMVar reapMap
            case IM.lookup key rm of
              Just (Left ps) → do
                void $ complete (procResult ph) ps
                putMVar reapMap $! IM.delete key rm
              _ →
                putMVar reapMap $! IM.insert key (Right ph) rm
            return ph
  where
    (cmd, args) = case procCmd of
                    ShellCmd cmd'      → ("/bin/sh", ["-c", cmd']) 
                    FileCmd path args' → (path,        args')
    env = (<$> procEnv) $ fmap $ \(n, v) → BS.concat [n, "=", v]

signalProcess ∷ MonadBase IO μ ⇒ ProcHandle → Signal → μ Bool
signalProcess ph sig = liftBase $ pollWaitOp ph >>= \case
  Just _  → return False
  Nothing → withMVar reapMap $ \rm → do
    let pid = procPid ph
        key = fromIntegral pid
    case IM.lookup key rm of
      Just (Right ph') | procSerial ph' == procSerial ph → do
        POSIX.signalProcess sig pid
        return True
      _ → return False

instance WaitOp ProcHandle where
  type WaitOpResult ProcHandle = ProcessStatus
  registerWaitOp = registerWaitOp . procResult
  pollWaitOp = pollWaitOp . procResult

aioExec ∷ (MonadAIO s μ, MonadFinally μ) ⇒ ProcSpec → μ ProcessStatus
aioExec ps = bracketOnEscape (runProcess ps)
                             (`signalProcess` POSIX.sigKILL)
                             aioAwait

syncExec ∷ MonadBase IO μ ⇒ ProcSpec → μ ProcessStatus
syncExec ps = liftBase $ bracketOnEscape (runProcess ps)
                                         (`signalProcess` POSIX.sigKILL)
                                         await

data ExitedUnsuccessfully = ExitedUnsuccessfully ProcessStatus
                            deriving (Typeable, Eq, Show)

instance Exception ExitedUnsuccessfully

exitedSuccessfully ∷ ProcessStatus → Bool
exitedSuccessfully (Exited ExitSuccess) = True
exitedSuccessfully _                    = False

aioExecSuccessfully ∷ (MonadAIO s μ, MonadFinally μ) ⇒ ProcSpec → μ ()
aioExecSuccessfully ps = do
  r ← aioExec ps
  unless (exitedSuccessfully r) $
    liftBase $ throw $ ExitedUnsuccessfully r

syncExecSuccessfully ∷ MonadBase IO μ ⇒ ProcSpec → μ ()
syncExecSuccessfully ps = do
  r ← syncExec ps
  unless (exitedSuccessfully r) $
    liftBase $ throw $ ExitedUnsuccessfully r

foreign import ccall "hs_await_cbits_runProcess"
  c_runProcess ∷ Ptr CString → Ptr CString → CString
               → Ptr Fd → Ptr Fd → Ptr Fd
               → ProcFlags → IO CPid

