{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Control.Concurrent.Await.Thread (
    ThreadGroup,
    newThreadGroup,
    shutdownThreadGroup,

    UnpooledForkError(..),
    Thread,
    threadId,
    threadGroup,
    spawnThread,
    forkThread,

    StopThread(..),
    stopThread
  ) where

import Data.Typeable
import Data.Map (Map)
import qualified Data.Map as M
import Data.Heterogeneous.List
import Data.Capability
import Control.Applicative
import Control.Monad
import Control.Monad.Base
import Control.Monad.Exception
import Control.Concurrent
import Control.Concurrent.Event
import Control.Concurrent.Await
import Control.Concurrent.Await.OneShot
import System.IO.Unsafe (unsafePerformIO)
import Internal.Control

data ThreadGroup =
  ThreadGroup { tgShutdown ∷ !(OneShot (ReadCap :*: WriteCap) ())
              , tgThreads  ∷ !(MVar Int)
              }

newThreadGroup ∷ MonadBase IO μ ⇒ μ ThreadGroup
newThreadGroup = liftBase $ ThreadGroup <$> newOneShot <*> newMVar 1

shutdownThreadGroup ∷ MonadBase IO μ ⇒ ThreadGroup → μ Bool
shutdownThreadGroup (ThreadGroup {..}) = liftBase $ mask_ $ do
  n ← takeMVar tgThreads
  let !n' | n <= 0    = n
          | n == 1    = 0
          | otherwise = -n + 1
  putMVar tgThreads n'
  when (n == 1) $ void $ complete tgShutdown ()
  return $ n' == 0

instance WaitOp ThreadGroup where
  type WaitOpResult ThreadGroup = ()
  registerWaitOp = registerWaitOp . tgShutdown
  pollWaitOp = pollWaitOp . tgShutdown

tgMapV ∷ MVar (Map ThreadId ThreadGroup)
tgMapV = unsafePerformIO $ newMVar M.empty
{-# NOINLINE tgMapV #-}

data Thread α = Thread { thId     ∷ !ThreadId
                       , thGroup  ∷ !ThreadGroup
                       , thResult ∷ !(OneShot (ReadCap :*: WriteCap)
                                              (Attempt α))
                       }

threadId ∷ Thread α → ThreadId
threadId = thId 

threadGroup ∷ Thread α → ThreadGroup
threadGroup = thGroup

data UnpooledForkError = UnpooledForkError deriving (Show, Typeable)

instance Exception UnpooledForkError

spawnThread' ∷ ThreadGroup → IO α → IO (Thread α)
spawnThread' tg@(ThreadGroup {..}) io = do
  resultEv ← newOneShot
  childId  ← forkIO $ do
    childId ← myThreadId
    updateMVar_' tgMapV $ M.insert childId tg
    result  ← catch (Success <$> io)
                    (\(e ∷ SomeException) → return $ Failure e)
    updateMVar_' tgMapV $ M.delete childId
    void $ complete resultEv $ result
    n ← takeMVar tgThreads
    let !n' | n > 0     = n - 1
            | otherwise = n + 1
    putMVar tgThreads n'
    when (n == -1) $ void $ complete tgShutdown ()
  return $ Thread childId tg resultEv

spawnThread ∷ MonadBase IO μ ⇒ ThreadGroup → IO α → μ (Maybe (Thread α))
spawnThread tg@(ThreadGroup {tgThreads}) io = liftBase $ mask $ \restore → do
  n ← takeMVar tgThreads
  if n <= 0 then do
    putMVar tgThreads n
    return Nothing
  else do
    putMVar tgThreads $! n + 1
    Just <$> spawnThread' tg (restore io)

forkThread ∷ MonadBase IO μ ⇒ IO α → μ (Thread α)
forkThread io = liftBase $ do
  parentId ← myThreadId
  tgm      ← readMVar tgMapV
  case M.lookup parentId tgm of
    Just tg@(ThreadGroup {tgThreads}) → mask $ \restore → do
      n ← takeMVar tgThreads
      putMVar tgThreads $! if n > 0 then n + 1 else n - 1
      spawnThread' tg (restore io)
    Nothing →
      throw UnpooledForkError

instance WaitOp (Thread α) where
  type WaitOpResult (Thread α) = Attempt α
  registerWaitOp (Thread {thResult}) e = registerWaitOp thResult e
  pollWaitOp (Thread {thResult}) = pollWaitOp thResult

data StopThread s α = ∀ caps . (WriteCap :∈: caps)
                    ⇒ StopThread (Thread α) (OneShot caps s)

instance WaitOp (StopThread s α) where
  type WaitOpResult (StopThread s α) = Attempt α
  registerWaitOp (StopThread t _) e = registerWaitOp t e
  pollWaitOp (StopThread t _) = pollWaitOp t

stopThread ∷ (MonadBase IO μ, MonadMask μ) ⇒ StopThread s α → s → μ Bool
stopThread (StopThread _ sh) s = complete sh s

