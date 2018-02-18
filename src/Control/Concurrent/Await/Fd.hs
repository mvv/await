{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

module Control.Concurrent.Await.Fd (
    ReadFd(..),
    WriteFd(..)
  ) where

import Control.Monad (void, unless)
import Control.Concurrent.Event
import Control.Concurrent.Await
import System.Posix.Types (Fd)
import qualified GHC.Event as GE

newtype ReadFd  = ReadFd Fd  deriving (Eq, Show)
newtype WriteFd = WriteFd Fd deriving (Eq, Show)

registerFd ∷ (EventHook e ~ IO, StatefulEvent e IO, CompletableEvent e IO,
              StateHookEvent e IO)
           ⇒ Fd → GE.Event → e (Attempt ()) → IO Bool
registerFd fd evt ev = do
  Just em ← GE.getSystemEventManager
  let cb key _ = do
        void $ GE.unregisterFd_ em key
        void $ complete ev $ Success ()
  key ← GE.registerFd em cb fd evt GE.MultiShot
  r ← onEvent ev $ const $ GE.unregisterFd_ em key
  unless r $ void $ GE.unregisterFd_ em key
  return r

instance WaitOp ReadFd where
  type WaitOpResult ReadFd = ()
  registerWaitOp (ReadFd fd) ev _ = registerFd fd GE.evtRead ev

instance WaitOp WriteFd where
  type WaitOpResult WriteFd = ()
  registerWaitOp (WriteFd fd) ev _ = registerFd fd GE.evtWrite ev

