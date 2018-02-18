{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

module Control.Concurrent.Await.Socket (
    SocketOp(..),
  ) where

import Data.Monoid (mconcat)
import Data.Flags (noFlags, enumFlags)
import Control.Applicative ((<$>))
import Control.Monad (void, unless)
import Control.Concurrent.Event
import Control.Concurrent.Await
import qualified GHC.Event as GE
import System.Posix.Socket

data SocketOp f = SocketOp (Socket f) SockOps

registerFd ∷ (EventHook e ~ IO, StatefulEvent e IO, CompletableEvent e IO,
              StateHookEvent e IO)
           ⇒ Socket f → [GE.Event] → e (Attempt (Socket f)) → IO Bool
registerFd sk evts ev = do
  Just em ← GE.getSystemEventManager
  let cb key _ = do
        void $ GE.unregisterFd_ em key
        void $ complete ev $ Success sk
  key ← withSocketFd sk $ \fd → GE.registerFd em cb fd (mconcat evts) GE.MultiShot
  r ← onEvent ev $ const $ GE.unregisterFd_ em key
  unless r $ void $ GE.unregisterFd_ em key
  return r

instance WaitOp (SocketOp f) where
  type WaitOpResult (SocketOp f) = Socket f
  registerWaitOp (SocketOp sk ops) ev _ =
      if ops == noFlags
        then return True
        else registerFd sk (f <$> enumFlags ops) ev
    where
      f op = if op == SendSockOps then GE.evtWrite else GE.evtRead

