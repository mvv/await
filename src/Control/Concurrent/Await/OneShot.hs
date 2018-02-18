{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Control.Concurrent.Await.OneShot (
    OneShot,
    newOneShot
  ) where

import Data.Functor.Identity
import Data.Inject
import Data.Heterogeneous.List
import Data.Capability
import Control.Applicative
import Control.Monad
import Control.Monad.Base
import Control.Monad.Trans.Class
import Control.Monad.Exception
import Control.Concurrent.STM.Lifted
import Control.Concurrent.STM.Hooks
import Control.Concurrent.STM.Rollback
import Control.Concurrent.STM.TWaitQueue (TWaitQueue)
import qualified Control.Concurrent.STM.TWaitQueue as TWQ
import Control.Concurrent.Event
import Control.Concurrent.Await

data SomeCE α = ∀ e . CompletableEvent e IO ⇒ SomeCE (e α)

newtype OneShot caps α = OneShot (TWaitQueue (SomeCE α) α)

instance Restrict1 OneShot where
  restrict1 (OneShot wq) = OneShot wq

newOneShot ∷ MonadBase IO μ ⇒ μ (OneShot (ReadCap :*: WriteCap) α)
newOneShot = OneShot <$> TWQ.emptyIO

instance Event (OneShot caps) where
  type EventResult (OneShot caps) = Identity

instance (MonadBase IO μ, ReadCap :∈: caps)
       ⇒ StatefulEvent (OneShot caps) μ where
  eventState (OneShot wq) = (Some . Identity <$>) <$> TWQ.resultIO wq

instance (MonadBase IO μ, ReadCap :∈: caps)
       ⇒ ResultfulEvent (OneShot caps) μ where
  eventResult (OneShot wq) = (Identity <$>) <$> TWQ.resultIO wq

instance (MonadBase IO μ, MonadMask μ, WriteCap :∈: caps)
       ⇒ CompletableEvent (OneShot caps) μ where
  complete (OneShot wq) v = mask_ $ (atomically $ TWQ.finish wq v) >>= \case
    Just evs → liftBase $ do
      forM_ evs $ \(SomeCE ev) → complete ev v
      return True
    Nothing → return False

instance (ReadCap :∈: caps) ⇒ WaitOp (OneShot caps α) where
  type WaitOpResult (OneShot caps α) = α
  registerWaitOp (OneShot wq) ev _ = atomicallyHR $ do
    TWQ.enqueue wq (SomeCE $ Inject ev Success) >>= \case
      Right key → do
        (rollbackUnless False =<<) $
          lift $ onEvent ev $ const $ atomically $ TWQ.delete wq key
        return True
      Left r → lift $ complete ev $ Success r
  pollWaitOp (OneShot wq) = TWQ.resultIO wq

