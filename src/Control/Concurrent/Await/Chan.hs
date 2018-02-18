{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DoAndIfThenElse #-}

module Control.Concurrent.Await.Chan (
    Chan,
    ReadChanOp(..),
    WriteChanOp(..),
    newChan,
    readChan,
    timedReadChan,
    writeChanAsync
  ) where

import Data.Inject
import Data.Heterogeneous.List
import Data.Capability
import Data.Timeout
import Control.Applicative
import Control.Monad
import Control.Monad.Base
import Control.Monad.Trans.Class
import Control.Concurrent.STM.Lifted
import Control.Concurrent.STM.Hooks
import Control.Concurrent.STM.Rollback
import Control.Concurrent.STM.TWaitQueue (TWaitQueue)
import qualified Control.Concurrent.STM.TWaitQueue as TWQ
import Control.Concurrent.Event
import Control.Concurrent.Await

data SomeCE α = ∀ e . CompletableEvent e (STMH IO) ⇒ SomeCE (e α)

data Chan caps α = Chan { chanReads  ∷ TWaitQueue (SomeCE α) ()
                        , chanWrites ∷ TWaitQueue (α, Maybe (SomeCE ())) ()
                        }

instance Show (Chan caps α) where
  show _ = "<<Chan>>"

instance Restrict1 Chan where
  restrict1 (Chan {..}) = Chan chanReads chanWrites

newChan ∷ MonadBase IO μ ⇒ μ (Chan (ReadCap :*: WriteCap) α)
newChan = Chan <$> TWQ.emptyIO <*> TWQ.emptyIO

data ReadChanOp α = ∀ caps . (ReadCap :∈: caps) ⇒ ReadChanOp (Chan caps α)

instance WaitOp (ReadChanOp α) where
  type WaitOpResult (ReadChanOp α) = α
  registerWaitOp (ReadChanOp (Chan {..})) re _ = atomicallyHR $ do
    add ← TWQ.nullOrFinished chanReads >>= \case
      True → go
        where go = TWQ.dequeue chanWrites >>= \case
                     Right (Just (e, Just (SomeCE we))) →
                       (lift $ complete we ()) >>= \case
                         True → do
                           (rollbackUnless False =<<) $
                             lift $ complete re $ Success e
                           return False
                         False → go
                     Right (Just (e, Nothing)) → do
                       (rollbackUnless False =<<) $
                         lift $ complete re $ Success e
                       return False
                     _ → return True
      False → return True
    when add $ do
      Right key ← TWQ.enqueue chanReads $ SomeCE $ Inject re Success
      (rollbackUnless False =<<) $
        lift $ onEvent re $ const $ atomically $ TWQ.delete chanReads key
    return True

readChan ∷ (ReadCap :∈: caps, MonadBase IO μ) ⇒ Chan caps α → μ α
readChan = await . ReadChanOp

timedReadChan ∷ (ReadCap :∈: caps, MonadBase IO μ)
              ⇒ Chan caps α → Timeout → μ (Maybe α)
timedReadChan c = timedAwait (ReadChanOp c)

data WriteChanOp α = ∀ caps . (WriteCap :∈: caps)
                   ⇒ WriteChanOp (Chan caps α) α

instance WaitOp (WriteChanOp α) where
  type WaitOpResult (WriteChanOp α) = ()
  registerWaitOp (WriteChanOp (Chan {..}) v) we _ = atomicallyHR $ do
    add ← TWQ.nullOrFinished chanWrites >>= \case
      True → go
        where go = TWQ.dequeue chanReads >>= \case
                     Right (Just (SomeCE re)) →
                       (lift $ complete re v) >>= \case
                         True → do
                           (rollbackUnless False =<<) $
                             lift $ complete we $ Success ()
                           return False
                         False → go
                     _ → return True
      False → return True
    when add $ do
      Right key ← TWQ.enqueue chanWrites (v, Just $ SomeCE $ Inject we Success)
      (rollbackUnless False =<<) $
        lift $ onEvent we $ const $ atomically $ TWQ.delete chanWrites key
    return True

writeChanAsync ∷ (WriteCap :∈: caps, MonadBase IO μ)
               ⇒ Chan caps α → α → μ ()
writeChanAsync (Chan {..}) v = liftBase $ atomicallyH $ go
  where go = TWQ.dequeue chanReads >>= \case
               Right (Just (SomeCE re)) → complete re v >>= \case
                 True  → return ()
                 False → go
               _ → void $ TWQ.enqueue chanWrites (v, Nothing)

{-
data CChan ω α = CChan { cChanReads  ∷ TWaitQueue (SomeCE (Either ω α)) ω
                       , cChanWrites ∷ TWaitQueue (α, Maybe (SomeCE Bool)) ω
                       }
-}


