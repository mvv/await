{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Control.Concurrent.STM.Rollback (
    STMRT,
    STMR,
    atomicallyRT,
    atomicallyR,
    rollback,
    rollbackIf,
    rollbackUnless,
  ) where

import Data.Typeable
import Data.Maybe (fromJust)
import Data.IORef
import Control.Applicative
import Control.Monad
import Control.Monad.Base
import Control.Monad.Trans.Class
import Control.Monad.Trans.Control
import Control.Monad.Trans.Finish
import Control.Monad.Abort (MonadRecover)
import Control.Monad.Exception (Exception, SomeException, handle)
import Control.Concurrent.STM.Lifted
import Control.Concurrent.STM (throwSTM)
import GHC.Conc (unsafeIOToSTM)

newtype STMRT r μ α = STMRT { unSTMRT ∷ FinishT r μ α }

type STMR r α = STMRT r STM α

instance Functor μ ⇒ Functor (STMRT r μ) where
  fmap f (STMRT m) = STMRT $ fmap f m

instance (Functor μ, Monad μ) ⇒ Applicative (STMRT r μ) where
  pure x = STMRT $ pure x
  (STMRT mf) <*> (STMRT ma) = STMRT $ mf <*> ma

instance (Functor μ, Monad μ) ⇒ Monad (STMRT r μ) where
  return x = STMRT $ return x
  (STMRT m) >>= f = STMRT $ m >>= unSTMRT . f

instance MonadTrans (STMRT r) where
  lift = STMRT . lift

instance MonadTransControl (STMRT r) where
  type StT (STMRT r) α = Either r α
  liftWith = defaultLiftWith STMRT unSTMRT
  restoreT = defaultRestoreT STMRT

instance MonadBase STM μ ⇒ MonadBase STM (STMRT r μ) where
  liftBase = STMRT . lift . liftBase
  {-# INLINE liftBase #-}

instance MonadBaseControl STM μ ⇒ MonadBaseControl STM (STMRT r μ) where
  type StM (STMRT r μ) α = ComposeSt (STMRT r) μ α
  liftBaseWith = defaultLiftBaseWith
  restoreM     = defaultRestoreM

data RollbackException = RollbackException deriving (Typeable, Show)

instance Exception RollbackException

atomicallyRT ∷ (AtomicIn μ ν, MonadRecover SomeException ν)
             ⇒ STMRT α μ α → ν α
atomicallyRT (STMRT m) = do
  rv ← liftBase $ newIORef Nothing
  handle (\(_ ∷ RollbackException) → liftBase $ fromJust <$> readIORef rv) $
    atomicallyIn $ runFinishT m >>= \case
      Left r → liftBase $ do
        unsafeIOToSTM $ writeIORef rv $ Just r
        throwSTM RollbackException
      Right r → return r

atomicallyR ∷ MonadBase IO μ ⇒ STMR α α → μ α
atomicallyR = liftBase . atomicallyRT

rollback ∷ Monad μ ⇒ r → STMRT r μ α
rollback = STMRT . finish

rollbackIf ∷ (Functor μ, Monad μ) ⇒ r → Bool → STMRT r μ ()
rollbackIf r True = rollback r
rollbackIf _ _    = return ()

rollbackUnless ∷ (Functor μ, Monad μ) ⇒ r → Bool → STMRT r μ ()
rollbackUnless r test = rollbackIf r $ not test

