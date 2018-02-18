{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Control.Concurrent.STM.Hooks (
    CommitHooksIn(..),
    STMH,
    atomicallyH,
    STMHR,
    atomicallyHR
  ) where

import Control.Applicative
import Control.Monad
import Control.Monad.Base
import Control.Monad.Trans.Class
import Control.Monad.Trans.Control
import Control.Monad.Trans.Reader
import Control.Monad.Exception
import Control.Monad.Abort (MonadAbort(..), MonadRecover(..))
import Control.Concurrent.STM.Lifted
import Control.Concurrent.STM.Rollback

class (MonadBase STM μ, MonadBase IO η) ⇒ CommitHooksIn μ η where
  onCommit ∷ η α → μ ()

newtype STMH η α = STMH { unSTMH ∷ (ReaderT (TVar [η ()]) STM α) }

instance Functor (STMH η) where
  fmap f (STMH m) = STMH $ fmap f m

instance Applicative (STMH η) where
  pure x = STMH $ pure x
  (STMH mf) <*> (STMH ma) = STMH $ mf <*> ma

instance Alternative (STMH η) where
  empty = retry
  (<|>) = orElse

instance Monad (STMH η) where
  return x = STMH $ return x
  (STMH m) >>= f = STMH $ m >>= unSTMH . f

instance MonadPlus (STMH η) where
  mzero = retry
  mplus = orElse

instance MonadBase STM (STMH η) where
  liftBase = STMH . lift
  {-# INLINE liftBase #-}

{-
instance MonadBaseControl STM (STMH η) where
  newtype StM (STMH η) α =
    StMSTMH { unStMSTMH ∷ StM (ReaderT (TVar [η ()]) STM) α }
  liftBaseWith f = STMH $ liftBaseWith $ \run' →
                     f (liftM StMSTMH . run' . unSTMH)
  restoreM       = STMH . restoreM . unStMSTMH
  -}

instance MonadBaseControl STM (STMH η) where
  type StM (STMH η) α = StM (ReaderT (TVar [η ()]) STM) α
  --liftBaseWith = defaultLiftBaseWith
  --restoreM     = defaultRestoreM

instance MonadAbort SomeException (STMH η) where
  abort = liftBase . abort

instance MonadBase IO μ ⇒ CommitHooksIn (STMH μ) μ where
  onCommit cb = STMH $ do
    cbsv ← ask
    cbs  ← readTVar cbsv
    writeTVar cbsv $ void cb : cbs

instance (MonadBase IO μ, MonadFinally μ) ⇒ AtomicIn (STMH μ) μ where
  atomicallyIn = atomicallyH

atomicallyH ∷ (MonadBase IO μ, MonadFinally μ) ⇒ STMH μ α → μ α
atomicallyH (STMH m) = do
  cbsv ← newTVarIO []
  (r, cbs) ← atomically $ (,) <$> runReaderT m cbsv <*> readTVar cbsv
  chainCleanups $ reverse cbs
  return r

type STMHR η r α = STMRT r (STMH η) α

atomicallyHR ∷ (MonadBase IO μ, MonadRecover SomeException μ, MonadFinally μ)
             ⇒ STMHR μ α α → μ α
atomicallyHR = atomicallyRT

