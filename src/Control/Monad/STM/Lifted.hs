{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Monad.STM.Lifted (
    STM,
    AtomicIn(..),
    atomically,
    always,
    alwaysSucceeds,
    retry,
    orElse
  ) where

import Control.Monad.Base
import Control.Monad.Trans.Control
import Control.Monad.Abort
import Control.Exception
import Control.Monad.STM (STM)
import qualified Control.Monad.STM as STM
import GHC.Prim (getMaskingState#,
                 maskAsyncExceptions#, unmaskAsyncExceptions#)

instance MonadAbort SomeException STM where
  abort = STM.throwSTM

instance MonadRecover SomeException STM where
  recover = STM.catchSTM

class (MonadBase STM μ, MonadBase IO η) ⇒ AtomicIn μ η where
  atomicallyIn ∷ μ α → η α

instance MonadBase IO η ⇒ AtomicIn STM η where
  atomicallyIn = atomically

atomically ∷ MonadBase IO μ ⇒ STM α → μ α
atomically = liftBase . STM.atomically

always ∷ MonadBase STM μ ⇒ STM Bool → μ ()
always = liftBase . STM.always
{-# INLINE always #-}

alwaysSucceeds ∷ MonadBase STM μ ⇒ STM α → μ ()
alwaysSucceeds = liftBase . STM.alwaysSucceeds
{-# INLINE alwaysSucceeds #-}

retry ∷ MonadBase STM μ ⇒ μ α
retry = liftBase STM.retry
{-# INLINE retry #-}

orElse ∷ MonadBaseControl STM μ ⇒ μ α → μ α → μ α
orElse m1 m2 = control $ \runInSTM → runInSTM m1 `STM.orElse` runInSTM m2
{-# INLINE orElse #-}

