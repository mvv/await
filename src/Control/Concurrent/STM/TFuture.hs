{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Concurrent.STM.TFuture (
    TSFuture,
    newTSFuture,
    newTSFutureIO,

    TCFuture,
    newTCFuture,
    newTCFutureIO,

    THFuture,
    newTHFuture,
    newTHFutureIO,
    
{-
    THCFuture,
    newTHCFuture,
    newTHCFutureIO
-}
  ) where

import Data.Functor.Identity
import Data.Timeout
import Control.Applicative
import Control.Monad
import Control.Monad.Base
import Control.Monad.Abort (MonadRecover(..))
import Control.Monad.Exception
import Control.Concurrent.Event
import Control.Concurrent.STM.Lifted
import Control.Concurrent.STM.Hooks

class ReadTVarImpl ν where
  readTVarImpl ∷ TVar α → ν α

instance ReadTVarImpl STM where
  readTVarImpl = readTVar

instance ReadTVarImpl IO where
  readTVarImpl = readTVarIO

class CompleteImpl ν where
  completeImpl ∷ TVar (Maybe α) → α → ν Bool

instance CompleteImpl STM where
  completeImpl tv v = readTVar tv >>= \case
    Nothing → writeTVar tv (Just v) >> return True
    _       → return False

instance CompleteImpl IO where
  completeImpl tv v = readTVarIO tv >>= \case
    Nothing → atomically $ readTVar tv >>= \case
      Nothing → writeTVar tv (Just v) >> return True
      _       → return False
    _       → return False

class MonadBase ν μ ⇒ HookCompleteImpl ν μ η where
  hookCompleteImpl ∷ TVar (Either [α → η ()] α) → α → μ Bool

instance (MonadRecover SomeException η, CommitHooksIn μ η)
         ⇒ HookCompleteImpl STM μ η where
  hookCompleteImpl tv v = readTVar tv >>= \case
    Left hooks → do
      writeTVar tv (Right v)
      onCommit $ forM_ (reverse hooks) $ \hook → recover (hook v) (const $ return ())
      return True
    _ → return False

instance (MonadBase IO μ, MonadRecover SomeException μ)
         ⇒ HookCompleteImpl IO μ μ where
  hookCompleteImpl tv v = readTVarIO tv >>= \case
    Left _ → do
      (hooks, result) ← atomically $ readTVar tv >>= \case
        (Left hooks) → writeTVar tv (Right v) >> return (hooks, True)
        _            → return ([], False)
      forM_ (reverse hooks) $ \hook → recover (hook v) (const $ return ())
      return result
    _ → return False

newtype TSFuture α = TSFuture (TVar (Maybe α))

newTSFuture ∷ MonadBase STM μ ⇒ μ (TSFuture α)
newTSFuture = TSFuture <$> newTVar Nothing

newTSFutureIO ∷ MonadBase IO μ ⇒ μ (TSFuture α)
newTSFutureIO = TSFuture <$> newTVarIO Nothing

instance Event TSFuture where
  type EventResult TSFuture = Identity

instance (Monad μ, MonadBase ν μ, ReadTVarImpl ν) ⇒ StatefulEvent TSFuture μ where
  eventState (TSFuture tv) = liftBase $ readTVarImpl tv >>= \case
    Nothing → return Nothing
    Just r  → return $ Just $ Some $ Identity r

instance (Monad μ, MonadBase ν μ, ReadTVarImpl ν) ⇒ ResultfulEvent TSFuture μ where
  eventResult (TSFuture tv) =
    liftBase $ (Identity <$>) <$> readTVarImpl tv

instance (Monad μ, MonadBase ν μ, CompleteImpl ν)
       ⇒ CompletableEvent TSFuture μ where
  complete (TSFuture tv) = liftBase . completeImpl tv

instance (Monad μ, MonadBase IO μ) ⇒ AwaitableEvent TSFuture μ where
  awaitEvent (TSFuture tv) = readTVarIO tv >>= \case
    Nothing → atomically $ readTVar tv >>= \case
      Nothing → retry
      Just r  → return $ Some $ Identity r
    Just r  → return $ Some $ Identity r

newtype TCFuture α = TCFuture (TVar (Maybe (MaybeCancelled α)))

newTCFuture ∷ MonadBase STM μ ⇒ μ (TCFuture α)
newTCFuture = TCFuture <$> newTVar Nothing

newTCFutureIO ∷ MonadBase IO μ ⇒ μ (TCFuture α)
newTCFutureIO = TCFuture <$> newTVarIO Nothing

instance Event TCFuture where
  type EventResult TCFuture = MaybeCancelled

instance (Monad μ, MonadBase ν μ, CompleteImpl ν) ⇒ CompletableEvent TCFuture μ where
  complete (TCFuture tv) = liftBase . completeImpl tv . NotCancelled

instance (Monad μ, MonadBase ν μ, CompleteImpl ν) ⇒ CancellableEvent TCFuture μ where
  cancel (TCFuture tv) = liftBase $ completeImpl tv Cancelled

instance (Monad μ, MonadBase ν μ, ReadTVarImpl ν) ⇒ StatefulEvent TCFuture μ where
  eventState (TCFuture tv) = liftBase $ readTVarImpl tv >>= \case
    Nothing → return Nothing
    Just r  → return $ Just $ Some r

instance (Monad μ, MonadBase ν μ, ReadTVarImpl ν) ⇒ ResultfulEvent TCFuture μ where
  eventResult (TCFuture tv) = liftBase $ readTVarImpl tv

instance (Monad μ, MonadBase IO μ) ⇒ AwaitableEvent TCFuture μ where
  awaitEvent (TCFuture tv) = liftBase $ readTVarIO tv >>= \case
    Nothing → atomically $ readTVar tv >>= \case
      Nothing → retry
      Just r  → return $ Some r
    Just r  → return $ Some r

newtype THFuture η α = THFuture (TVar (Either [α → η ()] α))

newTHFuture ∷ MonadBase STM μ ⇒ μ (THFuture η α)
newTHFuture = THFuture <$> newTVar (Left [])

newTHFutureIO ∷ MonadBase IO μ ⇒ μ (THFuture η α)
newTHFutureIO = THFuture <$> newTVarIO (Left [])

instance Event (THFuture η) where
  type EventResult (THFuture η) = Identity

instance (MonadBase ν μ, ReadTVarImpl ν) ⇒ StatefulEvent (THFuture η) μ where
  eventState (THFuture tv) = liftBase $ readTVarImpl tv >>= \case
    Left _  → return Nothing
    Right r → return $ Just $ Some $ Identity r

{-
instance MonadBase STM μ ⇒ StatefulEvent (THFuture η) μ where
  eventState (THFuture tv) = readTVar tv >>= \case
    Left _  → return Nothing
    Right r → return $ Just $ Some $ Identity r

instance MonadBase IO μ ⇒ StatefulEvent (THFuture η) μ where
  eventState (THFuture tv) = readTVarIO tv >>= \case
    Left _  → return Nothing
    Right r → return $ Just $ Some $ Identity r
-}

instance (MonadBase ν μ, HookCompleteImpl ν μ η)
       ⇒ CompletableEvent (THFuture η) μ where
  complete (THFuture tv) = hookCompleteImpl tv

{-
instance CommitHooksIn μ η ⇒ CompletableEvent (THFuture η) μ where
  complete (THFuture tv) v = readTVar tv >>= \
    (Left mHook) → do
      writeTVar tv (Right v)
      maybe (return ()) onCommit mHook
      return True
    (Right _)    → return False

instance MonadBase η IO ⇒ CompletableEvent (THFuture η) η where
  complete f@(THFuture tv) v = readTVarIO tv >>= \
    (Left mHook) → atomically $ complete f v
    (Right _)    → return False
-}

instance (MonadBase ν μ, ReadTVarImpl ν) ⇒ ResultfulEvent (THFuture η) μ where
  eventResult (THFuture tv) =
    liftBase $ either (const Nothing) (Just . Identity) <$> readTVarImpl tv

{-
instance MonadBase STM μ ⇒ ResultfulEvent (THFuture η) μ where
  eventResult (THFuture tv) = (Identity <$>) <$> readTVar tv

instance MonadBase IO μ ⇒ ResultfulEvent (THFuture η) μ where
  eventResult (THFuture tv) = (Identity <$>) <$> readTVarIO tv
-}

class MonadBase ν μ ⇒ CallbackImpl ν μ η where
  callbackImpl ∷ TVar (Either [α → η ()] α) → (α → η ()) → μ Bool

instance MonadBase STM μ ⇒ CallbackImpl STM μ η where
  callbackImpl tv cb = readTVar tv >>= \case
    Left hooks → do
      writeTVar tv $ Left (cb : hooks)
      return True
    _ → return False

instance MonadBase IO μ ⇒ CallbackImpl IO μ η where
  callbackImpl tv cb = readTVarIO tv >>= \case
    Left _ → atomically $ callbackImpl tv cb
    _      → return False

instance (Applicative η, Monad η) ⇒ HookEvent (THFuture η) where
  type EventHook (THFuture η) = η

instance (Applicative η, Monad η, MonadBase ν μ, CallbackImpl ν μ η)
         ⇒ StateHookEvent (THFuture η) μ where
  onEvent (THFuture tv) cb = callbackImpl tv (void . cb . Some . Identity)

instance MonadBase IO μ ⇒ AwaitableEvent (THFuture η) μ where
  awaitEvent (THFuture tv) = readTVarIO tv >>= \case
    Left _ → atomically $ readTVar tv >>= \case
      Left _  → retry
      Right r → return $ Some $ Identity r
    Right r → return $ Some $ Identity r

instance (Applicative μ, MonadBase IO μ)
         ⇒ TimedAwaitableEvent (THFuture η) μ where
  timedAwaitEvent (THFuture tv) tt = liftBase $ readTVarIO tv >>= \case
    Left _ | tt == instantly → return Nothing
    Left _ → do
      ttv ← registerDelay tt
      atomically $ readTVar tv >>= \case
        Left _ → readTVar ttv >>= \case
          True  → return Nothing
          False → retry
        Right r → return $ Just $ Some $ Identity r
    Right r → return $ Just $ Some $ Identity r

