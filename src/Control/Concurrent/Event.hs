{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Control.Concurrent.Event where

import Data.Functor.Identity
import Data.Typeable
import Data.Maybe (fromJust)
import Data.Inject
import Data.Timeout
import Data.Heterogeneous.List
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)
import Control.Applicative

data Some f = ∀ α . Some { getSome ∷ f α }

class Functor r ⇒ Result r where
  resultValue ∷ r α → Maybe α

instance Result Identity where
  resultValue = Just . runIdentity

instance Result Maybe where
  resultValue = id

class Result (EventResult f) ⇒ Event (f ∷ ★ → ★) where
  type EventResult f ∷ ★ → ★

instance Event f ⇒ Event (Inject f) where
  type EventResult (Inject f) = EventResult f

instance Event f ⇒ Event (Eject f) where
  type EventResult (Eject f) = EventResult f

class (Event f, Applicative μ, Monad μ) ⇒ StatefulEvent f μ where
  eventState ∷ f α → μ (Maybe (Some (EventResult f)))

instance StatefulEvent f μ ⇒ StatefulEvent (Inject f) μ where
  eventState (Inject f _) = eventState f

instance StatefulEvent f μ ⇒ StatefulEvent (Eject f) μ where
  eventState (Eject f _) = eventState f

class (Event f, Applicative μ, Monad μ) ⇒ ResultfulEvent f μ where
  eventResult ∷ f α → μ (Maybe (EventResult f α))

instance ResultfulEvent f μ ⇒ ResultfulEvent (Eject f) μ where
  eventResult (Eject f ej) = ((ej <$>) <$>) <$> eventResult f

class (Event f, Applicative μ, Monad μ) ⇒ CompletableEvent f μ where
  complete ∷ f α → α → μ Bool

instance CompletableEvent f μ ⇒ CompletableEvent (Inject f) μ where
  complete (Inject f inj) = complete f . inj

class (Event f, Applicative μ, Monad μ) ⇒ CancellableEvent f μ where
  cancel ∷ f α → μ Bool

instance CancellableEvent f μ ⇒ CancellableEvent (Inject f) μ where
  cancel (Inject f _) = cancel f

instance CancellableEvent f μ ⇒ CancellableEvent (Eject f) μ where
  cancel (Eject f _) = cancel f

data MaybeCancelled α = Cancelled
                      | NotCancelled α
  deriving (Typeable, Eq, Show, Functor, Foldable, Traversable)

instance Result MaybeCancelled where
  resultValue Cancelled        = Nothing
  resultValue (NotCancelled a) = Just a

class (Event f, Applicative (EventHook f), Monad (EventHook f))
    ⇒ HookEvent f where
  type EventHook f ∷ ★ → ★

instance HookEvent f ⇒ HookEvent (Inject f) where
  type EventHook (Inject f) = EventHook f

instance HookEvent f ⇒ HookEvent (Eject f) where
  type EventHook (Eject f) = EventHook f

class (Applicative μ, Monad μ, HookEvent f) ⇒ StateHookEvent f μ where
  onEvent ∷ f α → (Some (EventResult f) → EventHook f β) → μ Bool

instance StateHookEvent f μ ⇒ StateHookEvent (Inject f) μ where
  onEvent (Inject f _) cb = onEvent f cb

instance StateHookEvent f μ ⇒ StateHookEvent (Eject f) μ where
  onEvent (Eject f _) cb = onEvent f cb

class HookEvent f ⇒ ResultHookEvent f μ where
  onEventResult ∷ f α → (EventResult f α → EventHook f β) → μ Bool

instance (Applicative μ, Monad μ, ResultHookEvent f μ)
       ⇒ ResultHookEvent (Eject f) μ where
  onEventResult (Eject f ej) cb = onEventResult f (cb . (ej <$>))

class (Event f, Applicative μ, Monad μ) ⇒ AwaitableEvent f μ where
  awaitEvent ∷ f α → μ (Some (EventResult f))

instance AwaitableEvent f μ ⇒ AwaitableEvent (Inject f) μ where
  awaitEvent (Inject f _) = awaitEvent f

instance AwaitableEvent f μ ⇒ AwaitableEvent (Eject f) μ where
  awaitEvent (Eject f _) = awaitEvent f

class (Event f, Applicative μ, Monad μ) ⇒ TimedAwaitableEvent f μ where
  timedAwaitEvent ∷ f α → Timeout → μ (Maybe (Some (EventResult f)))

instance TimedAwaitableEvent f μ ⇒ TimedAwaitableEvent (Inject f) μ where
  timedAwaitEvent (Inject f _) tt = timedAwaitEvent f tt

instance TimedAwaitableEvent f μ ⇒ TimedAwaitableEvent (Eject f) μ where
  timedAwaitEvent (Eject f _) tt = timedAwaitEvent f tt

eventIdResult ∷ (ResultfulEvent f μ, EventResult f ~ Identity)
              ⇒ f α → μ (Maybe α)
eventIdResult f = fmap runIdentity <$> eventResult f
{-# INLINABLE eventIdResult #-}

awaitResult ∷ (ResultfulEvent f μ, AwaitableEvent f μ)
            ⇒ f α → μ (EventResult f α)
awaitResult f = awaitEvent f >> fromJust <$> eventResult f
{-# INLINABLE awaitResult #-}

timedAwaitResult ∷ (ResultfulEvent f μ, TimedAwaitableEvent f μ)
                 ⇒ f α → Timeout → μ (Maybe (EventResult f α))
timedAwaitResult f tt = timedAwaitEvent f tt >> eventResult f
{-# INLINABLE timedAwaitResult #-}

awaitIdResult ∷ (ResultfulEvent f μ, AwaitableEvent f μ,
                 EventResult f ~ Identity)
              ⇒ f α → μ α
awaitIdResult f = runIdentity <$> awaitResult f
{-# INLINABLE awaitIdResult #-}

timedAwaitIdResult ∷ (ResultfulEvent f μ, TimedAwaitableEvent f μ,
                      EventResult f ~ Identity)
                   ⇒ f α → Timeout → μ (Maybe α)
timedAwaitIdResult f tt = fmap runIdentity <$> timedAwaitResult f tt
{-# INLINABLE timedAwaitIdResult #-}

data family EventRepr cap (r ∷ ★ → ★) α

data StatefulCap (μ ∷ ★ → ★)
data ResultfulCap (μ ∷ ★ → ★)

data instance EventRepr (StatefulCap μ) r α =
  ∀ f . (Result r, EventResult f ~ r, StatefulEvent f μ) ⇒ StatefulRepr (f α)
data instance EventRepr (ResultfulCap μ) r α =
  ∀ f . (Result r, EventResult f ~ r, ResultfulEvent f μ) ⇒ ResultfulRepr (f α)

data EventReprs caps r α where
  EventRepr  ∷ EventRepr cap r α → EventReprs (HSingle cap) r α
  EventReprs ∷ EventRepr cap r α → EventReprs caps r α
             → EventReprs (cap :* caps) r α

getRepr ∷ ∀ cap caps r α . (cap :∈: caps)
        ⇒ EventReprs caps r α → EventRepr cap r α
getRepr (EventRepr repr) =
  case hMembershipWitness ∷ HMembershipWitness cap caps of
    HHeadMember → repr
    _           → undefined
getRepr (EventReprs repr tailReprs) =
  case hMembershipWitness ∷ HMembershipWitness cap caps of
    HHeadMember   → repr
    HTailMember _ → getRepr tailReprs

newtype SomeEvent caps r α = SomeEvent (EventReprs caps r α)

instance Result r ⇒ Event (SomeEvent caps r) where
  type EventResult (SomeEvent caps r) = r

instance (Applicative μ, Monad μ, Result r, StatefulCap μ :∈: caps)
       ⇒ StatefulEvent (SomeEvent caps r) μ where
  eventState = go 
    where go ∷ ∀ α . SomeEvent caps r α → μ (Maybe (Some r))
          go (SomeEvent reprs) =
            case getRepr reprs ∷ EventRepr (StatefulCap μ) r α of
              StatefulRepr f → eventState f

instance (Applicative μ, Monad μ, Result r, ResultfulCap μ :∈: caps)
       ⇒ ResultfulEvent (SomeEvent caps r) μ where
  eventResult = go 
    where go ∷ ∀ α . SomeEvent caps r α → μ (Maybe (r α))
          go (SomeEvent reprs) =
            case getRepr reprs ∷ EventRepr (ResultfulCap μ) r α of
              ResultfulRepr f → eventResult f

