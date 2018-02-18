{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ExistentialQuantification #-}

module Data.Inject (
    Inject(..),
    inject,
    Eject(..),
    eject
  ) where

import Data.Functor.Contravariant

data Inject f α = ∀ β . Inject (f β) (α → β)

inject ∷ f α → Inject f α
inject c = Inject c id

instance Contravariant (Inject f) where
  contramap f (Inject c g) = Inject c (g . f)

data Eject f α = ∀ β . Eject (f β) (β → α)

eject ∷ f α → Eject f α
eject c = Eject c id

instance Functor (Eject f) where
  fmap f (Eject c g) = Eject c (f . g)

