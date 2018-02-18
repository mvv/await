{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}

module Data.Lift (
    IdLift(..),
    Lift(..)
  ) where

data IdLift = IdLift

class Lift lift μ η | lift μ → η where 
  liftValue ∷ lift → η α → μ α

instance Lift IdLift μ μ where
  liftValue _ = id
  {-# INLINE liftValue #-}

