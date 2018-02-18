{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

module Data.Quantity (
    Measurable(..),
    QuantityUnit(..),
    QuantityScalar(..),
    Quantity(..),
    (:#),
    (#),
    fromUnit,
    toUnit,
    Milli(..),
    Micro(..),
    Nano(..),
    Pico(..),
    Kilo(..),
    Mega(..),
    Giga(..),
    Tera(..),
    Time(..),
    Second(..),
    Minute(..),
    Hour(..),
    Day(..),
    Week(..)
  ) where

import Data.Ratio
import Data.Word
import Data.Int
import Debug.Trace (trace)

class (Show (BaseUnit p), Measures (BaseUnit p) ~ p) ⇒ Measurable p where
  type BaseUnit p
  measurableAbbr ∷ p → String

instance Measurable () where
  type BaseUnit () = ()
  measurableAbbr _ = "1"

class Measurable (Measures u) ⇒ QuantityUnit u where
  type Measures u
  baseUnits ∷ Num n ⇒ u → (n, Int)
  unitAbbr  ∷ u → String

instance QuantityUnit () where
  type Measures () = ()
  baseUnits _ = (1, 0)
  unitAbbr  _ = "1"

class Num s ⇒ QuantityScalar s where
  -- | Specialized $(n / d) * 10 ^^ p$
  quantityPow10 ∷ s → s → Int → s
  showQuantity  ∷ Show s ⇒ s → String → String
  showQuantity s abbr = show s ++ " " ++ abbr

instance QuantityScalar Float where
  quantityPow10 n d p = (n * 10 ^^ p) / d
  {-# INLINE quantityPow10 #-}

instance QuantityScalar Double where
  quantityPow10 n d p = (n * 10 ^^ p) / d
  {-# INLINE quantityPow10 #-}

instance Integral n ⇒ QuantityScalar (Ratio n) where
  quantityPow10 n d p = (n * 10 ^^ p) / d
  {-# INLINE quantityPow10 #-}

instance QuantityScalar Integer where
  quantityPow10 n d 0         = n `quot` d
  quantityPow10 n d p | p > 0 = (n * 10 ^ p) `quot` d
  quantityPow10 n d p         = (n `quot` d) `quot` 10 ^ (-p) 
  {-# INLINE quantityPow10 #-}

instance QuantityScalar Int where
  quantityPow10 n d 0         = n `quot` d
  quantityPow10 n d p | p > 0 = (n * 10 ^ p) `quot` d
  quantityPow10 n d p         = (n `quot` d) `quot` 10 ^ (-p) 
  {-# INLINE quantityPow10 #-}

instance QuantityScalar Word where
  quantityPow10 n d 0         = n `quot` d
  quantityPow10 n d p | p > 0 = (n * 10 ^ p) `quot` d
  quantityPow10 n d p         = (n `quot` d) `quot` 10 ^ (-p) 
  {-# INLINE quantityPow10 #-}

{-
newtype Rebased u s = Rebased s
                      deriving (Eq, Ord, Bounded, Enum, Num, Real, Integral,
                                Fractional, Floating, RealFrac, RealFloat)

instance (QuantityUnit u, QuantityScalar s, Show s) ⇒ Show (Rebased u s) where
  show (Rebased s) = show s

instance (QuantityUnit u, QuantityScalar s) ⇒ QuantityScalar (Rebased u s) where
  quantityPow10 (Rebased n) (Rebased d) p =
      Rebased $ quantityPow10 n (d * unitN) (p - unitPow)
    where (unitN, unitPow) = baseUnits (undefined ∷ u)
  showQuantity (Rebased s) _ = show s ++ " " ++ unitAbbr (undefined ∷ u)
-}

infix 9 :#, #

newtype Quantity u s = Quantity { quantityScalar ∷ s }
                       deriving (Eq, Ord, Bounded, Enum)

type s :# u = Quantity u s

{-
(#) ∷ (QuantityScalar s, QuantityUnit u) ⇒ s → u → Quantity (Measures u) s
n # u = Quantity $ quantityPow10 (n * unitN) 1 unitPow
  where (unitN, unitPow) = baseUnits u

instance (Measurable p, QuantityUnit (BaseUnit p), QuantityScalar s, Show s)
       ⇒ Show (Quantity p s) where
  show (Quantity s) = showQuantity s (unitAbbr (undefined ∷ BaseUnit p))
-}

(#) ∷ (QuantityScalar s, QuantityUnit u) ⇒ s → u → s :# u
s # _ = Quantity s

instance (QuantityScalar s, QuantityUnit u) ⇒ Show (Quantity u s) where
  show (Quantity s) = show s ++ " " ++ unitAbbr (undefined ∷ u)

fromUnit ∷ ∀ s u u'
         . (QuantityScalar s, QuantityUnit u, QuantityUnit u',
            Measures u ~ Measures u')
         ⇒ s :# u → s :# u'
fromUnit (Quantity s) = Quantity $ quantityPow10 (s * n) n' (p - p')
  where (n,  p)  = baseUnits (undefined ∷ u)
        (n', p') = baseUnits (undefined ∷ u')
{-# INLINE fromUnit #-}

toUnit ∷ ∀ s u u'
       . (QuantityScalar s, QuantityUnit u, QuantityUnit u',
          Measures u ~ Measures u')
       ⇒ u' → s :# u → s :# u'
toUnit _ = fromUnit
{-# INLINE toUnit #-}

data Milli u = Milli u

instance QuantityUnit u ⇒ QuantityUnit (Milli u) where
  type Measures (Milli u) = Measures u
  baseUnits _ = let (n, p) = baseUnits (undefined ∷ u) in (n, p - 3)
  unitAbbr  _ = "m" ++ unitAbbr (undefined ∷ u)
  {-# INLINE baseUnits #-}

data Micro u = Micro u

instance QuantityUnit u ⇒ QuantityUnit (Micro u) where
  type Measures (Micro u) = Measures u
  baseUnits _ = let (n, p) = baseUnits (undefined ∷ u) in (n, p - 6)
  unitAbbr  _ = "μ" ++ unitAbbr (undefined ∷ u)
  {-# INLINE baseUnits #-}

data Nano u = Nano u

instance QuantityUnit u ⇒ QuantityUnit (Nano u) where
  type Measures (Nano u) = Measures u
  baseUnits _ = let (n, p) = baseUnits (undefined ∷ u) in (n, p - 9)
  unitAbbr  _ = "n" ++ unitAbbr (undefined ∷ u)
  {-# INLINE baseUnits #-}

data Pico u = Pico u

instance QuantityUnit u ⇒ QuantityUnit (Pico u) where
  type Measures (Pico u) = Measures u
  baseUnits _ = let (n, p) = baseUnits (undefined ∷ u) in (n, p - 12)
  unitAbbr  _ = "p" ++ unitAbbr (undefined ∷ u)
  {-# INLINE baseUnits #-}

data Kilo u = Kilo u

instance QuantityUnit u ⇒ QuantityUnit (Kilo u) where
  type Measures (Kilo u) = Measures u
  baseUnits _ = let (n, p) = baseUnits (undefined ∷ u) in (n, p + 3)
  unitAbbr  _ = "k" ++ unitAbbr (undefined ∷ u)
  {-# INLINE baseUnits #-}

data Mega u = Mega u

instance QuantityUnit u ⇒ QuantityUnit (Mega u) where
  type Measures (Mega u) = Measures u
  baseUnits _ = let (n, p) = baseUnits (undefined ∷ u) in (n, p + 6)
  unitAbbr  _ = "M" ++ unitAbbr (undefined ∷ u)
  {-# INLINE baseUnits #-}

data Giga u = Giga u

instance QuantityUnit u ⇒ QuantityUnit (Giga u) where
  type Measures (Giga u) = Measures u
  baseUnits _ = let (n, p) = baseUnits (undefined ∷ u) in (n, p + 9)
  unitAbbr  _ = "G" ++ unitAbbr (undefined ∷ u)
  {-# INLINE baseUnits #-}

data Tera u = Tera u

instance QuantityUnit u ⇒ QuantityUnit (Tera u) where
  type Measures (Tera u) = Measures u
  baseUnits _ = let (n, p) = baseUnits (undefined ∷ u) in (n, p + 12)
  unitAbbr  _ = "T" ++ unitAbbr (undefined ∷ u)
  {-# INLINE baseUnits #-}

data Time = Time

instance Measurable Time where
  type BaseUnit Time = Second

data Second = Second deriving (Eq, Show)

instance QuantityUnit Second where
  type Measures Second = Time
  baseUnits _ = (1, 0)
  unitAbbr  _ = "s"

data Minute = Minute deriving (Eq, Show)

instance QuantityUnit Minute where
  type Measures Minute = Time
  baseUnits _ = (6, 1)
  unitAbbr  _ = "min"

data Hour = Hour deriving (Eq, Show)

instance QuantityUnit Hour where
  type Measures Hour = Time
  baseUnits _ = (36, 2)
  unitAbbr  _ = "h"

data Day = Day deriving (Eq, Show)

instance QuantityUnit Day where
  type Measures Day = Time
  baseUnits _ = (864, 2)
  unitAbbr  _ = "d"

data Week = Week deriving (Eq, Show)

instance QuantityUnit Week where
  type Measures Week = Time
  baseUnits _ = (6048, 2)
  unitAbbr  _ = "w"

