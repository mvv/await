{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
--{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}

module Data.Peano where

import Data.Typeable
import Data.Constraint (Constraint, Dict(..))

{-
data Peano = PZero | PSucc Peano deriving Typeable

pInd ∷ ∀ (c ∷ Peano → Constraint) (m ∷ Peano)
     . Dict (c PZero)
     → (∀ (n ∷ Peano) . Dict (c n) → Dict (c (PSucc n)))
     → Dict (c m)
pInd base step = undefined
-}

data PZero deriving Typeable
data PSucc p deriving Typeable

data Peano n where
  PZero ∷ Peano PZero
  PSucc ∷ IsPeano p ⇒ Peano p → Peano (PSucc p)

instance Show (Peano n) where
  show n = show (peanoNum n ∷ Int)

pZero ∷ Peano n → Bool
pZero PZero = True
pZero _     = False

peanoNum ∷ Num n ⇒ Peano p → n
peanoNum PZero     = 0
peanoNum (PSucc p) = 1 + peanoNum p

class Typeable n ⇒ IsPeano n where
  peano ∷ Peano n

instance IsPeano PZero where
  peano = PZero

instance IsPeano p ⇒ IsPeano (PSucc p) where
  peano = PSucc peano

type P0 = PZero
type P1 = PSucc P0
type P2 = PSucc P1
type P3 = PSucc P2
type P4 = PSucc P3
type P5 = PSucc P4
type P6 = PSucc P5
type P7 = PSucc P6
type P8 = PSucc P7
type P9 = PSucc P8

peano0 ∷ Peano P0
peano0 = peano
peano1 ∷ Peano P1
peano1 = peano
peano2 ∷ Peano P2
peano2 = peano
peano3 ∷ Peano P3
peano3 = peano
peano4 ∷ Peano P4
peano4 = peano
peano5 ∷ Peano P5
peano5 = peano
peano6 ∷ Peano P6
peano6 = peano
peano7 ∷ Peano P7
peano7 = peano
peano8 ∷ Peano P8
peano8 = peano
peano9 ∷ Peano P9
peano9 = peano

class (IsPeano (PPred n), n ~ PSucc (PPred n)) ⇒ PHasPred n where
  type PPred n

instance IsPeano p ⇒ PHasPred (PSucc p) where
  type PPred (PSucc p) = p

pPred ∷ Peano (PSucc p) → Peano p
pPred (PSucc p) = p

{-

data PAddWitness n m where
  PAddZeroZero ∷ PAddWitness PZero PZero
  PAddZeroSucc ∷ (PAdd p PZero, PAdd PZero p, (p :+: PZero) ~ p)
               ⇒ PAddWitness PZero (PSucc p)
  PAddSuccZero ∷ (PAdd p PZero, PAdd PZero p, (p :+: PZero) ~ p)
               ⇒ PAddWitness (PSucc p) PZero
  PAddSuccSucc ∷ (PAdd n m, PAdd m n, PAdd (PSucc n) m, PAdd m (PSucc n),
                  PAdd n (PSucc m), PAdd (PSucc m) n)
               ⇒ PAddWitness (PSucc n) (PSucc m)

infixl 6 :+:

class (IsPeano n, IsPeano m, IsPeano (n :+: m), (n :+: m) ~ (m :+: n))
      ⇒ PAdd n m where
  type n :+: m
  pAddWitness ∷ PAddWitness n m

instance PAdd PZero PZero where
  type PZero :+: PZero = PZero
  pAddWitness = PAddZeroZero

instance (PAdd p PZero, PAdd PZero p, (p :+: PZero) ~ p) ⇒ PAdd PZero (PSucc p) where
  type PZero :+: PSucc p = PSucc p
  pAddWitness = PAddZeroSucc

instance (PAdd p PZero, PAdd PZero p, (p :+: PZero) ~ p) ⇒ PAdd (PSucc p) PZero where
  type PSucc p :+: PZero = PSucc p
  pAddWitness = PAddSuccZero

instance (PAdd n m, PAdd m n,
          PAdd (PSucc n) m, PAdd m (PSucc n),
          PAdd n (PSucc m), PAdd (PSucc m) n)
         ⇒ PAdd (PSucc n) (PSucc m) where
  type PSucc n :+: PSucc m = PSucc (PSucc (n :+: m))
  pAddWitness = PAddSuccSucc

type PAddResultC n m r = (PAdd n m, PAdd m n, (n :+: m) ~ r)
type PAddResult n m r = Dict (PAddResultC n m r)
type PAddZero1 n = PAddResult PZero n n
type PAddZero2 n = PAddResult n PZero n

pAddZero1 ∷ ∀ p . PAdd PZero p ⇒ PAddZero1 (PSucc p)
pAddZero1 = case pAddWitness ∷ PAddWitness PZero p of
  PAddZeroZero → Dict
  PAddZeroSucc → Dict

pAddZero2 ∷ ∀ p . PAdd p PZero ⇒ PAddZero2 (PSucc p)
pAddZero2 = case pAddWitness ∷ PAddWitness p PZero of
  PAddZeroZero → Dict
  PAddSuccZero → Dict

pAddPred1 ∷ ∀ n m . PAdd (PSucc n) m ⇒ Dict (PAdd n m)
pAddPred1 = case pAddWitness ∷ PAddWitness (PSucc n) m of
  PAddSuccZero → Dict
  PAddSuccSucc → Dict

pAddPred2 ∷ ∀ n m . PAdd n (PSucc m) ⇒ Dict (PAdd n m)
pAddPred2 = case pAddWitness ∷ PAddWitness n (PSucc m) of
  PAddZeroSucc → Dict
  PAddSuccSucc → Dict

pAddSucc1 ∷ ∀ n m . (PAdd n m, PAdd m n) ⇒ PAddResult (PSucc n) m (PSucc (n :+: m))
pAddSucc1 = case pAddWitness ∷ PAddWitness n m of
  PAddZeroZero → Dict
  PAddZeroSucc → case pAddZero2 ∷ PAddZero2 m of
    Dict → Dict
-}

{-
type PAddZero n = PAddResult n PZero n

pAddZero ∷ ∀ n . IsPeano n ⇒ PAddZero n
pAddZero = case peano ∷ Peano n of
-}

{-
type PAdd1C n = (PAdd n n, PAdd n PZero, PAdd PZero n, (n :+: PZero) ~ n)
type PAdd1 n = Dict (PAdd1C n)

pAdd1 ∷ ∀ n . IsPeano n ⇒ PAdd1 n
pAdd1 = case peano ∷ Peano n of
  PZero   → Dict
  PSucc _ → case pAdd1 ∷ PAdd1 (PPred n) of
    Dict → Dict

type PAdd2C n m = (PAdd1C n, PAdd1C m, PAdd1C (n :+: m),
                   PAdd1C (PSucc n), PAdd1C (PSucc m),
                   PAdd n m, PAdd m n,
                   PAdd (PSucc n) m, PAdd m (PSucc n),
                   PAdd n (PSucc m), PAdd (PSucc m) n,
                   PAdd (PSucc n) (PSucc m), PAdd (PSucc m) (PSucc m),
                   (PSucc n :+: m) ~ PSucc (n :+: m),
                   (n :+: PSucc m) ~ PSucc (n :+: m))
type PAdd2 n m = Dict (PAdd2C n m)

pAdd2 ∷ ∀ n m . (IsPeano n, IsPeano m) ⇒ PAdd2 n m
pAdd2 = case (peano ∷ Peano n, peano ∷ Peano m) of
  (PZero,   PZero)   → Dict
  (PZero,   PSucc _) → case pAdd1 ∷ PAdd1 (PPred m) of
    Dict → Dict
  (PSucc _, PZero)   → case pAdd1 ∷ PAdd1 (PPred n) of
    Dict → Dict
  (PSucc _, PSucc _) → case pAdd2 ∷ PAdd2 (PPred n) (PPred m) of
    Dict → Dict

{-
type PAdd2 n m = Dict (PAdd n m, PAdd m n)

pAdd2 ∷ ∀ n m . (IsPeano n, IsPeano m) ⇒ PAdd2 n m
pAdd2 = case (peano ∷ Peano n, peano ∷ Peano m) of
  (PZero,   PZero)   → Dict
  (PZero,   PSucc _) → Dict
  (PSucc _, PZero)   → Dict
  (PSucc _, PSucc _) → case pAdd2 ∷ PAdd2 (PPred n) (PPred m) of
    Dict → Dict
-}

{-
type PAdd3C n m k =
  (PAdd2C n m, PAdd2C m k, PAdd2C n k,
   PAdd2C (n :+: m) k, PAdd2C k (m :+: n),
   PAdd2C n (m :+: k), PAdd2C (m :+: k) n,
   PAdd2C (n :+: k) m, PAdd2C m (n :+: k),
   ((n :+: m) :+: k) ~ (n :+: (m :+: k)),
   (m :+: (n :+: k)) ~ ((m :+: n) :+: k))
type PAdd3 n m k = Dict (PAdd3C n m k)

pAdd3 ∷ ∀ n m k . (IsPeano n, IsPeano m, IsPeano k) ⇒ PAdd3 n m k
pAdd3 = case (peano ∷ Peano n, peano ∷ Peano m, peano ∷ Peano k) of
  (PZero,   PZero,   PZero)   → Dict
  (PZero,   PZero,   PSucc _) → case pAdd1 ∷ PAdd1 (PPred k) of
    Dict → Dict
  (PZero,   PSucc _, PZero)   → case pAdd1 ∷ PAdd1 (PPred m) of
    Dict → Dict
  (PSucc _, PZero,   PZero)   → case pAdd1 ∷ PAdd1 (PPred n) of
    Dict → Dict
  (PZero,   PSucc _, PSucc _) → case pAdd2 ∷ PAdd2 (PPred m) (PPred k) of
      Dict → Dict
  (PSucc _, PZero,   PSucc _) → case pAdd2 ∷ PAdd2 (PPred n) (PPred k) of
      Dict → Dict
  (PSucc _, PSucc _, PZero)   → case pAdd2 ∷ PAdd2 (PPred n) (PPred m) of
      Dict → Dict
  (PSucc _, PSucc _, PSucc _) → 
    case pAdd3 ∷ PAdd3 (PPred n) (PPred m) (PPred k) of
{-
      Dict → case pAdd2 ∷ PAdd2 (PSucc (PPred n :+: PPred m)) (PPred k) of
        Dict → case pAdd2 ∷ PAdd2 (PSucc (PPred n :+: PPred k)) (PPred m) of
          Dict → case pAdd2 ∷ PAdd2 (PSucc (PPred m :+: PPred k)) (PPred n) of 
-}
            Dict → Dict
-}

data PLeqWitness n m where
  PLeqZero ∷ IsPeano m ⇒ PLeqWitness PZero m
  PLeqSucc ∷ (n :≤: m) ⇒ PLeqWitness (PSucc n) (PSucc m)

infixl 6 :-:

class (IsPeano n, IsPeano m, IsPeano (m :-: n)) ⇒ n :≤: m where
  type m :-: n
  pLeqWitness ∷ PLeqWitness n m

instance IsPeano n ⇒ PZero :≤: n where
  type n :-: PZero = n
  pLeqWitness = PLeqZero

instance (n :≤: m) ⇒ PSucc n :≤: PSucc m where
  type PSucc m :-: PSucc n = m :-: n
  pLeqWitness = PLeqSucc

type n :≥: m = m :≤: n

type PSubResult m n r = Dict (n :≤: m, (m :-: n) ~ r)

pLeqAntisymm ∷ ∀ n m . (n :≤: m, m :≤: n) ⇒ Dict (n ~ m)
pLeqAntisymm = case (pLeqWitness ∷ PLeqWitness n m,
                     pLeqWitness ∷ PLeqWitness m n) of
  (PLeqZero, PLeqZero) → Dict
  (PLeqSucc, PLeqSucc) → case pLeqAntisymm ∷ Dict (PPred n ~ PPred m) of
    Dict → Dict
  _ → undefined

pAddDiff ∷ ∀ n m . (n :≤: m) ⇒ PAddResult (m :-: n) n m
pAddDiff = case pLeqWitness ∷ PLeqWitness n m of
  PLeqZero → case peano ∷ Peano m of
    PZero   → Dict
    PSucc _ → Dict
  PLeqSucc → case pAddDiff ∷ PAddResult (PPred m :-: PPred n)
                                        (PPred n) (PPred m) of
    Dict → case pAdd2 ∷ PAdd2 (PPred m :-: PPred n) n of
      Dict → Dict

pSubSelf ∷ ∀ n . IsPeano n ⇒ PSubResult n n PZero
pSubSelf = case peano ∷ Peano n of
  PZero   → Dict
  PSucc _ → case pSubSelf ∷ PSubResult (PPred n) (PPred n) PZero of
    Dict → Dict

infixl 7 :×:

class (PAdd n m, PAdd m n, IsPeano (n :×: m), (n :×: m) ~ (m :×: n))
      ⇒ PMul n m where
  type n :×: m

instance PMul PZero PZero where
  type PZero :×: PZero = PZero

instance IsPeano p ⇒ PMul PZero (PSucc p) where
  type PZero :×: PSucc p = PZero

instance IsPeano p ⇒ PMul (PSucc p) PZero where
  type PSucc p :×: PZero = PZero

instance (PAdd (n :+: m) (n :×: m), PAdd (n :×: m) (n :+: m), PMul n m)
         ⇒ PMul (PSucc n) (PSucc m) where
  type PSucc n :×: PSucc m = PSucc (n :+: m :+: (n :×: m))

type PMul2C n m = (PMul n m, PMul m n, PAdd3C n m (n :×: m))
type PMul2 n m = Dict (PMul2C n m)
-}

{-
pMul2 ∷ ∀ n m . (IsPeano n, IsPeano m) ⇒ PMul2 n m
pMul2 = case (peano ∷ Peano n, peano ∷ Peano m) of
  (PZero,   PZero)   → Dict
  (PZero,   PSucc _) → Dict
  (PSucc _, PZero)   → Dict
  (PSucc _, PSucc _) → case pMul2 ∷ PMul2 (PPred n) (PPred m) of
    Dict → case pAdd3 ∷ PAdd3 (PPred n) (PPred m) (PPred (n :×: m)) of
      Dict → case pAdd2 ∷ PAdd2 (PPred n :+: PPred m) (PPred (n :×: m)) of
        Dict → case pAdd2 ∷ PAdd2 (PPred n :+: PPred (n :×: m)) (PPred m) of
          Dict → case pAdd2 ∷ PAdd2 (PPred m :+: PPred (n :×: m)) (PPred n) of 
            Dict → Dict
{-
    Dict → case pAdd3 ∷ PAdd3 (PPred n) (PPred m) (PPred (n :×: m)) of
      Dict → case pAddSucc ∷ PAddSucc (PPred (n :×: m)) (PPred (n :+: m)) of
        Dict → case pAddSucc ∷ PAddSucc (PPred (n :×: m) :+: PPred m)
                                         (PPred n) of
          Dict → case pAddSucc ∷ PAddSucc (PPred (n :×: m) :+: PPred n)
                                           (PPred m) of
            Dict → Dict
-}

type PMulResult n m r = Dict (PMul n m, PMul m n, (n :×: m) ~ r)

type PMulZero n = PMulResult n PZero PZero

pMulZero ∷ ∀ n . IsPeano n ⇒ PMulZero n
pMulZero = case peano ∷ Peano n of
  PZero   → Dict
  PSucc _ → Dict

type PMulOne n = PMulResult n P1 n

pMulOne ∷ ∀ n . IsPeano n ⇒ PMulOne n
pMulOne = case peano ∷ Peano n of
  PZero   → Dict
  PSucc _ → case pMulZero ∷ PMulZero (PPred n) of
    Dict → case pAddZero ∷ PAddZero (PPred n) of
      Dict → Dict

type PMulSucc n m =
  Dict (PMul n m, PMul m n,
         PMul (PSucc n) m, PMul m (PSucc n),
         PMul n (PSucc m), PMul (PSucc m) n,
         PAdd (n :×: m) n, PAdd n (n :×: m),
         PAdd (n :×: m) m, PAdd m (n :×: m),
         (PSucc n :×: m) ~ ((n :×: m) :+: m),
         (n :×: PSucc m) ~ ((n :×: m) :+: n))

pMulSucc ∷ ∀ n m . (IsPeano n, IsPeano m) ⇒ PMulSucc n m
pMulSucc = case (peano ∷ Peano n, peano ∷ Peano m) of
  (PZero, PZero)     → Dict
  (PZero, PSucc _)   → case pMulZero ∷ PMulZero (PPred m) of
    Dict → case pAddZero ∷ PAddZero (PPred m) of
      Dict → Dict
  (PSucc _, PZero)   → case pMulZero ∷ PMulZero (PPred n) of
    Dict → case pAddZero ∷ PAddZero (PPred n) of
      Dict → Dict
  (PSucc _, PSucc _) → case pMulSucc ∷ PMulSucc (PPred n) (PPred m) of
    Dict → case pAdd2 ∷ PAdd2 (PPred n) (PPred m) of
      Dict → case pAdd2 ∷ PAdd2 ((PPred n :×: PPred m) :+: PPred n)
                                 (PPred n :+: PPred m) of
        Dict → case pAdd2 ∷ PAdd2 ((PPred n :×: PPred m) :+: PPred m)
                                   (PPred n :+: PPred m) of
          Dict → case pAdd3 ∷ PAdd3 (PPred n :×: PPred m)
                                     (PPred n :+: PPred m)
                                     (PPred n) of
            Dict → case pAdd3 ∷ PAdd3 (PPred n :×: PPred m)
                                       (PPred n :+: PPred m)
                                       (PPred m) of
              Dict → Dict

type PMul3 n m k =
  Dict (PMul n m, PMul m k, PMul m n, PMul k m, PMul n k, PMul k n,
         PMul (n :×: m) k, PMul k (m :×: n),
         PMul n (m :×: k), PMul (m :×: k) n,
         PMul (n :×: k) m, PMul m (n :×: k),
         ((n :×: m) :×: k) ~ (n :×: (m :×: k)),
         (m :×: (n :×: k)) ~ ((m :×: n) :×: k))

pMul3 ∷ ∀ n m k . (IsPeano n, IsPeano m, IsPeano k) ⇒ PMul3 n m k
pMul3 = case (peano ∷ Peano n, peano ∷ Peano m, peano ∷ Peano k) of
  (PZero,   PZero,   PZero)   → Dict
  (PZero,   PZero,   PSucc _) → Dict
  (PZero,   PSucc _, PZero)   → Dict
  (PSucc _, PZero,   PZero)   → Dict
  (PZero,   PSucc _, PSucc _) → case pMul2 ∷ PMul2 (PPred m) (PPred k) of
    Dict → Dict
  (PSucc _, PZero,   PSucc _) → case pMul2 ∷ PMul2 (PPred n) (PPred k) of
    Dict → Dict
  (PSucc _, PSucc _, PZero)   → case pMul2 ∷ PMul2 (PPred n) (PPred m) of
    Dict → Dict
{-
  (PSucc _, PSucc _, PSucc _) → 
    case pMul3 ∷ PMul3 (PPred n) (PPred m) (PPred k) of
      Dict → case pMulSucc ∷ PMulSucc (PPred n :×: PPred m) (PPred k) of
        Dict → case pMulSucc ∷ PMulSucc (PPred n :×: PPred k) (PPred m) of
          Dict → case pMulSucc ∷ PMulSucc (PPred m :×: PPred k) (PPred n) of 
            Dict → case pAdd3 ∷ PAdd3 (PPred n :+: PPred m)
                                       (PPred n :×: PPred m)
                                       (PPred k) of
              Dict → case pAdd3 ∷ PAdd3 (PPred n :+: PPred k)
                                         (PPred n :×: PPred k)
                                         (PPred m) of
                Dict → case pAdd3 ∷ PAdd3 (PPred m :+: PPred k)
                                           (PPred m :×: PPred k)
                                           (PPred n) of
                  Dict → Dict
-}

type PDist n m k =
  Dict (PAdd n m, PAdd m n, PAdd n k, PAdd k n, PAdd m k, PAdd k m,
         PMul n m, PMul m n, PMul n k, PMul k n, PMul m k, PMul k m,
         PAdd (n :×: m) (n :×: k), PAdd (n :×: k) (n :×: m),
         PAdd (n :×: m) (m :×: k), PAdd (m :×: k) (n :×: m),
         PAdd (n :×: k) (m :×: k), PAdd (m :×: k) (n :×: k),
         PMul n (m :+: k), PMul (m :+: k) n,
         PMul m (n :+: k), PMul (n :+: k) m,
         PMul k (n :+: m), PMul (n :+: m) k,
         (n :×: (m :+: k)) ~ ((n :×: m) :+: (n :×: k)),
         (m :×: (n :+: k)) ~ ((n :×: m) :+: (m :×: k)),
         (k :×: (n :+: m)) ~ ((n :×: k) :+: (m :×: k)))

pDist ∷ ∀ n m k . (IsPeano n, IsPeano m, IsPeano k) ⇒ PDist n m k
pDist = case (peano ∷ Peano n, peano ∷ Peano m, peano ∷ Peano k) of
  (PZero,   PZero,   PZero)   → Dict
  (PZero,   PZero,   PSucc _) → Dict
  (PZero,   PSucc _, PZero)   → Dict
  (PSucc _, PZero,   PZero)   → Dict
  (PZero,   PSucc _, PSucc _) → case pMul2 ∷ PMul2 (PPred m) (PPred k) of
    Dict → Dict
  (PSucc _, PZero,   PSucc _) → case pMul2 ∷ PMul2 (PPred n) (PPred k) of
    Dict → Dict
  (PSucc _, PSucc _, PZero)   → case pMul2 ∷ PMul2 (PPred n) (PPred m) of
    Dict → Dict

-}
