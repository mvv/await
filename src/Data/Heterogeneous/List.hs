{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Rank2Types #-}

module Data.Heterogeneous.List where

import Data.Peano

infixr 7 :*, .*
infix  8 :*:, .*.

data HNil
data h :* t
type HSingle α = α :* HNil
type α :*: β = α :* β :* HNil

data HList l where
  HNil ∷ HList HNil
  (:*) ∷ HListClass t ⇒ h → HList t → HList (h :* t)

instance Show (HList HNil) where
  show _ = "HNil"

instance (Show h, Show (HList t)) ⇒ Show (HList (h :* t)) where
  showsPrec d (h :* t) = showParen (d > 7) $
    showsPrec 8 h . showString " .* " . showsPrec 7 t

(.*) ∷ HListClass t ⇒ h → HList t → HList (h :* t)
(.*) = (:*)

(.*.) ∷ α → β → HList (α :*: β)
a .*. b = a .* b .* HNil

data HListWitness l where
  HNilList  ∷ HListWitness HNil
  HConsList ∷ HListClass t ⇒ HListWitness (h :* t)

class HListClass l where
  hListWitness ∷ HListWitness l

instance HListClass HNil where
  hListWitness = HNilList

instance HListClass t ⇒ HListClass (h :* t) where
  hListWitness = HConsList

data HListInst l where
  HListInst ∷ HListClass l ⇒ HListInst l

hListInst ∷ HList l → HListInst l
hListInst HNil     = HListInst
hListInst (_ :* _) = HListInst

class (l ~ (HHead l :* HTail l), HListClass (HTail l)) ⇒ HNonEmpty l where
  type HHead l
  type HTail l

instance HListClass t ⇒ HNonEmpty (h :* t) where
  type HHead (h :* t) = h
  type HTail (h :* t) = t

hHead ∷ HList (h :* t) → h
hHead (h :* _) = h

hTail ∷ HList (h :* t) → HList t
hTail (_ :* t) = t

data HNonEmptyInst l where
  HNonEmptyInst ∷ HListClass t ⇒ HNonEmptyInst (h :* t)

data HDropWitness n l where
  HDropZero ∷ HListClass l ⇒ HDropWitness PZero l
  HDropSucc ∷ HDropClass p t ⇒ HDropWitness (PSucc p) (h :* t)

class (IsPeano n, HListClass l, HListClass (HDrop n l)) ⇒ HDropClass n l where
  type HDrop n l
  hDropWitness ∷ HDropWitness n l

instance HListClass l ⇒ HDropClass PZero l where
  type HDrop PZero l = l
  hDropWitness = HDropZero

instance HDropClass p t ⇒ HDropClass (PSucc p) (h :* t) where
  type HDrop (PSucc p) (h :* t) = HDrop p t
  hDropWitness = case hDropWitness ∷ HDropWitness p t of
    HDropZero → HDropSucc
    HDropSucc → HDropSucc

data HDropInst n l where
  HDropInst ∷ HDropClass n l ⇒ HDropInst n l

hDrop ∷ ∀ n l . HDropClass n l ⇒ Peano n → HList l → HList (HDrop n l)
hDrop n l = case hDropWitness ∷ HDropWitness n l of
  HDropZero → l
  HDropSucc → hDrop (pPred n) (hTail l)

data HNonEmptyDropInst n l where
  HNonEmptyDropInst ∷ (HDropClass n l, HNonEmpty l,
                       HDropClass (PSucc n) l, HNonEmpty (HDrop n l))
                    ⇒ HNonEmptyDropInst n l

pPrevDropInst ∷ ∀ n l . HDropClass (PSucc n) l ⇒ HNonEmptyDropInst n l
pPrevDropInst = case hDropWitness ∷ HDropWitness (PSucc n) l of
  HDropSucc → case hDropWitness ∷ HDropWitness n (HTail l) of
    HDropZero → HNonEmptyDropInst
    HDropSucc → case pPrevDropInst ∷ HNonEmptyDropInst (PPred n) (HTail l) of
      HNonEmptyDropInst → HNonEmptyDropInst

hNextDropInst ∷ ∀ n l . (HDropClass n l, HNonEmpty (HDrop n l))
              ⇒ HNonEmptyDropInst n l
hNextDropInst = case hDropWitness ∷ HDropWitness n l of
  HDropZero → HNonEmptyDropInst
  HDropSucc → case hNextDropInst ∷ HNonEmptyDropInst (PPred n) (HTail l) of
    HNonEmptyDropInst → HNonEmptyDropInst

data HTailDropComm n l where
  HTailDropComm ∷ (HNonEmpty l, HDropClass n l,
                   HNonEmpty (HDrop n l), HDropClass n (HTail l),
                   HDropClass (PSucc n) l,
                   HTail (HDrop n l) ~ HDrop n (HTail l),
                   HDrop (PSucc n) l ~ HTail (HDrop n l),
                   HDrop (PSucc n) l ~ HDrop n (HTail l))
                ⇒ HTailDropComm n l

hTailDropComm' ∷ ∀ n l . (HDropClass (PSucc n) l)
               ⇒ HTailDropComm n l
hTailDropComm' = case pPrevDropInst ∷ HNonEmptyDropInst n l of
  HNonEmptyDropInst → hTailDropComm

hTailDropComm ∷ ∀ n l . (HDropClass n l, HNonEmpty (HDrop n l))
               ⇒ HTailDropComm n l
hTailDropComm = case hDropWitness ∷ HDropWitness n l of
  HDropZero → HTailDropComm
  HDropSucc  → case hTailDropComm ∷ HTailDropComm (PPred n) (HTail l) of
    HTailDropComm → HTailDropComm

type HNth n l = HHead (HDrop n l)

hNth ∷ ∀ n l . (HDropClass n l, HNonEmpty (HDrop n l))
     ⇒ Peano n → HList l → HNth n l
hNth n l = case hDropWitness ∷ HDropWitness n l of
  HDropZero → hHead l
  HDropSucc  → hNth (pPred n) (hTail l)

data HElemOf l where
  HNth ∷ (HDropClass n l, HNonEmpty (HDrop n l))
       ⇒ Peano n → HNth n l → HElemOf l

hGetIfNth ∷ ∀ n l . (HDropClass n l, HNonEmpty (HDrop n l))
          ⇒ Peano n → HElemOf l → Maybe (HNth n l)
hGetIfNth PZero    (HNth PZero x)     = Just x
hGetIfNth (PSucc p) (HNth (PSucc p') x) =
  case hDropWitness ∷ HDropWitness n l of
    HDropSucc  →
      let inst ∷ ∀ m . HDropClass (PSucc m) l
               ⇒ Peano m → HTailDropComm m l
          inst _ = hTailDropComm' in
        case inst p' of
          HTailDropComm → hGetIfNth p (HNth p' x ∷ HElemOf (HTail l))
    _          → undefined
hGetIfNth _        _                  = Nothing

elem0 ∷ HNonEmpty l ⇒ HElemOf l → Maybe (HHead l)
elem0 = hGetIfNth peano0
elem1 ∷ (HDropClass P1 l, HNonEmpty (HDrop P1 l))
      ⇒ HElemOf l → Maybe (HNth P1 l)
elem1 = hGetIfNth peano1
elem2 ∷ (HDropClass P2 l, HNonEmpty (HDrop P2 l))
      ⇒ HElemOf l → Maybe (HNth P2 l)
elem2 = hGetIfNth peano2
elem3 ∷ (HDropClass P3 l, HNonEmpty (HDrop P3 l))
      ⇒ HElemOf l → Maybe (HNth P3 l)
elem3 = hGetIfNth peano3
elem4 ∷ (HDropClass P4 l, HNonEmpty (HDrop P4 l))
      ⇒ HElemOf l → Maybe (HNth P4 l)
elem4 = hGetIfNth peano4
elem5 ∷ (HDropClass P5 l, HNonEmpty (HDrop P5 l))
      ⇒ HElemOf l → Maybe (HNth P5 l)
elem5 = hGetIfNth peano5
elem6 ∷ (HDropClass P6 l, HNonEmpty (HDrop P6 l))
      ⇒ HElemOf l → Maybe (HNth P6 l)
elem6 = hGetIfNth peano6
elem7 ∷ (HDropClass P7 l, HNonEmpty (HDrop P7 l))
      ⇒ HElemOf l → Maybe (HNth P7 l)
elem7 = hGetIfNth peano7
elem8 ∷ (HDropClass P8 l, HNonEmpty (HDrop P8 l))
      ⇒ HElemOf l → Maybe (HNth P8 l)
elem8 = hGetIfNth peano8
elem9 ∷ (HDropClass P9 l, HNonEmpty (HDrop P9 l))
      ⇒ HElemOf l → Maybe (HNth P9 l)
elem9 = hGetIfNth peano9

data HMapWitness f l where
  HNilMap  ∷ HMapWitness f HNil
  HConsMap ∷ HMapClass f t ⇒ HMapWitness f (h :* t)

class (HListClass l, HListClass (HMap f l)) ⇒ HMapClass (f ∷ ★ → ★) l where
  type HMap f l
  hMapWitness ∷ HMapWitness f l

instance HMapClass f HNil where
  type HMap f HNil = HNil
  hMapWitness = HNilMap

instance HMapClass f t ⇒ HMapClass f (h :* t) where
  type HMap f (h :* t) = f h :* HMap f t
  hMapWitness = HConsMap

data HMapInst f l where
  HMapInst ∷ HMapClass f l ⇒ HMapInst f l

hMapInst ∷ ∀ f l . HListClass l ⇒ HMapInst f l
hMapInst = case hListWitness ∷ HListWitness l of
  HNilList  → HMapInst
  HConsList → case hMapInst ∷ HMapInst f (HTail l) of
    HMapInst → HMapInst

hMapWitness' ∷ ∀ f l . HListClass l ⇒ HMapWitness f l
hMapWitness' = case hMapInst ∷ HMapInst f l of
  HMapInst → hMapWitness

hMap ∷ ∀ f l . HMapClass f l ⇒ (∀ α . α → f α) → HList l → HList (HMap f l)
hMap f l = case hMapWitness ∷ HMapWitness f l of
  HNilMap  → HNil
  HConsMap → f (hHead l) :* hMap f (hTail l)

data HMapDropComm f n l where
  HMapDropComm ∷ (HDropClass n l, HMapClass f l,
                  HDropClass n (HMap f l), HMapClass f (HDrop n l),
                  HMap f (HDrop n l) ~ HDrop n (HMap f l))
               ⇒ HMapDropComm f n l

hMapDropComm ∷ ∀ f n l . HDropClass n l ⇒ HMapDropComm f n l
hMapDropComm = case hDropWitness ∷ HDropWitness n l of
  HDropZero → case hMapWitness' ∷ HMapWitness f l of
    HNilMap  → HMapDropComm
    HConsMap → HMapDropComm
  HDropSucc  → case hMapInst ∷ HMapInst f l of
    HMapInst → case hMapInst ∷ HMapInst f (HDrop n l) of
      HMapInst → case hMapDropComm ∷ HMapDropComm f (PPred n) (HTail l) of
        HMapDropComm → HMapDropComm

hMapDropInst ∷ ∀ f n l α . (HMapClass f l, HDropClass n (HMap f l))
             ⇒ f α → HDropInst n l
hMapDropInst f = case hMapWitness ∷ HMapWitness f l of
  HNilMap  → HDropInst
  HConsMap → case hDropWitness ∷ HDropWitness n (HMap f l) of
    HDropZero → HDropInst
    HDropSucc → case hMapDropInst f ∷ HDropInst (PPred n) (HTail l) of
      HDropInst → HDropInst

hMapDropComm' ∷ ∀ f n l . (HMapClass f l, HDropClass n (HMap f l))
              ⇒ HMapDropComm f n l
hMapDropComm' = case hMapDropInst (undefined ∷ f ()) ∷ HDropInst n l of
  HDropInst → hMapDropComm

data HNonEmptyMap f l where
  HNonEmptyMap ∷ (HNonEmpty l, HMapClass f l,
                  HNonEmpty (HMap f l), HMapClass f (HTail l),
                  HHead (HMap f l) ~ f (HHead l),
                  HTail (HMap f l) ~ HMap f (HTail l))
               ⇒ HNonEmptyMap f l

hNonEmptyMap ∷ ∀ f l . HNonEmpty l ⇒ HNonEmptyMap f l
hNonEmptyMap = case hMapInst ∷ HMapInst f l of
  HMapInst → case hMapInst ∷ HMapInst f (HTail l) of
    HMapInst → HNonEmptyMap

hNonEmptyMap' ∷ ∀ f l . (HMapClass f l, HNonEmpty (HMap f l))
              ⇒ HNonEmptyMap f l
hNonEmptyMap' = case hMapWitness ∷ HMapWitness f l of
  HConsMap → HNonEmptyMap
  _        → undefined

{-
data HNonEmptyMapDropComm f n l where
  HNonEmptyMapDropComm ∷ (HDropClass n l, HMapClass f l,
                          HDropClass n (HMap f l), HMapClass f (HDrop n l),
                          HMap f (HDrop n l) ~ HDrop n (HMap f l),
                          HNonEmpty (HDrop n l),
                          HNonEmpty (HMap f (HDrop n l)),
                          HMapClass f (HTail (HDrop n l)),
                          HHead (HMap f (HDrop n l)) ~ f (HHead (HDrop n l)),
                          HTail (HMap f (HDrop n l)) ~ HMap f (HTail (HDrop n l)))
                       ⇒ HNonEmptyMapDropComm f n l

hNonEmptyMapDropComm' ∷ ∀ f n l
                      . (HMapClass f l,
                         HDropClass n l,
                         HDropClass n (HMap f l),
                         HNonEmpty (HDrop n (HMap f l)))
                      ⇒ HNonEmptyMapDropComm f n (HDrop n l)
hNonEmptyMapDropComm' =
  case hNextDropInst ∷ HNonEmptyDropInst n (HMap f l) of
    HNonEmptyDropInst →
      case hMapDropInst (undefined ∷ f ()) ∷ HDropInst n l of
        HDropInst → case hMapDropComm' ∷ HMapDropComm f n l of
          HMapDropComm → case hNonEmptyMap' ∷ HNonEmptyMap f (HDrop n l) of
            HNonEmptyMap → HNonEmptyMapDropComm
-}

{-case hNonEmptyMap' ∷ HNonEmptyMap f l of
        HNonEmptyMap → HNonEmptyMapDropComm-}

infixr 6 :∪:

type family s1 :∪: s2
type instance HNil     :∪: s2 = s2
type instance (h :* t) :∪: s2 = h :* (t :∪: s2)

infix 4 :∈:

data HMembershipWitness e s where
  HHeadMember ∷ HMembershipWitness e (e :* tail)
  HTailMember ∷ ∀ e head tail . (e :∈: tail)
              ⇒ HMembershipWitness e tail
              → HMembershipWitness e (head :* tail)

class e :∈: s where
  hMembershipWitness ∷ HMembershipWitness e s

instance e :∈: (e :* tail) where
  hMembershipWitness = HHeadMember

instance (e :∈: tail) ⇒ e :∈: (head :* tail) where
  hMembershipWitness = HTailMember hMembershipWitness

infix 4 :⊆:

data HInclusionWitness sub set where
  HNilInclusion  ∷ HInclusionWitness HNil set
  HConsInclusion ∷ ∀ head tail set . (head :∈: set, tail :⊆: set)
                 ⇒ HMembershipWitness head set
                 → HInclusionWitness tail set
                 → HInclusionWitness (head :* tail) set

class sub :⊆: set where
  hInclusionWitness ∷ HInclusionWitness sub set

instance HNil :⊆: set where
  hInclusionWitness = HNilInclusion

instance (head :∈: set, tail :⊆: set) ⇒ (head :* tail) :⊆: set where
  hInclusionWitness = HConsInclusion hMembershipWitness hInclusionWitness

class Restrict f where
  restrict ∷ (sub :⊆: set) ⇒ f set → f sub

class Restrict1 f where
  restrict1 ∷ (sub :⊆: set) ⇒ f set α → f sub α

class Restrict2 f where
  restrict2 ∷ (sub :⊆: set) ⇒ f set α β → f sub α β

class Restrict3 f where
  restrict3 ∷ (sub :⊆: set) ⇒ f set α β γ → f sub α β γ

