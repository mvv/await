{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

{-
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverlappingInstances #-}
-}

module Data.Capability (
    ReadCap,
    WriteCap,
    WaitCap,
    CancelCap,
    Capable(..),
    Capable1(..)
  ) where

import Data.Heterogeneous.List

data ReadCap
data WriteCap
data WaitCap
data CancelCap

data Capable c f where
  Capable ∷ (c :∈: cs) ⇒ f cs → Capable c f

data Capable1 c f α where
  Capable1 ∷ (c :∈: cs) ⇒ f cs α → Capable1 c f α

{-
data a :⊔: b

data CapWitness c cs where
  SingleCapWitness ∷ CapWitness c c
  FirstCapWitness  ∷ CapWitness c (c :⊔: cs)
  RestCapWitness   ∷ ∀ c c' cs . (c :⊑: cs)
                   ⇒ CapWitness c (c' :⊔: cs)
  UnionCapWitness  ∷ ∀ c c' cs . (c :⊑: cs, c' :⊑: cs)
                   ⇒ CapWitness (c :⊔: c') cs

class c :⊑: cs where
  capWitness ∷ c → cs → CapWitness c cs

instance c :⊑: c where
  capWitness _ _ = SingleCapWitness

instance c :⊑: (c :⊔: cs) where
  capWitness _ _ = FirstCapWitness

instance (c :⊑: cs) ⇒ c :⊑: (c' :⊔: cs) where
  capWitness _ _ = RestCapWitness

instance (c :⊑: cs, c' :⊑: cs) ⇒ (c :⊔: c') :⊑: cs where
  capWitness _ _ = UnionCapWitness

class RestrictCaps f where
  restirctCaps ∷ (cs :⊑: cs') ⇒ f cs' → f cs

class RestrictCaps1 f where
  restrictCaps1 ∷ (cs :⊑: cs') ⇒ f cs' α → f cs α

class RestrictCaps2 f where
  restrictCaps2 ∷ (cs :⊑: cs') ⇒ f cs' α β → f cs α β

class RestrictCaps3 f where
  restrictCaps3 ∷ (cs :⊑: cs') ⇒ f cs' α β γ → f cs α β γ
-}

