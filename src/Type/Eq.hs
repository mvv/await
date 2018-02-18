{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Type.Eq (
    True, False, (:≡?:), (:≡:), (:≢:), IfEq
  ) where

data True
data False

class TypeEq g a b r | g a b → r
instance TypeEq () a a True

class TypeNotEq g a b r | g a b → r
instance TypeNotEq () a b False

class TypeMaybeEq g a b r | g a b → r
instance TypeEq    () a b r ⇒ TypeMaybeEq () a b r
instance TypeNotEq g  a b r ⇒ TypeMaybeEq g  a b r

class ab :≡?: r | ab → r
instance TypeMaybeEq () a b r ⇒ (a, b) :≡?: r

class a :≡: b
instance ((a, b) :≡?: True) ⇒ a :≡: b

class a :≢: b
instance ((a, b) :≡?: False) ⇒ a :≢: b

class If test t f r | test t f → r
instance If True t f t
instance If False t f f

class IfEq a b t f r | a b t f → r
instance ((a, b) :≡?: test, If test t f r) ⇒ IfEq a b t f r

{-
infix 9 :∖=:

class se :∖=: c | se → c
instance (s, HEmpty) :∖=: s
instance (HEmpty, HSingle e) :∖=: HEmpty
instance (HEmpty, h :×: t) :∖=: HEmpty
instance (IfEq e1 e2 HEmpty (HSingle e1) r) ⇒ (HSingle e1, HSingle e2) :∖=: r
instance (IfEq e1 e2 t (e1 :×: t) r) ⇒ (e1 :×: t, HSingle e2) :∖=: r
instance (e1 :≡: e2) ⇒ (HSingle e1, e2 :×: t) :∖=: HEmpty
instance (e1 :≢: e2, (HSingle e1, t) :∖=: t') ⇒ (HSingle e1, e2 :×: t) :∖=: t'
instance (e1 :≡: e2, (t1, e2 :×: t2) :∖=: t1') ⇒ (e1 :×: t1, e2 :×: t2) :∖=: t1'
instance (e1 :≢: e2, (t1, e2 :×: t2) :∖=: t1') ⇒ (e1 :×: t1, e2 :×: t2) :∖=: (e1 :×: t1')
-}

