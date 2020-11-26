module GradedMonad where

open import Level
open import Function hiding (_$_;id)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality as HE

-- **** Graded monad

record Monoid {l : Level} : Set (Level.suc l) where
  field Carrier : Set l
        unit : Carrier
        _⊕_ : Carrier -> Carrier -> Carrier
        assoc : {x y z : Carrier} -> (x ⊕ (y ⊕ z)) ≡ ((x ⊕ y) ⊕ z)
        unit-left : {x : Carrier} -> (unit ⊕ x) ≡ x
        unit-right : {x : Carrier} -> (x ⊕ unit) ≡ x

open Monoid

record GMonad {l : Level} : Set (Level.suc (Level.suc l)) where -- Graded monad
  field M : Monoid {l}
        Gm : Carrier M -> Set -> Set₁
        gunit : {A : Set} -> A -> Gm (unit M) A
        gbind  : {A B : Set} {i j : Carrier M} -> Gm i A -> (A -> Gm j B) -> Gm (_⊕_ M i j) B

        -- Laws
        lunit : {A B : Set} {i : Carrier M} -> (x : A) (f : A -> Gm i B) -> gbind (gunit x) f ≅ f x

        runit : {A : Set} {i : Carrier M}
         -> (x : Gm i A) -> gbind x gunit ≅ x

        assoc : {A B C : Set} {i j k : Carrier M}
         (m : Gm i A)
         (f : A -> Gm j B)
         (g : B -> Gm k C) ->
         (gbind {A} {C} {i} {_⊕_ M j k}
              m (\x -> gbind {B} {C} {j} {k} (f x) g))
         ≅
         (gbind {B} {C} {_⊕_ M i j} {k} (gbind {A} {B} {i} {j} m f) g)

open GMonad
