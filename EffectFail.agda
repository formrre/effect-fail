{-# OPTIONS --rewriting #-}
{-# OPTIONS --confluence-check #-}
module EffectFail where

open import Level
open import Agda.Primitive
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality as HE using (_≅_;refl)
import Relation.Binary.HeterogeneousEquality as HE
open import Axiom.Extensionality.Heterogeneous as HExt

record RMonad {a b} (M : Set a -> Set b) : Set (lsuc a ⊔ b) where
  field
    pure : {A : Set a} -> A -> M A
    _>>=_ : {A B : Set a} -> M A -> (A -> M B) -> M B
    rightId : {A : Set a} (m : M A) -> m >>= pure ≡ m
    leftId : {A B : Set a} {a : A} {f : A -> M B} -> (pure a) >>= f ≡ f a
    bindAssoc : {A B C : Set a} (m : M A) (f : A -> M B) (g : B -> M C) -> (m >>= f) >>= g ≡ m >>= (λ x → f x >>= g)
open RMonad {{...}}
record RMonadFail {a b} (M : Set a -> Set b) : Set (lsuc a ⊔ b) where
  field
    overlap {{mA}} : RMonad M
    mfail : {A : Set a} -> M A
    mfailbind : {A B : Set a} {m : A -> M B} -> mfail >>= m ≡ mfail

variable
  l1 l2 : Level
  A : Set l1
  B : Set l2

data Maybe (A : Set l1) : Set l1 where
  Nothing : Maybe A
  Just : A -> Maybe A

RMonadMaybe : RMonad {l1} Maybe
RMonad.pure RMonadMaybe x = Just x
(RMonadMaybe RMonad.>>= Nothing) k = Nothing
(RMonadMaybe RMonad.>>= Just x) k = k x
RMonad.rightId RMonadMaybe Nothing = refl
RMonad.rightId RMonadMaybe (Just x) = refl
RMonad.leftId RMonadMaybe = refl
RMonad.bindAssoc RMonadMaybe Nothing f g = refl
RMonad.bindAssoc RMonadMaybe (Just x) f g = refl

data MaybeT (M : Set l1 -> Set l2) (A : Set l1) : Set l2 where
  MT : M (Maybe A) -> MaybeT M A

case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x

runMaybeT : {M : Set l1 -> Set l2} {A : Set l1} -> MaybeT M A -> M (Maybe A)
runMaybeT (MT x) = x

open Relation.Binary.PropositionalEquality.≡-Reasoning

data Singleton {a} {A : Set a} (x : A) : Set a where
  _withm≡_ : (y : A) → x ≡ y → Singleton x

myinspect : ∀ {a} {A : Set a} (x : A) → Singleton x
myinspect x = x withm≡ refl

postulate
  funExt : ∀ {l1 l2} {A : Set l1} {B : A → Set l2} {f g : (x : A) → B x} →
           ((x : A) → f x ≡ g x) → f ≡ g

  funExtHE : {l j : Level} -> HExt.Extensionality l j

helpermt : {l1 l2 : Level} {M : Set l1 -> Set l2} {A B : Set l1}(z : MaybeT M B) {x : M (Maybe B)} -> z ≡ MT x → runMaybeT z ≡ x
helpermt .(MT _) refl = refl

RMonadMaybeT : {M : Set l1 -> Set l2} -> RMonad M -> RMonad (MaybeT M)
RMonad.pure (RMonadMaybeT record { pure = pure ; _>>=_ = _ ; rightId = _ ; leftId = _ ; bindAssoc = _ }) x = MT (pure (Just x))
(RMonadMaybeT record { pure = purei ; _>>=_ = _>>=_ ; rightId = _ ; leftId = _ ; bindAssoc = _ } RMonad.>>= x) k = MT (do
  v ← runMaybeT x
  case v of
    λ{ Nothing → purei Nothing
    ; (Just y) → runMaybeT (k y)})
RMonad.rightId (RMonadMaybeT {l1} {l2} {M} record { pure = purei ; _>>=_ = _>>=i_ ; rightId = rightIdi ; leftId = _ ; bindAssoc = _ }) (MT x) =
  cong MT (helper (funExt λ { Nothing → refl ; (Just x) → refl }))
    where
      helper : {A : Set l1} {x : M A} {f : A -> M A} → (f ≡ purei) -> x >>=i f ≡ x
      helper {x = x} {f = f} prf = begin (x >>=i f)
             ≡⟨ cong₂ _>>=i_ refl prf ⟩
           (x >>=i purei)
             ≡⟨ rightIdi x ⟩
            x ∎
RMonad.leftId (RMonadMaybeT {l1} {l2} {M} record { pure = _ ; _>>=_ = _ ; rightId = _ ; leftId = leftIdi ; bindAssoc = _ }) {A = A} {B = B} {a = a} {f = f} with myinspect (f a)
... | (MT x) withm≡ prf = begin _
       ≡⟨ cong MT (begin _
          ≡⟨ leftIdi {a = Just a} ⟩
         runMaybeT (f a)
         ≡⟨ helpermt {l1} {l2}{M} {A} (f a) {x} prf  ⟩
         x ∎) ⟩
       _
       ≡⟨ sym prf ⟩
       _ ∎
RMonad.bindAssoc (RMonadMaybeT record { pure = _ ; _>>=_ = _>>=i_ ; rightId = _ ; leftId = leftIdi ; bindAssoc = bindAssoci }) (MT x) f g =
  cong MT (begin _
    ≡⟨ bindAssoci _ _ _ ⟩
    _
    ≡⟨ cong (_>>=i_ x)
    (funExt λ { Nothing →
        begin _ ≡⟨ leftIdi {a = Nothing} ⟩ _ ∎
      ; (Just w) → cong₂ _>>=i_ refl (funExt λ{ Nothing → refl ; (Just x) → refl}) }) ⟩
  _ ∎)

-- Given a monad then MaybeT is a Monad fail
RMonadFailMaybeT : {M : Set l1 -> Set l2} -> RMonad M -> RMonadFail (MaybeT M)
RMonadFail.mA (RMonadFailMaybeT m) = RMonadMaybeT m
RMonadFail.mfail (RMonadFailMaybeT record { pure = purei ; _>>=_ = _>>=i_ ; rightId = rightIdi ; leftId = leftIdi ; bindAssoc = bindAssoci }) = MT (purei Nothing)
RMonadFail.mfailbind (RMonadFailMaybeT record { pure = purei ; _>>=_ = _>>=i_ ; rightId = rightIdi ; leftId = leftIdi ; bindAssoc = bindAssoci }) = cong MT leftIdi

open import Data.List
open import Data.Bool
open import Data.Empty
open import Data.Unit

-- This is really a postulate
cmpSet : {l : Level} -> (Set l -> Set l) -> (Set l -> Set l) -> Bool
cmpSet = λ _ _ → false

inSetList : {l : Level} -> (Set l -> Set l) -> List (Set l -> Set l) -> Bool
inSetList _ [] = false
inSetList s (x ∷ xs) = case cmpSet s x of λ{ false → inSetList s xs ; true → true}

boolToSet : Bool -> Set
boolToSet false = ⊥
boolToSet true = ⊤

-- Free monad indexed by set of
data Eff (E : List (Set -> Set)) (A : Set) : Set₁ where
  Pure : A -> Eff E A
  Impure : {F : Set -> Set} {X : Set} -> .{proof_FinE : boolToSet (inSetList F E)} -> F X -> (X -> Eff E A) -> Eff E A

_>>>_ : {l1 l2 l3 : Level} -> {M : Set l1 -> Set l2} -> {B C : Set l1} -> {A : Set l3} -> (A -> M B) -> (B -> M C) -> {{RM : RMonad M}} -> (A -> M C)
(f >>> g) ⦃ record { pure = pure ; _>>=_ = _>>=_ ; rightId = rightId ; leftId = leftId ; bindAssoc = bindAssoc } ⦄ x = (f x) >>= g

-- IDEA: (08/10/2020) This could be a graded monad as well

effbind : {E : List (Set -> Set)} {A B : Set} -> Eff E A -> (A -> Eff E B) -> Eff E B
effbind (Pure x) k = k x
effbind {E} {A} {B} (Impure {F} {X} {prf} f cont) k = Impure {F = F} {X} {prf} f λ x → effbind (cont x) k

effpure : {E : List (Set -> Set)} {A : Set} -> A -> Eff E A
effpure = Pure

effLeftId : {E : List (Set -> Set)} {A B : Set} -> (x : A) -> (f : A -> Eff E B) -> effbind (effpure x) f ≡ f x
effLeftId x f = refl

effRightId : {E : List (Set -> Set)} {A : Set} -> (x : Eff E A) -> effbind x effpure ≡ x
effRightId (Pure x) = refl
effRightId (Impure x x₁) = cong (Impure x) (funExt λ x₂ → effRightId (x₁ x₂))

effBindAssoc : {E : List (Set -> Set)} {A B C : Set} -> (x : Eff E A) -> (f : A -> Eff E B) -> (g : B -> Eff E C) -> effbind (effbind x f) g ≡ effbind x λ y → effbind (f y) g
effBindAssoc (Pure x) f g = refl
effBindAssoc (Impure x z) f g = cong (Impure x) (funExt λ w → effBindAssoc (z w) f g)

RMonadEff : {E : List (Set -> Set)} -> RMonad (Eff E)
RMonad.pure RMonadEff = effpure
RMonad._>>=_ RMonadEff = effbind
RMonad.rightId RMonadEff {A} m = effRightId m
RMonad.leftId RMonadEff {A} {B} {a} {f} = effLeftId a f
RMonad.bindAssoc RMonadEff x f g = effBindAssoc x f g

EffFail : (E : List (Set -> Set)) -> (A : Set) -> Set₁
EffFail E A = MaybeT (Eff E) A

-- Specialise previous result that for every monad M, then M is a MonadFail
RMonadEffFail : {E : List (Set -> Set)} -> RMonadFail (EffFail E)
RMonadEffFail = RMonadFailMaybeT RMonadEff

run : Eff [] A -> A
run (Pure x) = x

runFail : EffFail [] A -> Maybe A
runFail (MT x) = run x

-- Smart constructor for `Impure`
send : {E : List (Set -> Set)} {T : Set -> Set} {V : Set} -> (T V) -> .(boolToSet (inSetList T E)) -> Eff E V
send {E} {T} {V} x irr  = Impure {E} {V} {T} {V} {irr} x Pure

-- Smart constructor `Impure` but inside of a MaybeT
sendFail : {E : List (Set -> Set)} {T : Set -> Set} {V : Set} -> (T V) -> boolToSet (inSetList T E) -> EffFail E V
sendFail {E} {T} {V} x prf = MT (Impure {F = T} {X = V} {prf} x λ x → Pure (Just x))

data Either {l1 l2 : Level} (A : Set l1) (B : Set l2) : Set (l1 ⊔ l2) where
  Left : A -> Either A B
  Right : B -> Either A B

open import Data.Nat

{- TODO to provide these nicely in our setting we need type case -}
decomp : {F : Set -> Set} {X : Set} -> Either ℕ (F X)
decomp = Left ℕ.zero

-- IDEA: (08/10/2020) postulate deleteAll (and its relevant properties) instead?
-- TODO
handleRelay : {ES : List (Set -> Set)} {E : Set -> Set} {A B : Set}
   -> (A -> Eff ES B) -> ((∀ {V : Set} → E V -> Eff ES B)) -> Eff ES A -> Eff ES B {- deleteAll E ES ; TODO -}
handleRelay ret h (Pure x) = ret x
handleRelay ret h (Impure x x₁) = Impure x (λ z → handleRelay ret h (x₁ z))

open import Data.List.Properties

record Monoid {l : Level} : Set (lsuc l) where
  field Carrier : Set l
        unit : Carrier
        _⊕_ : Carrier -> Carrier -> Carrier
        assoc : {x y z : Carrier} -> (x ⊕ (y ⊕ z)) ≡ ((x ⊕ y) ⊕ z)
        unit-left : {x : Carrier} -> (unit ⊕ x) ≡ x
        unit-right : {x : Carrier} -> (x ⊕ unit) ≡ x

open Monoid

++-unit-r : {l : Level} → {A : Set l} → (xs : List A) → xs ++ [] ≡ xs
++-unit-r [] = refl
++-unit-r (x ∷ xs) = cong (_∷_ x) (++-unit-r xs)

MonoidEL : Monoid
MonoidEL = record
             { Carrier = List (Set → Set)
             ; unit = []
             ; _⊕_ = _++_
             ; assoc = λ{x}{y}{z} → sym (++-assoc x y z)
             ; unit-left = refl
             ; unit-right = λ{x} → ++-unit-r x
             }

gunit : {A : Set} → A → Eff [] A
gunit x = Pure x

boolToSetLemma : {F : Set → Set} -> (X Y : List (Set → Set)) → boolToSet (inSetList F Y) → boolToSet (inSetList F (X ++ Y))
boolToSetLemma {F} [] Y p = p
boolToSetLemma {F} (x ∷ X) Y p = boolToSetLemma {F} X Y p

boolToSetLemma2 : {F : Set → Set} -> (X Y : List (Set → Set)) → boolToSet (inSetList F X) → boolToSet (inSetList F (X ++ Y))
boolToSetLemma2 {F} (x ∷ X) Y p = boolToSetLemma2 {F} X Y p

upcast : {E NE : List (Set → Set)} → {A : Set} → Eff E A → Eff (NE ++ E) A
upcast (Pure x) = Pure x
upcast {E} {NE} (Impure {F = F} {X = X} {prf} x k) = Impure {F = F} {X = X} {boolToSetLemma {F} NE E prf} x λ y → upcast (k y)

gbind : {A B : Set} {X Y : List (Set → Set)} → Eff X A → (A → Eff Y B) → (Eff (X ++ Y) B)
gbind {A} {B} {XT} {YT} (Pure x) k with k x
... | Pure x₁ = Pure x₁
... | Impure {F = F} {X = X} {prf} x₁ x₂ = Impure {F = F} {X = X} { boolToSetLemma {F} XT YT prf } x₁ λ x₃ → upcast (x₂ x₃)
gbind {A} {B} {XT} {YT} (Impure {F = F} {X = X} {prf} x cont) k = Impure {F = F} {X = X} { boolToSetLemma2 {F} XT YT prf } x λ y → gbind (cont y) k
-- boolToSetUnit : boolTSetLemma [] Y proof ≡ proof

boolToSetLemma2Unit : {F : Set -> Set} -> (X : List (Set -> Set)) -> (z : boolToSet (inSetList F X))
                  -> boolToSetLemma2 {F} X [] z ≅ z
boolToSetLemma2Unit {F} (x ∷ X) z = boolToSetLemma2Unit {F} X z

mutual
  upcastUnit : {E : List (Set -> Set)} {A : Set} {x : Eff E A} -> upcast {E} {[]} x ≡ x
  upcastUnit {[]} {A} {Pure x} = refl
  upcastUnit {x ∷ E} {A} {Pure x₁} = refl
  upcastUnit {x ∷ E} {A} {Impure {F} {X} {proof_FinE} y k} rewrite upcastUnit' {x ∷ E} {X} {A} {k} = refl

  upcastUnit' : {E : List (Set -> Set)} {A B : Set} {k : A -> Eff E B} -> (λ x -> upcast {E} {[]} (k x)) ≡ k
  upcastUnit' {E} {A} {B} {k} = funExt (\x -> upcastUnit {E} {B} {k x})

leftUnit : {Y : List (Set → Set)} {A B : Set} {x : A} {f : A → Eff Y B} → gbind (gunit x) f ≡ f x
leftUnit {Y} {A} {B} {z} {f} with (f z)
... | Pure x = refl
... | Impure {fx} {X} x k rewrite upcastUnit' {Y} {X} {B} {k} = refl

++-identityr : {l : Level} {A : Set l} → (Y : List A) → Y ≡ Y ++ []
++-identityr [] = refl
++-identityr (x ∷ Y) = cong (x ∷_) (++-identityr Y)

++-identityl : {l : Level} {A : Set l} → {Y : List A} → Y ++ [] ≡ Y
++-identityl {Y = Y} = sym (++-identityr Y)

{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE ++-identityl #-}

cong3 : ∀{i j k l}{A : Set i}{B : Set j}{C : Set k}{D : Set l}{a a' : A}{b b' : B}{c c' : C}
  → (f : A → B → C → D)
  → a ≡ a'
  → b ≡ b'
  → c ≡ c'
  → f a b c ≡ f a' b' c'
cong3 f refl refl refl = refl

--rightUnit : {E : List (Set → Set)} {A : Set} {x : Eff E A} → gbind x gunit ≡ x
--rightUnit {E} {A} {Pure x} = refl
--rightUnit {E} {A} {Impure proof_FinE x y} = cong3 Impure {!!} refl (funExt λ z → rightUnit)

postulate
  boolToSetPost :
   (i j k : List (Set → Set)) (F : Set → Set) → (proofFinE : _) → (boolToSetLemma2 {F} (i ++ j) k (boolToSetLemma2 {F} i j proofFinE)) ≅
      (boolToSetLemma2 {F} i (j ++ k) proofFinE)
postulate
  boolToSetPost2 :
     (i j k : List (Set → Set)) (F : Set → Set) → (proofFinE : _) → 
   boolToSetLemma2 {F} (i ++ j) k (boolToSetLemma {F} i j proofFinE) ≅
      boolToSetLemma {F} i (j ++ k) (boolToSetLemma2 {F} j k proofFinE)

rightUnit : {Y : List (Set -> Set)} {A : Set} {x : Eff Y A} -> gbind x gunit ≡ x
rightUnit {Y} {A} {Pure x} rewrite ++-unit-r Y = refl
rightUnit {Y} {A} {Impure {F} {X} x k} rewrite ++-unit-r Y = cong (Impure x) (funExt λ x₁ → begin _ ≡⟨ refl ⟩
   gbind (k x₁) gunit
  ≡⟨ rightUnit ⟩
  _ ∎)
{-
module _ {l a b c d : _} {I : Set l} {A : I → Set a} {B : {k : I} → A k → Set b} {C : {k : I} {u : A k} → B u → Set c}
      {D : {k : I} {u : A k} {v : B u} → C v → Set d} where
  icong₃ :
           {i j : I} {x : A i} {y : A j} {u : B x} {v : B y} {uu : C u} {vv : C v} →
           i ≡ j →
           (f : {k : I} → (z : A k) → (w : B z) → (m : C w) → D m) →
           x ≅ y → u ≅ v → uu ≅ vv →
           f x u uu ≅ f y v vv
  icong₃ refl _ refl refl refl = refl
-}
myicong : {l a b : _} → {I : Set l} {A : I → Set a} {B : {k : I} → A k → Set b} {i j : I} {x : A i} {y : A j} →
          i ≡ j →
          (f : {k : I} → (z : A k) → B z) →
          x ≅ y →
          f x ≅ f y
myicong refl _ refl = refl
{-
upcastupcast : {C : Set} {i j k : List (Set → Set)}(u : Eff k C) → upcast { j ++ k } { i } (upcast { k } { j } u) ≅  upcast { k } { i ++ j } u
upcastupcast {C} {i} {j} {k} (Pure x) rewrite ++-assoc i j k = refl
upcastupcast {C} {i} {j} {k} (Impure {F} {X} {prf} x x₁) = {!!}
-}
{-
gassocHelper : {X C : Set} {i j k : List (Set → Set)} (x₁ : X → Eff j B) (g : B -> Eff k C) → (x₂ : X) → gbind (upcast {j} {i} (x₁ x₂)) g ≅ upcast {j ++ k} {i} (gbind (x₁ x₂) g)
gassocHelper x₁ g x₂ with x₁ x₂
gassocHelper x₁ g x₂ | Pure x with g x
gassocHelper {i = i} {j = j} {k = k} x₁ g x₂ | Pure x | Pure x₃ rewrite ++-assoc i j k = refl
gassocHelper {C = C} {i = i} {j = j} {k = k} x₁ g x₂ | Pure x | Impure {F} {X} proof_FinE x₃ x₄ = HE.icong₂ _
   { λ{Y'} _ → X -> Eff Y' C } (++-assoc i j k) (λ {ix} z w → Impure z x₃ w) (boolToSetAnotherLemma2 {F} {i} {j} {k})
      (funExtHE (λ x₅ → cong₂ Eff (++-assoc i j k) refl) λ x₅ → upcastupcast (x₄ x₅))
gassocHelper {C = C}  {i = i} {j = j} {k = k} x₁ g x₂ | Impure {F} {X} proof_FinE x x₃ = HE.icong₂ _
   {λ{Y'} _ → X -> Eff Y' C}
   (++-assoc i j k) (\{ix} z w → Impure z x w) (boolToSetAnotherLemma {F} {i} {j} {k}) (funExtHE (λ x₄ → cong₂ Eff (++-assoc i j k) refl) λ x₄ → gassocHelper x₃ g x₄)
-}
_∋_ : ∀ {a} (A : Set a) → A → A
A ∋ x = x

myicong₃ : {l a b c : _} → {I : Set l} {A : I → Set a} {B : {k : I} → A k → Set b} {C : {k : I} -> {kk : A k} → B kk → Set c} {i j : I} {x : A i} {y : A j} →
          {u : B x} {v : B y} →
          i ≡ j →
          (f : {k : I} → (z : A k) → (zz : B z) → C zz) →
          x ≅ y →
          u ≅ v →
          f x u ≅ f y v
myicong₃ refl _ refl refl = refl

hsubst :
  {l1 l2 : Level}
  {A    : Set l1}
  {P    : A → Set l2}
  {x x' : A}
  → x ≅ x'
  → P x
  → P x' 
hsubst {P} refl p = p


myassoc = ++-assoc
{-# REWRITE myassoc #-}


upcastupcast : {C : Set} {i j k : List (Set → Set)}(u : Eff k C) → upcast { j ++ k } { i } (upcast { k } { j } u) ≡  upcast { k } { i ++ j } u
upcastupcast {C} {i} {j} {k} (Pure x) = refl
upcastupcast {C} {i} {j} {k} (Impure {F} {X} {prf} x x₁) = cong (Impure x) (funExt λ x₂ → upcastupcast (x₁ x₂))

gbindupcast : {i j k : List (Set → Set)} {B C : Set} (g : B → Eff k C) → (nf : Eff j B) → gbind (upcast {j} {i} nf) g ≡ upcast { j ++ k } { i } (gbind nf g)
gbindupcast g (Pure n) with g n
... | Pure x = refl
... | Impure x x₁ = cong (Impure x) (funExt λ y → sym (upcastupcast (x₁ y)))
gbindupcast g (Impure n nn) = cong (Impure n) (funExt (λ x → gbindupcast g (nn x)))

gassoc : {A B C : Set} {i j k : List (Set → Set)}
         (m : Eff i A)
         (f : A -> Eff j B)
         (g : B -> Eff k C) ->
         gbind { B } { C } { i ++ j } { k } (gbind { A } { B } { i } { j } m f) g ≡ gbind {A} {C} {i} { j ++ k } m λ x → gbind (f x) g
gassoc {A} {B} {C} {i} {j} {k} (Pure x) f g with f x
gassoc {A} {B} {C} {i} {j} {k} (Pure x) f g | Pure z with g z
gassoc {A} {B} {C} {i} {j} {k} (Pure x) f g | Pure z | Pure x₁ = refl
gassoc {A} {B} {C} {i} {j} {k} (Pure x) f g | Pure z | Impure x₁ x₂ = cong (Impure x₁) (funExt λ x₃ → sym (upcastupcast (x₂ x₃)))
gassoc {A} {B} {C} {i} {j} {k} (Pure x) f g | Impure {F = F} x₁ x₂ =
  cong (Impure x₁) (funExt λ x₃ → gbindupcast {i = i} {j = j} {k = k} {B = B} {C = C} g (x₂ x₃))
gassoc {A} {B} {C} {i} {j} {k} (Impure {F} {X} x x₁) f g = cong (Impure x) (funExt λ x₂ → gassoc (x₁ x₂) f g)

{-
gassoc {A} {B} {C} {i} {j} {k} y@(Pure x) f g with f x
gassoc {A} {B} {C} {i} {j} {k} y@(Pure x) f g | Pure a  with g a
... | Pure x₁ rewrite ++-assoc i j k = HE.refl
... | Impure {F} {X} proof_FinE x₁ = {!!}
gassoc {A} {B} {C} {i} {j} {k} y@(Pure p) f g | Impure {F} {X} proof_FinE  =
    -- Heterogeneous binary congruence on `Impure`
    -- (skipping over the second parameter which stays constant)
     HE.icong₂
       _ -- Type of first parameter to `Impure`
       {λ{Y'} _ → X -> Eff Y' C}           -- Type of third parameter to `Impure`
       (++-assoc i j k)                       -- Index equality
       (\{ix} member kont -> Impure member kont) -- "Hole" to lift into
       (boolToSetPost2 i j k F proof_FinE)                           -- First parameter heteroequality
       (funExtHE (λ x₂ → cong₂ Eff (++-assoc i j k) refl) λ x₂ → ?)                              -- Third parameter heteroequality       

gassoc {A} {B} {C} {i} {j} {k} (Impure {F} {X} proof_FinE x x₁) f g = let
    kontEq = funExtHE
       (λ x₂ → cong₂ Eff (++-assoc i j k) refl)
       λ x₂ → gassoc (x₁ x₂) f g
    in
    -- Heterogeneous binary congruence on `Impure`
    -- (skipping over the second parameter which stays constant)
     HE.icong₂
       _ -- Type of first parameter to `Impure`
       {λ{Y'} _ → X -> Eff Y' C}           -- Type of third parameter to `Impure`
       (++-assoc i j k)                       -- Index equality
       (\{ix} member kont -> Impure member x kont) -- "Hole" to lift into
       (boolToSetPost i j k F proof_FinE)                            -- First parameter heteroequality
       kontEq                              -- Third parameter heteroequality       
-}

