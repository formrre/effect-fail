{-# OPTIONS --without-K #-}
module EffectFail where

open import Agda.Primitive
open import Relation.Binary.PropositionalEquality

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

funExt : ∀ {l1 l2} {A : Set l1} {B : A → Set l2} {f g : (x : A) → B x} →
           ((x : A) → f x ≡ g x) → f ≡ g
funExt = {!!}

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
  Impure : {F : Set -> Set} {X : Set} -> (proof_FinE : boolToSet (inSetList F E)) -> F X -> (X -> Eff E A) -> Eff E A

_>>>_ : {l1 l2 l3 : Level} -> {M : Set l1 -> Set l2} -> {B C : Set l1} -> {A : Set l3} -> (A -> M B) -> (B -> M C) -> {{RM : RMonad M}} -> (A -> M C)
(f >>> g) ⦃ record { pure = pure ; _>>=_ = _>>=_ ; rightId = rightId ; leftId = leftId ; bindAssoc = bindAssoc } ⦄ x = (f x) >>= g

-- IDEA: (08/10/2020) This could be a graded monad as well

effbind : {E : List (Set -> Set)} {A B : Set} -> Eff E A -> (A -> Eff E B) -> Eff E B
effbind (Pure x) k = k x
effbind {E} {A} {B} (Impure {F} prf f cont) k = Impure {F = F} prf f λ x → effbind (cont x) k

effpure : {E : List (Set -> Set)} {A : Set} -> A -> Eff E A
effpure = Pure

effLeftId : {E : List (Set -> Set)} {A B : Set} -> (x : A) -> (f : A -> Eff E B) -> effbind (effpure x) f ≡ f x
effLeftId x f = refl

effRightId : {E : List (Set -> Set)} {A : Set} -> (x : Eff E A) -> effbind x effpure ≡ x
effRightId (Pure x) = refl
effRightId (Impure x y z) = cong (Impure x y) (funExt λ w → effRightId (z w))

effBindAssoc : {E : List (Set -> Set)} {A B C : Set} -> (x : Eff E A) -> (f : A -> Eff E B) -> (g : B -> Eff E C) -> effbind (effbind x f) g ≡ effbind x λ y → effbind (f y) g
effBindAssoc (Pure x) f g = refl
effBindAssoc (Impure x u w) f g = cong (Impure x u) (funExt λ z → effBindAssoc (w z) f g)

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
run (Impure () _ _)

runFail : EffFail [] A -> Maybe A
runFail (MT x) = run x

-- Smart constructor for `Impure`
send : {E : List (Set -> Set)} {T : Set -> Set} {V : Set} -> (T V) -> boolToSet (inSetList T E) -> Eff E V
send {E} {T} {V} x prf = Impure {E} {V} {T} {V} prf x Pure

-- Smart constructor `Impure` but inside of a MaybeT
sendFail : {E : List (Set -> Set)} {T : Set -> Set} {V : Set} -> (T V) -> boolToSet (inSetList T E) -> EffFail E V
sendFail {E} {T} {V} x prf = MT (Impure {F = T} {X = V} prf x λ x → Pure (Just x))

data Either {l1 l2 : Level} (A : Set l1) (B : Set l2) : Set (l1 ⊔ l2) where
  Left : A -> Either A B
  Right : B -> Either A B

open import Data.Nat

{- TODO to provide these nicely in our setting we need type case -}
decomp : {F : Set -> Set} {X : Set} -> Either ℕ (F X)
decomp = {!!}

-- IDEA: (08/10/2020) postulate deleteAll (and its relevant properties) instead?

handleRelay : {ES : List (Set -> Set)} {E : Set -> Set} {A B : Set}
   -> (A -> Eff ES B) -> ((∀ {V : Set} → E V -> Eff ES B)) -> Eff ES A -> Eff ES B {- deleteAll E ES ; TODO -}
handleRelay ret h (Pure x) = ret x
handleRelay ret h (Impure prf f cont) = {!!}
