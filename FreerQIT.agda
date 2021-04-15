{-# OPTIONS --cubical #-}

module FreerQIT where

open import Cubical.Foundations.Everything
open import Agda.Primitive

{-
    Note: doing Lan (Freer f a) behaves antimodularly
    let's see why
-}


{- let's analyse and gradually decompose Eff -}

open import Cubical.Data.List
-- Free monad indexed by set of effects

data Eff (E : List (Set -> Set)) (A : Set) : Set₁ where
  Pure : A -> Eff E A
  Impure : {F : Set -> Set} {X : Set} -> F X -> (X -> Eff E A) -> Eff E A

effbind : {E : List (Set -> Set)} {A B : Set} -> Eff E A -> (A -> Eff E B) -> Eff E B
effbind (Pure x) k = k x
effbind {E} {A} {B} (Impure {F} {X} f cont) k = Impure {F = F} {X} f λ x → effbind (cont x) k

effpure : {E : List (Set -> Set)} {A : Set} -> A -> Eff E A
effpure = Pure

-- non-indexed version

data Eff2 (E : Set -> Set) (A : Set) : Set₁ where
  Pure : A -> Eff2 E A
  Impure : {X : Set} -> E X -> (X -> Eff2 E A) -> Eff2 E A

eff2pure : {E : Set -> Set} {A : Set} -> A -> Eff2 E A
eff2pure = Pure

eff2bind : {E : Set -> Set} {A B : Set} -> Eff2 E A -> (A -> Eff2 E B) -> Eff2 E B
eff2bind (Pure x) k = k x
eff2bind (Impure {X = X} f cont) k = Impure {X = X} f λ x → eff2bind (cont x) k

-- factoring out the left kan extension

data Lan {l1 l2 l3 : Level} (G : Set l1 -> Set l2) (A : Set l3) : Set (lsuc l1 ⊔ l2 ⊔ l3) where
    FMap : (X : Set l1) -> G X -> (X -> A) -> Lan G A

data Eff3 (E : Set -> Set) (A : Set) : Set₁ where
  Pure3 : A -> Eff3 E A
  Impure3 : Lan E (Eff3 E A) -> Eff3 E A

eff3pure : {E : Set -> Set} {A : Set} -> A -> Eff3 E A
eff3pure = Pure3

eff3bind : {E : Set -> Set} {A B : Set} -> Eff3 E A -> (A -> Eff3 E B) -> Eff3 E B
eff3bind (Pure3 x) k = k x
eff3bind (Impure3 (FMap X x cont)) k = Impure3 (FMap X x λ y → eff3bind (cont y) k)

-- factor out Lan's fmap from bind
lanfmap : {l1 l2 l3 : _} {G : Set l1 → Set l2} {A B : Set l3} -> (A -> B) -> Lan G A -> Lan G B
lanfmap x (FMap X a b) = FMap X a λ y → x (b y)

{-# TERMINATING #-}
{- factoring out lan fmap is obviously terminating by isomorphism to eff3bind -}
eff3bindalt : {E : Set -> Set} {A B : Set} -> Eff3 E A -> (A -> Eff3 E B) -> Eff3 E B
eff3bindalt (Pure3 x) k = k x
eff3bindalt (Impure3 X) k = Impure3 (lanfmap (λ x → eff3bindalt x k) X)


eqv1 : {E : Set -> Set} {A B : Set} -> (x : Eff3 E A) -> (y : _) -> eff3bind {E} {A} {B} x y ≡ eff3bindalt {E} {A} {B} x y
eqv1 (Pure3 x) y = refl
eqv1 {E} {A} {B} (Impure3 (FMap X x x₁)) y = cong Impure3 (cong (FMap X x) (funExt λ z → eqv1 (x₁ z) y))

{- Is it possible that possible non-termination of eff3bindalt makes this proof absurd? -}
eqv : {E : Set -> Set} {A B : Set} -> eff3bind {E} {A} {B} ≡ eff3bindalt {E} {A} {B}
eqv = funExt λ x → funExt λ y → eqv1 x y

{- prove algebraically-free for Eff3 i.e. Lan E-Alg Endo <-> Eff3 E-Alg Mnd
   prove that   Lan E-alg endo is the free algebra for QIT E
-}

{- definition of EndoFunctor -}

id : {l : _} {A : Set l} -> A -> A
id x = x

compose : {l : _} {A B C : Set l} -> (B -> C) -> (A -> B) -> (A -> C)
compose g f x = g (f x)

record EndoFunctor {l1 l2} (F : Set l1 -> Set l2) : Set (lsuc l1 ⊔ l2) where
  field
    fmap : ∀{A B} -> (A -> B) -> F A -> F B
    fmapid : ∀{A} -> (x : F A) -> fmap id x ≡ x

{- Lan is endo -}
EndoLan : {l1 l2 l3 : Level} → (X : Set l1 -> Set l2) -> EndoFunctor {l1 = l3} (Lan X)
EndoFunctor.fmap (EndoLan X) = lanfmap
EndoFunctor.fmapid (EndoLan X) (FMap Y x y) = cong₂ (FMap Y) refl (funExt λ z → refl)

{- definition of Monad -}

record Monad {l1 l2} (M : Set l1 -> Set l2) : Set (lsuc l1 ⊔ l2) where
  field
    pure : ∀{A} -> A -> M A
    bind : ∀{A B} -> M A -> (A -> M B) -> M B {- note join does not work as it require l1 = l2 -}
    rightId : ∀{A} -> (m : M A) -> bind m pure ≡ m
    leftId : ∀{A B} -> (x : A) (m : A -> M B) -> bind (pure x) m ≡ m x
    assocB : ∀{A B C} -> (m : M A) (f : A -> M B) (g : B -> M C) -> bind (bind m f) g ≡ bind m λ x → bind (f x) g

{- Eff3 is a monad -}

Eff3rightId : {E : Set -> Set} {A : Set} -> (m : Eff3 E A) → eff3bind m Pure3 ≡ m
Eff3rightId (Pure3 x) = refl
Eff3rightId (Impure3 (FMap X x y)) = cong Impure3 (cong (FMap X x) (funExt λ z → Eff3rightId (y z)))

Eff3assoc : {E : Set -> Set} {A B C : Set} -> (m : Eff3 E A) -> (f : A -> Eff3 E B) -> (g : B -> Eff3 E C) → eff3bind (eff3bind m f) g ≡ eff3bind m λ x → eff3bind (f x) g
Eff3assoc (Pure3 x) f g = refl
Eff3assoc (Impure3 (FMap X x y)) f g = cong Impure3 (cong (FMap X x) (funExt λ z → Eff3assoc (y z) f g))

MndEff3 : (E : Set -> Set) -> Monad (Eff3 E)
Monad.pure (MndEff3 E) = eff3pure
Monad.bind (MndEff3 E) = eff3bind
Monad.rightId (MndEff3 E) = Eff3rightId
Monad.leftId (MndEff3 E) x m = refl
Monad.assocB (MndEff3 E) = Eff3assoc

{- TODO definition of algebra for EndoFunctor -}
EndoAlg : {l1 l2 : _} {F : Set l1 → Set l2} -> EndoFunctor F → Set (ℓ-max (ℓ-suc l1) l2)
EndoAlg {l1} {_} {F} EF = Σ (Set l1) (\U -> F U -> U)

EndoAlgMorph : {l1 l2 : _} {F : Set l1 → Set l2} -> (f : EndoFunctor F) → EndoAlg f -> EndoAlg f -> Set {!!}
EndoAlgMorph {l1} {_} {F} EF (X , f) (Y , g) = {!!}

{- TODO definition of algebra for a monad -}
MndAlg : {l1 l2 : _} {T : Set l1 → Set l2} -> Monad T → Set {!   !}
MndAlg MT = {!   !}

{- monad ( TODO prove uniqueness?) determines a functor -}
mnd-to-endo : {l1 l2 : _} {T : Set l1 → Set l2} → Monad T → EndoFunctor T
EndoFunctor.fmap (mnd-to-endo record { pure = pure ; bind = bind ; rightId = rightId ; leftId = leftId ; assocB = assocB }) f x
   = bind x λ y → pure (f y)
EndoFunctor.fmapid (mnd-to-endo record { pure = pure ; bind = bind ; rightId = rightId ; leftId = leftId ; assocB = assocB }) x
  = rightId x


{- defining algebraic-freeness of x
   monad for f is algebraic free if endoalg is equivalent to mndalg -}
{- TODO do i need to switch to Equiv due to subtle issues of levels and univalence? i believe isomorphisms should be enough -}
algFree : {l1 l2 : _} {T : Set l1 → Set l2} -> Monad T → Set ?
algFree x = Iso (MndAlg x) (EndoAlg (mnd-to-endo x))

{- TODO free as the standard definition of free with respect to forgetful functor Mnd(C) -> End(C)
      should be the type of standard handlers instantiated at Lan
 -}
free : {l : _} {T : Set l → Set l} -> Monad T → Set {!   !}
free = {!   !}


algFreeEff : {E : Set -> Set} → algFree (MndEff3 E)
Iso.fun algFreeEff = {!   !}
Iso.inv algFreeEff = {!   !}
Iso.rightInv algFreeEff = {!   !}
Iso.leftInv algFreeEff = {!   !}

freeEff : {!   !}
freeEff = {!   !}
{- TODO monad free over Lan means its algebras are given by the underlying QIT of Lan 
   TLDR need abstract quotient type to even state this in what sense?
  as a QIT determined by datatype and R, also need a sum of these quotients -}

{- the sum of 2 quotients should be a sum (+) of their underlying sets and the sum (+) of their quotients
   thus just standard type theoretic sum
 -}