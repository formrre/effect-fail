open import Agda.Primitive
open import Relation.Binary.PropositionalEquality
open import Data.Product
open ≡-Reasoning

postulate funext : {i j : Level} {X : Set i} {Y : X → Set j} {f g : (x : X) → Y x}
                → ((x : X) → f x ≡ g x) → f ≡ g

{- auxilliary -}
id : {l : _} {A : Set l} → A → A
id x = x

_o_ : {l1 l2 l3 : _} {A : Set l1} {B : Set l2} {C : Set l3} → (B → C) → (A → B) → (A → C)
(f o g) = λ x → f (g x)
{- Functor -}

{- raw -}
record RawFunctor {l1 l2 : _} (F : Set l1 → Set l2) : Set (lsuc l1 ⊔ l2) where
    field
      fmap : {A B : Set l1} → (f : A → B) → (x : F A) → F B
open RawFunctor{{...}}

{- laws -}
record Functor {l1 l2 : _} (F : Set l1 → Set l2) : Set (lsuc l1 ⊔ l2) where
    field
        overlap {{rfF}} : RawFunctor F
        fmapId : {A : Set l1} → fmap {A = A} id ≡ id
        fmapCompose : {A B C : Set l1} (f : B → C) (g : A → B) → fmap (f o g) ≡ fmap f o fmap g
open Functor {{...}}

data Lan {l1 l2 l3 : _} (G : Set l1 → Set l2) (A : Set l3) : Set (lsuc l1 ⊔ l2 ⊔ l3) where
    FMap : {X : Set l1} → (lx : G X) → (lk : X → A) → Lan G A

lanfmap : {l1 l2 lA lB : _} {G : Set l1 → Set l2} {A : Set lA} {B : Set lB} → (f : A -> B) → (x : Lan G A) → Lan G B
lanfmap f (FMap lx lk) = FMap lx (f o lk)

instance
    lanRawFunctor : {l1 l2 l3 : _} {G : Set l1 → Set l2} → RawFunctor (Lan {l3 = l3} G)
    RawFunctor.fmap lanRawFunctor f x = lanfmap f x

instance
    lanFunctor : {l1 l2 l3 : _} {G : Set l1 → Set l2} → Functor (Lan {l3 = l3} G)
    Functor.rfF lanFunctor = lanRawFunctor
    Functor.fmapId lanFunctor {A} = funext λ{(FMap lx lk) → refl}
    Functor.fmapCompose lanFunctor f g = funext λ{(FMap lx lk) → refl}

data FreerEndo {l1 : _} (G : Set l1 → Set l1) (A : Set (lsuc l1)) : Set (lsuc l1) where
   Pure : A → FreerEndo G A
   Impure : Lan G (FreerEndo G A) → FreerEndo G A

fmapfse : {l1 : _} {G : Set l1 → Set l1} {A B : Set (lsuc l1)} → (A → B) → FreerEndo G A → FreerEndo G B
fmapfse f (Pure x) = Pure (f x)
fmapfse f (Impure (FMap lx lk)) = Impure (FMap lx λ z → fmapfse f (lk z))

fmapfseId : {l1 : _}{G : Set l1 → Set l1} {A : Set (lsuc l1)} (x : FreerEndo G A) → fmapfse id x ≡ id x
fmapfseId (Pure x) = refl
fmapfseId (Impure (FMap lx lk)) = cong Impure (cong (FMap lx) (funext λ x → fmapfseId _))

fmapfsecomposeext : {l1 : _}{A B C : Set (lsuc l1)} {G : Set l1 → Set l1} (f : A → B) (g : C → A)
  (x : FreerEndo G C)
  → fmapfse {G = G} (f o g) x ≡ ((fmapfse f) o (fmapfse g)) x
fmapfsecomposeext f g (Pure x) = refl
fmapfsecomposeext f g (Impure (FMap lx lk)) = cong (Impure o FMap lx) (funext λ x → fmapfsecomposeext f g (lk x))

fmapfsecompose : {l1 : _}{A B C : Set (lsuc l1)} {G : Set l1 → Set l1} (f : A → B) (g : C → A) → fmapfse {G = G} (f o g) ≡ (fmapfse f) o (fmapfse g)
fmapfsecompose f g = funext (fmapfsecomposeext _ _)

fsepure : {l1 : _} {G : Set l1 → Set l1} {A : Set (lsuc l1)} → A → FreerEndo G A
fsepure = Pure

fsejoin : {l1 : _} {G : Set l1 → Set l1} {A : Set (lsuc l1)} → FreerEndo G (FreerEndo G A) → FreerEndo G A
fsejoin (Pure x) = x
fsejoin (Impure (FMap lx lk)) = Impure (FMap lx λ x → fsejoin (lk x))

joinlaw1 : {l1 : _} {G : Set l1 → Set l1} {A : Set (lsuc l1)} → (x : FreerEndo G (FreerEndo G (FreerEndo G A)))
 → fsejoin (fmapfse fsejoin x) ≡ fsejoin (fsejoin x)
joinlaw1 (Pure x) = refl
joinlaw1 (Impure (FMap lx lk)) = cong (Impure o FMap lx) (funext λ x → joinlaw1 (lk x)) {- why does this hole not _ fill? -}


joinlaw21 : {l1 : _} {G : Set l1 → Set l1} {A : Set (lsuc l1)} (x : FreerEndo G A) → fsejoin (fmapfse fsepure x) ≡ x
joinlaw21 (Pure x) = refl
joinlaw21 (Impure (FMap lx lk)) = cong (Impure o FMap lx) (funext λ x → joinlaw21 (lk x))

joinlaw22 : {l1 : _} {G : Set l1 → Set l1} {A : Set (lsuc l1)} {x : FreerEndo G A} → fsejoin (fsepure x) ≡ x
joinlaw22 = refl


joinlaw3 : {l1 : _} {G : Set l1 → Set l1} {A : Set (lsuc l1)} {B : Set (lsuc l1)} (f : A → B) (x : FreerEndo G (FreerEndo G A))
    → fsejoin (fmapfse (fmapfse f) x) ≡ fmapfse f (fsejoin x)
joinlaw3 f (Pure x) = refl
joinlaw3 f (Impure (FMap lx lk)) = cong (Impure o FMap lx) (funext λ x → joinlaw3 _ (lk x))


liftF : ∀{l1 : Level}{E : Set l1 → Set l1}{xt : Set (lsuc l1)} → Lan E xt → FreerEndo E xt
liftF (FMap lx lk) = Impure (FMap lx (Pure o lk))


iter : ∀{l1}{E}{x : Set (lsuc l1)} → (Lan E x → x) → (FreerEndo E x → x)
iter f (Pure x) = x
iter f (Impure (FMap lx lk)) = f (FMap lx (λ z → iter f (lk z)))

iterAlt : ∀{l1}{E}{x : Set (lsuc l1)} (f : Lan E x → x) (z : _) → iter f (Impure z) ≡ f (lanfmap (iter f) z)
iterAlt f (FMap lx lk) = refl

uniter : ∀{l1}{E}{x : Set (lsuc l1)} → (FreerEndo E x → x) → (Lan E x → x)
uniter f x = f (Impure (lanfmap Pure x))

uniteriter : ∀{l1}{E}{X : Set (lsuc l1)}(x : Lan E X → X) → uniter (iter x) ≡ x
uniteriter x = funext λ{(FMap lx lk) → refl}

iteruniter : ∀{l1}{E}{X : Set (lsuc l1)}(act : FreerEndo E X → X)  
  (purel : act o fsepure ≡ id)
  (joinl : act o fmapfse act ≡ act o fsejoin)
  (z : FreerEndo E X)
  → 
  iter (uniter act) z ≡ act z
iteruniter act purel joinl (Pure y) = sym (cong-app purel _) {- pure law -}
iteruniter act purel joinl m@(Impure z@(FMap lx lk)) = begin
    _
    ≡⟨⟩
      (let f = uniter act in f (lanfmap (iter f) z))
    ≡⟨⟩
      uniter act (lanfmap (iter (uniter act)) z)
    ≡⟨ cong (uniter act) (cong (FMap lx) (funext λ x → iteruniter act purel joinl (lk x))) ⟩
      uniter act (lanfmap act z)
    ≡⟨⟩
      (act o fmapfse act) (Impure (FMap lx (Pure o lk)))
    ≡⟨⟩
      (act o fmapfse act) (Impure (lanfmap Pure (FMap lx lk)))
    ≡⟨⟩
      (act o fmapfse act) w
    ≡⟨ cong-app joinl _ ⟩ -- join law
     (act o fsejoin) w
    ≡⟨⟩
    act (Impure z) ∎
  where
     w =  (Impure (FMap lx (Pure o lk)))


iteruniterext : ∀{l1}{E}{X : Set (lsuc l1)}(act : FreerEndo E X → X)  
  (purel : act o fsepure ≡ id)
  (joinl : act o fmapfse act ≡ act o fsejoin)
  → 
  iter (uniter act) ≡ act
iteruniterext act purel joinl = funext λ x → iteruniter act purel joinl x

module _ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} where
  section : (f : A → B) → (g : B → A) → Set ℓ'
  section f g = ∀ b → f (g b) ≡ b

  -- NB: `g` is the retraction!
  retract : (f : A → B) → (g : B → A) → Set ℓ
  retract f g = ∀ a → g (f a) ≡ a

record Iso {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') : Set (ℓ ⊔ ℓ') where
  no-eta-equality
  constructor iso
  field
    fun : A → B
    inv : B → A
    rightInv : section fun inv
    leftInv : retract fun inv


record FAlg {l1 l2 : _} (F : Set l1 → Set l2) (FT : Functor F) : Set (lsuc l1 ⊔ l2) where
    constructor FA
    field
        carrier : Set l1
        action : F carrier → carrier
open FAlg{{...}}


record RawMonadJ {l1 : _} (T : Set l1 → Set l1) : Set (lsuc l1) where
    field
        return : {A : Set l1} → (x : A) → T A
        join : {A : Set l1} → (m : T (T A)) → T A 
open RawMonadJ{{...}}

record MonadJ {l1 : _} (T : Set l1 → Set l1) : Set (lsuc l1) where
    field
        overlap {{fT}} : Functor T
        overlap {{rmT}} : RawMonadJ T
        law1 : {A : Set l1} {x : T (T (T A))} → join (fmap join x) ≡ join (join x)
        law21 : {A : Set l1}{x : T A} → join (fmap return x) ≡ x
        law22 : {A : Set l1}{x : T A} → join (return x) ≡ x
        law3 : {A B : Set l1}{x : T (T A)}{f : A → B} → join (fmap (fmap f) x) ≡ fmap f (join x)

record TAlg {l1 : _} (T : Set l1 → Set l1) (MT : MonadJ T) : Set (lsuc l1) where
    constructor TA
    field
        FoT : FAlg T (MonadJ.fT MT)
        purelaw : FAlg.action FoT o return ≡ id
        joinlaw : FAlg.action FoT o (fmap (FAlg.action FoT)) ≡ ((FAlg.action FoT) o join)

instance
    rawFreerFunctor : {l1 : _} {G : Set l1 → Set l1} → RawFunctor (FreerEndo G)
    RawFunctor.fmap rawFreerFunctor = fmapfse

instance
    freerFunctor : {l1 : _} {G : Set l1 → Set l1} → Functor (FreerEndo G)
    Functor.rfF freerFunctor = rawFreerFunctor
    Functor.fmapId freerFunctor = funext fmapfseId
    Functor.fmapCompose freerFunctor = fmapfsecompose

instance
    rawFreerMonadJ : {l1 : _} {G : Set l1 → Set l1} → RawMonadJ (FreerEndo G)
    RawMonadJ.return rawFreerMonadJ = fsepure
    RawMonadJ.join rawFreerMonadJ = fsejoin

instance
    freerMonadJ : {l1 : _} {G : Set l1 → Set l1} → MonadJ (FreerEndo G)
    MonadJ.fT freerMonadJ = freerFunctor
    MonadJ.rmT freerMonadJ = rawFreerMonadJ
    MonadJ.law1 freerMonadJ {x = x} = joinlaw1 x
    MonadJ.law21 freerMonadJ {x = x} = joinlaw21 x
    MonadJ.law22 freerMonadJ = joinlaw22
    MonadJ.law3 freerMonadJ {x = x} {f = f} = joinlaw3 f x


{-
record FAlg {l1 l2 : _} (F : Set l1 → Set l2) (FT : Functor F) : Set (lsuc l1 ⊔ l2) where
    constructor FA
    field
        carrier : Set l1
        action : F carrier → carrier
open FAlg{{...}}
-}

FAlgΣ : {l1 l2 : _} (F : Set l1 → Set l2) (FT : Functor F) → Set (lsuc l1 ⊔ l2)
FAlgΣ {l1} F FT = Σ (Set l1) λ x → F x → x

{-
record TAlg {l1 : _} (T : Set l1 → Set l1) (MT : MonadJ T) : Set (lsuc l1) where
    constructor TA
    field
        FoT : FAlg T (MonadJ.fT MT)
        purelaw : FAlg.action FoT o return ≡ id
        joinlaw : FAlg.action FoT o (fmap (FAlg.action FoT)) ≡ ((FAlg.action FoT) o join)
-}

TAlgΣ : {l1 : _} (T : Set l1 → Set l1) {{MT : MonadJ T}} → Set (lsuc l1)
TAlgΣ T {{MT}} = Σ (FAlgΣ T (MonadJ.fT MT)) λ{(car , act) → (act o return) ≡ id × (act o fmap act) ≡ (act o join)}
{-
algFree : {l1 : _} {G : Set l1 → Set l1} → Iso (TAlg (FreerEndo G) freerMonadJ) (FAlg (Lan G) lanFunctor)
Iso.fun algFree (TA (FA carrier₁ action₁) purelaw joinlaw) = FA carrier₁ (uniter action₁)
Iso.inv (algFree {G = G}) (FA carrier₁ action₁) = let
    w x = b x
   in
    TA (FA carrier₁ (iter action₁)) refl (funext w)
    where
     b : (x : FreerEndo G (FreerEndo G carrier₁)) → (iter action₁ o fmapfse (iter action₁)) x ≡ (iter action₁ o fsejoin) x
     b (Pure x) = refl
     b (Impure (FMap lx lk)) = cong (action₁ o FMap lx) (funext λ x → b (lk x))
Iso.rightInv algFree (FA carrier₁ action₁) = cong (FA carrier₁) (uniteriter _)
Iso.leftInv algFree (TA (FA carrier₁ action₁) purelaw joinlaw)
  = {!   !}
-}
_✶ : ∀{l1 ℓⱼ} {A : Set l1} {P : A → Set ℓⱼ} {a b : A} → a ≡ b → P a → P b
(refl ✶) x₁ = x₁

Σ-bycomponents : {l1 l2 : _} {A : Set l1} {P : A → Set l2} {v w : Σ A P} → 
  Σ (proj₁ v ≡ proj₁ w) (λ p → (p ✶) (proj₂ v) ≡ proj₂ w)
  → v ≡ w
Σ-bycomponents (refl , refl) = refl

UIP : {l : _} {X : Set l} → ∀{x x' : X} → ∀{r s : x ≡ x'} → r ≡ s
UIP {r = refl} {refl} = refl

algFreeΣ : {l1 : _} {G : Set l1 → Set l1} → Iso (TAlgΣ (FreerEndo G)) (FAlgΣ {l1 = (lsuc l1)} (Lan G) lanFunctor)
Iso.fun algFreeΣ ((carrier , action) , laws) = carrier , uniter action
Iso.inv (algFreeΣ {G = G}) (carrier , action) = (carrier , iter action) , refl , 
    let w x = b x
      in funext w
    where
      b : (x : FreerEndo G (FreerEndo G carrier)) → (iter action o fmapfse (iter action)) x ≡ (iter action o fsejoin) x
      b (Pure x) = refl
      b (Impure (FMap lx lk)) = cong (action o FMap lx) (funext λ x → b (lk x))
Iso.rightInv algFreeΣ (fst , snd) = cong (_,_ fst) (uniteriter _)
Iso.leftInv algFreeΣ ((carrier , action) , purel , joinl) = Σ-bycomponents (Σ-bycomponents (refl , iteruniterext action purel joinl) ,
    Σ-bycomponents (UIP , UIP))