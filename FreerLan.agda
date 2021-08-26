open import Agda.Primitive
open import Relation.Binary.PropositionalEquality
open import Data.Product

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

{- Monad -}

{- raw -}
{-
record RawMonad {l1 l2 : _} (T : Set l1 → Set l2) : Set (lsuc l1 ⊔ l2) where
    field
        return : {A : Set l1} → (x : A) → T A
        _>>=_ : {A B : Set l1} → (m : T A) → (k : A → T B) → T B 
open RawMonad{{...}}

{- laws -}
record Monad {l1 l2 : _} (T : Set l1 → Set l2) : Set (lsuc l1 ⊔ l2) where
    field
        overlap {{rmT}} : RawMonad T
        leftId : {A B : Set l1} {a : A} {f : A → T B} → (return a >>= f) ≡ f a
        rightId : {A : Set l1} {m : T A} → (m >>= return) ≡ m
        bindAssoc : {A B C : Set l1} {m : T A} {f : A → T B} {g : B → T C}
                    → (m >>= f) >>= g ≡ (m >>= λ x → f x >>= g)
open Monad {{...}}

{- Monad is a functor -}

{- raw -}


instance
    rm2f : {{RawMonad G}} → RawFunctor G
    RawFunctor.fmap rm2f = λ f x → do
       z ← x
       return (f z)
-}
variable
    l1 l2 : Level
    G : Set l1 → Set l2
{- laws -}
open ≡-Reasoning
{-
instance
    lm2f : {G : Set l1 → Set l2} → {{Monad G}} → Functor G
    Functor.rfF lm2f = rm2f
    Functor.fmapId lm2f = funext λ z → rightId
    Functor.fmapCompose lm2f f g = funext λ x → {!   !}
-}
{- Lan datatype -}

Lan : {l1 l2 l3 : _} → (G : Set l1 → Set l2) → (A : Set l3) → Set (lsuc l1 ⊔ l2 ⊔ l3)
Lan {l1} {l2} G A = Σ (Set l1) λ X → G X × (X → A)

{- Lan is a functor -}

{- raw -}
lanfmap : {l1 l2 lA lB : _} {G : Set l1 → Set l2} {A : Set lA} {B : Set lB} → (A -> B) → Lan G A → Lan G B
lanfmap f (_ , x , g) = _ , x , (f o g)
-- lanfmap f (_ , x , g) = _ , x , (f o g)

instance
    lanRawFunctor : {l3 : _} → RawFunctor (Lan {l3 = l3} G)
    RawFunctor.fmap lanRawFunctor f x = lanfmap f x

{- laws -}

instance
    lanFunctor : {l3 : _} → Functor (Lan {l3 = l3} G)
    Functor.rfF lanFunctor = lanRawFunctor
    Functor.fmapId lanFunctor = refl
    Functor.fmapCompose lanFunctor f g = refl

{- Freer datatype -}
{-
data Freer {l1 l2 l3 : _} (G : Set l1 → Set l2) (A : Set l3) : Set (lsuc l1 ⊔ l2 ⊔ l3) where
   Pure : A → Freer G A
   Impure : Lan G (Freer G A) → Freer G A

{- Freer is a monad -}

{- raw -}

RawBind : {lA lB : _} {A : Set lA} {B : Set lB} → Freer G A → (A → Freer G B) → Freer G B
RawBind (Pure x) k = k x
RawBind (Impure (fst , fst₁ , snd)) k = Impure (fst , fst₁ , λ x → RawBind (snd x) k)

instance
    freerRawMonad : {l3 : _} → RawMonad (Freer {l3 = l3} G)
    RawMonad.return freerRawMonad = Pure
    RawMonad._>>=_ freerRawMonad = RawBind

{- laws -}

freerRightId : {l3 : _} {A : Set l3} → (m : Freer G A) → RawBind m Pure ≡ m
freerRightId (Pure _) = refl
freerRightId (Impure (_ , _ , c)) = cong Impure (cong (λ x → (_ , _ , x)) (funext λ x → freerRightId _))


freerAssoc : {l3 : _} {A B C : Set l3} → (m : Freer G A) (f : A → Freer G B) (g : B → Freer G C)
    → RawBind (RawBind m f) g ≡ RawBind m λ x → RawBind (f x) g
freerAssoc (Pure x) f g = refl
freerAssoc (Impure (fst , fst₁ , snd)) f g = cong Impure (cong (_,_ fst) (cong (_,_ fst₁) (funext λ x → freerAssoc (snd x) _ _)))

instance
    freerMonad : {l3 : _} → Monad (Freer {l3 = l3} G)
    Monad.rmT freerMonad = freerRawMonad
    Monad.leftId freerMonad = refl
    Monad.rightId freerMonad = freerRightId _
    Monad.bindAssoc freerMonad {m = m} {f = f} {g = g} = freerAssoc m f g

{- true formulation of freeness / also called hoist -}
{- Freer G is free over G -}
fold : ∀ {l1 l2 l3} {F : Set l1 → Set l2} {M : Set l1 → Set l3} {A : _}
    → ({X : _} → F X → M X) → {{RawMonad M}} → Freer F A → M A
fold f (Pure x) = return x
fold f (Impure (X , x , k)) = do
       z ← f x
       fold f (k z) 


embed : ∀ {l1 l2} {F : Set l1 → Set l2} {A : _} → F A → Freer F A
embed x = Impure (_ , x , Pure)

{- TODO freeness over Lan -}
{-
foldLan : ∀ {l1 l2 l3} {F : Set l1 → Set l2} {M : Set l1 → Set l3} {A : _}
    → ({X : _} → Lan F X → M X) → {{RawMonad M}} → Freer F A → M A
foldLan f (Pure x) = return x
foldLan f (Impure x) = {!   !}
  where
     z = f {!   !}
-}
-}


{- Freer going strictly endo -}
data FreerEndo {l1 : _} (G : Set l1 → Set l1) (A : Set (lsuc l1)) : Set (lsuc l1) where
   Pure : A → FreerEndo G A
   Impure : Lan G (FreerEndo G A) → FreerEndo G A

-- should be same as Rawbind x id
fmapfse : {l1 : _} {G : Set l1 → Set l1} {A B : Set (lsuc l1)} → (A → B) → FreerEndo G A → FreerEndo G B
fmapfse f (Pure x) = Pure (f x)
fmapfse f (Impure (fst , fst₁ , snd)) = Impure (fst , fst₁ , λ z → fmapfse f (snd z))

fmapfseId : {l1 : _}{G : Set l1 → Set l1} {A : Set (lsuc l1)} (x : FreerEndo G A) → fmapfse id x ≡ id x
fmapfseId (Pure x) = refl
fmapfseId (Impure (fst , fst₁ , snd)) = cong Impure (cong (_,_ fst) (cong (_,_ fst₁) (funext λ x → fmapfseId _)))


fsepure : {l1 : _} {G : Set l1 → Set l1} {A : Set (lsuc l1)} → A → FreerEndo G A
fsepure = Pure

fsejoin : {l1 : _} {G : Set l1 → Set l1} {A : Set (lsuc l1)} → FreerEndo G (FreerEndo G A) → FreerEndo G A
fsejoin (Pure x) = x
fsejoin (Impure (fst , fst₁ , snd)) = Impure (fst , fst₁ , (fsejoin o snd))

joinlaw1 : {l1 : _} {G : Set l1 → Set l1} {A : Set (lsuc l1)} → (x : FreerEndo G (FreerEndo G (FreerEndo G A)))
 → fsejoin (fmapfse fsejoin x) ≡ fsejoin (fsejoin x)
joinlaw1 (Pure x) = refl
joinlaw1 (Impure (fst , fst₁ , snd)) = cong Impure (cong (_,_ fst) (cong (_,_ fst₁) (funext λ x → joinlaw1 (snd x))))

joinlaw21 : {l1 : _} {G : Set l1 → Set l1} {A : Set (lsuc l1)} (x : FreerEndo G A) → fsejoin (fmapfse fsepure x) ≡ x
joinlaw21 (Pure x) = refl
joinlaw21 (Impure (fst , fst₁ , snd)) = cong Impure (cong (_,_ fst) (cong (_,_ fst₁) (funext λ x → joinlaw21 (snd x))))

joinlaw22 : {l1 : _} {G : Set l1 → Set l1} {A : Set (lsuc l1)} {x : FreerEndo G A} → fsejoin (fsepure x) ≡ x
joinlaw22 = refl

joinlaw3 : {l1 : _} {G : Set l1 → Set l1} {A : Set (lsuc l1)} {B : Set (lsuc l1)} (f : A → B) (x : FreerEndo G (FreerEndo G A))
    → fsejoin (fmapfse (fmapfse f) x) ≡ fmapfse f (fsejoin x)
joinlaw3 f (Pure x) = refl
joinlaw3 f (Impure (fst , fst₁ , snd)) = cong Impure (cong (_,_ fst) (cong (_,_ fst₁) (funext λ x → joinlaw3 f (snd x))))

record RawMonadJ {l1 : _} (T : Set l1 → Set l1) : Set (lsuc l1) where
    field
        return : {A : Set l1} → (x : A) → T A
        join : {A : Set l1} → (m : T (T A)) → T A 
open RawMonadJ{{...}}

{- laws -}

record MonadJ {l1 : _} (T : Set l1 → Set l1) : Set (lsuc l1) where
    field
        overlap {{fT}} : Functor T
        overlap {{rmT}} : RawMonadJ T
        law1 : {A : Set l1} {x : T (T (T A))} → join (fmap join x) ≡ join (join x)
        law21 : {A : Set l1}{x : T A} → join (fmap return x) ≡ x
        law22 : {A : Set l1}{x : T A} → join (return x) ≡ x
        law3 : {A B : Set l1}{x : T (T A)}{f : A → B} → join (fmap (fmap f) x) ≡ fmap f (join x)
open MonadJ {{...}}

instance
    FSEMonadRaw : {l1 : _} {G : Set l1 → Set l1} → RawMonadJ (FreerEndo G)
    RawMonadJ.return FSEMonadRaw = fsepure
    RawMonadJ.join FSEMonadRaw = fsejoin

instance
    FSEFunctorRaw : {l1 : _} {G : Set l1 → Set l1} → RawFunctor (FreerEndo G)
    RawFunctor.fmap FSEFunctorRaw = fmapfse

fmapfsecomposeext : {l1 : _}{A B C : Set (lsuc l1)} {G : Set l1 → Set l1} (f : A → B) (g : C → A)
  (x : FreerEndo G C)
  → fmapfse {G = G} (f o g) x ≡ ((fmapfse f) o (fmapfse g)) x
fmapfsecomposeext f g (Pure x) = refl
fmapfsecomposeext f g (Impure (fst , snd)) = cong Impure (cong (_,_ fst)
    (cong (_,_ (proj₁ snd)) (funext λ z → fmapfsecomposeext _ _ _)))

fmapfsecompose : {l1 : _}{A B C : Set (lsuc l1)} {G : Set l1 → Set l1} (f : A → B) (g : C → A) → fmapfse {G = G} (f o g) ≡ (fmapfse f) o (fmapfse g)
fmapfsecompose f g = funext (fmapfsecomposeext _ _)

instance
    FSEFunctor : {l1 : _} {G : Set l1 → Set l1} → Functor (FreerEndo G)
    Functor.rfF FSEFunctor = FSEFunctorRaw
    Functor.fmapId FSEFunctor = funext fmapfseId
    Functor.fmapCompose FSEFunctor = fmapfsecompose

instance
    FSEMonad : {l1 : _} {G : Set l1 → Set l1} → MonadJ (FreerEndo G)
    MonadJ.fT FSEMonad = FSEFunctor
    MonadJ.rmT FSEMonad = FSEMonadRaw
    MonadJ.law1 FSEMonad {x = x} = joinlaw1 x
    MonadJ.law21 FSEMonad {x = x} = joinlaw21 x
    MonadJ.law22 FSEMonad = refl
    MonadJ.law3 FSEMonad {x = x} {f} = joinlaw3 f x

record FAlg (F : Set l1 → Set l2) (FT : Functor F) : Set (lsuc l1 ⊔ l2) where
    constructor FA
    field
        carrier : Set l1
        action : F carrier → carrier
open FAlg{{...}}

-- things keep getting in the way let's do FAlg Sigma

FAlg' : {l1 l2 : _} (F : Set l1 → Set l2) {{FF : Functor F}} → Set (lsuc l1 ⊔ l2)
FAlg' {l1} {l2} F {{FF}} = Σ (Set l1) λ carrier → F carrier → carrier

record TAlg (T : Set l1 → Set l1) (MT : MonadJ T) : Set (lsuc l1) where
    constructor TA
    field
        FoT : FAlg T (MonadJ.fT MT)
        purelaw : FAlg.action FoT o return ≡ id
        joinlaw : FAlg.action FoT o (fmap (FAlg.action FoT)) ≡ ((FAlg.action FoT) o join)

TAlg' : {l1 : _} (T : Set l1 → Set l1) {{MT : MonadJ T}} → Set (lsuc l1)
TAlg' T {{MT}} = Σ (FAlg' T {{MonadJ.fT MT}}) λ{(carrier , action) → action o return ≡ id × (action o fmap action) ≡ (action o join)}

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

liftF : ∀{l1 : Level}{E : Set l1 → Set l1}{xt : Set (lsuc l1)} → Lan E xt → FreerEndo E xt
liftF (fst , fst₁ , snd) = Impure (fst , fst₁ , λ x → Pure (snd x))

iter : ∀{l1}{E}{x : Set (lsuc l1)} → (Lan E x → x) → (FreerEndo E x → x)
iter f (Pure x) = x
iter f (Impure (fst , fst₁ , snd)) = f (fst , fst₁ , λ z → iter f (snd z))

iterAlt : ∀{l1}{E}{x : Set (lsuc l1)} (f : Lan E x → x) (z : _) → iter f (Impure z) ≡ f (lanfmap (iter f) z)
iterAlt f (fst , snd) = refl

uniter : ∀{l1}{E}{x : Set (lsuc l1)} → (FreerEndo E x → x) → (Lan E x → x)
uniter f x = f (Impure (lanfmap Pure x))

uniteriter : ∀{l1}{E}{X : Set (lsuc l1)}(x : Lan E X → X) → uniter (iter x) ≡ x
uniteriter x = refl
fst : {l1 l2 : _} {A : Set l1} {P : A → Set l2} (v : Σ A P) → A
fst (fst₁ , snd) = fst₁
_✶ : ∀{l1 ℓⱼ} {A : Set l1} {P : A → Set ℓⱼ} {a b : A} → a ≡ b → P a → P b
(refl ✶) x₁ = x₁

snd : {l1 l2 : _} {A : Set l1} {P : A → Set l2} (v : Σ A P) → P (fst v)
snd (fst₁ , snd₁) = snd₁

Σ-bycomponents : {l1 l2 : _} {A : Set l1} {P : A → Set l2} {v w : Σ A P} → 
  Σ (fst v ≡ fst w) (λ p → (p ✶) (snd v) ≡ snd w)
  → v ≡ w
Σ-bycomponents (refl , refl) = refl

-- join form
iteruniterh : ∀{l1}{E}{car : Set (lsuc l1)}(act : FreerEndo E car → car)(y : Lan E (FreerEndo E car))
  → uniter act (proj₁ y , proj₁ (proj₂ y) , λ z → act (proj₂ (proj₂ y) z)) ≡ act (Impure y)
iteruniterh act z@(_ , el , cont) = begin _
     ≡⟨ {!   !} ⟩ --- join o pure ≡ snd₁ -- equiv followed by joinlaw of algebras
    _ ∎

iteruniter : ∀{l1}{E}{X : Set (lsuc l1)}(x : FreerEndo E X → X) (z : FreerEndo E X) → iter (uniter x) z ≡ x z
iteruniter x (Pure x₁) = {!   !} -- pure law
iteruniter x (Impure x₁) =
    begin 
      uniter x
      (proj₁ x₁ ,
       proj₁ (proj₂ x₁) , (λ z → iter (uniter x) (proj₂ (proj₂ x₁) z)))
      ≡⟨ cong (uniter x) (Σ-bycomponents (refl , cong (_,_ _) (funext λ x₂ → iteruniter x _))) ⟩
        uniter x (proj₁ x₁ ,
         proj₁ (proj₂ x₁) , (λ z → x (proj₂ (proj₂ x₁) z)))
      ≡⟨ iteruniterh x x₁ ⟩
      x (Impure x₁)
    ∎

iteruniteralt : ∀{l1}{E}{X : Set (lsuc l1)}(ax : FreerEndo E X → X) (z : FreerEndo E X) → iter (uniter ax) z ≡ ax z
iteruniteralt ax (Pure x) = {!   !}
iteruniteralt ax (Impure x) = {!   !}
iteruniterexpanded : ∀{l1}{E}{X : Set (lsuc l1)}(x : FreerEndo E X → X) (z : FreerEndo E X) → iter (uniter x) z ≡ x z
iteruniterexpanded x (Pure x₁) = {!   !} -- pure law
iteruniterexpanded f w@(Impure (X , (v , k))) =
    begin 
      uniter f (X , v , (λ z → iter (uniter f) (k z)))
      ≡⟨ cong (uniter f) (Σ-bycomponents (refl , cong (_,_ _) (funext λ a → iteruniterexpanded f _))) ⟩
      uniter f (X , v , (λ z → f (k z)))
      ≡⟨ {!   !} ⟩ -- TODO very close to join law
      f w
    ∎
joinlawhelpext : {G : Set l1 → Set l1}{carrier : Set (lsuc l1)}{a : Lan G carrier → carrier}
  → (x : FreerEndo G (FreerEndo G carrier))
  → (iter a o fmapfse (iter a)) x ≡ (iter a o fsejoin) x
joinlawhelpext (Pure x) = refl
joinlawhelpext {a = a} (Impure (fst , fst₁ , snd)) = cong a (cong (_,_ fst) (cong (_,_ fst₁)
     (funext λ x → joinlawhelpext (snd x))))


joinlawhelp : {G : Set l1 → Set l1}{carrier : Set (lsuc l1)}{action : Lan G carrier → carrier}
  → (iter action o fmapfse (iter action)) ≡ (iter action o fsejoin)
joinlawhelp {l1} {G} {car} {act} = funext joinlawhelpext

{- uniter -}
algFreeFun : {G : Set l1 → Set l1} → TAlg' (FreerEndo G) → FAlg' {l1 = lsuc l1} (Lan G)
algFreeFun ((carrier , action) , purel , joinl) = carrier , λ x → action (liftF x)

{- iter -}
algFreeInv : {G : Set l1 → Set l1} → FAlg' {l1 = lsuc l1} (Lan G) → TAlg' (FreerEndo G)
algFreeInv (carrier , action) = (carrier , iter action) , refl , joinlawhelp

{- uniter o iter = id -}
algFreeSection : {G : Set l1 → Set l1} → section (algFreeFun {G = G}) algFreeInv
algFreeSection {l1} {G} z = refl
{-
fst : {l1 l2 : _} {A : Set l1} {P : A → Set l2} (v : Σ A P) → A
fst (fst₁ , snd) = fst₁
_✶ : ∀{l1 ℓⱼ} {A : Set l1} {P : A → Set ℓⱼ} {a b : A} → a ≡ b → P a → P b
(refl ✶) x₁ = x₁

snd : {l1 l2 : _} {A : Set l1} {P : A → Set l2} (v : Σ A P) → P (fst v)
snd (fst₁ , snd₁) = snd₁
Σ-bycomponents : {l1 l2 : _} {A : Set l1} {P : A → Set l2} {v w : Σ A P} → 
  Σ (fst v ≡ fst w) (λ p → (p ✶) (snd v) ≡ snd w)
  → v ≡ w
Σ-bycomponents (refl , refl) = refl

uip : {l1 : _} {X : Set l1}{x y : X} {a b : x ≡ y} → a ≡ b
uip {l1} {X} {x} {.x} {refl} {refl} = refl

conghelp : {l1 l2 : _} {X : Set l1} {Y : Set l2} → {f g : X → Y} → f ≡ g → ∀ x → f x ≡ g x
conghelp refl x₁ = refl

algFreeRetractModIdentities : {G : Set l1 → Set l1} → (z : TAlg' (FreerEndo G)) → fst (algFreeInv (algFreeFun z)) ≡ fst z
algFreeRetractModIdentities {G = G} ((carr , act) , purel , joinl) = Σ-bycomponents (refl , funext λ w → help w)
    where
        help : (w : FreerEndo G carr) → _ ≡ act w
        help (Pure x) = sym (conghelp purel x)
        help (Impure z) = {!   !}
-}

{- iter o uniter = id -}
algFreeRetract : {G : Set l1 → Set l1} → retract (algFreeFun {G = G}) algFreeInv
algFreeRetract a = {!   !}

-- FAlg.carrier (algFreeFun (TA purelaw joinlaw)) = carrier
-- FAlg.action (algFreeFun (TA purelaw joinlaw)) x = action (liftF x)
{-
algFreeInv : {G : Set l1 → Set l1} → FAlg {l1 = lsuc l1} (Lan G) → TAlg (FreerEndo G)
{-
algFreeInv record { carrier = carrier ; action = action }
 = record { FoT = record { carrier = carrier ; action = iter action }
  ; purelaw = refl ; joinlaw
    = joinlawhelp}
-}
FAlg.carrier (TAlg.FoT (algFreeInv (FA carrier₁ action₁))) = carrier₁
FAlg.action (TAlg.FoT (algFreeInv (FA carrier₁ action₁))) = iter action₁
TAlg.purelaw (algFreeInv x) = refl
TAlg.joinlaw (algFreeInv x) = joinlawhelp


algFreeSection : {G : Set l1 → Set l1} → section (algFreeFun {G = G}) algFreeInv
algFreeSection {l1} {G} z = refl


algFreeRetract : {G : Set l1 → Set l1} → retract (algFreeFun {G = G}) algFreeInv
algFreeRetract (TA purelaw joinlaw) = {!   !}

algFree : {G : Set l1 → Set l1} → Iso (TAlg (FreerEndo G)) (FAlg {l1 = lsuc l1} (Lan G))
Iso.fun algFree = algFreeFun
Iso.inv algFree = {!   !}
Iso.rightInv algFree = {!   !}
Iso.leftInv algFree = {!   !}
-}

{- Freer quotiented by G -}

{- quotiented freer is monadic and admits handling constructs -}

