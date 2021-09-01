{-# OPTIONS --cubical #-}

open import Agda.Primitive
open import Cubical.Foundations.Everything

variable
  l1 l2 l3 : Level
  A B C S : Set l1
data Lan (G : Set l1 → Set l2) (A : Set l3) : Set (lsuc l1 ⊔ l2 ⊔ l3) where
    FMap : {X : Set l1} → G X → (X -> A) -> Lan G A

data P⊤ {lT : _} : Set lT where
    Ptt : P⊤
data SQ (S : Set l1) : Set l1 -> Set (lsuc l1) where
    Put : S -> SQ S P⊤
    Get : SQ S S

data FreeSQ (S : Set l1) (A : Set l1) : Set (lsuc l1) where
    Pure : A -> FreeSQ S A
    Impure : Lan (SQ S) (FreeSQ S A) -> FreeSQ S A

bind : FreeSQ S A -> (k : A -> FreeSQ S B) -> FreeSQ S B
bind (Pure x) k = k x
bind (Impure (FMap x x₁)) k = Impure (FMap x λ z → bind (x₁ z) k)

bindRightId : (m : FreeSQ S A) → bind m Pure ≡ m
bindRightId (Pure x) = refl
bindRightId (Impure (FMap x x₁)) = cong Impure (cong (FMap x) (funExt λ z → bindRightId _))

bindLeftId : (x : A) (h : A -> FreeSQ S A) → bind (Pure x) h ≡ h x
bindLeftId x h = refl

bindAssoc : (m : FreeSQ S A) (g : A -> FreeSQ S B) (h : B -> FreeSQ S C) -> bind (bind m g) h ≡ bind m λ x → bind (g x) h
bindAssoc (Pure x) g h = refl
bindAssoc (Impure (FMap x x₁)) g h = cong Impure (cong (FMap x) (funExt λ z → bindAssoc (x₁ z) g h))

id : A -> A
id x = x

data FreerESQ (S : Set l1) (A : Set l1) : Set (lsuc l1) where
  PureSQ : A -> FreerESQ S A
  ImpureSQ : {X : Set l1} -> SQ S X -> (X -> FreerESQ S A) -> FreerESQ S A


handle : S -> FreerESQ S A -> A
handle s (PureSQ x) = x
handle s (ImpureSQ (Put x) x₁) = handle x (x₁ Ptt)
handle s (ImpureSQ Get x₁) = handle s (x₁ s)

data ExFreerEqns (S : Set l1) (A : Set l1) : Set (lsuc l1) where
  PureEqn : A -> ExFreerEqns S A
  ImpureEqn : {X : Set l1} -> (x : SQ S X) -> (k : X -> ExFreerEqns S A) -> ExFreerEqns S A
  GetPutEqn : (m : ExFreerEqns S A) -> ImpureEqn Get (λ z → ImpureEqn (Put z) λ x → m) ≡ m
  PutPutEqn : (s' : S) (s : S) (m : ExFreerEqns S A) -> ImpureEqn (Put s') (λ _ → ImpureEqn (Put s) λ _ → m) ≡ ImpureEqn (Put s) λ _ → m
  PutGetEqn : (s : S) (k : S -> ExFreerEqns S A) -> ImpureEqn (Put s) (λ{_ → ImpureEqn Get k}) ≡ ImpureEqn (Put s) λ{_ → k s}

-- following Sam Lindley's notes http://msp.cis.strath.ac.uk/101/slides/2020-12-17_sam.pdf
GetGet : (k : S → ExFreerEqns S A) → ImpureEqn Get (λ _ → ImpureEqn Get k) ≡ ImpureEqn Get k
GetGet k = ImpureEqn Get (λ _ → ImpureEqn Get k)
             ≡⟨ sym (GetPutEqn _) ⟩
           ImpureEqn Get (λ x → ImpureEqn (Put x) λ _ → ImpureEqn Get λ _ → ImpureEqn Get k)
            ≡⟨ cong (ImpureEqn Get) (funExt λ w → PutGetEqn w _) ⟩
           ImpureEqn Get (λ z → ImpureEqn (Put z) (λ _ → ImpureEqn Get k))
             ≡⟨ GetPutEqn _ ⟩
           ImpureEqn Get k ∎

-- sequence 1 = sequence 2
-- graded composition sequence 1 = graded composition sequence 2
-- (Get o Put) ≡ id

handleE : S -> ExFreerEqns S A -> A
handleE s (PureEqn x) = x
handleE s (ImpureEqn (Put x) x₁) = handleE x (x₁ Ptt)
handleE s (ImpureEqn Get x₁) = handleE s (x₁ s)
handleE s (GetPutEqn m i) = handleE s m
handleE s (PutPutEqn s1 s2 m i) = handleE s2 m
handleE s (PutGetEqn s1 k i) = handleE s1 (k s1)

handleE' : S -> (A -> B) -> ExFreerEqns S A -> B
handleE' s f (PureEqn x) = f x
handleE' s f (ImpureEqn (Put x) x₁) = handleE' x f (x₁ Ptt)
handleE' s f (ImpureEqn Get x₁) = handleE' s f (x₁ s)
handleE' s f (GetPutEqn m i) = handleE' s f m
handleE' s f (PutPutEqn s1 s2 m i) = handleE' s2 f m
handleE' s f (PutGetEqn s1 k i) = handleE' s1 f (k s1)

pureEqns : A → ExFreerEqns S A
pureEqns x = PureEqn x

bindEqns : ExFreerEqns S A -> (A -> ExFreerEqns S B) -> ExFreerEqns S B
bindEqns (PureEqn x) k = k x
bindEqns (ImpureEqn x k') k = ImpureEqn x λ z → bindEqns (k' z) k
bindEqns (GetPutEqn x i) k = GetPutEqn (bindEqns x k) i
bindEqns (PutPutEqn s' s x i) k = PutPutEqn s' s (bindEqns x k) i
bindEqns (PutGetEqn s k' i) k = PutGetEqn s (λ x → bindEqns (k' x) k) i

getOp : ExFreerEqns S S
getOp = ImpureEqn Get PureEqn

putOp : S -> ExFreerEqns S P⊤
putOp s = ImpureEqn (Put s) PureEqn


return = pureEqns
_>>=_ = bindEqns
_>>_ : ExFreerEqns S A -> ExFreerEqns S B -> ExFreerEqns S B
x >> y = x >>= (λ _ → y)

open import Cubical.Data.Nat

leftIdEqns : (a : A) (h : A -> ExFreerEqns S B) → bindEqns (pureEqns a) h ≡ h a
leftIdEqns a h = refl

rightIdEqns : (m : ExFreerEqns S A) → bindEqns m pureEqns ≡ m
rightIdEqns (PureEqn x) = refl
rightIdEqns (ImpureEqn x k) = cong (ImpureEqn x) (funExt λ z → rightIdEqns (k z))
rightIdEqns (GetPutEqn m i) j = GetPutEqn (rightIdEqns m j) i
rightIdEqns (PutPutEqn s' s x i) j = PutPutEqn s' s (rightIdEqns x j) i
rightIdEqns (PutGetEqn s k i) j = PutGetEqn s (λ x → rightIdEqns (k x) j) i

assocEqns : {A : Set l1} {B : Set l1} {C : Set l1}
   → (m : ExFreerEqns S A) → (f : A → ExFreerEqns S B) → (g : B → ExFreerEqns S C)
   → bindEqns (bindEqns m f) g ≡ bindEqns m λ x → bindEqns (f x) g
assocEqns (PureEqn x) f g = refl
assocEqns (ImpureEqn x k) f g = cong (ImpureEqn x) (funExt λ z → assocEqns (k z) f g)
assocEqns (GetPutEqn m i) f g j = GetPutEqn (assocEqns m f g j) i
assocEqns (PutPutEqn s' s x i) f g j = PutPutEqn s' s (assocEqns x f g j) i
assocEqns (PutGetEqn s k i) f g j = PutGetEqn s (λ x → assocEqns (k x) f g j) i


-- example

operationExample : ExFreerEqns ℕ ℕ
operationExample = do
     m <- getOp
     z <- getOp
     putOp (z + 3)
     w <- getOp
     return w

opEx2 : ExFreerEqns ℕ ℕ
opEx2 = do
  z <- getOp
  putOp (z + 3)
  getOp

lawExample : operationExample ≡ opEx2
lawExample = _ ≡⟨ GetGet _ ⟩ _ ∎

-- send bind send variant of ⨄



-- exception
-- fresh
-- fail
-- reader
-- writer
-- state
-- accumulating nondet
-- choose
-- env
-- logict
-- cull + cut

-- concurrency algebra

-- scoping constructs ala schrijvers??