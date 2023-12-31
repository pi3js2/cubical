{-# OPTIONS --safe --lossy-unification #-}
{-
This file contains
1. Unordered joins, pairs, coproducts and smash products
2. Some simple lemmas concerning these types
3. A (rather lengthy) characterisation of Π-types over unorrered joins.
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence

open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sigma
open import Cubical.Data.Bool
open import Cubical.Data.Sum as ⊎

open import Cubical.HITs.Pushout
open import Cubical.HITs.RPn.Base
open import Cubical.HITs.Join
open import Cubical.HITs.SmashProduct

open import Cubical.Relation.Nullary

module Cubical.HITs.RPn.Unordered where

private
  variable
    ℓ ℓ' : Level

UnordJoinR-gen : (I : Type ℓ) (A : I → Type ℓ') → Type (ℓ-max ℓ ℓ')
UnordJoinR-gen I A = PushoutR (Σ I A) ((i : I) → A i)  λ x f → f (fst x) ≡ snd x

UnordJoin-gen : (I : Type ℓ) (A : I → Type ℓ') → Type (ℓ-max ℓ ℓ')
UnordJoin-gen I A =
  Pushout {A = I × ((i : I) → A i)}
          (λ fi → fst fi , snd fi (fst fi)) snd

module _ (I : RP∞' ℓ) (A : fst I → Type ℓ') where
  -- unordered coproducts
  UnordΣ : Type ℓ'
  UnordΣ = Σ (fst I) A

  -- unordered products
  UnordΠ : Type ℓ'
  UnordΠ = (i : fst I) → A i

  -- joins
  UnordJoin : Type ℓ'
  UnordJoin = UnordJoin-gen (fst I) A

  -- joins (via relational pushout)
  UnordJoinR : Type ℓ'
  UnordJoinR = UnordJoinR-gen (fst I) A

-- smash products
module _ (I : RP∞' ℓ) (A : fst I → Pointed ℓ) where
  open RP∞'-fields I
  UnordΣ→UnordΠ : UnordΣ I (fst ∘ A) → UnordΠ I (fst ∘ A)
  UnordΣ→UnordΠ (i , a) = elimRP∞' i a (pt (A (notRP∞' i)))

  UnordSmash : Type ℓ
  UnordSmash = Pushout fst UnordΣ→UnordΠ

  UnordSmash∙ : Pointed ℓ
  UnordSmash∙ = UnordSmash , inr (snd ∘ A)

-- characterisation of nestled UnordΠ and UnordΣ
module UnordΠUnordΣ-charac-lemmas {ℓ : Level} (I J : RP∞' ℓ)
  (A : fst I → fst J → Type ℓ) where
  F : (C : Type) (t : C ≃ (fst I → fst J))
    → ((i : fst I) → Σ (fst J) (A i))
    → Σ[ c ∈ C ] ((i : fst I) → A i (t .fst c i))
  F C t j = (invEq t (fst ∘ j))
    , λ i → subst (A i) (λ k → secEq t (λ i → fst (j i)) (~ k) i) (snd (j i))

  G : (C : Type) (t : C ≃ (fst I → fst J))
    → Σ[ c ∈ C ] ((i : fst I) → A i (t .fst c i))
    → ((i : fst I) → Σ (fst J) (A i))
  G C t (c , f) j = t .fst c j , f j

  G→F→G : (C : Type) (t : C ≃ (fst I → fst J))
    → (x : _) → F C t (G C t x) ≡ x
  G→F→G C = EquivJ (λ C t → (x : _) → F C t (G C t x) ≡ x)
    λ {(f , p) → ΣPathP (refl , funExt λ j → transportRefl (p j))}

  F→G→F : (C : Type) (t : C ≃ (fst I → fst J))
    → (x : _) → G C t (F C t x) ≡ x
  F→G→F C =
    EquivJ (λ C t → (x : _) → G C t (F C t x) ≡ x)
            λ f → funExt λ i → ΣPathP (refl , (transportRefl (snd (f i))))

module _ {ℓ : Level} (I J : RP∞' ℓ) {A : fst I → fst J → Type ℓ} where
  open UnordΠUnordΣ-charac-lemmas I J A
  UnordΠUnordΣ-charac :
    Iso (UnordΠ I (λ i → UnordΣ J (A i)))
        (Σ[ r ∈ fst J ⊎ (fst I ≃ fst J) ]
          ((i : fst I) → A i (eval⊎≃ r i)))
  Iso.fun UnordΠUnordΣ-charac = F _ (eval⊎≃Equiv I J)
  Iso.inv UnordΠUnordΣ-charac = G _ (eval⊎≃Equiv I J)
  Iso.rightInv UnordΠUnordΣ-charac x = G→F→G _ (eval⊎≃Equiv I J) x
  Iso.leftInv UnordΠUnordΣ-charac x = F→G→F _ (eval⊎≃Equiv I J) x

UnordJoinR-funct : {I : Type ℓ} {A B : I → Type ℓ'}
  (f : (i : I) → A i → B i) → UnordJoinR-gen I A → UnordJoinR-gen I B
UnordJoinR-funct f (inlR (i , a)) = inlR (i , f i a)
UnordJoinR-funct f (inrR x) = inrR λ i → f i (x i)
UnordJoinR-funct f (pushR (i , a) b x k) =
  pushR (i , f i a) (λ i → f i (b i)) (cong (f i) x) k

UnordJoinR-Equiv-cancel : {I : Type ℓ} {A B : I → Type ℓ'}
  (f : (i : I) → A i ≃ B i)
  → (x : UnordJoinR-gen I A)
  → UnordJoinR-funct (invEq ∘ f) (UnordJoinR-funct (fst ∘ f) x) ≡ x
UnordJoinR-Equiv-cancel f (inlR (i , a)) k = inlR (i , (retEq (f i) a k))
UnordJoinR-Equiv-cancel f (inrR x) k = inrR λ i → retEq (f i) (x i) k
UnordJoinR-Equiv-cancel f (pushR (i , a) b x k) j =
  pushR (i , retEq (f i) a j) (λ z → retEq (f z) (b z) j)
        (λ k → retEq (f i) (x k) j) k

UnordJoinR-functIso : {I : Type ℓ} {A B : I → Type ℓ'}
  (f : (i : I) → A i ≃ B i)
  → Iso (UnordJoinR-gen I A) (UnordJoinR-gen I B)
Iso.fun (UnordJoinR-functIso f) = UnordJoinR-funct (fst ∘ f)
Iso.inv (UnordJoinR-functIso f) = UnordJoinR-funct (invEq ∘ f)
Iso.rightInv (UnordJoinR-functIso f) x = UnordJoinR-Equiv-cancel (invEquiv ∘ f) x
Iso.leftInv (UnordJoinR-functIso f) x = UnordJoinR-Equiv-cancel f x

-- UnordJoinR is usual join when bool indexed
UnordJoinR→join : ∀ {ℓ} {A : Bool → Type ℓ}
  → UnordJoinR-gen Bool A → join (A true) (A false)
UnordJoinR→join (inlR (false , a)) = inr a
UnordJoinR→join (inlR (true , a)) = inl a
UnordJoinR→join (inrR x) = inl (x true)
UnordJoinR→join (pushR (false , a) b x i) = push (b true) a (~ i)
UnordJoinR→join (pushR (true , a) b x i) = inl (x (~ i))

join→UnordJoinR : ∀ {ℓ} {A : Bool → Type ℓ}
  → join (A true) (A false)
  → UnordJoinR-gen Bool A
join→UnordJoinR (inl x) = inlR (true , x)
join→UnordJoinR (inr x) = inlR (false , x)
join→UnordJoinR (push a b i) =
   (pushR (true , a) (CasesBool true a b) refl
  ∙ sym (pushR (false , b) (CasesBool true a b) refl)) i

join-UnordJoinR-iso : ∀ {ℓ} {A : Bool → Type ℓ}
  → Iso (UnordJoinR-gen Bool A) (join (A true) (A false))
Iso.fun join-UnordJoinR-iso = UnordJoinR→join
Iso.inv join-UnordJoinR-iso = join→UnordJoinR
Iso.rightInv join-UnordJoinR-iso (inl x) = refl
Iso.rightInv join-UnordJoinR-iso (inr x) = refl
Iso.rightInv (join-UnordJoinR-iso {A = A}) (push a b i) j = lem j i
  where
  lem : cong (UnordJoinR→join {A = A})
               (pushR (true , a) (CasesBool true a b) refl
              ∙ sym (pushR (false , b) (CasesBool true a b) refl))
      ≡ push a b
  lem = cong-∙ UnordJoinR→join
            (pushR (true , a) (CasesBool true a b) refl)
            (sym (pushR (false , b) (CasesBool true a b) refl))
       ∙ sym (lUnit (push a b))
Iso.leftInv join-UnordJoinR-iso (inlR (false , y)) = refl
Iso.leftInv join-UnordJoinR-iso (inlR (true , y)) = refl
Iso.leftInv join-UnordJoinR-iso (inrR x) = pushR (true , x true) x refl
Iso.leftInv (join-UnordJoinR-iso {A = A}) (pushR (false , x) b p i) j =
  lem x p j i
  where
  lem : (x : A false) (p : b false ≡ x)
    → Square {A = UnordJoinR-gen Bool A}
             (sym (pushR (true , b true) (CasesBool true (b true) x) refl
               ∙ sym (pushR (false , x) (CasesBool true (b true) x) refl)))
             (pushR (false , x) b p)
             refl
             (pushR (true , b true) b refl)
  lem = J> ((λ s → sym (pushR (true , b true) (CasesBoolη b s) refl
                ∙ sym (pushR (false , b false) (CasesBoolη b s) refl)))
        ◁ λ i j → compPath-filler'
                    (pushR (true , b true) b refl)
                    (sym (pushR (false , b false) b refl)) (~ i) (~ j))
Iso.leftInv (join-UnordJoinR-iso {A = A}) (pushR (true , x) b p i) j =
  lem x p j i
  where
  lem : (x : _) (p : b true ≡ x)
    → Square {A = UnordJoinR-gen Bool A}
              (λ i → inlR (true , p (~ i))) (pushR (true , x) b p )
              refl (pushR (true , b true) b (λ _ → b true))
  lem = J> λ i j → pushR (true , b true) b refl (i ∧ j)

module _ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} where
  private
    F : UnordJoin-gen A B → UnordJoinR-gen A B
    F (inl x) = inlR x
    F (inr x) = inrR x
    F (push (i' , a) i) = pushR (i' , a i') a refl i

  UnordJoinIso : Iso (UnordJoinR-gen A B) (UnordJoin-gen A B)
  Iso.fun UnordJoinIso (inlR x) = inl x
  Iso.fun UnordJoinIso (inrR x) = inr x
  Iso.fun UnordJoinIso (pushR a b x i) =
    ((λ i → inl (fst a , x (~ i))) ∙ push (fst a , b)) i
  Iso.inv UnordJoinIso = F
  Iso.rightInv UnordJoinIso (inl x) = refl
  Iso.rightInv UnordJoinIso (inr x) = refl
  Iso.rightInv UnordJoinIso (push a i) j = lUnit (push a) (~ j) i
  Iso.leftInv UnordJoinIso (inlR x) = refl
  Iso.leftInv UnordJoinIso (inrR x) = refl
  Iso.leftInv UnordJoinIso (pushR a b x i) j =
    hcomp (λ k → λ{(i = i0) → inlR (fst a , x k)
                  ; (i = i1) → inrR b
                  ; (j = i0) → F (compPath-filler' (λ i → inl (fst a , x (~ i)))
                                         (push (fst a , b)) k i)
                  ; (j = i1) → pushR (fst a , x k) b (λ i → x (i ∧ k)) i})
          (pushR (fst a , b (fst a)) b (λ _ → b (fst a)) i)

-- Analysis of Πᵢ (JoinR Aᵢ)
module ΠJoinR-gen {ℓ} (I : RP∞' ℓ) (J : Type) (A : fst I → J → Type ℓ)
       (AB : Type ℓ) (AB→J : (i : fst I) → AB → J)
       (AB→A : (i : fst I) (a : AB) → A i (AB→J i a))
  where
  open RP∞'-fields I

  Π∗-back : Type ℓ
  Π∗-back = Σ[ a ∈ AB ]
           Σ[ g ∈ ((i : fst I) (j : J) → A i j) ]
             ((i : fst I) → g i (AB→J i a) ≡ AB→A i a)
  Π∗-base : Type ℓ
  Π∗-base = Pushout {A = Π∗-back} {B = AB} {C = ((i : fst I) (j : J) → A i j)}
                       fst (fst ∘ snd)

  ΠR-left : Type _
  ΠR-left = Σ[ i ∈ fst I ] (Σ[ j ∈ J ] (A i j)) × ((j : J) → A (notRP∞' i) j)

  ΠR-left↑ₗ : fst I → Type _
  ΠR-left↑ₗ i =
    Σ[ f ∈ AB ] Σ[ g ∈ ((j : J) → A (notRP∞' i) j) ]
      g (AB→J (notRP∞' i) f) ≡ AB→A (notRP∞' i) f

  ΠR-left↑ᵣ : fst I → Type _
  ΠR-left↑ᵣ i = Σ[ f ∈ (Σ[ j ∈ J ] A i j) ]
      Σ[ g ∈ ((i : fst I) (j : J) → A i j) ] g i (fst f) ≡ snd f

  Π∗-back→ₗ : (i : fst I) → Π∗-back → ΠR-left↑ₗ i
  Π∗-back→ₗ  i (f , g , r) = (f , (g (notRP∞' i)) , (r (notRP∞' i)))

  Π∗-back→ᵣ : (i : fst I) → Π∗-back → ΠR-left↑ᵣ i
  Π∗-back→ᵣ i (f , g , r) =  (AB→J i f , AB→A i f) , g , r i

  PushTop : (i : fst I) → Type ℓ
  PushTop i = Pushout (Π∗-back→ₗ i) (Π∗-back→ᵣ i)


  ΣPushtop : Type _
  ΣPushtop = Σ[ i ∈ fst I ] (PushTop i)

  AB→Σ : (i : fst I) → AB → Σ J (A i)
  fst (AB→Σ a f) = AB→J a f
  snd (AB→Σ a f) = AB→A a f

  Pushtop→ΠR-left' : (i : fst I)
    → (Pushout (Π∗-back→ₗ i) (Π∗-back→ᵣ i))
    → (Σ[ j ∈ J ] (A i j)) × ((j : J) → A (notRP∞' i) j)
  Pushtop→ΠR-left' i (inl (f , g , p)) = AB→Σ i f , g
  Pushtop→ΠR-left' i (inr (f , g , p)) = f , (g (notRP∞' i))
  Pushtop→ΠR-left' i (push (f , g , p) k) = (AB→Σ i f) , g (notRP∞' i)

  ΣPushtop→ΠR-left : ΣPushtop → ΠR-left
  ΣPushtop→ΠR-left (i , x) = (i , Pushtop→ΠR-left' i x)

  ΣPushtop→Π∗-base : ΣPushtop → Π∗-base
  ΣPushtop→Π∗-base (i , inl (f , g , p)) = inl f
  ΣPushtop→Π∗-base (i , inr (f , g , p)) = inr g
  ΣPushtop→Π∗-base (i , push (f , g , p)  j) = push (f , g , p) j

  Π∗ : Type _
  Π∗ = Pushout ΣPushtop→ΠR-left ΣPushtop→Π∗-base

{-
Instantiating above with:

AB = ((i : fst I) → Σ J (A i))
AB→J = (λ i f → f i .fst)
AB→A = (λ i f → f i .snd)

yields a type Π∗ mapping into Πᵢ (JoinR Aᵢ)
-}
module ΠJoinR₁ {ℓ : Level} (I : RP∞' ℓ) (J : Type)
               (A : fst I → J → Type ℓ) where
  open ΠJoinR-gen I J A
    ((i : fst I) → Σ J (A i)) (λ i f → f i .fst) (λ i f → f i .snd)
    public
  open RP∞'-fields I

  Π∗→Πₗ : ΠR-left → ((i : fst I) → UnordJoinR-gen J (A i))
  Π∗→Πₗ (i , p , r) = elimRP∞' i (inlR p) (inrR r)

  Π∗-base→ : Π∗-base → ((i : fst I) → UnordJoinR-gen J (A i))
  Π∗-base→ (inl x) i = inlR (x i)
  Π∗-base→ (inr x) i = inrR λ j → x i j
  Π∗-base→ (push a i') i = pushR (fst a i) (fst (snd a) i) (snd (snd a) i) i'

  pre-eqvl-diag : (i' : fst I) (p : Pushout (Π∗-back→ₗ i') (Π∗-back→ᵣ i'))
    → Π∗→Πₗ (ΣPushtop→ΠR-left (i' , p)) i'
     ≡ Π∗-base→ (ΣPushtop→Π∗-base (i' , p)) i'
  pre-eqvl-diag i' (inl (f , f2 , p)) =
    elimRP∞'β {B = λ i → UnordJoinR-gen J (A i)} i'
              (inlR (f i' .fst , f i' .snd)) (inrR f2) .fst
  pre-eqvl-diag i' (inr (f , f2 , p)) =
    elimRP∞'β {B = λ i → UnordJoinR-gen J (A i)} i'
              (inlR f) (inrR (f2 (notRP∞' i'))) .fst ∙ pushR f (f2 i') p
  pre-eqvl-diag i' (push (f , f2 , p) i) j =
    compPath-filler
      (elimRP∞'β {B = λ i → UnordJoinR-gen J (A i)} i'
                 (inlR (f i')) (inrR (f2 (notRP∞' i'))) .fst)
      (pushR (f i') (f2 i') (p i')) i j

  pre-eqvl-not : (i' : fst I) (p : Pushout (Π∗-back→ₗ i') (Π∗-back→ᵣ i'))
    → Π∗→Πₗ (ΣPushtop→ΠR-left (i' , p)) (notRP∞' i') ≡
      Π∗-base→ (ΣPushtop→Π∗-base (i' , p)) (notRP∞' i')
  pre-eqvl-not i' (inl (f , f2 , p)) =
      elimRP∞'β {B = λ i → UnordJoinR-gen J (A i)} i'
                (inlR (f i')) (inrR f2) .snd
    ∙ sym (pushR (f (notRP∞' i')) f2 p)
  pre-eqvl-not i' (inr (f , f2 , p)) =
    elimRP∞'β {B = λ i → UnordJoinR-gen J (A i)} i'
              (inlR f) (inrR (f2 (notRP∞' i'))) .snd
  pre-eqvl-not i' (push (f , f2 , p) i) j =
    compPath-filler
     (elimRP∞'β {B = λ i → UnordJoinR-gen J (A i)} i'
                (inlR (f i')) (inrR (f2 (notRP∞' i'))) .snd)
     (sym (pushR (f (notRP∞' i')) (f2 (notRP∞' i')) (p (notRP∞' i')))) (~ i) j


  eqvl : (a : ΣPushtop) (i : fst I)
    → Π∗→Πₗ (ΣPushtop→ΠR-left a) i
     ≡ Π∗-base→ (ΣPushtop→Π∗-base a) i
  eqvl (i' , p) =
    elimRP∞' i' (pre-eqvl-diag i' p)
                 (pre-eqvl-not i' p)

  -- main map
  Π∗→Π : Π∗ → ((i : fst I) → UnordJoinR-gen J (A i))
  Π∗→Π (inl t) = Π∗→Πₗ t
  Π∗→Π (inr x) = Π∗-base→ x
  Π∗→Π (push a i) i' = eqvl a i' i

-- let's show that Π∗→Π is an equivalence.
-- It's enough to do so when I is Bool.
-- Let's give Π∗→Π an explicit definition in this case
Π∗→Π-Bool :
  ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → (fst J) → Type ℓ)
  → ΠJoinR₁.Π∗ (RP∞'∙ ℓ) (fst J) A
  → ((i : Bool) → UnordJoinR-gen (fst J) (A i))
Π∗→Π-Bool J A (inl (false , f , p)) false = inlR f
Π∗→Π-Bool J A (inl (false , f , p)) true = inrR p
Π∗→Π-Bool J A (inl (true , f , p)) false = inrR p
Π∗→Π-Bool J A (inl (true , f , p)) true = inlR f
Π∗→Π-Bool J A (inr (inl x)) a = inlR (x a)
Π∗→Π-Bool J A (inr (inr x)) b = inrR (x b)
Π∗→Π-Bool J A (inr (push a i)) c =
  pushR (fst a c) (fst (snd a) c) (snd (snd a) c) i
Π∗→Π-Bool J A (push (false , inl x) i) false = inlR (fst x false)
Π∗→Π-Bool J A (push (false , inr x) i) false =
  pushR (fst x) (fst (snd x) false) (snd (snd x)) i
Π∗→Π-Bool J A (push (false , push (f , p , q) j) i) false =
  pushR (f false) (p false) (q false) (i ∧ j)
Π∗→Π-Bool J A (push (false , inl x) i) true =
  pushR (fst x true) (fst (snd x)) (snd (snd x)) (~ i)
Π∗→Π-Bool J A (push (false , inr x) i) true = inrR (fst (snd x) true)
Π∗→Π-Bool J A (push (false , push (f , p , q) j) i) true =
  pushR (f true) (p true) (q true) (~ i ∨ j)
Π∗→Π-Bool J A (push (true , inl x) i) false =
  pushR (fst x false) (fst (snd x)) (snd (snd x)) (~ i)
Π∗→Π-Bool J A (push (true , inr x) i) false = inrR (fst (snd x) false)
Π∗→Π-Bool J A (push (true , push (f , p , q) j) i) false =
  pushR (f false) (p false) (q false) (~ i ∨ j)
Π∗→Π-Bool J A (push (true , inl x) i) true = inlR (fst x true)
Π∗→Π-Bool J A (push (true , inr x) i) true =
  pushR (fst x) (fst (snd x) true) (snd (snd x)) i
Π∗→Π-Bool J A (push (true , push (f , p , q) j) i) true =
  pushR (f true) (p true) (q true) (i ∧ j)

-- Π∗→Π-Bool agrees with our original definition
Π∗→Π-Bool≡ : ∀ {ℓ} {J : RP∞' ℓ} (A : Bool → fst J → Type ℓ)
  → (x : _) (z : _) → Π∗→Π-Bool J A x z
                     ≡ ΠJoinR₁.Π∗→Π (RP∞'∙ ℓ) (fst J) A x z
Π∗→Π-Bool≡ A (inl (false , y)) false = refl
Π∗→Π-Bool≡ A (inl (false , y)) true = refl
Π∗→Π-Bool≡ A (inl (true , y)) false = refl
Π∗→Π-Bool≡ A (inl (true , y)) true = refl
Π∗→Π-Bool≡ A (inr (inl x)) z = refl
Π∗→Π-Bool≡ A (inr (inr x)) z = refl
Π∗→Π-Bool≡ A (inr (push a i)) false = refl
Π∗→Π-Bool≡ A (inr (push a i)) true = refl
Π∗→Π-Bool≡ A (push (false , inl x) i) false = refl
Π∗→Π-Bool≡ A (push (false , inr x) i) false j =
  lUnit (pushR (fst x) (fst (snd x) false) (snd (snd x))) j i
Π∗→Π-Bool≡ A (push (false , push a j) i) false k =
  hcomp (λ r
  → λ {(i = i0) → inlR (fst a false)
      ; (i = i1) → pushR (fst a false) (fst (snd a) false)
                          (snd (snd a) false) (j ∧ (~ k ∨ r))
      ; (j = i0) → inlR (fst a false)
      ; (j = i1) → lUnit-filler (pushR (fst a false) (fst (snd a) false)
                                 (snd (snd a) false)) r k i
      ; (k = i0) → pushR (fst a false) (fst (snd a) false)
                          (snd (snd a) false) (i ∧ j)
      ; (k = i1) → compPath-filler refl
                     (pushR (fst a false) (fst (snd a) false)
                            (snd (snd a) false)) (r ∧ j) i})
      (pushR (fst a false) (fst (snd a) false)
             (snd (snd a) false) (i ∧ (j ∧ ~ k)))
Π∗→Π-Bool≡ A (push (true , inl x) i) false j =
  lUnit (sym (pushR (fst x false) (fst (snd x)) (snd (snd x)))) j i
Π∗→Π-Bool≡ A (push (true , inr x) i) false = refl
Π∗→Π-Bool≡ A (push (true , push a j) i) false k =
  hcomp (λ r
  → λ {(i = i0) → inrR (fst (snd a) false)
      ; (i = i1) → pushR (fst a false) (fst (snd a) false)
                          (snd (snd a) false) (j ∨ (k ∧ ~ r))
      ; (j = i0) → lUnit-filler (sym (pushR (fst a false) (fst (snd a) false)
                                 (snd (snd a) false))) r k i
      ; (j = i1) → inrR (fst (snd a) false)
      ; (k = i0) → pushR (fst a false) (fst (snd a) false)
                          (snd (snd a) false) (~ i ∨ j)
      ; (k = i1) → compPath-filler refl
                     (sym (pushR (fst a false) (fst (snd a) false)
                          (snd (snd a) false))) (r ∧ ~ j) i})
      (pushR (fst a false) (fst (snd a) false)
             (snd (snd a) false) ((k ∨ j) ∨ ~ i))
Π∗→Π-Bool≡ A (push (false , inl x) i) true j =
  lUnit (sym (pushR (fst x true) (fst (snd x)) (snd (snd x)))) j i
Π∗→Π-Bool≡ A (push (false , inr x) i) true = refl
Π∗→Π-Bool≡ A (push (false , push a j) i) true k =
  hcomp (λ r
  → λ {(i = i0) → inrR (fst (snd a) true)
      ; (i = i1) → pushR (fst a true) (fst (snd a) true)
                          (snd (snd a) true) (j ∨ (k ∧ ~ r))
      ; (j = i0) → lUnit-filler (sym (pushR (fst a true) (fst (snd a) true)
                                 (snd (snd a) true))) r k i
      ; (j = i1) → inrR (fst (snd a) true)
      ; (k = i0) → pushR (fst a true)
                     (fst (snd a) true) (snd (snd a) true) (~ i ∨ j)
      ; (k = i1) → compPath-filler refl
                     (sym (pushR (fst a true) (fst (snd a) true)
                            (snd (snd a) true))) (r ∧ ~ j) i})
        (pushR (fst a true) (fst (snd a) true)
               (snd (snd a) true) ((k ∨ j) ∨ ~ i))
Π∗→Π-Bool≡ A (push (true , inl x) i) true = refl
Π∗→Π-Bool≡ A (push (true , inr x) i) true j =
  lUnit (pushR (fst x) (fst (snd x) true) (snd (snd x))) j i
Π∗→Π-Bool≡ A (push (true , push a j) i) true k =
  hcomp (λ r
  → λ {(i = i0) → inlR (fst a true)
      ; (i = i1) → pushR (fst a true) (fst (snd a) true)
                          (snd (snd a) true) (j ∧ (~ k ∨ r))
      ; (j = i0) → inlR (fst a true)
      ; (j = i1) → lUnit-filler (pushR (fst a true) (fst (snd a) true)
                                 (snd (snd a) true)) r k i
      ; (k = i0) → pushR (fst a true)
                     (fst (snd a) true) (snd (snd a) true) (i ∧ j)
      ; (k = i1) → compPath-filler refl
                     (pushR (fst a true) (fst (snd a) true)
                       (snd (snd a) true)) (r ∧ j) i})
        (pushR (fst a true) (fst (snd a) true)
               (snd (snd a) true) (i ∧ (j ∧ ~ k)))


-- To show that Π∗→Π-Bool is an equivalence, it is easier to show that
-- its composition with ΠBool→× (equivalence between Π over bool and
-- products) is an equivalence:
Π∗→× : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
  → ΠJoinR₁.Π∗ (RP∞'∙ ℓ) (fst J) A
  → UnordJoinR-gen (fst J) (A true) × UnordJoinR-gen (fst J) (A false)
Π∗→× J A t =
  ΠBool→× {A = λ x → UnordJoinR-gen (fst J) (A x)} (Π∗→Π-Bool J A t)

-- To construct its inverse, we'll need some fillers.
private
  Square-filler : {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : z ≡ y)
    → I → I → I → A
  Square-filler {y = y} p q i j k =
    hfill (λ k → λ {(i = i0) → p (~ j ∨ ~ k)
                   ; (i = i1) → q (j ∨ ~ k)
                   ; (j = i0) → q (~ k ∨ ~ i)
                   ; (j = i1) → p (i ∨ ~ k)})
           (inS y)
           k
  module _ {ℓ : Level} (J : Type) (A : Bool → J → Type ℓ)
           (a a' : J) (b : A true a) (b₁ : A false a')
           (c : (i₂ : J) → A true i₂)
           (c₁ : (i₂ : J) → A false i₂)
           (x : c a ≡ b)
           (d : c₁ a' ≡ b₁) where

    ×→Π∗-push²-fill-btm : I → I → I → ΠJoinR₁.Π∗ (RP∞'∙ ℓ) J A
    ×→Π∗-push²-fill-btm i j r =
      Square-filler {A = ΠJoinR₁.Π∗ (RP∞'∙ ℓ) J A}
          (push (true , inl (CasesBool true (a , b) (a' , b₁) , c₁ , d)))
          (push (false , inl (CasesBool true (a , b) (a' , b₁) , c , x)))
           i j r

    ×→Π∗-push²-fill : I → I → I → ΠJoinR₁.Π∗ (RP∞'∙ ℓ) J A
    ×→Π∗-push²-fill i j r =
      hfill (λ r
      → λ {(i = i0) → push (true
                        , inl (CasesBool true (a , b) (a' , b₁) , c₁ , d)) (~ j)
          ; (i = i1) → push (false , push ((CasesBool true (a , b) (a' , b₁))
                           , (CasesBool true c c₁ , CasesBool true x d)) r) j
          ; (j = i0) → push (false
                        , inl (CasesBool true (a , b) (a' , b₁) , c , x)) (~ i)
          ; (j = i1) → push (true , push ((CasesBool true (a , b) (a' , b₁))
                           , (CasesBool true c c₁) , CasesBool true x d) r) i})
        (inS (×→Π∗-push²-fill-btm i j i1)) r

×→Π∗ : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
  → UnordJoinR-gen (fst J) (A true) × UnordJoinR-gen (fst J) (A false)
  → ΠJoinR₁.Π∗ (RP∞'∙ ℓ) (fst J) A
×→Π∗ J A (inlR x , inlR x₁) = inr (inl (CasesBool true x x₁))
×→Π∗ J A (inlR (x , b) , inrR x₁) = inl (true , ((_ , b) , x₁))
×→Π∗ J A (inlR (a , b) , pushR (a' , d) c x₁ i) =
  push (true , inl ((CasesBool true (a , b) (a' , d)) , c , x₁)) (~ i)
×→Π∗ J A (inrR x , inlR x₁) = inl (false , (x₁ , x))
×→Π∗ J A (inrR x , inrR x₁) = inr (inr (CasesBool true x x₁))
×→Π∗ J A (inrR x , pushR (a , b) c x₁ i) =
  push (false , (inr ((a , b) , ((CasesBool true x c) , x₁)))) i
×→Π∗ J A (pushR (a , b) c x i , inlR (a' , b')) =
  push (false , inl ((CasesBool true (a , b) (a' , b')) , (c , x))) (~ i)
×→Π∗ J A (pushR (a' , b) c x i , inrR x₁) =
  push (true , inr ((_ , b) , (CasesBool true c x₁ , x))) i
×→Π∗ J A (pushR (a , b) c x i , pushR (a' , b₁) c₁ d j) =
  ×→Π∗-push²-fill (fst J) A a a' b b₁ c c₁ x d i j i1

-- proving that the maps cancel out is easy in one direction
×→Π∗→× : ∀ {ℓ} {J : RP∞' ℓ} (A : Bool → fst J → Type ℓ)
  (m : UnordJoinR-gen (fst J) (A true) × UnordJoinR-gen (fst J) (A false))
  → Π∗→× J A (×→Π∗ J A m) ≡ m
×→Π∗→× A (inlR (a , b) , inlR (a' , d)) = refl
×→Π∗→× A (inlR (a , snd₁) , inrR x₁) = refl
×→Π∗→× A (inlR (a , b) , pushR (a' , d) e x₁ i) = refl
×→Π∗→× A (inrR x , inlR (a , b)) = refl
×→Π∗→× A (inrR x , inrR x₁) = refl
×→Π∗→× A (inrR x , pushR (a' , b) c x₁ i) = refl
×→Π∗→× A (pushR (a , b) b₁ x i , inlR (a' , b')) = refl
×→Π∗→× A (pushR (a , b) b₁ x i , inrR x₁) = refl
×→Π∗→× {ℓ = ℓ} {J = J} A (pushR (a , b) c x i , pushR (a' , b₁) c₁ d j) k =
   hcomp (λ r
    → λ {(k = i0) → Π∗→× J A (P i j r)
        ; (k = i1) → (pushR (a , b) c x (i ∧ (~ j ∨ r)))
                      , pushR (a' , b₁) c₁ d (((~ i) ∨ r) ∧ j)
        ; (j = i0) → Π∗→× J A (P i j r)
        ; (j = i1) → Π∗→× J A (P i j r)
        ; (i = i0) → Π∗→× J A (P i j r)
        ; (i = i1) → Π∗→× J A (P i j r)})
        (hcomp (λ r
       → λ {(k = i0) →
         Π∗→× J A
           (Square-filler
            (push (true , inl ((CasesBool true (a , b) (a' , b₁)) , (c₁ , d))))
            (push (false , inl ((CasesBool true (a , b) (a' , b₁)) , (c , x))))
             i j r)
        ; (k = i1) → pushR (a , b) c x (i ∧ ~ j ∧ r)
                    , pushR (a' , b₁) c₁ d (~ i ∧ j ∧ r)
        ; (j = i0) → pushR (a , b) c x (r ∧ i) , inlR (a' , b₁)
        ; (j = i1) → inlR (a , b) , pushR (a' , b₁) c₁ d (~ i ∧ r)
        ; (i = i0) → inlR (a , b) , pushR (a' , b₁) c₁ d (j ∧ r)
        ; (i = i1) → pushR (a , b) c x (~ j ∧ r) , inlR (a' , b₁) })
        ((inlR (a , b) , inlR (a' , b₁))))
  where
  P = ×→Π∗-push²-fill (fst J) A a a' b b₁ c c₁ x d

-- ... the other direction is harder and requires a bunch of fillers

module Π∗→×→Π∗-fillers
  {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
  (f : (j : Bool) → Σ (fst J) (A j))
  (a : (j : Bool) (j₁ : fst J) → A j j₁)
  (b : (j : Bool) → a j (f j .fst) ≡ f j .snd) where
  private
    H = ΠJoinR₁.Π∗ (RP∞'∙ ℓ) (fst J) A

    ×→Π∗-push²-fill-btm-path =
      ×→Π∗-push²-fill-btm
        (fst J) A (fst (f true)) (fst (f false)) (snd (f true)) (snd (f false))
        (a true) (a false) (b true) (b false)

    ×→Π∗-push²-fill-path =
      ×→Π∗-push²-fill (fst J) A
        (fst (f true)) (fst (f false)) (snd (f true)) (snd (f false))
        (a true) (a false) (b true) (b false)

  true-fill :  I → I → I → H
  true-fill i j k =
    hfill (λ r
    → λ {(i = i0) → push (true , (inl (CasesBoolη f j , a false , b false))) r
        ; (i = i1) → push (true , (inr (f true , CasesBoolη a j , b true))) r
        ; (j = i0) → ×→Π∗-push²-fill-path (i ∧ r) (i ∨ ~ r) i1
                   ; (j = i1) → push (true , (push (f , (a , b)) i)) r})
          (inS (inl (true , f true , a false))) k

  false-fill : I → I → I → H
  false-fill i j k =
    hfill (λ r
    → λ {(i = i0) → push (false , inl (CasesBoolη f j , a true , b true)) r
        ; (i = i1) → push (false , (inr (f false , CasesBoolη a j , b false))) r
        ; (j = i0) → ×→Π∗-push²-fill-path (i ∨ ~ r) (i ∧ r) i1
        ; (j = i1) → push (false , (push (f , (a , b)) i)) r})
          (inS (inl (false , f false , a true))) k

  true-fill≡false-fill :
    Path (Square {A = H} _ _ _ _)
         (λ i j → true-fill i j i1) (λ i j → false-fill i j i1)
  true-fill≡false-fill  k i j =
    hcomp (λ r →
    λ {(i = i0) → push (true , inl (CasesBoolη f j , a false , b false)) (r ∨ k)
     ; (i = i1) → push (true , inr (f true , CasesBoolη a j , b true)) (r ∨ k)
     ; (j = i0) → ×→Π∗-push²-fill-path (i ∧ (r ∨ k)) (i ∨ ~ (r ∨ k)) i1
     ; (j = i1) → push (true , push (f , a , b) i) (r ∨ k)
     ; (k = i0) → true-fill i j r
     ; (k = i1) → false-fill i j i1})
      (hcomp (λ r →
     λ {(i = i0) → push (true , inl (CasesBoolη f j , a false , b false)) k
      ; (i = i1) → push (true , push (CasesBoolη f j
                                     , CasesBoolη a j , CasesBoolη-coh b j) r) k
      ; (j = i0) → ×→Π∗-push²-fill-path (i ∧ k) (i ∨ ~ k) r
      ; (j = i1) → push (true , push (f , a , b) (r ∧ i)) k
      ; (k = i0) → inl (true , f true , a false)
      ; (k = i1) → cube₃ r j i})
       (hcomp (λ r →
     λ {(i = i0) → push (true
                       , inl (CasesBoolη f j , a false , b false)) (k ∨ ~ r)
      ; (i = i1) → push (true , inl ((CasesBoolη f j) ,
                         ((a false) , (b false)))) (k ∨ ~ r)
      ; (j = i0) → ×→Π∗-push²-fill-btm-path (i ∧ k) (i ∨ ~ k) r
      ; (j = i1) → push (true , inl (f , a false , b false)) (k ∨ ~ r)
      ; (k = i0) → push (true , inl (CasesBoolη f j , a false , b false)) (~ r)
      ; (k = i1) → cube₂ r j i})
     (inr (inl (CasesBoolη f j)))))
     where
     CasesBoolη-coh : (b : (j : Bool) → a j (f j .fst) ≡ f j .snd)
       → PathP (λ j → (i₃ : Bool) → CasesBoolη a j i₃ (CasesBoolη f j i₃ .fst)
                                    ≡ CasesBoolη f j i₃ .snd)
                (CasesBool true (b true) (b false)) b
     CasesBoolη-coh b = funExt λ { false → refl ; true → refl}

     CasesBoolη-coh-coh :
       SquareP (λ k i → (j : Bool) → CasesBoolη a i j (CasesBoolη f i j .fst)
                                    ≡ CasesBoolη f i j .snd)
                (CasesBoolη-coh (CasesBool true (b true) (b false)))
                (CasesBoolη-coh b)
                (refl {x = CasesBool true (b true) (b false)})
                (CasesBoolη b)
     CasesBoolη-coh-coh i a false = b false
     CasesBoolη-coh-coh i a true = b true

     cube₁ : I → I → I → H
     cube₁ i j k =
       hfill (λ r
       → λ {(i = i0) → ×→Π∗-push²-fill-btm-path j j r
           ; (i = i1) → inr (push (f , (a
                              , CasesBool true (b true) (b false))) (~ r ∧ ~ j))
           ; (j = i0) → inr (push ((CasesBoolη f i) ,
                              (a , (CasesBool true (b true) (b false))))
                              (~ r ∧ i))
           ; (j = i1) → inr (inl (CasesBoolη f i))})
       (inS ((inr
          (push (CasesBoolη f i , a
               , CasesBool true (b true) (b false)) (i ∧ ~ j)))))
       k


     cube₂ : I → I → I → H
     cube₂ i j k =
       hcomp (λ r →
       λ {(i = i0) → inr (push (CasesBoolη f j , a
                               , CasesBool true (b true) (b false))
                               (~ r ∧ ~ k ∧ j))
        ; (i = i1) → cube₁ j k r
        ; (j = i0) → ×→Π∗-push²-fill-btm-path k k (i ∧ r)
        ; (j = i1) → inr (push (f , a
                         , CasesBool true (b true) (b false)) (~ r ∧ ~ k))
        ; (k = i0) → inr (push (CasesBoolη f j , a
                               , CasesBool true (b true) (b false)) (~ r ∧ j))
        ; (k = i1) → inr (inl (CasesBoolη f j))})
      (inr (push (CasesBoolη f j , a
                , CasesBool true (b true) (b false)) (~ k ∧ j)))

     cube₃ : I → I → I → H
     cube₃ r i j =
       hcomp (λ k →
       λ {(i = i0) → ×→Π∗-push²-fill-path (j ∨ (~ k ∧ r)) (j ∧ (k ∨ ~ r)) r
        ; (i = i1) → push (false , push (f , a , b) (r ∧ j)) (k ∨ ~ r)
        ; (j = i0) → push (false , inl ((CasesBoolη f i)
                                      , ((a true) , (b true)))) (k ∨ ~ r)
        ; (j = i1) → push (false , push ((CasesBoolη f i)
                                        , (CasesBoolη a i
                                         , CasesBoolη-coh b i)) r) (k ∨ ~ r)
        ; (r = i0) → cube₁ i j i1
        ; (r = i1) → false-fill j i k})
       (hcomp (λ k →
       λ {(i = i0) → ×→Π∗-push²-fill-path (j ∨ r) (j ∧ (~ r)) (r ∧ k)
        ; (i = i1) → push (false
                         , push (f , a , CasesBoolη b k) (r ∧ (j ∧ k))) (~ r)
        ; (j = i0) → push (false , inl (CasesBoolη f i , a true , b true)) (~ r)
        ; (j = i1) → push (false
                           , push (CasesBoolη f i
                                 , CasesBoolη a i
                                 , CasesBoolη-coh-coh k i) (r ∧ k)) (~ r)
        ; (r = i0) → cube₁ i j i1
        ; (r = i1) → inl (false , f false , a true)})
        (hcomp (λ k →
        λ {(i = i0) → ×→Π∗-push²-fill-btm-path (j ∨ r) (j ∧ (~ r)) k
         ; (i = i1) → push (false
                           , push (f , (a , CasesBool true (b true) (b false)))
                             ((~ r ∧ ~ j)  ∧ ~ k)) (~ k ∨ (~ r))
         ; (j = i0) → push (false
                           , push ((CasesBoolη f i)
                                 , (a , CasesBool true (b true) (b false)))
                                 (~ r ∧ (~ k ∧ i))) (~ k ∨ (~ r))
         ; (j = i1) → push (false
                           , inl (CasesBoolη f i , a true , b true)) (~ k ∨ ~ r)
         ; (r = i0) → cube₁ i j k
         ; (r = i1) → push (false
                          , (inl (CasesBoolη f i , a true , b true))) (~ k)})
          (inr (push (CasesBoolη f i , a
                    , CasesBool true (b true) (b false)) (i ∧ (~ j ∧ ~ r))))))

Π∗→×→Π∗ : ∀ {ℓ} {J : RP∞' ℓ} (A : Bool → fst J → Type ℓ) (m : _)
  → ×→Π∗ J A (Π∗→× J A m) ≡ m
Π∗→×→Π∗ {J = J} A (inl (false , m)) = refl
Π∗→×→Π∗ {J = J} A (inl (true , m)) = refl
Π∗→×→Π∗ A (inr (inl x)) j = inr (inl (CasesBoolη x j))
Π∗→×→Π∗ {J = J} A (inr (inr x)) j =
  inr (inr (CasesBoolη {A = λ i → (j : fst J) → A i j} x j ))
Π∗→×→Π∗ {J = J} A (inr (push (f , a , b) i)) j =
  Π∗→×→Π∗-fillers.true-fill J A f a b i j i1
Π∗→×→Π∗ A (push (false , inl (f , q , t)) i) j =
  push (false , inl (CasesBoolη f j , q , t)) i
Π∗→×→Π∗ A (push (true , inl (f , q , t)) i) j =
  push (true , inl (CasesBoolη f j , q , t)) i
Π∗→×→Π∗ A (push (false , inr (f , q , t)) i) j =
  push (false , inr (f , CasesBoolη q j , t)) i
Π∗→×→Π∗ A (push (true , inr (f , q , t)) i) j =
  push (true , inr (f , CasesBoolη q j , t)) i
Π∗→×→Π∗ {J = J} A (push (false , push (f , q , t) i₂) i) j =
  hcomp (λ r →
  λ {(i = i0) → inl (false , f false , q true)
   ; (i = i1) → Π∗→×→Π∗-fillers.true-fill≡false-fill
                  J A f q t (~ r) i₂ j
   ; (j = i0) → ×→Π∗-push²-fill (fst J) A (fst (f true)) (fst (f false))
                          (snd (f true)) (snd (f false))
                          (q true) (q false)
                          (t true) (t false)
                          ((~ i) ∨ i₂) (i ∧ i₂) i1
   ; (j = i1) → push (false , push (f , q , t) i₂) i
   ; (i₂ = i0) → push (false , inl (CasesBoolη f j , q true , t true)) i
   ; (i₂ = i1) → push (false , inr (f false , CasesBoolη q j , t false)) i})
     (hcomp (λ r →
   λ {(i = i0) → inl (false , f false , q true)
    ; (i = i1) → Π∗→×→Π∗-fillers.false-fill J A f q t i₂ j r
    ; (j = i0) → ×→Π∗-push²-fill (fst J) A (fst (f true)) (fst (f false))
                           (snd (f true)) (snd (f false))
                           (q true) (q false)
                           (t true) (t false)
                           ((~ i) ∨ (i₂ ∨ ~ r)) (i ∧ (i₂ ∧ r)) i1
    ; (j = i1) → push (false , push (f , q , t) i₂) (r ∧ i)
    ; (i₂ = i0) → push (false
                      , (inl (CasesBoolη f j , (q true , t true)))) (i ∧ r)
    ; (i₂ = i1) → push (false
                       , inr (f false , CasesBoolη q j , t false)) (i ∧ r)})
    (inl (false , f false , q true)))
Π∗→×→Π∗ {J = J} A (push (true , push (f , q , t) i₂) i) j =
  hcomp (λ r →
  λ {(i = i0) → inl (true , f true , q false)
   ; (i = i1) → Π∗→×→Π∗-fillers.true-fill J A f q t i₂ j r
   ; (j = i0) → ×→Π∗-push²-fill (fst J) A (fst (f true)) (fst (f false))
                          (snd (f true)) (snd (f false))
                          (q true) (q false)
                          (t true) (t false)
                          (i ∧ (i₂ ∧ r)) ((~ i) ∨ (i₂ ∨ ~ r)) i1
   ; (j = i1) → push (true , push (f , q , t) i₂) (r ∧ i)
   ; (i₂ = i0) → push (true , inl (CasesBoolη f j , q false , t false)) (i ∧ r)
   ; (i₂ = i1) → push (true , inr (f true , CasesBoolη q j , t true)) (i ∧ r)})
    (inl (true , f true , q false))

-- so, finally, Π∗→× is an equivalence
Π∗→×Iso : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
  → Iso (ΠJoinR₁.Π∗ (RP∞'∙ ℓ) (fst J) A)
         (UnordJoinR-gen (fst J) (A true) × UnordJoinR-gen (fst J) (A false))
Iso.fun (Π∗→×Iso J A) = Π∗→× J A
Iso.inv (Π∗→×Iso J A) = ×→Π∗ J A
Iso.rightInv (Π∗→×Iso J A) = ×→Π∗→× {J = J} A
Iso.leftInv (Π∗→×Iso J A) = Π∗→×→Π∗ {J = J} A

-- this gives, via the following lemmas, that our original map
-- Π∗→Π is an equivalence
module _ {ℓ : Level} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
  where
  module Π∗→Π-equiv-base-lemmas where
    p : Π∗→Π-Bool J A ≡ ΠJoinR₁.Π∗→Π (RP∞'∙ ℓ) (fst J) A
    p = funExt λ x → funExt (Π∗→Π-Bool≡ {J = J} A x)

    alt : (ΠJoinR₁.Π∗ (RP∞'∙ ℓ) (fst J) A)
        ≃ ((x : Bool) → UnordJoinR-gen (fst J) (A x))
    alt = isoToEquiv (compIso (Π∗→×Iso J A) (invIso ΠBool×Iso))

    altid : fst alt ≡ Π∗→Π-Bool J A
    altid = funExt λ x → funExt (CasesBool true refl refl)

    isEq : isEquiv (Π∗→Π-Bool J A)
    isEq = subst isEquiv altid (snd alt)

  open Π∗→Π-equiv-base-lemmas
  Π∗→Π-equiv-base : isEquiv (ΠJoinR₁.Π∗→Π (RP∞'∙ ℓ) (fst J) A)
  Π∗→Π-equiv-base = transport (λ i → isEquiv (p i)) isEq

Π∗→Π-equiv : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
  → isEquiv (ΠJoinR₁.Π∗→Π I (fst J) A)
Π∗→Π-equiv {ℓ = ℓ} =
  RP∞'pt→Prop (λ _ → isPropΠ2 λ _ _ → isPropIsEquiv _) Π∗→Π-equiv-base

-- first theorem
Π∗≃ΠUnordJoinR : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
  → ΠJoinR₁.Π∗ I (fst J) A ≃ UnordΠ I λ i → UnordJoinR J (A i)
fst (Π∗≃ΠUnordJoinR I J A) = ΠJoinR₁.Π∗→Π I (fst J) A
snd (Π∗≃ΠUnordJoinR I J A) = Π∗→Π-equiv I J A

-- but ΠJoinR₁.Π∗ is still hard to work
-- it can be made nicer:
module ΠJoinR₂ {ℓ} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) where
  open ΠJoinR-gen I (fst J) A
         (Σ[ x ∈ fst J ⊎ (fst I ≃ fst J) ]
           ((i : fst I) → A i (fst (eval⊎≃Equiv I J) x i)))
         (λ i p → Iso.inv (UnordΠUnordΣ-charac I J {A}) p i .fst)
         (λ i x → Iso.inv (UnordΠUnordΣ-charac I J {A}) x i .snd)
       public

-- new goal: ΠJoinR₁.Π∗ ≃ ΠJoinR₂.Π∗

-- to do so we prove that ΠJoinR-genFunct is functorial
module ΠJoinR-genFunct {ℓ} (I : RP∞' ℓ) (J : Type) (A : fst I → J → Type ℓ)
       (AB AB' : Type ℓ) (e : AB → AB')
       (AB→J : (i : fst I) → AB → J)
       (AB→J' : (i : fst I) → AB' → J)
       (AB→J-coh : AB→J ≡ (λ i a → AB→J' i (e a)))
       (AB→A : (i : fst I) (a : AB) → A i (AB→J i a))
       (AB→A' : (i : fst I) (a : AB') → A i (AB→J' i a))
       (AB→A-coh : (i : fst I) (a : AB)
         → PathP (λ k → A i (AB→J-coh k i a)) (AB→A i a) (AB→A' i (e a)))
       where
  module J1 = ΠJoinR-gen I J A AB AB→J AB→A
  module J2 = ΠJoinR-gen I J A AB' AB→J' AB→A'
  open RP∞'-fields I

  ΠR-left-funct-push-fill : (a : AB) (i : fst I) (b : (j : J) → A i j)
                         (c : b (AB→J i a) ≡ AB→A i a)
                      → (k r : _) → A i (AB→J-coh r i a)
  ΠR-left-funct-push-fill a i b c k r =
    fill (λ r → A i (AB→J-coh r i a))
         (λ r → λ {(k = i0) → b (AB→J-coh r i a)
                  ; (k = i1) → AB→A-coh i a r})
         (inS (c k))
         r

  ΠR-left-funct-push : (a : AB) (i : fst I) (b : (j : J) → A i j)
                         (c : b (AB→J i a) ≡ AB→A i a)
                      → b (AB→J' i (e a)) ≡ AB→A' i (e a)
  ΠR-left-funct-push a i b c k = ΠR-left-funct-push-fill a i b c k i1


  module _ (i : fst I) (a : AB) (f : (i : fst I) (j : J) → A i j)
           (q : (i : fst I) → f i (AB→J i a) ≡ AB→A i a) where
    push-push-fill : (j k r : _) → A i (AB→J-coh (~ j ∧ r) i a)
    push-push-fill j k r =
      fill (λ r → A i (AB→J-coh (~ j ∧ r) i a))
           (λ r → λ {(k = i0) → f i (AB→J-coh (~ j ∧ r) i a)
                    ; (k = i1) → AB→A-coh i a (~ j ∧ r)
                    ; (j = i0) → ΠR-left-funct-push-fill a i (f i) (q i) k r
                    ; (j = i1) → q i k})
           (inS (q i k))
           r

    push-push-coh : PathP (λ r → f i (AB→J-coh (~ r) i a)
                                ≡ AB→A-coh i a (~ r))
                          (ΠR-left-funct-push a i (f i) (q i))
                          (q i)
    push-push-coh j k = push-push-fill j k i1

    push-push : (k j r : _) → J2.Π∗
    push-push k j r =
      hfill (λ r →
      λ {(k = i0) → inl (i , (AB→J-coh (~ r) i a , AB→A-coh i a (~ r))
                            , f (notRP∞' i))
       ; (k = i1) → inr (push (e a , f
                            , (λ i₁ → ΠR-left-funct-push a i₁ (f i₁) (q i₁))) j)
       ; (j = i0) → compPath-filler'
            (λ k → inl (i , (AB→J-coh k i a , AB→A-coh i a k)
                           , (f (notRP∞' i))))
            (push (i , inl (e a , f (notRP∞' i)
                          , ΠR-left-funct-push a (notRP∞' i)
                              (f (notRP∞' i)) (q (notRP∞' i))))) r k
       ; (j = i1) → push (i , inr ((AB→J-coh (~ r) i a , AB→A-coh i a (~ r))
                        , f
                        , push-push-coh r)) k})
       (inS (push (i , (push ((e a) , (f
                , (λ i → ΠR-left-funct-push a i (f i) (q i)))) j)) k))
       r

  ΠR-left-funct : J1.Π∗-base → J2.Π∗-base
  ΠR-left-funct (inl x) = inl (e x)
  ΠR-left-funct (inr x) = inr x
  ΠR-left-funct (push (a , b , c) i) =
    push (e a , b , λ i → ΠR-left-funct-push a i (b i) (c i)) i

  Π-extend-funct : J1.Π∗ → J2.Π∗
  Π-extend-funct (inl x) = inl x
  Π-extend-funct (inr x) = inr (ΠR-left-funct x)
  Π-extend-funct (push (i , inl (a , b , c)) k) =
      ((λ k → inl (i , (AB→J-coh k i a , AB→A-coh i a k) , b))
    ∙ push (i , inl ((e a) , b , ΠR-left-funct-push a (notRP∞' i) b c))) k
  Π-extend-funct (push (i , inr x) k) = push (i , (inr x)) k
  Π-extend-funct (push (i , push (a , f , q) j) k) = push-push i a f q k j i1

module ΠJoinR-genFunct-refl {ℓ} (I : RP∞' ℓ) (J : Type) (A : fst I → J → Type ℓ)
       (AB : Type ℓ)
       (AB→J : (i : fst I) → AB → J)
       (AB→A : (i : fst I) (a : AB) → A i (AB→J i a))
       where
  module M = ΠJoinR-genFunct I J A AB AB (idfun AB)
              AB→J AB→J refl AB→A AB→A (λ i a → refl)

  open RP∞'-fields I
  open M

  module _ (a : AB) (i : fst I) (b : (j : J) → A i j)
           (q : b (AB→J i a) ≡ AB→A i a) where
    ΠR-left-funct-push≡id-fill : (r k z : _) → A i (AB→J i a)
    ΠR-left-funct-push≡id-fill r k z =
      hfill (λ z → λ {(k = i0) → b (AB→J i a)
                     ; (k = i1) → AB→A i a
                     ; (r = i0) → ΠR-left-funct-push-fill a i b q k z
                     ; (r = i1) → q k})
            (inS (q k))
            z

    ΠR-left-funct-push≡id : ΠR-left-funct-push a i b q ≡ q
    ΠR-left-funct-push≡id r k = ΠR-left-funct-push≡id-fill r k i1

  ΠR-left-funct≡ : (x : _) → ΠR-left-funct x ≡ x
  ΠR-left-funct≡ (inl x) = refl
  ΠR-left-funct≡ (inr x) = refl
  ΠR-left-funct≡ (push (i , f , q) k) r =
    push (i , f , λ i' → ΠR-left-funct-push≡id i i' (f i') (q i') r) k

  Π-extend-funct≡ : (x : _) → Π-extend-funct x ≡ x
  Π-extend-funct≡ (inl x) = refl
  Π-extend-funct≡ (inr x) i = inr (ΠR-left-funct≡ x i)
  Π-extend-funct≡ (push (i , inl (a , b , c)) k) j =
    hcomp (λ r →
    λ {(j = i0) → compPath-filler' refl
                    (push (i , inl (a , b
                         , ΠR-left-funct-push a (notRP∞' i) b c))) r k
     ; (j = i1) → push (i , inl (a , b , c)) k
     ; (k = i0) → inl (i , J2.AB→Σ i a , b)
     ; (k = i1) → inr (inl a)})
     (push (i , (inl (a , b , ΠR-left-funct-push≡id a (notRP∞' i) b c j))) k)
  Π-extend-funct≡ (push (i , inr x) k) j = push (i , inr x) k
  Π-extend-funct≡ (push (i , push (a , b , c) r) k) j =
    hcomp (λ z →
    λ {(j = i0) → push-push i a b c k r z
     ; (j = i1) → push (i , push (a , b , c) r) k
     ; (k = i0) → inl (i , J2.AB→Σ i a , b (notRP∞' i))
     ; (k = i1) → inr (push (a , (b
                          , (λ i → ΠR-left-funct-push≡id a i (b i) (c i) j))) r)
     ; (r = i1) → push (i , (inr ((AB→J i a , AB→A i a) , b , lem z j))) k})
    (push (i , (push (a , b
             , λ i → ΠR-left-funct-push≡id a i (b i) (c i) j) r)) k)
    where
    lem : Square (ΠR-left-funct-push≡id a i (b i) (c i)) refl
                 (push-push-coh i a b c) refl
    lem z j r =
      hcomp (λ w → λ {(r = i0) → b i (AB→J i a)
                     ; (r = i1) → AB→A i a
                     ; (j = i0) → push-push-fill i a b c z r w
                     ; (j = i1) → c i r
                     ; (z = i1) → c i r})
               (c i r)

  isEquiv-Π-extend-funct : isEquiv Π-extend-funct
  isEquiv-Π-extend-funct =
    subst isEquiv (sym (funExt Π-extend-funct≡)) (idIsEquiv _)

ΠJoinR-genFunctEquiv : ∀ {ℓ}
  (I : RP∞' ℓ) (J : Type) (A : fst I → J → Type ℓ)
  (AB AB' : Type ℓ) (e : AB ≃ AB')
  (AB→J : (i : fst I) → AB → J)
  (AB→J' : (i : fst I) → AB' → J)
  (AB→J-coh : AB→J ≡ (λ i a → AB→J' i (fst e a)))
  (AB→A : (i : fst I) (a : AB) → A i (AB→J i a))
  (AB→A' : (i : fst I) (a : AB') → A i (AB→J' i a))
  (AB→A-coh : (i : fst I) (a : AB)
    → PathP (λ k → A i (AB→J-coh k i a)) (AB→A i a) (AB→A' i (fst e a)))
    → isEquiv (ΠJoinR-genFunct.Π-extend-funct I J A AB AB' (fst e)
                 AB→J AB→J' AB→J-coh AB→A AB→A' AB→A-coh)
ΠJoinR-genFunctEquiv I J A AB =
  EquivJ> λ AB→J → J> λ AB→A AB→A' AB→A-coh
    → main AB→J AB→A AB→A' λ k a b → AB→A-coh a b k
  where
  main : (AB→J : fst I → AB → J)
    (AB→A : (i : fst I) (a : AB) → A i (AB→J i a))
    (AB→A' : (i : fst I) (a : AB) → A i (AB→J i a))
    (AB→A-coh : AB→A ≡ AB→A')
    → isEquiv (ΠJoinR-genFunct.Π-extend-funct I J A AB AB (idfun _)
                 AB→J AB→J refl AB→A AB→A' λ i a k → AB→A-coh k i a)
  main AB→J AB→A =
    J> ΠJoinR-genFunct-refl.isEquiv-Π-extend-funct I J A AB AB→J AB→A

-- The following
module _ {ℓ} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) where
  open ΠJoinR-genFunct I (fst J) A
       (Σ[ e ∈ fst J ⊎ (fst I ≃ fst J) ]
         ((i : fst I) → A i (eval⊎≃ e i)))
       (UnordΠ I (λ i → UnordΣ J (A i)))
       (Iso.inv (UnordΠUnordΣ-charac I J))
       (λ i p → eval⊎≃ (p .fst) i)
       (λ i p → p i .fst)
       refl
       (λ i a → snd a i)
       (λ i a → a i .snd)
       (λ _ _ → refl)

  open RP∞'-fields I

  Π-extend-funct-main : ΠJoinR₂.Π∗ I J A → ΠJoinR₁.Π∗ I (fst J) A
  Π-extend-funct-main = Π-extend-funct

  isEq-Π-extend-funct-main : isEquiv Π-extend-funct-main
  isEq-Π-extend-funct-main = ΠJoinR-genFunctEquiv I (fst J) A _ _
    (invEquiv (isoToEquiv (UnordΠUnordΣ-charac I J))) _ _ _ _ _ _

  Π∗-base₂→Π∗-base₁ : ΠJoinR₂.Π∗-base I J A → ΠJoinR₁.Π∗-base I (fst J) A
  Π∗-base₂→Π∗-base₁ (inl (e , b)) = inl λ i → eval⊎≃ e i , b i
  Π∗-base₂→Π∗-base₁ (inr x) = inr x
  Π∗-base₂→Π∗-base₁ (push ((x , a) , b) i) =
    push ((λ i → eval⊎≃ x i , a i) , b) i

  Π∗₂→Π∗₁ : ΠJoinR₂.Π∗ I J A → ΠJoinR₁.Π∗ I (fst J) A
  Π∗₂→Π∗₁ (inl x) = inl x
  Π∗₂→Π∗₁ (inr x) = inr (Π∗-base₂→Π∗-base₁ x)
  Π∗₂→Π∗₁ (push (i , inl ((e , a) , b)) k) =
    push (i , inl ((λ i → eval⊎≃ e i , a i) , b)) k
  Π∗₂→Π∗₁ (push (i , inr x) k) = push (i , inr x) k
  Π∗₂→Π∗₁ (push (i , push ((e , a) , b) j) k) =
    push (i , push ((λ i → eval⊎≃ e i , a i) , b) j) k

  module _ (e : fst J ⊎ (fst I ≃ fst J)) (a : (i : fst I) → A i (eval⊎≃ e i))
           (i : fst I)
           (b : (j : fst J) → A i j)
           (q : b (eval⊎≃ e i) ≡ a i) where
    ΠR-left-funct-push≡id-fill : (r k z : _) → A i (eval⊎≃ e i)
    ΠR-left-funct-push≡id-fill r k z =
      hfill (λ z → λ {(k = i0) → b (eval⊎≃ e i)
                     ; (k = i1) → a i
                     ; (r = i0) → ΠR-left-funct-push-fill (e , a) i b q k z
                     ; (r = i1) → q k})
            (inS (q k))
            z

    ΠR-left-funct-push≡id : ΠR-left-funct-push (e , a) i b q ≡ q
    ΠR-left-funct-push≡id r k = ΠR-left-funct-push≡id-fill r k i1

  ΠR-left-funct≡ : (x : _) → ΠR-left-funct x ≡ Π∗-base₂→Π∗-base₁ x
  ΠR-left-funct≡ (inl x) = refl
  ΠR-left-funct≡ (inr x) = refl
  ΠR-left-funct≡ (push ((e , a) , b , q) k) r =
    push ((λ i → eval⊎≃ e i , a i)
        , (b
        , (λ i' → ΠR-left-funct-push≡id e a i' (b i') (q i') r))) k

  Π∗₂→Π∗₁≡ : (x : _) → Π-extend-funct-main x ≡ Π∗₂→Π∗₁ x
  Π∗₂→Π∗₁≡ (inl x) = refl
  Π∗₂→Π∗₁≡ (inr x) r = inr (ΠR-left-funct≡ x r)
  Π∗₂→Π∗₁≡ (push (i , inl ((e , a) , b , c)) k) j =
    hcomp (λ r →
    λ {(j = i0) → compPath-filler' refl
                    (push (i , inl ((λ i → eval⊎≃ e i , a i) , b
                        , ΠR-left-funct-push (e , a) (notRP∞' i) b c))) r k
     ; (j = i1) → push (i , inl ((λ i → eval⊎≃ e i , a i) , b , c)) k
     ; (k = i0) → inl (i , (eval⊎≃ e i , a i) , b)
     ; (k = i1) → inr (inl λ i → eval⊎≃ e i , a i)})
    (push (i , (inl ((λ i → eval⊎≃ e i , a i) , b
             , ΠR-left-funct-push≡id e a (notRP∞' i) b c j))) k)
  Π∗₂→Π∗₁≡ (push (i , inr x) k) = refl
  Π∗₂→Π∗₁≡ (push (i , push ((e , a) , b , c) r) k) j =
    hcomp (λ z →
    λ {(j = i0) → push-push i (e , a) b c k r z
     ; (j = i1) → push (i , push ((λ i → eval⊎≃ e i , a i) , (b , c)) r) k
     ; (k = i0) → inl (i , (eval⊎≃ e i , a i) , (b (notRP∞' i)))
     ; (k = i1) → inr (push ((λ i → eval⊎≃ e i , a i) , (b
                     , (λ i → ΠR-left-funct-push≡id e a i (b i) (c i) j))) r)
     ; (r = i1) → push (i , (inr ((eval⊎≃ e i , a i) , b , lem z j))) k })
     (push (i , push ((λ i → eval⊎≃ e i , a i)
             , (b , (λ i → ΠR-left-funct-push≡id e a i (b i) (c i) j))) r) k)
    where
    lem : Square (ΠR-left-funct-push≡id e a i (b i) (c i)) refl
                 (push-push-coh i (e , a) b c) refl
    lem z j r =
      hcomp (λ w → λ {(r = i0) → b i (eval⊎≃ e i)
                     ; (r = i1) → a i
                     ; (j = i0) → push-push-fill i (e , a) b c z r w
                     ; (j = i1) → c i r
                     ; (z = i1) → c i r
                     })
               (c i r)

  isEquiv-Π∗₂→Π∗₁ : isEquiv Π∗₂→Π∗₁
  isEquiv-Π∗₂→Π∗₁ =
    subst isEquiv (funExt Π∗₂→Π∗₁≡) isEq-Π-extend-funct-main

  Π∗₂≃Π∗₁ : ΠJoinR₂.Π∗ I J A ≃ ΠJoinR₁.Π∗ I (fst J) A
  fst Π∗₂≃Π∗₁ = Π∗₂→Π∗₁
  snd Π∗₂≃Π∗₁ = isEquiv-Π∗₂→Π∗₁

-- This equivalence allows us to beter undertand
-- nestled underordererd joins.

-- Goal: rewrite nestled unordered join as a pushout involving ΠJoinR₂.Π∗
-- We start with the maps involved
module _ {ℓ : Level} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) where
  open ΠJoinR₂ I J A
  ΠΣ→ΠJoinR : (i' : fst I) → Σ (fst J) (A i')
              → ((j : fst J) → A (RP∞'-fields.notRP∞' I i') j)
              → (i : fst I) → UnordJoinR-gen (fst J) (A i)
  ΠΣ→ΠJoinR i' t p =
    RP∞'-fields.elimRP∞' I {B = λ i → UnordJoinR-gen (fst J) (A i)} i'
      (inlR t) (inrR p)

  ΠΣ→ΠJoinRβ : (i : fst I) (a : _) (b : _)
    → (ΠΣ→ΠJoinR i a b i ≡ inlR a)
     × (ΠΣ→ΠJoinR i a b (RP∞'-fields.notRP∞' I i) ≡ inrR b)
  fst (ΠΣ→ΠJoinRβ i a b) = RP∞'-fields.elimRP∞'β I i (inlR a) (inrR b) .fst
  snd (ΠΣ→ΠJoinRβ i a b) = RP∞'-fields.elimRP∞'β I i (inlR a) (inrR b) .snd

  Π∗-base₂→JoinR : (i : fst I) → Π∗-base → UnordJoinR-gen (fst J) (A i)
  Π∗-base₂→JoinR i (inl (inl x , y)) = inlR (x , y i)
  Π∗-base₂→JoinR i (inl (inr x , y)) = inlR (fst x i , y i)
  Π∗-base₂→JoinR i (inr x) = inrR (x i)
  Π∗-base₂→JoinR i (push ((inl e , y) , b) j) =
    pushR (e , y i) (fst b i) (b .snd i) j
  Π∗-base₂→JoinR i (push ((inr e , y) , b) j) =
    pushR (fst e i , y i) (fst b i) (snd b i) j

  PushTop→JoinRₗ : (i : fst I) (x : PushTop i)
    → inlR (Pushtop→ΠR-left' i x .fst)
     ≡ Π∗-base₂→JoinR i (ΣPushtop→Π∗-base (i , x))
  PushTop→JoinRₗ i (inl ((inl x , p) , f , q)) = refl
  PushTop→JoinRₗ i (inl ((inr x , p) , f , q)) = refl
  PushTop→JoinRₗ i (inr ((j , a) , f , q)) = pushR (j , a) (f i) q
  PushTop→JoinRₗ i (push ((inl j , p) , f) k) l =
    pushR (j , p i) (fst f i) (snd f i) (k ∧ l)
  PushTop→JoinRₗ i (push ((inr x , p) , f) k) l =
    pushR (fst x i , p i) (fst f i) (snd f i) (k ∧ l)

  PushTop→JoinRᵣ : (i : fst I) (x : PushTop i)
      → inrR (Pushtop→ΠR-left' i x .snd)
      ≡ Π∗-base₂→JoinR (fst (snd I .fst) i) (ΣPushtop→Π∗-base (i , x))
  PushTop→JoinRᵣ i (inl ((inl x , p) , f , q)) =
    sym (pushR (x , p (RP∞'-fields.notRP∞' I i)) f q)
  PushTop→JoinRᵣ i (inl ((inr x , p) , f , q)) =
    sym (pushR (fst x (RP∞'-fields.notRP∞' I i)
                  , p (RP∞'-fields.notRP∞' I i)) f q)
  PushTop→JoinRᵣ i (inr ((j , a) , f , q)) = refl
  PushTop→JoinRᵣ i (push ((inl j , p) , f) k) l =
    pushR (j , p (fst (snd I .fst) i))
         (fst f (I .snd .fst .fst i)) (snd f (I .snd .fst .fst i)) (~ l ∨ k)
  PushTop→JoinRᵣ i (push ((inr x , p) , f) k) l =
    pushR (fst x (snd I .fst .fst i) , p (fst (snd I .fst) i))
         (fst f (I .snd .fst .fst i)) (snd f (I .snd .fst .fst i)) (~ l ∨ k)

  PushTop→JoinR : (i' : fst I) (x : PushTop i') (i : fst I)
    → ΠΣ→ΠJoinR i'
          (Pushtop→ΠR-left' i' x .fst)
          (Pushtop→ΠR-left' i' x .snd) i
     ≡ Π∗-base₂→JoinR i (ΣPushtop→Π∗-base (i' , x))
  PushTop→JoinR i' x =
    RP∞'-fields.elimRP∞' I i'
      (ΠΣ→ΠJoinRβ i'
         (Pushtop→ΠR-left' i' x .fst)
         (Pushtop→ΠR-left' i' x .snd) .fst
    ∙ PushTop→JoinRₗ i' x)
      (ΠΣ→ΠJoinRβ i'
         (Pushtop→ΠR-left' i' x .fst)
         (Pushtop→ΠR-left' i' x .snd) .snd
     ∙ PushTop→JoinRᵣ i' x)

  Π∗₂→JoinR : (i : fst I) → Π∗ → UnordJoinR-gen (fst J) (A i)
  Π∗₂→JoinR i (inl (i' , a , b)) = ΠΣ→ΠJoinR i' a b i
  Π∗₂→JoinR i (inr x) = Π∗-base₂→JoinR i x
  Π∗₂→JoinR i (push (i' , x) i₁) = PushTop→JoinR i' x i i₁

  ΣΠ∗₂→ΣJoinR : (x : fst I × Π∗)
    → Σ[ i ∈ fst I ] (UnordJoinR-gen (fst J) (A i))
  ΣΠ∗₂→ΣJoinR (i , a) = i , Π∗₂→JoinR i a

module _ (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) where
  open ΠJoinR₂ I J A

  UnordJoinR² : Type ℓ
  UnordJoinR² = UnordJoinR I λ i → UnordJoinR J (A i)

  UnordJoin² : Type ℓ
  UnordJoin² = UnordJoin I λ i → UnordJoinR J (A i)

  UnordJoinR²≃UnordJoin² : UnordJoinR² ≃ UnordJoin²
  UnordJoinR²≃UnordJoin² = isoToEquiv UnordJoinIso

  UnordJoin²₂ : Type ℓ
  UnordJoin²₂ = Pushout {A = fst I × Π∗} (ΣΠ∗₂→ΣJoinR I J A) snd

Π∗₂≃ΠUnordJoinR : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
  → ΠJoinR₂.Π∗ I J A ≃ UnordΠ I (λ i → UnordJoinR J (A i))
Π∗₂≃ΠUnordJoinR I J A =
  compEquiv (Π∗₂≃Π∗₁ I J A) (Π∗≃ΠUnordJoinR I J A)

UnordJoin²₂≃UnordJoin² : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
  → UnordJoin²₂ I J A ≃ UnordJoinR² I J A
UnordJoin²₂≃UnordJoin² {ℓ = ℓ} I J A =
  compEquiv
    (isoToEquiv
      (pushoutIso _ _ _ _
       (Σ-cong-equiv-snd (λ _ → Π∗₂≃ΠUnordJoinR I J A))
       (idEquiv _)
       (Π∗₂≃ΠUnordJoinR I J A)
       (funExt (uncurry λ i x → ΣPathP (refl , main-coh I i A x)))
       refl))
    (invEquiv (UnordJoinR²≃UnordJoin² I J A))
  where
  module _ (A : Bool → fst J → Type ℓ) where
    Π∗₂→JoinRBool :
      ΠJoinR₂.Π∗ (RP∞'∙ ℓ) J A → UnordJoinR-gen (fst J) (A true)
    Π∗₂→JoinRBool (inl (i' , a , b)) = ΠΣ→ΠJoinR (RP∞'∙ _) J A i' a b true
    Π∗₂→JoinRBool (inr x) = Π∗-base₂→JoinR (RP∞'∙ _) J A true x
    Π∗₂→JoinRBool (push (false , a) k) =
      PushTop→JoinRᵣ (RP∞'∙ _) J A false a k
    Π∗₂→JoinRBool (push (true , y) k) =
      PushTop→JoinRₗ (RP∞'∙ _) J A true y k

    leftFunBool≡' : (x : ΠJoinR₂.Π∗ (RP∞'∙ ℓ) J A)
      → Π∗₂→JoinR (RP∞'∙ _) J A true x ≡ Π∗₂→JoinRBool x
    leftFunBool≡' (inl x) = refl
    leftFunBool≡' (inr x) = refl
    leftFunBool≡' (push (false , a) k) j =
      lUnit (PushTop→JoinRᵣ (RP∞'∙ _) J A false a) (~ j) k
    leftFunBool≡' (push (true , a) k) j =
      lUnit (PushTop→JoinRₗ (RP∞'∙ _) J A true a) (~ j) k

    main : (x : _)
      → Π∗₂→JoinRBool x
       ≡ Π∗→Π-Bool J A (Π∗₂→Π∗₁ (RP∞'∙ ℓ) J A x) true
    main (inl (false , b)) = refl
    main (inl (true , b)) = refl
    main (inr (inl (inl x , b))) = refl
    main (inr (inl (inr x , b))) = refl
    main (inr (inr x)) = refl
    main (inr (push ((inl x , b) , c) i)) = refl
    main (inr (push ((inr x , b) , c) i)) = refl
    main (push (false , inl ((inl x , b) , c)) i) = refl
    main (push (false , inl ((inr x , b) , c)) i) = refl
    main (push (false , inr x) i) = refl
    main (push (false , push ((inl x , b) , c) i₁) i) = refl
    main (push (false , push ((inr x , b) , c) i₁) i) = refl
    main (push (true , inl ((inl x , b) , c)) i) = refl
    main (push (true , inl ((inr x , b) , c)) i) = refl
    main (push (true , inr x) i) = refl
    main (push (true , push ((inl x , b) , c) i₁) i) = refl
    main (push (true , push ((inr x , b) , c) i₁) i) = refl

  main-coh : (I : RP∞' ℓ) (i : fst I) (A : fst I → fst J → Type ℓ)
    → (x : ΠJoinR₂.Π∗ I J A)
      → Π∗₂→JoinR I J A i x
       ≡ Π∗₂≃ΠUnordJoinR I J A .fst x i
  main-coh = JRP∞' λ A x
    → leftFunBool≡' A x
    ∙∙ main A x
    ∙∙ Π∗→Π-Bool≡ {J = J} A
        (Π∗₂→Π∗₁ (RP∞'∙ ℓ) J A x) true
