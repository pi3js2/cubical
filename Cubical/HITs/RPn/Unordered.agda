{-# OPTIONS --safe --lossy-unification #-}

{-
This file contains
1. The Thom isomorphism (various related forms of it)
2. The Gysin sequence
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence

open import Cubical.Data.Sigma
open import Cubical.Data.Bool
open import Cubical.Data.Sum as ⊎

open import Cubical.HITs.Pushout
open import Cubical.HITs.RPn.Base
open import Cubical.HITs.Join


open import Cubical.Relation.Nullary
open import Cubical.HITs.SmashProduct


module Cubical.HITs.RPn.Unordered where


open import Cubical.Functions.FunExtEquiv

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

-- characterisation of nestled UnordΠ and UnordΣ
module UnordΠUnordΣ-charac-lemmas {ℓ : Level} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) where
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

-- Analysis of Πᵢ (JoinR Aᵢ)
module ΠJoinR-gen {ℓ} (I : RP∞' ℓ) (J : Type) (A : fst I → J → Type ℓ)
       (AB : Type ℓ) (AB→J : (i : fst I) → AB → J)
       (AB→A : (i : fst I) (a : AB) → A i (AB→J i a))
  where
  open RP∞'-fields I

  fat : Type ℓ
  fat = Σ[ a ∈ AB ]
           Σ[ g ∈ ((i : fst I) (j : J) → A i j) ]
             ((i : fst I) → g i (AB→J i a) ≡ AB→A i a)
  ΠR-base : Type ℓ
  ΠR-base = Pushout {A = fat} {B = AB} {C = ((i : fst I) (j : J) → A i j)}
                       fst (fst ∘ snd)

  left-push : Type _
  left-push = Σ[ i ∈ fst I ] (Σ[ j ∈ J ] (A i j)) × ((j : J) → A (notRP∞' i) j)

  left-push↑ₗ : fst I → Type _
  left-push↑ₗ i = Σ[ f ∈ AB ]
    Σ[ g ∈ ((j : J) → A (notRP∞' i) j) ] g (AB→J (notRP∞' i) f) ≡ AB→A (notRP∞' i) f

  left-push↑ᵣ : fst I → Type _
  left-push↑ᵣ i = Σ[ f ∈ (Σ[ j ∈ J ] A i j) ]
      Σ[ g ∈ ((i : fst I) (j : J) → A i j) ] g i (fst f) ≡ snd f

  fat→ₗ : (i : fst I) → fat → left-push↑ₗ i
  fat→ₗ  i (f , g , r) = (f , (g (notRP∞' i)) , (r (notRP∞' i)))

  fat→ᵣ : (i : fst I) → fat → left-push↑ᵣ i
  fat→ᵣ i (f , g , r) =  (AB→J i f , AB→A i f) , g , r i

  PushTop₂ : (i : fst I) → Type ℓ
  PushTop₂ i = Pushout (fat→ₗ i) (fat→ᵣ i)
  

  PushTop : Type _
  PushTop = Σ[ i ∈ fst I ] (PushTop₂ i)

  AB→Σ : (i : fst I) → AB → Σ J (A i)
  fst (AB→Σ a f) = AB→J a f
  snd (AB→Σ a f) = AB→A a f

  PushTop→left-push' : (i : fst I)
    → (Pushout (fat→ₗ i) (fat→ᵣ i))
    → (Σ[ j ∈ J ] (A i j)) × ((j : J) → A (notRP∞' i) j)
  PushTop→left-push' i (inl (f , g , p)) = AB→Σ i f , g
  PushTop→left-push' i (inr (f , g , p)) = f , (g (notRP∞' i))
  PushTop→left-push' i (push (f , g , p) k) = (AB→Σ i f) , g (notRP∞' i)

  PushTop→left-push : PushTop → left-push
  PushTop→left-push (i , x) = (i , PushTop→left-push' i x)

  PushTop→ΠR-base : PushTop → ΠR-base
  PushTop→ΠR-base (i , inl (f , g , p)) = inl f
  PushTop→ΠR-base (i , inr (f , g , p)) = inr g
  PushTop→ΠR-base (i , push (f , g , p)  j) = push (f , g , p) j

  ΠR-extend : Type _
  ΠR-extend = Pushout PushTop→left-push PushTop→ΠR-base

{-
Instantiating above with:

AB = ((i : fst I) → Σ J (A i))
AB→J = (λ i f → f i .fst)
AB→A = (λ i f → f i .snd)

yields a type ΠR-extend mapping into Πᵢ (JoinR Aᵢ)
-}
module ΠJoinR₁ {ℓ : Level} (I : RP∞' ℓ) (J : Type) (A : fst I → J → Type ℓ) where
  open ΠJoinR-gen I J A
    ((i : fst I) → Σ J (A i)) (λ i f → f i .fst) (λ i f → f i .snd)
    public
  open RP∞'-fields I

  ΠR-extend→Πₗ : left-push → ((i : fst I) → UnordJoinR-gen J (A i))
  ΠR-extend→Πₗ (i , p , r) = elimRP∞' i (inlR p) (inrR r)

  ΠR-base→ : ΠR-base → ((i : fst I) → UnordJoinR-gen J (A i))
  ΠR-base→ (inl x) i = inlR (x i)
  ΠR-base→ (inr x) i = inrR λ j → x i j
  ΠR-base→ (push a i') i = pushR (fst a i) (fst (snd a) i) (snd (snd a) i) i'

  pre-eqvl-diag : (i' : fst I) (p : Pushout (fat→ₗ i') (fat→ᵣ i'))
    → ΠR-extend→Πₗ (PushTop→left-push (i' , p)) i'
     ≡ ΠR-base→ (PushTop→ΠR-base (i' , p)) i'
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

  pre-eqvl-not : (i' : fst I) (p : Pushout (fat→ₗ i') (fat→ᵣ i'))
    → ΠR-extend→Πₗ (PushTop→left-push (i' , p)) (notRP∞' i') ≡
      ΠR-base→ (PushTop→ΠR-base (i' , p)) (notRP∞' i')
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


  eqvl : (a : PushTop) (i : fst I)
    → ΠR-extend→Πₗ (PushTop→left-push a) i
     ≡ ΠR-base→ (PushTop→ΠR-base a) i
  eqvl (i' , p) =
    elimRP∞' i' (pre-eqvl-diag i' p)
                 (pre-eqvl-not i' p)

  -- main map
  ΠR-extend→Π : ΠR-extend → ((i : fst I) → UnordJoinR-gen J (A i))
  ΠR-extend→Π (inl t) = ΠR-extend→Πₗ t
  ΠR-extend→Π (inr x) = ΠR-base→ x
  ΠR-extend→Π (push a i) i' = eqvl a i' i

-- let's show that ΠR-extend→Π is an equivalence.
-- It's enough to do so when I is Bool.
-- Let's give ΠR-extend→Π an explicit definition in this case
ΠR-extend→Π-Bool :
  ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → (fst J) → Type ℓ)
  → ΠJoinR₁.ΠR-extend (RP∞'∙ ℓ) (fst J) A
  → ((i : Bool) → UnordJoinR-gen (fst J) (A i))
ΠR-extend→Π-Bool J A (inl (false , f , p)) false = inlR f
ΠR-extend→Π-Bool J A (inl (false , f , p)) true = inrR p
ΠR-extend→Π-Bool J A (inl (true , f , p)) false = inrR p
ΠR-extend→Π-Bool J A (inl (true , f , p)) true = inlR f
ΠR-extend→Π-Bool J A (inr (inl x)) a = inlR (x a)
ΠR-extend→Π-Bool J A (inr (inr x)) b = inrR (x b)
ΠR-extend→Π-Bool J A (inr (push a i)) c =
  pushR (fst a c) (fst (snd a) c) (snd (snd a) c) i
ΠR-extend→Π-Bool J A (push (false , inl x) i) false = inlR (fst x false)
ΠR-extend→Π-Bool J A (push (false , inr x) i) false =
  pushR (fst x) (fst (snd x) false) (snd (snd x)) i
ΠR-extend→Π-Bool J A (push (false , push (f , p , q) j) i) false =
  pushR (f false) (p false) (q false) (i ∧ j)
ΠR-extend→Π-Bool J A (push (false , inl x) i) true =
  pushR (fst x true) (fst (snd x)) (snd (snd x)) (~ i)
ΠR-extend→Π-Bool J A (push (false , inr x) i) true = inrR (fst (snd x) true)
ΠR-extend→Π-Bool J A (push (false , push (f , p , q) j) i) true =
  pushR (f true) (p true) (q true) (~ i ∨ j)
ΠR-extend→Π-Bool J A (push (true , inl x) i) false =
  pushR (fst x false) (fst (snd x)) (snd (snd x)) (~ i)
ΠR-extend→Π-Bool J A (push (true , inr x) i) false = inrR (fst (snd x) false)
ΠR-extend→Π-Bool J A (push (true , push (f , p , q) j) i) false =
  pushR (f false) (p false) (q false) (~ i ∨ j)
ΠR-extend→Π-Bool J A (push (true , inl x) i) true = inlR (fst x true)
ΠR-extend→Π-Bool J A (push (true , inr x) i) true =
  pushR (fst x) (fst (snd x) true) (snd (snd x)) i
ΠR-extend→Π-Bool J A (push (true , push (f , p , q) j) i) true =
  pushR (f true) (p true) (q true) (i ∧ j)

-- ΠR-extend→Π-Bool agrees with our original definition
ΠR-extend→Π-Bool≡ : ∀ {ℓ} {J : RP∞' ℓ} (A : Bool → fst J → Type ℓ)
  → (x : _) (z : _) → ΠR-extend→Π-Bool J A x z
                     ≡ ΠJoinR₁.ΠR-extend→Π (RP∞'∙ ℓ) (fst J) A x z
ΠR-extend→Π-Bool≡ A (inl (false , y)) false = refl
ΠR-extend→Π-Bool≡ A (inl (false , y)) true = refl
ΠR-extend→Π-Bool≡ A (inl (true , y)) false = refl
ΠR-extend→Π-Bool≡ A (inl (true , y)) true = refl
ΠR-extend→Π-Bool≡ A (inr (inl x)) z = refl
ΠR-extend→Π-Bool≡ A (inr (inr x)) z = refl
ΠR-extend→Π-Bool≡ A (inr (push a i)) false = refl
ΠR-extend→Π-Bool≡ A (inr (push a i)) true = refl
ΠR-extend→Π-Bool≡ A (push (false , inl x) i) false = refl
ΠR-extend→Π-Bool≡ A (push (false , inr x) i) false j =
  lUnit (pushR (fst x) (fst (snd x) false) (snd (snd x))) j i
ΠR-extend→Π-Bool≡ A (push (false , push a j) i) false k =
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
ΠR-extend→Π-Bool≡ A (push (true , inl x) i) false j =
  lUnit (sym (pushR (fst x false) (fst (snd x)) (snd (snd x)))) j i
ΠR-extend→Π-Bool≡ A (push (true , inr x) i) false = refl
ΠR-extend→Π-Bool≡ A (push (true , push a j) i) false k =
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
ΠR-extend→Π-Bool≡ A (push (false , inl x) i) true j =
  lUnit (sym (pushR (fst x true) (fst (snd x)) (snd (snd x)))) j i
ΠR-extend→Π-Bool≡ A (push (false , inr x) i) true = refl
ΠR-extend→Π-Bool≡ A (push (false , push a j) i) true k =
  hcomp (λ r
  → λ {(i = i0) → inrR (fst (snd a) true)
      ; (i = i1) → pushR (fst a true) (fst (snd a) true)
                          (snd (snd a) true) (j ∨ (k ∧ ~ r))
      ; (j = i0) → lUnit-filler (sym (pushR (fst a true) (fst (snd a) true)
                                 (snd (snd a) true))) r k i
      ; (j = i1) → inrR (fst (snd a) true)
      ; (k = i0) → pushR (fst a true) (fst (snd a) true) (snd (snd a) true) (~ i ∨ j)
      ; (k = i1) → compPath-filler refl
                     (sym (pushR (fst a true) (fst (snd a) true)
                            (snd (snd a) true))) (r ∧ ~ j) i})
        (pushR (fst a true) (fst (snd a) true)
               (snd (snd a) true) ((k ∨ j) ∨ ~ i))
ΠR-extend→Π-Bool≡ A (push (true , inl x) i) true = refl
ΠR-extend→Π-Bool≡ A (push (true , inr x) i) true j =
  lUnit (pushR (fst x) (fst (snd x) true) (snd (snd x))) j i
ΠR-extend→Π-Bool≡ A (push (true , push a j) i) true k =
  hcomp (λ r
  → λ {(i = i0) → inlR (fst a true)
      ; (i = i1) → pushR (fst a true) (fst (snd a) true)
                          (snd (snd a) true) (j ∧ (~ k ∨ r))
      ; (j = i0) → inlR (fst a true)
      ; (j = i1) → lUnit-filler (pushR (fst a true) (fst (snd a) true)
                                 (snd (snd a) true)) r k i
      ; (k = i0) → pushR (fst a true) (fst (snd a) true) (snd (snd a) true) (i ∧ j)
      ; (k = i1) → compPath-filler refl
                     (pushR (fst a true) (fst (snd a) true)
                       (snd (snd a) true)) (r ∧ j) i})
        (pushR (fst a true) (fst (snd a) true)
               (snd (snd a) true) (i ∧ (j ∧ ~ k)))


-- To show that ΠR-extend→Π-Bool is an equivalence, it is easier to show that
-- its composition with ΠBool→× (equivalence between Π over bool and products)
-- is an equivalence:
ΠR-extend→× : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
  → ΠJoinR₁.ΠR-extend (RP∞'∙ ℓ) (fst J) A
  → UnordJoinR-gen (fst J) (A true) × UnordJoinR-gen (fst J) (A false)
ΠR-extend→× J A t =
  ΠBool→× {A = λ x → UnordJoinR-gen (fst J) (A x)} (ΠR-extend→Π-Bool J A t)

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

    ×→ΠR-extend-push²-fill-btm : I → I → I → ΠJoinR₁.ΠR-extend (RP∞'∙ ℓ) J A
    ×→ΠR-extend-push²-fill-btm i j r =
      Square-filler {A = ΠJoinR₁.ΠR-extend (RP∞'∙ ℓ) J A}
          (push (true , inl (CasesBool true (a , b) (a' , b₁) , c₁ , d)))
          (push (false , inl (CasesBool true (a , b) (a' , b₁) , c , x)))
           i j r

    ×→ΠR-extend-push²-fill : I → I → I → ΠJoinR₁.ΠR-extend (RP∞'∙ ℓ) J A
    ×→ΠR-extend-push²-fill i j r =
      hfill (λ r
      → λ {(i = i0) → push (true , inl (CasesBool true (a , b) (a' , b₁) , c₁ , d)) (~ j)
          ; (i = i1) → push (false , push ((CasesBool true (a , b) (a' , b₁))
                           , (CasesBool true c c₁ , CasesBool true x d)) r) j
          ; (j = i0) → push (false , inl (CasesBool true (a , b) (a' , b₁) , c , x)) (~ i)
          ; (j = i1) → push (true , push ((CasesBool true (a , b) (a' , b₁))
                           , (CasesBool true c c₁) , CasesBool true x d) r) i})
        (inS (×→ΠR-extend-push²-fill-btm i j i1)) r

×→ΠR-extend : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
  → UnordJoinR-gen (fst J) (A true) × UnordJoinR-gen (fst J) (A false)
  → ΠJoinR₁.ΠR-extend (RP∞'∙ ℓ) (fst J) A
×→ΠR-extend J A (inlR x , inlR x₁) = inr (inl (CasesBool true x x₁))
×→ΠR-extend J A (inlR (x , b) , inrR x₁) = inl (true , ((_ , b) , x₁))
×→ΠR-extend J A (inlR (a , b) , pushR (a' , d) c x₁ i) =
  push (true , inl ((CasesBool true (a , b) (a' , d)) , c , x₁)) (~ i)
×→ΠR-extend J A (inrR x , inlR x₁) = inl (false , (x₁ , x))
×→ΠR-extend J A (inrR x , inrR x₁) = inr (inr (CasesBool true x x₁))
×→ΠR-extend J A (inrR x , pushR (a , b) c x₁ i) =
  push (false , (inr ((a , b) , ((CasesBool true x c) , x₁)))) i
×→ΠR-extend J A (pushR (a , b) c x i , inlR (a' , b')) =
  push (false , inl ((CasesBool true (a , b) (a' , b')) , (c , x))) (~ i)
×→ΠR-extend J A (pushR (a' , b) c x i , inrR x₁) =
  push (true , inr ((_ , b) , (CasesBool true c x₁ , x))) i
×→ΠR-extend J A (pushR (a , b) c x i , pushR (a' , b₁) c₁ d j) =
  ×→ΠR-extend-push²-fill (fst J) A a a' b b₁ c c₁ x d i j i1

-- proving that the maps cancel out is easy in one direction
×→ΠR-extend→× : ∀ {ℓ} {J : RP∞' ℓ} (A : Bool → fst J → Type ℓ)
  (m : UnordJoinR-gen (fst J) (A true) × UnordJoinR-gen (fst J) (A false))
  → ΠR-extend→× J A (×→ΠR-extend J A m) ≡ m
×→ΠR-extend→× A (inlR (a , b) , inlR (a' , d)) = refl
×→ΠR-extend→× A (inlR (a , snd₁) , inrR x₁) = refl
×→ΠR-extend→× A (inlR (a , b) , pushR (a' , d) e x₁ i) = refl
×→ΠR-extend→× A (inrR x , inlR (a , b)) = refl
×→ΠR-extend→× A (inrR x , inrR x₁) = refl
×→ΠR-extend→× A (inrR x , pushR (a' , b) c x₁ i) = refl
×→ΠR-extend→× A (pushR (a , b) b₁ x i , inlR (a' , b')) = refl
×→ΠR-extend→× A (pushR (a , b) b₁ x i , inrR x₁) = refl
×→ΠR-extend→× {ℓ = ℓ} {J = J} A (pushR (a , b) c x i , pushR (a' , b₁) c₁ d j) k =
   hcomp (λ r
    → λ {(k = i0) → ΠR-extend→× J A (P i j r)
        ; (k = i1) → (pushR (a , b) c x (i ∧ (~ j ∨ r)))
                      , pushR (a' , b₁) c₁ d (((~ i) ∨ r) ∧ j)
        ; (j = i0) → ΠR-extend→× J A (P i j r)
        ; (j = i1) → ΠR-extend→× J A (P i j r)
        ; (i = i0) → ΠR-extend→× J A (P i j r)
        ; (i = i1) → ΠR-extend→× J A (P i j r)})
        (hcomp (λ r
       → λ {(k = i0) →
         ΠR-extend→× J A
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
  P = ×→ΠR-extend-push²-fill (fst J) A a a' b b₁ c c₁ x d

-- ... the other direction is harder and requires a bunch of fillers

module ΠR-extend→×→ΠR-extend-fillers
  {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
  (f : (j : Bool) → Σ (fst J) (A j))
  (a : (j : Bool) (j₁ : fst J) → A j j₁)
  (b : (j : Bool) → a j (f j .fst) ≡ f j .snd) where
  private
    H = ΠJoinR₁.ΠR-extend (RP∞'∙ ℓ) (fst J) A

    ×→ΠR-extend-push²-fill-btm-path =
      ×→ΠR-extend-push²-fill-btm
        (fst J) A (fst (f true)) (fst (f false)) (snd (f true)) (snd (f false))
        (a true) (a false) (b true) (b false)

    ×→ΠR-extend-push²-fill-path =
      ×→ΠR-extend-push²-fill (fst J) A
        (fst (f true)) (fst (f false)) (snd (f true)) (snd (f false))
        (a true) (a false) (b true) (b false)

  true-fill :  I → I → I → H
  true-fill i j k =
    hfill (λ r
    → λ {(i = i0) → push (true , (inl (CasesBoolη f j , a false , b false))) r
        ; (i = i1) → push (true , (inr (f true , CasesBoolη a j , b true))) r
        ; (j = i0) → ×→ΠR-extend-push²-fill-path (i ∧ r) (i ∨ ~ r) i1
                   ; (j = i1) → push (true , (push (f , (a , b)) i)) r})
          (inS (inl (true , f true , a false))) k

  false-fill : I → I → I → H
  false-fill i j k =
    hfill (λ r
    → λ {(i = i0) → push (false , inl (CasesBoolη f j , a true , b true)) r
        ; (i = i1) → push (false , (inr (f false , CasesBoolη a j , b false))) r
        ; (j = i0) → ×→ΠR-extend-push²-fill-path (i ∨ ~ r) (i ∧ r) i1
        ; (j = i1) → push (false , (push (f , (a , b)) i)) r})
          (inS (inl (false , f false , a true))) k

  true-fill≡false-fill :
    Path (Square {A = H} _ _ _ _)
         (λ i j → true-fill i j i1) (λ i j → false-fill i j i1)
  true-fill≡false-fill  k i j =
    hcomp (λ r →
    λ {(i = i0) → push (true , inl (CasesBoolη f j , a false , b false)) (r ∨ k)
     ; (i = i1) → push (true , inr (f true , CasesBoolη a j , b true)) (r ∨ k)
     ; (j = i0) → ×→ΠR-extend-push²-fill-path (i ∧ (r ∨ k)) (i ∨ ~ (r ∨ k)) i1
     ; (j = i1) → push (true , push (f , a , b) i) (r ∨ k)
     ; (k = i0) → true-fill i j r
     ; (k = i1) → false-fill i j i1})
      (hcomp (λ r →
     λ {(i = i0) → push (true , inl (CasesBoolη f j , a false , b false)) k
      ; (i = i1) → push (true , push (CasesBoolη f j , CasesBoolη a j , CasesBoolη-coh b j) r) k
      ; (j = i0) → ×→ΠR-extend-push²-fill-path (i ∧ k) (i ∨ ~ k) r
      ; (j = i1) → push (true , push (f , a , b) (r ∧ i)) k
      ; (k = i0) → inl (true , f true , a false)
      ; (k = i1) → cube₃ r j i})
       (hcomp (λ r →
     λ {(i = i0) → push (true , inl (CasesBoolη f j , a false , b false)) (k ∨ ~ r)
      ; (i = i1) → push (true , inl ((CasesBoolη f j) , ((a false) , (b false)))) (k ∨ ~ r)
      ; (j = i0) → ×→ΠR-extend-push²-fill-btm-path (i ∧ k) (i ∨ ~ k) r
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
       → λ {(i = i0) → ×→ΠR-extend-push²-fill-btm-path j j r
           ; (i = i1) → inr (push (f , (a , CasesBool true (b true) (b false))) (~ r ∧ ~ j))
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
        ; (j = i0) → ×→ΠR-extend-push²-fill-btm-path k k (i ∧ r)
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
       λ {(i = i0) → ×→ΠR-extend-push²-fill-path (j ∨ (~ k ∧ r)) (j ∧ (k ∨ ~ r)) r
        ; (i = i1) → push (false , push (f , a , b) (r ∧ j)) (k ∨ ~ r)
        ; (j = i0) → push (false , inl ((CasesBoolη f i)
                                      , ((a true) , (b true)))) (k ∨ ~ r)
        ; (j = i1) → push (false , push ((CasesBoolη f i)
                                        , (CasesBoolη a i
                                         , CasesBoolη-coh b i)) r) (k ∨ ~ r)
        ; (r = i0) → cube₁ i j i1
        ; (r = i1) → false-fill j i k})
       (hcomp (λ k →
       λ {(i = i0) → ×→ΠR-extend-push²-fill-path (j ∨ r) (j ∧ (~ r)) (r ∧ k)
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
        λ {(i = i0) → ×→ΠR-extend-push²-fill-btm-path (j ∨ r) (j ∧ (~ r)) k
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
         ; (r = i1) → push (false , (inl (CasesBoolη f i , a true , b true))) (~ k)})
          (inr (push (CasesBoolη f i , a
                    , CasesBool true (b true) (b false)) (i ∧ (~ j ∧ ~ r))))))

ΠR-extend→×→ΠR-extend : ∀ {ℓ} {J : RP∞' ℓ} (A : Bool → fst J → Type ℓ) (m : _)
  → ×→ΠR-extend J A (ΠR-extend→× J A m) ≡ m
ΠR-extend→×→ΠR-extend {J = J} A (inl (false , m)) = refl
ΠR-extend→×→ΠR-extend {J = J} A (inl (true , m)) = refl
ΠR-extend→×→ΠR-extend A (inr (inl x)) j = inr (inl (CasesBoolη x j))
ΠR-extend→×→ΠR-extend {J = J} A (inr (inr x)) j =
  inr (inr (CasesBoolη {A = λ i → (j : fst J) → A i j} x j ))
ΠR-extend→×→ΠR-extend {J = J} A (inr (push (f , a , b) i)) j =
  ΠR-extend→×→ΠR-extend-fillers.true-fill J A f a b i j i1
ΠR-extend→×→ΠR-extend A (push (false , inl (f , q , t)) i) j =
  push (false , inl (CasesBoolη f j , q , t)) i
ΠR-extend→×→ΠR-extend A (push (true , inl (f , q , t)) i) j =
  push (true , inl (CasesBoolη f j , q , t)) i
ΠR-extend→×→ΠR-extend A (push (false , inr (f , q , t)) i) j =
  push (false , inr (f , CasesBoolη q j , t)) i
ΠR-extend→×→ΠR-extend A (push (true , inr (f , q , t)) i) j =
  push (true , inr (f , CasesBoolη q j , t)) i
ΠR-extend→×→ΠR-extend {J = J} A (push (false , push (f , q , t) i₂) i) j =
  hcomp (λ r →
  λ {(i = i0) → inl (false , f false , q true)
   ; (i = i1) → ΠR-extend→×→ΠR-extend-fillers.true-fill≡false-fill
                  J A f q t (~ r) i₂ j
   ; (j = i0) → ×→ΠR-extend-push²-fill (fst J) A (fst (f true)) (fst (f false))
                          (snd (f true)) (snd (f false))
                          (q true) (q false)
                          (t true) (t false)
                          ((~ i) ∨ i₂) (i ∧ i₂) i1
   ; (j = i1) → push (false , push (f , q , t) i₂) i
   ; (i₂ = i0) → push (false , inl (CasesBoolη f j , q true , t true)) i
   ; (i₂ = i1) → push (false , inr (f false , CasesBoolη q j , t false)) i})
     (hcomp (λ r →
   λ {(i = i0) → inl (false , f false , q true)
    ; (i = i1) → ΠR-extend→×→ΠR-extend-fillers.false-fill J A f q t i₂ j r
    ; (j = i0) → ×→ΠR-extend-push²-fill (fst J) A (fst (f true)) (fst (f false))
                           (snd (f true)) (snd (f false))
                           (q true) (q false)
                           (t true) (t false)
                           ((~ i) ∨ (i₂ ∨ ~ r)) (i ∧ (i₂ ∧ r)) i1
    ; (j = i1) → push (false , push (f , q , t) i₂) (r ∧ i)
    ; (i₂ = i0) → push (false , (inl (CasesBoolη f j , (q true , t true)))) (i ∧ r)
    ; (i₂ = i1) → push (false , inr (f false , CasesBoolη q j , t false)) (i ∧ r)})
    (inl (false , f false , q true)))
ΠR-extend→×→ΠR-extend {J = J} A (push (true , push (f , q , t) i₂) i) j =
  hcomp (λ r →
  λ {(i = i0) → inl (true , f true , q false)
   ; (i = i1) → ΠR-extend→×→ΠR-extend-fillers.true-fill J A f q t i₂ j r
   ; (j = i0) → ×→ΠR-extend-push²-fill (fst J) A (fst (f true)) (fst (f false))
                          (snd (f true)) (snd (f false))
                          (q true) (q false)
                          (t true) (t false)
                          (i ∧ (i₂ ∧ r)) ((~ i) ∨ (i₂ ∨ ~ r)) i1
   ; (j = i1) → push (true , push (f , q , t) i₂) (r ∧ i)
   ; (i₂ = i0) → push (true , inl (CasesBoolη f j , q false , t false)) (i ∧ r)
   ; (i₂ = i1) → push (true , inr (f true , CasesBoolη q j , t true)) (i ∧ r)})
    (inl (true , f true , q false))

-- so, finally, ΠR-extend→× is an equivalence
ΠR-extend→×Iso : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
  → Iso (ΠJoinR₁.ΠR-extend (RP∞'∙ ℓ) (fst J) A)
         (UnordJoinR-gen (fst J) (A true) × UnordJoinR-gen (fst J) (A false))
Iso.fun (ΠR-extend→×Iso J A) = ΠR-extend→× J A
Iso.inv (ΠR-extend→×Iso J A) = ×→ΠR-extend J A
Iso.rightInv (ΠR-extend→×Iso J A) = ×→ΠR-extend→× {J = J} A
Iso.leftInv (ΠR-extend→×Iso J A) = ΠR-extend→×→ΠR-extend {J = J} A

-- this gives, via the following lemmas, that our original map
-- ΠR-extend→Π is an equivalence
module _ {ℓ : Level} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
  where
  module ΠR-extend→Π-equiv-base-lemmas where
    p : ΠR-extend→Π-Bool J A ≡ ΠJoinR₁.ΠR-extend→Π (RP∞'∙ ℓ) (fst J) A
    p = funExt λ x → funExt (ΠR-extend→Π-Bool≡ {J = J} A x)

    alt : (ΠJoinR₁.ΠR-extend (RP∞'∙ ℓ) (fst J) A) ≃ ((x : Bool) → UnordJoinR-gen (fst J) (A x))
    alt = isoToEquiv (compIso (ΠR-extend→×Iso J A) (invIso ΠBool×Iso))

    altid : fst alt ≡ ΠR-extend→Π-Bool J A
    altid = funExt λ x → funExt (CasesBool true refl refl)

    isEq : isEquiv (ΠR-extend→Π-Bool J A)
    isEq = subst isEquiv altid (snd alt)

  open ΠR-extend→Π-equiv-base-lemmas
  ΠR-extend→Π-equiv-base : isEquiv (ΠJoinR₁.ΠR-extend→Π (RP∞'∙ ℓ) (fst J) A)
  ΠR-extend→Π-equiv-base = transport (λ i → isEquiv (p i)) isEq

ΠR-extend→Π-equiv : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
  → isEquiv (ΠJoinR₁.ΠR-extend→Π I (fst J) A)
ΠR-extend→Π-equiv {ℓ = ℓ} =
  RP∞'pt→Prop (λ _ → isPropΠ2 λ _ _ → isPropIsEquiv _) ΠR-extend→Π-equiv-base

ΠR-extend≃ΠUnordJoinR : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
  → ΠJoinR₁.ΠR-extend I (fst J) A ≃ UnordΠ I λ i → UnordJoinR J (A i)
fst (ΠR-extend≃ΠUnordJoinR I J A) = ΠJoinR₁.ΠR-extend→Π I (fst J) A
snd (ΠR-extend≃ΠUnordJoinR I J A) = ΠR-extend→Π-equiv I J A
