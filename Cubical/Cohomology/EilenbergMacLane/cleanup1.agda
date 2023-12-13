{-# OPTIONS --safe --lossy-unification #-}

{-
This file contains
1. The Thom isomorphism (various related forms of it)
2. The Gysin sequence
-}
open import Cubical.Cohomology.EilenbergMacLane.Base
open import Cubical.Cohomology.EilenbergMacLane.Groups.Sn
open import Cubical.Cohomology.EilenbergMacLane.CupProduct

open import Cubical.Homotopy.EilenbergMacLane.CupProduct
open import Cubical.Homotopy.EilenbergMacLane.CupProductTensor
  renaming (_⌣ₖ_ to _⌣ₖ⊗_ ; ⌣ₖ-0ₖ to ⌣ₖ-0ₖ⊗ ; 0ₖ-⌣ₖ to 0ₖ-⌣ₖ⊗)
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.EilenbergMacLane.GradedCommTensor
  hiding (⌣ₖ-comm)
open import Cubical.Homotopy.EilenbergMacLane.GroupStructure
open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Group.Base

open import Cubical.Functions.Morphism
open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.Isomorphism

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout
open import Cubical.HITs.EilenbergMacLane1.Base
open import Cubical.HITs.Susp
open import Cubical.HITs.S1

open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order hiding (eq)
open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_≤_ ; Bool*)

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing

open import Cubical.HITs.RPn
open import Cubical.Homotopy.EilenbergMacLane.Order2

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.HLevels
open import Cubical.Foundations.Function
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Empty as ⊥
open import Cubical.HITs.SmashProduct

open import Cubical.Foundations.Univalence


module Cubical.Cohomology.EilenbergMacLane.cleanup1 where
open import Cubical.HITs.Join
open import Cubical.Functions.FunExtEquiv

joinR-gen : ∀ {ℓ ℓ'} (I : Type ℓ) (A : I → Type ℓ') → Type _
joinR-gen I A = PushoutR (Σ I A) ((i : I) → A i)  λ x f → f (fst x) ≡ snd x

joinR : ∀ {ℓ} (I : RP∞) (A : fst I → Type ℓ) → Type _
joinR I A = PushoutR (Σ (fst I) A) ((i : fst I) → A i)  λ x f → f (fst x) ≡ snd x

joinRD : ∀ {ℓ} (I J : RP∞) (A : fst I → fst J → Type ℓ) → Type _
joinRD I J A = joinR I λ i → joinR J (A i)

module ΠJoinR-gen {ℓ} (I : RP∞' ℓ) (J : Type) (A : fst I → J → Type ℓ)
       (AB : Type ℓ) (AB→J : (i : fst I) → AB → J)
       (AB→A : (i : fst I) (a : AB) → A i (AB→J i a))
       where
  fat : Type ℓ
  fat = Σ[ a ∈ AB ]
           Σ[ g ∈ ((i : fst I) (j : J) → A i j) ]
             ((i : fst I) → g i (AB→J i a) ≡ AB→A i a)
  ΠR-base : Type ℓ
  ΠR-base = Pushout {A = fat} {B = AB} {C = ((i : fst I) (j : J) → A i j)}
                       fst (fst ∘ snd)

  left-push : Type _
  left-push = Σ[ i ∈ fst I ] (Σ[ j ∈ J ] (A i j)) × ((j : J) → A (RP∞'-fields.notRP∞' I i) j)

  left-push↑ₗ : fst I → Type _
  left-push↑ₗ i = Σ[ f ∈ AB ]
    Σ[ g ∈ ((j : J) → A (RP∞'-fields.notRP∞' I i) j) ] g (AB→J (RP∞'-fields.notRP∞' I i) f) ≡ AB→A (RP∞'-fields.notRP∞' I i) f

  left-push↑ᵣ : fst I → Type _
  left-push↑ᵣ i = Σ[ f ∈ (Σ[ j ∈ J ] A i j) ]
      Σ[ g ∈ ((i : fst I) (j : J) → A i j) ] g i (fst f) ≡ snd f

  fat→ₗ : (i : fst I) → fat → left-push↑ₗ i
  fat→ₗ  i (f , g , r) = (f , (g (RP∞'-fields.notRP∞' I i)) , (r (RP∞'-fields.notRP∞' I i)))

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
    → (Σ[ j ∈ J ] (A i j)) × ((j : J) → A (RP∞'-fields.notRP∞' I i) j)
  PushTop→left-push' i (inl (f , g , p)) = AB→Σ i f , g
  PushTop→left-push' i (inr (f , g , p)) = f , (g (RP∞'-fields.notRP∞' I i))
  PushTop→left-push' i (push (f , g , p) k) = (AB→Σ i f) , g (RP∞'-fields.notRP∞' I i)

  PushTop→left-push : PushTop → left-push
  PushTop→left-push (i , x) = (i , PushTop→left-push' i x)

  PushTop→ΠR-base : PushTop → ΠR-base
  PushTop→ΠR-base (i , inl (f , g , p)) = inl f
  PushTop→ΠR-base (i , inr (f , g , p)) = inr g
  PushTop→ΠR-base (i , push (f , g , p)  i₁) = push (f , g , p) i₁

  ΠR-extend : Type _
  ΠR-extend = Pushout PushTop→left-push PushTop→ΠR-base


module ΠJoinR₁ {ℓ : Level} (I : RP∞' ℓ) (J : Type) (A : fst I → J → Type ℓ) where
  open ΠJoinR-gen I J A
    ((i : fst I) → Σ J (A i)) (λ i f → f i .fst) (λ i f → f i .snd)
    public
  open RP∞'-fields I

  ΠR-extend→Πₗ : left-push → ((i : fst I) → joinR-gen J (A i))
  ΠR-extend→Πₗ (i , p , r) = elimRP∞' i (inlR p) (inrR r)

  ΠR-base→ : ΠR-base → ((i : fst I) → joinR-gen J (A i))
  ΠR-base→ (inl x) i = inlR (x i)
  ΠR-base→ (inr x) i = inrR λ j → x i j
  ΠR-base→ (push a i') i = pushR (fst a i) (fst (snd a) i) (snd (snd a) i) i'

  pre-eqvl-diag : (i' : fst I) (p : Pushout (fat→ₗ i') (fat→ᵣ i'))
    → ΠR-extend→Πₗ (PushTop→left-push (i' , p)) i'
     ≡ ΠR-base→ (PushTop→ΠR-base (i' , p)) i'
  pre-eqvl-diag i' (inl (f , f2 , p)) =
    elimRP∞'β {B = λ i → joinR-gen J (A i)} i' (inlR (f i' .fst , f i' .snd)) (inrR f2) .fst
  pre-eqvl-diag i' (inr (f , f2 , p)) =
    elimRP∞'β {B = λ i → joinR-gen J (A i)} i' (inlR f) (inrR (f2 (notRP∞' i'))) .fst ∙ pushR f (f2 i') p 
  pre-eqvl-diag i' (push (f , f2 , p) i) j =
    compPath-filler (elimRP∞'β {B = λ i → joinR-gen J (A i)} i' (inlR (f i')) (inrR (f2 (notRP∞' i'))) .fst)
                    (pushR (f i') (f2 i') (p i')) i j

  pre-eqvl-not : (i' : fst I) (p : Pushout (fat→ₗ i') (fat→ᵣ i'))
    → ΠR-extend→Πₗ (PushTop→left-push (i' , p)) (notRP∞' i') ≡
      ΠR-base→ (PushTop→ΠR-base (i' , p)) (notRP∞' i')
  pre-eqvl-not i' (inl (f , f2 , p)) =
      elimRP∞'β {B = λ i → joinR-gen J (A i)} i' (inlR (f i')) (inrR f2) .snd
    ∙ sym (pushR (f (notRP∞' i')) f2 p)
  pre-eqvl-not i' (inr (f , f2 , p)) =
    elimRP∞'β {B = λ i → joinR-gen J (A i)} i' (inlR f) (inrR (f2 (notRP∞' i'))) .snd
  pre-eqvl-not i' (push (f , f2 , p) i) j =
      compPath-filler
        (elimRP∞'β {B = λ i → joinR-gen J (A i)} i' (inlR (f i')) (inrR (f2 (notRP∞' i'))) .snd)
        (sym (pushR (f (notRP∞' i')) (f2 (notRP∞' i')) (p (notRP∞' i')))) (~ i) j


  eqvl : (a : PushTop) (i : fst I)
    → ΠR-extend→Πₗ (PushTop→left-push a) i
     ≡ ΠR-base→ (PushTop→ΠR-base a) i
  eqvl (i' , p) =
    elimRP∞' i' (pre-eqvl-diag i' p)
                 (pre-eqvl-not i' p)

  ΠR-extend→Π : ΠR-extend → ((i : fst I) → joinR-gen J (A i))
  ΠR-extend→Π (inl t) = ΠR-extend→Πₗ t
  ΠR-extend→Π (inr x) = ΠR-base→ x
  ΠR-extend→Π (push a i) i' = eqvl a i' i

  dable : Type _
  dable = Pushout {A = fst I × ΠR-extend} {B = Σ[ i ∈ fst I ] joinR-gen J (A i)} {C = ΠR-extend}
                  (λ a → fst a , ΠR-extend→Π (snd a) (fst a))
                  snd
                  

  private
    inl123 : (a : _) → dable
    inl123 = inl
  module _ (ise : isEquiv ΠR-extend→Π) where
    
    updater→ : dable → (joinR-gen (fst I) (λ i → joinR-gen J (A i)))
    updater→ (inl x) = inlR x
    updater→ (inr x) = inrR (ΠR-extend→Π x)
    updater→ (push a i) = pushR (fst a , ΠR-extend→Π (snd a) (fst a)) (ΠR-extend→Π (snd a)) refl i

    updater← : joinR-gen (fst I) (λ i → joinR-gen J (A i)) → dable
    updater← (inlR x) = inl x
    updater← (inrR x) = inr (invEq (_ , ise) x)
    updater← (pushR a b x i) =
      (cong inl123 (ΣPathP (refl , sym x ∙ sym (funExt⁻ (secEq (_ , ise) b) (fst a))))
              ∙ push ((fst a) , invEq (_ , ise) b)) i

ΠR-extend→Π-alt : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → (fst J) → Type ℓ)
  → ΠJoinR₁.ΠR-extend (RP∞'∙ ℓ) (fst J) A
  → ((i : Bool) → joinR-gen (fst J) (A i))
ΠR-extend→Π-alt J A (inl (false , f , p)) false = inlR f
ΠR-extend→Π-alt J A (inl (false , f , p)) true = inrR p
ΠR-extend→Π-alt J A (inl (true , f , p)) false = inrR p
ΠR-extend→Π-alt J A (inl (true , f , p)) true = inlR f
ΠR-extend→Π-alt J A (inr (inl x)) a = inlR (x a)
ΠR-extend→Π-alt J A (inr (inr x)) b = inrR (x b)
ΠR-extend→Π-alt J A (inr (push a i)) c =
  pushR (fst a c) (fst (snd a) c) (snd (snd a) c) i
ΠR-extend→Π-alt J A (push (false , inl x) i) false = inlR (fst x false)
ΠR-extend→Π-alt J A (push (false , inr x) i) false =
  pushR (fst x) (fst (snd x) false) (snd (snd x)) i
ΠR-extend→Π-alt J A (push (false , push (f , p , q) i₁) i) false =
  pushR (f false) (p false) (q false) (i ∧ i₁)
ΠR-extend→Π-alt J A (push (false , inl x) i) true =
  pushR (fst x true) (fst (snd x)) (snd (snd x)) (~ i)
ΠR-extend→Π-alt J A (push (false , inr x) i) true = inrR (fst (snd x) true)
ΠR-extend→Π-alt J A (push (false , push (f , p , q) i₁) i) true =
  pushR (f true) (p true) (q true) (~ i ∨ i₁)
ΠR-extend→Π-alt J A (push (true , inl x) i) false =
  pushR (fst x false) (fst (snd x)) (snd (snd x)) (~ i)
ΠR-extend→Π-alt J A (push (true , inr x) i) false = inrR (fst (snd x) false)
ΠR-extend→Π-alt J A (push (true , push (f , p , q) i₁) i) false =
  pushR (f false) (p false) (q false) (~ i ∨ i₁)
ΠR-extend→Π-alt J A (push (true , inl x) i) true = inlR (fst x true)
ΠR-extend→Π-alt J A (push (true , inr x) i) true = pushR (fst x) (fst (snd x) true) (snd (snd x)) i
ΠR-extend→Π-alt J A (push (true , push (f , p , q) i₁) i) true = pushR (f true) (p true) (q true) (i ∧ i₁)

ΠR-extend→Π-alt≡ : ∀ {ℓ} {J : RP∞' ℓ} (A : Bool → fst J → Type ℓ)
  → (x : _) (z : _) → ΠR-extend→Π-alt J A x z ≡ ΠJoinR₁.ΠR-extend→Π (RP∞'∙ ℓ) (fst J) A x z
ΠR-extend→Π-alt≡ A (inl (false , y)) false = refl
ΠR-extend→Π-alt≡ A (inl (false , y)) true = refl
ΠR-extend→Π-alt≡ A (inl (true , y)) false = refl
ΠR-extend→Π-alt≡ A (inl (true , y)) true = refl
ΠR-extend→Π-alt≡ A (inr (inl x)) z = refl
ΠR-extend→Π-alt≡ A (inr (inr x)) z = refl
ΠR-extend→Π-alt≡ A (inr (push a i)) false = refl
ΠR-extend→Π-alt≡ A (inr (push a i)) true = refl
ΠR-extend→Π-alt≡ A (push (false , inl x) i) false = refl
ΠR-extend→Π-alt≡ A (push (false , inr x) i) false j = lUnit (pushR (fst x) (fst (snd x) false) (snd (snd x))) j i
ΠR-extend→Π-alt≡ A (push (false , push a i₁) i) false k =
  hcomp (λ r → λ {(i = i0) → inlR (fst a false)
                 ; (i = i1) → pushR (fst a false) (fst (snd a) false) (snd (snd a) false) (i₁ ∧ (~ k ∨ r))
                 ; (i₁ = i0) → inlR (fst a false)
                 ; (i₁ = i1) → lUnit-filler (pushR (fst a false) (fst (snd a) false) (snd (snd a) false)) r k i
                 ; (k = i0) → pushR (fst a false) (fst (snd a) false) (snd (snd a) false) (i ∧ i₁)
                 ; (k = i1) → compPath-filler refl (pushR (fst a false) (fst (snd a) false) (snd (snd a) false)) (r ∧ i₁) i})
        (pushR (fst a false) (fst (snd a) false) (snd (snd a) false) (i ∧ (i₁ ∧ ~ k)))
ΠR-extend→Π-alt≡ A (push (true , inl x) i) false j = lUnit (sym (pushR (fst x false) (fst (snd x)) (snd (snd x)))) j i
ΠR-extend→Π-alt≡ A (push (true , inr x) i) false = refl
ΠR-extend→Π-alt≡ A (push (true , push a i₁) i) false k =
  hcomp (λ r → λ {(i = i0) → inrR (fst (snd a) false)
                 ; (i = i1) → pushR (fst a false) (fst (snd a) false) (snd (snd a) false) (i₁ ∨ (k ∧ ~ r))
                 ; (i₁ = i0) → lUnit-filler (sym (pushR (fst a false) (fst (snd a) false) (snd (snd a) false))) r k i
                 ; (i₁ = i1) → inrR (fst (snd a) false)
                 ; (k = i0) → pushR (fst a false) (fst (snd a) false) (snd (snd a) false) (~ i ∨ i₁)
                 ; (k = i1) → compPath-filler refl
                                (sym (pushR (fst a false) (fst (snd a) false) (snd (snd a) false))) (r ∧ ~ i₁) i})
          (pushR (fst a false) (fst (snd a) false) (snd (snd a) false) ((k ∨ i₁) ∨ ~ i))
ΠR-extend→Π-alt≡ A (push (false , inl x) i) true j = lUnit (sym (pushR (fst x true) (fst (snd x)) (snd (snd x)))) j i
ΠR-extend→Π-alt≡ A (push (false , inr x) i) true = refl
ΠR-extend→Π-alt≡ A (push (false , push a i₁) i) true k =
  hcomp (λ r → λ {(i = i0) → inrR (fst (snd a) true)
                 ; (i = i1) → pushR (fst a true) (fst (snd a) true) (snd (snd a) true) (i₁ ∨ (k ∧ ~ r))
                 ; (i₁ = i0) → lUnit-filler (sym (pushR (fst a true) (fst (snd a) true) (snd (snd a) true))) r k i
                 ; (i₁ = i1) → inrR (fst (snd a) true)
                 ; (k = i0) → pushR (fst a true) (fst (snd a) true) (snd (snd a) true) (~ i ∨ i₁)
                 ; (k = i1) → compPath-filler refl
                                (sym (pushR (fst a true) (fst (snd a) true) (snd (snd a) true))) (r ∧ ~ i₁) i})
          (pushR (fst a true) (fst (snd a) true) (snd (snd a) true) ((k ∨ i₁) ∨ ~ i))
ΠR-extend→Π-alt≡ A (push (true , inl x) i) true = refl
ΠR-extend→Π-alt≡ A (push (true , inr x) i) true j = lUnit (pushR (fst x) (fst (snd x) true) (snd (snd x))) j i
ΠR-extend→Π-alt≡ A (push (true , push a i₁) i) true k =
  hcomp (λ r → λ {(i = i0) → inlR (fst a true)
                 ; (i = i1) → pushR (fst a true) (fst (snd a) true) (snd (snd a) true) (i₁ ∧ (~ k ∨ r))
                 ; (i₁ = i0) → inlR (fst a true)
                 ; (i₁ = i1) → lUnit-filler (pushR (fst a true) (fst (snd a) true) (snd (snd a) true)) r k i
                 ; (k = i0) → pushR (fst a true) (fst (snd a) true) (snd (snd a) true) (i ∧ i₁)
                 ; (k = i1) → compPath-filler refl (pushR (fst a true) (fst (snd a) true) (snd (snd a) true)) (r ∧ i₁) i})
        (pushR (fst a true) (fst (snd a) true) (snd (snd a) true) (i ∧ (i₁ ∧ ~ k)))


ΠR-extend→× : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
  → ΠJoinR₁.ΠR-extend (RP∞'∙ ℓ) (fst J) A
  → joinR-gen (fst J) (A true) × joinR-gen (fst J) (A false)
ΠR-extend→× J A t = ΠBool→× {A = λ x → joinR-gen (fst J) (A x)} (ΠR-extend→Π-alt J A t)

ΠR-extend→×-old : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
  → ΠJoinR₁.ΠR-extend (RP∞'∙ ℓ) (fst J) A
  → joinR-gen (fst J) (A true) × joinR-gen (fst J) (A false)
ΠR-extend→×-old {ℓ = ℓ} J A t =
  ΠBool→× {A = λ x → joinR-gen (fst J) (A x)}
    (ΠJoinR₁.ΠR-extend→Π (RP∞'∙ ℓ) (fst J) A t)

Square-filler : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : z ≡ y)
  → I → I → I → A
Square-filler {y = y} p q i j k =
  hfill (λ k → λ {(i = i0) → p (~ j ∨ ~ k)
                 ; (i = i1) → q (j ∨ ~ k)
                 ; (j = i0) → q (~ k ∨ ~ i)
                 ; (j = i1) → p (i ∨ ~ k)})
         (inS y)
         k

private
  module _ {ℓ : Level} (J : Type) (A : Bool → J → Type ℓ) where

    fill₂-b : (a a' : J) (b : A true a) (b₁ : A false a')
            (c : (i₂ : J) → A true i₂)
            (c₁ : (i₂ : J) → A false i₂)
            (x : c a ≡ b)
            (d : c₁ a' ≡ b₁)
          → I → I → I → ΠJoinR₁.ΠR-extend (RP∞'∙ ℓ) J A
    fill₂-b a a' b b₁ c c₁ x d i i₁ r = Square-filler {A = ΠJoinR₁.ΠR-extend (RP∞'∙ ℓ) J A}
          (push (true , inl (CasesBool true (a , b) (a' , b₁) , c₁ , d)))
          (push (false , inl (CasesBool true (a , b) (a' , b₁) , c , x)))
           i i₁ r

    fill₂ : (a a' : J) (b : A true a) (b₁ : A false a')
            (c : (i₂ : J) → A true i₂)
            (c₁ : (i₂ : J) → A false i₂)
            (x : c a ≡ b)
            (d : c₁ a' ≡ b₁)
          → I → I → I → ΠJoinR₁.ΠR-extend (RP∞'∙ ℓ) J A
    fill₂ a a' b b₁ c c₁ x d i i₁ r =
      hfill (λ r → λ {(i = i0) → push (true , inl (CasesBool true (a , b) (a' , b₁) , c₁ , d)) (~ i₁)
                 ; (i = i1) → push (false , push ((CasesBool true (a , b) (a' , b₁)) , (CasesBool true c c₁ , CasesBool true x d)) r) i₁
                 ; (i₁ = i0) → push (false , inl (CasesBool true (a , b) (a' , b₁) , c , x)) (~ i)
                 ; (i₁ = i1) → push (true , push ((CasesBool true (a , b) (a' , b₁)) , ((CasesBool true c c₁) , CasesBool true x d)) r) i})
        (inS (Square-filler {A = ΠJoinR₁.ΠR-extend (RP∞'∙ ℓ) J A}
          (push (true , inl (CasesBool true (a , b) (a' , b₁) , c₁ , d)))
          (push (false , inl (CasesBool true (a , b) (a' , b₁) , c , x)))
           i i₁ i1)) r

×→ΠR-extend : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
  → joinR-gen (fst J) (A true) × joinR-gen (fst J) (A false)
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
×→ΠR-extend J A (pushR (a , b) c x i , pushR (a' , b₁) c₁ d i₁) =
  fill₂ (fst J) A a a' b b₁ c c₁ x d i i₁ i1

×→ΠR-extend' : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
  → ((x : Bool) → joinR-gen (fst J) (A x))
  → ΠJoinR₁.ΠR-extend (RP∞'∙ ℓ) (fst J) A
×→ΠR-extend' J A = ×→ΠR-extend J A ∘ Iso.fun ΠBool×Iso

private
  module _ {ℓ : Level} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ) where
    fill-fill : (a a' : fst J) (b : A true a) (b₁ : A false a')
            (c : (i₂ : fst J) → A true i₂)
            (c₁ : (i₂ : fst J) → A false i₂)
            (x : c a ≡ b)
            (d : c₁ a' ≡ b₁)
          → I → I → I → joinR-gen (fst J) (A true) × joinR-gen (fst J) (A false)
    fill-fill a a' b b₁ c c₁ x d i i₁ k =
      hcomp (λ r → λ {(k = i0) → ΠR-extend→× J A (fill₂ (fst J) A a a' b b₁ c c₁ x d i i₁ r)
                 ; (k = i1) → (pushR (a , b) c x (i ∧ (~ i₁ ∨ r)))
                               , pushR (a' , b₁) c₁ d (((~ i) ∨ r) ∧ i₁)
                 ; (i₁ = i0) → ΠR-extend→× J A (fill₂ (fst J) A a a' b b₁ c c₁ x d i i₁ r)
                 ; (i₁ = i1) → ΠR-extend→× J A (fill₂ (fst J) A a a' b b₁ c c₁ x d i i₁ r)
                 ; (i = i0) → ΠR-extend→× J A (fill₂ (fst J) A a a' b b₁ c c₁ x d i i₁ r)
                 ; (i = i1) → ΠR-extend→× J A (fill₂ (fst J) A a a' b b₁ c c₁ x d i i₁ r)})
                 (hcomp (λ r
                → λ {(k = i0) → ΠR-extend→× J A (Square-filler {A = ΠJoinR₁.ΠR-extend (RP∞'∙ ℓ) (fst J) A}
                                   (push (true , inl ((CasesBool true (a , b) (a' , b₁)) , (c₁ , d))))
                                   (push (false , inl ((CasesBool true (a , b) (a' , b₁)) , (c , x))))
                                    i i₁ r)
                 ; (k = i1) → pushR (a , b) c x (i ∧ ~ i₁ ∧ r) , pushR (a' , b₁) c₁ d (~ i ∧ i₁ ∧ r)
                 ; (i₁ = i0) → pushR (a , b) c x (r ∧ i) , inlR (a' , b₁)
                 ; (i₁ = i1) → inlR (a , b) , pushR (a' , b₁) c₁ d (~ i ∧ r)
                 ; (i = i0) → inlR (a , b) , pushR (a' , b₁) c₁ d (i₁ ∧ r)
                 ; (i = i1) → pushR (a , b) c x (~ i₁ ∧ r) , inlR (a' , b₁) })
                 ((inlR (a , b) , inlR (a' , b₁))))

×→ΠR-extend→× : ∀ {ℓ} {J : RP∞' ℓ} (A : Bool → fst J → Type ℓ)
  (m : joinR-gen (fst J) (A true) × joinR-gen (fst J) (A false))
  → ΠR-extend→× J A (×→ΠR-extend J A m) ≡ m
×→ΠR-extend→× A (inlR (a , b) , inlR (a' , d)) = refl
×→ΠR-extend→× A (inlR (a , snd₁) , inrR x₁) = refl
×→ΠR-extend→× A (inlR (a , b) , pushR (a' , d) e x₁ i) = refl
×→ΠR-extend→× A (inrR x , inlR (a , b)) = refl
×→ΠR-extend→× A (inrR x , inrR x₁) = refl
×→ΠR-extend→× A (inrR x , pushR (a' , b) c x₁ i) = refl
×→ΠR-extend→× A (pushR (a , b) b₁ x i , inlR (a' , b')) = refl
×→ΠR-extend→× A (pushR (a , b) b₁ x i , inrR x₁) = refl
×→ΠR-extend→× {J = J} A (pushR (a , b) b₁ x i , pushR (a' , b') c x₁ i₁) k =
  fill-fill J A a a' b b' b₁ c x x₁ i i₁ k


ΠR-extend→×→ΠR-extend-inl : ∀ {ℓ} (J : RP∞' ℓ)
  (A : Bool → fst J → Type ℓ) (m : _)
  → ×→ΠR-extend J A (ΠR-extend→× J A (inl m)) ≡ (inl m)
ΠR-extend→×→ΠR-extend-inl J A (false , (b , c) , d) = refl
ΠR-extend→×→ΠR-extend-inl J A (true , (b , c) , d) = refl

fill23 : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
  (f : (i₁ : Bool) → Σ (fst J) (A i₁))
  (a : (i₁ : Bool) (j₁ : fst J) → A i₁ j₁)
  (b : (i₁ : Bool) → a i₁ (f i₁ .fst) ≡ f i₁ .snd)
  → I → I → I → ΠJoinR₁.ΠR-extend (RP∞'∙ ℓ) (fst J) A
fill23 J A f a b i j k =
  hfill (λ r → λ {(i = i0) → push (true , (inl (CasesBoolη f j , a false , b false))) r
                 ; (i = i1) → push (true , (inr (f true , CasesBoolη a j , b true))) r
                 ; (j = i0) → fill₂ (fst J) A (fst (f true)) (fst (f false)) (snd (f true))
                                       (snd (f false)) (a true) (a false) (b true) (b false) (i ∧ r) (i ∨ ~ r) i1
                 ; (j = i1) → push (true , (push (f , (a , b)) i)) r})
        (inS (inl (true , f true , a false)))
        k

fill23PP : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
  (f : (i₁ : Bool) → Σ (fst J) (A i₁))
  (a : (i₁ : Bool) (j₁ : fst J) → A i₁ j₁)
  (b : (i₁ : Bool) → a i₁ (f i₁ .fst) ≡ f i₁ .snd)
  → Square (λ j → push (true , (inl (CasesBoolη f j , a false , b false))) i1)
            (λ j → push (true , (inr (f true , CasesBoolη a j , b true))) i1)
                  (λ i → fill₂ (fst J) A (fst (f true)) (fst (f false)) (snd (f true))
                                 (snd (f false)) (a true) (a false) (b true) (b false) i i i1)
            λ i → push (true , (push (f , (a , b)) i)) i1
fill23PP J A f a b i j = fill23 J A f a b i j i1

fill23' : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
  (f : (i₁ : Bool) → Σ (fst J) (A i₁))
  (a : (i₁ : Bool) (j₁ : fst J) → A i₁ j₁)
  (b : (i₁ : Bool) → a i₁ (f i₁ .fst) ≡ f i₁ .snd)
  → I → I → I → ΠJoinR₁.ΠR-extend (RP∞'∙ ℓ) (fst J) A
fill23' J A f a b i j k =
  hfill (λ r → λ {(i = i0) → push (false , inl (CasesBoolη f j , a true , b true)) r
                 ; (i = i1) → push (false , (inr (f false , CasesBoolη a j , b false))) r
                 ; (j = i0) → fill₂ (fst J) A (fst (f true)) (fst (f false)) (snd (f true))
                                       (snd (f false)) (a true) (a false) (b true) (b false) (i ∨ ~ r) (i ∧ r) i1
                 ; (j = i1) → push (false , (push (f , (a , b)) i)) r})
        (inS (inl (false , f false , a true)))
        k

fill23PP≡ : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
  (f : (i₁ : Bool) → Σ (fst J) (A i₁))
  (a : (i₁ : Bool) (j₁ : fst J) → A i₁ j₁)
  (b : (i₁ : Bool) → a i₁ (f i₁ .fst) ≡ f i₁ .snd)
  → fill23PP J A f a b ≡ λ i j → fill23' J A f a b i j i1
fill23PP≡ {ℓ = ℓ} J A f a b k i j =
  hcomp (λ r → λ {(i = i0) → push (true , inl (CasesBoolη f j , a false , b false)) (r ∨ k)
                 ; (i = i1) → push (true , inr (f true , CasesBoolη a j , b true)) (r ∨ k)
                 ; (j = i0) → fill₂ (fst J) A (fst (f true)) (fst (f false)) (snd (f true))
                                       (snd (f false)) (a true) (a false) (b true) (b false) (i ∧ (r ∨ k)) (i ∨ ~ (r ∨ k)) i1
                 ; (j = i1) → push (true , push (f , a , b) i) (r ∨ k)
                 ; (k = i0) → fill23 J A f a b i j r
                 ; (k = i1) → fill23' J A f a b i j i1})
    (hcomp (λ r → λ {(i = i0) → push (true , inl (CasesBoolη f j , a false , b false)) k
                 ; (i = i1) → push (true , push (CasesBoolη f j , CasesBoolη a j , lee j) r) k
                 ; (j = i0) → fill₂ (fst J) A (fst (f true)) (fst (f false)) (snd (f true))
                                       (snd (f false)) (a true) (a false) (b true) (b false) (i ∧ k) (i ∨ ~ k) r
                 ; (j = i1) → push (true , push (f , a , b) (r ∧ i)) k
                 ; (k = i0) → inl (true , f true , a false)
                 ; (k = i1) → tap2 r j i})
      (hcomp (λ r → λ {(i = i0) → push (true , inl (CasesBoolη f j , a false , b false)) (k ∨ ~ r)
                 ; (i = i1) → push (true , inl ((CasesBoolη f j) , ((a false) , (b false)))) (k ∨ ~ r)
                 ; (j = i0) → fill₂-b (fst J) A (fst (f true)) (fst (f false)) (snd (f true))
                                       (snd (f false)) (a true) (a false) (b true) (b false) (i ∧ k) (i ∨ ~ k) r
                 ; (j = i1) → push (true , inl (f , a false , b false)) (k ∨ ~ r)
                 ; (k = i0) → push (true , inl (CasesBoolη f j , a false , b false)) (~ r)
                 ; (k = i1) → tap r j i})
             ((inr (inl (CasesBoolη f j))))))
   where
   H = ΠJoinR₁.ΠR-extend (RP∞'∙ ℓ) (fst J) A

   topSqfiller : I → I → I → H
   topSqfiller i j k =
     hfill (λ r → λ {(i = i0) → fill₂-b (fst J) A (fst (f true)) (fst (f false)) (snd (f true))
                                            (snd (f false)) (a true) (a false) (b true) (b false) j j r
                 ; (i = i1) → inr (push (f , (a , CasesBool true (b true) (b false))) (~ r ∧ ~ j))
                 ; (j = i0) → inr (push ((CasesBoolη f i) , (a , (CasesBool true (b true) (b false)))) (~ r ∧ i))
                 ; (j = i1) → inr (inl (CasesBoolη f i))})
       (inS ((inr
          (push (CasesBoolη f i , a , CasesBool true (b true) (b false)) (i ∧ ~ j)))))
       k

   topSq : Square {A = H}
      (λ i₁ →
         fill₂-b (fst J) A (fst (f true)) (fst (f false)) (snd (f true))
         (snd (f false)) (a true) (a false) (b true) (b false) i₁ i₁ i1)
      (λ _ → inr (inl f)) (λ j₁ → inr (inl (CasesBoolη f j₁)))
      (λ j₁ → inr (inl (CasesBoolη f j₁)))
   topSq i j = topSqfiller i j i1
  
   tap : Cube {A = H}
              (λ j i → inr (inl (CasesBoolη f j)))
              topSq
              (λ r i → fill₂-b (fst J) A (fst (f true)) (fst (f false)) (snd (f true))
                         (snd (f false)) (a true) (a false) (b true) (b false) i i r)
              (λ _ _ → inr (inl f))
              (λ r j → inr (inl (CasesBoolη f j)))
              (λ r j → inr (inl (CasesBoolη f j))) -- r j i
   tap i j k =
     hcomp (λ r → λ {(i = i0) → inr (push (CasesBoolη f j , a , CasesBool true (b true) (b false)) (~ r ∧ ~ k ∧ j))
                 ; (i = i1) → topSqfiller j k r
                 ; (j = i0) → fill₂-b (fst J) A (fst (f true)) (fst (f false)) (snd (f true))
                                (snd (f false)) (a true) (a false) (b true) (b false) k k (i ∧ r)
                 ; (j = i1) → inr (push (f , a , CasesBool true (b true) (b false)) (~ r ∧ ~ k))
                 ; (k = i0) → inr (push (CasesBoolη f j , a , CasesBool true (b true) (b false)) (~ r ∧ j))
                 ; (k = i1) → inr (inl (CasesBoolη f j))})
           ((inr
          (push (CasesBoolη f j , a , CasesBool true (b true) (b false))
           (~ k ∧ j))))


   lee : PathP (λ i₁ → (i₃ : Bool) → CasesBoolη a i₁ i₃ (CasesBoolη f i₁ i₃ .fst) ≡ CasesBoolη f i₁ i₃ .snd) (CasesBool true (b true) (b false)) b
   lee = funExt λ { false → refl ; true → refl}


   tap2 : Cube {A = H}
              (λ j i → topSq j i)
              (λ j i → fill23' J A f a b i j i1)
              (λ r i → fill₂ (fst J) A (fst (f true)) (fst (f false)) (snd (f true))
                    (snd (f false)) (a true) (a false) (b true) (b false) i i r)
              (λ r i → inr (push (f , a , b) (r ∧ i)))
              (λ i j → inr (inl (CasesBoolη f j)))
              λ i j → inr (push (CasesBoolη f j , CasesBoolη a j , lee j) i)
   tap2 r i j =
     hcomp (λ k → λ {(i = i0) → fill₂ (fst J) A (fst (f true)) (fst (f false)) (snd (f true))
                                       (snd (f false)) (a true) (a false) (b true) (b false) (j ∨ (~ k ∧ r)) (j ∧ (k ∨ ~ r)) r
                 ; (i = i1) → push (false , push (f , a , b) (r ∧ j)) (k ∨ ~ r)
                 ; (j = i0) → push (false , inl ((CasesBoolη f i) , ((a true) , (b true)))) (k ∨ ~ r)
                 ; (j = i1) → push (false , push ((CasesBoolη f i) , (CasesBoolη a i , lee i)) r) (k ∨ ~ r)
                 ; (r = i0) → topSqfiller i j i1
                 ; (r = i1) → fill23' J A f a b j i k})
           (hcomp (λ k → λ {(i = i0) →
             fill₂ (fst J) A (fst (f true)) (fst (f false)) (snd (f true)) (snd (f false)) (a true) (a false) (b true) (b false) (j ∨ r) (j ∧ (~ r)) (r ∧ k)
                 ; (i = i1) → push (false , push (f , a , CasesBoolη b k) (r ∧ (j ∧ k))) (~ r)
                 ; (j = i0) → push ((false , inl (CasesBoolη f i , a true , b true))) (~ r)
                 ; (j = i1) → push ((false , push (CasesBoolη f i , CasesBoolη a i , helpme k i) (r ∧ k))) (~ r)
                 ; (r = i0) → topSqfiller i j i1 -- topSqfiller i j i1
                 ; (r = i1) → inl (false , f false , a true)})
              (hcomp (λ k → λ {(i = i0) → fill₂-b (fst J) A (fst (f true)) (fst (f false))
                                             (snd (f true)) (snd (f false))
                                             (a true) (a false) (b true) (b false) (j ∨ r) (j ∧ (~ r)) k
                 ; (i = i1) → push (false , push (f , (a , CasesBool true (b true) (b false))) ((~ r ∧ ~ j)  ∧ ~ k)) (~ k ∨ (~ r))
                 ; (j = i0) → push (false , push ((CasesBoolη f i) , (a , CasesBool true (b true) (b false))) (~ r ∧ (~ k ∧ i))) (~ k ∨ (~ r))
                 ; (j = i1) → push (false , inl (CasesBoolη f i , a true , b true)) (~ k ∨ ~ r)
                 ; (r = i0) → topSqfiller i j k
                 ; (r = i1) → push (false , (inl (CasesBoolη f i , a true , b true))) (~ k)})
                (inr (push (CasesBoolη f i , a , CasesBool true (b true) (b false)) (i ∧ (~ j ∧ ~ r))))))
                where
                harp : PathP
                       (λ i₁ →
                          (i₃ : Bool) →
                          CasesBoolη a i₁ i₃ (CasesBoolη f i₁ i₃ .fst) ≡
                          CasesBoolη f i₁ i₃ .snd)
                       (CasesBool true (b true) (b false))
                       (CasesBool true (b true) (b false))
                harp = funExt λ { false → refl ; true → refl}
                helpme : SquareP (λ k i → (i₁ : Bool) → CasesBoolη a i i₁ (CasesBoolη f i i₁ .fst) ≡ CasesBoolη f i i₁ .snd)
                              harp (λ i → lee i) (refl {x = CasesBool true (b true) (b false)}) (CasesBoolη b)
                helpme i a false = b false
                helpme i a true = b true

ΠR-extend→×→ΠR-extend : ∀ {ℓ} {J : RP∞' ℓ} (A : Bool → fst J → Type ℓ) (m : _)
  → ×→ΠR-extend J A (ΠR-extend→× J A m) ≡ m
ΠR-extend→×→ΠR-extend {J = J} A (inl m) = ΠR-extend→×→ΠR-extend-inl J A m
ΠR-extend→×→ΠR-extend A (inr (inl x)) j = inr (inl (CasesBoolη x j))
ΠR-extend→×→ΠR-extend {J = J} A (inr (inr x)) j = inr (inr (CasesBoolη {A = λ i → (j : fst J) → A i j} x j ))
ΠR-extend→×→ΠR-extend {J = J} A (inr (push (f , a , b) i)) j = fill23 J A f a b i j i1
ΠR-extend→×→ΠR-extend A (push (false , inl (f , q , t)) i) i₁ = push (false , inl (CasesBoolη f i₁ , q , t)) i
ΠR-extend→×→ΠR-extend A (push (true , inl (f , q , t)) i) i₁ = push (true , inl (CasesBoolη f i₁ , q , t)) i
ΠR-extend→×→ΠR-extend A (push (false , inr (f , q , t)) i) j = push (false , inr (f , CasesBoolη q j , t)) i
ΠR-extend→×→ΠR-extend A (push (true , inr (f , q , t)) i) j = push (true , inr (f , CasesBoolη q j , t)) i
ΠR-extend→×→ΠR-extend {J = J} A (push (false , push (f , q , t) i₂) i) i₁ =
  hcomp (λ r → λ {(i = i0) → inl (false , f false , q true)
                  ; (i = i1) → fill23PP≡ J A f q t (~ r) i₂ i₁
                  ; (i₁ = i0) → fill₂ (fst J) A (fst (f true)) (fst (f false))
                                         (snd (f true)) (snd (f false))
                                         (q true) (q false)
                                         (t true) (t false)
                                         ((~ i) ∨ i₂) (i ∧ i₂) i1
                  ; (i₁ = i1) → push (false , push (f , q , t) i₂) i -- push (false , {!!}) i
                  ; (i₂ = i0) → push (false , inl (CasesBoolη f i₁ , q true , t true)) i
                  ; (i₂ = i1) → push (false , inr (f false , CasesBoolη q i₁ , t false)) i})
     (hcomp (λ r → λ {(i = i0) → inl (false , f false , q true)
                  ; (i = i1) → fill23' J A f q t i₂ i₁ r
                  ; (i₁ = i0) → fill₂ (fst J) A (fst (f true)) (fst (f false))
                                         (snd (f true)) (snd (f false))
                                         (q true) (q false)
                                         (t true) (t false)
                                         ((~ i) ∨ (i₂ ∨ ~ r)) (i ∧ (i₂ ∧ r)) i1
                  ; (i₁ = i1) → push (false , push (f , q , t) i₂) (r ∧ i)
                  ; (i₂ = i0) → push (false , (inl ((CasesBoolη f i₁) , ((q true) , (t true))))) (i ∧ r)
                  ; (i₂ = i1) → push (false , inr (f false , CasesBoolη q i₁ , t false)) (i ∧ r)})
                  (inl (false , f false , q true)))
ΠR-extend→×→ΠR-extend {J = J} A (push (true , push (f , q , t) i₂) i) i₁ =
  hcomp (λ r → λ {(i = i0) → inl (true , f true , q false)
                  ; (i = i1) → fill23 J A f q t i₂ i₁ r
                  ; (i₁ = i0) → fill₂ (fst J) A (fst (f true)) (fst (f false))
                                         (snd (f true)) (snd (f false))
                                         (q true) (q false)
                                         (t true) (t false)
                                         (i ∧ (i₂ ∧ r)) ((~ i) ∨ (i₂ ∨ ~ r)) i1
                  ; (i₁ = i1) → push (true , push (f , q , t) i₂) (r ∧ i)
                  ; (i₂ = i0) → push (true , inl (CasesBoolη f i₁ , q false , t false)) (i ∧ r)
                  ; (i₂ = i1) → push (true , inr (f true , CasesBoolη q i₁ , t true)) (i ∧ r)})
          (inl (true , f true , q false))


ΠR-extend→×Iso : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
  → Iso (ΠJoinR₁.ΠR-extend (RP∞'∙ ℓ) (fst J) A)
         (joinR-gen (fst J) (A true) × joinR-gen (fst J) (A false))
Iso.fun (ΠR-extend→×Iso J A) = ΠR-extend→× J A
Iso.inv (ΠR-extend→×Iso J A) = ×→ΠR-extend J A
Iso.rightInv (ΠR-extend→×Iso J A) = ×→ΠR-extend→× {J = J} A
Iso.leftInv (ΠR-extend→×Iso J A) = ΠR-extend→×→ΠR-extend {J = J} A

module _ {ℓ : Level} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
  where
  module ΠR-extend→Π-equiv-base-lemmas where
    p : ΠR-extend→Π-alt J A ≡ ΠJoinR₁.ΠR-extend→Π (RP∞'∙ ℓ) (fst J) A
    p = funExt λ x → funExt (ΠR-extend→Π-alt≡ {J = J} A x)

    alt : (ΠJoinR₁.ΠR-extend (RP∞'∙ ℓ) (fst J) A) ≃ ((x : Bool) → joinR-gen (fst J) (A x))
    alt = isoToEquiv (compIso (ΠR-extend→×Iso J A) (invIso ΠBool×Iso))

    altid : fst alt ≡ ΠR-extend→Π-alt J A
    altid = funExt λ x → funExt (CasesBool true refl refl)

    isEq : isEquiv (ΠR-extend→Π-alt J A)
    isEq = subst isEquiv altid (snd alt)

  open ΠR-extend→Π-equiv-base-lemmas
  ΠR-extend→Π-equiv-base : isEquiv (ΠJoinR₁.ΠR-extend→Π (RP∞'∙ ℓ) (fst J) A)
  ΠR-extend→Π-equiv-base = transport (λ i → isEquiv (p i)) isEq

ΠR-extend→Π-equiv : ∀ {ℓ} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
  → isEquiv (ΠJoinR₁.ΠR-extend→Π I (fst J) A)
ΠR-extend→Π-equiv {ℓ} =
  RP∞'pt→Prop (λ _ → isPropΠ2 λ _ _ → isPropIsEquiv _) ΠR-extend→Π-equiv-base

eval⊎≃ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → B ⊎ (A ≃ B) → A → B
eval⊎≃ (inl x) _ = x
eval⊎≃ (inr x) = fst x

eval⊎≃Equiv : ∀ {ℓ} {I J : RP∞' ℓ}
  → (fst J ⊎ (fst I ≃ fst J)) ≃ (fst I → fst J)
eval⊎≃Equiv {ℓ} {I} {J} = eval⊎≃ ,
  RP∞'pt→Prop {B = λ I → isEquiv {A = fst J ⊎ (fst I ≃ fst J)} eval⊎≃}
    (λ _ → isPropIsEquiv _) (isoToIsEquiv (invIso isEquivG)) I
  where
  back : (J : RP∞' ℓ) → fst J × fst J → Lift (fst J ⊎ (Bool ≃ fst J))
  back J = uncurry λ j → snd J .fst .snd .snd (λ _ → Lift (fst J ⊎ (Bool ≃ fst J))) .fst j
    (lift (inl j))
    (lift (inr (invEquiv (isRP∞→≃Bool _ (fst J) (snd J .fst) j))))

  T : (J : RP∞' ℓ) → (j : fst J) → _
  T J j = snd J .fst .snd .snd (λ _ → Lift (fst J ⊎ (Bool ≃ fst J))) .snd j (lift (inl j))
    (lift (inr (invEquiv (isRP∞→≃Bool _ (fst J) (snd J .fst) j))))

  inr* : _ → Bool ⊎ (Bool ≃ Bool)
  inr* = inr

  FF : (J : RP∞' ℓ) → Lift (fst J ⊎ (Bool ≃ fst J)) → _
  FF J = invEq LiftEquiv

  Iso1 : Iso (fst J × fst J) (fst J ⊎ (Bool ≃ fst J))
  Iso.fun Iso1 = FF J ∘ (back J)
  Iso.inv Iso1 f = Iso.fun ΠBool×Iso (eval⊎≃ f)
  Iso.rightInv Iso1 (inl j) =
    cong (invEq (LiftEquiv {ℓ' = ℓ})) (T J j .fst)
  Iso.rightInv Iso1 (inr eq) =
    EquivJRP∞' (RP∞'∙ ℓ) {B = λ J eq → invEq LiftEquiv (back J (ΠBool→× (fst eq))) ≡ inr eq}
      (cong inr* (Σ≡Prop (λ _ → isPropIsEquiv _)
        (funExt (CasesBool true refl refl)))) J eq
  Iso.leftInv Iso1 =
    uncurry (JRP∞' {B = λ J x → (y : fst J)
                → ΠBool→× (eval⊎≃ (FF J (back J (x , y)))) ≡ (x , y)}
      (CasesBool true refl refl) J)

  isEquivG : Iso (Bool → fst J) (fst J ⊎ (Bool ≃ fst J))
  Iso.fun isEquivG = invEq LiftEquiv ∘ back J ∘ Iso.fun ΠBool×Iso
  Iso.inv isEquivG = eval⊎≃
  Iso.rightInv isEquivG x = Iso.rightInv Iso1 x
  Iso.leftInv isEquivG x =
    (sym (Iso.leftInv ΠBool×Iso (eval⊎≃ (FF J (back J (x true , x false)))))
    ∙ cong (Iso.inv ΠBool×Iso) (Iso.leftInv Iso1 (x true , x false)))
    ∙ funExt (CasesBool true refl refl)

private
  eval⊎≃Equiv-elim' : ∀ {ℓ ℓ'} {A B : Type ℓ} {C : B → Type ℓ'} (e : A ≃ B)
    → (ind : (a : A) → C (fst e a))
    → (x : _) → subst C (secEq e _) (ind (invEq e (fst e x))) ≡ ind x
  eval⊎≃Equiv-elim' {A = A} {B = B} {C = C} =
    EquivJ (λ A e → (ind : (a : A) → C (fst e a))
      → (x : _) → subst C (secEq e _) (ind (invEq e (fst e x))) ≡ ind x)
      λ ind x → transportRefl (ind x)

module _ {ℓ : Level} {I J : RP∞' ℓ} {A : (fst I → fst J) → Type ℓ}
  (ind : (x : _) → A (fst (eval⊎≃Equiv {I = I} {J}) x)) where
  eval⊎≃Equiv-elim : (x : _) → A x
  eval⊎≃Equiv-elim f = subst A (secEq (eval⊎≃Equiv {ℓ} {I} {J}) f) (ind (invEq (eval⊎≃Equiv {I = I} {J}) f))

  eval⊎≃Equiv-elim-coh : (x : _) → eval⊎≃Equiv-elim  (fst (eval⊎≃Equiv {I = I} {J}) x) ≡ ind x
  eval⊎≃Equiv-elim-coh = eval⊎≃Equiv-elim' {C = A} (eval⊎≃Equiv {I = I} {J}) ind


module _ {ℓ : Level} (I J : RP∞' ℓ) {A : fst I → fst J → Type ℓ} where
  M1 : (C : Type) (t : C ≃ (fst I → fst J))
    → ((i : fst I) → Σ (fst J) (A i))
    → Σ[ c ∈ C ] ((i : fst I) → A i (t .fst c i))
  M1 C t j = (invEq t (fst ∘ j))
    , λ i → subst (A i) (λ k → secEq t (λ i → fst (j i)) (~ k) i) (snd (j i))

  M2 : (C : Type) (t : C ≃ (fst I → fst J))
    → Σ[ c ∈ C ] ((i : fst I) → A i (t .fst c i))
    → ((i : fst I) → Σ (fst J) (A i))
  M2 C t (c , f) j = t .fst c j , f j

  M121 : (C : Type) (t : C ≃ (fst I → fst J))
    → (x : _) → M1 C t (M2 C t x) ≡ x
  M121 C = EquivJ (λ C t → (x : _) → M1 C t (M2 C t x) ≡ x)
    λ {(f , p) → ΣPathP (refl , funExt λ j → transportRefl (p j))}

  M212 : (C : Type) (t : C ≃ (fst I → fst J))
    → (x : _) → M2 C t (M1 C t x) ≡ x
  M212 C = EquivJ (λ C t → (x : _) → M2 C t (M1 C t x) ≡ x)
            λ f → funExt λ i → ΣPathP (refl , (transportRefl (snd (f i))))
  

module _ {ℓ : Level} (I J : RP∞' ℓ) {A : fst I → fst J → Type ℓ} where
  f1 : ((i : fst I) → Σ (fst J) (A i))
    → Σ[ r ∈ fst J ⊎ (fst I ≃ fst J) ] ((i : fst I) → A i (fst (eval⊎≃Equiv {I = I} {J = J}) r i))
  f1 = M1 I J {A = A} _ (eval⊎≃Equiv {I = I} {J = J})

  f3 : Σ[ r ∈ fst J ⊎ (fst I ≃ fst J) ] ((i : fst I) → A i (fst (eval⊎≃Equiv {I = I} {J = J}) r i)) → ((i : fst I) → Σ (fst J) (A i))
  f3 = M2 I J {A = A} _ (eval⊎≃Equiv {I = I} {J = J})


  TotAIso : Iso ((i : fst I) → Σ (fst J) (A i))
                (Σ[ r ∈ fst J ⊎ (fst I ≃ fst J) ]
                  ((i : fst I) → A i (fst (eval⊎≃Equiv {I = I} {J = J}) r i)))
  Iso.fun TotAIso = f1
  Iso.inv TotAIso = f3
  Iso.rightInv TotAIso x =
      M121 I J {A = A} _ (eval⊎≃Equiv {I = I} {J = J}) x
  Iso.leftInv TotAIso x =
     M212 I J {A = A} _ (eval⊎≃Equiv {I = I} {J = J}) x
