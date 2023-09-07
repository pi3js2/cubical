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
open import Cubical.Data.Bool hiding (_≤_)

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

open import Cubical.Cohomology.EilenbergMacLane.GenSmash

open import Cubical.Foundations.Univalence
open import Cubical.Cohomology.EilenbergMacLane.join.prelims


module Cubical.Cohomology.EilenbergMacLane.join.2elter where
open import Cubical.HITs.Join
open import Cubical.Functions.FunExtEquiv


module 2-elter {ℓ : Level} (I : RP∞' ℓ) (J : Type) (A : fst I → J → Type ℓ) where
  I2 = I .snd
  notI : fst I → fst I
  notI = I2 .fst .fst

  elimI : {B : fst I → Type ℓ} → _
  elimI {B} = I2 .fst .snd .snd B .fst

  elimIβ : {B : fst I → Type ℓ} → _
  elimIβ {B} = I2 .fst .snd .snd B .snd
  
  ΠR-base : Type _
  ΠR-base =
    Pushout {A = Σ[ f ∈ (TotΠ λ i → Σ[ j ∈ J ] (A i j)) ]
      (Σ[ g ∈ ((i : fst I) (j : J) → A i j) ] ((i : fst I) → g i (f i .fst) ≡ f i .snd))}
                    {B = TotΠ λ i → Σ[ j ∈ J ] (A i j)}
                    {C = (i : fst I) (j : J) → A i j}
                    fst
                    (fst ∘ snd)

  left-push : Type _
  left-push = Σ[ i ∈ fst I ] (Σ[ j ∈ J ] (A i j)) × ((j : J) → A (notI i) j)

  left-push↑ₗ : fst I → Type _
  left-push↑ₗ i = Σ[ f ∈ ((i : fst I) → Σ[ j ∈ J ] A i j) ]
    Σ[ g ∈ ((j : J) → A (notI i) j) ] (g (f (notI i) .fst) ≡ f (notI i) .snd)

  left-push↑ᵣ : fst I → Type _
  left-push↑ᵣ i = Σ[ f ∈ (Σ[ j ∈ J ] A i j) ]
      Σ[ g ∈ ((i : fst I) (j : J) → A i j) ] g i (fst f) ≡ snd f

  fat : Type _
  fat = (Σ[ f ∈ ((i : fst I) → Σ[ j ∈ J ] A i j) ]
          Σ[ g ∈ ((i : fst I) (j : J) → A i j) ]
            ((i : fst I) → g i (f i .fst) ≡ f i .snd))

  fat→ₗ : (i : fst I) → fat → left-push↑ₗ i
  fat→ₗ  i (f , g , r) = (f , (g (notI i)) , (r (notI i)))

  fat→ᵣ : (i : fst I) → fat → left-push↑ᵣ i
  fat→ᵣ i (f , g , r) =  f i , g , r i

  PushTop : Type _
  PushTop = Σ[ i ∈ fst I ] (Pushout (fat→ₗ i) (fat→ᵣ i))

  PushTop→left-push' : (i : fst I)
    → (Pushout (fat→ₗ i) (fat→ᵣ i))
    → (Σ[ j ∈ J ] (A i j)) × ((j : J) → A (notI i) j)
  PushTop→left-push' i (inl (f , g , p)) = (f i) , g
  PushTop→left-push' i (inr (f , g , p)) = f , (g (notI i))
  PushTop→left-push' i (push (f , g , p) k) = (f i) , λ j → g (notI i) j

  PushTop→left-push : PushTop → left-push
  PushTop→left-push (i , x) = (i , PushTop→left-push' i x)

  PushTop→ΠR-base : PushTop → ΠR-base
  PushTop→ΠR-base (i , inl (f , g , p)) = inl f
  PushTop→ΠR-base (i , inr (f , g , p)) = inr g
  PushTop→ΠR-base (i , push (f , g , p)  i₁) = push (f , g , p) i₁

  ΠR-extend : Type _
  ΠR-extend = Pushout PushTop→left-push PushTop→ΠR-base


  ΠR-extend→Πₗ : left-push → TotΠ (λ i → joinR-gen J (A i))
  ΠR-extend→Πₗ (i , p , r) = elimI i (inlR p) (inrR r)

  ΠR-base→ : ΠR-base → TotΠ (λ i → joinR-gen J (A i))
  ΠR-base→ (inl x) i = inlR (x i)
  ΠR-base→ (inr x) i = inrR λ j → x i j
  ΠR-base→ (push a i') i = push* (fst a i) (fst (snd a) i) (snd (snd a) i) i'

  pre-eqvl-diag : (i' : fst I) (p : Pushout (fat→ₗ i') (fat→ᵣ i'))
    → ΠR-extend→Πₗ (PushTop→left-push (i' , p)) i'
     ≡ ΠR-base→ (PushTop→ΠR-base (i' , p)) i'
  pre-eqvl-diag i' (inl (f , f2 , p)) =
    elimIβ {B = λ i → joinR-gen J (A i)} i' (inlR (f i' .fst , f i' .snd)) (inrR f2) .fst
  pre-eqvl-diag i' (inr (f , f2 , p)) =
    elimIβ {B = λ i → joinR-gen J (A i)} i' (inlR f) (inrR (f2 (notI i'))) .fst ∙ push* f (f2 i') p 
  pre-eqvl-diag i' (push (f , f2 , p) i) j =
    compPath-filler (elimIβ {B = λ i → joinR-gen J (A i)} i' (inlR (f i')) (inrR (f2 (notI i'))) .fst)
                    (push* (f i') (f2 i') (p i')) i j

  pre-eqvl-not : (i' : fst I) (p : Pushout (fat→ₗ i') (fat→ᵣ i'))
    → ΠR-extend→Πₗ (PushTop→left-push (i' , p)) (notI i') ≡
      ΠR-base→ (PushTop→ΠR-base (i' , p)) (notI i')
  pre-eqvl-not i' (inl (f , f2 , p)) =
      elimIβ {B = λ i → joinR-gen J (A i)} i' (inlR (f i')) (inrR f2) .snd
    ∙ sym (push* (f (notI i')) f2 p)
  pre-eqvl-not i' (inr (f , f2 , p)) =
    elimIβ {B = λ i → joinR-gen J (A i)} i' (inlR f) (inrR (f2 (notI i'))) .snd
  pre-eqvl-not i' (push (f , f2 , p) i) j =
      compPath-filler
        (elimIβ {B = λ i → joinR-gen J (A i)} i' (inlR (f i')) (inrR (f2 (notI i'))) .snd)
        (sym (push* (f (notI i')) (f2 (notI i')) (p (notI i')))) (~ i) j


  eqvl : (a : PushTop) (i : fst I)
    → ΠR-extend→Πₗ (PushTop→left-push a) i
     ≡ ΠR-base→ (PushTop→ΠR-base a) i
  eqvl (i' , p) =
    elimI i' (pre-eqvl-diag i' p)
                 (pre-eqvl-not i' p)

  ΠR-extend→Π : ΠR-extend → TotΠ (λ i → joinR-gen J (A i))
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
    updater→ (push a i) = push* (fst a , ΠR-extend→Π (snd a) (fst a)) (ΠR-extend→Π (snd a)) refl i

    updater← : joinR-gen (fst I) (λ i → joinR-gen J (A i)) → dable
    updater← (inlR x) = inl x
    updater← (inrR x) = inr (invEq (_ , ise) x)
    updater← (push* a b x i) =
      (cong inl123 (ΣPathP (refl , sym x ∙ sym (funExt⁻ (secEq (_ , ise) b) (fst a))))
              ∙ push ((fst a) , invEq (_ , ise) b)) i
