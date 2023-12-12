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


open import Cubical.Cohomology.EilenbergMacLane.nov.base
open import Cubical.Cohomology.EilenbergMacLane.nov.boolcase
open import Cubical.Cohomology.EilenbergMacLane.nov.boolcase-alt
module Cubical.Cohomology.EilenbergMacLane.nov.final where
open import Cubical.HITs.Join
open import Cubical.Functions.FunExtEquiv

mapone-l : {ℓ : Level} (I J : RP∞' ℓ)  (A : fst I → fst J → Type ℓ) (i : fst I)
  → 2-elter.ΠR-base I (fst J) A → joinR-gen (fst J) (A i)
mapone-l I J A i (inl x) = inlR (x i)
mapone-l I J A i (inr x) = inrR (x i)
mapone-l I J A i (push a i₁) = push* (fst a i) (snd a .fst i ) (snd a .snd i) i₁

mapone : {ℓ : Level} (I J : RP∞' ℓ)  (A : fst I → fst J → Type ℓ) (i : fst I)
  → 2-elter.ΠR-extend I (fst J) A → joinR-gen (fst J) (A i)
mapone I J A i (inl (i'  , (j ,  a) , k)) = leftFun'-inl I (fst J) A i' (j , a) k i
mapone I J A i (inr x) = mapone-l I J A i x
mapone I J A i (push (i' , inl x) j) = {!!}
mapone I J A i (push (i' , inr x) j) = {!!}
mapone I J A i (push (i' , push a i₁) j) = {!!}

module EZ {ℓ : Level} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) where
  DOMTY : Type ℓ
  DOMTY = joinR-gen (fst I) λ i → joinR-gen (fst J) (A i)

  equivElim-lem : ∀ {ℓ} {A B : Type ℓ}
               (C : B → Type ℓ)
               (e : A ≃ B)
               → ((a : A) → C (fst e a))
               → ((b : B) → C b)
  equivElim-lem C e ind b = subst C (secEq e b) (ind (invEq e b))

  equivElim-lem-id : ∀ {ℓ} {A B : Type ℓ} (C : B → Type ℓ)
               → (e : A ≃ B)
               → (ind : (a : A) → C (fst e a))
               → (a : A)
               → equivElim-lem C e ind (fst e a) ≡ ind a
  equivElim-lem-id {A = A} {B = B} C =
    EquivJ (λ A e →
                (ind : (a : A) → C (fst e a))
               → (a : A)
               → equivElim-lem C e ind (fst e a) ≡ ind a)
           λ ind a → transportRefl (ind a)

  mainTY :  (f : TotΠ (λ i → Σ-syntax (fst J) (A i)))
    → Type ℓ
  mainTY f = Σ[ h ∈ ΠR-extend* I J A ]
          ((g : (i₁ : fst I) (j : fst J) → A i₁ j)
            (p : (i₁ : fst I) → g i₁ (f i₁ .fst) ≡ f i₁ .snd)
          → h ≡ inr (inr g))

  main-b : (x : _) → mainTY (Iso.inv (TotAIso I J {A}) x)
  fst (main-b x) = inr (inl x)
  snd (main-b x) g p k  = inr (push (x , (g , p)) k)

  main : (f : TotΠ (λ i → Σ-syntax (fst J) (A i)))
      → mainTY f
  main = equivElim-lem mainTY
          (invEquiv (isoToEquiv (TotAIso I J {A})))
          main-b

  mainId : (x : _)
    → main (Iso.inv (TotAIso I J {A}) x) ≡ main-b x
  mainId = equivElim-lem-id mainTY
          (invEquiv (isoToEquiv (TotAIso I J {A})))
          main-b


  megaty : (f : TotΠ (λ i → Σ-syntax (fst J) (A i))) → Type ℓ
  megaty f =
    Σ[ h ∈ ΠR-extend* I J A ]
      Σ[ h2 ∈ (((g : (i₁ : fst I) (j : fst J) → A i₁ j)
              (p : (i₁ : fst I) → g i₁ (f i₁ .fst) ≡ f i₁ .snd)
            → h ≡ inr (inr g))) ]
       ((t : fst I)
         → Σ[ one ∈ (((q : (j : fst J) → A (RP'.notI I t) j) (p : q (f (RP'.notI I t) .fst) ≡ f (RP'.notI I t) .snd)
                   → inl (t , f t , q) ≡ h)) ]
         (((g : (i₂ : fst I) (j : fst J) → A i₂ j)
              (p : (i₂ : fst I) → g i₂ (f i₂ .fst) ≡ f i₂ .snd)
           → Square (λ j → inl (t , f t , g (I .snd .fst .fst t)))
                    (h2 g p)
                    (one (g (RP'.notI I t)) (p _))
                    (push (t , inr (f t , g , p t))))))

  megaty-b : (f : _) → megaty (Iso.inv (TotAIso I J {A}) f)
  fst (megaty-b f) = inr (inl f)
  fst (snd (megaty-b f)) g p k = inr (push (f , (g , p)) k)
  fst (snd (snd (megaty-b f)) t) g q = push (t , (inl (f , g , q)))
  snd (snd (snd (megaty-b f)) t) g q i j = push (t , push (f , g , q) j) i

  megaty-ba : (f : _) → megaty f
  megaty-ba =
    equivElim-lem megaty (invEquiv (isoToEquiv (TotAIso I J {A})))
     megaty-b

  megaty-ba≡ : (f : _) → megaty-ba (Iso.inv (TotAIso I J {A}) f) ≡ megaty-b f
  megaty-ba≡ =
    equivElim-lem-id megaty (invEquiv (isoToEquiv (TotAIso I J {A})))
      megaty-b

  L2-side : 2-elter.ΠR-extend I (fst J) A
          → ΠR-extend* I J A
  L2-side (inl x) = inl x
  L2-side (inr (inl f)) = megaty-ba f .fst
  L2-side (inr (inr x)) = inr (inr x)
  L2-side (inr (push (f , g , p) i)) = megaty-ba f .snd .fst g p i
  L2-side (push (t , inl (f , q , p)) i) = megaty-ba f .snd .snd t .fst q p i
  L2-side (push (t , inr x) i) = push (t , inr x) i
  L2-side (push (t , push (f , g , p) j) i) = megaty-ba f .snd .snd t .snd g p i j


module _ {ℓ : Level} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ) where
  open EZ (RP∞'· ℓ) J A

  T = TotAIso (RP∞'· ℓ) J {A}

  main-cohTY : (f : _) (m : mainTY f) → Type ℓ
  main-cohTY f m = Σ[ h ∈ (inlR (f true) ≡ leftFun*-full (RP∞'· ℓ) J A true (m .fst)) ]
               ((g : (i₁ : fst (RP∞'· ℓ)) (j : fst J) → A i₁ j)
                      (p : (i₁ : fst (RP∞'· ℓ)) → g i₁ (f i₁ .fst) ≡ f i₁ .snd)
                 → Square h (λ _ → inrR (g true))
                             (push* (f true) (g true) (p true))
                             λ i → leftFun*-full (RP∞'· ℓ) J A true (m .snd g p i))

  main-cohTY-bb : (f : _) → main-cohTY (Iso.inv T f) (main-b f)
  fst (main-cohTY-bb (inl x , p)) = refl
  fst (main-cohTY-bb (inr x , p)) = refl
  snd (main-cohTY-bb (inl x , p)) g q = λ i _ → push* (Iso.inv T (inl x , p) true) (g true) (q true) i
  snd (main-cohTY-bb (inr x , p)) g q = {!!} -- i _ → push* (Iso.inv T (inl x , p) true) (g true) (q true) i

  main-cohTY-b : (f : _) → main-cohTY (Iso.inv T f) (main (Iso.inv T f))
  main-cohTY-b f = subst (main-cohTY (Iso.inv T f)) (sym (mainId f)) (main-cohTY-bb f)

  main-coh : (f : _) → main-cohTY f (main f)
  main-coh = equivElim-lem (λ f → main-cohTY f (main f))
                          (invEquiv (isoToEquiv T))
                          main-cohTY-b

  TYVM : (f : TotΠ (λ i → Σ-syntax (fst J) (A i))) (q : megaty f)
    → Type ℓ
  TYVM f q =
    Σ[ p1 ∈ {!!} ]
      {!!}
  

  L2-side-Bool : (a : _)
    → leftFun (fst J) A a ≡ leftFun*-full (RP∞'· ℓ) J A true (EZ.L2-side (RP∞'· ℓ) J A a)
  L2-side-Bool (inl (false , a)) = refl
  L2-side-Bool (inl (true , a)) = refl
  L2-side-Bool (inr (inl f)) = {!f!} -- main-coh f .fst
  L2-side-Bool (inr (inr x)) = refl
  L2-side-Bool (inr (push (f , g , p) i)) = {!!} -- main-coh f .snd g p i
  L2-side-Bool (push (t , x) i) = {!!}

mainCoh : {ℓ : Level} (I : RP∞' ℓ) (t : fst I) (J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
  → (a : _)
  → snd (leftFunExt I (fst J) A (t , a))
  ≡ leftFun*-full I J A t (EZ.L2-side I J A a)
mainCoh {ℓ = ℓ} = JRP∞' λ J A a
   → (λ k → help k (fst J) A a)
  ∙ L2-side-Bool J A a
  where
  help :  leftFunExtCurry (RP∞'· ℓ) true ≡ leftFun
  help = JRP∞'∙ leftFun



module _ {ℓ : Level} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) where
  open EZ I J A
  L2 : joinR-Push' I (fst J) A → Pushout (λ i → fst i , leftFun*-full I J A (fst i) (snd i)) snd
  L2 (inl x) = inl x
  L2 (inr x) = inr (L2-side x)
  L2 (push (t , a) i) = ((λ k → inl (t , mainCoh I t J A a k)) ∙ push (t , L2-side a)) i

  mainComm : DOMTY → GOALTY I J A
  mainComm x = TheId I J A (ΠR-pushout→Better! I J A (L2 x'))
    where
    x' : joinR-Push' I (fst J) A
    x' = Iso.fun (FullIso₁ I J A) (Iso.fun (joinR-Equiv) x)
