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

  abstract
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

  L2-side-Bool-inl : (a : _)
    → leftFun (fst J) A (inl a) ≡ leftFun*-fullBool J A true (EZ.L2-side (RP∞'· ℓ) J A (inl a))
  L2-side-Bool-inl (false , snd₁) = refl
  L2-side-Bool-inl (true , snd₁) = refl

  L2-side-Bool-push-inr : (t : Bool) (x : 2-elter.left-push↑ᵣ (RP∞'· ℓ) (fst J) A t)
    → Square (λ i → leftFun (fst J) A (push (t , inr x) i))
              (λ i → leftFun*-fullBool J A true (push (t , inr x) i))
              (L2-side-Bool-inl (t , fst x , fst (snd x) (not t)))
              refl
  L2-side-Bool-push-inr false x = refl
  L2-side-Bool-push-inr true x = refl

  TYVM : (f : TotΠ (λ i → Σ-syntax (fst J) (A i))) (q : megaty f)
    → Type ℓ
  TYVM f q =
    Σ[ p1 ∈ inlR (f true) ≡ leftFun*-fullBool J A true (q .fst) ]
      Σ[ p2 ∈ (((g : (i₁ : Bool) (j : fst J) → A i₁ j)
                (p : (i₁ : fst (RP∞'· ℓ)) → g i₁ (f i₁ .fst) ≡ f i₁ .snd)
             → Square p1 refl
                      (push* (f true) (g true) (p true))
                      (λ i → leftFun*-fullBool J A true (q .snd .fst g p i)))) ]
        ((t : Bool)
        → Σ[ p3 ∈ ((g : (j : fst J) → A (2-elter.notI (RP∞'· ℓ) (fst J) A t) j)
                     (p : g (f (not t) .fst) ≡ f (not t) .snd)
                → Square
                    (L2-side-Bool-inl (t , 2-elter.PushTop→left-push (RP∞'· ℓ) (fst J) A (t , inl (f , g , p)) .snd))
                    p1
                    (cong (leftFun (fst J) A) (push (t , inl (f , g , p))))
                    λ i → leftFun*-fullBool J A true (q .snd .snd t .fst g p i)) ]
             ((g : (i₁ : Bool) (j₁ : fst J) → A i₁ j₁)
               (p : (i₁ : Bool) → g i₁ (f i₁ .fst) ≡ f i₁ .snd)
                → Cube (λ i j → leftFun (fst J) A (push (t , push (f , g , p) j) i))
                        (λ i j → leftFun*-fullBool J A true (q .snd .snd t .snd g p i j))
                        (λ k j → L2-side-Bool-inl (t , f t , g (2-elter.notI (RP∞'· ℓ) (fst J) A t)) k)
                        (λ j i → p2 g p i j)
                        (λ i j → p3 (g (not t)) (p (not t)) j i)
                        (L2-side-Bool-push-inr t ((f t) , (g , p t)))))

  abstract
    TYVM-b : (f : _) → TYVM (Iso.inv T f) (megaty-b f)
    fst (TYVM-b (inl x , p)) = refl
    fst (TYVM-b (inr x , p)) = refl
    fst (snd (TYVM-b (inl x , p))) g q i j =
      push* (x , p true) (g true) (q true) i
    fst (snd (snd (TYVM-b (inl x , p))) false) g q i j =
      push* (x , p true) g q (~ i)
    fst (snd (snd (TYVM-b (inl x , p))) true) g q i j =
      inlR (x , p true)
    snd (snd (snd (TYVM-b (inl x , p))) false) g q i j k =
      push* (x , p true) (g true) (q true) (~ j ∨ k)
    snd (snd (snd (TYVM-b (inl x , p))) true) g q i j k =
      push* (x , p true) (g true) (q true) (k ∧ j)
    fst (snd (TYVM-b (inr x , p))) g q i j =
      push* (fst x true , p true) (g true) (q true) i
    fst (snd (snd (TYVM-b (inr x , p))) false) g q i j =
      push* (fst x true , p true) g q (~ i)
    fst (snd (snd (TYVM-b (inr x , p))) true) g q i j =
      inlR (fst x true , p true)
    snd (snd (snd (TYVM-b (inr x , p))) false) g q = refl
    snd (snd (snd (TYVM-b (inr x , p))) true) g q = refl

    TYVM∙ : (f : _) → TYVM f (megaty-ba f)
    TYVM∙ = equivElim-lem
      (λ f → TYVM f (megaty-ba f))
      (invEquiv (isoToEquiv T))
      λ f → subst (TYVM (fst (invEquiv (isoToEquiv T)) f))
                   (sym (megaty-ba≡ f))
                   (TYVM-b f)


  L2-side-Bool : (a : _)
    → leftFun (fst J) A a ≡ leftFun*-fullBool J A true (EZ.L2-side (RP∞'· ℓ) J A a)
  L2-side-Bool (inl (t , a)) = L2-side-Bool-inl (t , a)
  L2-side-Bool (inr (inl f)) = TYVM∙ f .fst
  L2-side-Bool (inr (inr x)) = refl
  L2-side-Bool (inr (push (f , g , p) i)) = TYVM∙ f .snd .fst g p i
  L2-side-Bool (push (t , inl (f , g , p)) i) = TYVM∙ f .snd .snd t .fst g p i
  L2-side-Bool (push (t , inr x) i) j = L2-side-Bool-push-inr t x j i
  L2-side-Bool (push (t , push (f , g , p) j) i) k = TYVM∙ f .snd .snd t .snd g p k i j

mainCoh : {ℓ : Level} (I : RP∞' ℓ) (t : fst I) (J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
  → (a : _)
  → snd (leftFunExt I (fst J) A (t , a))
  ≡ leftFun*-full I J A t (EZ.L2-side I J A a)
mainCoh {ℓ = ℓ} = JRP∞' λ J A a →
    (λ k → help k (fst J) A a)
  ∙ L2-side-Bool J A a
  ∙ sym (leftFunBool≡' J A true (EZ.L2-side (RP∞'· ℓ) J A a))
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

joinR→join : ∀ {ℓ} {A : Bool → Type ℓ}
  → joinR-gen Bool A → join (A true) (A false)
joinR→join (inlR (false , a)) = inr a
joinR→join (inlR (true , a)) = inl a
joinR→join (inrR x) = inl (x true)
joinR→join (push* (false , a) b x i) = push (b true) a (~ i)
joinR→join (push* (true , a) b x i) = inl (x (~ i))

join→joinR : ∀ {ℓ} {A : Bool → Type ℓ}
  → join (A true) (A false)
  → joinR-gen Bool A
join→joinR (inl x) = inlR (true , x)
join→joinR (inr x) = inlR (false , x)
join→joinR (push a b i) =
   (push* (true , a) (CasesBool true a b) refl
  ∙ sym (push* (false , b) (CasesBool true a b) refl)) i

join-joinR-iso : ∀ {ℓ} {A : Bool → Type ℓ}
  → Iso (joinR-gen Bool A) (join (A true) (A false))
Iso.fun join-joinR-iso = joinR→join
Iso.inv join-joinR-iso = join→joinR
Iso.rightInv join-joinR-iso (inl x) = refl
Iso.rightInv join-joinR-iso (inr x) = refl
Iso.rightInv (join-joinR-iso {A = A}) (push a b i) j = help j i
  where
  help : cong (joinR→join {A = A})
               (push* (true , a) (CasesBool true a b) refl
              ∙ sym (push* (false , b) (CasesBool true a b) refl))
      ≡ push a b
  help = cong-∙ joinR→join
            (push* (true , a) (CasesBool true a b) refl)
            (sym (push* (false , b) (CasesBool true a b) refl))
       ∙ sym (lUnit (push a b))
Iso.leftInv join-joinR-iso (inlR (false , y)) = refl
Iso.leftInv join-joinR-iso (inlR (true , y)) = refl
Iso.leftInv join-joinR-iso (inrR x) = push* (true , x true) x refl
Iso.leftInv (join-joinR-iso {A = A}) (push* (false , x) b p i) j =  h x p j i
  where
  h : (x : A false) (p : b false ≡ x)
    → Square {A = joinR-gen Bool A}
             (sym (push* (true , b true) (CasesBool true (b true) x) refl
               ∙ sym (push* (false , x) (CasesBool true (b true) x) refl)))
             (push* (false , x) b p)
             refl
             (push* (true , b true) b refl)
  h = J> ((λ s → sym (push* (true , b true) (CasesBoolη b s) refl
                ∙ sym (push* (false , b false) (CasesBoolη b s) refl)))
        ◁ λ i j → compPath-filler'
                    (push* (true , b true) b refl)
                    (sym (push* (false , b false) b refl)) (~ i) (~ j))
Iso.leftInv (join-joinR-iso {A = A}) (push* (true , x) b p i) j = h x p j i
  where
  h : (x : _) (p : b true ≡ x)
    → Square {A = joinR-gen Bool A}
              (λ i → inlR (true , p (~ i))) (push* (true , x) b p )
              refl (push* (true , b true) b (λ _ → b true))
  h = J> λ i j → push* (true , b true) b refl (i ∧ j)
