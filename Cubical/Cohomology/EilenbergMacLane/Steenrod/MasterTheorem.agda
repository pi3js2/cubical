{-# OPTIONS --safe --lossy-unification #-}

{-
This file contiains.
-}

module Cubical.Cohomology.EilenbergMacLane.Steenrod.MasterTheorem where

open import Cubical.Cohomology.EilenbergMacLane.Base
open import Cubical.Cohomology.EilenbergMacLane.Groups.Sn
open import Cubical.Cohomology.EilenbergMacLane.CupProduct
open import Cubical.Cohomology.EilenbergMacLane.Gysin
open import Cubical.Cohomology.EilenbergMacLane.Rings.RPinf
open import Cubical.Cohomology.EilenbergMacLane.Steenrod.Base

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
open import Cubical.Homotopy.EilenbergMacLane.Order2

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
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Univalence

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.Sn hiding (S)
open import Cubical.HITs.Pushout
open import Cubical.HITs.EilenbergMacLane1
open import Cubical.HITs.Susp
open import Cubical.HITs.S1
open import Cubical.HITs.RPn
open import Cubical.HITs.RPn.Unordered
open import Cubical.HITs.RPn.JoinFubini
open import Cubical.HITs.Join
open import Cubical.HITs.SmashProduct

open import Cubical.Data.Empty as ⊥
open import Cubical.Relation.Nullary


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
open import Cubical.Algebra.CommRing.Instances.IntMod
open import Cubical.Algebra.Group.Instances.IntMod

open import Cubical.Data.Fin.Arithmetic
open import Cubical.Data.Fin.Base


open RingStr renaming (_+_ to _+r_)
open PlusBis

open Iso
-- The goal of this file is to show that, for X Y : RP∞', we have
-- S(X,S(Y,a)) = S(Y,S(X,a)).  Doing this when X and Y are both Bool
-- boils down to commutativity and associativity of ⌣ₖ.  The goal now:
-- Define S(X,S(Y,a)) and S(Y,S(X,a)) as quadruply pointed functions
-- (the type of which will turn out to be a set).

-- 
module _ {ℓ} (X Y : RP∞' ℓ) (A : fst X → fst Y → Pointed ℓ) (B : Pointed ℓ) where
  QuadpointedUnordJoin : (f : ((x : fst X) (y : fst Y) → A x y .fst) → fst B) → Type ℓ
  QuadpointedUnordJoin f = (g : (x : fst X) (y : fst Y) → A x y .fst)
    → UnordJoinR X (λ x → UnordJoinR Y λ y → g x y ≡ A x y .snd)
    → f g ≡ B .snd

SteenrodFun²Type : (X Y : RP∞' ℓ-zero) (n : fst X → fst Y → ℕ) → Type
SteenrodFun²Type X Y n =
  Σ[ f ∈ (((x : fst X) (y : fst Y) → EM ℤ/2 (n x y))
         → EM ℤ/2 (∑RP∞' X λ x → ∑RP∞' Y λ y → n x y)) ]
      QuadpointedUnordJoin X Y
        (λ x y → EM∙ ℤ/2 (n x y))
        (EM∙ ℤ/2 (∑RP∞' X λ x → ∑RP∞' Y λ y → n x y)) f

-- The two functions we want to compare are S(X,S(Y,-)):
SteenrodFun² : (X Y : RP∞' ℓ-zero) (n : fst X → fst Y → ℕ) → SteenrodFun²Type X Y n
fst (SteenrodFun² X Y n) f =
  S X (λ x → ∑RP∞' Y (n x)) λ x → S Y (n x) (f x)
snd (SteenrodFun² X Y n) g (inlR p) =
  SteenrodFun X (λ x → ∑RP∞' Y (n x)) .snd _
    (inlR (fst p , SteenrodFun Y (n (fst p)) .snd _ (snd p)))
snd (SteenrodFun² X Y n) g (inrR f) =
  SteenrodFun X (λ x → ∑RP∞' Y (n x)) .snd _
    (inrR λ x → SteenrodFun Y (n x) .snd _ (f x))
snd (SteenrodFun² X Y n) g (pushR p f r i) =
  SteenrodFun X (λ x → ∑RP∞' Y (n x)) .snd _
    (pushR (fst p , SteenrodFun Y (n (fst p)) .snd _ (snd p))
           (λ x → SteenrodFun Y (n x) .snd _ (f x))
           (cong (SteenrodFun Y (n (fst p)) .snd (λ x₂ → g (fst p) x₂)) r) i)

-- and S(Y,S(X,-)):
SteenrodFun²Flip' : (X Y : RP∞' ℓ-zero) (n : fst X → fst Y → ℕ)
  → Σ[ f ∈ (((x : fst X) (y : fst Y) → EM ℤ/2 (n x y))
         → EM ℤ/2 (∑RP∞' Y λ y → ∑RP∞' X λ x → n x y)) ]
      QuadpointedUnordJoin Y X
        (λ y x → EM∙ ℤ/2 (n x y))
        (EM∙ ℤ/2 (∑RP∞' Y λ y → ∑RP∞' X λ x → n x y))
        (λ g → f (λ x y → g y x))
fst (SteenrodFun²Flip' X Y n) f =
  S Y (λ z → ∑RP∞' X (λ x → n x z))
    λ y → S X (λ x → n x y) (λ x → f x y)
snd (SteenrodFun²Flip' X Y n) g (inlR x) =
  SteenrodFun Y (λ z → ∑RP∞' X (λ x₁ → n x₁ z)) .snd
    (λ y → SteenrodFun X (λ x₁ → n x₁ y) .fst (λ x₁ → g y x₁))
      (inlR (fst x , SteenrodFun X (λ x₁ → n x₁ (fst x)) .snd (g (fst x)) (snd x)))
snd (SteenrodFun²Flip' X Y n) g (inrR f) =
  SteenrodFun Y (λ y → ∑RP∞' X (λ x → n x y)) .snd
    (λ y → SteenrodFun X (λ x → n x y) .fst (g y))
    (inrR λ y → SteenrodFun X (λ x → n x y) .snd (g y) (f y))
snd (SteenrodFun²Flip' X Y n) g (pushR a b x i) =
  SteenrodFun Y (λ y → ∑RP∞' X (λ x → n x y)) .snd
    (λ y → SteenrodFun X (λ x₁ → n x₁ y) .fst (g y))
      (pushR (fst a , SteenrodFun X (λ x → n x (fst a)) .snd (g (fst a)) (snd a))
             (λ y → SteenrodFun X (λ x → n x y) .snd (g y) (b y))
             (cong (SteenrodFun X (λ x₁ → n x₁ (fst a)) .snd (g (fst a))) x) i)

-- Problem: These terms have different type. The type of their first
-- projections agree up to a path in ℕ.
∑RP∞'Fubini : (X Y : RP∞' ℓ-zero) (n : fst X → fst Y → ℕ)
  → (∑RP∞' Y (λ y → ∑RP∞' X (λ x → n x y)))
   ≡ (∑RP∞' X (λ x → ∑RP∞' Y (n x)))
∑RP∞'Fubini =
  RP∞'pt→Prop (λ X → isPropΠ2 λ _ _ → isSetℕ _ _)
    (RP∞'pt→Prop ((λ _ → isPropΠ λ _ → isSetℕ _ _))
      λ n → move4 (n true true) (n false true) (n true false) (n false false) _+'_
        +'-assoc
        +'-comm)

-- More problematic is their structures which are of different
-- type. Fortunately, we can use a fubini theorem to tranform
-- SteenrodFun²Flip' into something of the appropriate time.
SteenrodFun²Flip : (X Y : RP∞' ℓ-zero) (n : fst X → fst Y → ℕ) → SteenrodFun²Type X Y n
fst (SteenrodFun²Flip X Y n) f =
  subst (EM ℤ/2) (∑RP∞'Fubini X Y n)
    (SteenrodFun Y (λ z → ∑RP∞' X (λ x → n x z)) .fst
      λ y → SteenrodFun X (λ x → n x y) .fst λ x → f x y)
snd (SteenrodFun²Flip X Y n) f p =
    cong (subst (EM ℤ/2) (∑RP∞'Fubini X Y n))
      (SteenrodFun²Flip' X Y n .snd (λ y x → f x y)
        (UnordJoinFubiniFun X Y _ p))
  ∙ subst-EM∙ (∑RP∞'Fubini X Y n) .snd

-- Goal of this file: Show that SteenrodFun² ≡ SteenrodFun²Flip
-- To do this, we want to show that SteenrodFun²Type is an hSet.

-- It will suffices to examine SteenrodFun²Type when X and Y are Bool. In this case
-- We QuadpointedUnordJoin is clearly equvialent to the following type
module _ (A B C D T :  Pointed ℓ-zero)
         (f : fst A → fst B → fst C → fst D → fst T) where
  QuadpointedUnordJoinBool : Type
  QuadpointedUnordJoinBool = (a : fst A) (b : fst B) (c : fst C) (d : fst D)
      → join (join (a ≡ snd A) (b ≡ snd B)) (join (c ≡ snd C) (d ≡ snd D))
      → f a b c d ≡ pt T

Iso-ΣQuadpointedUnordJoinBool-Quadpoint : (A B C D T : Pointed ℓ-zero)
  → Iso (Σ[ f ∈ (fst A → fst B → fst C → fst D → fst T) ]
            QuadpointedUnordJoinBool A B C D T f)
         (A →∙ (B →∙ C →∙ D →∙ T ∙ ∙ ∙))
Iso-ΣQuadpointedUnordJoinBool-Quadpoint A B C D T =
  compIso
   (compIso mainIso
     (Σ-cong-iso
       (codomainIso (codomainIso (Iso-ΣBipointedJoinBool-Bipointed C D T)))
       λ f → codomainIsoDep λ a
           → codomainIsoDep λ b
           → codomainIso
             (compIso (congIso {x = f a b}
               (Iso-ΣBipointedJoinBool-Bipointed C D T))
               (pathToIso
                 (cong (fun (Iso-ΣBipointedJoinBool-Bipointed C D T) (f a b) ≡_)
                 Iso-ΣBipointedJoinBool-Bipointed∙) ))))
    (Iso-ΣBipointedJoinBool-Bipointed A B (C →∙ D →∙ T ∙ ∙))
  where
  -- abbreviations
  ty₁ = Σ[ f ∈ (fst A → fst B → fst C → fst D → fst T) ]
         QuadpointedUnordJoinBool A B C D T f

  ty₂ = Σ (fst A → fst B → Σ (fst C → fst D → fst T) (BipointedJoinBool C D T))
          (BipointedJoinBool A B
            (Σ (fst C → fst D → fst T) (BipointedJoinBool C D T)
             , (λ _ _ → snd T) , (λ _ _ _ → refl)))

  module _ (a : fst A) (b : fst B) (c : fst C) (d : fst D)
           (p : join (a ≡ snd A) (b ≡ snd B))
           (q : join (c ≡ snd C) (d ≡ snd D)) (i j k : I) where
    fill₁ : ty₁ → fst T
    fill₁ (f , g) =
      hfill (λ k → λ {(i = i0) → g a b c d (push p q k) j
                     ; (i = i1) → snd T
                     ; (j = i0) → g a b c d (inl p) i
                     ; (j = i1) → snd T})
            (inS (g a b c d (inl p) (i ∨ j))) k

    fill₂ : ty₂ → fst T
    fill₂ (f , g) =
      hfill (λ k → λ {(i = i0) → g a b p j .snd c d q (~ k)
                   ; (i = i1) → f a b .snd c d q (~ k ∨ j)
                   ; (j = i0) → f a b .snd c d q (~ k)
                   ; (j = i1) → snd T})
          (inS (snd T)) k

  ty₁→ty₂ : ty₁ → ty₂
  fst (fst (ty₁→ty₂ (f , p)) a b) c d = f a b c d
  snd (fst (ty₁→ty₂ (f , p)) a b) c d t = p a b c d (inr t)
  fst (snd (ty₁→ty₂ (f , p)) a b t i) c d = p a b c d (inl t) i
  snd (snd (ty₁→ty₂ (f , p)) a b t i) c d q j = fill₁ a b c d t q i j i1 (f , p)

  ty₂→ty₁ : ty₂ → ty₁
  fst (ty₂→ty₁ (f , p)) a b c d = f a b .fst c d
  snd (ty₂→ty₁ (f , p)) a b c d (inl x) i = p a b x i .fst c d
  snd (ty₂→ty₁ (f , p)) a b c d (inr x) = f a b .snd c d x
  snd (ty₂→ty₁ (f , g)) a b c d (push p q i) j = fill₂ a b c d p q i j i1 (f , g)

  mainIso : Iso ty₁ ty₂
  Iso.fun mainIso = ty₁→ty₂
  Iso.inv mainIso = ty₂→ty₁
  fst (Iso.rightInv mainIso (f , p) i) = fst (ty₁→ty₂ (ty₂→ty₁ (f , p)))
  fst (snd (Iso.rightInv mainIso (f , p) i) a b t j) = p a b t j .fst
  snd (snd (Iso.rightInv mainIso (f , g) i) a b p j) c d q k =
    hcomp (λ r → λ {(i = i0) → fill₁ a b c d p q j k r (ty₂→ty₁ (f , g))
                   ; (i = i1) → snd (g a b p j) c d q k
                   ; (j = i0) → cube₂ r i k
                   ; (j = i1) → snd T
                   ; (k = i0) → g a b p j .fst c d
                   ; (k = i1) → snd T})
           (cube₃ k j i)
    where
    cube₁ : (k i r : I) → fst T
    cube₁ k i r =
      hfill (λ r → λ {(i = i0) → g a b p k .snd c d q (~ r)
                     ; (i = i1) → f a b .snd c d q (~ r ∨ k)
                     ; (k = i0) → f a b .snd c d q (~ r)
                     ; (k = i1) → snd T})
            (inS (snd T))
            r

    cube₂ : (r i k : I) → fst T
    cube₂ r i k =
      hcomp (λ w → λ {(r = i0) → cube₁ k i w
                     ; (r = i1) → f a b .snd c d q (~ w ∨ k)
                     ; (i = i0) → fill₂ a b c d p q r k w
                                    (f , λ a b p → g a b p)
                     ; (i = i1) → f a b .snd c d q (~ w ∨ k)
                     ; (k = i0) → f a b .snd c d q (~ w)
                     ; (k = i1) → snd T})
                (snd T)

    cube₃ : (k j i : I) → fst T
    cube₃ k j i =
      hcomp (λ r → λ {(i = i0) → g a b p (k ∨ j) .snd c d q (~ r)
                     ; (i = i1) → snd (g a b p j) c d q (~ r ∨ k)
                     ; (j = i1) → snd T
                     ; (k = i0) → g a b p j .snd c d q (~ r)
                     ; (k = i1) → snd T})
            (snd T)
  fst (Iso.leftInv mainIso (f , g) i) = f
  snd (Iso.leftInv mainIso (f , g) i) a b c d (inl p) = g a b c d (inl p)
  snd (Iso.leftInv mainIso (f , g) i) a b c d (inr p) = g a b c d (inr p)
  snd (Iso.leftInv mainIso (f , g) i) a b c d (push p q j) k =
    hcomp (λ r → λ {(i = i0) → fill₂ a b c d p q j k r
                                   (ty₁→ty₂ (f , g))
                   ; (i = i1) → cube₃ r j k
                   ; (j = i0) → cube₂ r k i
                   ; (j = i1) → g a b c d (inr q) (~ r ∨ k)
                   ; (k = i0) → g a b c d (inr q) (~ r)
                   ; (k = i1) → pt T})
           (snd T)
    where
    cube₁ : (i j k : I) → fst T
    cube₁ i j k =
      doubleWhiskFiller {A = λ i → g a b c d (inr q) (~ i) ≡ pt T} refl
          (λ i j → g a b c d (inr q) (~ i ∨ j))
          (λ j k → g a b c d (push p q (~ j)) k)
          k i j

    cube₂ : (r k i : I) → fst T
    cube₂ r k i =
      hcomp (λ j → λ {(r = i0) → pt T
                     ; (r = i1) → g a b c d (push p q (~ j ∧ i)) k
                     ; (k = i0) → g a b c d (push p q (j ∨ i)) (~ r)
                     ; (k = i1) → pt T
                     ; (i = i0) → fill₁ a b c d p q k (~ r) j (f , g)
                     ; (i = i1) → cube₁ r k j})
            (g a b c d (push p q i) (k ∨ ~ r))

    cube₃ : (r j k : I) → fst T
    cube₃ r j k =
      hcomp (λ w → λ {(r = i0) → pt T
                   ; (r = i1) → g a b c d (push p q (~ w ∨ j)) k
                   ; (j = i1) → g a b c d (inr q) (~ r ∨ k)
                   ; (k = i0) → g a b c d (inr q) (~ r)
                   ; (k = i1) → pt T})
           (g a b c d (inr q) (~ r ∨ k))

  Iso-ΣBipointedJoinBool-Bipointed∙ :
    Iso.fun (Iso-ΣBipointedJoinBool-Bipointed C D T)
            ((λ c d → pt T) , (λ _ _ _ → refl))
    ≡ (C →∙ (D →∙ T ∙) ∙) .snd
  Iso-ΣBipointedJoinBool-Bipointed∙ =
    cong (Iso.fun SmashAdjIso)
       (ΣPathP ((funExt (
         λ { (inl x) → refl
            ; (inr x) → refl
            ; (push (inl x) i) → refl
            ; (push (inr x) i) → refl
            ; (push (push a i₁) i) → refl})) , refl))
      ∙ SmashAdj≃∙ .snd

-- Using the above, we we get the same result for SteenrodFun²Type
SteenrodFun²TypeBool : (n : Bool → Bool → ℕ)
  → Iso (SteenrodFun²Type (RP∞'∙ ℓ-zero) (RP∞'∙ ℓ-zero) n)
        (EM∙ ℤ/2 (n true true)
     →∙ (EM∙ ℤ/2 (n true false)
     →∙ EM∙ ℤ/2 (n false true)
     →∙ EM∙ ℤ/2 (n false false)
     →∙ EM∙ ℤ/2 ((n true true +' n true false)
               +' (n false true +' n false false)) ∙ ∙ ∙))
SteenrodFun²TypeBool n =
   (compIso
    (Σ-cong-iso
     (invIso (compIso (invIso curryIso)
     (compIso (invIso curryIso)
     (compIso (invIso curryIso)
     (domIso (invIso help))))))
      λ f → invIso (compIso
        (compIso (invIso curryIso)
          (compIso (invIso curryIso)
            (compIso (invIso curryIso)
              (invIso
                (ΠIso idIso
                  λ {(((x , y) , z) , w)
               → domIso (compIso join-UnordJoinR-iso
                   (Iso→joinIso
                     join-UnordJoinR-iso
                     join-UnordJoinR-iso))})))))
          (ΠIso (invIso help) λ _ → idIso)))
    (Iso-ΣQuadpointedUnordJoinBool-Quadpoint (EM∙ ℤ/2 (n true true))
           (EM∙ ℤ/2 (n true false))
           (EM∙ ℤ/2 (n false true))
           (EM∙ ℤ/2 (n false false))
     (EM∙ ℤ/2 ((n true true +' n true false)
           +' (n false true +' n false false)))))
  where
  help : Iso ((x y : fst (RP∞'∙ ℓ-zero)) → EM∙ ℤ/2 (n x y) .fst)
             (((EM ℤ/2 (n true true)
              × EM ℤ/2 (n true false))
              × EM ℤ/2 (n false true))
              × EM ℤ/2 (n false false))
  help = compIso (compIso ΠBool×Iso
                  (prodIso ΠBool×Iso ΠBool×Iso))
                  (invIso Σ-assoc-Iso)

-- Corollary 1: SteenrodFun²Type is a set
isSetSteenrodFun²Type : (X Y : RP∞' ℓ-zero) (n : fst X → fst Y → ℕ)
  → isSet (SteenrodFun²Type X Y n)
isSetSteenrodFun²Type =
  RP∞'pt→Prop (λ Y → isPropΠ2 (λ _ _ → isPropIsSet))
    (RP∞'pt→Prop (λ Y → isPropΠ (λ _ → isPropIsSet))
      λ n → isOfHLevelRetractFromIso 2
              (SteenrodFun²TypeBool n)
              (isConnected→∙ (suc (n true true)) 1
                (isConnectedEM (n true true))
                (isConnected→∙ (suc (n true false)) (n true true + 1)
                  (isConnectedEM (n true false))
                  (isConnected→∙ (suc (n false true))
                    ((n true false) + (n true true + 1))
                    (isConnectedEM (n false true))
                    (isConnected→∙
                      (suc (n false false))
                      (n false true + (n true false + (n true true + 1)))
                      (isConnectedEM (n false false))
                      (subst (λ k → isOfHLevel (suc k) (EM ℤ/2 (N' n)))
                        (lem n)
                        (hLevelEM ℤ/2 (N' n))))))))
  where
  N' : (n : Bool → Bool → ℕ) → ℕ
  N' n = ((n true true +' n true false) +' (n false true +' n false false))

  lem : (n : _) → suc (N' n)
                 ≡ (n false false + (n false true + (n true false + (n true true + 1))))
  lem n =  cong suc ((cong₂ _+'_ (+'≡+ (n true true) (n true false))
                                (+'≡+ (n false true) (n false false))
                 ∙ +'≡+ _ _)
                 ∙ +-assoc (n true true + n true false ) (n false true) (n false false))
         ∙ cong (_+ n false false)
              (cong (_+ n false true)
                ((λ i → +-comm (+-comm 1 (n true true) i) (n true false) i))
              ∙ +-comm _ (n false true))
         ∙ +-comm _ (n false false)

-- Corollary 2: to show that two elements (f , fs) and (g , gs) of
-- SteenrodFun²Type are equal, it suffices to show that f = g.
SteenrodFun²Type≡ : (X Y : RP∞' ℓ-zero) (n : fst X → fst Y → ℕ)
  (f g : SteenrodFun²Type X Y n)
  → ((t : _) → f .fst t ≡ g .fst t)
  → f ≡ g
SteenrodFun²Type≡ =
  RP∞'pt→Prop (λ X → isPropΠ5 λ Y n _ _ _ → isSetSteenrodFun²Type X Y n _ _)
    (RP∞'pt→Prop (λ Y → isPropΠ4 λ n _ _ _
                       → isSetSteenrodFun²Type (RP∞'∙ ℓ-zero) Y n _ _)
     λ n f g p
   → sym (Iso.leftInv (SteenrodFun²TypeBool n) f)
   ∙∙ cong (inv (SteenrodFun²TypeBool n))
       (main n f g p)
   ∙∙ Iso.leftInv (SteenrodFun²TypeBool n) g)
  where
  module _ (n : Bool → Bool → ℕ)
           (f g : SteenrodFun²Type (RP∞'∙ ℓ-zero) (RP∞'∙ ℓ-zero) n)
         (p : (t : (x y : fst (RP∞'∙ ℓ-zero)) → EM ℤ/2 (n x y))
        →  f .fst t ≡ g .fst t) where
    p' : (x : _) (y : _) (z : _) (w : _)
      → fun (SteenrodFun²TypeBool n) f .fst x .fst y .fst z .fst w
      ≡ fun (SteenrodFun²TypeBool n) g .fst x .fst y .fst z .fst w
    p' x y z w = p (CasesBool true
                       (CasesBool true x y)
                       (CasesBool true z w))

    module _ {ℓ ℓ' ℓT} {C : Pointed ℓ} {D : Pointed ℓ'} {T : Pointed ℓT}
              (hom : isHomogeneous T) where
      isHomogeneous→∙₂ : isHomogeneous (C →∙ (D →∙ T ∙) ∙) 
      isHomogeneous→∙₂ = isHomogeneous→∙ (isHomogeneous→∙ hom)

      module _ {ℓ'' : Level} {B : Pointed ℓ''} where
        isHomogeneous→∙₃ : isHomogeneous (B →∙ (C →∙ (D →∙ T ∙) ∙) ∙) 
        isHomogeneous→∙₃ = isHomogeneous→∙ isHomogeneous→∙₂

        isHomogeneous→∙₄ : ∀ {ℓ'''} {A : Pointed ℓ'''}
          → isHomogeneous (A →∙ (B →∙ (C →∙ (D →∙ T ∙) ∙) ∙) ∙)
        isHomogeneous→∙₄ = isHomogeneous→∙ isHomogeneous→∙₃

    N = (n true true +' n true false) +' (n false true +' n false false)

    main₄ : (x : EM ℤ/2 (n true true)) (y : EM ℤ/2 (n true false))
         (z : EM ℤ/2 (n false true))
       → fun (SteenrodFun²TypeBool n) f .fst x .fst y .fst z
       ≡ fun (SteenrodFun²TypeBool n) g .fst x .fst y .fst z
    main₄ x y z = →∙Homogeneous≡ (isHomogeneousEM N) (funExt (p' x y z))

    main₃ : (x : EM ℤ/2 (n true true)) (y : EM ℤ/2 (n true false))
       → fun (SteenrodFun²TypeBool n) f .fst x .fst y
       ≡ fun (SteenrodFun²TypeBool n) g .fst x .fst y
    main₃ x y = →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneousEM N))
               (funExt (main₄ x y))

    main₂ : (x : EM ℤ/2 (n true true))
      → fun (SteenrodFun²TypeBool n) f .fst x
       ≡ fun (SteenrodFun²TypeBool n) g .fst x
    main₂ x = →∙Homogeneous≡ (isHomogeneous→∙₂ (isHomogeneousEM N))
             (funExt (main₃ x))

    main : fun (SteenrodFun²TypeBool n) f ≡ fun (SteenrodFun²TypeBool n) g
    main = →∙Homogeneous≡ (isHomogeneous→∙₃ (isHomogeneousEM N))
             (funExt main₂)

SteenrodFun²≡SteenrodFun²Flip : (X Y : RP∞' ℓ-zero) (n : fst X → fst Y → ℕ)
  → SteenrodFun² X Y n ≡ SteenrodFun²Flip X Y n
SteenrodFun²≡SteenrodFun²Flip =
  RP∞'pt→Prop (λ _ → isPropΠ2 λ Y n → isSetSteenrodFun²Type _ Y n _ _)
  (RP∞'pt→Prop (λ Y → isPropΠ λ n → isSetSteenrodFun²Type _ Y n _ _)
    λ n → SteenrodFun²Type≡ _ _ _ _ _
      λ f → SteenrodFunBool (λ x → ∑RP∞' (RP∞'∙ ℓ-zero) (n x))
                    (λ x → SteenrodFun (RP∞'∙ ℓ-zero) (n x) .fst (f x))
           ∙ cong₂ ⌣ₖ₂ (SteenrodFunBool (n true) (f true))
                      (SteenrodFunBool (n false) (f false))
           ∙ help (EM ℤ/2) (λ n m x y → ⌣ₖ₂ {n = n} {m = m} x y)
               ⌣ₖ-commℤ/2 assoc⌣ₖ
               (n true true) (n true false)
               (n false true) (n false false)
               (f true true) (f true false)
               (f false true) (f false false)
               (∑RP∞'Fubini (RP∞'∙ ℓ-zero) (RP∞'∙ ℓ-zero) n)
           ∙ cong (subst (EM ℤ/2) (∑RP∞'Fubini (RP∞'∙ ℓ-zero) (RP∞'∙ ℓ-zero) n))
               (sym (SteenrodFunBool (λ z → ∑RP∞' (RP∞'∙ ℓ-zero) (λ x → n x z))
                         (λ y → SteenrodFun (RP∞'∙ ℓ-zero) (λ x → n x y) .fst (λ x → f x y))
               ∙ cong₂ ⌣ₖ₂ (SteenrodFunBool (λ x → n x true) (λ x → f x true))
                               (SteenrodFunBool (λ x → n x false) (λ x → f x false)))))
  where
  help : ∀ {ℓ} (A : ℕ → Type ℓ) (compA : (n m : ℕ) (x : A n) (y : A m) → A (n +' m))
    → (⌣comm : (n m : ℕ) (x : A n) (y : A m)
      → compA n m x y
       ≡ subst A (+'-comm m n) (compA m n y x))
    → (⌣assoc : (n m l : ℕ) (x : A n) (y : A m) (z : A l)
      → compA (n +' m) l (compA n m x y) z
       ≡ subst A (+'-assoc n m l)
           (compA n (m +' l) x (compA m l y z)))
    → (n m k l : ℕ) (x : A n) (y : A m) (z : A k) (w : A l)
    → (p : ((n +' k) +' (m +' l)) ≡ ((n +' m) +' (k +' l)))
    → compA (n +' m) (k +' l) (compA n m x y) (compA k l z w)
     ≡ subst A p (compA (n +' k) (m +' l) (compA n k x z) (compA m l y w))
  help A compA ⌣comm ⌣assoc n m k l x y z w p =
      (sym (transportRefl _)
    ∙ (λ i → subst A (isSetℕ _ _ refl (((sym (+'-assoc n m (k +' l))) ∙ p5 ∙ p4) ∙ p) i)
               (compA (n +' m) (k +' l) (compA n m x y) (compA k l z w))))
    ∙ substComposite A ((sym (+'-assoc n m (k +' l)) ∙ p5 ∙ p4)) p _
    ∙ cong (subst A p)
        ((substComposite A (sym (+'-assoc n m (k +' l))) (p5 ∙ p4) _
        ∙ cong (subst A (p5 ∙ p4))
           (cong (subst A (sym (+'-assoc n m (k +' l))))
                 (⌣assoc _ _ _ x y (compA k l z w))
         ∙ subst⁻Subst A (+'-assoc n m (k +' l)) _))
        ∙ substComposite A (cong (_+'_ n) ((p1 ∙ p2) ∙ p3)) p4
           (compA n (m +' (k +' l)) x (compA m (k +' l) y (compA k l z w)))
        ∙ cong (subst A (+'-assoc n k (m +' l)))
          (sym (substLems _ _ ((p1 ∙ p2) ∙ p3) _ .snd
                 x (compA m (k +' l) y (compA k l z w)))
         ∙ cong (compA n (k +' (m +' l)) x)
            (substComposite A (p1 ∙ p2) p3 (compA m (k +' l) y (compA k l z w))
           ∙ cong (subst A p3)
              ((substComposite A p1 p2 (compA m (k +' l) y (compA k l z w))
              ∙ cong (subst A (cong (_+' l) (+'-comm m k)))
                  (sym (⌣assoc m k l y z w)))
              ∙ sym (substLems _ _ (+'-comm m k) _ .fst (compA m k y z) w)
              ∙ cong (λ z → compA (k +' m) l z w)
                 (sym (⌣comm k m z y)))
            ∙ cong (subst A p3)
              (⌣assoc _ _ _ z y w)
           ∙ subst⁻Subst A (+'-assoc k m l) _))
        ∙ sym (⌣assoc _ _ _ x z (compA m l y w)))
    where
    p1 = +'-assoc m k l
    p2 = cong (_+' l) (+'-comm m k)
    p3 = sym (+'-assoc k m l)
    p4 = +'-assoc n k (m +' l)
    p5 = cong (n +'_) ((p1 ∙ p2) ∙ p3)

    substLems : (n n' : ℕ) (p : n ≡ n') (m : ℕ)
      → ((x : A n) (y : A m)
        → compA n' m (subst A p x) y ≡ subst A (cong (_+' m) p) (compA n m x y))
       × ((x : A m) (y : A n)
        → compA m n' x (subst A p y) ≡ subst A (cong (m +'_) p) (compA m n x y))
    substLems n = J> λ m
      → (λ x y → cong (λ x → compA n m x y) (transportRefl x)
                 ∙ sym (transportRefl _))
       , ((λ x y → cong (λ y → compA m n x y) (transportRefl y)
                 ∙ sym (transportRefl _)))

S-MasterTheorem : (X Y : RP∞' ℓ-zero) (n : fst X → fst Y → ℕ)
  → (f : (x : fst X) (y : fst Y) → EM ℤ/2 (n x y))
  → S X (λ x → ∑RP∞' Y (n x)) (λ x → S Y (n x) (f x))
   ≡ subst (EM ℤ/2) (∑RP∞'Fubini X Y n)
       (S Y (λ y → ∑RP∞' X (λ x → n x y))
         (λ y → S X (λ x → n x y) (λ x → f x y)))
S-MasterTheorem X Y n f i = SteenrodFun²≡SteenrodFun²Flip X Y n i .fst f


S-CartanPath : (X : RP∞' ℓ-zero) (n n' : fst X → ℕ)
  → (∑RP∞' X n +' ∑RP∞' X n') ≡ ∑RP∞' X λ x → n x +' n' x
S-CartanPath = RP∞'pt→Prop (λ _ → isPropΠ2 λ _ _ → isSetℕ _ _)
  λ n n' → +'-assoc (n true +' n false) (n' true) (n' false)
          ∙ cong (_+' n' false) (sym (+'-assoc (n true) (n false) (n' true))
                              ∙ cong (n true +'_) (+'-comm (n false) (n' true))
                              ∙ +'-assoc (n true) (n' true) (n false))
          ∙ sym (+'-assoc (n true +' n' true) (n false) (n' false))

S-Cartan : (X : RP∞' ℓ-zero) (n n' : fst X → ℕ)
  (f : (x : fst X) → EM ℤ/2 (n x)) (g : (x : fst X) → EM ℤ/2 (n' x))
  → S X (λ x → n x +' n' x) (λ x → ⌣ₖ₂ (f x) (g x))
  ≡ subst (EM ℤ/2) (S-CartanPath X n n') (⌣ₖ₂ (S X n f) (S X n' g)) 
S-Cartan X n n' f g =
  cong (S X (λ x → n x +' n' x))
    (funExt (λ x → sym (SteenrodFunBool (n+n' x) (CasesBool true (f x) (g x)))))
  ∙ (S-MasterTheorem X (RP∞'∙ ℓ-zero) n+n' λ x → CasesBool true (f x) (g x))
  ∙ cong (subst (EM ℤ/2) (∑RP∞'Fubini X (RP∞'∙ ℓ-zero) n+n'))
         (SteenrodFunBool (λ y → ∑RP∞' X (λ x → n+n' x y))
           (λ y → S X (λ z → n+n' z y) λ x
             → CasesBool {A = λ y → EM ℤ/2 (n+n' x y)} true (f x) (g x) y)
        ∙ refl)
    ∙ λ i → subst (EM ℤ/2) (isSetℕ _ _
                             (∑RP∞'Fubini X (RP∞'∙ ℓ-zero) n+n')
                             (S-CartanPath X n n') i)
               (⌣ₖ₂ (S X n f) (S X n' g))
  where
  n+n' : fst X → Bool → ℕ
  n+n' x false = n' x
  n+n' x true = n x
