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
open import Cubical.HITs.RPn.Unordered
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
         (UnordJoinR-gen (fst J) (A true) × UnordJoinR-gen (fst J) (A false))
Iso.fun (ΠR-extend→×Iso J A) = ΠR-extend→× J A
Iso.inv (ΠR-extend→×Iso J A) = ×→ΠR-extend J A
Iso.rightInv (ΠR-extend→×Iso J A) = ×→ΠR-extend→× {J = J} A
Iso.leftInv (ΠR-extend→×Iso J A) = ΠR-extend→×→ΠR-extend {J = J} A


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

-- main theorem
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
