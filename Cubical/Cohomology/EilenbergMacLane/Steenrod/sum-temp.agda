{-# OPTIONS --safe --lossy-unification #-}

{-
This file contiains.
-}

module Cubical.Cohomology.EilenbergMacLane.Steenrod.sum-temp where

open import Cubical.Cohomology.EilenbergMacLane.Base
open import Cubical.Cohomology.EilenbergMacLane.Groups.Sn
open import Cubical.Cohomology.EilenbergMacLane.CupProduct
open import Cubical.Cohomology.EilenbergMacLane.Gysin
open import Cubical.Cohomology.EilenbergMacLane.Rings.RPinf

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

lastˣ : ∀ {ℓ} (A : ℕ → Type ℓ) (n : ℕ) → A ˣ n → A n
lastˣ A zero x = x
lastˣ A (suc n) x = snd x

projˣ : ∀ {ℓ} (A : ℕ → Type ℓ) (n m : ℕ) (p : m ≤ n) → A ˣ n → A m
projˣ A n m (zero , p) x = subst A (sym p) (lastˣ A n x)
projˣ A zero m (suc diff , p) x = ⊥.rec (snotz p)
projˣ A (suc n) m (suc diff , p) (x , y) = projˣ A n m (diff , cong predℕ p) x

projTot :  ∀ {ℓ} (A : ℕ → Pointed ℓ) (n m : ℕ) → (fst ∘ A) ˣ n → (fst ∘ A) m
projTot A n m with (m Cubical.Data.Nat.Order.≟ n)
... | lt x = projˣ (fst ∘ A) n m (<-weaken x) 
... | Trichotomy.eq x = projˣ (fst ∘ A) n m (0 , x) 
... | gt x = λ x → A m .snd

projTot0 : ∀ {ℓ} (A : ℕ → Pointed ℓ) (n m : ℕ) (p : n < m) (x : (fst ∘ A) ˣ n)
  → projTot A n m x ≡ snd (A m)
projTot0 A n m p x with (m Cubical.Data.Nat.Order.≟ n)
... | lt q = ⊥.rec (¬m<m (<-trans q p))
... | Trichotomy.eq x₁ = ⊥.rec (¬m<m (subst (_< m) (sym x₁) p))
... | gt x₁ = refl

_ˣ̂_ : ∀ {ℓ} (A : ℕ → Pointed ℓ) (n : ℕ) → Type ℓ
A ˣ̂ n = Σ[ A' ∈ ((n : ℕ) → A n .fst) ] ((k : ℕ) → A' (suc k + n) ≡ snd (A (suc (k + n))))

-- Πℕ-pick-fsts₁ : ∀ {ℓ} (A : ℕ → Type ℓ) (m : ℕ) → ((n : ℕ) → A n) → (A ˣ m)
-- Πℕ-pick-fsts₁ A zero f = f zero
-- Πℕ-pick-fsts₁ A (suc m) f = (Πℕ-pick-fsts₁ A m f) , (f (suc m))


-- projˣ-Πℕ-pick-fsts₁ : ∀ {ℓ} (A : ℕ → Type ℓ) (m n : ℕ) (p : n ≤ m) (f : (n : ℕ) → A n)
--   → projˣ A m n p (Πℕ-pick-fsts₁ A m f) ≡ f n
-- projˣ-Πℕ-pick-fsts₁ A zero n (zero , p) f = fromPathP (λ i → f (p (~ i)))
-- projˣ-Πℕ-pick-fsts₁ A zero n (suc diff , p) f = ⊥.rec (snotz p)
-- projˣ-Πℕ-pick-fsts₁ A (suc m) n (zero , p) f = fromPathP (λ i → f (p (~ i)))
-- projˣ-Πℕ-pick-fsts₁ A (suc m) n (suc diff , p) f = projˣ-Πℕ-pick-fsts₁ A m n (diff , cong predℕ p) f

-- Πℕ-pick-fsts : ∀ {ℓ} (A : ℕ → Type ℓ) (m : ℕ) → ((n : ℕ) → A n) → (A ˣ m) × ((k : ℕ) → A (suc k + m))
-- Πℕ-pick-fsts A m f = Πℕ-pick-fsts₁ A m f , (λ k → f (suc k + m))

open import Cubical.Data.FinData.DepFinVec
open import Cubical.Data.Vec.DepVec
open import Cubical.Induction.WellFounded

module _ {ℓ} {A : Type ℓ} (f : (n : ℕ) → A) (plusA : A → A → A) where
  sum-helper : (n : ℕ) → A
  sum-helper zero = f zero
  sum-helper (suc n) = plusA (sum-helper n) (f (suc n))

module _ {ℓ} {A : Type ℓ} (m : ℕ) (f : (n : ℕ) → n ≤ m → A) (plusA : A → A → A) where
  sum-helper≤ : (n : ℕ) → n ≤ m  → A
  sum-helper≤ zero p = f zero p
  sum-helper≤ (suc n) p = plusA (sum-helper≤ n (≤-trans (1 , refl) p)) (f (suc n) p)

  sum≤ : A
  sum≤ = sum-helper≤ m (0 , refl)

sum-helper≤0 : ∀ {ℓ} {A : Type ℓ} (m : ℕ) (plusA : A → A → A)
  (0A : A)
  (rid : plusA 0A 0A ≡ 0A)
  (n : ℕ) (p : n ≤ m)
  → sum-helper≤ m (λ _ _ → 0A) plusA n p ≡ 0A
sum-helper≤0 m plusA 0A rid zero p = refl
sum-helper≤0 m plusA 0A rid (suc n) p =
  cong₂ plusA (sum-helper≤0 m plusA 0A rid n _) refl ∙ rid

sum-helper<-eq : ∀ {ℓ} {A : Type ℓ} (m : ℕ) (f g : (n : ℕ) → n ≤ m → A) (plusA : A → A → A)
  → ((t : ℕ) (q : t < m) → f t (<-weaken q) ≡ g t (<-weaken q))
  → (k : ℕ) (p : k < m) (q s : _)
  → sum-helper≤ m f plusA k q
   ≡ sum-helper≤ m g plusA k s
sum-helper<-eq m f g plusA indfg zero p q s =
  sym (cong (f zero) (Cubical.Data.Nat.Order.isProp≤ _ _))
  ∙∙ indfg zero p
  ∙∙ cong (g zero) (Cubical.Data.Nat.Order.isProp≤ _ _)
sum-helper<-eq m f g plusA indfg (suc k) p q s =
  cong₂ plusA (sum-helper<-eq m f g plusA indfg k (≤-trans (1 , refl) p) _ _)
              (sym (cong (f (suc k)) (Cubical.Data.Nat.Order.isProp≤ _ _))
  ∙∙ indfg (suc k) p
  ∙∙ cong (g (suc k)) (Cubical.Data.Nat.Order.isProp≤ _ _))

finFun↓ : ∀ {ℓ} {A : Type ℓ} (m : ℕ) (f : (n : ℕ) → n ≤ m → A) (0A : A)
  → (n₁ : ℕ) → n₁ ≤ suc m → A 
finFun↓ m f 0A n (zero , p) = 0A
finFun↓ m f 0A n (suc diff , p) = f n (diff , cong predℕ p)

finFun↓≡ : ∀ {ℓ} {A : Type ℓ} (m : ℕ) (f : (n : ℕ) → n ≤ m → A) (0A : A)
  (n  : ℕ) (p : n ≤ m)
  → finFun↓ m f 0A n (≤-trans p (1 , refl)) ≡ f n p
finFun↓≡ m f 0A n (diff , p) = cong (finFun↓ m f 0A n)
  (Cubical.Data.Nat.Order.isProp≤ (≤-trans (diff , p) (1 , refl))
    (suc diff , cong suc p))

module _ {ℓ} {A B C : Type ℓ} (m : ℕ) (f : (n : ℕ) → n ≤ m → A) (0A : A)
  (l : (b : B) (a : A) → C)
  (b : B)
  where
  finFun↓Multₗ : (0C : C) (l0 : l b 0A ≡ 0C) (n : ℕ) (p : n ≤ suc m)
    → l b (finFun↓ m f 0A n p) ≡ finFun↓ m (λ n p → l b (f n p)) 0C n p
  finFun↓Multₗ 0C l0 n (zero , k) = l0
  finFun↓Multₗ 0C l0 n (suc dif , k) = refl

module _ {ℓ} {A B C : Type ℓ} (m : ℕ) (f : (n : ℕ) → n ≤ m → A) (0A : A)
  (plusA : A → A → A)
  (plusC : C → C → C)
  (l : (b : B) (a : A) → C)
  (l-distr : (b : B) (a1 a2 : A) → plusC (l b a1) (l b a2) ≡ l b (plusA a1 a2)) 
  (b : B)
  where

  distrL-sum-helper≤ : (n : ℕ) (r : n ≤ m)
    → sum-helper≤ (suc m) (λ n p → l b (finFun↓ m f 0A n p)) plusC n (≤-trans r (1 , refl))
    ≡  l b (sum-helper≤ m f plusA n r)
  distrL-sum-helper≤ zero r = cong (l b) (finFun↓≡ m f 0A zero r)
  distrL-sum-helper≤ (suc n) r =
    cong₂ plusC
      (cong (sum-helper≤ (suc m) (λ n₁ p → l b (finFun↓ m f 0A n₁ p)) plusC n)
            (Cubical.Data.Nat.Order.isProp≤ _ _)
          ∙ distrL-sum-helper≤ n (≤-trans (1 , refl) r))
          (cong (l b) (finFun↓≡ m f 0A (suc n) r))
    ∙ l-distr b _ _

⌣ₖ₂ : {n m : ℕ} → EM ℤ/2 n → EM ℤ/2 m → EM ℤ/2 (n +' m)
⌣ₖ₂ = _⌣ₖ_ {G'' = ℤ/2Ring}

⌣ₖ₂' : (n m : ℕ) → EM ℤ/2 n → EM ℤ/2 m → EM ℤ/2 (n + m)
⌣ₖ₂' n m x y = subst (EM ℤ/2) (+'≡+ n m) (⌣ₖ₂ {n = n} {m} x y)

⌣ₖ₂'-0ₖ : (n m : ℕ) (x : EM ℤ/2 n) → ⌣ₖ₂' n m x (0ₖ m) ≡ 0ₖ (n + m)
⌣ₖ₂'-0ₖ n m x = cong (subst (EM ℤ/2) (+'≡+ n m)) (⌣ₖ-0ₖ n m x)
              ∙ subst-EM-0ₖ (+'≡+ n m)

0ₖ-⌣ₖ₂' : (n m : ℕ) (y : EM ℤ/2 m) → ⌣ₖ₂' n m (0ₖ n) y ≡ 0ₖ (n + m)
0ₖ-⌣ₖ₂' n m y = cong (subst (EM ℤ/2) (+'≡+ n m)) (0ₖ-⌣ₖ n m y)
              ∙ subst-EM-0ₖ (+'≡+ n m)

substComp⌣ₖ : ∀ {ℓ} {R : Ring ℓ} (n m n' : ℕ) (p : n ≡ n') (m' : ℕ) (q : m ≡ m')
  (r : (n +' m) ≡ (n' +' m'))
  (x : EM (Ring→AbGroup R) n) (y : EM (Ring→AbGroup R) m)
  → _⌣ₖ_ {G'' = R} {n = n'} {m'}
          (subst (EM (Ring→AbGroup R)) p x)
          ((subst (EM (Ring→AbGroup R)) q y))
  ≡ subst (EM (Ring→AbGroup R)) r (_⌣ₖ_ {G'' = R} {n = n} {m} x y)
substComp⌣ₖ {R = R} n m = J> (J> λ r x y
  → cong₂ (_⌣ₖ_ {G'' = R} {n = n} {m}) (transportRefl x) (transportRefl y)
  ∙ sym (transportRefl _)
  ∙ cong (λ p → subst (EM (Ring→AbGroup R)) p (_⌣ₖ_ {G'' = R} {n = n} {m} x y))
         (isSetℕ _ _ refl r))

distrL⌣ₖ₂' : (n m : ℕ) (x : EM ℤ/2 n) (y z : EM ℤ/2 m)
  → ⌣ₖ₂' n m x (y +ₖ z) ≡ (⌣ₖ₂' n m x y) +ₖ (⌣ₖ₂' n m x z) 
distrL⌣ₖ₂' n m x y z =
  cong (subst (EM ℤ/2) (+'≡+ n m)) (distrL⌣ₖ n m x y z)
  ∙ λ i → transp (λ j → EM ℤ/2 (+'≡+ n m (i ∨ j))) i
            (transp (λ j → EM ℤ/2 (+'≡+ n m (i ∧ j))) (~ i) (⌣ₖ₂ x y)
          +ₖ transp (λ j → EM ℤ/2 (+'≡+ n m (i ∧ j))) (~ i) (⌣ₖ₂ x z))

distrR⌣ₖ₂' : (n m : ℕ) (x y : EM ℤ/2 n) (z : EM ℤ/2 m)
  → ⌣ₖ₂' n m (x +ₖ y) z ≡ (⌣ₖ₂' n m x z) +ₖ (⌣ₖ₂' n m y z) 
distrR⌣ₖ₂' n m x y z =
  cong (subst (EM ℤ/2) (+'≡+ n m)) (distrR⌣ₖ n m x y z)
  ∙ λ i → transp (λ j → EM ℤ/2 (+'≡+ n m (i ∨ j))) i
            (transp (λ j → EM ℤ/2 (+'≡+ n m (i ∧ j))) (~ i) (⌣ₖ₂ x z)
          +ₖ transp (λ j → EM ℤ/2 (+'≡+ n m (i ∧ j))) (~ i) (⌣ₖ₂ y z))

comm⌣ₖ₂' : (n m : ℕ) (x : EM ℤ/2 n) (y : EM ℤ/2 m)
  → PathP (λ i → EM ℤ/2 (+-comm n m i)) (⌣ₖ₂' n m x y) (⌣ₖ₂' m n y x)
comm⌣ₖ₂' n m x y = cong (subst (EM ℤ/2) (+'≡+ n m))
  (⌣ₖ-commℤ/2 n m x y)
  ◁ symP (toPathP (sym (substComposite (EM ℤ/2) (+'≡+ m n) (sym (+-comm n m)) (⌣ₖ₂ {n = m} {n} y x))
    ∙ cong (λ p → subst (EM ℤ/2) p (⌣ₖ₂ {n = m} {n} y x)) (isSetℕ _ _ _ _)
    ∙ substComposite (EM ℤ/2) (+'-comm m n) (+'≡+ n m) (⌣ₖ₂ {n = m} {n} y x)))

assoc⌣ₖ₂' : (n m k : ℕ) (x : EM ℤ/2 n) (y : EM ℤ/2 m) (z : EM ℤ/2 k)
  → PathP (λ i → EM ℤ/2 (+-assoc n m k i))
           (⌣ₖ₂' n (m + k) x (⌣ₖ₂' m k y z))
           (⌣ₖ₂' (n + m) k (⌣ₖ₂' n m x y) z)
assoc⌣ₖ₂' n m k x y z =
  toPathP (sym (substComposite (EM ℤ/2) (+'≡+ n (m + k)) (+-assoc n m k)
               _)
        ∙ (cong (subst (EM ℤ/2) (+'≡+ n (m + k) ∙ +-assoc n m k))
            (cong (λ x → (⌣ₖ₂ {n = n} {m + k} x (⌣ₖ₂' m k y z)))
              (sym (transportRefl x))
          ∙ (substComp⌣ₖ _ _ _ refl _ (+'≡+ m k)
              (cong (n +'_) (+'≡+ m k)) x (⌣ₖ₂ {n = m} {k} y z)))
        ∙ sym (substComposite (EM ℤ/2) (cong (n +'_) (+'≡+ m k)) (+'≡+ n (m + k) ∙ +-assoc n m k)
               _))
        ∙ cong (subst (EM ℤ/2) (cong (n +'_) (+'≡+ m k) ∙ +'≡+ n (m + k) ∙ +-assoc n m k))
               (sym (subst⁻Subst (EM ℤ/2) (+'-assoc n m k) _)
               ∙ cong (subst (EM ℤ/2) (sym (+'-assoc n m k)))
                 (sym (assoc⌣ₖ {G'' = ℤ/2Ring} n m k x y z)))
        ∙ sym (substComposite (EM ℤ/2) (sym (+'-assoc n m k))
            (cong (n +'_) (+'≡+ m k) ∙ +'≡+ n (m + k) ∙ +-assoc n m k) _)
        ∙ (cong (λ p → subst (EM ℤ/2) p
                         (⌣ₖ₂ {n = n +' m} {m = k}
                          (⌣ₖ₂ {n = n} {m = m} x y) z)) (isSetℕ _ _ _ _)
         ∙ substComposite (EM ℤ/2) (cong (_+' k) (+'≡+ n m)) (+'≡+ (n + m) k) _)
        ∙ cong (subst (EM ℤ/2) (+'≡+ (n + m) k))
            (sym (substComp⌣ₖ _ _ _ (+'≡+ n m) _ refl
               (cong (_+' k) (+'≡+ n m)) (⌣ₖ₂ {n = n} {m} x y) z)
           ∙ cong₂ (⌣ₖ₂ {n = n + m} {k}) refl (transportRefl z)))


EMℤ/2-sumFun : (k : ℕ) → (f g : (n : ℕ) → EM ℤ/2 n) → EM ℤ/2 k
EMℤ/2-sumFun k f g =
  sum≤ {A = EM ℤ/2 k} k
    (λ p r → subst (EM ℤ/2) (snd r)
               (⌣ₖ₂' (fst r) p (f (fst r)) (g p)))
    _+ₖ_


sum : ∀ {ℓ} {A : ℕ → Type ℓ}
  → (plusA : {n : ℕ} → A n → A n → A n)
  → (mult : (n m : ℕ) → A n → A m → A (n + m))
  → (f g : (n : ℕ) → A n)
  → (k : ℕ) → A k
sum {A = A} plusA mult f g k = sum≤ {A = A k} k
  (λ p r → subst A (snd r) (mult (fst r) p (f (fst r)) (g p))) plusA

flip¬≤ : (n : ℕ) (x : Fin (suc n)) → n ∸ (fst x) < suc n
flip¬≤ n (zero , p) = 0 , refl
flip¬≤ zero (suc x , p) = 0 , refl
flip¬≤ (suc n) (suc x , p) =
  <-trans (flip¬≤ n (x , pred-≤-pred p)) (0 , refl)

flipFin : (n : ℕ) → Fin (suc n) → Fin (suc n)
flipFin n x = (n ∸ (fst x)) , flip¬≤ n x

flipIdemP : (n : ℕ) (x : _) → flipFin n (flipFin n x) ≡ x
flipIdemP n (x , y , p) = Σ≡Prop (λ _ → Cubical.Data.Nat.Order.isProp≤)
  (cong (λ n → n ∸ (n ∸ x)) (cong predℕ (sym p ∙ +-suc y x))
  ∙ cong (y + x ∸_) (+∸ y x)
  ∙ ∸+ x y)

flipFinIso : (n : ℕ) → Iso (Fin (suc n)) (Fin (suc n))
fun (flipFinIso n) = flipFin n
inv (flipFinIso n) = flipFin n
rightInv (flipFinIso n) = flipIdemP n
leftInv (flipFinIso n) = flipIdemP n

flipFin' : (n : ℕ) → (Σ[ m ∈ ℕ ] (m ≤ n)) → (Σ[ m ∈ ℕ ] (m ≤ n))
flipFin' n (x , p) = t .fst , snd t .fst
  , cong predℕ (sym (+-suc (fst (snd t)) (fst t)) ∙ (snd t .snd))
  where
  t = flipFin n (x , fst p , +-suc (fst p) x ∙ cong suc (snd p))

flipFin'idemP : (n : ℕ) → (x : Σ[ m ∈ ℕ ] (m ≤ n)) → flipFin' n (flipFin' n x) ≡ x
flipFin'idemP n (x , p) = Σ≡Prop (λ _ → Cubical.Data.Nat.Order.isProp≤)
  (cong fst (flipIdemP n (x , fst p , +-suc (fst p) x ∙ cong suc (snd p))))

flipFinIso' : (n : ℕ) → Iso (Σ[ m ∈ ℕ ] (m ≤ n)) (Σ[ m ∈ ℕ ] (m ≤ n))
fun (flipFinIso' n) = flipFin' n
inv (flipFinIso' n) = flipFin' n
rightInv (flipFinIso' n) = flipFin'idemP n
leftInv (flipFinIso' n) = flipFin'idemP n

sum-helper≤-suc : ∀ {ℓ} {A : Type ℓ} (m : ℕ)
  (f : (n : ℕ) → n ≤ (suc m) → A) (plusA : A → A → A)
  (k : ℕ) (p : k ≤ m)
  → (sum-helper≤ {A = A} m (λ n p → f n (≤-trans p (1 , refl))) plusA k p)
   ≡ sum-helper≤ {A = A} (suc m) f plusA k (≤-trans p (1 , refl))
sum-helper≤-suc m f plusA zero p = refl
sum-helper≤-suc m f plusA (suc k) p =
  cong₂ plusA (sum-helper≤-suc m f plusA k
    (≤-trans (1 , (λ _ → suc k)) p)
     ∙ cong (sum-helper≤ (suc m) f plusA k) (Cubical.Data.Nat.Order.isProp≤ _ _))
    refl

f1' : ∀ {ℓ} {A : Type ℓ} (m : ℕ) (f : (n : ℕ) → n ≤ (suc m) → A) (plusA : A → A → A)
  → (plusAssoc : (x y z : A) → plusA x (plusA y z) ≡ plusA (plusA x y) z)
  → (k : _) {p : _} {q : _} {r : _}
  → sum-helper≤ {A = A} (suc m) f plusA (suc k) p
   ≡ plusA (f zero (suc m , q))
           (sum-helper≤ {A = A} m (λ n p → f (suc n) (suc-≤-suc p)) plusA k r)
f1' {A = A} m f plusA plusAssoc zero =
  cong₂ plusA (cong (f zero) (Cubical.Data.Nat.Order.isProp≤ _ _))
              (cong (f 1) (Cubical.Data.Nat.Order.isProp≤ _ _))
f1' {A = A} m f plusA plusAssoc (suc k) {p = p} {q = q} {r = r} =
     cong₂ plusA
       (f1' m f plusA plusAssoc k {p = (≤-trans (1 , (λ _ → 1 + suc k)) p)}
            {q = q}
            {r = ≤-trans (1 , (λ _ → 1 + k)) r})
       (cong (f (suc (suc k))) (Cubical.Data.Nat.Order.isProp≤ _ _))
   ∙ sym (plusAssoc (f zero (suc m , q))
                    (sum-helper≤ m (λ n p₁ → f (suc n) (suc-≤-suc p₁))
                      plusA k (≤-trans (1 , (λ _ → suc k)) r))
                    (f (suc (suc k)) (suc-≤-suc r)))

sum-comm' : {A : ℕ → Type}
  → (plusA : {n : ℕ} → A n → A n → A n)
  → (plusA-comm : {n : ℕ} → (x y : A n) → plusA x y ≡ plusA y x)
  → (plusAssoc : {n : ℕ} (x y z : A n) → plusA x (plusA y z) ≡ plusA (plusA x y) z)
  → (k : ℕ)
  → (f g : (n : ℕ) → n ≤ k → A k)
  → ((λ n p → f (k ∸ n) (Iso.fun (flipFinIso' k) (n , p) .snd)) ≡ g)
  → sum-helper≤ {A = A k} k f plusA k (0 , refl)
   ≡ sum-helper≤ {A = A k} k g plusA k (0 , refl)
sum-comm' {A = A} plusA plusA-comm plusAssoc zero f = J> refl
sum-comm' {A = A} plusA plusA-comm plusAssoc (suc k) f =
  J> f1' k f plusA plusAssoc k
      {p = 0 , refl} {q = +-comm (suc k) zero} {r = 0 , refl}
    ∙ plusA-comm _ _
    ∙ cong₂ plusA ((sum-comm' {A = A ∘ suc} plusA plusA-comm plusAssoc k
                              (λ n p → f (suc n) (suc-≤-suc p))
                              (λ n p → f (suc (k ∸ n)) (suc-≤-suc (flipFin' k (n , p) .snd)))
                              refl
                 ∙ cong (λ s → sum-helper≤ k s plusA k (0 , (λ i → k)))
                        (funExt (λ n → funExt λ p
                          → cong (λ x → f (fst x) (snd x))
                            (Σ≡Prop (λ _ → Cubical.Data.Nat.Order.isProp≤)
                              ((cong suc (cong (_∸ n) (sym (snd p))
                                ∙ +∸ (fst p) n)
                              ∙ sym (+∸ (suc (fst p)) n))
                             ∙ cong (_∸ n) (cong suc (snd p)))))))
                 ∙ sum-helper≤-suc k (λ n p → f (suc k ∸ n)
                  (flipFin' (suc k) (n , p) .snd)) plusA k (0 , refl))
        (cong (λ x → f (fst x) (snd x))
        (Σ≡Prop (λ _ → Cubical.Data.Nat.Order.isProp≤) (sym (n∸n k))) )

open import Cubical.Data.Sum
multᵣΠDepFinVec : ∀ {ℓ} (A : ℕ → Pointed ℓ)
          (mult : (n m : ℕ) → A n .fst → A m .fst → A (n + m) .fst)
       → (k : ℕ) (a : A k .fst) (f : (n : ℕ) → A n .fst)
       → ((n : ℕ) → A n .fst)
multᵣΠDepFinVec A mult k a f n with (Dichotomyℕ k n)
... | inl x = subst (fst ∘ A) (snd x) (mult _ _ (f (fst x)) a)
... | inr x = snd (A n)

sum-comm : {A : ℕ → Type}
  → (plusA : {n : ℕ} → A n → A n → A n)
  → (plusA-comm : {n : ℕ} → (x y : A n) → plusA x y ≡ plusA y x)
  → (plusAssoc : {n : ℕ} (x y z : A n) → plusA x (plusA y z) ≡ plusA (plusA x y) z)
  → (mult : (n m : ℕ) → A n → A m → A (n + m))
  → ((n m : ℕ) (x : A n) (y : A m)
      → PathP (λ i → A (+-comm n m i)) (mult n m x y) (mult m n y x))
  → (f g : (n : ℕ) → A n)
  → (k : ℕ) → sum plusA mult f g k ≡ sum plusA mult g f k
sum-comm {A = A} plusA plusA-comm plusAssoc mult commMult f g k =
  sum-comm' {A = A} plusA plusA-comm plusAssoc
     k ((λ p r → subst A (snd r) (mult (fst r) p (f (fst r)) (g p))))
       (λ p r → subst A (snd r) (mult (fst r) p (g (fst r)) (f p)))
       (funExt (λ n → funExt λ p
         → cong (subst A (snd (flipFin' k (n , p) .snd)))
                 (sym (fromPathP (commMult (k ∸ n) (fst (flipFin' k (n , p) .snd))
                   (g (k ∸ n)) (f (fst (flipFin' k (n , p) .snd)))))
                ∙ cong (subst A (+-comm (k ∸ n) (fst (flipFin' k (n , p) .snd))))
                       (sym (fromPathP λ i → mult (lem₁ n p i)
                                                   (lem₂ n p i)
                                                   (g (lem₁ n p i))
                                                   (f (lem₂ n p i)))))
               ∙ substLem _ _ _ _ _ _ _ _ (mult (fst p) n (g (fst p)) (f n))))
  where
  substLem : ∀ (a b : ℕ) (p : a ≡ b) (c : ℕ) (q : b ≡ c)
    (d : ℕ) (r : c ≡ d) (s : a ≡ d) (a : A a)
      → subst A r (subst A q (subst A p a)) ≡ subst A s a 
  substLem a = J> J> J> λ s a → transportRefl _ ∙ transportRefl _
    ∙ λ i → subst A (isSetℕ _ _ refl s i) a
  module _ (n : ℕ) (p : n ≤ k) where
    lem₁ : fst p ≡ k ∸ n
    lem₁ = (sym (+∸ (fst p) n) ∙ (cong (_∸ n) (snd p)))

    lem₂ : n ≡ (fst (flipFin' k (n , p) .snd))
    lem₂ = cong fst (Cubical.Data.Nat.Order.isProp≤
             (n , cong (n +_) (cong (_∸ n) (sym (snd p)))
                ∙ (cong (n +_)
                    (+∸ (fst p) n)
                ∙ +-comm n (fst p))
                ∙ snd p)
             (flipFin' k (n , p) .snd))

+ΠDepFinVec : (n : ℕ) (f g : ΠDepFinVec (EM∙ ℤ/2) n) → ΠDepFinVec (EM∙ ℤ/2) n
fst (+ΠDepFinVec n f g) x = fst f x +ₖ fst g x
snd (+ΠDepFinVec n f g) k = cong₂ _+ₖ_ (snd f k) (snd g k) ∙ rUnitₖ (suc (k + n)) (0ₖ _)

{-RP→EM-ℤ/2-CharacIso-}

RP→EM-ℤ/2-CharacIso' : (n : ℕ)
  → Iso (EM ℤ/2 1 → EM ℤ/2 n)
         (ΠDepFinVec (EM∙ ℤ/2) n)
RP→EM-ℤ/2-CharacIso' zero = compIso RP→Charac₀ (invIso (ΠDepFinVec≅× zero (EM∙ ℤ/2)))
RP→EM-ℤ/2-CharacIso' (suc n) =
  compIso (EM→-charac {A = EM∙ ℤ/2 1} (suc n))
   (compIso Σ-swap-Iso
     (compIso (prodIso idIso (compIso (invIso (equivToIso (⌣RP∞''Equiv n)))
       (RP→EM-ℤ/2-CharacIso' n)))
         (invIso (ΠDepFinVec-ind n (EM∙ ℤ/2)))))

0ₖΠDepFinVec : (n : ℕ) → ΠDepFinVec (EM∙ ℤ/2) n
0ₖΠDepFinVec n = 0ΠDepFinVec n (EM∙ ℤ/2)

ΠDepFinVec↓∙ : (n : ℕ) → ΠDepFinVec↓ n (EM∙ ℤ/2) (0ₖΠDepFinVec (suc n)) ≡ 0ₖΠDepFinVec n
ΠDepFinVec↓∙ n = toPathΠDepFinVec (EM∙ ℤ/2) n λ k _ → ΠDepFinVec↓₁∙ n (EM∙ ℤ/2) k

RP→EM-ℤ/2-CharacIso'inv∙ :  (n : ℕ)
  → Iso.inv (RP→EM-ℤ/2-CharacIso' n) (0ₖΠDepFinVec n) ≡ λ _ → 0ₖ n
RP→EM-ℤ/2-CharacIso'inv∙ zero = refl
RP→EM-ℤ/2-CharacIso'inv∙ (suc n) =
  funExt (λ x
    → rUnitₖ (suc n) (⌣RP∞''Equiv n .fst
         (inv (RP→EM-ℤ/2-CharacIso' n)
          (ΠDepFinVec↓ n (EM∙ ℤ/2) (0ₖΠDepFinVec (suc n)))) .fst x)
    ∙∙ cong (subst (EM ℤ/2) (+'-suc₁ n))
         (lem x)
    ∙∙ subst-EM-0ₖ (+'-suc₁ n))
  where
  lem : (x : EM ℤ/2 1)
    → ⌣ₖ₂ {n = 1} {m = n} x
           (inv (RP→EM-ℤ/2-CharacIso' n) (ΠDepFinVec↓ n (EM∙ ℤ/2) (0ₖΠDepFinVec (suc n))) x)
    ≡ 0ₖ (1 +' n)
  lem x =
      cong (⌣ₖ₂ {n = 1} {m = n} x)
          (funExt⁻ (cong (inv (RP→EM-ℤ/2-CharacIso' n)) (ΠDepFinVec↓∙ n)) x
        ∙ funExt⁻ (RP→EM-ℤ/2-CharacIso'inv∙ n) x)
    ∙ ⌣ₖ-0ₖ {G'' = ℤ/2Ring} 1 n x


expEM₁ : (x : EM ℤ/2 1) → (n : ℕ) → EM ℤ/2 n
expEM₁ x zero = fone
expEM₁ x (suc n) = ⌣ₖ₂' 1 n x (expEM₁ x n)

module _ {ℓ} (A : ℕ → Pointed ℓ) (n m : ℕ)
  (f : ΠDepFinVec A n) (g : ΠDepFinVec A m)
  (plusA : {n : ℕ} → A n .fst → A n .fst → A n .fst)
  (multA : (n m : ℕ) → A n .fst → A m .fst → A (n + m) .fst)
  where
  multΠDepFinVec₁ : (n : ℕ) → A n .fst
  multΠDepFinVec₁ = sum {A = fst ∘ A} plusA multA (fst f) (fst g)

  module _ (ridA : {n : ℕ} → plusA (snd (A n)) (snd (A n)) ≡ snd (A n))
           (multAL : (n m : ℕ) (y : A m .fst)
           → multA n m (snd (A n)) y ≡ snd (A (n + m)))
           (multAR : (n m : ℕ) (x : A n .fst)
           → multA n m x (snd (A m)) ≡ snd (A (n + m))) where

    abstract
      f∙g=0 : (k s : ℕ) (p : s ≤ suc (k + (n + m)))
        → subst (fst ∘ A) (snd p) (multA (fst p) s (f .fst (fst p)) (g .fst s))
        ≡ snd (A (suc (k + (n + m))))
      f∙g=0 k s p with (Dichotomyℕ (fst p) n)
      ... | inl x =
        ((cong (λ xa → subst (fst ∘ A) xa (multA (fst p) s (f .fst (fst p)) (g .fst s)))
                       (isSetℕ _ _ _ _)
         ∙ substComposite (fst ∘ A)
                      (cong (fst p +_) (sym s>))
                      rl
                      (multA (fst p) s (f .fst (fst p)) (g .fst s))))
        ∙∙ cong (subst (fst ∘ A) rl)
            (fromPathP (cong (λ w → multA (fst p) w (f .fst (fst p)) (g .fst w))
                          (sym s>)
                  ▷ cong (multA (fst p) (suc (k + fst x + m)) (f .fst (fst p)))
                         (g .snd (k + fst x)))
                 ∙ multAR _ _ _)
        ∙∙ λ j → transp (λ k → fst (A (rl (j ∨ k))))
                         j (snd (A (rl j)))
        where
        abstract
          s> : suc (k + fst x + m) ≡ s
          s> = sym (+-suc (k + fst x) m)
                  ∙ sym (inj-m+ (snd p
                  ∙ cong (λ n → suc (k + (n + m))) (sym (snd x))
                  ∙ sym (+-suc k (fst x + fst p + m))
                  ∙ cong (k +_)
                     (sym (+-suc (fst x + fst p) m)
                     ∙ cong (_+ suc m) (+-comm (fst x) (fst p)))
                 ∙ +-assoc k (fst p + fst x) (suc m)
                 ∙ cong (_+ suc m) (+-assoc k (fst p) (fst x)
                          ∙ cong (_+ fst x) (+-comm k (fst p))
                          ∙ sym (+-assoc (fst p) k (fst x)))
                 ∙ sym (+-assoc (fst p) (k + fst x) (suc m))))

          rl : fst p + suc (k + fst x + m) ≡ suc (k + (n + m))
          rl = cong (fst p +_) s> ∙ snd p

      ... | inr x = (cong (λ xa → subst (fst ∘ A) xa (multA (fst p) s (f .fst (fst p)) (g .fst s)))
                       (isSetℕ _ _ _ _)
         ∙ substComposite (fst ∘ A)
                      (cong (_+ s) (sym (snd x) ∙ +-suc (fst x) n))
                      (cong suc path)
                      (multA (fst p) s (f .fst (fst p)) (g .fst s)))
        ∙∙ cong (subst (fst ∘ A ∘ suc) path)
              (fromPathP (cong (λ m → multA m s (f .fst m) (g .fst s))
                          (sym (snd x) ∙ +-suc (fst x) n)
                  ▷ (cong (λ m → multA _ s m (g .fst s)) (snd f (fst x))
                  ∙ multAL _ s (g .fst s))))
               ∙∙ λ j → transp (λ k → fst (A (suc (path (j ∨ k)))))
                         j (snd (A (suc (path j))))
        where
        path : fst x + n + s ≡ k + (n + m)
        path = cong predℕ
          (cong (_+ s) (sym (+-suc (fst x) n) ∙ snd x) ∙ snd p)

      multΠDepFinVec₂ : (k : ℕ) → multΠDepFinVec₁ (suc (k + (n + m))) ≡ snd (A (suc (k + (n + m))))
      multΠDepFinVec₂ k = (λ i → sum≤ (suc (k + (n + m)))
           (λ s p → f∙g=0 k s p i )
           plusA)
        ∙ sum-helper≤0 (suc (k + (n + m))) plusA
                       (snd (A (suc (k + (n + m)))))
                       ridA (suc (k + (n + m))) (0 , refl)

    multΠDepFinVec : ΠDepFinVec A (n + m)
    fst multΠDepFinVec = multΠDepFinVec₁
    snd multΠDepFinVec = multΠDepFinVec₂

⌣ΠDepFinVec : (n m : ℕ) (f : ΠDepFinVec (EM∙ ℤ/2) n) (g : ΠDepFinVec (EM∙ ℤ/2) m)
  → ΠDepFinVec (EM∙ ℤ/2) (n + m)
⌣ΠDepFinVec n m f g =
  multΠDepFinVec (EM∙ ℤ/2) n m f g
    (λ {n} → _+ₖ_ {n = n}) ⌣ₖ₂'
    (λ {n} → rUnitₖ n (0ₖ {G = ℤ/2} n))
    0ₖ-⌣ₖ₂' ⌣ₖ₂'-0ₖ
