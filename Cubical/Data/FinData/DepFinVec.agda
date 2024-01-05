{-# OPTIONS --safe #-}
module Cubical.Data.FinData.DepFinVec where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open Iso

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sum
open import Cubical.Data.Sigma

open import Cubical.Data.FinData.Base
open import Cubical.Data.FinData.Properties hiding (snotz)

private
  variable
    ℓ ℓ' : Level

{-

  WARNING : If someone use dependent vector in a general case.
            One always think about the following definition.
            Yet because of the definition one to add (toℕ k).
            Which is going to introduce a lot of issues.
            One may consider depVec rather than depFinVec to avoid this issue?
-}

depFinVec : ((n : ℕ) → Type ℓ) → (m : ℕ) → Type ℓ
depFinVec G m = (k : Fin m) → G (toℕ k)

-- move to ℕ
Dichotomyℕ : ∀ (n m : ℕ) → (n ≤ m) ⊎ (n > m)
Dichotomyℕ n m with (Cubical.Data.Nat.Order._≟_ n m)
... | lt x = inl (<-weaken x)
... | Trichotomy.eq x = inl (0 , x)
... | gt x = inr x

open import Cubical.Foundations.Pointed
open import Cubical.Data.Empty as ⊥

ΠDepFinVec : (A : ℕ → Pointed ℓ) (m : ℕ) → Type ℓ
ΠDepFinVec A m = Σ[ f ∈ ((n : ℕ) → A n .fst) ] ((k : ℕ) → f (suc k + m) ≡ snd (A (suc k + m)))

0ΠDepFinVec : (n : ℕ) (A : ℕ → Pointed ℓ) → ΠDepFinVec A n 
fst (0ΠDepFinVec n A) m = snd (A m)
snd (0ΠDepFinVec n A) _ = refl

ΠDepFinVec↓₁ : (n : ℕ) (A : ℕ → Pointed ℓ) → ΠDepFinVec A (suc n) → (x : ℕ) → A x .fst
ΠDepFinVec↓₁ n A f m with (Dichotomyℕ m n)
... | inl x = fst f m
... | inr x = snd (A m)

ΠDepFinVec↓₁≡ : (n : ℕ) (A : ℕ → Pointed ℓ) (f : ΠDepFinVec A (suc n)) (x : ℕ)
  → x ≤ n → ΠDepFinVec↓₁ n A f x ≡ f .fst x
ΠDepFinVec↓₁≡ n A f m p with (Dichotomyℕ m n)
... | inl x = refl
... | inr x = ⊥.rec (¬m<m (≤-trans x p))

ΠDepFinVec↓₁∙ : (n : ℕ) (A : ℕ → Pointed ℓ)
  → (k : ℕ) → ΠDepFinVec↓₁ n A (0ΠDepFinVec (suc n) A) k ≡ A k .snd
ΠDepFinVec↓₁∙ n A k with (Dichotomyℕ k n)
... | inl x = refl
... | inr x = refl

abstract
  ΠDepFinVec↓₂ : (n : ℕ) (A : ℕ → Pointed ℓ) (f : ΠDepFinVec A (suc n))
    → (k : ℕ) → ΠDepFinVec↓₁ n A f (suc (k + n)) ≡ snd (A (suc (k + n)))
  ΠDepFinVec↓₂ n A (f , p) k  with (Dichotomyℕ (suc (k + n)) n)
  ... | inl x = ⊥.rec (¬m<m (fst x + k
    , (sym (+-assoc (fst x) k (suc n)) ∙ cong (fst x +_) (+-suc k n)) ∙ snd x))
  ... | inr x = refl

ΠDepFinVec↓ : (n : ℕ) (A : ℕ → Pointed ℓ) → ΠDepFinVec A (suc n) → ΠDepFinVec A n
fst (ΠDepFinVec↓ n A f) = ΠDepFinVec↓₁ n A f
snd (ΠDepFinVec↓ n A f) = ΠDepFinVec↓₂ n A f 

ΠDepFinVec↑ : (n : ℕ) (A : ℕ → Pointed ℓ)
  → A (suc n) .fst → ΠDepFinVec A n → ΠDepFinVec A (suc n)
fst (ΠDepFinVec↑ n A x f) m with (Cubical.Data.Nat.Order._≟_ m (suc n))
... | lt x₁ = fst f m
... | Trichotomy.eq x₁ = subst (fst ∘ A) (sym x₁) x
... | gt x₁ = snd (A m)
snd (ΠDepFinVec↑ n A x f) k with (Cubical.Data.Nat.Order._≟_ (k + suc n) n)
... | lt x₁ = subst (λ n → fst f n ≡ snd (A n)) (cong suc (sym (+-suc k n))) (f .snd (suc k))
... | Trichotomy.eq x₁ = ⊥.rec (¬m<m (k , x₁))
... | gt x₁ = refl

toPathΠDepFinVec : (A : ℕ → Pointed ℓ) (m : ℕ) {f g : ΠDepFinVec A m}
  → ((k : ℕ) → k ≤ m → fst f k ≡ fst g k) → f ≡ g
toPathΠDepFinVec A m {f = f} {g} p = ΣPathP ((funExt help) , funExt p2)
  where
  h2-fill : (n : ℕ) (i j : I) (p : m < n) → fst (A _)
  h2-fill n i j (x , p) =
    fill (λ k → fst (A ((sym (+-suc x m) ∙ p) k)))
         (λ k → λ {(i = i0) → fst f ((sym (+-suc x m) ∙ p) k)
                  ; (i = i1) → fst g ((sym (+-suc x m) ∙ p) k)})
         (inS ((snd f x ∙∙ refl ∙∙ sym (snd g x)) i)) j

  help : (x : _) → fst f x ≡ fst g x
  help n with (Dichotomyℕ n m)
  ... | inl x = p n x
  ... | inr (x , p) = (λ i → h2-fill n i i1 (x , p))

  p2 : (x : ℕ) →
      PathP (λ z → help (suc (x + m)) z ≡ snd (A (suc (x + m))))
            (snd f x) (snd g x)
  p2 x with (Dichotomyℕ (suc (x + m)) m)
  ... | inl x₁ = ⊥.rec (¬m<m (fst x₁ + x
    , (sym (+-assoc (fst x₁) x (suc m))
    ∙ cong (fst x₁ +_) (+-suc x m)) ∙ snd x₁))
  ... | inr x₁ = λ i j →
       comp (λ k → fst (A (((sym (+-suc (fst x₁) m)) ∙ snd x₁) k)))
            (λ k → λ {(i = i0) → help2 (fst f) (snd f) (fst x₁) x
                                    (inj-+m (snd x₁ ∙ sym (+-suc x m)))
                                    ((sym (+-suc (fst x₁) m)) ∙ snd x₁) k j
                     ; (i = i1) → help2 (fst g) (snd g) (fst x₁) x
                                    (inj-+m (snd x₁ ∙ sym (+-suc x m)))
                                    ((sym (+-suc (fst x₁) m)) ∙ snd x₁) k j
                     ; (j = i0) → h2-fill (suc (x + m)) i k x₁
                     ; (j = i1) → snd (A (((sym (+-suc (fst x₁) m)) ∙ snd x₁) k))})
            (doubleCompPath-filler (snd f (fst x₁)) refl (sym (snd g (fst x₁))) (~ j) i)
    where
    help2 : (f : (n : ℕ) → A n .fst)
           (sndf : (k₁ : ℕ) → f (suc (k₁ + m)) ≡ snd (A (suc (k₁ + m))))
           (x₁ x : ℕ) (r : x₁ ≡ x)
         → (p : (suc (x₁ + m)) ≡ (suc (x + m)))
         → SquareP (λ i j → fst (A (p i))) (sndf x₁) (sndf x)
                    (cong f p) (cong (snd ∘ A) p)
    help2 f sndf x₁ = J> λ p
      → subst (λ p → SquareP (λ i j → fst (A (p i))) (sndf x₁) (sndf x₁)
                               (cong f p) (cong ((λ r → snd r) ∘ A) p))
                               (isSetℕ _ _ refl p)
                               refl

ΠDepFinVec-ind : (n : ℕ) (A : ℕ → Pointed ℓ)
  → Iso (ΠDepFinVec A (suc n)) (A (suc n) .fst × ΠDepFinVec A n)
fun (ΠDepFinVec-ind n A) (f , p) = (f (suc n)) , ΠDepFinVec↓ n A (f , p)
inv (ΠDepFinVec-ind n A) (f , p) = ΠDepFinVec↑ n A f p
rightInv (ΠDepFinVec-ind n A) (f , p) =
  ΣPathP (l1 , toPathΠDepFinVec A _ l2)
  where
  l2 : (k : ℕ) → (k ≤ n)
    → (snd (fun (ΠDepFinVec-ind n A) (inv (ΠDepFinVec-ind n A) (f , p)))) .fst k ≡ p .fst k
  l2 k r with (Dichotomyℕ k n)
  ... | inl x = l3
   where
   l3 : fst (ΠDepFinVec↑ n A f p) k ≡ p .fst k
   l3 with (k Cubical.Data.Nat.Order.≟ suc n)
   ... | lt x = refl
   ... | Trichotomy.eq x = ⊥.rec (¬m<m (fst r , (cong (fst r +_) (sym x)) ∙ snd r))
   ... | gt q = ⊥.rec (¬m<m (≤-trans q (suc (fst x) , cong suc (snd x) )))
  ... | inr x =
    ⊥.rec (¬m<m (fst x + fst r
      , (sym (+-assoc (fst x) (fst r) (suc k))
       ∙ cong (fst x +_) (+-suc (fst r) k))
      ∙ cong (fst x +_) (cong suc (snd r)) ∙ snd x))
  l1 : fst (ΠDepFinVec↑ n A f p) (suc n) ≡ f
  l1 with (n Cubical.Data.Nat.Order.≟ n)
  ... | lt x = ⊥.rec (¬m<m x)
  ... | Trichotomy.eq x = (λ i → subst (fst ∘ A) (isSetℕ _ _ (cong suc (sym x)) refl i) f)
                        ∙ transportRefl f
  ... | gt x = ⊥.rec (¬m<m x)
leftInv (ΠDepFinVec-ind n A) (f , p) = toPathΠDepFinVec A _ help
  where
  h2 : (k : ℕ) (r : k < suc n) → fst (ΠDepFinVec↓ n A (f , p)) k ≡ f k
  h2 k q with (Dichotomyℕ k n)
  ... | inl x = refl
  ... | inr x = ⊥.rec (¬m<m
    (fst x + fst q , sym (+-assoc (fst x) (fst q) (suc k))
      ∙ cong (fst x +_) (snd q) ∙ snd x))
  help : (k : ℕ) →  k ≤ suc n
      → fst (inv (ΠDepFinVec-ind n A) (fun (ΠDepFinVec-ind n A) (f , p))) k ≡ f k
  help k q with (Cubical.Data.Nat.Order._≟_ k (suc n))
  ... | lt x = h2 k x
  ... | Trichotomy.eq x = fromPathP (λ i → f (x (~ i)))
  ... | gt x = ⊥.rec (¬m<m (fst x + fst q
      , (sym (+-assoc (fst x) (fst q) (suc k))
      ∙ cong (fst x +_) (+-suc (fst q) k))
      ∙ cong (fst x +_) (cong suc (snd q)) ∙ snd x))

ΠDepFinVec≅×₀ : (A : ℕ → Pointed ℓ)
  → Iso (ΠDepFinVec A 0) (A 0 .fst)
fun (ΠDepFinVec≅×₀ A) (f , p) = f zero
fst (inv (ΠDepFinVec≅×₀ A) a) zero = a
fst (inv (ΠDepFinVec≅×₀ A) a) (suc x) = A (suc x) .snd
snd (inv (ΠDepFinVec≅×₀ A) a) = λ _ → refl
rightInv (ΠDepFinVec≅×₀ A) a = refl
leftInv (ΠDepFinVec≅×₀ A) (f , p) = toPathΠDepFinVec
  A _ λ { zero → λ _ → refl ; (suc k) p → ⊥.rec (snotz (sym (+-suc (fst p) k) ∙ snd p))}

ΠDepFinVec≅× : (n : ℕ) (A : ℕ → Pointed ℓ)
  → Iso (ΠDepFinVec A n) ((fst ∘ A) ˣ n)
ΠDepFinVec≅× zero A = ΠDepFinVec≅×₀ A
ΠDepFinVec≅× (suc n) A =
  compIso (ΠDepFinVec-ind n A)
          (compIso Σ-swap-Iso (prodIso (ΠDepFinVec≅× n A) idIso))
