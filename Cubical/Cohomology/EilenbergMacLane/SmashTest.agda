{-# OPTIONS --safe --experimental-lossy-unification #-}

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


module Cubical.Cohomology.EilenbergMacLane.SmashTest where

-- testlem : (B C : Pointed₀) (D : fst B → Pointed₀) → isContr (fst B) →
--   (A : Pointed₀) (e : (Σ (fst B) (fst ∘ D) , pt B , pt (D _)) ≡ A) (a : fst A)
--    → (e' : (b : typ B) → D b ≡ A)
--    → (F : Σ (fst B) (fst ∘ D) → fst C)
--    → (c : fst C)
--    → ((x : fst B) → F (x , transport (sym (cong fst (e' x))) a) ≡ c)
--    → ((x : fst B) (r : fst (D x))
--      → (r ≡ transport (sym (cong fst (e' x))) a))
--    → F (transport (sym (cong fst e)) a) ≡ c
-- testlem B C D contr =
--   J> λ a e' F → λ c → λ id r → cong F
--     (transportRefl a)
--     ∙ cong F (ΣPathP (refl , r (fst a) (snd a)))
--      ∙ id (fst a)


-- ps : (A B : Type) (ct : isContr A) (e : Iso B (A × B))
--   → (b : B) → Iso.fun e b ≡ (ct .fst , b)
-- ps A B ct e b = {!!}

-- testlem' : (B C : Pointed₀) (A : Pointed₀) (D : fst B → Pointed₀)
--   → (e' : (λ _ → A) ≡ D)
--   → isContr (fst B)
--    → (e : (Σ (fst B) (fst ∘ D) , pt B , pt (D _)) ≡ A) (a : fst A)
--    → (F : Σ (fst B) (fst ∘ D) → fst C)
--    → (c : fst C)
--    → ((x : fst B) → F (_ , transport (cong fst (funExt⁻ e' x)) a) ≡ c)
--    → (id2 : (x : fst B) → snd (transport (sym (cong fst e)) a)
--                          ≡ {!transport (cong fst (funExt⁻ e' x)) a!})
--    → F (transport (sym (cong fst e)) a) ≡ c
-- testlem' B C A = J>
--   λ ctr e a F r id id2
--   → cong F
--       (ΣPathP ((sym (ctr .snd _))
--       , (({!cong fst e!}
--         ∙ {!!}) ▷ sym (transportRefl a))))
--   ∙ id (ctr .fst)


{-
  J> λ ctr e a F c k → k (fst ctr)
-}

{-
  J> λ a e' F → λ c → λ id r → cong F
    (transportRefl a)
    ∙ cong F (ΣPathP (refl , r (fst a) (snd a)))
     ∙ id (fst a)
-}

open import Cubical.HITs.Join

module _ {ℓ : Level} (X : RP∞) (A : fst X → Type ℓ) where
  data jo : Type ℓ where
    makel : {x : fst X} → A x → jo
    maker : ((x : _) → A x) → jo
    pusher : {x : fst X} (f : ((x : _) → A x)) → makel (f x) ≡ maker f

fam : (X : RP∞) → ℕ → Type
fam X zero = fst X
fam X (suc n) = join (fst X) (fam X n)

fam↓ : (X : RP∞) (n : ℕ) → fam X n → fam X (suc n)
fam↓ X n p = inr p

open import Cubical.HITs.SequentialColimit

S∞ : (X : RP∞) → Type
S∞ X = Lim→ (record { space = fam X ; map = λ {n} → fam↓ X n })

S∞pt : (n : ℕ) → (x : RP∞) → fst x → fam x n
S∞pt zero x p = p
S∞pt (suc n) x p = inr (S∞pt n x p)

BLT : (X : RP∞) (Y : RP∞)
  (A : fst X → fst Y → Pointed₀)
  → (isHomogeneous (SM∙ Y λ y → SM∙ X (λ x → A x y)))
  → (x : fst X) (y : fst Y)
  → A x y
    →∙ (A x (not* Y y)
    →∙ A (not* X x) y
    →∙ A (not* X x) (not* Y y)
    →∙ (SM∙ Y λ y → SM∙ X (λ x → A x y)) ∙ ∙ ∙) 
fst (BLT X Y A h x y) a1 = F
  where
  T = SM∙ Y λ y → SM∙ X (λ x → A x y)
  H : fst (A x (not* Y y)) → fst (A (not* X x) y) → A (not* X x) (not* Y y) →∙ T
  fst (H a2 a3) a4 = inr (CasesRP Y y (inr (CasesRP X x a1 a3)) (inr (CasesRP X x a2 a4)))
  snd (H a2 a3) = {!!}

  G : fst (A x (not* Y y)) →
      A (not* X x) y →∙ (A (not* X x) (not* Y y) →∙ T ∙)
  fst (G a2) = {!!}
  snd (G a2) = {!!}

  F : A x (not* Y y) →∙ (A (not* X x) y  →∙ A (not* X x) (not* Y y) →∙ T ∙ ∙)
  fst F = {!y!}
  snd F = {!!}
snd (BLT X Y A h x y) =
  →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneous→∙ h))
    (funExt λ a → →∙Homogeneous≡ (isHomogeneous→∙ h)
      (funExt λ b → →∙Homogeneous≡ h (funExt λ c → {!!})))

S∞-fib : (X Y : RP∞) (A : fst X → fst Y → Pointed₀)
  → S∞ X → S∞ Y → Σ[ B ∈ Pointed₀ ] ((SM∙ X λ x → SM∙ Y (A x)) ≡ B)
S∞-fib X Y A (inl {n = n} x) y = h n x y
  where
  t : (n n1 : ℕ) → fam X n
      → fam Y n1
      → Σ[ B ∈ Pointed₀ ] ((SM∙ X λ x → SM∙ Y (A x)) ≡ B)
  fst (t zero zero a b) =
      (A a b
    ⋀∙ A a (not* Y b))
    ⋀∙ (A (not* X a) b
    ⋀∙ A (not* X a) (not* Y b))
  snd (t zero zero a b) = {!!}
  t zero (suc n1) a b = _ , refl
  t (suc n) n1 a b = _ , refl

  h : (n : ℕ) → fam X n
      → S∞ Y
      → Σ[ B ∈ Pointed₀ ] ((SM∙ X λ x → SM∙ Y (A x)) ≡ B)
  h n y (inl {n = n1} y') = t n n1 y y'
  h n y (push {n = n1} x i) =
    isContr→isProp
      (isContrSingl (SM∙ X (λ x₂ → SM∙ Y (A x₂))))
        (t n n1 y x) (t n (suc n1) y (fam↓ Y n1 x)) i
S∞-fib X Y A (push {n = n} x i) s =
  isContr→isProp
      (isContrSingl (SM∙ X (λ x₂ → SM∙ Y (A x₂)))) (S∞-fib X Y A (inl x) s)
        (S∞-fib X Y A (inl {n = suc n} (fam↓ X n x)) s) i


S∞-ind' : (X : RP∞) (A : S∞ X → Type) (f g : (x : _) → A x)
     (p : (x : fst X) → f (inl x) ≡ g (inl x))
  → (x : _) → f x ≡ g x
S∞-ind' X A f g h (inl {n = zero} x) = h x
S∞-ind' X A f g h (inl {n = suc n} (inl x)) j = {!!}
S∞-ind' X A f g h (inl {n = suc n} (inr x)) j = {!!}
S∞-ind' X A f g h (inl {n = suc n} (push a b i)) j = {!!}
{-
  comp (λ k → A (push {n = suc n} (inl x) (~ k)))
       (λ k → λ {(j = i0) → f (push {n = suc n} (inl x) (~ k))
               ; (j = i1) → g (push {n = suc n} (inl x) (~ k))})
       {!f (push {n = suc n} (inl x) (~ i0))!}
       -}
S∞-ind' X A f g h (push x i) = {!x!}

S∞-ind : (X : RP∞) → (A : S∞ X → Type)
       → ((x : fst X) → A (inl x))
       → {!!}
S∞-ind = {!!}

S∞→' : (X : RP∞) → (A : S∞ X → Type)
  → (n : ℕ)
  → ((x : _) → isOfHLevel n (A x))
  → isContr (S∞ X)
  → ((x : fst X) → A (inl x))
  → (x : _) → A x
S∞→' X A zero hl c ind x = hl x .fst
S∞→' X A (suc n) hl c ind (inl {n = zero} x) = ind x
S∞→' X A (suc n) hl c ind (inl {n = suc m} (inl x)) =
  subst A (isContr→isProp c _ _) (ind x)
S∞→' X A (suc n) hl c ind (inl {n = suc m} (inr x)) =
  subst A (isContr→isProp c _ _) (S∞→' X A (suc n) hl c ind (inl {n = m} x))
S∞→' X A (suc n) hl c ind (inl {n = suc m} (push a b i)) = {!c!}
  where
  help : {!!}
  help = {!!}
S∞→' X A (suc n) hl c ind (push x i) = {!!}

S∞→ : (X : RP∞) → (A : S∞ X → Type)
  → isContr (S∞ X)
  → ((x : fst X) → A (inl x))
  → (x : _) → A x
S∞→ X A c r (inl {n = zero} x) = r x
S∞→ X A c r (inl {n = suc n} x) = {!x!}
S∞→ X A c r (push x i) = {!!}


-- help : (X : RP∞) → (A : fst X → Pointed₀) (c : (x y : _) → A x ≡ A y) → (n : ℕ) →  fam X n → Pointed₀
-- help' : (X : RP∞) → (A : fst X → Pointed₀) (c : (x y : _) → A x ≡ A y) → (n : ℕ) (a : fst X) (y : join (fst X) (fam X n)) → help X A c (suc n) y ≡ A a
-- help X A c zero x = A x
-- help X A c (suc n) (inl x) = A x
-- help X A c (suc n) (inr x) = help X A c n x
-- help X A c (suc zero) (push a b i) = c a b i
-- help X A c (suc (suc n)) (push a x i) = help' X A c n a x (~ i)
-- help' X A c zero a (inl x) = c x a
-- help' X A c zero a (inr x) = c x a
-- help' X A c zero a (push a' b i) = {!!}
-- help' X A c (suc n) a (inl x) = c x a
-- help' X A c (suc n) a (inr x) = help' X A c n a x
-- help' X A c (suc n) a (push a₁ b i) = {!!}

-- S∞→Type : (X : RP∞) → (A : fst X → Pointed₀) → ((x y : _) → A x ≡ A y) → S∞ X → Type
-- S∞→Type X A r (inl {n = zero} x) = A x .fst
-- S∞→Type X A r (inl {n = suc zero} (inl x)) = A x .fst
-- S∞→Type X A r (inl {n = suc (suc n)} (inl x)) = S∞→Type X A r (inl {n = suc n} (inl x))
-- S∞→Type X A r (inl {n = suc zero} (inr x)) = A x .fst
-- S∞→Type X A r (inl {n = suc (suc n)} (inr x)) = S∞→Type X A r (inl {n = suc n} x)
-- S∞→Type X A r (inl {n = suc zero} (push a b i)) = r a b i .fst
-- S∞→Type X A r (inl {n = suc (suc n)} (push a b i)) = {!!}
-- S∞→Type X A r (push {n = zero} x i) = A x .fst
-- S∞→Type X A r (push {n = suc zero} (inl x) i) = A x .fst
-- S∞→Type X A r (push {n = suc zero} (inr x) i) = A x .fst
-- S∞→Type X A r (push {n = suc zero} (push a b i₁) i) = r a b i₁ .fst
-- S∞→Type X A r (push {n = suc (suc n)} (inl x) i) = {!!}
-- S∞→Type X A r (push {n = suc (suc n)} (inr x) i) = {!!}
-- S∞→Type X A r (push {n = suc (suc n)} (push a b i₁) i) = {!!}

-- inl** : S∞ Bool* → {!!}
-- inl** = {!!}

-- isContr- : isContr (S∞ Bool*)
-- fst isContr- = Lim→.inl {n = 0} true
-- snd isContr- = {!!}
--   where
--   t : (n : ℕ) → Bool → fam Bool* n
--   t zero x = x
--   t (suc n) x = inl x

--   h : (n : ℕ) (y : fam Bool* (suc n)) → Path (S∞ Bool*) (inl true) (inl {n = suc n} y)
--   h zero (inl x) = push true ∙ λ i → inl {n = 1} (push x true (~ i))
--   h zero (inr x) = push true ∙ λ i → inl {n = 1} ((sym (push true true) ∙ (push true x)) i) -- cong (inl {n = 1}) {!!}
--   h zero (push a b i) = {!!}
--   h (suc n) (inl x) = h n (inl x)
--     ∙ push (inl x)
--     ∙ {!refl!}
--     ∙ sym (push (inl x)) -- (λ i → inl {n = suc n} (push x (t n x) i)) ∙ {!!}
--   h (suc n) (inr x) = h n x ∙ push x
--   h (suc n) (push a b i) = {!!}

-- fst isContr- = Lim→.inl {n = 0} true
-- snd isContr- (inl {n = zero} false) =
--   push _ ∙ cong s (sym (push false true))
--          ∙ cong s (push false false)
--          ∙ sym (push false)
--   where
--   t : Bool → S∞ Bool*
--   t = inl {n = zero}

--   s : fam Bool* 1 → S∞ Bool*
--   s = inl {n = 1}

-- snd isContr- (inl {n = zero} true) = refl
-- snd isContr- (inl {n = suc n} (inl x)) =
--   {!!}
-- snd isContr- (inl {n = suc n} (inr x)) =
--     snd isContr- (inl {n = n} x)
--   ∙ push x
-- snd isContr- (inl {n = suc n} (push a b i)) = {!!}
-- snd isContr- (push x i) = {!!}

-- module _ {A B : Type} (R : A → B → Type) where
--   PushoutRel : Type
--   PushoutRel = {!!}

-- module MM (X : RP∞) (A : fst X → Pointed₀) where
--   A' : Type
--   A' = fst X

--   B' : Type
--   B' = (x : fst X) → A x .fst

--   R : A' → B' → Type
--   R a b = Σ[ t ∈ A a .fst ] CasesRP X a t (pt (A _)) ≡ b

-- module _ (X Y : RP∞) (A : fst X → fst Y → Pointed₀) where

--   A' : (x : fst X) → Type
--   A' x = MM.A' Y (A x)

--   B' : (x : fst X) → Type
--   B' x = MM.B' Y (A x)

--   R' : (x : fst X) → A' x → B' x → Type
--   R' x = MM.R Y (A x)

--   ¬' = not* X

--   TYP = SM Y λ y → SM∙ X λ x → A x y
-- {-
--   module _ (B : Type) (e : ((x : fst X) → SM Y λ y → A x y) ≃ B)
--     (Bf : B → TYP) where

--     thep : (x : fst X) (r : fst (SM∙ Y (λ y₁ → A x y₁)))
--       → Σ[ b ∈ B ] invEq e b ≡  (CasesRP X x r (snd (SM∙ Y (A (not* X x)))))
--     thep = {!!}

--     test : (SM X λ x → SM∙ Y λ y → A x y) → TYP
--     test (inl x) = inr λ y → inl x
--     test (inr f) = Bf (fst e f)
--     test (push (y , r) i) = ({!!} ∙ cong Bf (sym (cong (fst e) (sym (thep y r .snd)) ∙ secEq e (fst (thep y r))))) i
-- -}
--   data mjo : Type where
--     aa : ((x : fst X) → A' x) → mjo
--     bb : ((x : fst X) → B' x) → mjo
--     ab : (x : fst X) → A' (¬' x) → B' x → mjo
--     ar : (x : fst X) (f : (x : fst X) → A' x)
--          (b : B' x) → R' x (f x) b → aa f ≡ ab x (f (¬' x)) b
--     br : (x : fst X) (a : A' (¬' x)) (b : (x : fst X) → B' x)
--          → R' (¬' x) a (b (¬' x))
--          → ab x a (b x) ≡ bb b
--     rr : (a : (x : fst X) → A' x) (b : (x : fst X) → B' x)
--        → ((x : fst X) → R' x (a x) (b x))
--        → aa a ≡ bb b
--     rr' : (a : (x : fst X) → A' x)
--           (b : (x : fst X) → B' x)
--           (r : ((x : fst X) → R' x (a x) (b x)))
--           (x : fst X)
--       → PathP (λ i → ar x a (b x) (r x) i ≡ bb b)
--                (rr a b r) (br x (a (¬' x)) b (r (¬' x)))

--   eval : (x : fst X) → fst Y ⊎ (fst X ≃ fst Y) → fst Y
--   eval x (inl y) = y
--   eval x (inr y) = fst y x

--   data mjo' : Type where
--       aa' : (fst Y ⊎ (fst X ≃ fst Y)) → mjo' -- X → Y
--       bb' : ((x : fst X) → B' x) → mjo'
--       ab' : (x : fst X) → fst Y → B' x → mjo'
--       ar' : (x : fst X) (f : fst Y ⊎ (fst X ≃ fst Y))
--            (b : B' x) → R' x (eval x f) b → aa' f ≡ ab' x (eval x f) b
--       br' : (x : fst X) (y : fst Y) (b : (x : fst X) → B' x)
--         → R' x y (b x)
--         → ab' x y (b x) ≡ bb' b
--       rr* : (a : (fst Y ⊎ (fst X ≃ fst Y)))
--             (b : (x : fst X) → B' x)
--          → ((x : fst X) → R' x (eval x a) (b x))
--          → aa' a ≡ bb' b
--       rr** : (a : (fst Y ⊎ (fst X ≃ fst Y)))
--             (b : (x : fst X) → B' x)
--             (r : ((x : fst X) → R' x (eval x a) (b x)))
--             (x : fst X)
--         → PathP (λ i → ar' x a (b x) (r x) i ≡ bb' b)
--                  (rr* a b r) (br' x (eval x a) b (r x))

--   mjo-ind* : (B : Type)
--     → (b : ((x : fst X) → B' x) → B)
--     → (f : fst Y → mjo' → B)
--     → (g : fst X ≃ fst Y → mjo' → B)
--     → (hyp1 : (x : fst X) (e : fst X ≃ fst Y) (F : B' x) (r : R' x (fst e x) F)
--               → g e ((ab' x (fst e x) F)) ≡ f (fst e x) (ab' x (fst e x) F))
--     → (hyp2 : (x : fst X) (y : fst Y) (F : (x : fst X) → B' x) (r : R' x y (F x))
--             → f y (bb' F) ≡ b F)
--     → (hyp3 : (y : fst Y) (F : (x : fst X) → B' x) (r : (x : fst X) → R' x y (F x))
--             → f y (bb' F) ≡ b F )
--     → (hyp4 : (e : fst X ≃ fst Y) (F : (x : fst X) → B' x) (r : (x : fst X) → R' x (fst e x) (F x))
--               → g e (bb' F) ≡ b F)
--     → (hyp5 : (x : fst X) (y : fst Y) (F : (x₁ : fst X) → B' x₁) (r : (x₁ : fst X) → R' x₁ y (F x₁))
--             → hyp3 y F r ≡ hyp2 x y F (r x))
--     → (hyp6 : (x : fst X) (e : fst X ≃ fst Y) (F : (x₁ : fst X) → B' x₁) (r : (x₁ : fst X) → R' x₁ (fst e x₁) (F x₁))
--             → PathP (λ i → hyp1 x e (F x) (r x) i ≡ (hyp2 x (fst e x) F (r x) ∙ sym (hyp4 e F r)) (~ i))
--                  (cong (g e) (br' x (fst e x) F (r x)))
--                  (cong (f (fst e x)) (br' x (fst e x) F (r x))))
--     →  mjo' → B
--   mjo-ind* B b f g h1 h2 h3 h4 h5 h6 (aa' (inl x)) = f x (aa' (inl x))
--   mjo-ind* B b f g h1 h2 h3 h4 h5 h6 (aa' (inr x)) = g x (aa' (inr x))
--   mjo-ind* B b f g h1 h2 h3 h4 h5 h6 (bb' x) = b x
--   mjo-ind* B b f g h1 h2 h3 h4 h5 h6 (ab' x x₁ x₂) = f x₁ (ab' x x₁ x₂)
--   mjo-ind* B b f g h1 h2 h3 h4 h5 h6 (ar' x (inl x₂) b₁ x₁ i) = f x₂ (ar' x (inl x₂) b₁ x₁ i)
--   mjo-ind* B b f g h1 h2 h3 h4 h5 h6 (ar' x (inr e) F r i) =
--     (cong (g e) (ar' x (inr e) F r) ∙ h1 x e F r) i
--   mjo-ind* B b f g h1 h2 h3 h4 h5 h6 (br' x y F r i) =
--     (cong (f y) (br' x y F r) ∙ h2 x y F r) i
--   mjo-ind* B b f g h1 h2 h3 h4 h5 h6 (rr* (inl y) F r i) = (cong (f y) (rr* (inl y) F r) ∙ h3 y F r) i
--   mjo-ind* B b f g h1 h2 h3 h4 h5 h6 (rr* (inr e) F r i) = (cong (g e) (rr* (inr e) F r) ∙ h4 e F r) i
--   mjo-ind* B b f g h1 h2 h3 h4 h5 h6 (rr** (inl y) F r x i j) =
--     hcomp (λ k → λ {(i = i0) → compPath-filler' (λ i₁ → f y (rr* (inl y) F r i₁)) (h3 y F r) k j
--                    ; (i = i1) → compPath-filler' (λ i₁ → f y (br' x y F (r x) i₁)) (h2 x y F (r x)) k j
--                    ; (j = i0) → f y (rr** (inl y) F r x i (~ k))
--                    ; (j = i1) → b F})
--           (h5 x y F r i j)
--   mjo-ind* B b f g h1 h2 h3 h4 h5 h6 (rr** (inr e) F r x i j) =
--     hcomp (λ k → λ {(i = i0) → compPath-filler (λ i₁ → g e (rr* (inr e) F r i₁)) (h4 e F r) k j
--                    ; (i = i1) → ((λ i₁ → f (fst e x) (br' x (fst e x) F (r x) i₁))
--                                  ∙ compPath-filler (h2 x (fst e x) F (r x)) (sym (h4 e F r)) (~ k)) j
--                    ; (j = i0) → ((λ i₁ → g e (ar' x (inr e) (F x) (r x) i₁)) ∙ h1 x e (F x) (r x)) i
--                    ; (j = i1) → h4 e F r k})
--      (hcomp (λ k → λ {(i = i0) → g e (rr** (inr e) F r x (~ k) j)
--                      ; (i = i1) → ((λ i₁ → f (fst e x) (br' x (fst e x) F (r x) i₁))
--                                  ∙ compPath-filler (h2 x (fst e x) F (r x)) (sym (h4 e F r)) i1) j
--                      ; (j = i0) → compPath-filler' (λ i₁ → g e (ar' x (inr e) (F x) (r x) i₁)) (h1 x e (F x) (r x)) k i
--                      ; (j = i1) → g e (bb' F)})
--        (hcomp (λ k → λ {(i = i0) → g e (br' x (fst e x) F (r x) j)
--                      ; (i = i1) → compPath-filler (cong (f (fst e x)) (br' x (fst e x) F (r x)))  (h2 x (fst e x) F (r x) ∙ sym (h4 e F r)) k j
--                      ; (j = i0) → h1 x e (F x) (r x) i
--                      ; (j = i1) → (h2 x (fst e x) F (r x) ∙ sym (h4 e F r)) (~ i ∨ k)})
--               (h6 x e  F r i j)))

-- {-
--   mjo-ind* : (B : Type)
--     → (b : ((x : fst X) → B' x) → B)
--     → (f : fst Y → mjo' → B)
--     → (g : fst X ≃ fst Y → mjo' → B)
--     → (hyp1 : (x : fst X) (e : fst X ≃ fst Y) (F : B' x) (r : R' x (fst e x) F)
--               → g e ((ab' x (fst e x) F)) ≡ f (fst e x) (ab' x (fst e x) F))
--     → (hyp2 : (x : fst X) (y : fst Y) (F : (x : fst X) → B' x) (r : R' x y (F x))
--             → f y (bb' F) ≡ b F)
--     → (hyp3 : (y : fst Y) (F : (x : fst X) → B' x) (r : (x : fst X) → R' x y (F x))
--             → f y (bb' F) ≡ b F )
--     → (hyp4 : (e : fst X ≃ fst Y) (F : (x : fst X) → B' x) (r : (x : fst X) → R' x (fst e x) (F x))
--               → g e (bb' F) ≡ b F)
--     → (hyp5 : (x : fst X) (y : fst Y) (F : (x₁ : fst X) → B' x₁) (r : (x₁ : fst X) → R' x₁ y (F x₁))
--             → hyp3 y F r ≡ hyp2 x y F (r x))
--     → (hyp6 : (x : fst X) (e : fst X ≃ fst Y) (F : (x₁ : fst X) → B' x₁) (r : (x₁ : fst X) → R' x₁ (fst e x₁) (F x₁))
--             → PathP (λ i → hyp1 x e (F x) (r x) i ≡ (hyp2 x (fst e x) F (r x) ∙ sym (hyp4 e F r)) (~ i))
--                  (cong (g e) (br' x (fst e x) F (r x)))
--                  (cong (f (fst e x)) (br' x (fst e x) F (r x))))
--     →  mjo' → B
-- -}
-- H1-b : (X : RP∞) (A : fst X → Bool → Pointed₀)
--   → mjo' X Bool* A → SM Bool* λ y → SM∙ X λ x → A x y
-- H1-b X A (aa' x) = inl true
-- H1-b X A (bb' f) = inr λ y → inr λ x → f x y
-- H1-b X A (ab' x x₁ x₂) = {!!}
-- H1-b X A (ar' x f b x₁ i) = {!f!}
-- H1-b X A (br' x y b x₁ i) = {!!}
-- H1-b X A (rr* a b x i) = {!!}
-- H1-b X A (rr** a b r x i i₁) = {!!}

-- H1 : (X Y : RP∞) (y : fst Y) → (A : fst X → fst Y → Pointed₀)
--   → mjo' X Y A → SM Y λ y → SM∙ X λ x → A x y
-- H1 X = J2-elem _ .fst (H1-b X)


-- module _ where
--   Tₗ : (X : RP∞) (Y : RP∞) (y : fst Y) (A : fst X → fst Y → Pointed₀) (B : Type)
--     → (bb : ((x : fst X) (y : fst Y) → A x y .fst))
--     → Type
--   Tₗ X Y y A B b =
--     Σ[ aa ∈ B ]
--       Σ[ ab' ∈ ((x : fst X) → B* x → B) ]
--        Σ[ ar' ∈ ((x : fst X) → (b : B* x) → R* x y b → aa ≡ ab' x b) ]
--          {!(x : fst X) (y : fst Y) (b : (x : fst X) → B' x)
--         → R' x y (b x)
--         → ab' x y (b x) ≡ bb' b!}
--     where
--     B* = B' X Y A
--     R* = R' X Y A

-- --   Tᵣ : Σ[ ? ∈ B ] {!!}
-- --   Tᵣ = {!!}

-- -- module _ (X Y : RP∞) (A : fst X → fst Y → Type) (B : Type)
-- --   (bb : ((x : fst X) (y : fst Y) → A x y) → B) where
-- --   Tₗ : Σ[ aa' ∈ B ] {!!}
-- --   Tₗ = {!!}

-- -- mjo-ind : (B : (X Y : RP∞) (A : fst X → fst Y → Type) → Type)
-- --   → ((X Y : RP∞) (y : fst Y) (A : fst X → fst Y → Type)
-- --         → {!!})
-- --   → {!!}
-- -- mjo-ind = {!!}
  


-- --   -- inlo : fst Y → TYP
-- --   -- inlo = inl
-- --   -- inro : _ → TYP
-- --   -- inro = inr
-- --   -- inli : (y : _) → _ → SM X λ x → A x y
-- --   -- inli y = inl
-- --   -- inri : (y : _) → _ → SM X λ x → A x y
-- --   -- inri y = inr
  
  

-- --   -- smashΠ : mjo' → SM Y λ y → SM∙ X λ x → A x y
-- --   -- smashΠ (aa' (inl x)) = inl x
-- --   -- smashΠ (aa' (inr x)) = inr λ y → inl (invEq x y)
-- --   -- smashΠ (bb' f) = inr λ x → inr (λ y → f y x)
-- --   -- smashΠ (ab' x y b) = inr (λ y → inr (λ x → A x y .snd)) -- inl y
-- --   -- smashΠ (ar' x (inl y) b x₁ i) = help i -- inl y -- help i
-- --   --   where
-- --   --   cool : (y : fst Y) → _
-- --   --   cool y = CasesRPβ Y {A = λ y → SM X λ x → A x y} y (SM∙ X (λ x₂ → A x₂ y) .snd) (snd (SM∙ X (λ x₂ → A x₂ (not* Y y))))

-- --   --   P : (y' : fst Y)
-- --   --     → CasesRP Y {A = λ y → SM X λ x → A x y}
-- --   --         y (SM∙ X (λ x₂ → A x₂ y) .snd)
-- --   --         (snd (SM∙ X (λ x₂ → A x₂ (not* Y y)))) y'
-- --   --         ≡ inr (λ x₂ → A x₂ y' .snd)
-- --   --   P = CasesRP Y y (cool y .fst) (cool y .snd)

-- --   --   help : inlo y ≡ inr (λ y₁ → inr (λ x₂ → A x₂ y₁ .snd))
-- --   --   help = push (y , SM∙ X (λ x₂ → A x₂ y) .snd)
-- --   --        ∙ cong inro (funExt P)

-- --   -- smashΠ (ar' x (inr e) b x₁ i) = help i -- help i
-- --   --   where
-- --   --   cool : (y' : fst Y) (x : fst X) → _
-- --   --   cool y' x = CasesRPβ X {A = λ x → A x y' .fst} (invEq e y') (snd (A (invEq e y') y'))
-- --   --     (snd (A (not* X (invEq e y')) y'))
-- --   --   {-
-- --   --     CasesRP X (invEq e y') (snd (A (invEq e y') y'))
-- --   --     (snd (A (not* X (invEq e y')) y'))
-- --   --     ≡ A x y' .snd
-- --   --     -}

-- --   --   P : (y' : fst Y) (x : fst X)
-- --   --     → CasesRP X {A = λ x → A x  y' .fst} (invEq e y') (snd (A (invEq e y') y'))
-- --   --          (snd (A (not* X (invEq e y')) y')) x
-- --   --       ≡ A x y' .snd
-- --   --   P y' = CasesRP X (invEq e y')
-- --   --                    (cool y' x .fst)
-- --   --                    (cool y' x .snd)
    
-- --   --   help : inro (λ y → inl (invEq e y)) ≡ inr (λ y₁ → inr (λ x₂ → A x₂ y₁ .snd))
-- --   --   help = cong inro (funExt λ y' → push (invEq e y' , snd (A (invEq e y') y'))
-- --   --                  ∙ cong (inri y')
-- --   --                  (funExt (P y')))
-- --   -- smashΠ (br' x y b (v , p) i) = {!!}
-- --   --   where
-- --   --   b-id : Path ((x : fst X) → _) (λ x → b x y) (CasesRP X (¬' x) (b (not* X x) y) (A _ y .snd))
-- --   --   b-id = funExt (CasesRP X x (funExt⁻ (sym p) y ∙ {!casesRP!} ∙ {!!}) (sym (CasesRPβ X (¬' x) (b (not* X x) y) (A _ y .snd) .fst)))

-- --   --   help : (y' : fst Y)
-- --   --     → Path (SM X (λ x → A x y')) -- ((x : fst X) → _)
-- --   --             (inr λ x → b x y')
-- --   --             (CasesRP Y {A = λ y → SM X (λ x → A x y)}
-- --   --               y (pt (SM∙ X (λ x → A x y))) -- (inr λ x → b x (not* Y y))
-- --   --                 (inr (λ x → b x (not* Y y))) y')
-- --   --   help = CasesRP Y y
-- --   --     (cong (inri y) (b-id)
-- --   --    ∙ sym (push (¬' x , b (¬' x) y))
-- --   --    ∙ (push (¬' x , A (¬' x) y .snd)
-- --   --    ∙ {!!})
-- --   --    ∙ sym ((CasesRPβ Y {A = λ y → SM X (λ x → A x y)} y
-- --   --            (pt (SM∙ X (λ x₁ → A x₁ y))) (inr (λ x₁ → b x₁ (not* Y y)))) .fst))
-- --   --     (sym ((CasesRPβ Y {A = λ y → SM X (λ x → A x y)} y
-- --   --            (pt (SM∙ X (λ x₁ → A x₁ y))) (inr (λ x₁ → b x₁ (not* Y y)))) .snd))
-- --   --     {- (cong (inri (not* Y y))
-- --   --       (funExt (CasesRP X x (sym (funExt⁻ p (not* Y y))
-- --   --                          ∙ CasesRPβ Y {A = λ y → A x y .fst} y v (pt (A x (not* Y y))) .snd
-- --   --                          ∙ {!!})
-- --   --                            {!!}))
-- --   --     ∙ {!!}) -}
-- --   -- smashΠ (rr* (inl x₁) b x i) = {!!}
-- --   -- smashΠ (rr* (inr x₁) b x i) = {!!}
-- --   -- smashΠ (rr** a b r x i i₁) = {!!}
