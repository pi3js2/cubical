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
open import Cubical.Cohomology.EilenbergMacLane.Steenrod5


module Cubical.Cohomology.EilenbergMacLane.Steentod6 where
open import Cubical.HITs.Join
open import Cubical.Functions.FunExtEquiv

f₁eq : ∀ {ℓ} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
  → 2-elter.ΠR-extend I (fst J) A
   ≃ TotΠ (λ i → joinR-gen (fst J) (A i))
fst (f₁eq I J A) = 2-elter.ΠR-extend→Π I (fst J) A
snd (f₁eq I J A) = ΠR-extend→Π-equiv I J A

f₁ : ∀ {ℓ} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
  → TotΠ (λ i → joinR-gen (fst J) (A i))
  → 2-elter.ΠR-extend I (fst J) A
f₁ I J A = invEq (f₁eq I J A)

f₂eq : ∀ {ℓ} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
  → 2-elter'.ΠR-extend I (fst J) A
   ≃ 2-elter.ΠR-extend I (fst J) A
f₂eq I J A = isoToEquiv (Π-extend→ I J A)

f₃ : ∀ {ℓ} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
  → 2-elter'.ΠR-extend I (fst J) A
   → joinR-gen (fst J) (λ j → joinR-gen (fst I) (λ i → A i j))
f₃ = ΠR-extendOut-full-lets

inrmap : ∀ {ℓ} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
  → TotΠ (λ i → joinR-gen (fst J) (A i))
  → joinR-gen (fst J) (λ j → joinR-gen (fst I) (λ i → A i j))
inrmap I J A p = f₃ I J A (invEq (f₂eq I J A) (f₁ I J A p))

inlmap-bool : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
  → joinR-gen (fst J) (A true)
  → joinR-gen (fst J) (λ j → joinR-gen Bool (λ i → A i j)) 
inlmap-bool J A (inlR (j , a)) = inlR (j , (inlR (true , a)))
inlmap-bool J A (inrR x) = inrR λ j → inlR (true , x j)
inlmap-bool J A (push* (j , a) b x i) =
  push* (j , inlR (true , a)) (λ i₁ → inlR (true , b i₁)) (λ i → inlR (true , x i)) i

inl-map : ∀ {ℓ} (I : RP∞' ℓ) (i : fst I)
   (J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
  → joinR-gen (fst J) (A i)
  → joinR-gen (fst J) (λ j → joinR-gen (fst I) (λ i → A i j))  
inl-map = JRP∞' inlmap-bool

tlem : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
  → (x : _)
  → f₃ (RP∞'· ℓ) J A x
   ≡ inlmap-bool J A
      (f₁eq (RP∞'· ℓ) J A .fst (f₂eq (RP∞'· ℓ) J A .fst x) true)
tlem J A x =
    {!f₃ ? J A!}
  ∙ cong (inlmap-bool J A)
      (ΠR-extend→Π-alt≡ {J = J} A (f₂eq (RP∞'· _) J A .fst x) true)

-- tlem J A (inl (false , snd₁)) = {!snd₁!}
-- tlem J A (inl (true , snd₁)) = {!!}
-- tlem J A (inr (inl (inl x , snd₁))) i =
--   inlR (x , (push* (true , snd₁ true) snd₁ refl (~ i)))
-- tlem J A (inr (inl (inr x , snd₁))) = {!!}
-- tlem J A (inr (inr x)) = {!!}
-- tlem J A (inr (push a i)) = {!!}
-- tlem J A (push (false , snd₁) i) = {!!}
-- tlem J A (push (true , snd₁) i) = {!!}

-- main-coh : ∀ {ℓ} (I : RP∞' ℓ) (i' : fst I)
--    (J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
--    (a : joinR-gen (fst J) (A i'))
--    (b : TotΠ (λ i → joinR-gen (fst J) (A i)))
--    (x : b i' ≡ a)
--    → inl-map I i' J A a ≡ inrmap I J A b
-- main-coh {ℓ} = JRP∞' λ J A a b x
--   → (λ i → JRP∞'∙ {ℓ} {B = λ I i → (J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
--   → joinR-gen (fst J) (A i)
--   → joinR-gen (fst J) (λ j → joinR-gen (fst I) (λ i → A i j))} inlmap-bool i J A a)
--   ∙ cong (inlmap-bool J A)
--        (sym x
--       ∙ funExt⁻ (sym (secEq (myF J A) b)) true)
--   ∙ (sym (tlem J A (invEq (myF J A) b)))
--   where
--   myF : (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
--     → 2-elter'.ΠR-extend (RP∞'· ℓ) (fst J) A
--      ≃ TotΠ (λ i → joinR-gen (fst J) (A i))
--   myF J A = compEquiv (f₂eq (RP∞'· ℓ) J A) (f₁eq (RP∞'· ℓ) J A)

-- L1 : ∀ {ℓ} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
--   → joinR-gen (fst I) (λ i → joinR-gen (fst J) (A i))
--   → joinR-gen (fst J) (λ j → joinR-gen (fst I) (λ i → A i j))
-- L1 I J A (inlR (i , a)) = inl-map I i J A a 
-- L1 I J A (inrR x) = inrmap I J A x
-- L1 I J A (push* (i' , a) b x i) = main-coh I i' J A a b x i
