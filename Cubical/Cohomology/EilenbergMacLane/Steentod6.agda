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

module _ {ℓ : Level} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) where
  open 2-elter' I (fst J) A
  ΠR-base*er : ΠR-base* → (i : fst I) → joinR-gen (fst J) (A i)
  ΠR-base*er (inl x) i = inlR (fst x , snd x i)
  ΠR-base*er (inr x) i = inrR (x i)
  ΠR-base*er (push a i) i' = push* (fst a , snd a i' (fst a)) (snd a i') refl i

  inler-push : (i' : fst I) (a : fst J)
    (b : A i' a × ((j : fst J) → A (notI i') j)) (i : fst I)
    → Path (joinR-gen (fst J) (A i))
            (elimI {B = λ i → joinR-gen (fst J) (A i)} i' (inlR (a , fst b)) (inrR (snd b)) i)
            (inlR (a , elimI {B = λ i → A i a} i' (b .fst) (b .snd a) i))
  inler-push i' a b =
    elimI i' (elimIβ {B = λ i → joinR-gen (fst J) (A i)} i' (inlR (a , fst b)) (inrR (snd b)) .fst
            ∙∙ refl ∙∙ (λ j → inlR (a , elimIβ {B = λ i → A i a} i' (b .fst) (b .snd a) .fst (~ j))))
              (elimIβ {B = λ i → joinR-gen (fst J) (A i)} i' (inlR (a , fst b)) (inrR (snd b)) .snd
             ∙∙ sym (push* (a , (b .snd a)) (snd b) refl)
             ∙∙ λ j → inlR (a , elimIβ {B = λ i → A i a} i' (b .fst) (b .snd a) .snd (~ j)))

  inler : ΠR-extend**↑ → (i : fst I) → joinR-gen (fst J) (A i)
  inler (2-elter'.inl (i' , a , b)) =
    elimI {B = λ i → joinR-gen (fst J) (A i)} i' (inlR a) (inrR b)
  inler (2-elter'.inr x) = ΠR-base*er x
  inler (2-elter'.pashₗ i' (a , b) k) i = inler-push i' a b i k

  inler-coh-ppl : (e : fst I ≃ fst J) (f : (i₁ : fst I) (j : fst J) → A i₁ j) (i : fst I)
    → Path (joinR-gen (fst J) (A i)) (inrR (f i)) (inlR (fst e i , asPushoutBack→ᵣ-pre e (ppl f) i))
  inler-coh-ppl e f i = sym (push* (fst e i , f i (fst e i)) (f i) refl)

  inler-coh-ppr₁ : (e : fst I ≃ fst J) (i₁ : fst I)
    (a : A i₁ (fst e i₁)) (b : TotΠ (A (notI i₁)))
    → Path (joinR-gen (fst J) (A i₁))
            (elimI {λ i → joinR-gen (fst J) (A i)} i₁ (inlR (fst e i₁ , a)) (inrR b) i₁)
            (inlR (fst e i₁
                 , elimI {B = λ i → A i (fst e i)} i₁ a (b (fst e (notI i₁))) i₁))
  inler-coh-ppr₁ e i₁ a b =
       elimIβ i₁ (inlR (fst e i₁ , a)) (inrR b) .fst
    ∙∙ refl
    ∙∙ λ j → inlR (fst e i₁
                   , elimIβ {B = λ i → A i (fst e i)} i₁ a (b (fst e (notI i₁))) .fst (~ j))

  inler-coh-ppr₂ : (e : fst I ≃ fst J) (i₁ : fst I)
    (a : A i₁ (fst e i₁)) (b : TotΠ (A (notI i₁)))
    → Path (joinR-gen (fst J) (A (notI i₁)))
            (elimI {λ i → joinR-gen (fst J) (A i)} i₁ (inlR (fst e i₁ , a)) (inrR b) (notI i₁))
            (inlR (fst e (notI i₁) , elimI {B = λ i → A i (fst e i)} i₁ a (b (fst e (notI i₁))) (notI i₁)))
  inler-coh-ppr₂ e i₁ a b =
       elimIβ i₁ (inlR (fst e i₁ , a)) (inrR b) .snd
    ∙∙ sym (push* (fst e (notI i₁) , b (fst e (notI i₁))) b refl)
    ∙∙ λ j → inlR (fst e (notI i₁)
                   , elimIβ {B = λ i → A i (fst e i)} i₁ a (b (fst e (notI i₁))) .snd (~ j))

  inler-coh-pplr : (e : fst I ≃ fst J) (i₁ : fst I) (f : (i₃ : fst I) (j : fst J) → A i₃ j)
    → (i : fst I)
    → PathP (λ i₂ → inler (asPushoutBack→ₗ↑ (e , pplr i₁ f i₂)) i
                    ≡ inlR (fst e i , asPushoutBack→ᵣ-pre e (pplr i₁ f i₂) i))
             (inler-coh-ppl e f i)
             (elimI {B = λ i → inler (asPushoutBack→ₗ↑ (e , ppr i₁ (f i₁ (fst e i₁)) (f (notI i₁)))) i
                       ≡ inlR (fst e i , asPushoutBack→ᵣ-pre e (ppr i₁ (f i₁ (fst e i₁)) (f (notI i₁))) i)} i₁
                    (inler-coh-ppr₁ e i₁ _ _)
                    (inler-coh-ppr₂ e i₁ _ _) i)
  inler-coh-pplr e i₁ f =
    elimI i₁
      ((λ i j → hcomp (λ k → λ {(i = i0) → push* (fst e i₁ , f i₁ (fst e i₁)) (f i₁) (λ _ → f i₁ (fst e i₁)) (~ j ∧ k)
                                ; (i = i1) → {!!}
                                ; (j = i0) → inler (doubleCompPath-filler
                                                      (λ i₂ → inr (push (fst e i₁ , f) (~ i₂)))
                                                      ((λ k → inr (inl (fst e i₁
                                                                   , elimIη (λ j → f j (fst e i₁)) i₁ (~ k)))))
                                                      (sym (pashₗ i₁ ((fst e i₁) , ((f i₁ (fst e i₁)) , (f (notI i₁)))))) k i) i₁
                                ; (j = i1) → {!!}})
                       {!!})
      ▷ sym (elimIβ i₁ (inler-coh-ppr₁ e i₁ (f i₁ (fst e i₁)) (f (notI i₁)))
            (inler-coh-ppr₂ e i₁ (f i₁ (fst e i₁)) (f (notI i₁))) .fst))
      {!PathP
      (λ i₂ →
         inler (asPushoutBack→ₗ↑ (e , pplr i₁ f i₂)) i₁ ≡
         inlR (fst e i₁ , asPushoutBack→ᵣ-pre e (pplr i₁ f i₂) i₁))
      (inler-coh-ppl e f i₁)
      (inler-coh-ppr₁ e i₁ (f i₁ (fst e i₁)) (f (notI i₁)))!}

  inler-coh : (e : fst I ≃ fst J) (t : asPushoutBack e) (i : fst I)
    → inler (asPushoutBack→ₗ↑ (e , t)) i
     ≡ inlR ((fst e i) , (asPushoutBack→ᵣ-pre e t i))
  inler-coh e (2-elter'.ppl f) i = inler-coh-ppl e f i
  inler-coh e (2-elter'.ppr i₁ a b) = {!!}
  inler-coh e (2-elter'.pplr i₁ f i₂) i = inler-coh-pplr e i₁ f i i₂

  asPushout'→join : asPushout' → (i : fst I) → joinR-gen (fst J) (A i)
  asPushout'→join (inl x) = inler x
  asPushout'→join (inr (e , t)) i = inlR ((fst e i) , (t i))
  asPushout'→join (push (e , t) k) i = inler-coh e t i k


module wBool {ℓ : Level} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ) where
  open 2-elter' (RP∞'· ℓ) (fst J) A

  asPushout'→join' : asPushout' → (i : Bool) → joinR-gen (fst J) (A i)
  asPushout'→join' (inl (2-elter'.inl (false , b))) false = inlR (fst b)
  asPushout'→join' (inl (2-elter'.inl (false , b))) true = inrR (snd b)
  asPushout'→join' (inl (2-elter'.inl (true , b))) false = inrR (snd b)
  asPushout'→join' (inl (2-elter'.inl (true , b))) true = inlR (fst b)
  asPushout'→join' (inl (2-elter'.inr (inl x))) i = inlR (fst x , snd x i)
  asPushout'→join' (inl (2-elter'.inr (inr x))) i = inrR (x i)
  asPushout'→join' (inl (2-elter'.inr (push a i₁))) i = push* (fst a , snd a i (fst a)) (snd a i) refl i₁
  asPushout'→join' (inl (2-elter'.pashₗ false b i₂)) false = inlR (b .fst , b .snd .fst)
  asPushout'→join' (inl (2-elter'.pashₗ true b i₂)) false = push* (b .fst , b .snd .snd (b .fst)) (b .snd .snd) refl (~ i₂)
  asPushout'→join' (inl (2-elter'.pashₗ false b i₂)) true = push* (b .fst , b .snd .snd (b .fst)) (b .snd .snd) refl (~ i₂)
  asPushout'→join' (inl (2-elter'.pashₗ true b i₂)) true = inlR (b .fst , b .snd .fst)
  asPushout'→join' (inr (e , f)) i = inlR (fst e i , f i)
  asPushout'→join' (push (e , 2-elter'.ppl f) i₁) i = push* (fst e i , f i (fst e i)) (f i) refl (~ i₁)
  asPushout'→join' (push (e , 2-elter'.ppr false a b) i₁) false = inlR (fst e false , a)
  asPushout'→join' (push (e , 2-elter'.ppr false a b) i₁) true = push* (fst e true , b (fst e true)) b refl (~ i₁)
  asPushout'→join' (push (e , 2-elter'.ppr true a b) i₁) false = push* (fst e false , b (fst e false)) b refl (~ i₁)
  asPushout'→join' (push (e , 2-elter'.ppr true a b) i₁) true = inlR (fst e true , a)
  asPushout'→join' (push (e , 2-elter'.pplr i₂ f i₃) i₁) i = {!!}

-- f₁eq : ∀ {ℓ} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
--   → 2-elter.ΠR-extend I (fst J) A
--    ≃ TotΠ (λ i → joinR-gen (fst J) (A i))
-- fst (f₁eq I J A) = 2-elter.ΠR-extend→Π I (fst J) A
-- snd (f₁eq I J A) = ΠR-extend→Π-equiv I J A

-- f₁ : ∀ {ℓ} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
--   → TotΠ (λ i → joinR-gen (fst J) (A i))
--   → 2-elter.ΠR-extend I (fst J) A
-- f₁ I J A = invEq (f₁eq I J A)

-- f₂eq : ∀ {ℓ} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
--   → 2-elter'.ΠR-extend I (fst J) A
--    ≃ 2-elter.ΠR-extend I (fst J) A
-- f₂eq I J A = isoToEquiv (Π-extend→ I J A)

-- f₃ : ∀ {ℓ} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
--   → 2-elter'.ΠR-extend I (fst J) A
--    → joinR-gen (fst J) (λ j → joinR-gen (fst I) (λ i → A i j))
-- f₃ = ΠR-extendOut-full-lets

-- inrmap : ∀ {ℓ} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
--   → TotΠ (λ i → joinR-gen (fst J) (A i))
--   → joinR-gen (fst J) (λ j → joinR-gen (fst I) (λ i → A i j))
-- inrmap I J A p = f₃ I J A (invEq (f₂eq I J A) (f₁ I J A p))

-- inlmap-bool : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
--   → joinR-gen (fst J) (A true)
--   → joinR-gen (fst J) (λ j → joinR-gen Bool (λ i → A i j)) 
-- inlmap-bool J A (inlR (j , a)) = inlR (j , (inlR (true , a)))
-- inlmap-bool J A (inrR x) = inrR λ j → inlR (true , x j)
-- inlmap-bool J A (push* (j , a) b x i) =
--   push* (j , inlR (true , a)) (λ i₁ → inlR (true , b i₁)) (λ i → inlR (true , x i)) i

-- inl-map-gen : ∀ {ℓ} (I : RP∞' ℓ)
--    (J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
--   → (i : fst I)
--   → joinR-gen (fst J) (A i)
--   → joinR-gen (fst J) (λ j → joinR-gen (fst I) (λ i → A i j))  
-- inl-map-gen I J A i (inlR (j , a)) = inlR (j , inlR (i , a))
-- inl-map-gen I J A i (inrR x) = inrR λ j → inlR (i , x j)
-- inl-map-gen I J A i (push* a b x i₁) =
--   push* (fst a , inlR (i , snd a)) (λ k → inlR (i , b k)) (λ i' → inlR (i , x i')) i₁

-- inl-map : ∀ {ℓ} (I : RP∞' ℓ) (i : fst I)
--    (J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
--   → joinR-gen (fst J) (A i)
--   → joinR-gen (fst J) (λ j → joinR-gen (fst I) (λ i → A i j))  
-- inl-map = JRP∞' inlmap-bool

-- tlem'-inr : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
--   → (x : _)
--   → f₃ (RP∞'· ℓ) J A {!!}
--   ≡ {!!}
-- tlem'-inr = {!!}

-- tlem' : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
--   → (x : _)
--   → f₃ (RP∞'· ℓ) J A x
--    ≡ inlmap-bool J A
--       (ΠR-extend→Π-alt J A (f₂eq (RP∞'· ℓ) J A .fst x) true)
-- tlem' J A (inl (false , snd₁)) =
--   push* (snd₁ .fst .fst
--         , inrR (CasesBool false (snd₁ .fst .snd) (snd₁ .snd _)))
--         (λ i → inlR (true , snd₁ .snd i)) (push* (true , {!!}) {!!} {!!})
-- tlem' J A (inl (true , snd₁)) = {!!}
-- tlem' J A (inr x) = {!x!}
-- tlem' J A (push (x , k) i) = {!x!}

-- tlem** : ∀ {ℓ} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
--   → (x : 2-elter'.asPushout I (fst J) A)
--   → (i : fst I)
--   → f₃ I J A (2-elter'.asPushout→ΠR-extend I (fst J) A x)
--   ≡ inl-map-gen I J A i
--       (2-elter.ΠR-extend→Π I (fst J) A
--         (f₂eq I J A .fst (2-elter'.asPushout→ΠR-extend I (fst J) A x)) i)
-- tlem** {ℓ} I = asPushout-elim' I (λ J A x → (i : fst I) → f₃ I J A
--                        (2-elter'.asPushout→ΠR-extend I (fst J) A x)
--                        ≡ inl-map-gen I J A i
--                            (2-elter.ΠR-extend→Π I (fst J) A
--                              (f₂eq I J A .fst (2-elter'.asPushout→ΠR-extend I (fst J) A x)) i))
--                        LEFT
--                        {!!}
--                        {!!}
--   where
--   open 2-elter'
--   LEFT : (J₁ : RP∞' ℓ) (A : fst I → fst J₁ → Type ℓ)
--       (x : 2-elter'.ΠR-extend** I (fst J₁) A) (i : fst I) →
--       f₃ I J₁ A (2-elter'.asPushout→ΠR-extend I (fst J₁) A (inl x)) ≡
--       inl-map-gen I J₁ A i
--       (2-elter.ΠR-extend→Π I (fst J₁) A
--        (f₂eq I J₁ A .fst
--         (2-elter'.asPushout→ΠR-extend I (fst J₁) A (inl x)))
--        i)
--   LEFT J A =
--     ΠR-extend**-elim I (fst J) A
--       {!!}
--       {!!}
--       {!!}

-- tlem : ∀ {ℓ} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
--   → (x : _)
--   → (i : fst I)
--   → f₃ I J A x
--   ≡ inl-map-gen I J A i
--     (f₁eq I J A .fst
--       (f₂eq I J A .fst x) i)
-- tlem I J A x i = {!!}



-- main-coh' : ∀ {ℓ} (I : RP∞' ℓ) (J : RP∞' ℓ)
--   (A : fst I → fst J → Type ℓ)
--    (b : TotΠ (λ i → joinR-gen (fst J) (A i)))
--    (i' : fst I)
--    (a : joinR-gen (fst J) (A i'))
--    (x : b i' ≡ a)
--    → inl-map-gen I J A i' a ≡ inrmap I J A b
-- main-coh' I J A b i' a x =
--   cong (inl-map-gen I J A i')
--     (sym x
--     ∙ funExt⁻ (sym (secEq myF b)) i')
--   ∙ sym (tlem I J A (invEq myF b) i')
--   where
--   myF : 2-elter'.ΠR-extend I (fst J) A
--      ≃ TotΠ (λ i → joinR-gen (fst J) (A i))
--   myF = compEquiv (f₂eq I J A) (f₁eq I J A)

-- L1 : ∀ {ℓ} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
--   → joinR-gen (fst I) (λ i → joinR-gen (fst J) (A i))
--   → joinR-gen (fst J) (λ j → joinR-gen (fst I) (λ i → A i j))
-- L1 I J A (inlR (i , a)) = inl-map-gen I J A i a
-- L1 I J A (inrR x) = inrmap I J A x
-- L1 I J A (push* (i' , a) b x i) = main-coh' I J A b i' a x i
