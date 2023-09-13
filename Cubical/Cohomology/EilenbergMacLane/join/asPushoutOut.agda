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

open import Cubical.Cohomology.EilenbergMacLane.join.2elter

open import Cubical.Cohomology.EilenbergMacLane.join.2elter-alt
module Cubical.Cohomology.EilenbergMacLane.join.asPushoutOut where

open import Cubical.HITs.Join
open import Cubical.Functions.FunExtEquiv

module _ {ℓ : Level} (J : Type) (A : Bool →  J → Type ℓ) where
  module M* = 2-elter' (RP∞'· ℓ) J A
  open M*

  pree : joinR-gen J (A true) × joinR-gen J (A false) → asPushout
  pree (t , q) = {!q!}

module TT {ℓ : Level} (I : RP∞' ℓ) (J : Type) (A : fst I →  J → Type ℓ) where
  module M = 2-elter' I J A
  open M

  GOAL : Type _
  GOAL = (i : fst I) → joinR-gen J (A i)

  ΠR-base*→Goal : (i : fst I) → ΠR-base* → joinR-gen J (A i)
  ΠR-base*→Goal i (inl (j , a)) = inlR (j , a i)
  ΠR-base*→Goal i (inr x) = inrR (x i)
  ΠR-base*→Goal i (push (j , p) i₁) = push* (j , p i j) (p i) refl i₁

  coh₁-diag : (i : fst I) (e : left-push↑ₗ* i)
    → Path (joinR-gen J (A i))
            (elimI {B = λ i → joinR-gen J (A i)} i (inlR (e .fst , e .snd .fst)) (inrR (e .snd .snd)) i)
            (inlR (fst e , elimI {B = λ i → A i (fst e)} i (snd e .fst) (snd e .snd (fst e)) i))
  coh₁-diag i e =
      elimIβ {B = λ i → joinR-gen J (A i)} i (inlR (e .fst , e .snd .fst)) (inrR (e .snd .snd)) .fst
    ∙ cong inlR (cong (e .fst ,_) (sym (elimIβ {B = λ i → A i (fst e)} i (snd e .fst) (snd e .snd (fst e)) .fst)))

  coh₁-not : (i : fst I) (e : left-push↑ₗ* i)
    → Path (joinR-gen J (A (notI i)))
            (elimI {B = λ i → joinR-gen J (A i)} i (inlR (e .fst , e .snd .fst)) (inrR (e .snd .snd)) (notI i)) 
            (inlR (fst e , elimI {B = λ i → A i (fst e)} i (snd e .fst) (snd e .snd (fst e)) (notI i)))
  coh₁-not i e = elimIβ {B = λ i → joinR-gen J (A i)} i (inlR (e .fst , e .snd .fst)) (inrR (e .snd .snd)) .snd
               ∙∙ sym (push* (e .fst , e .snd .snd (e .fst)) (e .snd .snd) refl)
               ∙∙ cong inlR (cong (e .fst ,_) (sym (elimIβ {B = λ i → A i (fst e)} i (snd e .fst) (snd e .snd (fst e)) .snd)))

  coh₁ : (i₁ i : fst I) (e : left-push↑ₗ* i₁)
    → Path (joinR-gen J (A i))
            (elimI {B = λ i → joinR-gen J (A i)} i₁ (inlR (e .fst , e .snd .fst)) (inrR (e .snd .snd)) i)
            (inlR (fst e , elimI {B = λ i → A i (fst e)} i₁ (snd e .fst) (snd e .snd (fst e)) i))
  coh₁ i₁ =
    elimI i₁ (coh₁-diag i₁) (coh₁-not i₁)

  coh₂ : (i₁ i : fst I) (e : left-push↑ᵣ i₁)
    → Path (joinR-gen J (A i))
            (elimI {B = λ i → joinR-gen J (A i)} i₁ (inlR (fst e , snd e i₁ (fst e))) (inrR (snd e (notI i₁))) i)
            (inrR (snd e i))
  coh₂ i₁ =
    elimI i₁
      (λ e → elimIβ {B = λ i → joinR-gen J (A i)} i₁ (inlR (fst e , snd e i₁ (fst e))) (inrR (snd e (notI i₁))) .fst
            ∙ push* (fst e , snd e i₁ (fst e)) (snd e i₁) refl)
      λ e → elimIβ {B = λ i → joinR-gen J (A i)} i₁ (inlR (fst e , snd e i₁ (fst e))) (inrR (snd e (notI i₁))) .snd

  coh₂-diag : (i₁ : fst I) (e : left-push↑ᵣ i₁)
    → Path (joinR-gen J (A i₁))
            (elimI {B = λ i → joinR-gen J (A i)} i₁ (inlR (fst e , snd e i₁ (fst e))) (inrR (snd e (notI i₁))) i₁)
            (inrR (snd e i₁))
  coh₂-diag i₁ e =
      elimIβ {B = λ i → joinR-gen J (A i)} i₁ (inlR (fst e , snd e i₁ (fst e))) (inrR (snd e (notI i₁))) .fst
    ∙ push* (fst e , snd e i₁ (fst e)) (snd e i₁) refl

  module _ (i₁ : fst I) (e : fat*) where
    coh-coh-diag-side :
      Square {A =  A i₁ (fst e)} (refl {x = snd e i₁ (fst e)})
               (λ k → elimIηPushTop* i₁ (fst e) (snd e) k i₁)
               (sym (elimIβ {B = λ i → A i (fst e)} i₁ (snd e i₁ (fst e)) (snd e (notI i₁) (fst e)) .fst))
               (refl {x = snd e i₁ (fst e)})
    coh-coh-diag-side =
      flipSquare (cong sym (sym (elimIη-id {B = λ i → A i (fst e)} (λ x → snd e x (fst e)) i₁ .fst))
                  ◁ λ a b → elimIηPushTop* i₁ (fst e) (snd e) (a ∨ ~ b) i₁)

    coh-coh-not-side : 
      Square {A =  A (notI i₁) (fst e)} (refl {x = snd e (notI i₁) (fst e)})
               (λ k → elimIηPushTop* i₁ (fst e) (snd e) k (notI i₁))
               (sym (elimIβ {B = λ i → A i (fst e)} i₁ (snd e i₁ (fst e)) (snd e (notI i₁) (fst e)) .snd))
               (refl {x = snd e (notI i₁) (fst e)})
    coh-coh-not-side =
      flipSquare (cong sym (sym (elimIη-id {B = λ i → A i (fst e)} (λ x → snd e x (fst e)) i₁ .snd))
                ◁ λ a b → elimIηPushTop* i₁ (fst e) (snd e) (a ∨ ~ b) (notI i₁))

  coh-coh-diag : (i₁ : fst I) (e : fat*)
    → Square {A = joinR-gen J (A i₁)}
      (λ i₃ → inlR (fst e , elimIηPushTop* i₁ (fst e) (snd e) i₃ i₁))
      (coh₂-diag i₁ e) -- (coh₂ i₁ i₁ e)
      (sym (coh₁-diag i₁ (fst e , snd e i₁ (fst e) , snd e (notI i₁)))) -- (sym (coh₁ i₁ i₁ (fst e , snd e i₁ (fst e) , snd e (notI i₁))))
      (push* (fst e , snd e i₁ (eval (inl (fst e)) i₁)) (snd e i₁) refl)
  coh-coh-diag i₁ e j k =
    hcomp (λ r → λ {(j = i0) → inlR (fst e , coh-coh-diag-side i₁ e r k)
                   ; (j = i1) → compPath-filler
                                  (elimIβ {B = λ i → joinR-gen J (A i)} i₁
                                    (inlR (fst e , snd e i₁ (fst e))) (inrR (snd e (notI i₁))) .fst)
                                  (push* (fst e , snd e i₁ (fst e)) (snd e i₁) refl)
                                  r k
                   ; (k = i0) → compPath-filler (elimIβ {B = λ i → joinR-gen J (A i)} i₁ (inlR (fst e , snd e i₁ (fst e))) (inrR (snd e (notI i₁))) .fst)
                                  (cong inlR (cong (e .fst ,_) (sym (elimIβ {B = λ i → A i (fst e)} i₁ (snd e i₁ (fst e)) (snd e (notI i₁) (fst e)) .fst)))) r (~ j)
                   ; (k = i1) → push* (fst e , snd e i₁ (fst e)) (snd e i₁) refl (j ∧ r)})
          (elimIβ {B = λ i → joinR-gen J (A i)} i₁ (inlR (fst e , snd e i₁ (fst e))) (inrR (snd e (notI i₁))) .fst (~ j ∨ k))

  coh₂-not : (i₁ : fst I) (e : fat*)
    → Path (joinR-gen J (A (notI i₁)))
            (elimI {B = λ i → joinR-gen J (A i)} i₁ (inlR (fst e , snd e i₁ (fst e))) (inrR (snd e (notI i₁))) (notI i₁))
            (inrR (snd e (notI i₁)))
  coh₂-not i₁ e = elimIβ {B = λ i → joinR-gen J (A i)} i₁ (inlR (fst e , snd e i₁ (fst e))) (inrR (snd e (notI i₁))) .snd

  coh-coh-not : (i₁ : fst I) (e : fat*)
    → Square {A = joinR-gen J (A (notI i₁))}
              (λ i₃ → inlR (fst e , elimIηPushTop* i₁ (fst e) (snd e) i₃ (notI i₁)))
              (coh₂-not i₁ e)
              (sym (coh₁-not i₁ (fst e , snd e i₁ (fst e) , snd e (notI i₁))))
              (push* (fst e , snd e (notI i₁) (eval (inl (fst e)) (notI i₁))) (snd e (notI i₁)) refl)
  coh-coh-not i₁ e j k =
    hcomp (λ r → λ {(j = i0) → inlR (fst e , coh-coh-not-side i₁ e r k)
                   ; (j = i1) → coh₂-not i₁ e (k ∨ ~ r)
                   ; (k = i0) → doubleCompPath-filler
                                  (elimIβ {B = λ i → joinR-gen J (A i)} i₁ (inlR (fst e , snd e i₁ (fst e))) (inrR (snd e (notI i₁))) .snd)
                                  (sym (push* (e .fst , e .snd (notI i₁) (e .fst)) (e .snd (notI i₁)) refl))
                                  (cong inlR (cong (e .fst ,_)
                                    (sym (elimIβ {B = λ i → A i (fst e)} i₁ (snd e i₁ (fst e)) (snd e (notI i₁) (fst e)) .snd)))) r (~ j)
                   ; (k = i1) → push* (fst e , snd e (notI i₁) (eval (inl (fst e)) (notI i₁))) (snd e (notI i₁)) refl j})
          (push* (fst e , snd e (notI i₁) (eval (inl (fst e)) (notI i₁))) (snd e (notI i₁)) refl j)


  record mega-coh' (i₁ i : fst I) : Type ℓ where
    field
      coher1 : ((e : left-push↑ₗ* i₁)
           → Path (joinR-gen J (A i))
             (elimI {B = λ i → joinR-gen J (A i)} i₁ (inlR (e .fst , e .snd .fst)) (inrR (e .snd .snd)) i)
             (inlR (fst e , elimI {B = λ i → A i (fst e)} i₁ (snd e .fst) (snd e .snd (fst e)) i)))
      simp-coh : (e : fst I ≃ J) (a : A i₁ (fst e i₁)) (b : (j : J) → A (notI i₁) j)
              → Path (joinR-gen J (A i))
                      (elimI {B = λ i → joinR-gen J (A i)} i₁ (inlR (fst e i₁ , a)) (inrR b) i)
                      (inlR ((fst e i) , (elimI {B = λ i → A i (fst e i) } i₁ a (b (fst e (notI i₁))) i)))

      coher2 : (e : fat*) → Path (joinR-gen J (A i))
                              (elimI {B = λ i → joinR-gen J (A i)} i₁ (inlR (fst e , snd e i₁ (fst e))) (inrR (snd e (notI i₁))) i)
                              (inrR (snd e i))
      coh-coher2₁ : (e : fat*) → Square {A = joinR-gen J (A i)}
              (λ i₃ → inlR (fst e , elimIηPushTop* i₁ (fst e) (snd e) i₃ i))
              (coher2 e)
              (sym (coher1 ((fst e) , (snd e i₁ (fst e) , snd e (notI i₁)))))
              (push* (fst e , snd e i (fst e)) (snd e i) refl)

      coh-coher2₂ : (e : fst I ≃ J) (f : (i₂ : fst I) (j₁ : J) → A i₂ j₁)
        → Square {A = joinR-gen J (A i)}
              (sym (coher2 ((fst e i₁) , f)))
              (cong inlR (cong (fst e i ,_) (funExt⁻ (sym (elimIη {B = λ i → A i (fst e i)} (λ x → f x (fst e x)) i₁)) i)))
              (sym (push* (fst e i , f i (fst e i)) (f i) refl) )
              (simp-coh e (f i₁ (fst e i₁)) (f (notI i₁)))

  open mega-coh'
  simp-coh-diag : (i₁ : fst I) (e : fst I ≃ J) (a : A i₁ (fst e i₁))
      (b : (j : J) → A (notI i₁) j) →
      Path (joinR-gen J (A i₁))
      (elimI {B = λ i → joinR-gen J (A i)} i₁ (inlR (fst e i₁ , a)) (inrR b) i₁)
      (inlR (fst e i₁ , elimI {B = λ i → A i (fst e i)} i₁ a (b (fst e (notI i₁))) i₁))
  simp-coh-diag i₁ e a b = elimIβ i₁ (inlR (fst e i₁ , a)) (inrR b) .fst
                          ∙ cong inlR (cong (fst e i₁ ,_) (sym (elimIβ i₁ a (b (fst e (notI i₁))) .fst)))

  simp-coh-not : (i₁ : fst I) (e : fst I ≃ J) (a : A i₁ (fst e i₁))
      (b : (j : J) → A (notI i₁) j) →
      Path (joinR-gen J (A (notI i₁)))
      (elimI {B = λ i → joinR-gen J (A i)} i₁ (inlR (fst e i₁ , a)) (inrR b) (notI i₁))
      (inlR (fst e (notI i₁) , elimI {B = λ i → A i (fst e i)} i₁ a (b (fst e (notI i₁))) (notI i₁)))
  simp-coh-not i₁ e a b =
       elimIβ {B = λ i → joinR-gen J (A i)} i₁ (inlR (fst e i₁ , a)) (inrR b) .snd
    ∙∙ sym (push* ((fst e (notI i₁)) , (b (fst e (notI i₁)))) b refl)
    ∙∙ cong inlR (cong (fst e (notI i₁) ,_) (sym (elimIβ {B = λ i → A i (fst e i)} i₁ a (b (fst e (notI i₁))) .snd)))

  module _ (i₁ : fst I) (e : fst I ≃ J) (f : (i : fst I) (j : J) → A i j) where
    diag-help₂ : Square (refl {x = f i₁ (fst e i₁)})
                        (funExt⁻ (sym (elimIη (λ x → f x (fst e x)) i₁)) i₁)
                        (refl {x = f i₁ (fst e i₁)})
                        (sym (elimIβ {B = λ i → A i (fst e i)} i₁
                              (f i₁ (fst e i₁)) (f (notI i₁) (fst e (notI i₁))) .fst))
    diag-help₂ = (λ k j → elimIβ {B = λ i → A i (fst e i)} i₁
                                  (f i₁ (fst e i₁)) (f (notI i₁) (fst e (notI i₁))) .fst (~ k ∨ ~ j))
               ▷ cong sym (sym (elimIη-id {B = λ i → A i (fst e i)} (λ x → f x (fst e x)) i₁ .fst))

    not-help₂ : Square (refl {x = f (notI i₁) (fst e (notI i₁))})
                        (funExt⁻ (sym (elimIη (λ x → f x (fst e x)) i₁)) (notI i₁))
                        (refl {x = f (notI i₁) (fst e (notI i₁))})
                        (sym (elimIβ {B = λ i → A i (fst e i)} i₁
                              (f i₁ (fst e i₁)) (f (notI i₁) (fst e (notI i₁))) .snd))
    not-help₂ = ((λ k j → elimIβ {B = λ i → A i (fst e i)} i₁
                                  (f i₁ (fst e i₁)) (f (notI i₁) (fst e (notI i₁))) .snd (~ k ∨ ~ j)))
               ▷ cong sym (sym (elimIη-id {B = λ i → A i (fst e i)} (λ x → f x (fst e x)) i₁ .snd))

    coh-coh-diag₂ :
      Square (sym (coh₂-diag i₁ (fst e i₁ , f)))
             (cong inlR (cong (fst e i₁ ,_) (funExt⁻ (sym (elimIη (λ x → f x (fst e x)) i₁)) i₁)))
             (sym (push* (fst e i₁ , f i₁ (fst e i₁)) (f i₁) refl))
             (simp-coh-diag i₁ e (f i₁ (fst e i₁)) (f (notI i₁)))
    coh-coh-diag₂ j k =
      hcomp (λ r → λ {(j = i0) → compPath-filler (elimIβ {B = λ i → joinR-gen J (A i)} i₁
                                                     (inlR (fst e i₁ , f i₁ (fst e i₁)))
                                                     (inrR (f (notI i₁))) .fst)
                                                   (push* ((fst e i₁) , (f i₁ (fst e i₁))) (f i₁) refl)
                                                   r (~ k)
                     ; (j = i1) → inlR (fst e i₁ , diag-help₂ r k)
                     ; (k = i0) → push* (fst e i₁ , f i₁ (fst e i₁)) (f i₁) refl (~ j ∧ r)
                     ; (k = i1) → compPath-filler (elimIβ {B = λ i → joinR-gen J (A i)} i₁ (inlR (fst e i₁ , f i₁ (fst e i₁))) (inrR (f (notI i₁))) .fst)
                                                    (cong inlR (cong (fst e i₁ ,_) (sym (elimIβ {B = λ i → A i (fst e i)} i₁
                                                      (f i₁ (fst e i₁)) (f (notI i₁) (fst e (notI i₁))) .fst)))) r j})
            (elimIβ {B = λ i → joinR-gen J (A i)} i₁
                    (inlR (fst e i₁ , f i₁ (fst e i₁))) (inrR (f (notI i₁))) .fst (j ∨ ~ k))

    coh-coh-not₂ :
      Square (sym (coh₂-not i₁ (fst e i₁ , f)))
             (cong inlR (cong (fst e (notI i₁) ,_) (funExt⁻ (sym (elimIη (λ x → f x (fst e x)) i₁)) (notI i₁))))
             (sym (push* (fst e (notI i₁) , f (notI i₁) (fst e (notI i₁))) (f (notI i₁)) refl))
             (simp-coh-not i₁ e (f i₁ (fst e i₁)) (f (notI i₁)))
    coh-coh-not₂ j k =
      hcomp (λ r → λ {(j = i0) → elimIβ {B = λ i → joinR-gen J (A i)} i₁ (inlR (fst e i₁ , f i₁ (fst e i₁))) (inrR (f (notI i₁))) .snd (~ r ∨ ~ k)
                     ; (j = i1) → inlR (fst e (notI i₁) , not-help₂ r k)
                     ; (k = i0) → push* (fst e (notI i₁) , f (notI i₁) (fst e (notI i₁))) (f (notI i₁)) refl (~ j)
                     ; (k = i1) → doubleCompPath-filler
                                    (elimIβ {B = λ i → joinR-gen J (A i)} i₁ (inlR (fst e i₁ , f i₁ (fst e i₁))) (inrR (f (notI i₁))) .snd)
                                    (sym (push* ((fst e (notI i₁)) , (f (notI i₁) (fst e (notI i₁)))) (f (notI i₁)) refl))
                                    (cong inlR (cong (fst e (notI i₁) ,_) (sym (elimIβ {B = λ i → A i (fst e i)} i₁
                                      (f i₁ (fst e i₁)) (f (notI i₁) (fst e (notI i₁))) .snd)))) r j -- ) r j
                                    })
            (push* (fst e (notI i₁) , f (notI i₁) (fst e (notI i₁))) (f (notI i₁)) refl (~ j))

  HAH-diag : (i₁ : fst I) → mega-coh' i₁ i₁
  coher1 (HAH-diag i₁) = coh₁-diag i₁
  simp-coh (HAH-diag i₁) = simp-coh-diag i₁
  coher2 (HAH-diag i₁) = coh₂-diag i₁
  coh-coher2₁ (HAH-diag i₁) = coh-coh-diag i₁
  coh-coher2₂ (HAH-diag i₁) = coh-coh-diag₂ i₁

  HAH-not : (i₁ : fst I) → mega-coh' i₁ (notI i₁)
  coher1 (HAH-not i₁) = coh₁-not i₁
  simp-coh (HAH-not i₁) e a b = simp-coh-not i₁ e a b
  coher2 (HAH-not i₁) = coh₂-not i₁
  coh-coher2₁ (HAH-not i₁) = coh-coh-not i₁
  coh-coher2₂ (HAH-not i₁) = coh-coh-not₂ i₁

  HAH : (i₁ i : fst I) → mega-coh' i₁ i
  HAH i₁ = elimI i₁ (HAH-diag i₁) (HAH-not i₁)

  module makeWithHah (HAH' : (i₁ i : fst I) → mega-coh' i₁ i) where

    ΠR-extend**→ : (i : fst I) → ΠR-extend** → joinR-gen J (A i)
    ΠR-extend**→ i (2-elter'.inl (i' , p , d)) = elimI {B = λ i → joinR-gen J (A i)} i' (inlR p) (inrR d) i
    ΠR-extend**→ i (2-elter'.inr x) = ΠR-base*→Goal i x
    ΠR-extend**→ i (2-elter'.pashₗ i₁ e i₂) = coher1 (HAH' i₁ i) e i₂
    ΠR-extend**→ i (2-elter'.pashᵣ i₁ e i₂) = coher2 (HAH' i₁ i) e i₂
    ΠR-extend**→ i (2-elter'.pashₗᵣ i₁ e i₂ i₃) = coh-coher2₁ (HAH' i₁ i) e i₂ i₃

    asPushout→ : asPushout → GOAL
    asPushout→ (inl x) i = ΠR-extend**→ i x
    asPushout→ (inr (e , f)) i = inlR ((fst e i) , (f i))
    asPushout→ (push (e , 2-elter'.ppl f) i₁) i = push* (fst e i , f i (fst e i)) (f i) refl (~ i₁)
    asPushout→ (push (e , 2-elter'.ppr i₁ a b) j) i = simp-coh (HAH' i₁ i) e a b j
    asPushout→ (push (e , 2-elter'.pplr i₁ f i₃) j) i = coh-coher2₂ (HAH' i₁ i) e f j i₃

  asPushout→ : asPushout → GOAL
  asPushout→ = makeWithHah.asPushout→ HAH

TotΠFun : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : A → Type ℓ'} {C : A → Type ℓ''}
  → (f : (x : A) → B x → C x)
  → TotΠ B → TotΠ C
TotΠFun f g x = f x (g x)

module TT2 {ℓ : Level} (J : Type) (A : Bool →  J → Type ℓ) where

  open TT (RP∞'· ℓ) J A
  open 2-elter' (RP∞'· ℓ) J A
  open TT.mega-coh'

  HAH-diag-true : mega-coh' true true
  coher1 HAH-diag-true _ = refl
  simp-coh HAH-diag-true e a b = refl
  coher2 HAH-diag-true e = push* (fst e , snd e true (fst e)) (snd e true) refl
  coh-coher2₁ HAH-diag-true e i j = push* (fst e , snd e true (fst e)) (snd e true) refl (j ∧ i)
  coh-coher2₂ HAH-diag-true e f i j = push* (fst e true , f true (fst e true)) (f true) refl (~ j ∧ ~ i)

  HAH-diag-false : mega-coh' false false
  coher1 HAH-diag-false _ = refl
  simp-coh HAH-diag-false _ _ _ = refl
  coher2 HAH-diag-false e = push* (fst e , snd e false (fst e)) (snd e false) refl
  coh-coher2₁ HAH-diag-false e i j = push* (fst e , snd e false (fst e)) (snd e false) refl (j ∧ i)
  coh-coher2₂ HAH-diag-false e f i j = push* (fst e false , f false (fst e false)) (f false) refl (~ j ∧ ~ i)

  HAH-true-false : mega-coh' true false
  coher1 HAH-true-false e = sym (push* (fst e , snd e .snd (fst e)) (snd e .snd) refl)
  simp-coh HAH-true-false e a b = sym (push* (fst e false , b (fst e false)) b refl)
  coher2 HAH-true-false e = refl
  coh-coher2₁ HAH-true-false e i j = push* (fst e , snd e false (fst e)) (snd e false) refl i
  coh-coher2₂ HAH-true-false e f i j = push* (fst e false , f false (fst e false)) (f false) refl (~ i)

  HAH-false-true : mega-coh' false true
  coher1 HAH-false-true e = sym (push* (fst e , snd e .snd (fst e)) (snd e .snd) refl)
  simp-coh HAH-false-true e a b = sym (push* (fst e true , b (fst e true)) b refl)
  coher2 HAH-false-true e = refl
  coh-coher2₁ HAH-false-true e i j = push* (fst e , snd e true (fst e)) (snd e true) refl i
  coh-coher2₂ HAH-false-true e f i j = push* (fst e true , f true (fst e true)) (f true) refl (~ i)

  HAH-diag' : (i₁ : Bool) → mega-coh' i₁ i₁
  HAH-diag' = CasesBool true HAH-diag-true HAH-diag-false

  HAH-not' : (i₁ : Bool) → mega-coh' i₁ (notI i₁)
  HAH-not' = CasesBool true HAH-true-false HAH-false-true

  HAH-Bool : (a b : Bool) → mega-coh' a b
  HAH-Bool a = CasesBool a (HAH-diag' a) (HAH-not' a)

  asPushout→Bool : asPushout → GOAL
  asPushout→Bool = makeWithHah.asPushout→ HAH-Bool

  corr : GOAL → join-gen J (A true) × join-gen J (A false)
  corr = Iso.fun (ΠBool×Iso {A = λ x → join-gen J (A x)}) ∘ TotΠFun (λ x → Iso.fun (join-gen-Iso J (A x)))

  asPushout→Bool' : asPushout → join-gen J (A true) × join-gen J (A false)
  asPushout→Bool' = corr ∘ asPushout→Bool

module TTBool {ℓ : Level} (J : Type) (A : Bool → Bool → Type ℓ) where

  open TT (RP∞'· ℓ) Bool A
  open 2-elter' (RP∞'· ℓ) Bool A
  open TT.mega-coh'
  open TT2 Bool A

  GOAL'→AsPushout : join-gen Bool (A true) × join-gen Bool (A false) → asPushout
  GOAL'→AsPushout (inl (false , b) , inl (false , d)) = inl (inr (inl (false , (CasesBool true b d))))
  GOAL'→AsPushout (inl (true , b) , inl (false , d)) = inr ((idEquiv Bool) , (CasesBool true b d))
  GOAL'→AsPushout (inl (false , b) , inl (true , d)) = inr (notEquiv , (CasesBool true b d))
  GOAL'→AsPushout (inl (true , b) , inl (true , d)) = inl (inr (inl (true , CasesBool true b d)))
  GOAL'→AsPushout (inl (c , b) , inr g) = inl (inl (true , ((c , b) , g)))
  GOAL'→AsPushout (inl (false , b) , push (false , d) i) = inl (pashₗ true (false , (b , d)) (~ i))
  GOAL'→AsPushout (inl (false , b) , push (true , d) i) = push (notEquiv , ppr true b d) (~ i)
  GOAL'→AsPushout (inl (true , b) , push (false , d) i) = push (idEquiv Bool , ppr true b d) (~ i)
  GOAL'→AsPushout (inl (true , b) , push (true , d) i) = inl (pashₗ true (true , (b , d)) (~ i))
  GOAL'→AsPushout (inr x , inl (c , d)) = inl (inl (false , (c , d) , x))
  GOAL'→AsPushout (inr x , inr x₁) = inl (inr (inr (CasesBool true x x₁)))
  GOAL'→AsPushout (inr x , push (false , d) i) = inl (pashᵣ false (false , (CasesBool true x d)) i)
  GOAL'→AsPushout (inr x , push (true , d) i) = inl (pashᵣ false (true , CasesBool true x d) i)
  GOAL'→AsPushout (push (false , b) i , inl (false , d)) = inl (((pashₗ false (false , (d , b)))) (~ i))
  GOAL'→AsPushout (push (false , b) i , inl (true , d)) = push (notEquiv , ppr false d b) (~ i)
  GOAL'→AsPushout (push (true , b) i , inl (false , d)) = push (idEquiv Bool , ppr false d b) (~ i)
  GOAL'→AsPushout (push (true , b) i , inl (true , d)) = inl (((pashₗ false (true , (d , b)))) (~ i))
  GOAL'→AsPushout (push (false , d) i , inr x) = inl (pashᵣ true (false , (CasesBool true d x)) i)
  GOAL'→AsPushout (push (true , d) i , inr x) = inl (pashᵣ true (true , CasesBool true d x) i)
  GOAL'→AsPushout (push (false , b) i , push (false , d) j) =
    inl (hcomp (λ k → λ {(i = i0) → pashₗ true (false , b false , d) (~ j ∨ ~ k)
                        ; (i = i1) → pashₗᵣ false (false , (CasesBool true b d)) k j
                        ; (j = i0) → pashₗ false (false , d false , b) (~ i ∨ ~ k)
                        ; (j = i1) → pashₗᵣ true (false , CasesBool true b d) k i})
               (inr (inl (false , elimIηPushTop* true false (CasesBool true b d) (i ∧ j)))))
  GOAL'→AsPushout (push (false , b) i , push (true , d) j) =
    hcomp (λ k → λ {(j = i0) → push (notEquiv , pplr false (CasesBool true b d) k) (~ i)
                   ; (j = i1) → inl (pashᵣ true (false , CasesBool true b d) (i ∨ ~ k))
                   ; (i = i0) → push (notEquiv , pplr true (CasesBool true b d) k) (~ j)
                   ; (i = i1) → inl (pashᵣ false (true , CasesBool true b d) (j ∨ ~ k))})
          (push (notEquiv , ppl (CasesBool true b d)) (~ i ∧ ~ j))
  GOAL'→AsPushout (push (true , b) i , push (false , d) j) =
    hcomp (λ k → λ {(j = i0) → push (idEquiv Bool , pplr false (CasesBool true b d) k) (~ i)
                   ; (j = i1) → inl (pashᵣ true (true , CasesBool true b d) (i ∨ ~ k))
                   ; (i = i0) → push (idEquiv Bool , pplr true (CasesBool true b d) k) (~ j)
                   ; (i = i1) → inl (pashᵣ false (false , CasesBool true b d) (j ∨ ~ k))})
          (push (idEquiv Bool , ppl (CasesBool true b d)) (~ i ∧ ~ j))
  GOAL'→AsPushout (push (true , b) i , push (true , d) j) =
    inl (hcomp (λ k → λ {(i = i0) → pashₗ true (true , b true , d) (~ j ∨ ~ k)
                        ; (i = i1) → pashₗᵣ false (true , (CasesBool true b d)) k j
                        ; (j = i0) → pashₗ false (true , d true , b) (~ i ∨ ~ k)
                        ; (j = i1) → pashₗᵣ true (true , CasesBool true b d) k i})
               (inr (inl (true , elimIηPushTop* true true (CasesBool true b d) (i ∧ j)))))

  cancel1 : (x : _) → asPushout→Bool' (GOAL'→AsPushout x) ≡ x
  cancel1 (inl (false , b) , inl (false , d)) = refl
  cancel1 (inl (false , b) , inl (true , d)) = refl
  cancel1 (inl (true , b) , inl (false , d)) = refl
  cancel1 (inl (true , b) , inl (true , d)) = refl
  cancel1 (inl (false , b) , inr x) = refl
  cancel1 (inl (true , b) , inr x) = refl
  cancel1 (inl (false , b) , push (false , d) i) = {!refl!}
  cancel1 (inl (false , b) , push (true , d) i) = {!!}
  cancel1 (inl (true , b) , push a₁ i) = {!!}
  cancel1 (inr x , d) = {!!}
  cancel1 (push a i , d) = {!!}

--   GOAL : Type _
--   GOAL = (i : fst I) → joinR-gen J (A i)

--   ΠR-base*→Goal : (i : fst I) → ΠR-base* → joinR-gen J (A i)
--   ΠR-base*→Goal i (inl (j , a)) = inlR (j , a i)
--   ΠR-base*→Goal i (inr x) = inrR (x i)
--   ΠR-base*→Goal i (push (j , p) i₁) = push* (j , p i j) (p i) refl i₁



-- -- module _ {ℓ : Level} (I J : RP∞' ℓ) (A : fst I →  fst J → Type ℓ) where
-- --   module ASD = 2-elter' I (fst J) A
-- --   open ASD
-- --   module NN = TT I (fst J) A
-- --   open NN

-- --   module pps = 2-elter' J (fst I) (λ j i → A i j)

-- --   elimJ = pps.elimI
-- --   elimJβ = pps.elimIβ

-- --   ΠR-extend**→' : ΠR-extend** → joinR-gen (fst J) λ j → joinR-gen (fst I) λ i → A i j
-- --   ΠR-extend**→' (2-elter'.inl (x , ((j , a) , f))) =
-- --                  inlR (j , inrR (elimI x a (f j)))
-- --   ΠR-extend**→' (2-elter'.inr (inl x)) = inlR (fst x , inrR (snd x))
-- --   ΠR-extend**→' (2-elter'.inr (inr x)) = inrR λ j → inrR λ i → x i j
-- --   ΠR-extend**→' (2-elter'.inr (push a i)) =
-- --     push* (fst a , inrR (λ i → snd a i (fst a))) (λ j → inrR (λ z → snd a z j)) refl i
-- --   ΠR-extend**→' (2-elter'.pashₗ i e i₁) = inlR (e .fst , inrR (M.elimI i (e .snd .fst) (e .snd .snd (e .fst))))
-- --   ΠR-extend**→' (2-elter'.pashᵣ i e i₁) = {!push* ? ? !}
-- --   ΠR-extend**→' (2-elter'.pashₗᵣ i e i₁ i₂) = {!!}

-- --   asPushout→' : asPushout → joinR-gen (fst J) λ j → joinR-gen (fst I) λ i → A i j
-- --   asPushout→' (inl x) = ΠR-extend**→' x
-- --   asPushout→' (inr (e , p)) = inrR λ j → inlR ((invEq e j) , {!p (invEq e j)!})
-- --   asPushout→' (push (fst₁ , 2-elter'.ppl f) i) = {!fst₁!}
-- --   asPushout→' (push (fst₁ , 2-elter'.ppr i₁ a b) i) = {!fst₁!}
-- --   asPushout→' (push (fst₁ , 2-elter'.pplr i₁ f i₂) i) = {!!}
