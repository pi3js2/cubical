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
module Cubical.Cohomology.EilenbergMacLane.join.asPushoutOut-alt-gen where

open import Cubical.HITs.Join
open import Cubical.Functions.FunExtEquiv

module TT {ℓ : Level} (I : RP∞' ℓ) (J : Type) (A : fst I →  J → Type ℓ) where
  module M = 2-elter' I J A
  open M
  inl* : {i : fst I} → (x : _) → join-gen J (A i)
  inl* = inl

  inr* : {i : fst I} → (x : _) → join-gen J (A i)
  inr* = inr

  GOAL : Type _
  GOAL = (i : fst I) → join-gen J (A i)

  ΠR-base*→Goal : (i : fst I) → ΠR-base* → join-gen J (A i)
  ΠR-base*→Goal i (inl (j , a)) = inl (j , a i)
  ΠR-base*→Goal i (inr x) = inr (x i)
  ΠR-base*→Goal i (push (j , p) i₁) = push (j , p i) i₁

  coh₁-diag : (i : fst I) (e : left-push↑ₗ* i)
    → Path (join-gen J (A i))
            (elimI {B = λ i → join-gen J (A i)} i (inl (e .fst , e .snd .fst)) (inr (e .snd .snd)) i)
            (inl (fst e , elimI {B = λ i → A i (fst e)} i (snd e .fst) (snd e .snd (fst e)) i))
  coh₁-diag i e =
      elimIβ {B = λ i → join-gen J (A i)} i (inl (e .fst , e .snd .fst)) (inr (e .snd .snd)) .fst
    ∙ cong inl* (cong (e .fst ,_) (sym (elimIβ {B = λ i → A i (fst e)} i (snd e .fst) (snd e .snd (fst e)) .fst)))

  coh₁-not : (i : fst I) (e : left-push↑ₗ* i)
    → Path (join-gen J (A (notI i)))
            (elimI {B = λ i → join-gen J (A i)} i (inl (e .fst , e .snd .fst)) (inr (e .snd .snd)) (notI i)) 
            (inl (fst e , elimI {B = λ i → A i (fst e)} i (snd e .fst) (snd e .snd (fst e)) (notI i)))
  coh₁-not i e = elimIβ {B = λ i → join-gen J (A i)} i (inl (e .fst , e .snd .fst)) (inr (e .snd .snd)) .snd
               ∙∙ sym (push (e .fst ,  (e .snd .snd)))
               ∙∙ cong inl* (cong (e .fst ,_) (sym (elimIβ {B = λ i → A i (fst e)} i (snd e .fst) (snd e .snd (fst e)) .snd)))

  coh₁ : (i₁ i : fst I) (e : left-push↑ₗ* i₁)
    → Path (join-gen J (A i))
            (elimI {B = λ i → join-gen J (A i)} i₁ (inl (e .fst , e .snd .fst)) (inr (e .snd .snd)) i)
            (inl (fst e , elimI {B = λ i → A i (fst e)} i₁ (snd e .fst) (snd e .snd (fst e)) i))
  coh₁ i₁ =
    elimI i₁ (coh₁-diag i₁) (coh₁-not i₁)

  coh₂ : (i₁ i : fst I) (e : left-push↑ᵣ i₁)
    → Path (join-gen J (A i))
            (elimI {B = λ i → join-gen J (A i)} i₁ (inl (fst e , snd e i₁ (fst e))) (inr (snd e (notI i₁))) i)
            (inr (snd e i))
  coh₂ i₁ =
    elimI i₁
      (λ e → elimIβ {B = λ i → join-gen J (A i)} i₁ (inl (fst e , snd e i₁ (fst e))) (inr (snd e (notI i₁))) .fst
            ∙ push (fst e , snd e i₁))
      λ e → elimIβ {B = λ i → join-gen J (A i)} i₁ (inl (fst e , snd e i₁ (fst e))) (inr (snd e (notI i₁))) .snd

  coh₂-diag : (i₁ : fst I) (e : left-push↑ᵣ i₁)
    → Path (join-gen J (A i₁))
            (elimI {B = λ i → join-gen J (A i)} i₁ (inl (fst e , snd e i₁ (fst e))) (inr (snd e (notI i₁))) i₁)
            (inr (snd e i₁))
  coh₂-diag i₁ e =
      elimIβ {B = λ i → join-gen J (A i)} i₁ (inl (fst e , snd e i₁ (fst e))) (inr (snd e (notI i₁))) .fst
    ∙ push (fst e , snd e i₁)

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
    → Square {A = join-gen J (A i₁)}
      (λ i₃ → inl (fst e , elimIηPushTop* i₁ (fst e) (snd e) i₃ i₁))
      (coh₂-diag i₁ e) -- (coh₂ i₁ i₁ e)
      (sym (coh₁-diag i₁ (fst e , snd e i₁ (fst e) , snd e (notI i₁)))) -- (sym (coh₁ i₁ i₁ (fst e , snd e i₁ (fst e) , snd e (notI i₁))))
      (push (fst e , snd e i₁))
  coh-coh-diag i₁ e j k =
    hcomp (λ r → λ {(j = i0) → inl (fst e , coh-coh-diag-side i₁ e r k)
                   ; (j = i1) → compPath-filler
                                  (elimIβ {B = λ i → join-gen J (A i)} i₁
                                    (inl (fst e , snd e i₁ (fst e))) (inr (snd e (notI i₁))) .fst)
                                  (push (fst e , snd e i₁))
                                  r k
                   ; (k = i0) → compPath-filler (elimIβ {B = λ i → join-gen J (A i)} i₁ (inl (fst e , snd e i₁ (fst e))) (inr (snd e (notI i₁))) .fst)
                                  (cong inl* (cong (e .fst ,_) (sym (elimIβ {B = λ i → A i (fst e)} i₁ (snd e i₁ (fst e)) (snd e (notI i₁) (fst e)) .fst)))) r (~ j)
                   ; (k = i1) → push (fst e , snd e i₁) (j ∧ r)})
          (elimIβ {B = λ i → join-gen J (A i)} i₁ (inl (fst e , snd e i₁ (fst e))) (inr (snd e (notI i₁))) .fst (~ j ∨ k))

  coh₂-not : (i₁ : fst I) (e : fat*)
    → Path (join-gen J (A (notI i₁)))
            (elimI {B = λ i → join-gen J (A i)} i₁ (inl (fst e , snd e i₁ (fst e))) (inr (snd e (notI i₁))) (notI i₁))
            (inr (snd e (notI i₁)))
  coh₂-not i₁ e = elimIβ {B = λ i → join-gen J (A i)} i₁ (inl (fst e , snd e i₁ (fst e))) (inr (snd e (notI i₁))) .snd

  coh-coh-not : (i₁ : fst I) (e : fat*)
    → Square {A = join-gen J (A (notI i₁))}
              (λ i₃ → inl (fst e , elimIηPushTop* i₁ (fst e) (snd e) i₃ (notI i₁)))
              (coh₂-not i₁ e)
              (sym (coh₁-not i₁ (fst e , snd e i₁ (fst e) , snd e (notI i₁))))
              (push (fst e , snd e (notI i₁)))
  coh-coh-not i₁ e j k =
    hcomp (λ r → λ {(j = i0) → inl (fst e , coh-coh-not-side i₁ e r k)
                   ; (j = i1) → coh₂-not i₁ e (k ∨ ~ r)
                   ; (k = i0) → doubleCompPath-filler
                                  (elimIβ {B = λ i → join-gen J (A i)} i₁ (inl (fst e , snd e i₁ (fst e))) (inr (snd e (notI i₁))) .snd)
                                  (sym (push (e .fst , e .snd (notI i₁))))
                                  (cong inl* (cong (e .fst ,_)
                                    (sym (elimIβ {B = λ i → A i (fst e)} i₁ (snd e i₁ (fst e)) (snd e (notI i₁) (fst e)) .snd)))) r (~ j)
                   ; (k = i1) → push (fst e , snd e (notI i₁)) j})
          (push (fst e , snd e (notI i₁)) j)


  record mega-coh' (i₁ i : fst I) : Type ℓ where
    field
      coher1 : ((e : left-push↑ₗ* i₁)
           → Path (join-gen J (A i))
             (elimI {B = λ i → join-gen J (A i)} i₁ (inl (e .fst , e .snd .fst)) (inr (e .snd .snd)) i)
             (inl (fst e , elimI {B = λ i → A i (fst e)} i₁ (snd e .fst) (snd e .snd (fst e)) i)))
      simp-coh : (e : fst I ≃ J) (a : A i₁ (fst e i₁)) (b : (j : J) → A (notI i₁) j)
              → Path (join-gen J (A i))
                      (elimI {B = λ i → join-gen J (A i)} i₁ (inl (fst e i₁ , a)) (inr b) i)
                      (inl ((fst e i) , (elimI {B = λ i → A i (fst e i) } i₁ a (b (fst e (notI i₁))) i)))

      coher2 : (e : fat*) → Path (join-gen J (A i))
                              (elimI {B = λ i → join-gen J (A i)} i₁ (inl (fst e , snd e i₁ (fst e))) (inr (snd e (notI i₁))) i)
                              (inr (snd e i))
      coh-coher2₁ : (e : fat*) → Square {A = join-gen J (A i)}
              (λ i₃ → inl (fst e , elimIηPushTop* i₁ (fst e) (snd e) i₃ i))
              (coher2 e)
              (sym (coher1 ((fst e) , (snd e i₁ (fst e) , snd e (notI i₁)))))
              (push (fst e , snd e i))

      coh-coher2₂ : (e : fst I ≃ J) (f : (i₂ : fst I) (j₁ : J) → A i₂ j₁)
        → Square {A = join-gen J (A i)}
              (sym (coher2 ((fst e i₁) , f)))
              (cong inl* (cong (fst e i ,_) (funExt⁻ (sym (elimIη {B = λ i → A i (fst e i)} (λ x → f x (fst e x)) i₁)) i)))
              (sym (push (fst e i , f i)) )
              (simp-coh e (f i₁ (fst e i₁)) (f (notI i₁)))

  open mega-coh'
  simp-coh-diag : (i₁ : fst I) (e : fst I ≃ J) (a : A i₁ (fst e i₁))
      (b : (j : J) → A (notI i₁) j) →
      Path (join-gen J (A i₁))
      (elimI {B = λ i → join-gen J (A i)} i₁ (inl (fst e i₁ , a)) (inr b) i₁)
      (inl (fst e i₁ , elimI {B = λ i → A i (fst e i)} i₁ a (b (fst e (notI i₁))) i₁))
  simp-coh-diag i₁ e a b = elimIβ i₁ (inl (fst e i₁ , a)) (inr b) .fst
                          ∙ cong inl* (cong (fst e i₁ ,_) (sym (elimIβ i₁ a (b (fst e (notI i₁))) .fst)))

  simp-coh-not : (i₁ : fst I) (e : fst I ≃ J) (a : A i₁ (fst e i₁))
      (b : (j : J) → A (notI i₁) j) →
      Path (join-gen J (A (notI i₁)))
      (elimI {B = λ i → join-gen J (A i)} i₁ (inl (fst e i₁ , a)) (inr b) (notI i₁))
      (inl (fst e (notI i₁) , elimI {B = λ i → A i (fst e i)} i₁ a (b (fst e (notI i₁))) (notI i₁)))
  simp-coh-not i₁ e a b =
       elimIβ {B = λ i → join-gen J (A i)} i₁ (inl (fst e i₁ , a)) (inr b) .snd
    ∙∙ sym (push ((fst e (notI i₁)) , b))
    ∙∙ cong inl* (cong (fst e (notI i₁) ,_) (sym (elimIβ {B = λ i → A i (fst e i)} i₁ a (b (fst e (notI i₁))) .snd)))

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
             (cong inl* (cong (fst e i₁ ,_) (funExt⁻ (sym (elimIη (λ x → f x (fst e x)) i₁)) i₁)))
             (sym (push (fst e i₁ , f i₁)))
             (simp-coh-diag i₁ e (f i₁ (fst e i₁)) (f (notI i₁)))
    coh-coh-diag₂ j k =
      hcomp (λ r → λ {(j = i0) → compPath-filler (elimIβ {B = λ i → join-gen J (A i)} i₁
                                                     (inl (fst e i₁ , f i₁ (fst e i₁)))
                                                     (inr (f (notI i₁))) .fst)
                                                   (push ((fst e i₁) , f i₁))
                                                   r (~ k)
                     ; (j = i1) → inl (fst e i₁ , diag-help₂ r k)
                     ; (k = i0) → push (fst e i₁ , f i₁) (~ j ∧ r)
                     ; (k = i1) → compPath-filler (elimIβ {B = λ i → join-gen J (A i)} i₁ (inl (fst e i₁ , f i₁ (fst e i₁))) (inr (f (notI i₁))) .fst)
                                                    (cong inl* (cong (fst e i₁ ,_) (sym (elimIβ {B = λ i → A i (fst e i)} i₁
                                                      (f i₁ (fst e i₁)) (f (notI i₁) (fst e (notI i₁))) .fst)))) r j})
            (elimIβ {B = λ i → join-gen J (A i)} i₁
                    (inl (fst e i₁ , f i₁ (fst e i₁))) (inr (f (notI i₁))) .fst (j ∨ ~ k))

    coh-coh-not₂ :
      Square (sym (coh₂-not i₁ (fst e i₁ , f)))
             (cong inl* (cong (fst e (notI i₁) ,_) (funExt⁻ (sym (elimIη (λ x → f x (fst e x)) i₁)) (notI i₁))))
             (sym (push (fst e (notI i₁) , f (notI i₁))))
             (simp-coh-not i₁ e (f i₁ (fst e i₁)) (f (notI i₁)))
    coh-coh-not₂ j k =
      hcomp (λ r → λ {(j = i0) → elimIβ {B = λ i → join-gen J (A i)} i₁ (inl (fst e i₁ , f i₁ (fst e i₁))) (inr (f (notI i₁))) .snd (~ r ∨ ~ k)
                     ; (j = i1) → inl (fst e (notI i₁) , not-help₂ r k)
                     ; (k = i0) → push (fst e (notI i₁) , f (notI i₁)) (~ j)
                     ; (k = i1) → doubleCompPath-filler
                                    (elimIβ {B = λ i → join-gen J (A i)} i₁ (inl (fst e i₁ , f i₁ (fst e i₁))) (inr (f (notI i₁))) .snd)
                                    (sym (push ((fst e (notI i₁)) , f (notI i₁)) ))
                                    (cong inl* (cong (fst e (notI i₁) ,_) (sym (elimIβ {B = λ i → A i (fst e i)} i₁
                                      (f i₁ (fst e i₁)) (f (notI i₁) (fst e (notI i₁))) .snd)))) r j -- ) r j
                                    })
            (push (fst e (notI i₁) , f (notI i₁)) (~ j))

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

    ΠR-extend**→ : (i : fst I) → ΠR-extend** → join-gen J (A i)
    ΠR-extend**→ i (2-elter'.inl (i' , p , d)) = elimI {B = λ i → join-gen J (A i)} i' (inl p) (inr d) i
    ΠR-extend**→ i (2-elter'.inr x) = ΠR-base*→Goal i x
    ΠR-extend**→ i (2-elter'.pashₗ i₁ e i₂) = coher1 (HAH' i₁ i) e i₂
    ΠR-extend**→ i (2-elter'.pashᵣ i₁ e i₂) = coher2 (HAH' i₁ i) e i₂
    ΠR-extend**→ i (2-elter'.pashₗᵣ i₁ e i₂ i₃) = coh-coher2₁ (HAH' i₁ i) e i₂ i₃

    asPushout→ : asPushout → GOAL
    asPushout→ (inl x) i = ΠR-extend**→ i x
    asPushout→ (inr (e , f)) i = inl ((fst e i) , (f i))
    asPushout→ (push (e , 2-elter'.ppl f) i₁) i = push (fst e i , f i) (~ i₁)
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
  coher2 HAH-diag-true e = push (fst e , snd e true)
  coh-coher2₁ HAH-diag-true e i j = push (fst e , snd e true) (j ∧ i)
  coh-coher2₂ HAH-diag-true e f i j = push (fst e true , f true) (~ j ∧ ~ i)

  HAH-diag-false : mega-coh' false false
  coher1 HAH-diag-false _ = refl
  simp-coh HAH-diag-false _ _ _ = refl
  coher2 HAH-diag-false e = push (fst e , snd e false)
  coh-coher2₁ HAH-diag-false e i j = push (fst e , snd e false) (j ∧ i)
  coh-coher2₂ HAH-diag-false e f i j = push (fst e false , f false) (~ j ∧ ~ i)

  HAH-true-false : mega-coh' true false
  coher1 HAH-true-false e = sym (push (fst e , snd e .snd))
  simp-coh HAH-true-false e a b = sym (push (fst e false , b))
  coher2 HAH-true-false e = refl
  coh-coher2₁ HAH-true-false e i j = push (fst e , snd e false)  i
  coh-coher2₂ HAH-true-false e f i j = push (fst e false , f false) (~ i)

  HAH-false-true : mega-coh' false true
  coher1 HAH-false-true e = sym (push (fst e , snd e .snd))
  simp-coh HAH-false-true e a b = sym (push (fst e true , b))
  coher2 HAH-false-true e = refl
  coh-coher2₁ HAH-false-true e i j = push (fst e , snd e true) i
  coh-coher2₂ HAH-false-true e f i j = push (fst e true , f true) (~ i)

  HAH-diag' : (i₁ : Bool) → mega-coh' i₁ i₁
  HAH-diag' = CasesBool true HAH-diag-true HAH-diag-false

  HAH-not' : (i₁ : Bool) → mega-coh' i₁ (notI i₁)
  HAH-not' = CasesBool true HAH-true-false HAH-false-true

  HAH-Bool : (a b : Bool) → mega-coh' a b
  HAH-Bool a = CasesBool a (HAH-diag' a) (HAH-not' a)

  asPushout→Bool : asPushout → GOAL
  asPushout→Bool = makeWithHah.asPushout→ HAH-Bool

  -- 'Easy' goal
  HAH-Bool≡ : (x y : Bool) → HAH-Bool x y ≡ HAH x y
  HAH-Bool≡ = {!!}

  asPushout→Bool≡ : asPushout→Bool ≡ asPushout→
  asPushout→Bool≡ i = makeWithHah.asPushout→ λ x y → HAH-Bool≡ x y i

  asPushout→Bool' : asPushout → join-gen J (A true) × join-gen J (A false)
  asPushout→Bool' = Iso.fun (ΠBool×Iso {A = λ x → join-gen J (A x)}) ∘ asPushout→Bool

sql : ∀ {ℓ} {A : Type ℓ} {x : A} (y : A) (p : x ≡ y)
  → Cube (λ j i → p (i ∨ j)) (λ j i → p i) (λ r i → p i) (λ r i → p (i ∨ ~ r)) (λ r j → p (~ r ∧ j)) refl
sql = J> refl

module TTBool {ℓ : Level} (A : Bool → Bool → Type ℓ) where

  open TT (RP∞'· ℓ) Bool A
  open 2-elter' (RP∞'· ℓ) Bool A
  open TT.mega-coh'
  open TT2 Bool A

  module _ (b : TotΠ (A true)) (d : TotΠ (A false)) (i j k : I) where
    ff-fill : ΠR-extend**
    ff-fill =
      hfill (λ k → λ {(i = i0) → pashₗ true (false , b false , d) (~ j ∨ ~ k)
                          ; (i = i1) → pashₗᵣ false (false , (CasesBool true b d)) k j
                          ; (j = i0) → pashₗ false (false , d false , b) (~ i ∨ ~ k)
                          ; (j = i1) → pashₗᵣ true (false , CasesBool true b d) k i})
                 (inS (inr (inl (false , elimIηPushTop* true false (CasesBool true b d) (i ∧ j)))))
                 k

    tt-fill : ΠR-extend**
    tt-fill =
      hfill (λ k → λ {(i = i0) → pashₗ true (true , b true , d) (~ j ∨ ~ k)
                          ; (i = i1) → pashₗᵣ false (true , (CasesBool true b d)) k j
                          ; (j = i0) → pashₗ false (true , d true , b) (~ i ∨ ~ k)
                          ; (j = i1) → pashₗᵣ true (true , CasesBool true b d) k i})
                 (inS (inr (inl (true , elimIηPushTop* true true (CasesBool true b d) (i ∧ j)))))
             k

    ft-fill : asPushout
    ft-fill =
      hfill (λ k → λ {(j = i0) → push (notEquiv , pplr false (CasesBool true b d) k) (~ i)
                   ; (j = i1) → inl (pashᵣ true (false , CasesBool true b d) (i ∨ ~ k))
                   ; (i = i0) → push (notEquiv , pplr true (CasesBool true b d) k) (~ j)
                   ; (i = i1) → inl (pashᵣ false (true , CasesBool true b d) (j ∨ ~ k))})
          (inS (push (notEquiv , ppl (CasesBool true b d)) (~ i ∧ ~ j))) k

    tf-fill : asPushout
    tf-fill =
      hfill (λ k → λ {(j = i0) → push (idEquiv Bool , pplr false (CasesBool true b d) k) (~ i)
                   ; (j = i1) → inl (pashᵣ true (true , CasesBool true b d) (i ∨ ~ k))
                   ; (i = i0) → push (idEquiv Bool , pplr true (CasesBool true b d) k) (~ j)
                   ; (i = i1) → inl (pashᵣ false (false , CasesBool true b d) (j ∨ ~ k))})
          (inS (push (idEquiv Bool , ppl (CasesBool true b d)) (~ i ∧ ~ j)))
          k

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
  GOAL'→AsPushout (push (false , b) i , push (false , d) j) = inl (ff-fill b d i j i1)
  GOAL'→AsPushout (push (false , b) i , push (true , d) j) = ft-fill b d i j i1
  GOAL'→AsPushout (push (true , b) i , push (false , d) j) = tf-fill b d i j i1
  GOAL'→AsPushout (push (true , b) i , push (true , d) j) = inl (tt-fill b d i j i1)

  cancel2 : (x : _) → GOAL'→AsPushout (asPushout→Bool' x) ≡ x
  cancel2 =
    elimPushout left
                (uncurry (λ x → rmid x .fst))
                (uncurry λ x → rmid x .snd)
    where
    left : (b : ΠR-extend**) → GOAL'→AsPushout (asPushout→Bool' (inl b)) ≡ inl b
    left (2-elter'.inl (false , d)) = refl
    left (2-elter'.inl (true , (false , b) , f)) = refl
    left (2-elter'.inl (true , (true , b) , f)) = refl
    left (2-elter'.inr (inl (false , d))) j = inl (inr (inl (false , CasesBoolη d j)))
    left (2-elter'.inr (inl (true , d))) j = inl (inr  (inl (true , CasesBoolη d j)))
    left (2-elter'.inr (inr x)) j = inl (inr (inr (CasesBoolη x j)))
    left (2-elter'.inr (push (false , b) i)) j =
      inl {!ff-fill (b true) (b false)  (j ∧ i) (i ∨ ~ j) i1!}
    left (2-elter'.inr (push (true , b) i)) j = {!!}
    left (2-elter'.pashₗ i (false , b) i₁) = {!!}
    left (2-elter'.pashₗ i (true , b) i₁) = {!!}
    left (2-elter'.pashᵣ i e i₁) = {!e .snd!}
    left (2-elter'.pashₗᵣ i e i₁ i₂) = {!!}

    rmidT : (f : Bool ≃ Bool) → Type _
    rmidT f = Σ[ x ∈ ((g : (i : Bool) → A i (fst f i)) → GOAL'→AsPushout (asPushout→Bool' (inr (f , g))) ≡ inr (f , g)) ]
           ((y : asPushoutBack f)
             → PathP (λ i → GOAL'→AsPushout (asPushout→Bool' (push (f , y) i)) ≡ push (f , y) i)
                      (left (asPushoutBack→ₗ (f , y)))
                      (x (asPushoutBack→ᵣ (f , y) .snd)))
    rmidT-const : rmidT (idEquiv Bool)
    rmidT-const = {!!}

    rmid : (f : Bool ≃ Bool) → rmidT f
    rmid = {!!}
    

  cancel1 : (x : _) → asPushout→Bool' (GOAL'→AsPushout x) ≡ x
  cancel1 (inl (false , b) , inl (false , d)) = refl
  cancel1 (inl (false , b) , inl (true , d)) = refl
  cancel1 (inl (true , b) , inl (false , d)) = refl
  cancel1 (inl (true , b) , inl (true , d)) = refl
  cancel1 (inl (false , b) , inr x) = refl
  cancel1 (inl (true , b) , inr x) = refl
  cancel1 (inl (false , b) , push (false , d) i) = refl
  cancel1 (inl (false , b) , push (true , d) i) = refl
  cancel1 (inl (true , b) , push (false , d) i) = refl
  cancel1 (inl (true , b) , push (true , d) i) = refl
  cancel1 (inr x , inl x₁) = refl
  cancel1 (inr x , inr x₁) = refl
  cancel1 (inr x , push (false , d) i) = refl
  cancel1 (inr x , push (true , d) i) = refl
  cancel1 (push (false , b) i , inl (false , d)) = refl
  cancel1 (push (false , b) i , inl (true , d)) = refl
  cancel1 (push (true , b) i , inl (false , d)) = refl
  cancel1 (push (true , b) i , inl (true , d)) = refl
  cancel1 (push (false , b) i , inr g) = refl
  cancel1 (push (true , b) i , inr g) = refl
  cancel1 (push (false , b) i , push (false , d) j) k =
    hcomp (λ r → λ {(k = i0) → asPushout→Bool' (inl (ff-fill b d i j r))
                   ; (k = i1) → push (false , b) (i ∧ r) , push (false , d) (j ∧ r)
                   ; (j = i0) → push (false , b) (i ∧ r) , inl (false , d false)
                   ; (j = i1) → push (false , b) (i ∧ r) , push (false , d) r
                   ; (i = i0) → inl (false , b false) , push (false , d) (j ∧ r)
                   ; (i = i1) → push (false , b) r , push (false , d) (j ∧ r)})
          (inl (false , b false) , inl (false , d false))
  cancel1 (push (true , b) i , push (false , d) j) k =
      hcomp (λ r → λ { (k = i0) → asPushout→Bool' (tf-fill b d i j r)
                      ; (k = i1) → sql _ (push (true , b)) r j i , sql _ (push (false , d)) r i j 
                      ; (j = i0) → push (true , b) i , push (false , d) (~ r ∧ i)
                      ; (j = i1) → push (true , b) (i ∨ ~ r) , inr d
                      ; (i = i0) → push (true , b) (~ r ∧ j) , push (false , d) j
                      ; (i = i1) → inr b , push (false , d) (j ∨ ~ r) })
                (push (true , b) (i ∨ j) , push (false , d) (i ∨ j))
  cancel1 (push (false , b) i , push (true , d) j) k =
    hcomp (λ r → λ { (k = i0) → asPushout→Bool' (ft-fill b d i j r)
                      ; (k = i1) → (sql _ (push (false , b)) r j i) , (sql _ (push (true , d)) r i j)
                      ; (j = i0) → push (false , b) i , push (true , d) (~ r ∧ i)
                      ; (j = i1) → push (false , b) (i ∨ ~ r) , inr d
                      ; (i = i0) → push (false , b) (~ r ∧ j) , push (true , d) j
                      ; (i = i1) → inr b , push (true , d) (j ∨ ~ r)})
                      ((push (false , b) (i ∨ j)) , (push (true , d) (i ∨ j)))
  cancel1 (push (true , b) i , push (true , d) j) k =
    hcomp (λ r → λ {(k = i0) → asPushout→Bool' (inl (tt-fill b d i j r))
                   ; (k = i1) → push (true , b) (i ∧ r) , push (true , d) (j ∧ r)
                   ; (j = i0) → push (true , b) (i ∧ r) , inl (true , d true)
                   ; (j = i1) → push (true , b) (i ∧ r) , push (true , d) r
                   ; (i = i0) → inl (true , b true) , push (true , d) (j ∧ r)
                   ; (i = i1) → push (true , b) r , push (true , d) (j ∧ r)})
           (inl (true , b true) , inl (true , d true))

asPushout→Bool-isEquiv : {ℓ : Level} (A : Bool →  Bool → Type ℓ)
  → isEquiv (TT.asPushout→ (RP∞'· ℓ) Bool A)
asPushout→Bool-isEquiv {ℓ = ℓ} A =
  isoToIsEquiv
    (iso (TT.asPushout→ (RP∞'· _) Bool A)
      (GOAL'→AsPushout ∘ Iso.fun ΠBool×Iso)
      (λ x → sym (funExt⁻ (TT2.asPushout→Bool≡ Bool A) (GOAL'→AsPushout (ΠBool→× x)))
           ∙ sym (Iso.leftInv ΠBool×Iso _)
           ∙ cong (Iso.inv ΠBool×Iso) (cancel1 (ΠBool→× x))
           ∙ Iso.leftInv ΠBool×Iso x)
      λ x → cong GOAL'→AsPushout
        (sym (cong ΠBool→× (funExt⁻ (TT2.asPushout→Bool≡ Bool A) x))
        ∙ Iso.rightInv (ΠBool×Iso {A = λ j → join-gen Bool (A j)})
          (TT2.asPushout→Bool' {ℓ = ℓ} Bool A x))
        ∙ cancel2 x)
  where
  open TTBool A

asPushout→-isEquiv : {ℓ : Level} (I J : RP∞' ℓ) (A : fst I →  fst J → Type ℓ)
  → isEquiv (TT.asPushout→ I (fst J) A)
asPushout→-isEquiv =
  RP∞'pt→Prop
    (λ x → isPropΠ2 λ _ _ → isPropIsEquiv _)
    (RP∞'pt→Prop (λ _ → isPropΠ λ _ → isPropIsEquiv _)
      asPushout→Bool-isEquiv)

asPushout← : {ℓ : Level} (I J : RP∞' ℓ) (A : fst I →  fst J → Type ℓ)
  → TT.GOAL I (fst J) A →  TT.M.asPushout I (fst J) A 
asPushout← I J A = invEq (_ , asPushout→-isEquiv I J A)

asPushout←Bool : {ℓ : Level} (A : Bool →  Bool → Type ℓ)
  → asPushout← (RP∞'· ℓ) (RP∞'· ℓ) A
   ≡ TTBool.GOAL'→AsPushout A ∘ Iso.fun ΠBool×Iso
asPushout←Bool  A =
  cong (λ z → invEq (TT.asPushout→  (RP∞'· _) Bool A , z))
    (asPushout→-isEquiv-Bool-Bool A)
  where
  asPushout→-isEquiv-Bool-Bool :  {ℓ : Level} (A : Bool →  Bool → Type ℓ)
    →  asPushout→-isEquiv (RP∞'· ℓ) (RP∞'· ℓ) A ≡ asPushout→Bool-isEquiv A 
  asPushout→-isEquiv-Bool-Bool A = isPropIsEquiv _ _ _

--   GOAL : Type _
--   GOAL = (i : fst I) → join-gen J (A i)

--   ΠR-base*→Goal : (i : fst I) → ΠR-base* → join-gen J (A i)
--   ΠR-base*→Goal i (inl (j , a)) = inl (j , a i)
--   ΠR-base*→Goal i (inr x) = inr (x i)
--   ΠR-base*→Goal i (push (j , p) i₁) = push* (j , p i j) (p i) refl i₁



-- -- module _ {ℓ : Level} (I J : RP∞' ℓ) (A : fst I →  fst J → Type ℓ) where
-- --   module ASD = 2-elter' I (fst J) A
-- --   open ASD
-- --   module NN = TT I (fst J) A
-- --   open NN

-- --   module pps = 2-elter' J (fst I) (λ j i → A i j)

-- --   elimJ = pps.elimI
-- --   elimJβ = pps.elimIβ

-- --   ΠR-extend**→' : ΠR-extend** → join-gen (fst J) λ j → join-gen (fst I) λ i → A i j
-- --   ΠR-extend**→' (2-elter'.inl (x , ((j , a) , f))) =
-- --                  inl (j , inr (elimI x a (f j)))
-- --   ΠR-extend**→' (2-elter'.inr (inl x)) = inl (fst x , inr (snd x))
-- --   ΠR-extend**→' (2-elter'.inr (inr x)) = inr λ j → inr λ i → x i j
-- --   ΠR-extend**→' (2-elter'.inr (push a i)) =
-- --     push* (fst a , inr (λ i → snd a i (fst a))) (λ j → inr (λ z → snd a z j)) refl i
-- --   ΠR-extend**→' (2-elter'.pashₗ i e i₁) = inl (e .fst , inr (M.elimI i (e .snd .fst) (e .snd .snd (e .fst))))
-- --   ΠR-extend**→' (2-elter'.pashᵣ i e i₁) = {!push* ? ? !}
-- --   ΠR-extend**→' (2-elter'.pashₗᵣ i e i₁ i₂) = {!!}

-- --   asPushout→' : asPushout → join-gen (fst J) λ j → join-gen (fst I) λ i → A i j
-- --   asPushout→' (inl x) = ΠR-extend**→' x
-- --   asPushout→' (inr (e , p)) = inr λ j → inl ((invEq e j) , {!p (invEq e j)!})
-- --   asPushout→' (push (fst₁ , 2-elter'.ppl f) i) = {!fst₁!}
-- --   asPushout→' (push (fst₁ , 2-elter'.ppr i₁ a b) i) = {!fst₁!}
-- --   asPushout→' (push (fst₁ , 2-elter'.pplr i₁ f i₂) i) = {!!}

module _ {ℓ : Level} (I J : RP∞' ℓ) (A : fst I →  fst J → Type ℓ) where 
  notJ = 2-elter'.notI J (fst I) (λ j i → A i j)
  elimJ = 2-elter'.elimI J (fst I) (λ j i → A i j)

  open 2-elter' I (fst J) A

  ΠR-base*→joinₗ : TT.M.ΠR-base* I (fst J) A → join-gen (fst J) (λ j → join-gen (fst I) (λ i → A i j))
  ΠR-base*→joinₗ (inl (j' , f)) = inl (j' , inr f)
  ΠR-base*→joinₗ (inr x) = inr λ j → inr λ i → x i j
  ΠR-base*→joinₗ (push a i) = push ((fst a) , (λ j → inr λ x → snd a x j)) i
  
  asPushout→joinₗ : TT.M.ΠR-extend** I (fst J) A → join-gen (fst J) (λ j → join-gen (fst I) (λ i → A i j))
  asPushout→joinₗ (2-elter'.inl (i , (j' , a) , f)) = inl (j' , inr (elimI i a (f j')))
  asPushout→joinₗ (2-elter'.inr x) = ΠR-base*→joinₗ x
  asPushout→joinₗ (2-elter'.pashₗ i e i₁) = inl (e .fst , inr (elimI i (e .snd .fst) (e .snd .snd (e .fst))))
  asPushout→joinₗ (2-elter'.pashᵣ i e i₁) =
    ((λ k → inl (e .fst , inr (elimIη {B = λ z → A z (e .fst)} (λ x → snd e x (e .fst)) i k)))
    ∙ push ((fst e) , (λ j → inr λ x → snd e x j))) i₁
  asPushout→joinₗ (2-elter'.pashₗᵣ i e j k) =
    hcomp (λ r → λ {(k = i0) → inl (fst e , inr (elimI i (snd e i (fst e)) (snd e (notI i) (fst e))))
                   ; (k = i1) → push (fst e , (λ j₁ → inr (λ x → snd e x j₁))) (j ∧ r)
                   ; (j = i0) → inl (fst e , inr (elimIηPushTop* i (fst e) (snd e) k))
                   ; (j = i1) → compPath-filler
                                  (λ k₁ → inl (e .fst , inr (elimIη (λ x → snd e x (e .fst)) i k₁)))
                                  (push (fst e , (λ j₁ → inr (λ x → snd e x j₁)))) r k})
          (inl (fst e , inr (elimIη (λ x → snd e x (e .fst)) i k)))

module _ {ℓ : Level} {A : Type ℓ} {x1 x2 x3 x4 x5 x6 x7 : A}
   (p : x1 ≡ x2) (q : x4 ≡ x3) (r : x3 ≡ x2) (s : x1 ≡ x5)
   (t : x6 ≡ x5) (u : x6 ≡ x4) (m : x7 ≡ x1) (o : x3 ≡ x7) (l : x7 ≡ x6)
   (sq1 : Square o (sym p) r m)
   (sq2 : Square l s m t)
   (btm : Square o (sym u) (sym q) l)
  where
  the-coh-pplr-gen-fill : (i j r' : I) → A
  the-coh-pplr-gen-fill i j r' =
    hfill (λ r' → λ {(i = i0) → sq1 r' j
                    ; (i = i1) → doubleCompPath-filler (sym t) u refl r' ( ~ j)
                    ; (j = i0) → compPath-filler q r r' (~ i)
                    ; (j = i1) → sq2 r' i})
          (inS (btm i j))
          r'

  the-coh-pplr-gen : Square (sym p) (sym (sym t ∙∙ u ∙∙ refl)) (sym (q ∙ r)) s
  the-coh-pplr-gen i j = the-coh-pplr-gen-fill i j i1

module BoolCoh {ℓ : Level} (A : Bool → Bool → Type ℓ) where 
  open 2-elter' (RP∞'· ℓ) Bool A

  the-coh-pplr-f : (f : TotΠ (λ i → TotΠ (A i))) (i j r : I)
    → join-gen Bool (λ j → join-gen Bool (λ i → A i j))
  the-coh-pplr-f f = the-coh-pplr-gen-fill
    (λ i → inr λ x → push (x , (λ y → f y x)) i)
    (λ i → inl (false , inr (CasesBoolη (λ x → f x false) i))) _ _ _
    (λ i → inl (false , push (false , CasesBool true (f true false) (f false false)) i)) _ _ _
    (λ r j → push (false , (λ x → push (x , λ i → f i x) (~ j))) r)
    (λ r i → push (false , (λ x → inl (x , CasesBoolη (λ x → f x x) (~ i) x))) r)
    (λ i j → inl (false , push (false , CasesBoolη (λ x → f x false) (~ i)) (~ j)))

  the-coh-pplr-t : (f : TotΠ (λ i → TotΠ (A i))) (i j r : I)
    → join-gen Bool (λ j → join-gen Bool (λ i → A i j))
  the-coh-pplr-t f =
    the-coh-pplr-gen-fill (λ i → inr λ x → push (x , (λ y → f y x)) i)
      (λ i → inl (true , inr (CasesBoolη (λ x → f x true) i))) _ _ _
      (λ i → inl (true , push (true , CasesBool true (f true true) (f false true)) i)) _ _ _
      (λ r j → push (true , (λ x → push (x , (λ i → f i x)) (~ j))) r)
      (λ r i → push (true , λ x → inl (x , CasesBoolη (λ x → f x x) (~ i) x)) r)
      (λ i j → inl (true , push (true , CasesBoolη (λ x → f x true) (~ i)) (~ j)))  
  

  the-coh :  (a : TT.M.asPushoutBack (RP∞'· ℓ) Bool A (idEquiv Bool))
      → asPushout→joinₗ (RP∞'· ℓ) (RP∞'· ℓ) A (TT.M.asPushoutBack→ₗ (RP∞'· ℓ) Bool A (idEquiv Bool , a))
      ≡ inr (λ i → inl (i , TT.M.asPushoutBack→ᵣ (RP∞'· ℓ) Bool A (idEquiv Bool , a) .snd i))
  the-coh (2-elter'.ppl f) k = inr λ x → push (x , (λ i → f i x)) (~ k)
  the-coh (2-elter'.ppr false a b) =
      (λ k → inl (false , push (false , (CasesBool true (b false) a)) (~ k)))
    ∙ push (false , λ j → inl (j , CasesBool {A = λ x → A x x} true (b true) a j))
  the-coh (2-elter'.ppr true a b) =
      (λ k → inl (true , push (true , CasesBool true a (b true)) (~ k)))
    ∙ push (true , λ x → inl (x , CasesBool {A = λ z → A z z} true a (b false) x))
  the-coh (2-elter'.pplr false f i) j = the-coh-pplr-f f i j i1
  the-coh (2-elter'.pplr true f i) j = the-coh-pplr-t f i j i1

module _ {ℓ : Level} (I : RP∞' ℓ) (A : fst I →  fst I → Type ℓ) where 
  open 2-elter' I (fst I) A

  ppr-p : (i : fst I) (a : A i i) (b : (j : fst I) → A (notI i) j)
    → elimI {B = λ j → A j i} i a (b i) i ≡ elimI {B = λ i → A i i} i a (b (notI i)) i
  ppr-p i a b = elimIβ {B = λ k → A k i} i a (b i) .fst ∙∙ refl ∙∙ sym (elimIβ {B = λ k → A k k} i a (b (notI i)) .fst)

  the-coh :  (a : TT.M.asPushoutBack I (fst I) A (idEquiv (fst I)))
      → asPushout→joinₗ I I A (TT.M.asPushoutBack→ₗ I (fst I) A (idEquiv (fst I) , a))
      ≡ inr (λ i → inl (i , TT.M.asPushoutBack→ᵣ I (fst I) A (idEquiv (fst I) , a) .snd i))
  the-coh (2-elter'.ppl f) j = inr λ x → push (x , (λ j → f j x)) (~ j)
  the-coh (2-elter'.ppr i a b) =
    (λ k → inl (i , (sym (push (i , elimI {B = λ k → A k i} i a (b i)))
                   ∙ λ k → inl (i , ppr-p i a b k)) k))
    ∙ push (i , (λ j → inl (j , elimI i a (b (notI i)) j)))
  the-coh (2-elter'.pplr i f k) j =
    hcomp (λ r → λ {(j = i0) → compPath-filler
                                  (λ k₁ → inl (i , inr (elimIη (λ x → f x i) i k₁)))
                                  (push (i , (λ j₁ → inr (λ x → f x j₁)))) r (~ k)
                   ; (j = i1) → push (i , λ j → inl (j , elimIη {B = λ x → A x x} (λ x → f x x) i (~ k) j)) r
                   ; (k = i0) → push (i , (λ x → push (x , (λ m → f m x)) (~ j))) r
                   } )
      (inl (i , btm j k))
      where
      btm : Square {A = join-gen (fst I) (λ i₁ → A i₁ i)}
              (λ k → inr (elimIη {B = λ x → A x i} (λ x → f x i) i (~ k)))
              (λ k → inl (i , elimIη (λ x → f x x) i (~ k) i) )
              (sym (push (i , (λ m → f m i))))
              (sym (push (i , elimI {B = λ k → A k i} i (f i i) (f (notI i) i)))
             ∙ λ k → (inl (i , ppr-p i (f i i) (f (notI i)) k)))
      btm j k =
        hcomp (λ r → λ {(j = i0) → push (i , elimIη {B = λ x → A x i} (λ x → f x i) i (~ k)) r
                       ; (j = i1) → inl (i , elimIη (λ x → f x x) i (~ k) i)
                       ; (k = i0) → push (i , (λ m → f m i)) (~ j ∧ r)
                       ; (k = i1) → compPath-filler'
                                      (sym (push (i , elimI {B = λ k → A k i} i (f i i) (f (notI i) i))))
                                      (λ k → inl (i , ppr-p i (f i i) (f (notI i)) k)) r j})
              (inl (i , sts k j))
        where
        sts : Square (λ j → f i i) (ppr-p i (f i i) (f (notI i)))
                     (λ k → elimIη (λ x → f x i) i (~ k) i)
                     λ k → elimIη (λ x → f x x) i (~ k) i
        sts k j =
          hcomp (λ r → λ {(j = i0) → elimIη-id (λ x → f x i) i .fst (~ r) (~ k)
                         ; (j = i1) → elimIη-id (λ x → f x x) i .fst (~ r) (~ k)
                         ; (k = i0) → f i i
                         ; (k = i1) → ppr-p i (f i i) (f (notI i)) j})
                 (doubleCompPath-filler
                   (elimIβ {B = λ j → A j i} i (f i i) (f (notI i) i) .fst)
                   refl
                   (sym (elimIβ {B = λ j → A j j} i (f i i) (f (notI i) (notI i)) .fst)) k j)

asPushout→joinᵣₚ :
  {ℓ : Level} (I J : RP∞' ℓ) (e : fst I ≃ fst J) (A : fst I →  fst J → Type ℓ)
    →
    Σ[ F ∈ (((i : fst I) → A i (fst e i))
      → join-gen (fst J) (λ j → join-gen (fst I) (λ i → A i j))) ]
      ((a : TT.M.asPushoutBack I (fst J) A e)
        → asPushout→joinₗ I J A (TT.M.asPushoutBack→ₗ I (fst J) A (e , a))
          ≡ F (TT.M.asPushoutBack→ᵣ I (fst J) A (e , a) .snd)) 
asPushout→joinᵣₚ {ℓ} I =
  JRP∞'' I λ A → (λ f → inr λ i → inl (i , f i))
        , the-coh I A
  where
  open 2-elter' I (fst I)

asPushout→joinᵣₚ-refl : {ℓ : Level} (I : RP∞' ℓ) (A : fst I → fst I → Type ℓ)
  → asPushout→joinᵣₚ I I (idEquiv (fst I)) A
    ≡ ((λ f → inr λ i → inl (i , f i)) , (the-coh I A))
asPushout→joinᵣₚ-refl I = funExt⁻ (JRP∞''-refl I λ A → (λ f → inr λ i → inl (i , f i))
        , the-coh I A)

asPushout→join : {ℓ : Level} (I J : RP∞' ℓ) (A : fst I →  fst J → Type ℓ)
  → TT.M.asPushout I (fst J) A
  → join-gen (fst J) (λ j → join-gen (fst I) (λ i → A i j))
asPushout→join {ℓ} I J A (inl x) = asPushout→joinₗ I J A x
asPushout→join {ℓ} I J A (inr (e , p)) = asPushout→joinᵣₚ I J e A .fst p
asPushout→join {ℓ} I J A (push a i) = asPushout→joinᵣₚ I J (fst a) A .snd (snd a) i

bigTy : {ℓ : Level} (I : RP∞' ℓ) (i : fst I) (J : RP∞' ℓ) (A : fst I →  fst J → Type ℓ)
  → Type ℓ
bigTy I i J A = Σ[ g ∈ (join-gen (fst J) (A i) → join-gen (fst J) (λ j → join-gen (fst I) (λ i → A i j))) ]
      ((t : TotΠ (λ i₁ → join-gen (fst J) (A i₁)))
        → g (t i) ≡ asPushout→join I J A (asPushout← I J A t))

fun1 : {ℓ : Level} (J : RP∞' ℓ) (A : Bool →  fst J → Type ℓ)
  → join-gen (fst J) (A true)
  → join-gen (fst J) (λ j → join-gen Bool (λ i → A i j))
fun1 J A (inl (x , a)) = inl (x , inl (true , a))
fun1 J A (inr x) = inr λ j → inl (true , x j)
fun1 J A (push a i) = push (fst a , (λ j → inl (true , snd a j))) i


module _ {ℓ : Level} (J : RP∞' ℓ) (A : Bool →  fst J → Type ℓ) (e : fst J × TotΠ λ i → TotΠ (A i)) (i j : I) where  
  fun2ᵣ-false₁ : I → join-gen (fst J) (λ j₁ → join-gen Bool (λ i₁ → A i₁ j₁))
  fun2ᵣ-false₁ r =
    hfill (λ r → λ {(j = i0) → push (e .fst , (λ x → inl (true , snd e true x))) (r ∨ i)
                  ; (j = i1) → lUnit (push (fst e , (λ j₁ → inr (λ x → snd e x j₁)))) r i
                  ; (i = i0) → compPath-filler' (sym (push (e .fst , λ x → inl (true , snd e true x))))
                                                  (λ i → inl (e .fst , push (true , (λ x → snd e x (e .fst))) i)) r j
                  ; (i = i1) → inr (λ j₁ → push (true , (λ i → snd e i j₁)) j)})
          (inS (push (e .fst , (λ x → push (true , λ y → snd e y x) j)) i))
          r

  fun2ᵣ-false₂ : I → join-gen (fst J) (λ j₁ → join-gen Bool (λ i₁ → A i₁ j₁))
  fun2ᵣ-false₂ r =
    hfill (λ r → λ {(j = i0) → inr λ x → inl (true , snd e true x)
                  ; (j = i1) → ((λ i₁ → inl (e .fst , inr (CasesBoolη (λ x → snd e x (fst e)) (i₁ ∨ ~ r))))
                                ∙ push (fst e , λ j → inr (λ x → snd e x j))) i
                  ; (i = i0) → (sym (push (e .fst , λ x → inl (true , snd e true x)))
                               ∙ λ i → inl (e .fst , push (true , CasesBoolη (λ x → snd e x (e .fst)) (~ r)) i)) j
                  ; (i = i1) → inr (λ j₁ → push (true , (λ i → snd e i j₁)) j)})
         (inS (fun2ᵣ-false₁ i1))
         r

fun2 : {ℓ : Level} (J : RP∞' ℓ) (A : Bool →  fst J → Type ℓ)
  → (x : TT.M.ΠR-extend** (RP∞'· ℓ) (fst J) A)
  → fun1 J A (TT2.asPushout→Bool' (fst J) A (inl x) .fst)
   ≡ asPushout→join (RP∞'· ℓ) J A (inl x)
fun2 J A (2-elter'.inl (false , y)) =
    sym (push (y .fst .fst , λ j → inl (true , y .snd j)))
  ∙ λ k → inl (fst (fst y)
         , push (true , CasesBool true (snd y (fst (fst y))) (snd (fst y))) k)
fun2 J A (2-elter'.inl (true , y)) k =
  inl (fst (fst y) , push (true , CasesBool true (snd (fst y)) (snd y (fst (fst y)))) k)
fun2 J A (2-elter'.inr (inl x)) k = inl (fst x , push (true , snd x) k)
fun2 J A (2-elter'.inr (inr x)) k = inr (λ j → push (true , (λ i → x i j)) k)
fun2 J A (2-elter'.inr (push a i)) j = push (fst a , (λ r → push (true , (λ x → snd a x r)) j)) i
fun2 J A (2-elter'.pashₗ false e i₁) j =
  compPath-filler' (sym (push (e .fst , (λ j₁ → inl (true , e .snd .snd j₁)))))
     (λ k → inl (e .fst
           , push (true , (CasesBool {A = λ x → A x (e .fst)}
                             true (e .snd .snd (e .fst)) (e .snd .fst))) k))
     (~ i₁) j
fun2 J A (2-elter'.pashₗ true e i₁) j =
  inl (e .fst , push (true , CasesBool true (e .snd .fst) (e .snd .snd (e .fst))) j)
fun2 J A (2-elter'.pashᵣ false e i₁) j = fun2ᵣ-false₂ J A e i₁ j i1
fun2 J A (2-elter'.pashᵣ true e i₁) j = {!push (fst e , ?) i₁!}
fun2 J A (2-elter'.pashₗᵣ false e i₁ i₂) j = {!!}
fun2 J A (2-elter'.pashₗᵣ true e i₁ i₂) j = {!!}

module _ {ℓ : Level} {A : Bool → Bool → Type ℓ} where
  fun3-coh-ppl : (f : TotΠ (λ i → TotΠ (A i))) (i j r : I)
    → join-gen Bool (λ j → join-gen Bool (λ i → A i j))
  fun3-coh-ppl f i j r =
    hfill (λ r → λ {(i = i0) → push (true , (λ x → push (true , (λ y → f y x)) j)) r
                 ; (i = i1) → push (true , (λ x → inl (x , f x x))) (r ∧ j)
                 ; (j = i0) → push (true , (λ j₁ → inl (true , f true j₁))) (~ i ∧ r)
                 ; (j = i1) → push (true , (λ x → push (x , λ y → f y x) (~ i))) r})
        (inS (inl (true , push (true , (λ y → f y true)) (~ i ∧ j))))
        r

  fun₃-coh-true : (a : A true true) (b : TotΠ (A false)) (i j r : I)
    → join-gen Bool (λ j → join-gen Bool (λ i → A i j))
  fun₃-coh-true a b i j r =
    hfill (λ r → λ {(i = i0) → inl (true , push (true , (CasesBool {A = λ x → A x true} true a (b true))) (j ∨ ~ r))
                    ; (i = i1) → push (true , (λ i₁ → inl (i₁ , CasesBool-true {A = λ x → A x x} i₁ a (b false)))) (j ∧ r)
                    ; (j = i0) → inl (true , push (true , (CasesBool {A = λ x → A x true} true a (b true))) (~ r ∧ ~ i))
                    ; (j = i1) → compPath-filler (λ i → inl (true , push (true , CasesBool true a (b true)) (~ i)))
                                                  (push (true , λ x → inl (x , CasesBool {A = λ x → A x x} true a (b false) x)) ) r i})
        (inS (inl (true , push (true , CasesBool true a (b true)) (~ i))))
        r

  module _ (a : A false false) (b : TotΠ (A true)) (i j : I) where
    fun₃-coh-false₁ : I → join-gen Bool (λ j → join-gen Bool (λ i → A i j))
    fun₃-coh-false₁ =
      hfill (λ r → λ {(i = i0) → rUnit (sym (push (false , CasesBool true (inl (true , b true)) (inr (CasesBool true (b false) a))))) r j
                    ; (i = i1) → push (true , CasesBool true (inl (true , b true)) (inr (CasesBool true (b false) a))) (j ∨ ~ r)
                    ; (j = i0) → push (true , CasesBool true (inl (true , b true)) (inr (CasesBool true (b false) a))) (~ i ∨ ~ r)
                    ; (j = i1) → lUnit (push (false , CasesBool true (inl (true , b true)) (inr (CasesBool true (b false) a)))) r i})
               (inS (push (false , CasesBool true (inl (true , b true)) (inr (CasesBool true (b false) a))) (i ∨ ~ j)))

    fun₃-coh-false₂ : I → join-gen Bool (λ j → join-gen Bool (λ i → A i j))
    fun₃-coh-false₂ =
      hfill (λ r → λ {(i = i0) → (sym (push (false , (CasesBool {A = λ x → join-gen Bool (λ i₁ → A i₁ x)} true (inl (true , b true)) (push (true , CasesBool true (b false) a) (~ r)))))
                                ∙ λ j → inl (false , push (true , CasesBool {A = λ x → A x false} true (b false) a) (~ r ∨ j))) j
                    ; (i = i1) → push (true , CasesBool true (inl (true , b true)) (push (false , CasesBool true (b false) a) (~ r))) j
                    ; (j = i0) → push (true , λ x → CasesBool {A = λ x → join-gen Bool (λ i₁ → A i₁ x)} true
                                   (inl (true , b true))
                                   (push (true , CasesBool true (b false) a) (~ r)) x) (~ i)
                    ; (j = i1) → ((λ i → inl (false , push (false , CasesBool true (b false) a) (~ i ∨ ~ r)))
                                 ∙ push (false , CasesBool true (inl (true , b true)) (push (false , CasesBool true (b false) a) (~ r)))) i})
              (inS (fun₃-coh-false₁ i1))

    fun₃-coh-false₃ : I → join-gen Bool (λ j → join-gen Bool (λ i → A i j))
    fun₃-coh-false₃ =
      hfill (λ r → λ {(i = i0) → (sym (push (false , λ x → CasesBoolη {A = λ x → join-gen Bool (λ i₁ → A i₁ x)} (λ x₁ → inl (true , b x₁)) r x))
                             ∙ λ j → inl (false , push (true , CasesBool {A = λ x → A x false} true (b false) a) j)) j
                 ; (i = i1) → push (true , CasesBoolη {A = λ j₁ → join-gen Bool (λ i₁ → A i₁ j₁)}
                                              (λ x → inl (x , CasesBool {A = λ z → A z z} true (b true) a x)) r) j
                 ; (j = i0) → push (true , λ x → CasesBoolη {A = λ x → join-gen Bool (λ i₁ → A i₁ x)} (λ x → inl (true , b x)) r x) (~ i) 
                 ; (j = i1) → ((λ i → inl (false , push (false , CasesBool {A = λ x → A x false} true (b false) a) (~ i)))
                                   ∙ push (false , CasesBoolη {A = λ j₁ → join-gen Bool (λ i₁ → A i₁ j₁)}
                                                (λ x → inl (x , CasesBool {A = λ z → A z z} true (b true) a x)) r)) i })
             (inS (fun₃-coh-false₂ i1))

fun3-coh-bool : ∀ {ℓ} {A : Bool → Bool → Type ℓ}
  → (p : TT.M.asPushoutBack (RP∞'· ℓ) (fst (RP∞'· ℓ)) A (idEquiv _))
  → PathP (λ i → (fun1 (RP∞'· ℓ) A
          (TT.makeWithHah.asPushout→ (RP∞'· ℓ) (fst (RP∞'· ℓ)) A
           (TT2.HAH-Bool (fst (RP∞'· ℓ)) A)
           (push (idEquiv (fst (RP∞'· ℓ)) , p) i) true))
         ≡ BoolCoh.the-coh  A p i)
           (fun2 (RP∞'· ℓ) A
            (TT.M.asPushoutBack→ₗ (RP∞'· ℓ) (fst (RP∞'· ℓ)) A
             (idEquiv (fst (RP∞'· ℓ)) , p)))
           (push (true , λ i₁ → inl (i₁ , TT.M.asPushoutBack→ᵣ-pre (RP∞'· ℓ) Bool A (idEquiv Bool) p i₁)))
fun3-coh-bool {A = A} (2-elter'.ppl f) i j = fun3-coh-ppl f i j i1
fun3-coh-bool {A = A} (2-elter'.ppr false a b) i j = fun₃-coh-false₃ a b i j i1
fun3-coh-bool {A = A} (2-elter'.ppr true a b) i j = fun₃-coh-true a b i j i1
fun3-coh-bool {A = A} (2-elter'.pplr false f k) i j = help j i k
  where -- j i k
  help : Cube (λ i k → push (true , (λ j₁ → inl (true , f true j₁))) (~ i))
              (λ i k → BoolCoh.the-coh-pplr-f A f k i i1)
              (λ j k → fun2ᵣ-false₂ (RP∞'· _) A (false , f) (~ k) j i1)
              (λ j k → push (true , λ x → inl (x , CasesBoolη (λ x → f x x) (~ k) x)) j)
              (λ j i → fun3-coh-ppl f i j i1)
              (λ j i → fun₃-coh-false₃ (f false false) (f true) i j i1)
  help j i k =
    hcomp (λ r → λ {(j = i0) → {!!} -- push (true , (CasesBoolη (λ x → inl (true , f true x)) r)) (~ i)
                   ; (j = i1) → {!BoolCoh.the-coh-pplr-f A f k i r!}
                   ; (i = i0) → fun2ᵣ-false₂ (RP∞'· _) A (false , f) (~ k) j i1
                   ; (i = i1) → {!push (true , ?) !} -- push (true , CasesBoolη (λ x → inl (x , CasesBoolη (λ x₁ → f x₁ x₁) (~ k) x)) r) j
                   ; (k = i0) → {!!} -- fun3-coh-ppl f i j r -- fun3-coh-ppl f i j r
                   ; (k = i1) → {!!} }) -- fun₃-coh-false₃ (f false false) (f true) i j r})
          {!!}
fun3-coh-bool {A = A} (2-elter'.pplr true f i₂) i j = {!!}

-- fun3-coh : ∀ {ℓ} {A : Bool → Bool → Type ℓ}
--   → (p : TT.M.asPushoutBack (RP∞'· ℓ) (fst (RP∞'· ℓ)) A (idEquiv _))
--   → PathP (λ i → (fun1 (RP∞'· ℓ) A
--           (TT.makeWithHah.asPushout→ (RP∞'· ℓ) (fst (RP∞'· ℓ)) A
--            (TT2.HAH-Bool (fst (RP∞'· ℓ)) A)
--            (push (idEquiv (fst (RP∞'· ℓ)) , p) i) true))
--          ≡ the-coh (RP∞'· ℓ) A p i)
--            (fun2 (RP∞'· ℓ) A
--             (TT.M.asPushoutBack→ₗ (RP∞'· ℓ) (fst (RP∞'· ℓ)) A
--              (idEquiv (fst (RP∞'· ℓ)) , p)))
--            (push (true , λ i₁ → inl (i₁ , TT.M.asPushoutBack→ᵣ-pre (RP∞'· ℓ) Bool A (idEquiv Bool) p i₁)))
-- fun3-coh {A = A} (2-elter'.ppl f) i j =
--   hcomp (λ k → λ {(i = i0) → inr (λ j₁ → push (true , (λ i₁ → f i₁ j₁)) (~ k ∨ j))
--                  ; (i = i1) → push (true , (λ i₁ → push (i₁ , (λ k → f k i₁)) (~ k))) j
--                  ; (j = i0) → push (true , (λ j₁ → push (true , (λ i → f i j₁)) (~ k))) (~ i)
--                  ; (j = i1) → inr (λ x → push (x , (λ j₁ → f j₁ x)) (~ i ∨ ~ k))})
--         (push (true , (λ i₁ → inr (λ k → f k i₁))) (~ i ∨ j))
-- fun3-coh {A = A} (2-elter'.ppr false a b) i j =
--   hcomp (λ r → λ {(j = i0) → push (true , (λ j₁ → inl (true , b j₁)))  (~ i ∨ ~ r)
--                  ; (j = i1) → {!!}
--                  ; (i = i1) → {!!} -- push (true , λ x → inl (x , CasesBool {A = λ t → A t t} true (b true) a x)) j
--                  })
--     {!!} -- (push (true , λ x → inl (x , CasesBool {A = λ t → A t t} true (b true) a x)) j)
-- fun3-coh {A = A} (2-elter'.ppr true a b) i j =
--   {!Goal: Pushout (λ a₁ → fst a₁ , snd a₁ (fst a₁)) (λ r → snd r)
-- ———— Boundary (wanted) —————————————————————————————————————
-- j = i0 ⊢ push (true , (λ j₁ → inl (true , b j₁))) (~ i)
-- j = i1 ⊢ hcomp
--          (doubleComp-faces
--           (λ _ → inl (false , inr (λ y → CasesBool-true y (b false) a)))
--           (push (false , (λ i₁ → inl (i₁ , CasesBool-true i₁ (b true) a))))
--           i)
--          (inl
--           (false ,
--            hcomp
--            (doubleComp-faces (λ _ → inr (λ y → CasesBool-true y (b false) a))
--             (λ k →
--                inl (false , hcomp (doubleComp-faces (λ _ → a) (λ i₁ → a) k) a))
--             i)
--            (push (false , (λ y → CasesBool-true y (b false) a)) (~ i))))
-- i = i0 ⊢ hcomp
--          (doubleComp-faces (λ _ → inr (λ j₁ → inl (true , b j₁)))
--           (λ k →
--              inl (false , push (true , (λ y → CasesBool-true y (b false) a)) k))
--           j)
--          (push (false , (λ j₁ → inl (true , b j₁))) (~ j))
-- i = i1 ⊢ push
--          (true , (λ i₁ → inl (i₁ , CasesBool-true i₁ (b true) a))) j!}
-- fun3-coh {A = A} (2-elter'.pplr false f i₂) i j = {!!}
-- fun3-coh {A = A} (2-elter'.pplr true f i₂) i j = {!!}

-- fun3 : {ℓ : Level} (J : RP∞' ℓ) (e : Bool ≃ fst J)
--   (A : Bool → fst J → Type ℓ)
--   → Σ[ F ∈ ((p : (i : Bool) → A i (fst e i))
--   → inl (fst e true , inl (true , p true))
--     ≡ asPushout→joinᵣₚ (RP∞'· ℓ) J e A .fst p ) ]
--     ((p : TT.M.asPushoutBack (RP∞'· ℓ) (fst J) A e)
--     → PathP (λ i → fun1 J A (TT2.asPushout→Bool' (fst J) A (push (e , p) i) .fst)
--                    ≡ asPushout→joinᵣₚ (RP∞'· ℓ) J e A .snd p i)
--              (fun2 J A (TT.M.asPushoutBack→ₗ (RP∞'· ℓ) (fst J) A (e , p)))
--              (F (TT.M.asPushoutBack→ᵣ (RP∞'· ℓ) (fst J) A (e , p) .snd)))
-- fun3 {ℓ} = JRP∞'' (RP∞'· _)  λ A
--   → (λ p → push (true , (λ j → inl (j , p j)))
--             ∙ sym (funExt⁻ (cong fst (asPushout→joinᵣₚ-refl (RP∞'· _) A)) p))
--    , SQ
--    where
--    SQ : {A : Bool → Bool → Type ℓ}
--      → (p : TT.M.asPushoutBack (RP∞'· ℓ) (fst (RP∞'· ℓ)) A (idEquiv _))
--      → PathP (λ i →
--          fun1 (RP∞'· ℓ) A
--          (TT2.asPushout→Bool' (fst (RP∞'· ℓ)) A
--           (push (idEquiv (fst (RP∞'· ℓ)) , p) i) .fst)
--          ≡ asPushout→joinᵣₚ (RP∞'· ℓ) (RP∞'· ℓ) (idEquiv (fst (RP∞'· ℓ))) A .snd p i)
--          (fun2 (RP∞'· ℓ) A (TT.M.asPushoutBack→ₗ (RP∞'· ℓ) (fst (RP∞'· ℓ)) A
--            (idEquiv (fst (RP∞'· ℓ)) , p)))
--          (push (true , (λ j → inl (j , TT.M.asPushoutBack→ᵣ (RP∞'· ℓ) (fst (RP∞'· ℓ)) A (idEquiv _ , p) .snd j)))
--             ∙ sym (funExt⁻ (cong fst (asPushout→joinᵣₚ-refl (RP∞'· _) A))
--                 (TT.M.asPushoutBack→ᵣ (RP∞'· ℓ) (fst (RP∞'· ℓ)) A (idEquiv _ , p) .snd)))
--    SQ {A = A} p i j =
--      hcomp (λ k → λ {(j = i0) → fun1 (RP∞'· ℓ) A (TT.makeWithHah.asPushout→ (RP∞'· ℓ) (fst (RP∞'· ℓ)) A
--                                    (TT2.HAH-Bool (fst (RP∞'· ℓ)) A) (push (idEquiv (fst (RP∞'· ℓ)) , p) i) true)
--                     ; (j = i1) → asPushout→joinᵣₚ-refl (RP∞'· _) A (~ k) .snd p i
--                     ; (i = i0) → fun2 (RP∞'· ℓ) A (TT.M.asPushoutBack→ₗ (RP∞'· ℓ) (fst (RP∞'· ℓ)) A
--                                     (idEquiv (fst (RP∞'· ℓ)) , p)) j })
--            (fun3-coh p i j)

-- fun1-id : {ℓ : Level} (J : RP∞' ℓ) (A : Bool →  fst J → Type ℓ)
--   → (y : TT.M.asPushout (RP∞'· ℓ) (fst J) A)
--   → fun1 J A (TT2.asPushout→Bool' (fst J) A y .fst) ≡ asPushout→join (RP∞'· ℓ) J A y
-- fun1-id J A (inl x) = fun2 J A x
-- fun1-id J A (inr (e , p)) = fun3 J e A .fst p
-- fun1-id J A (push (e , p) i) = fun3 J e A .snd p i

-- lem1 : {ℓ : Level} (I : RP∞' ℓ) (i : fst I) (J : RP∞' ℓ) (A : fst I →  fst J → Type ℓ)
--   → bigTy I i J A
-- lem1 {ℓ} =
--   JRP∞' λ J A → (fun1 J A)
--   , λ F → cong (fun1 J A)
--            ((cong fst (main J A F)))
--          ∙ fun1-id J A (asPushout← (RP∞'· ℓ) J A F)
--   where
--   main : (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ) (F : TotΠ (λ i₁ → join-gen (fst J) (A i₁)))
--     → ΠBool→× F  ≡ TT2.asPushout→Bool' (fst J) A (asPushout← (RP∞'· ℓ) J A F)
--   main J A F = sym (cong (Iso.fun ΠBool×Iso) (funExt⁻ (TT2.asPushout→Bool≡ (fst J) A) (asPushout← (RP∞'· ℓ) J A F))
--              ∙ cong ΠBool→× (secEq (_ , asPushout→-isEquiv (RP∞'· _) J A) F))

-- mainFun : {ℓ : Level} (I J : RP∞' ℓ) (A : fst I →  fst J → Type ℓ)
--   → join-gen (fst I) (λ i → join-gen (fst J) (A i))
--   → join-gen (fst J) (λ j → join-gen (fst I) (λ i → A i j))
-- mainFun I J A =
--   join-gen-ind
--     (λ x → asPushout→join I J A (asPushout← I J A x))
--     λ i → lem1 I i J A

-- module _ {ℓ : Level} (I J : RP∞' ℓ) (A : fst I →  fst J → Type ℓ) where
  
