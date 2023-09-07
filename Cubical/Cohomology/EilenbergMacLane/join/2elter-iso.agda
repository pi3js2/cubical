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
module Cubical.Cohomology.EilenbergMacLane.join.2elter-iso where
open import Cubical.HITs.Join
open import Cubical.Functions.FunExtEquiv


RP∞J : ∀ {ℓ ℓ'} {I : RP∞' ℓ} (A : (J : RP∞' ℓ) (e : fst I ≃ fst J) → Type ℓ')
  → A I (idEquiv (fst I))
  → (J : _) (e : _) → A J e
RP∞J {I = I} A ind J e = transport (λ i → A (ua' i) (h2 i)) ind
  where
  ua' : I ≡ J
  ua' = Σ≡Prop (λ _ → isPropIsRP∞ _ _) (ua e)

  h2 : PathP (λ i → fst I ≃ ua e i) (idEquiv (fst I)) e
  h2 = toPathP (Σ≡Prop (λ _ → isPropIsEquiv _)
        (funExt λ i → λ j → transportRefl (fst e (transportRefl i j)) j))

module _ where
  open 2-elter'
  asPushout-elim : ∀ {ℓ ℓ'} (I : RP∞' ℓ)
    → (Goal : (J : Type) (A : fst I → J → Type ℓ) → asPushout I J A → Type ℓ')
    → (left : (J : Type) (A : fst I → J → Type ℓ) (x : ΠR-extend** I J A) → Goal J A (inl x))
    → (right : (A : fst I → fst I → Type ℓ) (x : (i : fst I) → A i i) → Goal (fst I) A (inr ((idEquiv (fst I)) , x)))
    → (pash : (A : fst I → fst I → Type ℓ) (x : asPushoutBack I (fst I) A (idEquiv (fst I)))
            → PathP (λ j → Goal (fst I) A (push ((idEquiv (fst I)) , x) j))
                     (left (fst I) A (asPushoutBack→ₗ I (fst I) A (idEquiv (fst I) , x)))
                     (right A (asPushoutBack→ᵣ-pre I (fst I) A (idEquiv (fst I)) x)))
    → (J : Type) (A : fst I → J → Type ℓ) (x : 2-elter'.asPushout I J A) → Goal J A x
  asPushout-elim {ℓ} I Goal left right pash J A =
    elimPushout (left J A)
      (uncurry λ e y → help J e A .fst y)
      (uncurry λ e y → help J e A .snd y)
    where
    help : (J : Type) (x : fst I ≃ J) (A : fst I → J → Type ℓ)
      → Σ[ F ∈ ((y : (i : fst I) → A i (fst x i)) → Goal J A (inr (x , y))) ]
          ((y : asPushoutBack I J A x) →
           PathP (λ i → Goal J A (push (x , y) i))
           (left J A (asPushoutBack→ₗ I J A (x , y)))
           (F (asPushoutBack→ᵣ-pre I J A x y)))
    help J = EquivJrev (λ J x → (A : fst I → J → Type ℓ)
      → Σ[ F ∈ ((y : (i : fst I) → A i (fst x i)) → Goal J A (inr (x , y))) ]
          ((y : asPushoutBack I J A x) →
           PathP (λ i → Goal J A (push (x , y) i))
           (left J A (asPushoutBack→ₗ I J A (x , y)))
           (F (asPushoutBack→ᵣ-pre I J A x y))))
           λ A → (right A) , (pash A)

  asPushout-elim' : ∀ {ℓ ℓ'} (I : RP∞' ℓ)
    → (Goal : (J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) → asPushout I (fst J) A → Type ℓ')
    → (left : (J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) (x : ΠR-extend** I (fst J) A) → Goal J A (inl x))
    → (right : (A : fst I → fst I → Type ℓ) (x : (i : fst I) → A i i) → Goal I A (inr ((idEquiv (fst I)) , x)))
    → (pash : (A : fst I → fst I → Type ℓ) (x : asPushoutBack I (fst I) A (idEquiv (fst I)))
            → PathP (λ j → Goal I A (push ((idEquiv (fst I)) , x) j))
                     (left I A (asPushoutBack→ₗ I (fst I) A (idEquiv (fst I) , x)))
                     (right A (asPushoutBack→ᵣ-pre I (fst I) A (idEquiv (fst I)) x)))
    → (J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) (x : 2-elter'.asPushout I (fst J) A) → Goal J A x
  asPushout-elim' {ℓ} I Goal left right pash J A =
    elimPushout (left J A)
      (uncurry (λ x → help J x A .fst))
      (uncurry (λ x → help J x A .snd))
    where
    help : (J : RP∞' ℓ) (x : fst I ≃ fst J) (A : fst I → fst J → Type ℓ)
      → Σ[ F ∈ ((y : (i : fst I) → A i (fst x i)) → Goal J A (inr (x , y))) ]
          ((y : asPushoutBack I (fst J) A x) →
           PathP (λ i → Goal J A (push (x , y) i))
           (left J A (asPushoutBack→ₗ I (fst J) A (x , y)))
           (F (asPushoutBack→ᵣ-pre I (fst J) A x y)))
    help = RP∞J {I = I} (λ J x → (A : fst I → fst J → Type ℓ)
      → Σ[ F ∈ ((y : (i : fst I) → A i (fst x i)) → Goal J A (inr (x , y))) ]
          ((y : asPushoutBack I (fst J) A x) →
           PathP (λ i → Goal J A (push (x , y) i))
           (left J A (asPushoutBack→ₗ I (fst J) A (x , y)))
           (F (asPushoutBack→ᵣ-pre I (fst J) A x y))))
           λ A → (right A) , (pash A)
  

ΠR-extend→Π*-pashB : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
  → (a : 2-elter'.PushTop (RP∞'· ℓ) (fst J) A) →
      2-elter'.ΠR-extend→Πₗ (RP∞'· ℓ) (fst J) A
      (2-elter'.PushTop→left-push (RP∞'· ℓ) (fst J) A a) true
      ≡
      2-elter'.ΠR-base→ (RP∞'· ℓ) (fst J) A
      (2-elter'.PushTop→ΠR-base (RP∞'· ℓ) (fst J) A a) true
ΠR-extend→Π*-pashB J A (false , inl (f , p)) =
  sym (push* (evalG f true , p .snd (evalG f true)) (snd p) refl)
ΠR-extend→Π*-pashB J A (true , inl (f , p)) = refl
ΠR-extend→Π*-pashB J A (false , inr x) = refl
ΠR-extend→Π*-pashB J A (true , inr (f , p)) =
  push* (f , p true f) (p true) refl
ΠR-extend→Π*-pashB {ℓ} J A (false , push (f , p) i) j =
  hcomp (λ k → λ {(i = i0) → push* (evalG f true , p true (evalG f true)) (p true) refl (~ j)
                 ; (i = i1) → push* (evalG f true , p true (evalG f true)) (p true) refl (k ∨ ~ j)
                 ; (j = i0) → inrR (p true)
                 ; (j = i1) → 2-elter'.ΠR-base→ (RP∞'· ℓ) (fst J) A
                                 (compPath-filler
                                   ((λ j → inl (f , 2-elter'.elimIηPushTop (RP∞'· ℓ) (fst J) A false f p j)))
                                   (push (f , p)) k i) true})
        (push* (evalG f true , p true (evalG f true)) (p true) refl (~ j))
ΠR-extend→Π*-pashB {ℓ} J A (true , push (f , p) i) j =
  hcomp (λ k → λ {(i = i0) → inlR (evalG f true , p true (evalG f true))
                 ; (i = i1) → push* (evalG f true , p true (evalG f true)) (p true) refl (j ∧ k)
                 ; (j = i0) → inlR (evalG f true , p true (evalG f true))
                 ; (j = i1) → 2-elter'.ΠR-base→ (RP∞'· ℓ) (fst J) A
                                 (compPath-filler
                                   ((λ j → inl (f , 2-elter'.elimIηPushTop (RP∞'· ℓ) (fst J) A true f p j)))
                                   (push (f , p)) k i) true})
         (inlR (evalG f true , p true (evalG f true)))

ΠR-extend→Π*-pashT : ∀ {ℓ} (I : RP∞' ℓ) (i : fst I)
  → Type _
ΠR-extend→Π*-pashT {ℓ = ℓ} I i = (J : RP∞' ℓ) (A : fst I → fst J → Type _) (a : _)
  → 2-elter'.ΠR-extend→Πₗ I (fst J) A
      (2-elter'.PushTop→left-push I (fst J) A a) i
   ≡ 2-elter'.ΠR-base→ I (fst J) A
      (2-elter'.PushTop→ΠR-base I (fst J) A a) i

ΠR-extend→Π*-pash : ∀ {ℓ} (I : RP∞' ℓ) (i : fst I) (J : RP∞' ℓ)
  (A : fst I → fst J → Type ℓ) (a : _)
  → 2-elter'.ΠR-extend→Πₗ I (fst J) A
      (2-elter'.PushTop→left-push I (fst J) A a) i
   ≡ 2-elter'.ΠR-base→ I (fst J) A
      (2-elter'.PushTop→ΠR-base I (fst J) A a) i
ΠR-extend→Π*-pash =
  JRP∞' {B = λ I i → ΠR-extend→Π*-pashT I i} ΠR-extend→Π*-pashB

ΠR-extend→Π* : ∀ {ℓ} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
  → 2-elter'.ΠR-extend I (fst J) A
  → TotΠ (λ i → joinR-gen (fst J) (A i))
ΠR-extend→Π* I J A (inl x) = 2-elter'.ΠR-extend→Πₗ I (fst J) A x 
ΠR-extend→Π* I J A (inr x) = 2-elter'.ΠR-base→ I (fst J) A x
ΠR-extend→Π* I J A (push a i) k =
  ΠR-extend→Π*-pash I k J A a i

ΠR-extend→Π*atTrue : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
  → 2-elter'.ΠR-extend (RP∞'· ℓ) (fst J) A → joinR-gen (fst J) (A true)
ΠR-extend→Π*atTrue J A =
  elimPushout (λ f → 2-elter'.ΠR-extend→Πₗ (RP∞'· _) (fst J) A f true)
              (λ f → 2-elter'.ΠR-base→ (RP∞'· _) (fst J) A f true)
              (ΠR-extend→Π*-pashB J A)

ΠR-extend→Π*atTrue≡ : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
  → (x : 2-elter'.ΠR-extend (RP∞'· ℓ) (fst J) A )
  → (ΠR-extend→Π* (RP∞'· ℓ) J A x true) ≡ (ΠR-extend→Π*atTrue J A x)
ΠR-extend→Π*atTrue≡ J A (inl x) = refl
ΠR-extend→Π*atTrue≡ J A (inr x) = refl
ΠR-extend→Π*atTrue≡ J A (push a i) j =
  JRP∞'∙ {B = λ I i → ΠR-extend→Π*-pashT I i} ΠR-extend→Π*-pashB j J A a i


module _ {ℓ : Level} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) where
  private
    module 1st = 2-elter I (fst J) A
    module 2nd = 2-elter' I (fst J) A

  Isor : Iso 2nd.ΠR-base 1st.ΠR-base
  Isor = pushoutIso _ _ _ _ (isoToEquiv (invIso is1)) (isoToEquiv (invIso (TotAIso I J {A = A}))) (idEquiv _)
                            refl refl
    where
    is1 : Iso _ 2nd.ΠR-base-back
    is1 = compIso (invIso (Σ-cong-iso-fst (invIso (TotAIso I J))))
           (compIso
             Σ-assoc-Iso
             (Σ-cong-iso-snd
               λ f → compIso
                 (invIso Σ-assoc-Iso)
                 (compIso
                   (invIso (Σ-cong-iso-fst (invIso Σ-swap-Iso)))
                   (compIso Σ-assoc-Iso
                     (compIso (Σ-cong-iso-snd
                       (λ r → compIso (Σ-cong-iso-snd (λ r → funExtIso)) (isContr→Iso (h f r) isContrUnit)))
                       rUnit×Iso)))))
      where
      h : (f : fst J ⊎ (fst I ≃ fst J)) (r : (i : fst I) (j : fst J) → A i j)
        → isContr (Σ[ g ∈ ((i : fst I) → A i (fst (2-eltFun {I = I} {J}) f i)) ]
                      (Path ((i : fst I) → _) (λ x → r x (fst (2-eltFun {I = I} {J}) f x)) λ x → g x))
      h f r = isContrSingl _

  Isor-alt : 2nd.ΠR-base → 1st.ΠR-base
  Isor-alt (inl (f , p)) = inl λ i → (evalG f i) , (p i)
  Isor-alt (inr x) = inr x
  Isor-alt (push a i) = push ((λ i → (evalG (fst a) i)
                            , (snd a i (evalG (fst a) i)))
                            , ((snd a) , (λ _ → refl))) i

  ΠR-base≃ : 2nd.ΠR-base ≃ 1st.ΠR-base 
  fst ΠR-base≃ = Isor-alt
  snd ΠR-base≃ = subst isEquiv (funExt help) (isoToIsEquiv Isor)
    where
    help : (x : _) → Iso.fun Isor x ≡ Isor-alt x
    help (inl x) = refl
    help (inr x) = refl
    help (push a i) j = rUnit (push ((λ i → (evalG (fst a) i)
                            , (snd a i (evalG (fst a) i)))
                            , ((snd a) , (λ _ → refl)))) (~ j) i

  helpIso33 : (i : fst I) (f : fst J ⊎ (fst I ≃ fst J))
    → (r : ((j : fst J) → A (1st.notI i) j))
    → Iso (A i (2nd.eval f i))
           (Σ[ g ∈ ((i : fst I) → A i (evalG f i)) ]
               r (evalG f (1st.notI i)) ≡ g (1st.notI i))
  Iso.fun (helpIso33 i f r) a =
      (1st.elimI {B = λ x → A x (evalG f x)} i a (r _))
    , sym (1st.elimIβ {B = λ x → A x (evalG f x)} i a (r _) .snd)
  Iso.inv (helpIso33 i f r) (a , p) = a i
  Iso.rightInv (helpIso33 i f r) (a , p) =
    ΣPathP ((funExt (1st.elimI {B = λ x → 1st.elimI {B = λ x → A x (evalG f x)} i (a i) (r _) x ≡ a x} i (1st.elimIβ i (a i) (r (evalG f (1st.notI i))) .fst)
                                 (1st.elimIβ i (a i) (r (evalG f (1st.notI i))) .snd ∙∙ refl ∙∙ p)))
      , flipSquare (doubleCompPath-filler (1st.elimIβ i (a i) (r (evalG f (1st.notI i))) .snd) refl p
        ▷ ((sym (1st.elimIβ {B = λ x → 1st.elimI {B = λ x → A x (evalG f x)} i (a i) (r _) x ≡ a x}
          i (1st.elimIβ i (a i) (r (evalG f (1st.notI i))) .fst)
             (1st.elimIβ i (a i) (r (evalG f (1st.notI i))) .snd ∙∙ refl ∙∙ p) .snd)))))
  Iso.leftInv (helpIso33 i f r) a = 1st.elimIβ {B = λ x → A x (evalG f x)} i a (r _) .fst


module _ {ℓ : Level} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ) where
  private
    module 1st = 2-elter (RP∞'· ℓ) (fst J) A
    module 2nd = 2-elter' (RP∞'· ℓ) (fst J) A

  is1* : 2nd.fat → 1st.fat
  is1* (f , p) = (λ i → (evalG f i) , p i (evalG f i))
    , p , (λ _ → refl)

  is*' : 1st.fat → 2nd.fat
  fst (is*' (f , p , q)) = invEq (2-eltFun {I = RP∞'· ℓ} {J}) (fst ∘ f)
  snd (is*' (f , p , q)) = p

  myIs : Iso 2nd.fat 1st.fat
  Iso.fun myIs = is1*
  Iso.inv myIs = is*'
  Iso.rightInv myIs (f , p , q) = bah (fst ∘ f) p (snd ∘ f) (funExt q)
    where
    bah : (f1 : (i : Bool) → fst J) 
      → (p : TotΠ (λ i → TotΠ (A i)))
      → (f2 : (x : Bool) → A x (f1 x))
      → (q : (λ x → p x (f1 x)) ≡ f2)
      → is1* (is*' (((λ i → f1 i , f2 i) , (p , (λ i j → q j i)))))
      ≡ ((λ i → f1 i , f2 i) , (p , (λ i j → q j i)))
    bah f1 p = J> (ΣPathP (funExt (λ a → ΣPathP (funExt⁻ (secEq (2-eltFun {I = RP∞'· ℓ} {J}) f1) a , λ j → p a (secEq (2-eltFun {I = RP∞'· ℓ} {J}) f1 j a)))
      , λ j → p , (λ i k' → p i (secEq (2-eltFun {I = RP∞'· ℓ} {J}) f1 j i))))
  Iso.leftInv myIs (f , p) = ΣPathP ((retEq (2-eltFun {I = RP∞'· ℓ} {J}) f) , refl)

  is1 : 2nd.fat ≃ 1st.fat
  is1 = isoToEquiv myIs

  is2 : 2nd.left-push↑ₗ true ≃ 1st.left-push↑ₗ true
  is2 = isoToEquiv
    (invIso (compIso
      (invIso (Σ-cong-iso-fst (invIso (TotAIso (RP∞'· ℓ) J {A = A}))))
      (compIso Σ-assoc-Iso
        (Σ-cong-iso-snd λ f
          → compIso (compIso (invIso Σ-assoc-Iso)
              (compIso (invIso (Σ-cong-iso-fst (invIso Σ-swap-Iso))) Σ-assoc-Iso))
               (compIso
                 (Σ-cong-iso-snd
                   (λ r → invIso (helpIso33 (RP∞'· ℓ) J A true f r)))
                 Σ-swap-Iso)))))

  is3 : 2nd.left-push↑ᵣ true ≃ 1st.left-push↑ᵣ true
  is3 = isoToEquiv (invIso
    (compIso
      Σ-assoc-Iso
      (Σ-cong-iso-snd
        λ j → compIso (invIso Σ-assoc-Iso)
          (compIso
            (invIso (Σ-cong-iso-fst (invIso Σ-swap-Iso)) )
            (compIso
              Σ-assoc-Iso
              (compIso
                (Σ-cong-iso-snd
                  (λ g → isContr→Iso (isContrSingl _) isContrUnit))
                rUnit×Iso))))))

{-
(funExt (uncurry (⊎.elim (λ j y → ΣPathP ((funExt (CasesBool true refl refl)) , refl)) λ b y → ΣPathP ((funExt (CasesBool true refl refl)) , refl))))
-}
  inl* : _ → Pushout (1st.fat→ₗ true) (1st.fat→ᵣ true)
  inl* = inl

  fatcoh : (x : 2nd.fat) → fst is2 (2nd.fat→ₗ true x) ≡ 1st.fat→ₗ true (fst is1 x)
  fatcoh x = ΣPathP ((funExt (CasesBool true refl refl)) , refl)

  FF→ : Pushout (2nd.fat→ₗ true) (2nd.fat→ᵣ true)
      → Pushout (1st.fat→ₗ true) (1st.fat→ᵣ true)
  FF→ = elimPushout
          (λ x → inl (fst is2 x))
          (λ x → inr (fst is3 x))
          λ x → cong inl* (fatcoh x)
               ∙ push (fst is1 x)

  FF : Iso (Pushout (2nd.fat→ₗ true) (2nd.fat→ᵣ true))
           (Pushout (1st.fat→ₗ true) (1st.fat→ᵣ true))
  FF = pushoutIso _ _ _ _ is1 is2 is3 (funExt fatcoh) refl

  FFmain : (Pushout (2nd.fat→ₗ true) (2nd.fat→ᵣ true))
         ≃ (Pushout (1st.fat→ₗ true) (1st.fat→ᵣ true))
  FFmain =
    (FF→ , subst isEquiv (sym (funExt help))
      (isoToIsEquiv FF))
    where
    help : (x : _) → FF→ x ≡ Iso.fun FF x 
    help (inl x) = refl
    help (inr x) = refl
    help (push a i) j = compPath≡compPath' (cong inl* (fatcoh a)) (push (fst is1 a)) j i

  private
    F = fst FFmain

  MPP : (f : fst J ⊎ (fst (RP∞'· ℓ) ≃ fst J))
    (p : (i₁ : fst (RP∞'· ℓ)) (j₁ : fst J) → A i₁ j₁)
    → Square {A = TotΠ (λ i₁ → Σ-syntax (fst J) (A i₁))}
            (λ i x → evalG f x , 2nd.elimIηPushTop true f p i x)
            (cong fst (fatcoh (f , p)) )
            refl
            refl
  MPP f p = funTypeSq λ { false → λ _ _ → evalG f false , p false (evalG f false) ; true → λ _ _ → evalG f true , p true (evalG f true)}

  F1S : (y : _) → 2nd.PushTop→left-push (true , y) ≡ 1st.PushTop→left-push (true , F y)
  F1S = elimPushout (λ _ → refl) (λ _ → refl)
    λ a j i → 1st.PushTop→left-push (true
      , compPath-filler (cong inl* (fatcoh a)) (push (fst is1 a)) i j)

  F2S : (y : _) → Isor-alt (RP∞'· ℓ) J A (2nd.PushTop→ΠR-base (true , y))
               ≡ 1st.PushTop→ΠR-base (true , F y)
  F2S (inl x) = refl
  F2S (inr x) = refl
  F2S (push (f , p) i) j =
    hcomp (λ k → λ {(i = i0) → 1st.PushTop→ΠR-base (true , F (inl (2nd.fat→ₗ true (f , p))))
                   ; (i = i1) → push ((λ i → evalG f i , p i (evalG f i))
                                    , (p , λ _ → refl)) k
                   ; (j = i0) → Isor-alt (RP∞'· ℓ) J A
                                   (compPath-filler
                                     (λ j → inl (f , 2nd.elimIηPushTop true f p j))
                                     (push (f , p)) k i)
                   ; (j = i1) → 1st.PushTop→ΠR-base (true ,
                                  compPath-filler (cong inl* (fatcoh (f , p))) (push (fst is1 (f , p))) k i)})
          (inl (MPP f p j i))

PushTop≃Main : {ℓ : Level} (I : RP∞' ℓ) (a : fst I) (J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)→
    Σ[ F ∈ (Pushout (2-elter'.fat→ₗ I (fst J) A a) (2-elter'.fat→ᵣ I (fst J) A a)
    ≃ Pushout (2-elter.fat→ₗ I (fst J) A a) (2-elter.fat→ᵣ I (fst J) A a)) ]
      (((y : Pushout (2-elter'.fat→ₗ I (fst J) A a)
                    (2-elter'.fat→ᵣ I (fst J) A a))
      → ((2-elter'.PushTop→left-push I (fst J) A (a , y)
       ≡ 2-elter.PushTop→left-push I (fst J) A (a , fst F y)))
       × (Isor-alt I J A (2-elter'.PushTop→ΠR-base I (fst J) A (a , y))
       ≡ 2-elter.PushTop→ΠR-base I (fst J) A (a , fst F y))))
PushTop≃Main = JRP∞' λ J A → (FFmain J A)
  , λ y → F1S J A y
  , F2S J A y


module _ {ℓ : Level} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) where
  private
    module 1st = 2-elter I (fst J) A
    module 2nd = 2-elter' I (fst J) A

  PushTopIso : 2nd.PushTop ≃ 1st.PushTop
  PushTopIso = Σ-cong-equiv-snd λ i
    → PushTop≃Main I i J A .fst

  Π-extend→ : Iso (2nd.ΠR-extend) (1st.ΠR-extend)
  Π-extend→ = pushoutIso _ _ _ _
    PushTopIso
    (idEquiv _)
    (ΠR-base≃ I J A)
    (funExt (uncurry λ i y → PushTop≃Main I i J A .snd y .fst))
    (funExt (uncurry λ i y → PushTop≃Main I i J A .snd y .snd))
