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

module Cubical.Cohomology.EilenbergMacLane.October where
open import Cubical.HITs.Join
open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.FunExtEquiv

{-
ΠR-extend→Π-equiv : ∀ {ℓ} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
  → isEquiv (2-elter.ΠR-extend→Π I (fst J) A)
ΠR-extend→Π-equiv {ℓ} =
  RP∞'pt→Prop (λ _ → isPropΠ2 λ _ _ → isPropIsEquiv _) ΠR-extend→Π-equiv-base
-}

makeRP'≃ₗ : {ℓ : Level} (J : RP∞' ℓ) (j : fst J) → Bool ≃ (fst J)
makeRP'≃ₗ J j = isoToEquiv (iso F G GFG FGF)
  where
  R = J .snd .fst .snd .snd (λ _ → Lift Bool)
  G' : fst J → Lift Bool
  G' = R .fst j (lift true) (lift false)

  G : fst J → Bool
  G = lower ∘ G'

  F : Bool → fst J
  F = CasesBool true j (J .snd .fst .fst j)

  FGF : (x : Bool) → G (F x) ≡ x
  FGF false = cong lower (R .snd j (lift true) (lift false) .snd)
  FGF true = cong lower (R .snd j (lift true) (lift false) .fst)

  GFG : (x : _) → F (G x) ≡ x
  GFG x = lower (J .snd .fst .snd .snd (λ x → Lift (F (G x) ≡ x)) .fst
                j
                (lift (cong F (cong lower (R .snd j (lift true) (lift false) .fst))))
                (lift (cong F (cong lower (R .snd j (lift true) (lift false) .snd)))) x)

module _  {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ) where

  private
    module JLem = 2-elter' J Bool (λ x y → A y x)
    GOAL = joinR-gen (fst J) λ j → joinR-gen Bool λ i → A i j

    inl-inlₗ : (j : fst J) → A true j → A false j → GOAL
    inl-inlₗ j x y = inlR (j , inrR (CasesBool true x y))

    inl-inlᵣ-pre : (j : fst J) → A true j → A false (JLem.notI j)
      → (j' : fst J) → Σ[ k ∈ Bool ] A k j'
    inl-inlᵣ-pre j x y = JLem.elimI j (true , x) (false , y)

    inl-inlᵣ : (j : fst J) → A true j → A false (JLem.notI j) → GOAL
    inl-inlᵣ j x y = inrR (λ j' → inlR (inl-inlᵣ-pre j x y j'))

    inl-inl : (j j1 : fst J) (a : A true j) (b : A false j1) → GOAL
    inl-inl j = JLem.elimI j (inl-inlₗ j) (inl-inlᵣ j)

    inl-inl-β : (j : fst J) (a : A true j)
      → ((b : A false j) → inl-inl j j a b ≡ inl-inlₗ j a b)
       × ((b : A false (JLem.notI j)) → inl-inl j (JLem.notI j) a b ≡ inl-inlᵣ j a b)
    inl-inl-β j a = (λ b i → T .fst i a b) , (λ b i → T .snd i a b)
      where
      T = JLem.elimIβ {B = λ j1 → (a : A true j) (b : A false j1) → GOAL}
           j (inl-inlₗ j) (inl-inlᵣ j)

    inl-pushₗ : (j : fst J) (a : A true j) (b : A false j) (f : TotΠ (A false))
      → f j ≡ b
      → inl-inl j j a b
       ≡ inlR (j , inrR (CasesBool true a (f j)))
    inl-pushₗ j a b f p =
        inl-inl-β j a .fst b
      ∙ λ i → inlR (j , inrR (CasesBool true a (p (~ i))))

    inl-pushᵣ : (j : fst J) (a : A true j) (b : A false (JLem.notI j)) (f : TotΠ (A false))
      → f (JLem.notI j) ≡ b
      → inl-inl j (JLem.notI j) a b
       ≡ inlR (j , inrR (CasesBool true a (f j)))
    inl-pushᵣ j a b f p =
        inl-inl-β j a .snd b
      ∙ sym (push* (j , inlR (true , a))
                   (λ j' → inlR (inl-inlᵣ-pre j a b j'))
                   (cong inlR (JLem.elimIβ j (true , a) (false , b) .fst)))
      ∙ λ i → inlR (j , push* (true , a) (CasesBool true a (f j)) refl i)

    inl-push : (j j' : fst J) (a : A true j) (b : A false j') (f : TotΠ (A false))
      → f j' ≡ b
      → inl-inl j j' a b
       ≡ inlR (j , inrR (CasesBool true a (f j)))
    inl-push j = JLem.elimI j (inl-pushₗ j) (inl-pushᵣ j)

    push-inlₗ : (j : fst J) (a : A true j) (b : A false j) (f : TotΠ (A true))
      → f j ≡ a
      → inl-inl j j a b ≡ inlR (j , inrR (CasesBool true (f j) b))
    push-inlₗ j a b f p =
        inl-inl-β j a .fst b
      ∙ λ i → inlR (j , inrR (CasesBool true (p (~ i)) b))

    push-inlᵣ : (j : fst J) (a : A true j)
      (b : A false (fst (snd J .fst) j))
      (f : (x : fst J) → A true x) (p : f j ≡ a)
      → inl-inl j (JLem.notI j) a b
       ≡ inlR (JLem.notI j , inrR (CasesBool true (f (JLem.notI j)) b))
    push-inlᵣ j a b f p =
        inl-inl-β j a .snd b
      ∙ {!!}
      ∙ {!!}

    push-inl : (j j' : fst J) (a : A true j) (b : A false j') (f : TotΠ (A true))
      → f j ≡ a
      → inl-inl j j' a b
       ≡ inlR (j' , inrR (CasesBool true (f j') b))
    push-inl j = JLem.elimI j (push-inlₗ j) (push-inlᵣ j)

  Join→Goalₗ : joinR-gen (fst J) (A true)
    → joinR-gen (fst J) λ j → joinR-gen Bool λ i → A i j
  Join→Goalₗ (inlR (j , a)) = inlR (j , inlR (true , a))
  Join→Goalₗ (inrR x) = inrR λ j → inlR (true , x j)
  Join→Goalₗ (push* (j , a) b x i) =
    push* (j , inlR (true , a)) (λ j → inlR (true , b j)) (λ i → inlR (true , x i)) i

  Join→Goal : joinR-gen (fst J) (A true) × joinR-gen (fst J) (A false)
    → joinR-gen (fst J) λ j → joinR-gen Bool λ i → A i j
  Join→Goal (inlR (j , a) , inlR (j1 , b)) = inl-inl j j1 a b
  Join→Goal (inlR (j , a) , inrR f) = inlR (j , inrR (CasesBool true a (f j)))
  Join→Goal (inlR (j , a) , push* (j' , b) f p i) = inl-push j j' a b f p i
  Join→Goal (inrR f , inlR (j , x)) = inlR (j , inrR (CasesBool true (f j) x))
  Join→Goal (inrR f , inrR g) = inrR λ j → inrR (CasesBool true (f j) (g j))
  Join→Goal (inrR f , push* (j , a) g p i) =
    push* (j , inrR (CasesBool true (f j) a))
          (λ t → inrR (CasesBool true (f t) (g t)))
          (λ i → inrR (CasesBool true (f j) (p i))) i
  Join→Goal (push* (j , a) f p i , inlR (j' , b)) =
    push-inl j j' a b f p i
  Join→Goal (push* (j , a) f p i , inrR g) =
    push* (j , inrR (CasesBool true a (g j)))
          (λ i → inrR (CasesBool true (f i) (g i)))
          (λ k → inrR (CasesBool true (p k) (g j))) i
  Join→Goal (push* (j , a) f p i , push* (j' , a') g q i') =
    push-push j j' a a' f g p q i' i
    where
    push-push-typ : (j : fst J) (j' : fst J) → Type _
    push-push-typ j j' =
      (a : A true j) (a' : A false j')
      (f : TotΠ (A true)) (g : TotΠ (A false))
      (p : f j ≡ a)
      (q : g j' ≡ a')
      → Square (push-inl j j' a a' f p)
                (push* (j , inrR (CasesBool true a (g j)))
                       (λ j → inrR (CasesBool true (f j) (g j)))
                       λ i → inrR (CasesBool true (p i) (g j)))
                (inl-push j j' a a' g q)
                (push* (j' , inrR (CasesBool true (f j') a'))
                       (λ t → inrR (CasesBool true (f t) (g t)))
                       λ i → inrR (CasesBool true (f j') (q i)))

    push-pushₗ : (j : fst J) → push-push-typ j j
    push-pushₗ j a a' f g p q i k =
      hcomp (λ r → λ {(i = i0) → {!!}
                   ; (i = i1) → {!!}
                   ; (k = i0) → {!!}
                   ; (k = i1) → {!!}})
          {!!}

    push-push : (j : fst J) (j' : fst J) → push-push-typ j j'
    push-push j = JLem.elimI j {!!} {!!}
  {-
    hcomp (λ k → λ {(i = i0) → {!!}
                   ; (i = i1) → {!!}
                   ; (i' = i0) → {!!}
                   ; (i' = i1) → {!!}})
          {!!}
          -}
{-
Goal: joinR-gen (fst J) (λ j₁ → joinR-gen Bool (λ i₁ → A i₁ j₁))
———— Boundary (wanted) —————————————————————————————————————
i' = i0 ⊢ push-inl j j' a a' f p i
i' = i1 ⊢ push* (j , inrR (λ y → CasesBool-true y a (g j)))
          (λ i₁ → inrR (λ y → CasesBool-true y (f i₁) (g i₁)))
          (λ k → inrR (λ y → CasesBool-true y (p k) (g j))) i
i = i0 ⊢ inl-push j j' a a' g q i'
i = i1 ⊢ push* (j' , inrR (λ y → CasesBool-true y (f j') a'))
         (λ t → inrR (λ y → CasesBool-true y (f t) (g t)))
         (λ i₁ → inrR (λ y → CasesBool-true y (f j') (q i₁))) i'
-}

  Join→Goal-vanish : (x : (joinR-gen (fst J) (A true) × joinR-gen (fst J) (A false)))
    → Join→Goal x ≡ Join→Goalₗ (fst x)
  Join→Goal-vanish (inlR s , inlR f) = {!!}
  Join→Goal-vanish (inlR x , inrR f) k =
    inlR (fst x , push* (true , snd x) (CasesBool true (snd x) (f (fst x))) refl (~ k))
  Join→Goal-vanish (inlR x , push* a b x₁ i) = {!!}
  Join→Goal-vanish (inrR f , inlR (j , a)) = {!f!}
  Join→Goal-vanish (inrR x , inrR f) k =
    inrR (λ j → push* (true , x j) (CasesBool true (x j) (f j)) refl (~ k))
  Join→Goal-vanish (inrR x , push* a b x₁ i) = {!!}
  Join→Goal-vanish (push* a b₁ x i , b) = {!!}


module _  {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ) where

  module JLem = 2-elter' J Bool (λ x y → A y x)

  Lift↓ : Lift {j = ℓ} (fst J ⊎ (Bool ≃ fst J)) → fst J ⊎ (Bool ≃ fst J)
  Lift↓  (lift x) = x

  →⊎ : fst J → fst J → fst J ⊎ (Bool ≃ fst J)
  →⊎ x = Lift↓ ∘ JLem.elimI x (lift (inl x)) (lift (inr (makeRP'≃ₗ J x)))

  inl-inl : (A : Bool → fst J → Type ℓ) (j1 j2 : fst J) → A true j1 → A false j2
    → Σ[ e ∈ (fst J ⊎ (Bool ≃ fst J)) ]
          ((i : Bool) → A i (2-elter'.eval (RP∞'· ℓ) (fst J) A e i))
  inl-inl A j1 =
    JLem.elimI {B = λ j2 → A true j1 → A false j2
                         → Σ[ e ∈ (fst J ⊎ (Bool ≃ fst J)) ]
                               ((i : Bool) → A i (2-elter'.eval (RP∞'· ℓ) (fst J) A e i))}
      j1 (λ a b → (inl j1) , CasesBool true a b)
          λ a b → inr (makeRP'≃ₗ J j1) , CasesBool true a b

  inl-inlₗ : (A : Bool → fst J → Type ℓ) (j1 : fst J) (x : A true j1)
    → ((y : A false j1)
      → inl-inl A j1 j1 x y ≡ ((inl j1) , CasesBool true x y))
     × ((y : A false (JLem.notI j1))
       → inl-inl A j1 (JLem.notI j1) x y ≡ (inr (makeRP'≃ₗ J j1) , CasesBool true x y))
  inl-inlₗ A j1 x = (λ y i → T .fst i x y) , λ y i → T .snd i x y
    where
    T = JLem.elimIβ {B = λ j2 → A true j1 → A false j2
                         → Σ[ e ∈ (fst J ⊎ (Bool ≃ fst J)) ]
                               ((i : Bool) → A i (2-elter'.eval (RP∞'· ℓ) (fst J) A e i))}
      j1 (λ a b → (inl j1) , CasesBool true a b)
          λ a b → inr (makeRP'≃ₗ J j1) , CasesBool true a b

  inl-pushₗ : (A : Bool → fst J → Type ℓ)
    (j1 : fst J) (x : A true j1) (y : A false j1)
    → (f : TotΠ (A false)) (p : f j1 ≡ y)
    → Path (2-elter'.ΠR-extend (RP∞'· ℓ) (fst J) A)
            (inr (inl (inl-inl A j1 j1 x y)))
            (inr (inl (inl j1 , CasesBool true x (f j1))))
  inl-pushₗ A j1 x y f p i = inr (inl ((inl-inlₗ A j1 x .fst y ∙ λ i → (inl j1 , (CasesBool true x (p (~ i))))) i))

  inl-pushᵣ : (A : Bool → fst J → Type ℓ)
    (j1 : fst J) (x : A true j1) (y : A false (JLem.notI j1))
    → (f : TotΠ (A false)) (p : f (JLem.notI j1) ≡ y)
    → Path (2-elter'.ΠR-extend (RP∞'· ℓ) (fst J) A)
            (inr (inl (inl-inl A j1 (JLem.notI j1) x y)))
            (inr (inl (inl j1 , CasesBool true x (f j1))))
  inl-pushᵣ A j1 x y f p i =
     ((λ i → inr (inl (inl-inlₗ A j1 x .snd y i)))
    ∙ (λ i → inr (inl (inr (makeRP'≃ₗ J j1) , (CasesBool true x (p (~ i))))))
    ∙ sym (push (true , (inl ((inr (makeRP'≃ₗ J j1)) , x , f))))
    ∙ p1) i
    where
    p1 : Path (2-elter'.ΠR-extend (RP∞'· ℓ) (fst J) A)
           (inl (true , (j1 , x) , f))
           (inr (inl (inl j1 , CasesBool true x (f j1))))
    p1 = push (true , (inl (inl j1 , x , f)))

  inl-push : (A : Bool → fst J → Type ℓ)
    (j1 j2 : fst J) (x : A true j1) (y : A false j2)
    → (f : TotΠ (A false)) (p : f j2 ≡ y)
    → Path (2-elter'.ΠR-extend (RP∞'· ℓ) (fst J) A)
            (inr (inl (inl-inl A j1 j2 x y)))
            (inr (inl (inl j1 , CasesBool true x (f j1))))
  inl-push A j1 = JLem.elimI j1 (inl-pushₗ A j1) (inl-pushᵣ A j1)


  ×→ΠR-extend* : joinR-gen (fst J) (A true) × joinR-gen (fst J) (A false)
    → 2-elter'.ΠR-extend (RP∞'· ℓ) (fst J) A
  ×→ΠR-extend* (inlR (j1 , x) , inlR (j2 , y)) = inr (inl (inl-inl A j1 j2 x y))
  ×→ΠR-extend* (inlR x , inrR f) =
    inr (inl ((inl (fst x)) , (CasesBool true (snd x) (f (fst x)))))
  ×→ΠR-extend* (inlR (j1 , x) , push* (j2 , y) f p i) = inl-push A j1 j2 x y f p i
  ×→ΠR-extend* (inrR f , inlR x) =
    inr (inl ((inl (fst x)) , (CasesBool true (f (fst x)) (snd x))))
  ×→ΠR-extend* (inrR x , inrR x₁) = inr (inr (CasesBool true x x₁))
  ×→ΠR-extend* (inrR x , push* (j , a) b x₁ i) =
    inr (((λ k → inl (inl j , p k)) ∙ push ((inl j) , CasesBool true x b)) i)
    where
    p : Path ((i₁ : Bool) → A i₁ j)
             (CasesBool true (x j) a)
             (λ i → CasesBool {A = λ i → (j : fst J) → A i j} true x b i j)
    p = funExt (CasesBool true refl (sym x₁))
  ×→ΠR-extend* (push* (j , a) f p i , inlR (j' , b)) =
    {!inl-push (λ x j → A (not x) j) j' j b a f p i!} -- inr (inl {!!})
  ×→ΠR-extend* (push* (j , a) f p i , inrR g) =
    inr (((λ i → inl (inl j , p' i))
        ∙ push (inl j , CasesBool true f g)) i)
    where
    p' : Path ((i₂ : Bool) → A i₂ j)
              (CasesBool true a (g j))
              (λ i → CasesBool {A = λ i → (j : fst J) → A i j} true f g i j)
    p' = funExt (CasesBool true (sym p) refl)
  ×→ΠR-extend* (push* (j , a) f p i , push* (j' , a') g q k) =
    {!Goal: 2-elter'.ΠR-base (RP∞'· ℓ) (fst J) A
———— Boundary (wanted) —————————————————————————————————————
i = i0 ⊢ (inl (inl j , (λ y → CasesBool-true y a (g j))))
i = i1 ⊢ (inr (λ y → CasesBool-true y f g))!}

{-
×→ΠR-extend* : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
  → joinR-gen (fst J) (A true) × joinR-gen (fst J) (A false)
  → 2-elter'.ΠR-extend (RP∞'· ℓ) (fst J) A
×→ΠR-extend* J A (inlR x , inlR x₁) = inr (inl (CasesBool true x x₁))
×→ΠR-extend* J A (inlR (x , b) , inrR x₁) = inl (true , ((_ , b) , x₁))
×→ΠR-extend* J A (inlR (a , b) , push* (a' , d) c x₁ i) =
  push (true , inl ((CasesBool true (a , b) (a' , d)) , c , x₁)) (~ i)
×→ΠR-extend* J A (inrR x , inlR x₁) = inl (false , (x₁ , x))
×→ΠR-extend* J A (inrR x , inrR x₁) = inr (inr (CasesBool true x x₁))
×→ΠR-extend* J A (inrR x , push* (a , b) c x₁ i) =
  push (false , (inr ((a , b) , ((CasesBool true x c) , x₁)))) i
×→ΠR-extend* J A (push* (a , b) c x i , inlR (a' , b')) =
  push (false , inl ((CasesBool true (a , b) (a' , b')) , (c , x))) (~ i)
×→ΠR-extend* J A (push* (a' , b) c x i , inrR x₁) =
  push (true , inr ((_ , b) , (CasesBool true c x₁ , x))) i
×→ΠR-extend* J A (push* (a , b) c x i , push* (a' , b₁) c₁ d i₁) =
  ?
-}
-- module _ {ℓ : Level} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) where
--   private
--     module 1st = 2-elter I (fst J) A
--     module 2nd = 2-elter' I (fst J) A

--   ΠR-extend→M : 2nd.ΠR-extend → joinR-gen (fst J) λ j → joinR-gen (fst I) (λ i → A i j)
--   ΠR-extend→M (inl x) = {!!}
--   ΠR-extend→M (inr x) = {!!}
--   ΠR-extend→M (push a i) = {!!}


-- eval⁻ : ∀ {ℓ} (I J : RP∞' ℓ) → fst J ⊎ (fst I ≃ fst J) → fst I → fst J
-- eval⁻ I J (inl j) _ = j
-- eval⁻ I J (inr f) = fst f

-- isEqEval : ∀ {ℓ} (I J : RP∞' ℓ) → isEquiv (eval⁻ I J)
-- isEqEval = RP∞'pt→Prop (λ _ → isPropΠ λ _ → isPropIsEquiv _)
--   {!λ !}
--   where
--   main : ∀ {ℓ} (J : RP∞' ℓ) → (Bool → fst J) → fst J ⊎ (Bool ≃ fst J)
--   main J f = {!!}

-- eval' : ∀ {ℓ} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
--   → Iso ((i : fst I) → Σ (fst J) (A i))
--          ((Σ[ j ∈ fst J ] ((i : fst I) → A i j))
--        ⊎ (Σ[ t ∈ (fst I ≃ fst J) ] ((i : fst I) → A i (fst t i))))
-- Iso.fun (eval' I J A) f =
--   ⊎.rec (λ j → inl (j , λ i → {!f i .snd!})) {!!} (invEq (_ , isEqEval I J) (fst ∘ f))
-- Iso.inv (eval' I J A) = {!!}
-- Iso.rightInv (eval' I J A) = {!!}
-- Iso.leftInv (eval' I J A) = {!!}

-- module _ {ℓ} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) where
--   module IM = 2-elter I (fst J) A
--   open IM
--   module JM = 2-elter J

--   TYP = 2-elter.ΠR-extend I (fst J) A
--   GOAL = joinR-gen (fst J) λ j → joinR-gen (fst I) λ i → A i j

--   sₗ : left-push → GOAL
--   sₗ (i , (j , a) , f) = inlR (j , inrR (elimI i a (f j)))

--   sᵣ : ΠR-base → GOAL
--   sᵣ (inl f) = inrR λ j → inrR λ i → JM.elimI (fst I) (λ x y → A y x) {B = λ j → A i j} (fst (f i)) (f i .snd) {!f i .snd!} j
--   sᵣ (inr x) = inrR λ j → inrR λ i → x i j
--   sᵣ (push a i) = {!a!}

--   s : TYP → joinR-gen (fst J) λ j → joinR-gen (fst I) λ i → A i j
--   s (inl x) = sₗ x
--   s (inr x) = sᵣ x
--   s (push (i , inl x) k) = {!!}
--   s (push (i , inr x) k) = {!!}
--   s (push (i , push a i₁) k) = {!!}
  

