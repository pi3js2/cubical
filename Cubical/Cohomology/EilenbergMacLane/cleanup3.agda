{-# OPTIONS --safe --lossy-unification #-}

{-
This file contains the construction of a fubini like map
flipping unordered joins:
∗ᵢ∗ⱼ Aᵢⱼ → ∗ⱼ ∗ᵢ Aⱼᵢ
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

module Cubical.Cohomology.EilenbergMacLane.cleanup3 where
open import Cubical.HITs.Join
open import Cubical.Functions.FunExtEquiv

private
  variable
    ℓ : Level


-- The following technical elimination principle will be used later
module _ (A : (e : Bool ≃ Bool) (p : fst e true ≡ true) → Type ℓ)
  (a : A (idEquiv _) refl) where
  private
    l = Bool≃Bool-elim (λ e → (p : fst e true ≡ true) → A e p)
                       (λ p → subst (A (idEquiv Bool)) (isSetBool _ _ refl p) a)
                       λ p → ⊥.rec (false≢true p)

  Bool≃Bool-elim-id : (e : Bool ≃ Bool) (p : fst e true ≡ true) → A e p
  Bool≃Bool-elim-id = l .fst

  Bool≃Bool-elim-idβ : Bool≃Bool-elim-id (idEquiv _) refl ≡ a
  Bool≃Bool-elim-idβ = funExt⁻ (l .snd .fst) refl
                     ∙ cong (λ x → subst (A (idEquiv Bool)) x a)
                         (isSet→isGroupoid isSetBool true true refl refl
                           (isSetBool true true refl refl) refl)
                     ∙ transportRefl a

-- It is shown in RP.Unordered that a nestled join can be written as a
-- pushout UnordJoin²₂ involving ΠJoinR₂.ΠR-extend, the latter alowing
-- for pattern patching on Π-typepes over underodered joins. We begin by
-- giving yet another description of these Π-typepes and hence yet
-- another description of nestled unordered joins.
module ΠJoinR₃ (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) where
  open ΠJoinR-gen I (fst J) A
         (Σ[ x ∈ fst J ⊎ (fst I ≃ fst J) ]
           ((i : fst I) → A i (eval⊎≃ x i)))
         (λ i p → Iso.inv (UnordΠUnordΣ-charac I J {A}) p i .fst)
         (λ i x → Iso.inv (UnordΠUnordΣ-charac I J {A}) x i .snd)
       public

  open RP∞'-fields I
  module _ (i : fst I) (j : fst J) where

    ΠJoinRBackₘ : Type ℓ
    ΠJoinRBackₘ = ((i : fst I) (j : fst J) → A i j)
        ⊎ (Σ[ e ∈ fst I ≃ fst J ]
          ((fst e i ≡ j) × ((i : fst I) (j : fst J) → A i j)))

    ΠJoinRBackₗ-left : Type ℓ
    ΠJoinRBackₗ-left = Σ[ f ∈ ((i : fst I) → A i j) ]
                (Σ[ g ∈ ((j : fst J) → A (notRP∞' i) j) ]
                  g j ≡ f (notRP∞' i))

    ΠJoinRBackₗ-right : Type ℓ
    ΠJoinRBackₗ-right = Σ[ e ∈ fst I ≃ fst J ]
                   ((fst e i ≡ j)
             × (Σ[ f ∈ ((i : fst I) → A i (fst e i)) ]
                 (Σ[ g ∈ ((j : fst J) → A (notRP∞' i) j) ]
                   g (fst e (notRP∞' i)) ≡ f (notRP∞' i))))

    ΠJoinRBackₗ : Type ℓ
    ΠJoinRBackₗ = ΠJoinRBackₗ-left ⊎ ΠJoinRBackₗ-right

    ΠJoinRBackₘ→ₗ : ΠJoinRBackₘ → ΠJoinRBackₗ
    ΠJoinRBackₘ→ₗ (inl g) =
      inl ((λ i → g i j) , ((g (notRP∞' i)) , refl))
    ΠJoinRBackₘ→ₗ (inr (e , p , g)) =
      inr (e , (p , (λ i → g i (fst e i)) , ((g (notRP∞' i)) , refl)))

    ΠJoinRBackₘ→ᵣ : ΠJoinRBackₘ → ((i : fst I) (j : fst J) → A i j)
    ΠJoinRBackₘ→ᵣ (inl x) = x
    ΠJoinRBackₘ→ᵣ (inr x) = snd (snd x)

    ΠJoinRBack = Pushout ΠJoinRBackₘ→ₗ ΠJoinRBackₘ→ᵣ

    ΠJoinRBack→ΠR-base : ΠJoinRBack → ΠR-base
    ΠJoinRBack→ΠR-base (inl (inl (a , g , p))) = inl ((inl j) , a)
    ΠJoinRBack→ΠR-base (inl (inr (e , p , a , g))) = inl ((inr e) , a)
    ΠJoinRBack→ΠR-base (inr x) = inr x
    ΠJoinRBack→ΠR-base (push (inl x) i) =
      push (((inl j) , (λ i → x i j)) , x , λ _ → refl) i
    ΠJoinRBack→ΠR-base (push (inr (x , (p , g))) i) =
      push ((inr x , λ i → g i (fst x i)) , g , λ _ → refl) i

    ΠJoinRBack→leftPush : (x : ΠJoinRBack)
      → Σ (fst J) (A i) × ((j : fst J) → A (notRP∞' i) j)
    ΠJoinRBack→leftPush (inl (inl (f , p , q))) = (j , f i) , p
    ΠJoinRBack→leftPush (inl (inr (e , p , f , q , r))) = (fst e i , f i) , q
    ΠJoinRBack→leftPush (inr x) = (j , x i j) , (x (notRP∞' i))
    ΠJoinRBack→leftPush (push (inl x) _) = (j , x i j) , x (notRP∞' i)
    ΠJoinRBack→leftPush (push (inr (e , p , f)) k) = (p k , f i (p k)) , f (notRP∞' i)

    ΠJoinRBack→L : ΠJoinRBack → ΠR-left
    ΠJoinRBack→L x = i , ΠJoinRBack→leftPush x

  ΣΠJoinRBack : Type ℓ
  ΣΠJoinRBack = Σ[ i ∈ fst I ] Σ[ j ∈ fst J ] (ΠJoinRBack i j)

  ΣΠJoinRBack→ₗ : ΣΠJoinRBack → ΠR-left
  ΣΠJoinRBack→ₗ (i , j , x) = ΠJoinRBack→L i j x

  ΣΠJoinRBack→ᵣ : ΣΠJoinRBack → ΠR-base
  ΣΠJoinRBack→ᵣ (i , j , x) = ΠJoinRBack→ΠR-base i j x

  ΠR-extend₃ : Type ℓ
  ΠR-extend₃ = Pushout {A = ΣΠJoinRBack} {B = ΠR-left} {C = ΠR-base}
                        ΣΠJoinRBack→ₗ
                        ΣΠJoinRBack→ᵣ

  -- We will see that there is map Π-extend₂ → Π-extend₃ (in fact, it
  -- should be an equivalence, but we will not need this here)
  ΠR-extend₂→ΠR-extend₃-push-fillerₗ :
    (i : fst I) (x : fst J) (f : (i : fst I) → A i x)
    (p : (i : fst I) (j : fst J) → A i j) (q : (i : fst I) → p i x ≡ f i)
    (i' j' k' : _) → ΠR-extend₃
  ΠR-extend₂→ΠR-extend₃-push-fillerₗ i x f p q i' j' k' =
    hfill (λ k →
    λ {(i' = i0) → push (i , x , (inl (inl ((λ i → q i k)
                        , p (notRP∞' i) , (λ j → q (notRP∞' i) (k ∧ j)))))) j'
     ; (i' = i1) → compPath-filler'
                     (λ j → (inl (i , (x , q i (~ j)) , p (notRP∞' i))))
                     (push (i , x , inr p)) k j'
     ; (j' = i0) → inl (i , (x , q i k) , p (notRP∞' i))
     ; (j' = i1) → inr (push (((inl x) , (λ i → q i k))
                             , (p , (λ i j → q i (k ∧ j)))) i')})
     (inS (push (i , x , push (inl p) i') j'))
     k'

  ΠR-extend₂→ΠR-extend₃-push-fillerᵣ :
   (i : fst I) (x : fst I ≃ fst J) (f : (i : fst I) → A i (fst x i))
   (p : (i : fst I) (j : fst J) → A i j) (q : (i : fst I) → p i (fst x i) ≡ f i)
   (i' j' k' : _) → ΠR-extend₃
  ΠR-extend₂→ΠR-extend₃-push-fillerᵣ i x f p q i' j' k' =
    hfill (λ k →
    λ {(i' = i0) → push (i , ((fst x i) , (inl (inr (x , (refl , (λ i → q i k)
                      , (p (notRP∞' i) , (λ j → q (notRP∞' i) (k ∧ j))))))))) j'
     ; (i' = i1) → compPath-filler'
                     (λ j → (inl (i , (fst x i , q i (~ j)) , p (notRP∞' i))))
                     (push (i , fst x i , inr p)) k j'
     ; (j' = i0) → inl (i , (fst x i , q i k) , p (notRP∞' i))
     ; (j' = i1) → inr (push (((inr x) , (λ i → q i k))
                             , (p , (λ i j → q i (k ∧ j)))) i')})
     (inS (push (i , fst x i , push (inr (x , (refl , p))) i') j'))
     k'

  ΠR-extend₂→ΠR-extend₃-push : (i : fst I) (x : _)
    → Path ΠR-extend₃ (inl (i , Pushtop→ΠR-left' i x))
                       (inr (ΣPushtop→ΠR-base (i , x)))
  ΠR-extend₂→ΠR-extend₃-push i (inl ((inl x , f) , p , q)) =
    push (i , x , inl (inl (f , (p , q))))
  ΠR-extend₂→ΠR-extend₃-push i (inl ((inr x , f) , p , q)) =
    push (i , fst x i , inl (inr (x , refl , f , p , q)))
  ΠR-extend₂→ΠR-extend₃-push i (inr ((j , a) , g , p))  =
    ((λ t → inl (i , (j , p (~ t)) , g (notRP∞' i)) ) ∙ push (i , j , inr g))
  ΠR-extend₂→ΠR-extend₃-push i (push ((inl x , f) , p , q) i') j' =
    ΠR-extend₂→ΠR-extend₃-push-fillerₗ i x f p q i' j' i1
  ΠR-extend₂→ΠR-extend₃-push i (push ((inr x , f) , p , q) i') j' =
    ΠR-extend₂→ΠR-extend₃-push-fillerᵣ i x f p q i' j' i1

  ΠR-extend₂→ΠR-extend₃ : ΠR-extend → ΠR-extend₃
  ΠR-extend₂→ΠR-extend₃ (inl x) = inl x
  ΠR-extend₂→ΠR-extend₃ (inr x) = inr x
  ΠR-extend₂→ΠR-extend₃ (push (i , x) k) = ΠR-extend₂→ΠR-extend₃-push i x k

module _ (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) where
  open ΠJoinR₃ I J A
  open RP∞'-fields I
  ΠR-extend₃→JoinR-pushₗ-fill :
    (i' : fst I) (j : fst J) (e : fst I ≃ fst J)
    (p : fst e i' ≡ j) (f : (i₁ : fst I) (j₁ : fst J) → A i₁ j₁)
    → (i k r : _) → UnordJoinR-gen (fst J) (A i')
  ΠR-extend₃→JoinR-pushₗ-fill i' j e p f i k r =
    hfill (λ r →
    λ {(i = i0) → inlR (p (~ r) , f i' (p (~ r)))
     ; (i = i1) → pushR (j , f i' j) (f i') (λ _ → f i' j) k
     ; (k = i0) → inlR ((p (i ∨ ~ r)) , (f i' (p (i ∨ ~ r))))
     ; (k = i1) → pushR (p (~ r) , f i' (p (~ r))) (f i')
                         (λ i → f i' (p (~ r))) i})
     (inS (pushR (j , f i' j) (f i') (λ _ → f i' j) (i ∧ k)))
     r

  ΠR-extend₃→JoinR-pushₗ :
    (i' : fst I) (j : fst J) (a : ΠJoinRBack i' j)
    → inlR (ΠJoinRBack→L i' j a .snd .fst)
     ≡ ΠR-base₂→JoinR I J A i' (ΠJoinRBack→ΠR-base i' j a)
  ΠR-extend₃→JoinR-pushₗ i' j (inl (inl x)) = refl
  ΠR-extend₃→JoinR-pushₗ i' j (inl (inr x)) = refl
  ΠR-extend₃→JoinR-pushₗ i' j (inr x) = pushR (j , (x i' j)) (x i') refl
  ΠR-extend₃→JoinR-pushₗ i' j (push (inl x) i) k =
    pushR (j , x i' j) (x i') (λ _ → x i' j) (i ∧ k)
  ΠR-extend₃→JoinR-pushₗ i' j (push (inr (e , p , f)) i) k =
    ΠR-extend₃→JoinR-pushₗ-fill i' j e p f i k i1

  ΠR-extend₃→JoinR-pushᵣ : (i' : fst I) (j : fst J) (a : ΠJoinRBack i' j)
    → inrR (ΠJoinRBack→L i' j a .snd .snd)
     ≡ ΠR-base₂→JoinR I J A (notRP∞' i') (ΠJoinRBack→ΠR-base i' j a)
  ΠR-extend₃→JoinR-pushᵣ i' j (inl (inl (f , p , q))) =
    sym (pushR (j , f (notRP∞' i')) p q)
  ΠR-extend₃→JoinR-pushᵣ i' j (inl (inr (e , p , f , q , r))) =
    sym (pushR (fst e (notRP∞' i') , f (notRP∞' i')) q r)
  ΠR-extend₃→JoinR-pushᵣ i' j (inr x) = refl
  ΠR-extend₃→JoinR-pushᵣ i' j (push (inl x) i) k =
    pushR (j , x (notRP∞' i') j) (x (notRP∞' i')) refl (i ∨ ~ k)
  ΠR-extend₃→JoinR-pushᵣ i' j (push (inr (e , p , f)) i) k =
    pushR (fst e (notRP∞' i') , f (notRP∞' i') (fst e (notRP∞' i')))
         (f (notRP∞' i')) refl (i ∨ ~ k)

  ΠR-extend₃→JoinR-push : (i' : fst I) (j : fst J) (a : ΠJoinRBack i' j)
    (i : fst I)
    → ΠΣ→ΠJoinR I J A i'
         (ΠJoinRBack→L i' j a .snd .fst)
         (ΠJoinRBack→L i' j a .snd .snd) i
     ≡ ΠR-base₂→JoinR I J A i (ΠJoinRBack→ΠR-base i' j a)
  ΠR-extend₃→JoinR-push i' j a =
    elimRP∞' i'
      (ΠΣ→ΠJoinRβ I J A i' _ _ .fst
      ∙ ΠR-extend₃→JoinR-pushₗ i' j a)
      (ΠΣ→ΠJoinRβ I J A i' _ _ .snd
      ∙ ΠR-extend₃→JoinR-pushᵣ i' j a)

  ΠR-extend₃→JoinR : (i : fst I)
    → ΠR-extend₃ → UnordJoinR-gen (fst J) (A i)
  ΠR-extend₃→JoinR i (inl (i' , a , b)) = ΠΣ→ΠJoinR I J A i' a b i
  ΠR-extend₃→JoinR i (inr x) = ΠR-base₂→JoinR I J A i x
  ΠR-extend₃→JoinR i (push (i' , j , a) k) = ΠR-extend₃→JoinR-push i' j a i k

  -- alternative description of nestled unordered join.
  UnordJoin²-alt : Type ℓ
  UnordJoin²-alt =
    Pushout {A = fst I × ΠR-extend₃}
            {B = Σ[ i ∈ fst I ] UnordJoinR-gen (fst J) (A i)}
            {C = ΠR-extend₃}
            (λ x → fst x , ΠR-extend₃→JoinR (fst x) (snd x))
            snd

-- goal: define a map from ΠR-extend₂ → ΠR-extend₃ To make things
-- easier, let us give an explicit definition of ΠR-extend₃→JoinR in
-- the case when I is Bool.
module _ (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ) where
  ΠR-extend₃→JoinR-Bool : (i : Bool)
    → ΠJoinR₃.ΠR-extend₃ (RP∞'∙ ℓ) J A → UnordJoinR-gen (fst J) (A i)
  ΠR-extend₃→JoinR-Bool i (inl (i' , a , b)) = ΠΣ→ΠJoinR (RP∞'∙ _) J A i' a b i
  ΠR-extend₃→JoinR-Bool i (inr x) = ΠR-base₂→JoinR (RP∞'∙ _) J A i x
  ΠR-extend₃→JoinR-Bool false (push (false , j , a) k) =
    ΠR-extend₃→JoinR-pushₗ (RP∞'∙ _) J A false j a k
  ΠR-extend₃→JoinR-Bool false (push (true , j , a) k) =
    ΠR-extend₃→JoinR-pushᵣ (RP∞'∙ _) J A true j a k
  ΠR-extend₃→JoinR-Bool true (push (false , j , a) k) =
    ΠR-extend₃→JoinR-pushᵣ (RP∞'∙ _) J A false j a k
  ΠR-extend₃→JoinR-Bool true (push (true , j , a) k) =
    ΠR-extend₃→JoinR-pushₗ (RP∞'∙ _) J A true j a k

  ΠR-extend₃→JoinR-Bool≡ : (i : Bool)
    (x : ΠJoinR₃.ΠR-extend₃ (RP∞'∙ ℓ) J A)
    → ΠR-extend₃→JoinR-Bool i x ≡ ΠR-extend₃→JoinR (RP∞'∙ _) J A i x
  ΠR-extend₃→JoinR-Bool≡ i (inl x) = refl
  ΠR-extend₃→JoinR-Bool≡ i (inr x) = refl
  ΠR-extend₃→JoinR-Bool≡ false (push (false , j , a) i₁) k =
    lUnit (ΠR-extend₃→JoinR-pushₗ (RP∞'∙ _) J A false j a) k i₁
  ΠR-extend₃→JoinR-Bool≡ true (push (false , j , a) i₁) k =
    lUnit (ΠR-extend₃→JoinR-pushᵣ (RP∞'∙ _) J A false j a) k i₁
  ΠR-extend₃→JoinR-Bool≡ false (push (true , j , a) i₁) k =
    lUnit (ΠR-extend₃→JoinR-pushᵣ (RP∞'∙ _) J A true j a) k i₁
  ΠR-extend₃→JoinR-Bool≡ true (push (true , j , a) i₁) k =
    lUnit (ΠR-extend₃→JoinR-pushₗ (RP∞'∙ _) J A true j a) k i₁

ΠR-extend₃→JoinR≡ΠR-extend₂→JoinR :
  (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
  (i : fst I) (x : ΠJoinR₂.ΠR-extend I J A)
  → ΠR-extend₃→JoinR I J A i (ΠJoinR₃.ΠR-extend₂→ΠR-extend₃ I J A x)
   ≡ ΠR-extend₂→JoinR I J A i x
ΠR-extend₃→JoinR≡ΠR-extend₂→JoinR I J A i (inl x) = refl
ΠR-extend₃→JoinR≡ΠR-extend₂→JoinR I J A i (inr x) = refl
ΠR-extend₃→JoinR≡ΠR-extend₂→JoinR {ℓ = ℓ} I J A i (push (i' , a) k) l =
  push-case I i' A i a l k
  where
  module _ (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ) where
    module _ (j' : fst J) (g : (i : Bool) (j : fst J) → A i j) where
      fill₁-refl : cong (ΠR-extend₃→JoinR-Bool J A false)
                        ((λ j → inl (true , (j' , g true j') , g false))
                       ∙ push (true , j' , inr g))
                 ≡ refl
      fill₁-refl i j =
        ΠR-extend₃→JoinR-Bool J A false
          (compPath-filler' refl (push (true , j' , inr g)) (~ i) j)

      fill₂-refl : cong (ΠR-extend₃→JoinR-Bool J A true)
                        ((λ j → inl (true , (j' , g true j') , g false))
                        ∙ push (true , j' , inr g))
                 ≡ pushR (j' , g true j') (g true) refl
      fill₂-refl i j =
        ΠR-extend₃→JoinR-Bool J A true
          (compPath-filler' refl (push (true , j' , inr g)) (~ i) j)

      abstract
        fill₁ : (a : A true j')  (q : g true j' ≡ a)
          → cong (ΠR-extend₃→JoinR-Bool J A false)
               ((λ j → inl (true , (j' , q (~ j)) , g false))
                ∙ push (true , j' , inr g))
           ≡ refl
        fill₁ = J> fill₁-refl

        fill₂ : (a : A true j')  (q : g true j' ≡ a)
          → cong (ΠR-extend₃→JoinR-Bool J A true)
                  ((λ j → inl (true , (j' , q (~ j)) , g false))
                  ∙ push (true , j' , inr g))
           ≡ pushR (j' , a) (g true) q
        fill₂ = J> fill₂-refl

        fill₁-refl≡ : fill₁ (g true j') refl ≡ fill₁-refl
        fill₁-refl≡ =
          JRefl (λ a q
            → cong (ΠR-extend₃→JoinR-Bool J A false)
                    ((λ j → inl (true , (j' , q (~ j)) , g false))
                    ∙ push (true , j' , inr g))
             ≡ refl)
            fill₁-refl

        fill₂-refl≡ : fill₂ (g true j') refl ≡ fill₂-refl
        fill₂-refl≡ =
          JRefl (λ a q
            → cong (ΠR-extend₃→JoinR-Bool J A true)
                     ((λ j → inl (true , (j' , q (~ j)) , g false))
                     ∙ push (true , j' , inr g))
             ≡ pushR (j' , a) (g true) q)
            fill₂-refl

      fill-inl : (f : (i : Bool) → A i j') (q : (λ j → g j j') ≡ f)
        → Cube
           (λ j k → pushR (j' , f false)  (g false) (funExt⁻ q false) (~ k))
           (fill₁ (f true) (funExt⁻ q true))
           (λ i k → ΠR-extend₃→JoinR-Bool J A false
                     (ΠJoinR₃.ΠR-extend₂→ΠR-extend₃-push (RP∞'∙ ℓ) J A true
                      (push ((inl j' , f) , g , (funExt⁻ q)) i) k))
           (λ i k → pushR (j' , f false)  (g false) (funExt⁻ q false) (~ k ∨ i))
           (λ _ _ → inrR (g false))
           λ i j → pushR (j' , f false) (g false) (funExt⁻ q false) i
      fill-inl =
        J> ((λ i j k → ΠR-extend₃→JoinR-Bool J A false
                          (ΠJoinR₃.ΠR-extend₂→ΠR-extend₃-push-fillerₗ (RP∞'∙ _)
                            J A true j' _ g (λ _ → refl) i k (~ j)))
           ▷ sym fill₁-refl≡)

      fill₂-inl : (f : (i : Bool) → A i j') (q : (λ i → g i j') ≡ f)
        → Cube (λ j k → inlR (j' , f true))
                (fill₂ (f true) (funExt⁻ q true))
                (λ i k → ΠR-extend₃→JoinR-Bool J A true
                           (ΠJoinR₃.ΠR-extend₂→ΠR-extend₃-push (RP∞'∙ ℓ) J A
                            true (push ((inl j' , f) , g , (funExt⁻ q)) i) k))
                (λ i k → pushR (j' , f true)  (g true) (funExt⁻ q true) (k ∧ i))
                (λ i j → inlR (j' , f true))
                λ i j → pushR (j' , f true) (g true) (funExt⁻ q true) i
      fill₂-inl =
        J> ((λ i j k → ΠR-extend₃→JoinR-Bool J A true
             (ΠJoinR₃.ΠR-extend₂→ΠR-extend₃-push-fillerₗ (RP∞'∙ _) J A true j'
               _ g (λ _ → refl) i k (~ j)))
        ▷ sym fill₂-refl≡)

    fill-inr : (x : Bool ≃ fst J) (p : (i : Bool) (j : fst J) → A i j)
      (f : (i : Bool) → A i (fst x i)) (q : (λ j → p j (fst x j)) ≡ f)
      → Cube (λ j k → pushR (fst x false , f false)
                              (p false) (funExt⁻ q false) (~ k))
              (fill₁ (fst x true) p (f true) (funExt⁻ q true))
              (λ i k → ΠR-extend₃→JoinR-Bool J A false
                         (ΠJoinR₃.ΠR-extend₂→ΠR-extend₃-push (RP∞'∙ ℓ) J A true
                           (push ((inr x , f) , p , (funExt⁻ q)) i) k))
              (λ i k → pushR (fst x false , f false)
                              (p false) (funExt⁻ q false) (~ k ∨ i))
              (λ _ _ → inrR (p false))
              λ i j → pushR (fst x false , f false) (p false) (funExt⁻ q false) i
    fill-inr x p =
      J> ((λ i j k
      → ΠR-extend₃→JoinR-Bool J A false
          (ΠJoinR₃.ΠR-extend₂→ΠR-extend₃-push-fillerᵣ (RP∞'∙ _) J A true
            x _ p (λ _ → refl) i k (~ j)))
       ▷ sym (fill₁-refl≡ (fst x true) p))

    fill₂-inr : (x : Bool ≃ fst J) (p : (i : Bool) (j : fst J) → A i j)
      (f : (i : Bool) → A i (fst x i)) (q : (λ j → p j (fst x j)) ≡ f)
      → Cube (λ j k → inlR (fst x true , f true))
         (fill₂ (fst x true) p (f true) (funExt⁻ q true))
         (λ i k → ΠR-extend₃→JoinR-Bool J A true
                    (ΠJoinR₃.ΠR-extend₂→ΠR-extend₃-push (RP∞'∙ ℓ) J A true
                      (push ((inr x , f) , p , (funExt⁻ q)) i) k))
         (λ i k → pushR (fst x true , f true)  (p true) (funExt⁻ q true) (k ∧ i))
         (λ i j → inlR (fst x true , f true))
         λ i j → pushR (fst x true , f true) (p true) (funExt⁻ q true) i
    fill₂-inr x p =
      J> ((λ i j k → lem i j k)
      ▷ sym (fill₂-refl≡ (fst x true) p))
      where
      lem : (i j k : _) → _
      lem i j k =
        hcomp (λ r →
        λ {(i = i0) → inlR (fst x true , p true (fst x true))
         ; (i = i1) → ΠR-extend₃→JoinR-Bool J A true
                        (compPath-filler' refl
                          (push (true , (fst x true) , (inr p))) (~ j ∧ r) k)
         ; (j = i0) → ΠR-extend₃→JoinR-Bool J A true
                        (ΠJoinR₃.ΠR-extend₂→ΠR-extend₃-push-fillerᵣ
                          (RP∞'∙ ℓ) J A true x
                          (λ i → p i (fst x i)) p (λ _ → refl) i k r)
         ; (j = i1) → pushR (fst x true , p true (fst x true)) (p true)
                             refl (k ∧ i)
         ; (k = i0) → inlR (fst x true , p true (fst x true))
         ; (k = i1) → pushR (fst x true , p true (fst x true)) (p true)
                             refl i})
        (hcomp (λ r →
        λ {(i = i0) → inlR (fst x true , p true (fst x true))
         ; (i = i1) →  pushR (fst x true , p true (fst x true)) (p true) refl k
         ; (j = i1) → pushR (fst x true , p true (fst x true)) (p true)
                             refl (k ∧ i)
         ; (k = i0) → inlR (fst x true , p true (fst x true))
         ; (k = i1) → pushR (fst x true , p true (fst x true)) (p true) refl i})
         (pushR (fst x true , p true (fst x true)) (p true) refl (k ∧ i)))

    mainₗ : (x : _)
      → cong (ΠR-extend₃→JoinR-Bool J A false)
              (ΠJoinR₃.ΠR-extend₂→ΠR-extend₃-push (RP∞'∙ ℓ) J A true x)
      ≡ PushTop→JoinRᵣ (RP∞'∙ ℓ) J A true x
    mainₗ (inl ((inl x , _) , _)) = refl
    mainₗ  (inl ((inr x , _) , _)) = refl
    mainₗ  (inr ((f , a) , g , q)) = fill₁ f g a q
    mainₗ  (push ((inl x , f) , p , q) i) j k = fill-inl x p f (funExt q) i j k
    mainₗ (push ((inr x , f) , p , q) i) j k = fill-inr x p f (funExt q) i j k

    mainᵣ : (x : _)
      → cong (ΠR-extend₃→JoinR-Bool J A true)
          (ΠJoinR₃.ΠR-extend₂→ΠR-extend₃-push (RP∞'∙ ℓ) J A true x)
      ≡ PushTop→JoinRₗ (RP∞'∙ ℓ) J A true x
    mainᵣ (inl ((inl x , _) , _)) = refl
    mainᵣ  (inl ((inr x , _) , _)) = refl
    mainᵣ  (inr ((f , a) , g , q)) = fill₂ f g a q
    mainᵣ  (push ((inl x , f) , p , q) i) j k = fill₂-inl x p f (funExt q) i j k
    mainᵣ (push ((inr x , f) , p , q) i) j k = fill₂-inr x p f (funExt q) i j k


    main : (k : _) (x : _)
      → cong (ΠR-extend₃→JoinR-Bool J A k)
          (ΠJoinR₃.ΠR-extend₂→ΠR-extend₃-push (RP∞'∙ ℓ) J A true x)
      ≡ cong (ΠR-extend₂→JoinR (RP∞'∙ ℓ) J A k) (push (true , x))
    main false x = mainₗ x ∙ lUnit _
    main true x = mainᵣ x ∙ lUnit _

  push-case : (I : RP∞' ℓ) (i' : fst I) (A : fst I → fst J → Type ℓ)
    (i : fst I) (a : _)
    → cong (ΠR-extend₃→JoinR I J A i)
            (cong (ΠJoinR₃.ΠR-extend₂→ΠR-extend₃ I J A) (push (i' , a)))
     ≡ cong (ΠR-extend₂→JoinR I J A i) (push (i' , a))
  push-case = JRP∞' λ A k x
    → (λ j i → ΠR-extend₃→JoinR-Bool≡ J A k
                  (ΠJoinR₃.ΠR-extend₂→ΠR-extend₃ (RP∞'∙ ℓ) J A
                    (push (true , x) i)) (~ j))
      ∙ main J A k x

-- we get a map UnordJoin²₂ → UnordJoin²-alt, the latter being
-- easier to map out of.
UnordJoin²₂→UnordJoin²-alt : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
  → UnordJoin²₂ I J A
  → UnordJoin²-alt I J A
UnordJoin²₂→UnordJoin²-alt I J A (inl x) = inl x
UnordJoin²₂→UnordJoin²-alt I J A (inr x) =
  inr (ΠJoinR₃.ΠR-extend₂→ΠR-extend₃ I J A x)
UnordJoin²₂→UnordJoin²-alt I J A (push (a , b) i) =
  ((λ t → inl (a , ΠR-extend₃→JoinR≡ΠR-extend₂→JoinR I J A a b (~ t)))
  ∙ push (a , ΠJoinR₃.ΠR-extend₂→ΠR-extend₃ I J A b)) i

-- So, we have left to define a map from UnordJoin²-alt into the
-- nestled unordered join ∗ⱼ ∗ᵢ Aⱼᵢ. The following module contains a
-- description of the minimal data we need to provide in order to
-- define such a map out of UnordJoin²-alt, assuming the domain is
-- defined for all I, J : RP∞ and (A : I → J → Type)

-- Below Targ is the type we are eliminating into. For future
-- flexibility We also allow for a specification of another Targ' and
-- an equivalence Targ Bool Bool ≃ Targ'. To get the usual elimination
-- principle, simply instantiate with Targ' := Targ Bool Bool.
module _ {ℓ : Level}
  (Targ : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) → ΠJoinR₃.ΠR-extend₃ I J A → Type ℓ)
  (Targ' : (A : Bool → Bool → Type ℓ) → ΠJoinR₃.ΠR-extend₃ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A → Type ℓ)
  (e : (A : Bool → Bool → Type ℓ) (x : ΠJoinR₃.ΠR-extend₃ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A)
     → Targ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A x ≃ Targ' A x) where

  -- The minimal data needed to map out of ΠR-extend₃
  record 𝕄₁ : Type (ℓ-suc ℓ) where
    field
      inler : (A : Bool → Bool → Type ℓ) (a : A true true) (b : (t : Bool) → A false t)
        → Targ' A (inl (true , (true , a) , b))
      inr-inr : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) (t : (i : fst I) (j : fst J) → A i j)
             → Targ I J A (inr (inr t))
      inr-inl-inl : (I : RP∞' ℓ) (A : fst I → Bool → Type ℓ)
                   (f : (x : fst I) → A x true)
                     → Σ[ k ∈ Targ I (RP∞'∙ ℓ) A (inr (inl (inl true , f))) ]
                       ((p : (i : fst I) (j : Bool) → A i j) (q : (x : fst I) → p x true ≡ f x)
                     → PathP (λ r → Targ I (RP∞'∙ ℓ) A (inr (push ((inl true , f) , (p , q)) r)))
                              k (inr-inr I (RP∞'∙ ℓ) A p))
      inr-inl-inr : (I : RP∞' ℓ) (A : fst I → fst I → Type ℓ) (f : (i : fst I) → A i i)
           → Σ[ k ∈ Targ I I A (inr (inl (inr (idEquiv (fst I)) , f))) ]
               ((p : (i : fst I) (j : fst I) → A i j) (q : (x : fst I) → p x x ≡ f x)
            → PathP (λ r → Targ I I A (inr (push ((inr (idEquiv (fst I)) , f) , (p , q)) r)))
                                   k (inr-inr I I A p))
      push-inl-inl : (A : Bool → Bool → Type ℓ) (f : (i : Bool) → A i true)
       (g : (j : Bool) → A false j) (p : g true ≡ f false)
       → PathP (λ k → Targ' A
                (push (true , true , inl (inl (f , g , p))) k))
              (inler A (f true) g)
              (fst (e A _) (inr-inl-inl (RP∞'∙ ℓ) A f .fst))
      push-inr : (A : Bool → Bool → Type ℓ) (g : (i j : Bool) → A i j)
         → PathP (λ k → Targ' A (push (true , true , inr g) k))
                  (inler A (g true true) (g false))
                  (fst (e A _) (inr-inr (RP∞'∙ ℓ) (RP∞'∙ ℓ) A g))
      push-inl-inr : (A : Bool → Bool → Type ℓ) (g : (i : Bool) → A i i) (f : (t : Bool) → A false t) (p : f false ≡ g false)
                   → PathP (λ k → Targ' A (push (true , true , inl (inr (idEquiv Bool , refl , g , f , p))) k))
                           (inler A (g true) f)
                     (fst (e A _) (inr-inl-inr (RP∞'∙ ℓ) A g .fst))
      push-push-inr : (A : Bool → Bool → Type ℓ) (g : (i j : Bool) → A i j)
         → SquareP (λ i j → Targ' A
                              (push (true , true , push (inr (idEquiv Bool , refl , g)) i) j))
                   (push-inl-inr A (λ i → g i i) (g false) refl)
                   (push-inr A g)
                   (λ _ → inler A (g true true) (g false))
                   λ i → fst (e A _) (inr-inl-inr (RP∞'∙ ℓ) A (λ i₁ → g i₁ i₁) .snd g (λ _ → refl) i)
      push-push-inl : (A : Bool → Bool → Type ℓ) (g : (i j : Bool) → A i j)
         → SquareP (λ i j → Targ' A
                             (push (true , true , push (inl g) i) j))
                     (push-inl-inl A (λ i₁ → g i₁ true) (g false) (λ _ → g false true))
                     (push-inr A g)
                     (λ _ → inler A (g true true) (g false))
                     (λ i → fst (e A _) (inr-inl-inl (RP∞'∙ ℓ) A (λ i → g i true) .snd g (λ _ → refl) i))

  module _
    (G : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
              → (x : ΠJoinR₃.ΠR-extend₃ I J A) → (i : fst I) → Targ I J A x)
    (pushG : (A : Bool → Bool → Type ℓ)
             (x : ΠJoinR₃.ΣΠJoinRBack (RP∞'∙ ℓ) (RP∞'∙ ℓ) A) (a : Bool)
            → PathP (λ i → Targ' A (push x i))
                     (fst (e A _) (G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A
                       (inl (ΠJoinR₃.ΣΠJoinRBack→ₗ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A x)) a))
                     (fst (e A _) (G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A
                       (inr (ΠJoinR₃.ΣΠJoinRBack→ᵣ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A x)) a)))
    where
    module _ (m : 𝕄₁) where
      open 𝕄₁ m

      -- The minimal data to check that the map out of ΠR-extend₃ is
      -- coherent with some other family of maps Gᵢ : ΠR-extend₃ → ...,
      -- where i : I.
      record 𝕄₂ : Type (ℓ-suc ℓ) where
        field
          G-inler : (A : Bool → Bool → Type ℓ) (a : A true true) (b : (t : Bool) → A false t) (i : Bool)
                          → fst (e A _) (G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (inl (true , (true , a) , b)) i) ≡ inler A a b
          G-inr-inr : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) (t : (i : fst I) (j : fst J) → A i j)
                             (i : fst I)
                        → G I J A (inr (inr t)) i ≡ inr-inr I J A t
          G-inr-inl-inl₁ : (I : RP∞' ℓ) (A : fst I → Bool → Type ℓ)
                              (f : (x : fst I) → A x true) (i : fst I)
                           → (G I (RP∞'∙ ℓ) A (inr (inl (inl true , f))) i)
                             ≡ inr-inl-inl I A f .fst
          G-inr-inl-inl₂ : (I : RP∞' ℓ) (A : fst I → Bool → Type ℓ)
                              (f : (x : fst I) → A x true) (i : fst I)
                              (p : (i₁ : fst I) (j : Bool) → A i₁ j) (q : (x : fst I) → p x true ≡ f x)
                           → SquareP (λ i j → Targ I (RP∞'∙ ℓ) A (inr (push ((inl true , f) , p , q) j)))
                                      (λ k → G I (RP∞'∙ ℓ) A (inr (push ((inl true , f) , p , q) k)) i)
                                      (inr-inl-inl I A f .snd p q)
                                      (G-inr-inl-inl₁ I A f i)
                                      (G-inr-inr I (RP∞'∙ ℓ) A p i)
          G-inr-inl-inr₁ : (I : RP∞' ℓ) (A : fst I → fst I → Type ℓ)
            (f : (i : fst I) → A i i) (i : fst I)
            → G I I A (inr (inl (inr (idEquiv (fst I)) , f))) i
              ≡ inr-inl-inr I A f .fst
          G-inr-inl-inr₂ : (I : RP∞' ℓ) (A : fst I → fst I → Type ℓ)
            (f : (i : fst I) → A i i) (p : (i₁ j : fst I) → A i₁ j)
            (q : ((x : fst I) → p x x ≡ f x))
            (i : fst I) →
            SquareP
              (λ i j → Targ I I A
                        (inr (push ((inr (idEquiv (fst I)) , f) , p , q) j)))
              (λ k → G I I A (inr (push ((inr (idEquiv (fst I)) , f) , p , q) k)) i)
              (inr-inl-inr I A f .snd p q)
              (G-inr-inl-inr₁ I A f i)
              (G-inr-inr I I A p i)

          G-push-inl-inl : (A : Bool → Bool → Type ℓ) (f : (i : fst (RP∞'∙ ℓ)) → A i true)
                    (g : (j : Bool) → A false j) (p : g true ≡ f false) (i : Bool)
                    → SquareP (λ i j → Targ' A
                                         (push (true , true , inl (inl (f , g , p))) j))
                               (λ k → pushG A (true , true , inl (inl (f , g , p))) i k)
                               (push-inl-inl A f g p)
                               (G-inler A (f true) g i)
                               λ k → fst (e A _) (G-inr-inl-inl₁ (RP∞'∙  ℓ) A f i k)
          G-push-inr : (A : Bool → Bool → Type ℓ) (g : (i j : Bool) → A i j) (i : Bool)
                 → SquareP (λ i j → Targ' A (push (true , true , inr g) j))
                            (pushG A (true , true , inr g) i)
                            (push-inr A g)
                            (G-inler A (g true true) (g false) i)
                            (λ k → fst (e A _) (G-inr-inr (RP∞'∙ ℓ) (RP∞'∙ ℓ) A g i k))
          G-push-inl-inr : (A : Bool → Bool → Type ℓ) (g : (i : Bool) → A i i) (f : (t : Bool) → A false t) (p : f false ≡ g false) (x : Bool)
                           → SquareP (λ i j → Targ' A (push (true , true , inl (inr (idEquiv Bool , refl , g , f , p))) j))
                             (pushG A (true , true , inl (inr (idEquiv Bool , refl , g , f , p))) x)
                             (push-inl-inr A g f p)
                             (G-inler A (g true) f x)
                             (λ t → fst (e A _) (G-inr-inl-inr₁ (RP∞'∙ ℓ) A g x t))
          G-push-push-inr : (A : Bool → Bool → Type ℓ) (g : (i j : Bool) → A i j) (x : Bool)
                 → CubeP (λ k i j → Targ' A
                                      (push (true , true , push (inr (idEquiv Bool , refl , g)) i) j))
                     (λ i j → pushG A (true , true , push (inr (idEquiv Bool , refl , g)) i) x j)
                     (push-push-inr A g)
                     (G-push-inl-inr A (λ i → g i i) (g false) refl x)
                     (G-push-inr A g x)
                     (λ i _ → G-inler A (g true true) (g false) x i)
                     λ s t → fst (e A _) (G-inr-inl-inr₂ (RP∞'∙ ℓ) A (λ i → g i i) g (λ i → refl) x s t)
          G-push-push-inl :
                    (A : Bool → Bool → Type ℓ) (g : (i j : Bool) → A i j) (x : Bool)
                 → CubeP (λ k i j → Targ' A
                                      (push (true , true , push (inl g) i) j))
                     (λ i j → pushG A (true , true , push (inl g) i) x j)
                     (push-push-inl A g)
                     (G-push-inl-inl A (λ i → g i true) (g false) refl x)
                     (G-push-inr A g x)
                     (λ i _ → G-inler A (g true true) (g false) x i)
                     λ s t → fst (e A _) (G-inr-inl-inl₂ (RP∞'∙ ℓ) A (λ i → g i true) x g (λ _ → refl) s t)

    -- all in one
    𝕄 : Type _
    𝕄 = Σ 𝕄₁ 𝕄₂

-- We instantiate the above and show that it indeed can be used to
-- define a map out of UnordJoin²-alt.
module ΠR-extend₃-elim
  (Targ : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
        → ΠJoinR₃.ΠR-extend₃ I J A → Type ℓ)
  (m : 𝕄₁ Targ (Targ (RP∞'∙ ℓ) (RP∞'∙ ℓ)) λ _ _ → idEquiv _)  where
  -- first goal: transform the data given to the data we need to
  -- define a map out of ΠR-extend₃
  open 𝕄₁ m
  abstract
    inr-inl-inl* : (I J : RP∞' ℓ) (j : fst J) (A : fst I → fst J → Type ℓ)
      (f : (x : fst I) → A x j)
        → Σ[ k ∈ Targ I J A (inr (inl (inl j , f))) ]
            ((p : (i : fst I) (j : fst J) → A i j)
             (q : (x : fst I) → p x j ≡ f x)
          → PathP (λ r → Targ I J A (inr (push ((inl j , f) , (p , q)) r)))
                   k (inr-inr I J A p))
    inr-inl-inl* I = JRP∞' (inr-inl-inl I)

    inr-inl-inl*≡ : (I : RP∞' ℓ) (A : fst I → Bool → Type ℓ)
         (f : (x : fst I) → A x true)
      → inr-inl-inl* I (RP∞'∙ ℓ) true A f ≡ inr-inl-inl I A f
    inr-inl-inl*≡ I A f i = help i A f
      where
      help : inr-inl-inl* I (RP∞'∙ ℓ) true ≡ inr-inl-inl I
      help = JRP∞'∙ (inr-inl-inl I)

    inr-inl-inr* :
      (I J : RP∞' ℓ) (e : fst I ≃ fst J) (A : fst I → fst J → Type ℓ)
         (f : (i : fst I) → A i (fst e i))
     → Σ[ k ∈ Targ I J A (inr (inl (inr e , f))) ]
         ((p : (i : fst I) (j : fst J) → A i j)
          (q : (x : fst I) → p x (fst e x) ≡ f x)
      → PathP (λ r → Targ I J A (inr (push ((inr e , f) , (p , q)) r)))
                             k (inr-inr I J A p))
    inr-inl-inr* I = EquivJRP∞' I (inr-inl-inr I)

    inr-inl-inr*≡ : (I : RP∞' ℓ) (A : fst I → fst I → Type ℓ)
                 (f : (i : fst I) → A i i)
             → inr-inl-inr* I I (idEquiv (fst I)) A f ≡ inr-inl-inr I A f
    inr-inl-inr*≡ I A f i = help i A f
      where
      help : inr-inl-inr* I I (idEquiv (fst I)) ≡ inr-inl-inr I
      help = EquivJRP∞'-idEquiv I (inr-inl-inr I)

    ΠR-extend→inl' : (J : RP∞' ℓ) (j : fst J) (A : Bool → fst J → Type ℓ)
       (a : A true j)
       (b : (t : fst J) → A false t)
      → Targ (RP∞'∙ ℓ) J A (inl (true , (j , a) , b))
    ΠR-extend→inl' = JRP∞' inler

    ΠR-extend→inl : (I : RP∞' ℓ) (i : fst I)
      (J : RP∞' ℓ) (j : fst J) (A : fst I → fst J → Type ℓ)
      (a : A i j)
      (b : (j : _) → A (RP∞'-fields.notRP∞' I i) j)
      → Targ I J A (inl (i , (j , a) , b))
    ΠR-extend→inl = JRP∞' ΠR-extend→inl'

    ΠR-extend→inl≡ : (A : Bool → Bool → Type ℓ)
      (a : A true true) (b : (t : Bool) → A false t)
      → ΠR-extend→inl (RP∞'∙ ℓ) true (RP∞'∙ ℓ) true A a b ≡ inler A a b
    ΠR-extend→inl≡ A a b =
       (λ k → id₁ k (RP∞'∙ ℓ) true A a b)
      ∙ λ k → id₂ k A a b
      where
      id₁ : ΠR-extend→inl (RP∞'∙ ℓ) true ≡ ΠR-extend→inl'
      id₁ = JRP∞'∙ ΠR-extend→inl'

      id₂ : ΠR-extend→inl' (RP∞'∙ ℓ) true ≡ inler
      id₂ = JRP∞'∙ inler

  ΠR-extend→inr : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
    (x : ΠJoinR₃.ΠR-base I J A) → Targ I J A (inr x)
  ΠR-extend→inr I J A (inl (inl j , f)) = inr-inl-inl* I J j A f .fst
  ΠR-extend→inr I J A (inl (inr e , f)) = inr-inl-inr* I J e A f .fst
  ΠR-extend→inr I J A (inr x) = inr-inr I J A x
  ΠR-extend→inr I J A (push ((inl j , f) , p , q) i) = inr-inl-inl* I J j A f .snd p q i
  ΠR-extend→inr I J A (push ((inr e , f) , p , q) i) = inr-inl-inr* I J e A f .snd p q i

  push-inr*-type : (A : Bool → Bool → Type ℓ)
    (e : Bool ≃ Bool) (pf : fst e true ≡ true)
    → Type ℓ
  push-inr*-type A e pf =
    Σ[ F ∈ (((g : (i : fst (RP∞'∙ ℓ)) → A i (fst e i))
     (f : (t : Bool) → A false t)
     (p : f (fst e false) ≡ g false)
     → PathP (λ k → Targ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A
                      (push (true , true
                           , inl (inr (e , pf , g , f , p))) k))
         (ΠR-extend→inl (RP∞'∙ ℓ) true (RP∞'∙ ℓ) (fst e true) A (g true) f)
         (inr-inl-inr* (RP∞'∙ ℓ) (RP∞'∙ ℓ) e A g .fst))) ]
      ((g : (i j : Bool) → A i j)
      → SquareP
           (λ i j → Targ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A
                      (push (true , true , push (inr (e , pf , g)) i) j))
          (F (λ i → g i (fst e i)) (g false) refl)
          (ΠR-extend→inl≡ A (g true true) (g false)
          ◁ push-inr A g)
          (λ i → ΠR-extend→inl (RP∞'∙ ℓ) true (RP∞'∙ ℓ)
                   (pf i) A (g true (pf i)) (g false))
          (inr-inl-inr* (RP∞'∙ ℓ) (RP∞'∙ ℓ) e A (λ i → g i (fst e i))
                   .snd g λ _ → refl))

  push-inr*-bool-filler : (A : Bool → Bool → Type ℓ)
    → (g : (i j : Bool) → A i j)
    → (i j k : _) → _
  push-inr*-bool-filler A g i j k =
    hfill (λ k →
    λ {(i = i0) → doubleWhiskFiller
        (ΠR-extend→inl≡ A (g true true) (g false))
        (push-inl-inr A (λ i → g i i) (g false) refl)
        (cong fst (sym (inr-inl-inr*≡ (RP∞'∙ ℓ) A (λ i → g i i)))) k j
     ; (i = i1) → doubleWhiskFiller
                    (ΠR-extend→inl≡ A (g true true) (g false))
                    (push-inr A g)
                    (λ _ → inr-inr (RP∞'∙ ℓ) (RP∞'∙ ℓ) A g) k j
     ; (j = i0) → ΠR-extend→inl≡ A (g true true) (g false) (~ k)
     ; (j = i1) → inr-inl-inr*≡ (RP∞'∙ ℓ) A (λ i → g i i) (~ k)
                    .snd g (λ _ → refl) i})
     (inS (push-push-inr A g i j))
     k

  push-inr*-bool : (A : Bool → Bool → Type ℓ)
    → push-inr*-type A (idEquiv _) refl
  fst (push-inr*-bool A) g f p =
      ΠR-extend→inl≡ A (g true) f
    ◁ push-inl-inr A g f p
    ▷ cong fst (sym (inr-inl-inr*≡ (RP∞'∙ ℓ) A g))
  snd (push-inr*-bool A) g i j = push-inr*-bool-filler A g i j i1

  push-inl-inl*-bool :
    (A : Bool → Bool → Type ℓ) (g : (i j : Bool) → A i j)
    → SquareP
        (λ i j → Targ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A
                   (push (true , true , push (inl g) i) j))
        (ΠR-extend→inl≡ A (g true true) (g false)
          ◁ push-inl-inl A (λ i₁ → g i₁ true) (g false) refl
          ▷ cong fst (sym (inr-inl-inl*≡ (RP∞'∙ ℓ) A (λ i₂ → g i₂ true))))
        (ΠR-extend→inl≡ A (g true true) (g false) ◁ push-inr A g)
        (λ _ → ΠR-extend→inl (RP∞'∙ ℓ) true (RP∞'∙ ℓ) true A
                 (g true true) (g (RP∞'-fields.notRP∞' (RP∞'∙ ℓ) true)))
         (inr-inl-inl* (RP∞'∙ ℓ) (RP∞'∙ ℓ) true A (λ i₁ → g i₁ true) .snd g λ _ → refl)
  push-inl-inl*-bool A g i j =
    hcomp (λ k →
    λ {(i = i0) → doubleWhiskFiller
                   (ΠR-extend→inl≡ A (g true true) (g false))
                   (push-inl-inl A (λ i₁ → g i₁ true) (g false) refl)
                   (cong fst (sym (inr-inl-inl*≡ (RP∞'∙ ℓ) A (λ i → g i true)))) k j
     ; (i = i1) → doubleWhiskFiller
                   (ΠR-extend→inl≡ A (g true true) (g false))
                   (push-inr A g)
                   (λ _ → inr-inr (RP∞'∙ ℓ) (RP∞'∙ ℓ) A g) k j
     ; (j = i0) → ΠR-extend→inl≡ A (g true true) (g false) (~ k)
     ; (j = i1) → inr-inl-inl*≡ (RP∞'∙ ℓ) A (λ i → g i true) (~ k) .snd g (λ _ → refl) i})
     (push-push-inl A g i j)

  abstract
    push-inr* : (A : Bool → Bool → Type ℓ)
      (e : Bool ≃ Bool) (pf : fst e true ≡ true)
      → push-inr*-type A e pf
    push-inr* A = Bool≃Bool-elim-id _ (push-inr*-bool A)

    push-inr*≡ : (A : Bool → Bool → Type ℓ)
      → push-inr* A (idEquiv _) refl ≡ push-inr*-bool A
    push-inr*≡ A = Bool≃Bool-elim-idβ _ (push-inr*-bool A)

  ΠR-extend→push-bool : (A : Bool → Bool → Type ℓ)
      (x : ΠJoinR₃.ΠJoinRBack (RP∞'∙ ℓ) (RP∞'∙ ℓ) A true true)
        → PathP (λ k → Targ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push (true , true , x) k))
                 (ΠR-extend→inl (RP∞'∙ ℓ) true (RP∞'∙ ℓ)
                  (fst (fst (ΠJoinR₃.ΠJoinRBack→leftPush (RP∞'∙ ℓ) (RP∞'∙ ℓ)
                    A true true x))) A
                 (snd (fst (ΠJoinR₃.ΠJoinRBack→leftPush (RP∞'∙ ℓ) (RP∞'∙ ℓ)
                   A true true x)))
                 (snd (ΠJoinR₃.ΠJoinRBack→leftPush (RP∞'∙ ℓ) (RP∞'∙ ℓ)
                   A true true x)))
         (ΠR-extend→inr (RP∞'∙ ℓ) (RP∞'∙ ℓ) A
           (ΠJoinR₃.ΠJoinRBack→ΠR-base (RP∞'∙ ℓ) (RP∞'∙ ℓ) A true true x))
  ΠR-extend→push-bool A (inl (inl (f , g , p))) =
      ΠR-extend→inl≡ A (f true) g
    ◁ push-inl-inl A f g p
    ▷ cong fst (sym (inr-inl-inl*≡ (RP∞'∙ ℓ) A f))
  ΠR-extend→push-bool A (inl (inr (e , pf , g , p , q))) =
    push-inr* A e pf .fst g p q
  ΠR-extend→push-bool A (inr x) =
    ΠR-extend→inl≡ A (x true true) (x false) ◁ push-inr A x
  ΠR-extend→push-bool A (push (inl g) i) j = push-inl-inl*-bool A g i j
  ΠR-extend→push-bool A (push (inr (e , pf , g)) i) j =
    push-inr* A e pf .snd g i j

  abstract
    ΠR-extend→push' : (J : RP∞' ℓ) (j : fst J) (A : Bool → fst J → Type ℓ)
      → (x : ΠJoinR₃.ΠJoinRBack (RP∞'∙ ℓ) J A true j)
      → PathP (λ k → Targ (RP∞'∙ ℓ) J A (push (true , j , x) k))
          (ΠR-extend→inl (RP∞'∙ ℓ) true J
           (fst (fst (ΠJoinR₃.ΠJoinRBack→leftPush (RP∞'∙ ℓ)  J A true j x))) A
            (snd (fst (ΠJoinR₃.ΠJoinRBack→leftPush (RP∞'∙ ℓ) J A true j x)))
             (snd (ΠJoinR₃.ΠJoinRBack→leftPush (RP∞'∙ ℓ) J A true j x)))
           (ΠR-extend→inr (RP∞'∙ ℓ) J A
            (ΠJoinR₃.ΠJoinRBack→ΠR-base (RP∞'∙ ℓ) J A true j x))
    ΠR-extend→push' = JRP∞' ΠR-extend→push-bool

    ΠR-extend→push : (I : RP∞' ℓ) (i : fst I) (J : RP∞' ℓ) (j : fst J)
      (A : fst I → fst J → Type ℓ) (x : ΠJoinR₃.ΠJoinRBack I J A i j) →
      PathP (λ k → Targ I J A (push (i , j , x) k))
       (ΠR-extend→inl I i J
        (fst (fst (ΠJoinR₃.ΠJoinRBack→leftPush I J A i j x))) A
         (snd (fst (ΠJoinR₃.ΠJoinRBack→leftPush I J A i j x)))
          (snd (ΠJoinR₃.ΠJoinRBack→leftPush I J A i j x)))
       (ΠR-extend→inr I J A (ΠJoinR₃.ΠJoinRBack→ΠR-base I J A i j x))
    ΠR-extend→push = JRP∞' ΠR-extend→push'

    ΠR-extend→push≡ : (A : Bool → Bool → Type ℓ) (k : Bool)
      (a : ΠJoinR₃.ΠJoinRBack (RP∞'∙ ℓ) (RP∞'∙ ℓ) A true true)
      → ΠR-extend→push (RP∞'∙ ℓ) true (RP∞'∙ ℓ) true A a
      ≡ ΠR-extend→push-bool A a
    ΠR-extend→push≡ A k a =
      (λ i → h i (RP∞'∙ ℓ) true A a) ∙ λ i → h2 i A a
      where
      h : ΠR-extend→push (RP∞'∙ ℓ) true ≡ ΠR-extend→push'
      h = JRP∞'∙ ΠR-extend→push'

      h2 : ΠR-extend→push' (RP∞'∙ ℓ) true ≡ ΠR-extend→push-bool
      h2 = JRP∞'∙ ΠR-extend→push-bool

  -- the map out of ΠR-extend₃
  ΠR-extend→ : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
    → (x : ΠJoinR₃.ΠR-extend₃ I J A) → Targ I J A x
  ΠR-extend→ I J A (inl (f , (j , a) , b)) = ΠR-extend→inl I f J j A a b
  ΠR-extend→ I J A (inr x) = ΠR-extend→inr I J A x
  ΠR-extend→ I J A (push (i , j , x) k) = ΠR-extend→push I i J j A x k

  -- In order to lift ΠR-extend→ to a map defined over all of
  -- UnordJoin²-alt, we will need to understand how to prove that
  -- ΠR-extend→ ≡ Gᵢ for some other family of maps Gᵢ indxed by i:I.
  module Coherence
    (G : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
          (x : ΠJoinR₃.ΠR-extend₃ I J A) (i : fst I) → Targ I J A x)
    (t : 𝕄₂ Targ (Targ (RP∞'∙ ℓ) (RP∞'∙ ℓ)) (λ _ _ → idEquiv _) G
             (λ A x a k → G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push x k) a) m)
    where
    open 𝕄₂ t
    G-inler-bool : (A : Bool → Bool → Type ℓ)
      (a : A true true) (f : (j : Bool) → A false j) (x : Bool)
      → G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (inl (true , (true , a) , f)) x
      ≡ ΠR-extend→inl (RP∞'∙ ℓ) true (RP∞'∙ ℓ) true A a f
    G-inler-bool A a f x = G-inler A a f x ∙ sym (ΠR-extend→inl≡ A a f)

    abstract
      G-inler' : (J : RP∞' ℓ) (j : fst J)
        (A : Bool → fst J → Type ℓ)
        (a : A true j) (f : (j : fst J) → A false j) (x : Bool)
        → G (RP∞'∙ ℓ) J A (inl (true , (j , a) , f)) x
         ≡ ΠR-extend→inl (RP∞'∙ ℓ) true J j A a f
      G-inler' = JRP∞' G-inler-bool

      G-inler* : (I : RP∞' ℓ) (i : fst I) (J : RP∞' ℓ)
        (j : fst J) (A : fst I → fst J → Type ℓ)
        (a : A i j) (f : (j : fst J) → A (RP∞'-fields.notRP∞' I i) j) (x : fst I)
        → G I J A (inl (i , (j , a) , f)) x ≡ ΠR-extend→inl I i J j A a f
      G-inler* = JRP∞' G-inler'

      G-inler*≡ : (A : Bool → Bool → Type ℓ)
        (a : A true true) (f : (j : Bool) → A false j) (x : Bool)
          → G-inler* (RP∞'∙ ℓ) true (RP∞'∙ ℓ) true A a f x
          ≡ G-inler-bool A a f x
      G-inler*≡ A a f x =
          (λ i → h1 i (RP∞'∙ ℓ) true A a f x)
        ∙ λ i → h2 i A a f x
        where
        h1 : G-inler* (RP∞'∙ ℓ) true ≡ G-inler'
        h1 = JRP∞'∙ G-inler'

        h2 : G-inler' (RP∞'∙ ℓ) true ≡ G-inler-bool
        h2 = JRP∞'∙ G-inler-bool

    G-inr-inl-inl*-type : (I : RP∞' ℓ) (J : RP∞' ℓ) (j : fst J)
      (A : fst I → fst J → Type ℓ)
      (f : (i : fst I) → A i j) (i : fst I)
      → Type ℓ
    G-inr-inl-inl*-type I J j A f i =
      Σ[ p1 ∈ G I J A (inr (inl (inl j , f))) i
            ≡ inr-inl-inl* I J j A f .fst ]
        ((g : (i : fst I) (j : fst J) → A i j)
         (p : (i : fst I) → g i j ≡ f i)
         → SquareP (λ k i → Targ I J A (inr (push ((inl j , f) , g , p) i)))
                     (λ k → G I J A (inr (push ((inl j , f) , g , p) k)) i)
                     (inr-inl-inl* I J j A f .snd g p)
                     p1
                     (G-inr-inr I J A g i))

    G-inr-inl-inl*-bool-diag-fill : (I : RP∞' ℓ)
      (A : fst I → Bool → Type ℓ)
      (f : (i : fst I) → A i true) (i : fst I)
      (g : _) (p : _) (j k r : _) → _
    G-inr-inl-inl*-bool-diag-fill I A f i g p j k r =
      hfill (λ r →
      λ {(k = i0) → compPath-filler
                     (G-inr-inl-inl₁ I A f i)
                     (λ i₁ → fst (inr-inl-inl*≡ I A f (~ i₁))) r j
       ; (k = i1) → G-inr-inr I (RP∞'∙ ℓ) A g i j
       ; (j = i0) → G I (RP∞'∙ ℓ) A (inr (push ((inl true , f) , g , p) k)) i
       ; (j = i1) → snd (inr-inl-inl*≡ I A f (~ r)) g p k})
      (inS (G-inr-inl-inl₂ I A f i g p j k))
      r

    G-inr-inl-inl*-bool : (I : RP∞' ℓ)
      (A : fst I → Bool → Type ℓ)
      (f : (i : fst I) → A i true) (i : fst I)
      → G-inr-inl-inl*-type I (RP∞'∙ ℓ) true A f i
    fst (G-inr-inl-inl*-bool I A f i) =
      G-inr-inl-inl₁ I A f i ∙ cong fst (sym (inr-inl-inl*≡ I A f))
    snd (G-inr-inl-inl*-bool I A f i) g p j k =
      G-inr-inl-inl*-bool-diag-fill I A f i g p j k i1

    abstract
      G-inr-inl-inl*-full : (I : RP∞' ℓ) (J : RP∞' ℓ) (j : fst J)
        (A : fst I → fst J → Type ℓ)
        (f : (i : fst I) → A i j) (i : fst I)
        → G-inr-inl-inl*-type I J j A f i
      G-inr-inl-inl*-full I = JRP∞' (G-inr-inl-inl*-bool I)

      G-inr-inl-inl*-full≡ : (I : RP∞' ℓ)
        (A : fst I → Bool → Type ℓ)
        (f : (i : fst I) → A i true) (i : fst I)
        → G-inr-inl-inl*-full I (RP∞'∙ ℓ) true A f i ≡ G-inr-inl-inl*-bool I A f i
      G-inr-inl-inl*-full≡ I A f i w = cool w A f i
        where
        cool : G-inr-inl-inl*-full I (RP∞'∙ ℓ) true ≡ G-inr-inl-inl*-bool I
        cool = JRP∞'∙ (G-inr-inl-inl*-bool I)

    G-inr-inl-inl*₁ : (I : RP∞' ℓ) (J : RP∞' ℓ) (j : fst J) (A : fst I → fst J → Type ℓ)
      → (f : (i : fst I) → A i j)
      → (i : fst I)
      → G I J A (inr (inl (inl j , f))) i ≡ inr-inl-inl* I J j A f .fst
    G-inr-inl-inl*₁ I = JRP∞' λ A f x
      → G-inr-inl-inl₁ I A f x ∙ cong fst (sym (inr-inl-inl*≡ I A f))

    G-inr-inl-inr*-type : (I J : RP∞' ℓ) (e : fst I ≃ fst J)
      (A : fst I → fst J → Type ℓ)
      (i : fst I)
      → Type ℓ
    G-inr-inl-inr*-type I J e A i =
      Σ[ p1 ∈ ((f : (i : fst I) → A i (fst e i))
              → G I J A (inr (inl (inr e , f))) i
               ≡ ΠR-extend→ I J A (inr (inl (inr e , f)))) ]
          ((f : (i₁ : fst I) → A i₁ (fst e i₁))
           (g : (i : fst I) (j : fst J) → A i j)
           (p : (i : fst I) → g i (fst e i) ≡ f i) →
       SquareP (λ k j → Targ I J A (inr (push ((inr e , f) , g , p) j)))
               (λ j → G I J A (inr (push ((inr e , f) , g , p) j)) i)
               (inr-inl-inr* I J e A f .snd g p)
               (p1 f)
               (G-inr-inr I J A g i))

    G-inr-inl-inr*-diag-fill : (I : RP∞' ℓ)
      (A : fst I → fst I → Type ℓ)
      (f : _) (g : _) (p : _)
      (i : fst I) (j k r : _)
      → _
    G-inr-inl-inr*-diag-fill I A f g p i j k r =
      hfill (λ r →
      λ {(k = i0) → compPath-filler
                     (G-inr-inl-inr₁ I A f i)
                     (λ i₁ → fst (inr-inl-inr*≡ I A f (~ i₁))) r j
       ; (k = i1) → G-inr-inr I I A g i j
       ; (j = i0) → G I I A (inr (push (((inr (idEquiv (fst I))) , f) , g , p) k)) i
       ; (j = i1) → snd (inr-inl-inr*≡ I A f (~ r)) g p k})
      (inS (G-inr-inl-inr₂ I A f g p i j k))
      r

    G-inr-inl-inr*-diag : (I : RP∞' ℓ)
      (A : fst I → fst I → Type ℓ)
      (i : fst I)
      → G-inr-inl-inr*-type I I (idEquiv (fst I)) A i
    fst (G-inr-inl-inr*-diag I A i) f =
        G-inr-inl-inr₁ I A f i
      ∙ cong fst (sym (inr-inl-inr*≡ I A f))
    snd (G-inr-inl-inr*-diag I A i) f g p j k =
      G-inr-inl-inr*-diag-fill I A f g p i j k i1

    abstract
      G-inr-inl-inr*-full : (I J : RP∞' ℓ) (e : fst I ≃ fst J)
        (A : fst I → fst J → Type ℓ)
        (i : fst I)
        → G-inr-inl-inr*-type I J e A i
      G-inr-inl-inr*-full I =
        EquivJRP∞' I (G-inr-inl-inr*-diag I)

      G-inr-inl-inr*≡ : (I : RP∞' ℓ)
        (A : fst I → fst I → Type ℓ)
        (i : fst I)
        → G-inr-inl-inr*-full I I (idEquiv _) A i ≡ G-inr-inl-inr*-diag I A i
      G-inr-inl-inr*≡ I A i k = help k A i
        where
        help : G-inr-inl-inr*-full I I (idEquiv _) ≡ G-inr-inl-inr*-diag I
        help = EquivJRP∞'-idEquiv I (G-inr-inl-inr*-diag I)

    GID-inr : (I : RP∞' ℓ) (i : fst I) (J : RP∞' ℓ)
      (A : fst I → fst J → Type ℓ) (x : _)
      → G I J A (inr x) i
      ≡ ΠR-extend→ I J A (inr x)
    GID-inr I i J A (inl (inl x , f)) = G-inr-inl-inl*-full I J x A f i .fst
    GID-inr I i J A (inl (inr e , f)) = G-inr-inl-inr*-full I J e A i .fst f
    GID-inr I i J A (inr x) = G-inr-inr I J A x i
    GID-inr I i J A (push ((inl x , f) , g , p) j) k =
      G-inr-inl-inl*-full I J x A f i .snd g p k j
    GID-inr I i J A (push ((inr x , f) , g , p) j) k =
      G-inr-inl-inr*-full I J x A i .snd f g p k j

    module _ (A : Bool → Bool → Type ℓ)
            (k : Bool)
            (x : _) where

      help-inr''-fill : (i j r : _) → _
      help-inr''-fill i j r =
        hfill (λ r →
        λ {(i = i0) → G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push (true , true , inr x) j) k
         ; (i = i1) → doubleWhiskFiller
                       (ΠR-extend→inl≡ A (x true true) (x false))
                       (push-inr A x) refl r j
         ; (j = i0) → compPath-filler
                         (G-inler A (x true true) (x false) k)
                         (sym (ΠR-extend→inl≡ A (x true true) (x false))) r i
         ; (j = i1) → G-inr-inr (RP∞'∙ ℓ) (RP∞'∙ ℓ) A x k i})
        (inS (G-push-inr A x k i j))
        r

      help-inr'' :
        SquareP
          (λ t s → Targ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push (true , true , inr x) s))
          (λ s → G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push (true , true , inr x) s) k)
          (ΠR-extend→inl≡ A (x true true) (x false)
            ◁ push-inr A x)
          (G-inler A (x true true) (x false) k
           ∙ sym (ΠR-extend→inl≡ A (x true true) (x false)))
          (G-inr-inr (RP∞'∙ ℓ) (RP∞'∙ ℓ) A x k)
      help-inr'' i j = help-inr''-fill i j i1

      help-inr'-fill : (i j r : _) → _
      help-inr'-fill i j r =
        hfill (λ r →
        λ {(i = i0) →  G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push (true , true , inr x) j) k
         ; (i = i1) → (ΠR-extend→inl≡ A (x true true) (x false) ◁ push-inr A x) j
         ; (j = i0) → G-inler*≡ A (x true true) (x false) k (~ r) i
         ; (j = i1) → G-inr-inr (RP∞'∙ ℓ) (RP∞'∙ ℓ) A x k i})
        (inS (help-inr'' i j))
        r

      help-inr' :
        SquareP
          (λ t s → Targ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push (true , true , inr x) s))
          (λ s → G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push (true , true , inr x) s) k)
          (ΠR-extend→inl≡ A (x true true) (x false) ◁ push-inr A x)
          (G-inler* (RP∞'∙ ℓ) true (RP∞'∙ ℓ) true A (x true true)
           (x false) k)
          (G-inr-inr (RP∞'∙ ℓ) (RP∞'∙ ℓ) A x k)
      help-inr' i j = help-inr'-fill i j i1

    module _ (A : Bool → Bool → Type ℓ)
            (k : Bool) (f : (i : Bool) → A i true) (g : (j : Bool) → A false j)
            (p : g true ≡ f false) where

      help-inl-inl-btm-fill : (i j r : _) → _
      help-inl-inl-btm-fill i j r =
        hfill (λ r → λ {(i = i0) → G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A
                                    (push (true , true , inl (inl (f , g , p))) j) k
                     ; (i = i1) → doubleWhiskFiller
                                    (ΠR-extend→inl≡ A (f true) g)
                                    (push-inl-inl A f g p)
                                    (sym (cong fst (inr-inl-inl*≡ (RP∞'∙ ℓ) A f))) r j
                     ; (j = i0) → compPath-filler
                                      (G-inler A (f true) g k)
                                      (sym (ΠR-extend→inl≡ A (f true) g)) r i
                     ; (j = i1) → compPath-filler
                                    (G-inr-inl-inl₁ (RP∞'∙ ℓ) A f k)
                                    (λ i₁ → fst (inr-inl-inl*≡ (RP∞'∙ ℓ) A f (~ i₁))) r i
                     })
              (inS (G-push-inl-inl A f g p k i j))
              r


      help-inl-inl :
             SquareP (λ t s → Targ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A
                                (push (true , true , inl (inl (f , g , p))) s))
                (λ s → G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A
                    (push (true , true , inl (inl (f , g , p))) s) k)
                (ΠR-extend→push-bool A (inl (inl (f , g , p))))
                (G-inler* (RP∞'∙ ℓ) true (RP∞'∙ ℓ) true A (f true) g k)
                (G-inr-inl-inl*-full (RP∞'∙ ℓ) (RP∞'∙ ℓ) true A f k .fst)
      help-inl-inl i j =
        hcomp (λ r → λ {(i = i0) → G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A
                                    (push (true , true , inl (inl (f , g , p))) j) k
                     ; (i = i1) → ΠR-extend→push-bool A (inl (inl (f , g , p))) j
                     ; (j = i0) → G-inler*≡ A (f true) g k (~ r) i
                     ; (j = i1) → G-inr-inl-inl*-full≡ (RP∞'∙ ℓ) A f k (~ r) .fst i})
         (help-inl-inl-btm-fill i j i1)

    help-inl-inr-type : (A : Bool → Bool → Type ℓ) (k : Bool)
      (e : Bool ≃ Bool) (pf : fst e true ≡ true)
        → Type ℓ
    help-inl-inr-type A k e pf =
      Σ[ h ∈ (
        (f : (i : Bool) → A i (fst e i))
        (g : (j : Bool) → A false j)
        (p : g (fst e false) ≡ f false)
        → SquareP (λ i j → Targ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A
                             (push (true , true , inl (inr (e , pf , f , g , p))) j))
                  (λ j → G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push (true , true , inl (inr (e , pf , f , g , p))) j) k)
                  (push-inr* A e pf .fst f g p)
                  (G-inler* (RP∞'∙ ℓ) true (RP∞'∙ ℓ) (fst e true) A (f true) g k)
                  (G-inr-inl-inr*-full (RP∞'∙ ℓ) (RP∞'∙ ℓ) e A k .fst f)
               ) ]
          ((g : (i j : Bool) → A i j)
          → (CubeP (λ j i l → Targ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A
                (push (true , true , push (inr (e , pf , g)) i) l))
                (λ i l → G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push (true , true , push (inr (e , pf , g)) i) l) k)
                (push-inr* A e pf .snd g) -- j = i1
                (h (λ i₁ → g i₁ (fst e i₁)) (g false) refl)
                (help-inr' A k g)
                (λ j i → G-inler* (RP∞'∙ ℓ) true (RP∞'∙ ℓ) (pf i) A (g true (pf i)) (g (RP∞'-fields.notRP∞' (RP∞'∙ ℓ) true)) k j)
                (G-inr-inl-inr*-full (RP∞'∙ ℓ) (RP∞'∙ ℓ) e A k .snd (λ i₁ → g i₁ (fst e i₁)) g (λ _ → refl))))

    help-inl-inr-id : (A : Bool → Bool → Type ℓ) (k : Bool)
      → help-inl-inr-type A k (idEquiv _) refl
    fst (help-inl-inr-id A k) f g p i j =
      hcomp (λ r → λ {(i = i0) → G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push (true , true , inl (inr (idEquiv Bool , refl , f , g , p))) j) k
                     ; (i = i1) → push-inr*≡ A (~ r) .fst f g p j
                     ; (j = i0) → G-inler*≡ A (f true) g k (~ r) i
                     ; (j = i1) → G-inr-inl-inr*≡ (RP∞'∙ ℓ) A k (~ r) .fst f i})
       (hcomp (λ r → λ {(i = i0) → G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push (true , true , inl (inr (idEquiv Bool , refl , f , g , p))) j) k
                     ; (i = i1) → doubleWhiskFiller
                                     (ΠR-extend→inl≡ A (f true) g)
                                     (push-inl-inr A f g p)
                                     (cong fst (sym (inr-inl-inr*≡ (RP∞'∙ ℓ) A f)))
                                     r j
                     ; (j = i0) → compPath-filler (G-inler A (f true) g k) (sym (ΠR-extend→inl≡ A (f true) g)) r i
                     ; (j = i1) → compPath-filler (G-inr-inl-inr₁ (RP∞'∙ ℓ) A f k)
                                    (λ i₁ → fst (inr-inl-inr*≡ (RP∞'∙ ℓ) A f (~ i₁)))
                                    r i})
              (G-push-inl-inr A f g p k i j))
    snd (help-inl-inr-id A k) g j i l =
      hcomp (λ r → λ {(i = i1) → help-inr'-fill A k g j l r
                     ; (j = i0) → G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push (true , true , push (inr (idEquiv Bool , refl , g)) i) l) k
                     ; (j = i1) → push-inr*≡ A (~ r) .snd g i l
                     ; (l = i0) → G-inler*≡ A (g true true) (g false) k (~ r) j
                     ; (l = i1) → G-inr-inl-inr*≡ (RP∞'∙ ℓ) A k (~ r) .snd (λ i → g i i) g (λ _ → refl) j i
                     })
       (hcomp (λ r → λ {(i = i1) → help-inr''-fill A k g j l r
                     ; (j = i0) → G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push (true , true , push (inr (idEquiv Bool , refl , g)) i) l) k
                     ; (j = i1) → push-inr*-bool-filler A g i l r
                     ; (l = i0) → compPath-filler (G-inler A (g true true) (g false) k)
                                                   (sym (ΠR-extend→inl≡ A (g true true) (g false))) r j
                     ; (l = i1) → G-inr-inl-inr*-diag-fill (RP∞'∙ ℓ) A (λ i → g i i) g (λ _ → refl) k j i r
                     })
             (G-push-push-inr A g k j i l))

    help-inl-inr : (A : Bool → Bool → Type ℓ) (k : Bool)
      (e : Bool ≃ Bool) (pf : fst e true ≡ true)
      → help-inl-inr-type A k e pf
    help-inl-inr A k = Bool≃Bool-elim-id _ (help-inl-inr-id A k)

    help' : (A : Bool → Bool → Type ℓ)
            (k : Bool)
            (a : ΠJoinR₃.ΠJoinRBack (RP∞'∙ ℓ) (RP∞'∙ ℓ) A true true)
         → SquareP (λ t s → Targ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push (true , true , a) s))
                    (λ s → G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push (true , true , a) s) k)
                    (ΠR-extend→push-bool A a)
                    (G-inler* (RP∞'∙ ℓ) true (RP∞'∙ ℓ)
                      (fst (fst (ΠJoinR₃.ΠJoinRBack→leftPush (RP∞'∙ ℓ) (RP∞'∙ ℓ) A true true a))) A
                      (snd (fst (ΠJoinR₃.ΠJoinRBack→leftPush (RP∞'∙ ℓ) (RP∞'∙ ℓ) A true true a)))
                      (snd (ΠJoinR₃.ΠJoinRBack→leftPush (RP∞'∙ ℓ) (RP∞'∙ ℓ) A true true a)) k)
                    (GID-inr (RP∞'∙ ℓ) k (RP∞'∙ ℓ) A
                      (ΠJoinR₃.ΠJoinRBack→ΠR-base (RP∞'∙ ℓ) (RP∞'∙ ℓ) A true true a))
    help' A k (inl (inl (f , g , p))) = help-inl-inl A k f g p
    help' A k (inl (inr (e , pf , f , g , p))) = help-inl-inr A k e pf .fst f g p
    help' A k (inr x) = help-inr' A k x
    help' A k (push (inl g) i) j l =
      hcomp (λ r → λ {(i = i1) → help-inr'-fill A k g j l r
                    ; (j = i0) → G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push (true , true , push (inl g) i) l) k
                    ; (j = i1) → push-inl-inl*-bool A g i l
                    ; (l = i0) → G-inler*≡ A (g true true) (g false) k (~ r) j
                    ; (l = i1) → G-inr-inl-inl*-full≡ (RP∞'∙ ℓ) A (λ i → g i true) k (~ r) .snd g (λ _ → refl) j i
                    })
            (hcomp (λ r → λ {
                    (i = i0) → help-inl-inl-btm-fill A k (λ i → g i true) (g false) refl j l r
                    ; (i = i1) → help-inr''-fill A k g j l r
                    ; (j = i0) → G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push (true , true , push (inl g) i) l) k
                    ; (l = i0) → help-inl-inl-btm-fill A k (λ i₁ → g i₁ true) (g false) (λ _ → g false true) j i0 r
                    ; (l = i1) → G-inr-inl-inl*-bool-diag-fill (RP∞'∙ ℓ) A (λ i → g i true) k g (λ _ → refl) j i r
                    })
              (G-push-push-inl A g k j i l))
    help' A k (push (inr (e , pf , g)) i) j l = help-inl-inr A k e pf .snd g j i l

    GID : (I : RP∞' ℓ) (i : fst I) (J : RP∞' ℓ)
      (A : fst I → fst J → Type ℓ) (x : _)
      → G I J A x i ≡ ΠR-extend→ I J A x
    GID I k J A (inl (i , (j , a) , f)) = G-inler* I i J j A a f k
    GID I k J A (inr x) = GID-inr I k J A x
    GID I k J A (push (i , j , a) s) t = lem I i J j A k a t s
      where
      lem : (I : RP∞' ℓ) (i : fst I) (J : RP∞' ℓ) (j : fst J)
             (A : fst I → fst J → Type ℓ)
             (k : fst I) (a : ΠJoinR₃.ΠJoinRBack I J A i j)
          → SquareP (λ t s → Targ I J A (push (i , j , a) s))
                     (λ s → G I J A (push (i , j , a) s) k)
                     (ΠR-extend→push I i J j A a)
                     (G-inler* I i J (fst (fst (ΠJoinR₃.ΠJoinRBack→leftPush I J A i j a))) A
                       (snd (fst (ΠJoinR₃.ΠJoinRBack→leftPush I J A i j a)))
                       (snd (ΠJoinR₃.ΠJoinRBack→leftPush I J A i j a)) k)
                     (GID-inr I k J A (ΠJoinR₃.ΠJoinRBack→ΠR-base I J A i j a))
      lem = JRP∞' (JRP∞' λ A k a → help' A k a ▷ sym (ΠR-extend→push≡ A k a))

ΠR-extend₃-elim-inst :
  (Targ : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) → ΠJoinR₃.ΠR-extend₃ I J A → Type ℓ)
  (Targ' : (A : Bool → Bool → Type ℓ) → ΠJoinR₃.ΠR-extend₃ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A → Type ℓ)
  (e : (A : Bool → Bool → Type ℓ) (x : ΠJoinR₃.ΠR-extend₃ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A)
    → Targ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A x ≃ Targ' A x)
  (G : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) → (x : ΠJoinR₃.ΠR-extend₃ I J A) → (i : fst I) → Targ I J A x)
  (pushG : (A : Bool → Bool → Type ℓ) (x : ΠJoinR₃.ΣΠJoinRBack (RP∞'∙ ℓ) (RP∞'∙ ℓ) A) (a : Bool)
    → PathP (λ i → Targ' A (push x i))
             (fst (e A _) (G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (inl (ΠJoinR₃.ΣΠJoinRBack→ₗ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A x)) a))
             (fst (e A _) (G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (inr (ΠJoinR₃.ΣΠJoinRBack→ᵣ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A x)) a)))
   (idpg : (λ A x a i → fst (e A _) (G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push x i) a)) ≡ pushG)
   (m : 𝕄 Targ Targ' e G pushG)
   (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
   → Σ[ f ∈ ((x : _) → Targ I J A x) ]
        ((i : fst I) (x : _) → G _ _ A x i ≡ f x)
ΠR-extend₃-elim-inst {ℓ = ℓ} Targ =
  EquivJ* (λ A → ΠJoinR₃.ΠR-extend₃ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A) λ G
    → J> λ m I J A → (ΠR-extend₃-elim.ΠR-extend→ Targ (fst m) I J A)
                     , (λ i → ΠR-extend₃-elim.Coherence.GID Targ (fst m) G (snd m) I i J A)
  where
  EquivJ* : ∀ {ℓ ℓ'}
    (C : (A : Bool → Bool → Type ℓ) → Type ℓ)
    {T1 : (A : Bool → Bool → Type ℓ) → C A → Type ℓ}
    {P : (T2 : (A : Bool → Bool → Type ℓ) → C A → Type ℓ)
      → ((A : Bool → Bool → Type ℓ) (c : C A) → T1 A c ≃ T2 A c) → Type ℓ'}
    → P T1 (λ A c → idEquiv _)
    → (T1 : _) (e : _) → P T1 e
  EquivJ* {ℓ = ℓ} C {T1 = T1} {P = P} q T2 e =
    subst (λ x → P (fst x) (snd x)) (isContr→isProp help (T1 , _) (T2 , e)) q
    where
    help : isContr (Σ[ T2 ∈ ((A : Bool → Bool → Type ℓ) → C A → Type ℓ) ]
                      ((A : _) (c : _) → T1 A c ≃ T2 A c))
    help = isOfHLevelRetractFromIso 0
            (Σ-cong-iso-snd (λ T1
              → compIso (codomainIsoDep
                (λ A → compIso (codomainIsoDep
                  (λ a → invIso (equivToIso univalence))) funExtIso)) funExtIso))
            (isContrSingl {A = (A : Bool → Bool → Type ℓ) → C A → Type ℓ} T1)

ΣBool→ : {A : Bool → Type ℓ} → Σ Bool A → A true × A false → Type ℓ
ΣBool→ (false , a) (b , c) = c ≡ a
ΣBool→ (true , a) (b , c) = b ≡ a

UnordJoinR-gen' : (A : Bool → Type ℓ) → Type ℓ
UnordJoinR-gen' A = PushoutR (Σ Bool A) (A true × A false) ΣBool→

UnordJoinR→ : (A : Bool → Type ℓ) →  UnordJoinR-gen Bool A → UnordJoinR-gen' A
UnordJoinR→ A (inlR x) = inlR x
UnordJoinR→ A (inrR x) = inrR (x true , x false)
UnordJoinR→ A (pushR (false , a) b x i) = pushR (false , a) (b true , b false) x i
UnordJoinR→ A (pushR (true , a) b x i) = pushR (true , a) (b true , b false) x i

UnordJoinRIso : (A : Bool → Type ℓ) → Iso (UnordJoinR-gen Bool A) (UnordJoinR-gen' A)
Iso.fun (UnordJoinRIso A) = UnordJoinR→ A
Iso.inv (UnordJoinRIso A) (inlR x) = inlR x
Iso.inv (UnordJoinRIso A) (inrR (a , b)) = inrR (CasesBool true a b)
Iso.inv (UnordJoinRIso A) (pushR (false , a) (b , c) x i) = pushR (false , a) (CasesBool true b c) x i
Iso.inv (UnordJoinRIso A) (pushR (true , a) (b , c) x i) = pushR (true , a) (CasesBool true b c) x i
Iso.rightInv (UnordJoinRIso A) (inlR x) = refl
Iso.rightInv (UnordJoinRIso A) (inrR x) = refl
Iso.rightInv (UnordJoinRIso A) (pushR (false , a) b x i) = refl
Iso.rightInv (UnordJoinRIso A) (pushR (true , a) b x i) = refl
Iso.leftInv (UnordJoinRIso A) (inlR x) = refl
Iso.leftInv (UnordJoinRIso A) (inrR x) = cong inrR (CasesBoolη x)
Iso.leftInv (UnordJoinRIso A) (pushR (false , a) f x i) j = pushR (false , a) (CasesBoolη f j) x i
Iso.leftInv (UnordJoinRIso A) (pushR (true , a) f x i) j = pushR (true , a) (CasesBoolη f j) x i

UnordJoinR'Funct : {A B : Bool → Type ℓ} → ((x : Bool) → A x → B x) → UnordJoinR-gen' A → UnordJoinR-gen' B
UnordJoinR'Funct f (inlR (i , x)) = inlR (i , f i x)
UnordJoinR'Funct f (inrR (a , b)) = inrR (f true a , f false b)
UnordJoinR'Funct f (pushR (false , a) (b , c) x i) = pushR (false , f false a) (f true b , f false c) (cong (f false) x) i
UnordJoinR'Funct f (pushR (true , a) (b , c) x i) = pushR (true , f true a) (f true b , f false c) (cong (f true) x) i

UnordJoinR'Funct'isEq : {A B : Bool → Type ℓ} → (e : (x : Bool) → A x ≃ B x)
  → section (UnordJoinR'Funct (fst ∘ e)) (UnordJoinR'Funct (invEq ∘ e))
  × retract (UnordJoinR'Funct (fst ∘ e)) (UnordJoinR'Funct (invEq ∘ e))
UnordJoinR'Funct'isEq {ℓ = ℓ} {A} {B} e = subst TYP (isContr→isProp help _ (B , e)) main
  where
  help : isContr (Σ[ B ∈ (Bool → Type ℓ) ] ((x : Bool) → A x ≃ B x))
  help = isOfHLevelRetractFromIso 0
           (Σ-cong-iso-snd (λ B → compIso (codomainIsoDep
             (λ b → equivToIso (invEquiv univalence))) funExtIso))
           (isContrSingl A)

  TYP : (Σ[ B ∈ (Bool → Type ℓ) ] ((x : Bool) → A x ≃ B x)) → Type ℓ
  TYP (B , e) = section (UnordJoinR'Funct (fst ∘ e)) (UnordJoinR'Funct (invEq ∘ e))
              × retract (UnordJoinR'Funct (fst ∘ e)) (UnordJoinR'Funct (invEq ∘ e))

  main : TYP (A , λ x → idEquiv (A x))
  fst main (inlR x) = refl
  fst main (inrR x) = refl
  fst main (pushR (false , a) b x i) = refl
  fst main (pushR (true , a) b x i) = refl
  snd main (inlR x) = refl
  snd main (inrR x) = refl
  snd main (pushR (false , a) b x i) = refl
  snd main (pushR (true , a) b x i) = refl

UnordJoinR'FunctIso : {A B : Bool → Type ℓ} (e : (x : Bool) → A x ≃ B x)
  → Iso (UnordJoinR-gen' A) (UnordJoinR-gen' B)
Iso.fun (UnordJoinR'FunctIso e) = UnordJoinR'Funct (fst ∘ e)
Iso.inv (UnordJoinR'FunctIso e) = UnordJoinR'Funct (invEq ∘ e)
Iso.rightInv (UnordJoinR'FunctIso e) = UnordJoinR'Funct'isEq e .fst
Iso.leftInv (UnordJoinR'FunctIso e) = UnordJoinR'Funct'isEq e .snd

UnordJoinRIso≃ : (A : Bool → Type ℓ) → UnordJoinR-gen Bool A ≃ UnordJoinR-gen' A
UnordJoinRIso≃ A = isoToEquiv (UnordJoinRIso A)

GOALTY : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) → Type ℓ
GOALTY I J A = UnordJoinR-gen (fst J) λ j → UnordJoinR-gen (fst I) λ i → A i j

GOALTY' : (A : Bool → Bool → Type ℓ) → Type ℓ
GOALTY' A = UnordJoinR-gen' λ a → UnordJoinR-gen' λ b → A b a

GOALTY≃ : (A : Bool → Bool → Type ℓ)
  → Iso (GOALTY (RP∞'∙ ℓ) (RP∞'∙ ℓ) A) (GOALTY' A)
GOALTY≃ A = compIso (UnordJoinRIso (λ y → UnordJoinR-gen Bool λ x → A x y))
                    (UnordJoinR'FunctIso λ y → isoToEquiv (UnordJoinRIso (λ x → A x y)))

GFUN : (A : Bool → Bool → Type ℓ)
  → GOALTY (RP∞'∙ ℓ) (RP∞'∙ ℓ) A → GOALTY' A
GFUN A = Iso.fun (GOALTY≃ A)

GFUNEq : (A : Bool → Bool → Type ℓ)
  → GOALTY (RP∞'∙ ℓ) (RP∞'∙ ℓ) A ≃ GOALTY' A
fst (GFUNEq A) = GFUN A
snd (GFUNEq A) = isoToIsEquiv (GOALTY≃ A)


module _ {ℓ} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) where
  ΣJoinR→JoinR² :  (Σ[ i ∈ fst I ] (UnordJoinR-gen (fst J) (A i)))
    → UnordJoinR-gen (fst J) λ j → UnordJoinR-gen (fst I) λ i → A i j
  ΣJoinR→JoinR² = uncurry λ i → UnordJoinR-funct λ j x → inlR (i , x)

inrerr : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
         (t : (i : fst I) (j : fst J) → A i j) → GOALTY I J A
inrerr I J A t = inrR λ j → inrR λ i → t i j

G-inr-inr* : (I₁ J₁ : RP∞' ℓ) (A : fst I₁ → fst J₁ → Type ℓ)
      (t : (i : fst I₁) (j : fst J₁) → A i j) (i : fst I₁) →
      inrR (λ j → inlR (i , t i j)) ≡ inrerr I₁ J₁ A t
G-inr-inr* I J A t i = cong inrR λ k j → pushR (i , t i j) (λ i → t i j) refl k

inr-inl-inl* : (I : RP∞' ℓ) (A : fst I → Bool → Type ℓ)
  (f : (x : fst I) → A x true)
  → Σ[ x ∈ GOALTY I (RP∞'∙ ℓ) A ]
      ((p : (i : fst I) (j : Bool) → A i j)
       (q : (i : fst I) → p i true ≡ f i)
      → x ≡ inrerr I (RP∞'∙ ℓ) A p)
fst (inr-inl-inl* I A f) = inlR (true , inrR f)
snd (inr-inl-inl* I A f) p q =
  pushR (true , inrR f) (λ i → inrR λ j → p j i) (cong inrR (funExt q))

G-inr-inl-inl*₁ : (I₁ : RP∞' ℓ) (A : fst I₁ → Bool → Type ℓ)
      (f : (x : fst I₁) → A x true) (i : fst I₁) →
      Path (GOALTY I₁ (RP∞'∙ ℓ) A) (inlR (true , inlR (i , f i))) (inlR (true , inrR f))
G-inr-inl-inl*₁ I A f i k = inlR (true , pushR (i , f i) f refl k)

G-inr-inl-inl*₂ : (I₁ : RP∞' ℓ) (A : fst I₁ → Bool → Type ℓ)
      (f : (x : fst I₁) → A x true) (i : fst I₁)
      (p : (i₁ : fst I₁) (j : Bool) → A i₁ j)
      (q : (x : fst I₁) → p x true ≡ f x) →
      Square {A = GOALTY I₁ (RP∞'∙ ℓ) A}
      (λ k → pushR (true , inlR (i , f i)) (λ j → inlR (i , p i j))
                    (λ t → inlR (i , q i t)) k)
      (pushR (true , inrR f) (λ j → inrR (λ i₁ → p i₁ j))
      (λ i₁ → inrR (funExt q i₁)))
      (G-inr-inl-inl*₁ I₁ A f i) (G-inr-inr* I₁ (RP∞'∙ ℓ) A p i)
G-inr-inl-inl*₂ I A f i p q k j =
  pushR (true , pushR (i , f i) f (λ _ → f i) k)
        (λ i₁ → pushR (i , p i i₁) (λ i₂ → p i₂ i₁) (λ _ → p i i₁) k)
        (λ t → pushR (i , q i t) (λ x → q x t) refl k) j

inr-inl-inr* : (I : RP∞' ℓ) (A : fst I → fst I → Type ℓ)
  (f : (x : fst I) → A x x)
  → Σ[ x ∈ GOALTY I I A ]
      ((p : (i j : fst I) → A i j)
       (q : (i : fst I) → p i i ≡ f i)
      → x ≡ inrerr I I A p)
fst (inr-inl-inr* I A f) = inrR λ i → inlR (i , (f i))
snd (inr-inl-inr* I A f) p q k = inrR (λ i → pushR (i , f i) (λ j → p j i) (q i) k)


G-inr-inl-inr*₁ : (I₁ : RP∞' ℓ) (A : fst I₁ → fst I₁ → Type ℓ)
      (f : (i : fst I₁) → A i i) (i : fst I₁) →
      Path (GOALTY I₁ I₁ A) (inlR (idfun (fst I₁) i , inlR (i , f i)))
                            (inrR (λ i₁ → inlR (i₁ , f i₁)))
G-inr-inl-inr*₁ I A f i = pushR (i , (inlR (i , f i))) (λ j → inlR (j , f j)) refl

module _ (I₁ : RP∞' ℓ) (A : fst I₁ → fst I₁ → Type ℓ)
      (p : (i₁ j : fst I₁) → A i₁ j) (i : fst I₁) where
  G-inr-inl-inr*₂-b-fill : (j k r : _) →  GOALTY I₁ I₁ A
  G-inr-inl-inr*₂-b-fill j k r =
    hfill (λ r → λ {(j = i0) → pushR (i , inlR (i , p i i))
                                        (λ s → pushR (i , p i s) (λ t → p t s) refl (~ r))
                                        (λ t → pushR (i , p i i) (λ t → p t i) refl (~ r ∧ ~ t)) k
                   ; (j = i1) → inrR (λ v → pushR (v , p v v) (λ a → p a v) (λ _ → p v v) (~ r ∨ k))
                   ; (k = i0) → pushR (i , inlR (i , p i i))
                                       (λ x → pushR (x , p x x) (λ a → p a x) refl (~ r))
                                       (λ j → pushR (i , p i i) (λ a → p a i) refl (~ r ∧ ~ j)) j
                   ; (k = i1) → inrR (λ v → pushR (i , p i v) (λ t → p t v) refl (~ r ∨ j))})
           (inS (pushR (i , inlR (i , p i i))
             (λ v → inrR (λ a → p a v))
             (sym (pushR (i , p i i) (λ a → p a i) refl))
             (j ∨ k)))
           r

  G-inr-inl-inr*₂-b :
    Square (λ k → pushR (i , inlR (i , p i i)) (λ v → inlR (i , p i v)) refl k)
            (λ k → inrR (λ i₁ → pushR (i₁ , p i₁ i₁) (λ j → p j i₁) refl k))
            (G-inr-inl-inr*₁ I₁ A (λ x → p x x) i)
            (G-inr-inr* I₁ I₁ A p i)
  G-inr-inl-inr*₂-b j k = G-inr-inl-inr*₂-b-fill j k i1

  G-inr-inl-inr*₂ :
        (f : (i : fst I₁) → A i i) (q : (λ x → p x x) ≡ f) →
        Square
        (λ k → pushR (i , inlR (i , f i)) (λ j → inlR (i , p i j))
                      (λ t → inlR (i , q t i)) k)
        (λ k → inrR (λ i₁ → pushR (i₁ , f i₁) (λ j → p j i₁) (funExt⁻ q i₁) k))
        (G-inr-inl-inr*₁ I₁ A f i)
        (G-inr-inr* I₁ I₁ A p i)
  G-inr-inl-inr*₂ = J> G-inr-inl-inr*₂-b

  G-inr-inl-inr*₂-refl : G-inr-inl-inr*₂ (λ x → p x x) refl ≡ G-inr-inl-inr*₂-b
  G-inr-inl-inr*₂-refl = transportRefl G-inr-inl-inr*₂-b

module Sol {ℓ : Level} (A : Bool → Bool → Type ℓ) where
  inler : A true true → ((t : Bool) → A false t) → GOALTY' A
  inler a b = inrR ((inrR (a , b true)) , (inlR (false , b false)))

  push-inl-inl :
      (f : (i : fst (RP∞'∙ ℓ)) → A i true)
      (g : (j : Bool) → A false j)
      (p : g true ≡ f false) →
      inler (f true) g ≡ GFUN A (inlR (true , inrR f))
  push-inl-inl f g p =
    sym (pushR (true , inrR (f true , f false))
               ((inrR (f true , g true)) , (inlR (false , g false)))
               λ k → inrR (f true , p k))

  push-inr : (g : (i j : Bool) → A i j) →
      inler (g true true) (g false) ≡
      GFUN A (inrerr (RP∞'∙ ℓ) (RP∞'∙ ℓ) A g)
  push-inr g i =
    inrR (inrR (g true true , g false true)
        , pushR (false , g false false)
                (g true false , g false false)
                refl i)

  push-inl-inr : (g : (i : Bool) → A i i)
      (f : (t : Bool) → A false t) (p : f false ≡ g false) →
      inler (g true) f ≡ GFUN A (inrR (λ i → inlR (i , g i)))
  push-inl-inr g f p i = inrR ((pushR (true , g true) (g true , f true) refl (~ i)) , (inlR (false , p i)))

  push-push-inr : (g : (i j : Bool) → A i j) →
      Square
      (push-inl-inr (λ i → g i i) (g false) refl) (push-inr g)
      (λ _ → inler (g true true) (g false))
      (λ i →
         GFUN A (inrR (λ i₁ → pushR (i₁ , g i₁ i₁) (λ j → g j i₁) refl i)))
  push-push-inr g i j = inrR ((pushR (true , g true true) (g true true , g false true) refl (i ∨ ~ j))
                      , (pushR (false , g false false) (g true false , g false false) refl (i ∧ j)))

  push-push-inl-fill : (g : (i j : Bool) → A i j) (i j k : _) → GOALTY' A
  push-push-inl-fill g i j k =
    hfill (λ k → λ {(i = i0) → pushR (true , inrR (g true true , g false true))
                                        (inrR (g true true , g false true) , inlR (false , g false false))
                                        (λ _ → inrR (g true true , g false true)) (k ∧ ~ j)
                   ; (i = i1) → pushR (true , inrR (g true true , g false true))
                                       (inrR (g true true , g false true)
                                           , pushR (false , g false false) (g true false , g false false) refl j)
                                       refl k
                   ; (j = i0) → pushR (true , inrR (g true true , g false true))
                                       (inrR (g true true , g false true) , inlR (false , g false false))
                                       (λ _ → inrR (g true true , g false true)) k
                   ; (j = i1) → pushR (true , inrR (g true true , g false true))
                                       (inrR (g true true , g false true) ,
                                        inrR (g true false , g false false)) refl (i ∧ k)})
          (inS (inlR (true , inrR (g true true , g false true))))
          k

  push-push-inl : (g : (i j : Bool) → A i j) →
      Square
      (push-inl-inl (λ i₁ → g i₁ true) (g false) (λ _ → g false true))
      (push-inr g)
      (λ _ → inler (g true true) (g false))
      (λ i →
         GFUN A (pushR (true , inrR (λ i₁ → g i₁ true))
          (λ j → inrR (λ i₁ → g i₁ j)) refl
          i))
  push-push-inl g i j = push-push-inl-fill g i j i1

  G-inler : (a : A true true)
      (b : (t : Bool) → A false t) (i : Bool) →
      GFUN A
      (ΣJoinR→JoinR² (RP∞'∙ ℓ) (RP∞'∙ ℓ) A
       (i , ΠΣ→ΠJoinR (RP∞'∙ ℓ) (RP∞'∙ ℓ) A true (true , a) b i))
      ≡ inler a b
  G-inler a b false i = inrR (pushR (false , b true) (a , b true) refl i , inlR (false , b false))
  G-inler a b true i =
    pushR (true , inlR (true , a))
          (inrR (a , b true) , inlR (false , b false))
          (sym (pushR (true , a) (a , b true) refl)) i

  module _ (f : (i : Bool) → A i true) (g : (j : Bool) → A false j) (p : g true ≡ f false) where
    G-push-inl-inl-filler : (i j k : _) → GOALTY' A
    G-push-inl-inl-filler i j k =
      hfill (λ k → λ {(j = i0) → pushR
                                     (true , inlR (true , f true))
                                     (inrR (f true , p (~ k)) , inlR (false , g false))
                                     (sym (pushR (true , f true) (f true , p (~ k)) refl)) i
                       ; (j = i1) → inlR (true , pushR (true , f true) (f true , f false) refl (i ∧ k))
                       ; (i = i0) → inlR (true , inlR (true , f true))
                       ; (i = i1) → pushR (true , pushR (true , f true) (f true , f false) refl k)
                                            (inrR (f true , p (~ k)) , inlR (false , g false))
                                            (λ i → pushR (true , f true) (f true , p (~ k ∨ i)) refl
                                            (k ∨ ~ i)) (~ j)})
              (inS (pushR (true , inlR (true , f true))
                     (inrR (f true , f false) , inlR (false , g false))
                     (sym (pushR (true , f true) (f true , f false) refl))
                     (i ∧ ~ j)))
              k
    G-push-inl-inl : (i : Bool) →
        Square (λ k → GFUN A (ΣJoinR→JoinR² (RP∞'∙ ℓ) (RP∞'∙ ℓ) A
                        (i , ΠR-extend₃→JoinR-Bool (RP∞'∙ ℓ) A i
                         (push (true , true , inl (inl (f , g , p))) k))))
        (push-inl-inl f g p)
        (G-inler (f true) g i)
        (λ k → GFUN A (G-inr-inl-inl*₁ (RP∞'∙ ℓ) A f i k))
    G-push-inl-inl false j k =
      pushR (true , pushR (false , f false) (f true , f false) refl j)
           ((pushR (false , g true) (f true , g true) refl j) , (inlR (false , g false)))
           (λ s → pushR (false , p s) (f true , p s) refl j) (~ k)
    G-push-inl-inl true i j = G-push-inl-inl-filler i j i1

  G-push-inr-t-fill : (g : (i j : Bool) → A i j) (i j k : _)
    → GOALTY' A
  G-push-inr-t-fill g i j k =
    hfill (λ k → λ {(j = i0) → pushR (true , inlR (true , g true true))
                                       (inrR (g true true , g false true) , inlR (false , g false false))
                                       (sym (pushR (true , g true true) (g true true , g false true) refl))
                                       (i ∧ k)
                   ; (j = i1) → pushR (true , inlR (true , g true true))
                                        ((pushR (true , g true true) (g true true , g false true) refl i)
                                       , (pushR (true , g true false) (g true false , g false false) refl i))
                                       (λ s → pushR (true , g true true) (g true true , g false true) refl (~ s ∧ i)) k
                   ; (i = i0) → pushR (true , inlR (true , g true true))
                                        (inlR (true , g true true) , inlR (true , g true false))
                                        (λ i₁ → inlR (true , g true true)) (j ∧ k)
                   ; (i = i1) → pushR (true , inlR (true , g true true)) (inrR (g true true , g false true)
                                           , pushR (false , g false false) (g true false , g false false) refl j)
                                           (sym (pushR (true , g true true) (g true true , g false true) refl)) k})
           (inS (inlR (true , inlR (true , g true true))))
           k

  G-push-inr : (g : (i j : Bool) → A i j)
      (i : Bool) →
      Square
      (λ j → GFUN A (ΣJoinR→JoinR² (RP∞'∙ ℓ) (RP∞'∙ ℓ) A
               (i , ΠR-extend₃→JoinR-Bool (RP∞'∙ ℓ) A i (push (true , true , inr g) j))))
      (push-inr g)
      (G-inler (g true true) (g false) i)
      λ k → GFUN A (G-inr-inr* (RP∞'∙ ℓ) (RP∞'∙ ℓ) A g i k)
  G-push-inr g false i j =
    inrR ((pushR (false , g false true) (g true true , g false true) refl i)
        , (pushR (false , g false false) (g true false , g false false) refl (i ∧ j)))
  G-push-inr g true i j = G-push-inr-t-fill g i j i1

  G-push-inl-inr-fill : (g : (i : Bool) → A i i)
        (f : (t : Bool) → A false t) (p : f false ≡ g false)
     → (i j k : _) → GOALTY' A
  G-push-inl-inr-fill g f p i j k =
    hfill (λ k → λ {(i = i0) → pushR (false , inlR (false , g false))
                                       (inlR (false , f true) , inlR (false , f false))
                                       (λ i₁ → inlR (false , p i₁)) (~ j ∧ k)
                   ; (i = i1) → pushR (false , inlR (false , g false))
                                       (pushR (true , g true) (g true , f true) refl (~ j)
                                       , inlR (false , p j))
                                       (λ i → inlR (false , p (i ∨ j))) k
                   ; (j = i0) → pushR (false , inlR (false , g false))
                                       (pushR (false , f true) (g true , f true) refl i , inlR (false , f false))
                                       (λ i → inlR (false , p i)) k
                   ; (j = i1) → pushR (false , inlR (false , g false))
                                       (inlR (true , g true) , inlR (false , g false))
                                       (λ i₁ → inlR (false , g false)) (i ∧ k)})
          (inS (inlR (false , inlR (false , g false))))
          k

  G-push-inl-inr : (g : (i : Bool) → A i i)
        (f : (t : Bool) → A false t) (p : f false ≡ g false) (x : Bool) →
        Square
        (λ j → GFUN A
           (ΣJoinR→JoinR² (RP∞'∙ ℓ) (RP∞'∙ ℓ) A
            (x , ΠR-extend₃→JoinR-Bool (RP∞'∙ ℓ) A x (push (true , true , inl (inr (idEquiv Bool , refl , g , f , p))) j))))
        (push-inl-inr g f p)
        (G-inler (g true) f x)
        (λ t → GFUN A (G-inr-inl-inr*₁ (RP∞'∙ ℓ) A g x t))
  G-push-inl-inr g f p false i j = G-push-inl-inr-fill g f p i j i1
  G-push-inl-inr g f p true i j =
    pushR (true , inlR (true , g true))
          (pushR (true , g true) (g true , f true) refl (~ j) , inlR (false , p j))
          (λ k → pushR (true , g true) (g true , f true) refl (~ j ∧ ~ k)) i

  G-push-push-inr-main :  (g : (i j : Bool) → A i j)
      (x : Bool) →
      Cube
      (λ i _ → G-inler (g true true) (g false) x i)
      (λ s t →
         GFUN A
         (G-inr-inl-inr*₂-b (RP∞'∙ ℓ) A g x s t))
      (λ i j → GFUN A
         (ΣJoinR→JoinR² (RP∞'∙ ℓ) (RP∞'∙ ℓ) A
          (x , ΠR-extend₃→JoinR-Bool (RP∞'∙ ℓ) A x
           (push (true , true , push (inr (idEquiv Bool , refl , g)) j) i)))) -- ()
      (λ i j → push-push-inr g j i) -- (G-push-inr g x)
      (λ i j → G-push-inl-inr (λ i → g i i) (g false) refl x j i)
      λ i j → G-push-inr g x j i
  G-push-push-inr-main g false k i j =
    hcomp (λ r →
    λ {(i = i0)
    → pushR (false , inlR (false , g false false))
             (inlR (false , g false true) , inlR (false , g false false))
             (λ i₁ → inlR (false , g false false)) ((~ k ∨ j) ∧ r)
     ; (i = i1) →
     pushR (false , inlR (false , g false false))
          ((pushR (true , g true true) (g true true , g false true) refl (j ∨ ~ k))
         , (pushR (false , g false false) (g true false , g false false) refl (j ∧ k)))
          (λ s → pushR (false , g false false) (g true false , g false false) refl (j ∧ k ∧ ~ s)) r
     ; (j = i0) → G-push-inl-inr-fill (λ i → g i i) (g false) refl i k r
     ; (j = i1) →
     pushR (false , inlR (false , g false false))
           ((pushR (false , g false true) (g true true , g false true) refl i)
          , (pushR (false , g false false) (g true false , g false false) refl (i ∧ k)))
           (λ s → pushR (false , g false false) (g true false , g false false) refl (i ∧ k ∧ ~ s)) r
     ; (k = i0) →
     pushR (false , inlR (false , g false false))
           ((pushR (false , g false true) (g true true , g false true) refl i)
          , (inlR (false , g false false)))
           refl r
     ; (k = i1) → h r i j
                   })
            (inlR (false , inlR (false , g false false)))
    where
    hah : {A : Type ℓ} {x : A} (y : A) (p : x ≡ y)
      → Cube (λ k j → p (~ k ∨ j)) (λ _ _ → x)
              (λ s j → p (~ s)) (λ s j → p (j ∧ ~ s))
              (λ s k → p (~ s ∧ ~ k)) λ i _ → p (~ i)
    hah = J> refl

    h : Cube (λ _ _ → inlR (false , inlR (false , g false false)))
             (λ i j → GFUN A (G-inr-inl-inr*₂-b-fill (RP∞'∙ ℓ) A g false i j i1))
             (λ r j → pushR (false , inlR (false , g false false))
                             (inlR (false , g false true) , inlR (false , g false false))
                             refl (j ∧ r))
             (λ r j → pushR (false , inlR (false , g false false))
                             (pushR (true , g true true) (g true true , g false true) refl j
                            , pushR (false , g false false) (g true false , g false false) refl j)
                            (λ s →  pushR (false , g false false) (g true false , g false false) refl (j ∧ ~ s))
                            r)
             (λ r i → G-push-inl-inr-fill (λ i₁ → g i₁ i₁) (g false) refl i i1 r)
             λ r i → pushR (false , inlR (false , g false false))
                            (pushR (false , g false true) (g true true , g false true) refl i
                           , pushR (false , g false false) (g true false , g false false) refl i)
                            (λ s →  pushR (false , g false false) (g true false , g false false) refl (i ∧ ~ s))
                            r
    h r i j =
        hcomp (λ k → λ {(i = i0) → pushR (false , inlR (false , g false false))
                                          ((pushR (false , g false true) (g true true , g false true) refl (~ k))
                                         , (pushR (false , g false false) (g true false , g false false) refl (~ k)))
                                          (λ s → pushR (false , g false false) (g true false , g false false) refl (~ k ∧ ~ s)) (r ∧ j)
                   ; (i = i1) → pushR (false , inlR (false , g false false))
                                       ((pushR (true , g true true) (g true true , g false true) refl (~ k ∨ j))
                                      , (pushR (false , g false false) (g true false , g false false) refl (~ k ∨ j)))
                                       (λ s → hah _ (pushR (false , g false false) (g true false , g false false) refl) s k j) r
                   ; (j = i0) → pushR (false , inlR (false , g false false))
                                       ((pushR (true , g true true) (g true true , g false true) refl (~ k))
                                       , (pushR (false , g false false) (g true false , g false false) refl (~ k)))
                                       (λ t → pushR (false , g false false) (g true false , g false false) refl (~ k ∧ ~ t)) (i ∧ r)
                   ; (j = i1) → pushR (false , inlR (false , g false false))
                                       ((pushR (false , g false true) (g true true , g false true) refl (~ k ∨ i))
                                       , (pushR (false , g false false) (g true false , g false false) refl (~ k ∨ i)))
                                       (λ s → hah _ (pushR (false , g false false) (g true false , g false false) refl) s k i) r
                   ; (r = i0) → inlR (false , inlR (false , g false false))
                   ; (r = i1) → GFUN A (G-inr-inl-inr*₂-b-fill (RP∞'∙ ℓ) A g false i j k)
                   })
           (pushR (false , inlR (false , g false false))
          (inrR (g true true , g false true) ,
           inrR (g true false , g false false))
          (sym (pushR (false , g false false) (g true false , g false false) refl))
          ((i ∨ j) ∧ r))
  G-push-push-inr-main g true k i j =
    hcomp (λ r → λ {(i = i0) → GFUN A (ΣJoinR→JoinR² (RP∞'∙ ℓ) (RP∞'∙ ℓ) A
                                  (true , ΠR-extend₃→JoinR-pushₗ-fill (RP∞'∙ _) (RP∞'∙ _) A true true (idEquiv Bool) refl g j k r))
                   ; (i = i1) → inrR ((pushR (true , g true true) (g true true , g false true) refl (j ∨ ~ k)
                               , pushR (false , g false false) (g true false , g false false) refl (j ∧ k)))
                   ; (j = i0) → pushR (true , inlR (true , g true true))
                                        (pushR (true , g true true) (g true true , g false true) refl (~ k)
                                        , inlR (false , g false false))
                                       (λ s → pushR (true , g true true) (g true true , g false true)
                                          (λ _ → g true true) (~ k ∧ ~ s)) i
                   ; (j = i1) → cong-GFUN r i k
                   ; (k = i0) → pushR (true , inlR (true , g true true))
                                       (inrR (g true true , g false true) , inlR (false , g false false))
                                       (sym (pushR (true , g true true) (g true true , g false true) refl)) i
                   ; (k = i1) → GFUN A (G-inr-inl-inr*₂-b-fill (RP∞'∙ ℓ) A g true i j i1)
                   })
       (hcomp (λ r → λ {(i = i0) → pushR (true , inlR (true , g true true))
                                            (inlR (true , g true true) , inlR (true , g true false))
                                            (λ i₁ → inlR (true , g true true)) (j ∧ (k ∧ r))
                   ; (i = i1) → pushR (true , inlR (true , g true true))
                                       ((pushR (true , g true true) (g true true , g false true)
                                               refl (j ∨ ~ k))
                                      , (pushR (false , g false false) (g true false , g false false) refl (j ∧ k)))
                                       (λ s → pushR (true , g true true) (g true true , g false true)
                                                     refl ((~ k ∨ j) ∧ (~ s))) r
                   ; (j = i0) → pushR (true , inlR (true , g true true))
                                       (pushR (true , g true true) (g true true , g false true)
                                        refl (~ k)
                                        , inlR (false , g false false))
                                       (λ s → pushR (true , g true true) (g true true , g false true)
                                                     refl (~ k ∧ ~ s))
                                       (i ∧ r)
                   ; (j = i1) → G-push-inr-t-fill g i k r
                   ; (k = i0) → pushR (true , inlR (true , g true true))
                                       (inrR (g true true , g false true) , inlR (false , g false false))
                                       (sym (pushR (true , g true true) (g true true , g false true) refl))
                                       (i ∧ r)
                   ; (k = i1) → F2 r i j
                   })
              (inlR (true , inlR (true , g true true))))
    where -- r i j
    F2 : Cube (λ _ _ → inlR (true , inlR (true , g true true)))
              (λ i j → GFUN A (G-inr-inl-inr*₂-b-fill (RP∞'∙ ℓ) A g true i j i1))
              (λ r j → pushR (true , inlR (true , g true true))
                              (inlR (true , g true true) , inlR (true , g true false))
                              refl (j ∧ r))
              (λ r j → pushR (true , inlR (true , g true true))
                              (pushR (true , g true true) (g true true , g false true) refl j
                             , pushR (false , g false false) (g true false , g false false) refl j)
                              (λ s → pushR (true , g true true) (g true true , g false true) refl (j ∧ ~ s)) r)
              (λ r i → pushR (true , inlR (true , g true true))
                              (inlR (true , g true true) , inlR (false , g false false))
                              refl (i ∧ r))
              λ r i → G-push-inr-t-fill g i i1 r
    F2 r i j =
      hcomp (λ k → λ {(i = i0) → pushR (true , inlR (true , g true true))
                                          (pushR (true , g true true) (g true true , g false true) refl (~ k)
                                        , pushR (true , g true false) (g true false , g false false) refl (~ k))
                                          (λ i₂ → pushR (true , g true true)
                                                         (g true true , g false true) refl (~ k ∧ ~ i₂)) (r ∧ j)
                   ; (i = i1) →  pushR (true , inlR (true , g true true))
                                        ((pushR (true , g true true) (g true true , g false true) refl (~ k ∨ j))
                                       , (pushR (false , g false false) (g true false , g false false) refl (~ k ∨ j)))
                                        (λ t → pushR (true , g true true) (g true true , g false true) refl ((j ∨ ~ k) ∧ (~ t))) r
                   ; (j = i0) → pushR (true , inlR (true , g true true))
                                       ((pushR (true , g true true) (g true true , g false true) refl (~ k))
                                       , (pushR (false , g false false) (g true false , g false false) refl (~ k)))
                                       (λ i → pushR (true , g true true) (g true true , g false true) refl (~ i ∧ ~ k))
                                       (r ∧ i)
                   ; (j = i1) → pushR (true , inlR (true , g true true))
                                       ((pushR (true , g true true) (g true true , g false true) refl (~ k ∨ i))
                                     , (pushR (true , g true false) (g true false , g false false) refl (~ k ∨ i)))
                                       (λ t → pushR (true , g true true) (g true true , g false true) refl (~ t ∧ (i ∨ ~ k))) r
                   ; (r = i0) → inlR (true , inlR (true , g true true))
                   ; (r = i1) → GFUN A (G-inr-inl-inr*₂-b-fill (RP∞'∙ ℓ) A g true i j k)
                   })
                  (pushR (true , inlR (true , g true true))
                         (inrR (g true true , g false true)
                        , inrR (g true false , g false false))
                         (sym (pushR (true , g true true) (g true true , g false true) refl))
                         (r ∧ (i ∨ j)))

    cong-GFUN : Cube (λ i k → G-push-inr-t-fill g i k i1)
                     (λ i k → G-push-inr-t-fill g i k i1)
                     (λ r k → pushR (true , inlR (true , g true true))
                                      (inlR (true , g true true) , inlR (true , g true false))
                                      refl k)
                     (λ r k → inrR (inrR (g true true , g false true)
                             , pushR (false , g false false) (g true false , g false false) refl k))
                     (λ r i → pushR (true , inlR (true , g true true))
                                       (inrR (g true true , g false true) , inlR (false , g false false))
                                       (sym (pushR (true , g true true) (g true true , g false true) refl)) i)
                     λ r i → inrR (pushR (true , g true true) (g true true , g false true) refl i
                            , pushR (true , g true false) (g true false , g false false) refl i)
    cong-GFUN r i k =
      hcomp (λ j → λ {(r = i0) → G-push-inr-t-fill g i k j
                   ; (r = i1) → G-push-inr-t-fill g i k j
                   ; (i = i0) → G-push-inr-t-fill g i k j
                   ; (i = i1) → G-push-inr-t-fill g i k j
                   ; (k = i0) → G-push-inr-t-fill g i k j
                   ; (k = i1) → G-push-inr-t-fill g i k j
                   })
              (inlR (true , inlR (true , g true true)))

  G-push-push-inr : (g : (i j : Bool) → A i j)
      (x : Bool) →
      Cube
      (λ i _ → G-inler (g true true) (g false) x i)
      (λ s t →
         GFUN A
         (G-inr-inl-inr*₂ (RP∞'∙ ℓ) A g x (λ i → g i i) refl s t))
      (λ i j → GFUN A
         (ΣJoinR→JoinR² (RP∞'∙ ℓ) (RP∞'∙ ℓ) A
          (x , ΠR-extend₃→JoinR-Bool (RP∞'∙ ℓ) A x
           (push (true , true , push (inr (idEquiv Bool , refl , g)) j) i)))) -- ()
      (λ i j → push-push-inr g j i) -- (G-push-inr g x)
      (λ i j → G-push-inl-inr (λ i → g i i) (g false) refl x j i)
      λ i j → G-push-inr g x j i
  G-push-push-inr g x =
    G-push-push-inr-main g x
    ▷ λ a s t → GFUN A (G-inr-inl-inr*₂-refl (RP∞'∙ ℓ) A g x (~ a) s t)

  G-push-push-inl : (g : (i j : Bool) → A i j) (x : Bool) →
      Cube
      (λ i j → GFUN A
         (ΣJoinR→JoinR² (RP∞'∙ ℓ) (RP∞'∙ ℓ) A
           (x , ΠR-extend₃→JoinR-Bool (RP∞'∙ ℓ) A x (push (true , true , push (inl g) i) j))))
      (push-push-inl g)
      (G-push-inl-inl (λ i → g i true) (g false) refl x)
      (G-push-inr g x)
      (λ i _ → G-inler (g true true) (g false) x i)
      (λ s t → GFUN A (G-inr-inl-inl*₂ (RP∞'∙ ℓ) A (λ i → g i true) x g (λ z → refl) s t))
  G-push-push-inl g false i j k =
    hcomp (λ r → λ {(i = i0) → f _ (pushR
                                      (true , inlR (false , g (RP∞'-fields.notRP∞' (RP∞'∙ ℓ) true) true))
                                      (inlR (false , g (RP∞'-fields.notRP∞' (RP∞'∙ ℓ) true) true) ,
                                       inlR (false , g (RP∞'-fields.notRP∞' (RP∞'∙ ℓ) true) false)) refl) r j k
                   ; (j = i0) → pushR (true , pushR (false , g false true) (g true true , g false true) refl i)
                                       ((pushR (false , g false true) (g true true , g false true) refl i)
                                      , (inlR (false , g false false)))
                                       refl (r ∧ ~ k)
                   ; (j = i1) → pushR (true , pushR (false , g false true) (g true true , g false true) refl i)
                                       ((pushR (false , g false true) (g true true , g false true) refl i)
                                      , (pushR (false , g false false) (g true false , g false false) refl(i ∧ k)))
                                       refl r
                   ; (k = i0) → pushR (true , (pushR (false , g false true) (g true true , g false true) refl i))
                                      ((pushR (false , g false true) (g true true , g false true) refl i)
                                     , (inlR (false , g false false)))
                                      refl r
                   ; (k = i1) → pushR (true , pushR (false , g false true) (g true true , g false true) refl i)
                                       ((pushR (false , g false true) (g true true , g false true) refl i)
                                      , (pushR (false , g false false) (g true false , g false false) refl i))
                                       refl (j ∧ r)})
          (inlR (true , pushR (false , g false true) (g true true , g false true) refl i))
    where
    f : {A : Type ℓ} {x : A} (y : A) (p : x ≡ y) -- r j k
      → Cube refl (λ j k → p (j ∨ ~ k))
             (λ r k → p (r ∧ ~ k)) (λ r k → p r)
             (λ r j → p r) (λ r j → p (j ∧ r))
    f = J> refl
  G-push-push-inl g true i j k =
    hcomp (λ r → λ {(i = i0) → pushR (true , inlR (true , g true true))
                                       (inlR (true , g true true) , inlR (true , g true false))
                                       refl (j ∧ k)
                   ; (i = i1) → s1 r j k
                   ; (j = i0) → G-push-inl-inl-filler (λ k → g k true) (g false) refl i k r
                   ; (j = i1) → G-push-inr-t-fill g i k i1
                   ; (k = i0) → pushR (true , inlR (true , g true true))
                                       (inrR (g true true , g false true) , inlR (false , g false false))
                                       (sym (pushR (true , g true true) (g true true , g false true) refl)) i
                   ; (k = i1) → pushR (true , pushR (true , g true true) (g true true , g false true) refl (i ∧ r))
                                       ((pushR (true , g true true) (g true true , g false true) refl i)
                                      , (pushR (true , g true false) (g true false , g false false) refl i))
                                      (λ k →  pushR (true , g true true) (g true true , g false true) refl (i ∧ (r ∨ ~ k))) j
                   })
     (hcomp (λ r → λ {(i = i0) → pushR (true , inlR (true , g true true))
                                         (inlR (true , g true true) , inlR (true , g true false))
                                          refl (j ∧ k ∧ r)
                   ; (i = i1) → SQ-f j k r
                   ; (j = i0) → pushR (true , inlR (true , g true true))
                                        (inrR (g true true , g false true) , inlR (false , g false false))
                                        (sym (pushR (true , g true true) (g true true , g false true) refl))
                                        (i ∧ ~ k ∧ r)
                   ; (j = i1) → G-push-inr-t-fill g i k r
                   ; (k = i0) → pushR (true , inlR (true , g true true))
                                       ((inrR (g true true , g false true))
                                      , (inlR (false , g false false)))
                                       (sym (pushR (true , g true true)
                                                   (g true true , g false true)
                                                   refl)) (i ∧ r)
                   ; (k = i1) → pushR (true , inlR (true , g true true))
                                       ((pushR (true , g true true) (g true true , g false true) refl i)
                                       , (pushR (true , g true false) (g true false , g false false) refl i))
                                       (λ s → pushR (true , g true true) (g true true , g false true) refl (i ∧ ~ s)) (r ∧ j)
                   })
            (inlR (true , inlR (true , g true true))))
    where
    SQ-f : (j k r : _) → GOALTY' A
    SQ-f j k r =
      hfill (λ r → λ {(j = i0) → pushR (true , inlR (true , g true true))
                                                 (inrR (g true true , g false true) , inlR (false , g false false))
                                                 (sym (pushR (true , g true true) (g true true , g false true) refl))
                                                 (~ k ∧ r)
                     ; (j = i1) → pushR (true , (inlR (true , g true true)))
                                         (inrR (g true true , g false true)
                                        , pushR (false , g false false) (g true false , g false false) refl k)
                                        (sym (pushR (true , g true true) (g true true , g false true) refl)) r
                     ; (k = i0) → pushR (true , inlR (true , g true true))
                                          (inrR (g true true , g false true) , inlR (false , g false false))
                                          (sym (pushR (true , g true true) (g true true , g false true) refl))
                                          r
                     ; (k = i1) → pushR (true , inlR (true , g true true))
                                         (inrR (g true true , g false true) , inrR (g true false , g false false))
                                         (sym (pushR (true , g true true) (g true true , g false true) refl)) (j ∧ r)})
            (inS (inlR (true , inlR (true , g true true))))
            r

    SQ : Square _ _ _ _
    SQ j k = SQ-f j k i1

    s1 : Cube SQ
              (λ j k → push-push-inl-fill g j k i1)
              (λ r k → G-push-inl-inl-filler (λ k → g k true) (g false) refl i1 k r)
              (λ r k → G-push-inr-t-fill g i1 k i1)
              (λ r j → inrR (inrR (g true true , g false true) , inlR (false , g false false)))
              (λ r j → pushR (true , pushR (true , g true true) (g true true , g false true) refl r)
                              (inrR (g true true , g false true) , inrR (g true false , g false false))
                              (λ k → pushR (true , g true true) (g true true , g false true) refl (r ∨ ~ k)) j)
    s1 r j k =
      hcomp (λ i →
        λ {(j = i0) → pushR (true , pushR (true , g true true) (g true true , g false true) refl r)
                            (inrR (g true true , g false true) , inlR (false , g false false))
                            (λ s → pushR (true , g true true) (g true true , g false true) refl (~ s ∨ r))
                            (~ k ∧ i)
         ; (j = i1) → pushR (true , pushR (true , g true true) (g true true , g false true) refl r)
                             ((inrR (g true true , g false true))
                             , (pushR (false , g false false) (g true false , g false false) refl k))
                             (λ j → pushR (true , g true true) (g true true , g false true) refl (r ∨ ~ j)) i
         ; (k = i0) → pushR (true , pushR (true , g true true) (g true true , g false true) refl r)
                             ((inrR (g true true , g false true))
                             , (inlR (false , g false false)))
                             (λ s → pushR (true , g true true) (g true true , g false true) refl (r ∨ ~ s)) i
         ; (k = i1) → pushR (true , pushR (true , g true true) (g true true , g false true) refl r)
                             ((inrR (g true true , g false true)) , (inrR (g true false , g false false)))
                             (λ k → pushR (true , g true true) (g true true , g false true) refl (r ∨ ~ k)) (j ∧ i)})
        (inlR (true , pushR (true , g true true) (g true true , g false true) refl r))

𝕄inst₁ : Type (ℓ-suc ℓ)
𝕄inst₁ = 𝕄₁ (λ I J A _ → GOALTY I J A) (λ A _ → GOALTY' A) (λ A _ → GFUNEq A)

open 𝕄₁
open 𝕄₂

𝕄inst₁· : 𝕄₁ {ℓ = ℓ} (λ I J A _ → GOALTY I J A) (λ A _ → GOALTY' A) (λ A _ → GFUNEq A)
inler 𝕄inst₁· = Sol.inler
inr-inr 𝕄inst₁· = inrerr
inr-inl-inl 𝕄inst₁· = inr-inl-inl*
inr-inl-inr 𝕄inst₁· = inr-inl-inr*
push-inl-inl 𝕄inst₁· = Sol.push-inl-inl
push-inr 𝕄inst₁· = Sol.push-inr
push-inl-inr 𝕄inst₁· = Sol.push-inl-inr
push-push-inr 𝕄inst₁· = Sol.push-push-inr
push-push-inl 𝕄inst₁· = Sol.push-push-inl

𝕄inst₂· : 𝕄₂ (λ I J A _ → GOALTY I J A) (λ A _ → GOALTY' A) (λ A _ → GFUNEq A)
  (λ I J A x i → ΣJoinR→JoinR² I J A (i , ΠR-extend₃→JoinR I J A i x))
  (λ A x a j → GFUN A (ΣJoinR→JoinR² (RP∞'∙ ℓ) (RP∞'∙ ℓ) A
                 (a , ΠR-extend₃→JoinR-Bool (RP∞'∙ ℓ) A a (push x j))))
  𝕄inst₁·
G-inler 𝕄inst₂· = Sol.G-inler
G-inr-inr 𝕄inst₂· = G-inr-inr*
G-inr-inl-inl₁ 𝕄inst₂· = G-inr-inl-inl*₁
G-inr-inl-inl₂ 𝕄inst₂· = G-inr-inl-inl*₂
G-inr-inl-inr₁ 𝕄inst₂· = G-inr-inl-inr*₁
G-inr-inl-inr₂ 𝕄inst₂· I A f p q i = G-inr-inl-inr*₂ I A p i f (funExt q)
G-push-inl-inl 𝕄inst₂· = Sol.G-push-inl-inl
G-push-inr 𝕄inst₂· = Sol.G-push-inr
G-push-inl-inr 𝕄inst₂· = Sol.G-push-inl-inr
G-push-push-inr 𝕄inst₂· A g x i j k = Sol.G-push-push-inr A g x k i j
G-push-push-inl 𝕄inst₂· =  Sol.G-push-push-inl

-- 𝕄inst· : 𝕄inst {ℓ = ℓ}
-- inler 𝕄inst· = Sol.inler
-- inr-inr 𝕄inst· = inrerr
-- inr-inl-inl 𝕄inst· = inr-inl-inl*
-- inr-inl-inr 𝕄inst· = inr-inl-inr*
-- push-inl-inl 𝕄inst· = Sol.push-inl-inl
-- push-inr 𝕄inst· = Sol.push-inr
-- push-inl-inr 𝕄inst· = Sol.push-inl-inr
-- push-push-inr 𝕄inst· = Sol.push-push-inr
-- push-push-inl 𝕄inst· = Sol.push-push-inl
-- G-inler 𝕄inst· = Sol.G-inler
-- G-inr-inr 𝕄inst· = G-inr-inr*
-- G-inr-inl-inl₁ 𝕄inst· = G-inr-inl-inl*₁
-- G-inr-inl-inl₂ 𝕄inst· = G-inr-inl-inl*₂
-- G-inr-inl-inr₁ 𝕄inst· = G-inr-inl-inr*₁
-- G-inr-inl-inr₂ 𝕄inst· I A f p q i = G-inr-inl-inr*₂ I A p i f (funExt q)
-- G-push-inl-inl 𝕄inst· = Sol.G-push-inl-inl
-- G-push-inr 𝕄inst· = Sol.G-push-inr
-- G-push-inl-inr 𝕄inst· = Sol.G-push-inl-inr
-- G-push-push-inr 𝕄inst· A g x i j k = Sol.G-push-push-inr A g x k i j
-- G-push-push-inl 𝕄inst· = Sol.G-push-push-inl

-- -- module _ (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) where
-- --   FF = ΠR-extend₃-elim-inst (λ I J A _ → GOALTY I J A) (λ A _ → GOALTY' A) (λ A _ → GFUNEq A)
-- --                  (λ I J A x i → ΣJoinR→JoinR² I J A (i , ΠR-extend₃→JoinR I J A i x))
-- --                  (λ A x a j → GFUN A (ΣJoinR→JoinR² (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (a , ΠR-extend₃→JoinR-Bool (RP∞'∙ ℓ) A a (push x j))))
-- --                  (λ t A x y i → GFUN A (ΣJoinR→JoinR² (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (y , ΠR-extend₃→JoinR-Bool≡ (RP∞'∙ ℓ) A y (push x i) (~ t))))
-- --                  𝕄inst· I J A

-- --   UnordJoin²-alt→FlippedJoinR : UnordJoin²-alt I J A → UnordJoinR J (λ j → UnordJoinR I (λ i → A i j))
-- --   UnordJoin²-alt→FlippedJoinR (inl x) = ΣJoinR→JoinR² I J A x
-- --   UnordJoin²-alt→FlippedJoinR (inr x) = FF .fst x
-- --   UnordJoin²-alt→FlippedJoinR (push (i , x) k) = FF .snd i x k

-- --   UnordJoinFubiniFun : UnordJoinR I (λ i → UnordJoinR J (A i))
-- --                    →  UnordJoinR J (λ j → UnordJoinR I (λ i → A i j))
-- --   UnordJoinFubiniFun =
-- --       UnordJoin²-alt→FlippedJoinR
-- --     ∘ UnordJoin²₂→UnordJoin²-alt I J A
-- --     ∘ invEq (UnordJoin²₂≃UnordJoin² I J A)
