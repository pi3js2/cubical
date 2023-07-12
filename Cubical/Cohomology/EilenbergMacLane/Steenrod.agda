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


module Cubical.Cohomology.EilenbergMacLane.Steenrod where

open import Cubical.HITs.Join

module _ {ℓ ℓ' : Level} {A : Type ℓ} {x : A} {P : ∀ y → y ≡ x → Type ℓ'} (d : P x refl) where

  J>'_ : ∀ y → (p : y ≡ x) → P y p
  J>'_ _ p = transport (λ i → P (p (~ i)) λ j → p (~ i ∨ j)) d

infix 10 J>'_

TotΠ : ∀ {ℓ ℓ'} {A : Type ℓ} (B : A → Type ℓ') → Type _
TotΠ {A = A} B = (x : A) → B x

TotΠ² : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} (C : A → B → Type ℓ'') → Type _
TotΠ² {A = A} {B} C = (x : A) (y : B) → C x y


module _ {ℓ ℓ' ℓ'' : Level} (A : Type ℓ) (B : Type ℓ')
  (R : A → B → Type ℓ'') where

  data PushoutR  : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ'')) where
    inlR : A → PushoutR
    inrR : B → PushoutR
    push* : (a : A) (b : B) → R a b → inlR a ≡ inrR b
{-
data  ΠRex {ℓ : Level} (I J : RP∞) (A : fst I → fst J → Type ℓ) : Type ℓ  where

  aaₗ : (j : fst J) (f : (i : fst I) → A i j) → ΠRex I J A
  aaᵣ : (e : fst I ≃ fst J) (f : (i : fst I) → A i (fst e i)) → ΠRex I J A

  bb : TotΠ² A → ΠRex I J A

  rrₗ : (j : fst J) (b : TotΠ² A) → aaₗ j (λ i → b i j) ≡ bb b
  rrᵣ : (e : fst I ≃ fst J) (b : TotΠ² A) → aaᵣ e (λ i → b i (fst e i)) ≡ bb b

  ab : (i : fst I) (j : fst J) → A i j → ((j : fst J) → A (not* I i) j) → ΠRex I J A
  br : (i : fst I) (j : fst J) (b : (i : fst I) (j : fst J) → A i j)
    → ab i j (b i j) (b _) ≡ bb b

  arₗ : (i : fst I) (j : fst J) (f : (i : fst I) → A i j)
        (b : (j : fst J) → A (not* I i) j)
        (m : f (not* I i) ≡ b j)
        → aaₗ j f ≡ ab i j (f i) b
  arᵣ : (i : fst I) (e : fst I ≃ fst J) (f : (i : fst I) → A i (fst e i))
        (b : (j : fst J) → A (not* I i) j)
        (m : f (not* I i) ≡ b (fst e (not* I i)))
        → aaᵣ e f ≡ ab i (fst e i) (f i) b

  rr'ₗ : (i : fst I) (j : fst J)
    (b : (i : fst I) (j : fst J) → A i j)
    → PathP (λ k → aaₗ j (λ i₁ → b i₁ j) ≡ br i j b (~ k))
            (rrₗ j b)
            (arₗ i j (λ i → b i j) (b (not* I i)) refl)

  rr'ᵣ : (i : fst I) (e : fst I ≃ fst J)
    (b : (i : fst I) (j : fst J) → A i j)
    → PathP (λ k → aaᵣ e (λ i → b i (fst e i)) ≡ br i (fst e i) b (~ k))
            (rrᵣ e b)
            (arᵣ i e (λ i → b i (fst e i)) (b (not* I i)) refl)
-}
module _ {ℓ ℓ' ℓ'' : Level} (I : RP∞) (A : Type ℓ') (B : Type ℓ'')
   (A-d : fst I → Type ℓ')
   (B-d : fst I → Type ℓ'')
   (A-eval : (i : fst I) (f : A) → A-d i)
   (B-eval : (i : fst I) (f : B) → B-d i)
   (R : {i : fst I} → A-d i → B-d i → Type ℓ)
  where
  private
    ℓ* = ℓ-max ℓ (ℓ-max ℓ' ℓ'')

  data ΠRgen : Type ℓ* where
    aa* : A → ΠRgen
    bb* : B → ΠRgen
    ab* : (i : fst I) → A-d i → B-d (not* I i) → ΠRgen
    ar* : (i : fst I) (x : A) (b : B-d (not* I i)) → R (A-eval (not* I i) x) b → aa* x ≡ ab* i (A-eval i x) b
    br* : (i : fst I) (a : A-d i) (b : B) → R a (B-eval i b) → ab* i a (B-eval (not* I i) b) ≡ bb* b
    rr* : (a : A) (b : B) (r : (i : fst I) → R (A-eval i a) (B-eval i b)) → aa* a ≡ bb* b
    rr** : (i : fst I) (a : A) (b : B) (r : (i : fst I) → R (A-eval i a) (B-eval i b))
      → PathP (λ j → aa* a ≡ (br* i (A-eval i a) b (r i) (~ j))) (rr* a b r) (ar* i a (B-eval (not* I i) b) (r _))


module _ {ℓ ℓ' : Level} (I : RP∞) (A B : fst I → Type ℓ)
  (R : {i : fst I} → A i → B i → Type ℓ') where
  private
    ℓ* = ℓ-max ℓ ℓ'

  data ΠR : Type ℓ* where
    aa : TotΠ A → ΠR
    bb : TotΠ B → ΠR
    rr : (a : TotΠ A) (b : TotΠ B) (r : (i : fst I) → R (a i) (b i)) → aa a ≡ bb b

    ab : (i : fst I) → A i → B (not* I i) → ΠR

    ar : (i : fst I) (x : TotΠ A) (b : B (not* I i)) (r : R (x (not* I i)) b) → aa x ≡ ab i (x i) b
    br : (i : fst I) (a : A i) (b : TotΠ B) (r : R a (b i)) → ab i a (b (not* I i)) ≡ bb b
 

    rr' : (i : fst I) (a : TotΠ A) (b : TotΠ B) (r : (i : fst I) → R (a i) (b i))
      → PathP (λ j → aa a ≡ (br i (a i) b (r i) (~ j)))
               (rr a b r) (ar i a (b (not* I i)) (r _))



  ΠR' = ΠRgen I (TotΠ A) (TotΠ B) A B (λ i f → f i) (λ i f → f i) R

  ΠR≡ : Iso ΠR ΠR'
  Iso.fun ΠR≡ (aa x) = aa* x
  Iso.fun ΠR≡ (bb x) = bb* x
  Iso.fun ΠR≡ (ab i x x₁) = ab* i x x₁
  Iso.fun ΠR≡ (ar i x b r i₁) = ar* i x b r i₁
  Iso.fun ΠR≡ (br i a b r i₁) = br* i a b r i₁
  Iso.fun ΠR≡ (rr a b r i) = rr* a b r i
  Iso.fun ΠR≡ (rr' i a b r j i₁) = rr** i a b r j i₁
  Iso.inv ΠR≡ (aa* x) = aa x
  Iso.inv ΠR≡ (bb* x) = bb x
  Iso.inv ΠR≡ (ab* i x x₁) = ab i x x₁
  Iso.inv ΠR≡ (ar* i x b x₁ i₁) = ar i x b x₁ i₁
  Iso.inv ΠR≡ (br* i a b x i₁) = br i a b x i₁
  Iso.inv ΠR≡ (rr* a b r i) = rr a b r i
  Iso.inv ΠR≡ (rr** i a b r j i₁) = rr' i a b r j i₁
  Iso.rightInv ΠR≡ (aa* x) = refl
  Iso.rightInv ΠR≡ (bb* x) = refl
  Iso.rightInv ΠR≡ (ab* i x x₁) = refl
  Iso.rightInv ΠR≡ (ar* i x b x₁ i₁) = refl
  Iso.rightInv ΠR≡ (br* i a b x i₁) = refl
  Iso.rightInv ΠR≡ (rr* a b r i) = refl
  Iso.rightInv ΠR≡ (rr** i a b r j i₁) = refl
  Iso.leftInv ΠR≡ (aa x) = refl
  Iso.leftInv ΠR≡ (bb x) = refl
  Iso.leftInv ΠR≡ (ab i x x₁) = refl
  Iso.leftInv ΠR≡ (ar i x b r i₁) = refl
  Iso.leftInv ΠR≡ (br i a b r i₁) = refl
  Iso.leftInv ΠR≡ (rr a b r i) = refl
  Iso.leftInv ΠR≡ (rr' i a b r j i₁) = refl


  PR : fst I → Type _
  PR i = PushoutR (A i) (B i) R

  F1 : (i j : fst I) (x : A j) (y : B (not* I j)) → PushoutR (A i) (B i) R
  F1 i j x y = CasesRP I {A = PR} j (inlR x) (inrR y) i

  F1β : (j : fst I) (x : A j) (y : B (not* I j))
    → (F1 j j x y ≡ inlR x) × (F1 (not* I j) j x y ≡ inrR y)
  F1β j x y = CasesRPβ I {A = PR} j (inlR x) (inrR y)

  F1R : (i j : fst I) (x : TotΠ A) (b : B (not* I j)) (r : _)
    → inlR (x i) ≡ F1 i j (x j) b
  F1R i j x b r =
    CasesRP I {A = λ i → inlR (x i) ≡ F1 i j (x j) b} j
            (sym (F1β j (x j) b .fst))
            (push* _ _ r ∙ sym (F1β j (x j) b .snd)) i

  F1Rβ : (i : fst I) (x : TotΠ A) (b : B (not* I i)) (r : _)
    → (F1R i i x b r ≡ sym (F1β i (x i) b .fst))
      × (F1R (not* I i) i x b r ≡ push* _ _ r ∙ sym (F1β i (x i) b .snd))
  F1Rβ j x b r =
    CasesRPβ I {A = λ i → inlR (x i) ≡ F1 i j (x j) b} j
            (sym (F1β j (x j) b .fst))
            (push* _ _ r ∙ sym (F1β j (x j) b .snd))

  F1L : (i j : fst I) (a : A i) (b : TotΠ B) (r : _)
    → (F1 j i a (b (not* I i))) ≡ (inrR (b j))
  F1L i j a b r =
    CasesRP I {A = λ j → F1 j i a (b (not* I i)) ≡ inrR (b j)} i
      (F1β i a (b (not* I i)) .fst ∙ push* _ _ r)
      (F1β i a (b (not* I i)) .snd) j

  FILβ : (i : fst I) (a : A i) (b : TotΠ B) (r : _)
    → (F1L i i a b r ≡ F1β i a (b (not* I i)) .fst ∙ push* _ _ r)
     × (F1L i (not* I i) a b r ≡ F1β i a (b (not* I i)) .snd)
  FILβ i a b r =
    CasesRPβ I {A = λ j → F1 j i a (b (not* I i)) ≡ inrR (b j)} i
      (F1β i a (b (not* I i)) .fst ∙ push* _ _ r)
      (F1β i a (b (not* I i)) .snd)

  module _ (a : TotΠ A) (b : TotΠ B)
    (r : (i : _) → R (a i) (b i)) where

    F1LR-T : (i j : fst I) → Type _
    F1LR-T i j  =
      PathP (λ k → inlR (a i) ≡ F1L j i (a j) b (r j) (~ k))
               (push* (a i) (b i) (r i))
               (F1R i j a (b (not* I j)) (r (not* I j)))

    F1LRₗ : (i : fst I) → F1LR-T i i
    F1LRₗ i k l =
      hcomp (λ m → λ {(k = i0) → push* (a i) (b i) (r i) l
                     ; (k = i1) → F1Rβ i a (b (not* I i)) (r (not* I i)) .fst (~ m) l
                     ; (l = i0) → inlR (a i)
                     ; (l = i1) → FILβ i (a i) b (r i) .fst (~ m) (~ k)})
        {!compPath-filler (F1β i (a i) (b (not* I i)) .fst) (push* (a i) (b i) (r i)) l (~ k)!}

    F1LR : (i j : fst I) → F1LR-T i j
    F1LR i =
      CasesRP I {A = λ j → F1LR-T i j} i
       {!!}
       {!l = i0 ⊢ inlR (a i)
l = i1 ⊢ F1L i i (a i) b (r i) (~ k)
k = i0 ⊢ push* (a i) (b i) (r i) l
k = i1 ⊢ F1R i i a (b (not* I i)) (r (not* I i)) l!}
  
  cool : ΠR → (i : fst I) → PushoutR (A i) (B i) R
  cool (aa x) i = inlR (x i)
  cool (bb x) i = inrR (x i)
  cool (ab j x y) i = F1 i j x y
  cool (ar j x b r k) i = F1R i j x b r k
  cool (br i a b r k) j = F1L i j a b r k
  cool (rr a b r i₁) i = push* (a i) (b i) (r i) i₁
  cool (rr' j a b r k l) i = {!!}

                                      

joinR : ∀ {ℓ} (I : RP∞) (A : fst I → Type ℓ) → Type _
joinR I A = PushoutR (Σ (fst I) A) ((i : fst I) → A i)  λ x f → f (fst x) ≡ snd x

joinRD : ∀ {ℓ} (I J : RP∞) (A : fst I → fst J → Type ℓ) → Type _
joinRD I J A = joinR I λ i → joinR J (A i)


2-eltFun : {I J : RP∞}
  → (fst J ⊎ (fst I ≃ fst J)) ≃ (fst I → fst J)
2-eltFun {I}{J} = help I J , isEq-help I J
  where
  help : (I J : RP∞) → fst J ⊎ (fst I ≃ fst J) → fst I → fst J
  help I J (inl x) i = x
  help I J (inr x) i = fst x i

  mapb : (f : Bool → Bool) (b1 b2 : Bool) → f true ≡ b1 → f false ≡ b2 → Bool ⊎ (Bool ≃ Bool)
  mapb f false false p q = inl false
  mapb f false true p q =
    inr (f , subst isEquiv (funExt (λ { false → sym q ; true → sym p})) (notEquiv .snd))
  mapb f true false p q =
    inr (f , subst isEquiv (funExt (λ { false → sym q ; true → sym p})) (idEquiv Bool .snd))
  mapb f true true p q = inl true

  F : (Bool → Bool) → (Bool ⊎ (Bool ≃ Bool))
  F f = mapb f _ _ refl refl

  help' : Iso (Bool → Bool) (Bool ⊎ (Bool ≃ Bool))
  Iso.fun help' = F
  Iso.inv help' = help Bool* Bool*
  Iso.rightInv help' (inl false) = refl
  Iso.rightInv help' (inl true) = refl
  Iso.rightInv help' (inr x) = cong F (cong fst (sym (Iso.leftInv Bool≃Charac x)))
                             ∙ main (Iso.fun Bool≃Charac x)
                             ∙ λ i → inr (Iso.leftInv Bool≃Charac x i)
    where
    inr* : _ → Bool ⊎ (Bool ≃ Bool)
    inr* = inr
    main : (a : Bool) → F (Iso.inv Bool≃Charac a .fst) ≡ inr (Iso.inv Bool≃Charac a)
    main false = cong inr* (Σ≡Prop (λ _ → isPropIsEquiv _) refl)
    main true = cong inr* (Σ≡Prop (λ _ → isPropIsEquiv _) refl)
  Iso.leftInv help' f = t f _ _ refl refl
    where
    t : (f : Bool → Bool) (b1 b2 : Bool) (p : f true ≡ b1) (q : f false ≡ b2)
      → help Bool* Bool* (mapb f b1 b2 p q) ≡ f
    t f false false p q = funExt λ { false → sym q ; true → sym p}
    t f false true p q = refl
    t f true false p q = refl
    t f true true p q = funExt λ { false → sym q ; true → sym p}

  isEq-help : (X Y : _) → isEquiv (help X Y)
  isEq-help = RP∞pt→Prop (λ _ → isPropΠ λ _ → isPropIsEquiv _)
    (RP∞pt→Prop (λ _ → isPropIsEquiv _) (isoToIsEquiv (invIso help')))



module _ {ℓ : Level} (I J : RP∞) {A : fst I → fst J → Type ℓ} where
  M1 : (C : Type) (t : C ≃ (fst I → fst J))
    → ((i : fst I) → Σ (fst J) (A i))
    → Σ[ c ∈ C ] ((i : fst I) → A i (t .fst c i))
  M1 C t j = (invEq t (fst ∘ j))
    , λ i → subst (A i) (λ k → secEq t (λ i → fst (j i)) (~ k) i) (snd (j i))

  M2 : (C : Type) (t : C ≃ (fst I → fst J))
    → Σ[ c ∈ C ] ((i : fst I) → A i (t .fst c i))
    → ((i : fst I) → Σ (fst J) (A i))
  M2 C t (c , f) j = t .fst c j , f j

  M121 : (C : Type) (t : C ≃ (fst I → fst J))
    → (x : _) → M1 C t (M2 C t x) ≡ x
  M121 C = EquivJ (λ C t → (x : _) → M1 C t (M2 C t x) ≡ x)
    λ {(f , p) → ΣPathP (refl , funExt λ j → transportRefl (p j))}

  M212 : (C : Type) (t : C ≃ (fst I → fst J))
    → (x : _) → M2 C t (M1 C t x) ≡ x
  M212 C = EquivJ (λ C t → (x : _) → M2 C t (M1 C t x) ≡ x)
            λ f → funExt λ i → ΣPathP (refl , (transportRefl (snd (f i))))
  

module _ {ℓ : Level} (I J : RP∞) {A : fst I → fst J → Type ℓ} where
  f1 : ((i : fst I) → Σ (fst J) (A i))
    → Σ[ r ∈ fst J ⊎ (fst I ≃ fst J) ] ((i : fst I) → A i (fst (2-eltFun {I = I} {J = J}) r i))
  f1 = M1 I J {A = A} _ (2-eltFun {I = I} {J = J})

  f3 : Σ[ r ∈ fst J ⊎ (fst I ≃ fst J) ] ((i : fst I) → A i (fst (2-eltFun {I = I} {J = J}) r i)) → ((i : fst I) → Σ (fst J) (A i))
  f3 = M2 I J {A = A} _ (2-eltFun {I = I} {J = J})


  TotAIso : Iso ((i : fst I) → Σ (fst J) (A i))
                (Σ[ r ∈ fst J ⊎ (fst I ≃ fst J) ]
                  ((i : fst I) → A i (fst (2-eltFun {I = I} {J = J}) r i)))
  Iso.fun TotAIso = f1
  Iso.inv TotAIso = f3
  Iso.rightInv TotAIso x =
      M121 I J {A = A} _ (2-eltFun {I = I} {J = J}) x
  Iso.leftInv TotAIso x =
     M212 I J {A = A} _ (2-eltFun {I = I} {J = J}) x


module _ {ℓ : Level} (I J : RP∞) {A : fst I → fst J → Type ℓ} where
  2-elim = 2-eltFun {I = I} {J = J} .fst
  2-elim-inv = invEq (2-eltFun {I = I} {J = J})


  ΠR-base : Type _
  ΠR-base =
    Pushout {A = Σ[ f ∈ (TotΠ λ i → Σ[ j ∈ fst J ] (A i j)) ]
      (Σ[ g ∈ ((i : fst I) (j : fst J) → A i j) ] ((i : fst I) → g i (f i .fst) ≡ f i .snd))}
                    {B = TotΠ λ i → Σ[ j ∈ fst J ] (A i j)}
                    {C = (i : fst I) (j : fst J) → A i j}
                    fst
                    (fst ∘ snd)

  ΠR-base' : Type _
  ΠR-base' =
    Pushout {A = (fst I → fst J) × ((i : fst I) (j : fst J) → A i j)}
                    {B = TotΠ λ i → Σ[ j ∈ fst J ] (A i j)}
                    {C = (i : fst I) (j : fst J) → A i j}
                    (λ f i → (f .fst i) , (f .snd i (f .fst i)))
                    snd

  ΠR-base'' : Type _
  ΠR-base'' = Pushout {A = ((fst J) ⊎ (fst I ≃ fst J)) × ((i : fst I) (j : fst J) → A i j)}
                    {B = Σ[ e ∈ (fst J) ⊎ (fst I ≃ fst J) ] ((i : fst I) → A i (2-elim e i))}
                    {C = (i : fst I) (j : fst J) → A i j}
                    (λ p → (p .fst) , (λ i → p .snd i (2-elim (p .fst) i)))
                    snd

  ΠR-base-iso₂ : Iso ΠR-base'' ΠR-base'
  ΠR-base-iso₂ = 
    pushoutIso _ _ _ _
      (Σ-cong-equiv-fst (2-eltFun {I = I} {J = J}))
      (isoToEquiv (invIso (TotAIso I J)))
      (idEquiv _)
      refl
      refl

  ΠR-base-iso : Iso ΠR-base ΠR-base'
  ΠR-base-iso = pushoutIso _ _ _ _
    (isoToEquiv thIso)
    (idEquiv _)
    (idEquiv _)
    (funExt (λ x → funExt λ i → ΣPathP (refl , sym (snd x .snd i))))
    refl
    where
    thIso : Iso _ _
    Iso.fun thIso (f , g , p) =
      fst ∘ f , g
    Iso.inv thIso (f , g) =
      (λ i → f i , g i (f i)) , (g , (λ j → refl))
    Iso.rightInv thIso (f , g) = refl
    fst (fst (Iso.leftInv thIso (f , g , p) i') i) = fst (f i)
    snd (fst (Iso.leftInv thIso (f , g , p) i') i) = p i i'
    fst (snd (Iso.leftInv thIso (f , g , p) i')) = g
    snd (snd (Iso.leftInv thIso (f , g , p) i')) i'' k = p i'' (k ∧ i') 


  left-push : Type _
  left-push = Σ[ i ∈ fst I ] (Σ[ j ∈ fst J ] (A i j)) × ((j : fst J) → A (not* I i) j)

  left-push↑ₗ : fst I → Type _
  left-push↑ₗ i = Σ[ f ∈ ((i : fst I) → Σ[ j ∈ fst J ] A i j) ]
    Σ[ g ∈ ((j : fst J) → A (not* I i) j) ] (g (f (not* I i) .fst) ≡ f (not* I i) .snd)


  left-push↑ₗ' : fst I → Type _
  left-push↑ₗ' i = Σ[ f ∈ (Σ[ e ∈ (fst J) ⊎ (fst I ≃ fst J) ] ((i : fst I) → A i (2-elim e i))) ]
    Σ[ g ∈ ((j : fst J) → A (not* I i) j) ] (g (2-elim (fst f) (not* I i)) ≡ f .snd (not* I i))

  toΣIso : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : A → Type ℓ'}
    {C : (a : A) → B a → Type ℓ''}
    → Iso ((a : A) → Σ (B a) (C a)) (Σ[ f ∈ ((a : A) → B a) ] ((a : A) → C a (f a)))
  Iso.fun toΣIso f = fst ∘ f , snd ∘ f
  Iso.inv toΣIso (f , g) a = f a , g a
  Iso.rightInv toΣIso _ = refl
  Iso.leftInv toΣIso _ = refl

  I' = Cubical.Foundations.Prelude.I

  
  left-push↑ₗ-iso : (i : fst I) → Iso (left-push↑ₗ i) (left-push↑ₗ' i)
  left-push↑ₗ-iso i =
    invIso (Σ-cong-iso-fst (invIso (TotAIso I J)))



  left-push↑ᵣ : fst I → Type _
  left-push↑ᵣ i = Σ[ f ∈ (Σ[ j ∈ fst J ] A i j) ]
      Σ[ g ∈ ((i : fst I) (j : fst J) → A i j) ] g i (fst f) ≡ snd f

  left-push↑ᵣ' : fst I → Type _
  left-push↑ᵣ' i = fst J × ((i : fst I) (j : fst J) → A i j)

  left-push↑ᵣ-iso : (i : fst I) → Iso (left-push↑ᵣ i) (left-push↑ᵣ' i)
  Iso.fun (left-push↑ᵣ-iso i) (p , q , r) = (fst p) , q
  Iso.inv (left-push↑ᵣ-iso i) (p , r) = (p , (r i p)) , (r , refl)
  Iso.rightInv (left-push↑ᵣ-iso i) (p , r) = refl
  fst (fst (Iso.leftInv (left-push↑ᵣ-iso i) (p , q , r) k)) = fst p
  snd (fst (Iso.leftInv (left-push↑ᵣ-iso i) (p , q , r) k)) = r k
  fst (snd (Iso.leftInv (left-push↑ᵣ-iso i) (p , q , r) k)) = q
  snd (snd (Iso.leftInv (left-push↑ᵣ-iso i) (p , q , r) k)) j = r (k ∧ j)

  fat' : Type _
  fat' = ((fst J) ⊎ (fst I ≃ fst J)) × ((i : fst I) (j : fst J) → A i j)


  fat : Type _
  fat = (Σ[ f ∈ ((i : fst I) → Σ[ j ∈ fst J ] A i j) ]
          Σ[ g ∈ ((i : fst I) (j : fst J) → A i j) ]
            ((i : fst I) → g i (f i .fst) ≡ f i .snd))

  fat-slim : Type _
  fat-slim = (fst I → fst J) × ((i : fst I) (j : fst J) → A i j)

  fatIso₂ : Iso fat' fat-slim
  fatIso₂ = Σ-cong-iso-fst (equivToIso (2-eltFun {I} {J}))

  fatIso₁ : Iso fat fat-slim
  Iso.fun fatIso₁ (f , g , p) = (fst ∘ f) , g
  Iso.inv fatIso₁ (f , p) = (λ i → f i , p i (f i)) , (p , (λ _ → refl))
  Iso.rightInv fatIso₁ (f , p)  = refl
  Iso.leftInv fatIso₁ (f , g , p) k =
     (λ l → (fst (f l)) , (p l k)) , g
    , (λ l m → p l (k ∧ m))

  fat'→ₗ : (i : fst I) → fat' → left-push↑ₗ' i
  fat'→ₗ i (f , q) = (f , (λ i → q i (2-elim f i))) , ((q (not* I i)) , refl)

  fat→ₗ : (i : fst I) → fat → left-push↑ₗ i
  fat→ₗ  i (f , g , r) = (f , (g (not* I i)) , (r (not* I i)))

  fat→ᵣ : (i : fst I) → fat → left-push↑ᵣ i
  fat→ᵣ i (f , g , r) =  f i , g , r i

  fat'→ᵣ : (i : fst I) → fat' → left-push↑ᵣ' i
  fat'→ᵣ i (f , q) = (2-elim f i) , q

  PushTop' : Type _
  PushTop' = Σ[ i ∈ fst I ] (Pushout (fat'→ₗ i) (fat'→ᵣ i))
  
  PushTop : Type _
  PushTop = Σ[ i ∈ fst I ] (Pushout (fat→ₗ i) (fat→ᵣ i))

  PushTopIso' : Iso PushTop' PushTop
  PushTopIso' = Σ-cong-iso-snd λ i
    → pushoutIso _ _ _ _
        (isoToEquiv (compIso fatIso₂ (invIso fatIso₁)))
         (isoToEquiv (invIso (left-push↑ₗ-iso i)))
         (isoToEquiv (invIso (left-push↑ᵣ-iso i)))
         refl
         refl


  PushTop'→left-push : PushTop' → left-push
  PushTop'→left-push (i , inl ((f , p) , g)) = i , (((2-elim f i) , (p i)) , g .fst)
  PushTop'→left-push (i , inr (f , g)) = i , (f , (g i f)) , (g (not* I i))
  PushTop'→left-push (i , push (f , g) i₁) = i , ((2-elim f i) , g i (2-elim f i)) , g (not* I i)

  PushTop→ΠR-base' : PushTop' → ΠR-base''
  PushTop→ΠR-base' (i , inl (f , g , p)) = inl f
  PushTop→ΠR-base' (i , inr (f , g)) = inr g
  PushTop→ΠR-base' (i , push (f , p) i₁) = push (f , p) i₁

  PushTop→left-push : PushTop → left-push
  PushTop→left-push (i , inl (f , g , p)) = i , ((f i) , g)
  PushTop→left-push (i , inr (f , g , p)) = i , f , (g (not* I i))
  PushTop→left-push (i , push (f , g , p) k) = i , (f i) , λ j → g (not* I i) j

  PushTop→ΠR-base : PushTop → ΠR-base
  PushTop→ΠR-base (i , inl (f , g , p)) = inl f
  PushTop→ΠR-base (i , inr (f , g , p)) = inr g
  PushTop→ΠR-base (i , push (f , g , p)  i₁) = push (f , g , p) i₁

  ΠR-extend : Type _
  ΠR-extend = Pushout PushTop→left-push PushTop→ΠR-base

  ΠR-extend→Πₗ : left-push → TotΠ (λ i → joinR J (A i))
  ΠR-extend→Πₗ (i , p , r) = CasesRP I i (inlR p) (inrR r)

  ΠR-base→ : ΠR-base → TotΠ (λ i → joinR J (A i))
  ΠR-base→ (inl x) i = inlR (x i)
  ΠR-base→ (inr x) i = inrR λ j → x i j
  ΠR-base→ (push a i') i = push* (fst a i) (fst (snd a) i) (snd (snd a) i) i'

  ΠR-base→* : ΠR-base'' → TotΠ (λ i → joinR J (A i))
  ΠR-base→* (inl (p , q)) i = {!!} -- inlR (p i , {!q i!})
  ΠR-base→* (inr x) i = {!!}
  ΠR-base→* (push a i₁) i = {!!}

  ΠR-base→' : ΠR-base'' → TotΠ (λ i → joinR J (A i))
  ΠR-base→' (inl (p , q)) i = inlR (2-elim p i , q i)
  ΠR-base→' (inr x) i = inrR (x i)
  ΠR-base→' (push (p , q) i₁) i = push* (2-elim p i , q i (2-elim p i)) (q i) refl i₁


  pre-eqvl-diag : (i' : fst I) (p : Pushout (fat→ₗ i') (fat→ᵣ i'))
    → ΠR-extend→Πₗ (PushTop→left-push (i' , p)) i'
    ≡ ΠR-base→ (PushTop→ΠR-base (i' , p)) i'
  pre-eqvl-diag i' (inl (f , f2 , p)) =
    CasesRPβ I {A = λ i → joinR J (A i)} i' (inlR (f i' .fst , f i' .snd)) (inrR f2) .fst
  pre-eqvl-diag i' (inr (f , f2 , p)) =
    CasesRPβ I {A = λ i → joinR J (A i)} i' (inlR f) (inrR (f2 (not* I i'))) .fst ∙ push* f (f2 i') p 
  pre-eqvl-diag i' (push (f , f2 , p) i) j =
    compPath-filler (CasesRPβ I {A = λ i → joinR J (A i)} i' (inlR (f i')) (inrR (f2 (not* I i'))) .fst) (push* (f i') (f2 i') (p i')) i j

  pre-eqvl-not : (i' : fst I) (p : Pushout (fat→ₗ i') (fat→ᵣ i'))
    → ΠR-extend→Πₗ (PushTop→left-push (i' , p)) (not* I i') ≡
      ΠR-base→ (PushTop→ΠR-base (i' , p)) (not* I i')
  pre-eqvl-not i' (inl (f , f2 , p)) =
      CasesRPβ I {A = λ i → joinR J (A i)} i' (inlR (f i')) (inrR f2) .snd
    ∙ sym (push* (f (not* I i')) f2 p)
  pre-eqvl-not i' (inr (f , f2 , p)) =
    CasesRPβ I {A = λ i → joinR J (A i)} i' (inlR f) (inrR (f2 (not* I i'))) .snd
  pre-eqvl-not i' (push (f , f2 , p) i) j =
      compPath-filler
        (CasesRPβ I {A = λ i → joinR J (A i)} i' (inlR (f i')) (inrR (f2 (not* I i'))) .snd)
        (sym (push* (f (not* I i')) (f2 (not* I i')) (p (not* I i')))) (~ i) j


  eqvl : (a : PushTop) (i : fst I)
    → ΠR-extend→Πₗ (PushTop→left-push a) i
     ≡ ΠR-base→ (PushTop→ΠR-base a) i
  eqvl (i' , p) =
    CasesRP I i' (pre-eqvl-diag i' p)
                 (pre-eqvl-not i' p)
  
  ΠR-extend→Π : ΠR-extend → TotΠ (λ i → joinR J (A i))
  ΠR-extend→Π (inl t) = ΠR-extend→Πₗ t
  ΠR-extend→Π (inr x) = ΠR-base→ x
  ΠR-extend→Π (push a i) i' = eqvl a i' i

open import Cubical.Data.Bool as Boo

BoolElim : ∀ {ℓ} {A : Bool → Type ℓ} → A true → A false → (x : Bool) → A x
BoolElim at af false = af
BoolElim at af true = at

BoolElimη : ∀ {ℓ} {A : Bool → Type ℓ} (x : (y : _) → A y) → BoolElim {A = A} (x true) (x false) ≡ x
BoolElimη x = funExt (BoolElim refl refl)

BoolElimβ : {!!}
BoolElimβ = {!!}

module _ {ℓ : Level} {A : Bool → Bool → Type ℓ} where
  ΠR-bool = ΠR-extend Bool* Bool* {A}
  ΠR-extend-Bool-inl : left-push Bool* Bool* {A = A} → ((x : Bool) → joinR Bool* (A x))
  ΠR-extend-Bool-inl (x , a , c) = CasesBool x (inlR a) (inrR c)

  ΠR-extend-Bool-inr : ΠR-base Bool* Bool* {A = A} → ((x : Bool) → joinR Bool* (A x))
  ΠR-extend-Bool-inr (inl x₁) x = inlR (x₁ x)
  ΠR-extend-Bool-inr (inr x₁) x = inrR (x₁ x)
  ΠR-extend-Bool-inr (push a i) x = push* (fst a x) (fst (snd a) x) (snd (snd a) x) i

  ΠR-extend-Bool-push : (a : PushTop Bool* Bool* {A = A}) (x : Bool)
    → ΠR-extend-Bool-inl (PushTop→left-push Bool* Bool* a) x
    ≡ ΠR-extend-Bool-inr (PushTop→ΠR-base Bool* Bool* a) x
  ΠR-extend-Bool-push (x , p) = CasesBool x (t x p) (s x p)
    where
    t : (x : Bool) (p : _) → ΠR-extend-Bool-inl (PushTop→left-push Bool* Bool* (x , p)) x
                            ≡ ΠR-extend-Bool-inr (PushTop→ΠR-base Bool* Bool* (x , p)) x
    t x (inl (f , p , q)) = CasesBoolβ {A = λ x → joinR Bool* (A x)} x (inlR (f x)) (inrR p) .fst
    t x (inr (f , p , q)) = CasesBoolβ {A = λ x → joinR Bool* (A x)} x (inlR f) (inrR (p (not x))) .fst ∙ push* f (p x) q
    t x (push (f , p , q) i) =
      compPath-filler (CasesBoolβ {A = λ x → joinR Bool* (A x)} x (inlR (f x)) (inrR (p (not x))) .fst)
        (push* (f x) (p x) (q x)) i

    s : (x : Bool) (p : _)
      → ΠR-extend-Bool-inl (PushTop→left-push Bool* Bool* (x , p)) (not* Bool* x)
       ≡ ΠR-extend-Bool-inr (PushTop→ΠR-base Bool* Bool* (x , p)) (not* Bool* x)
    s x (inl (f , p , q)) = CasesBoolβ {A = λ x → joinR Bool* (A x)} x (inlR (f x)) (inrR p) .snd ∙ sym (push* (f (not* Bool* x)) p q)
    s x (inr (f , p , q)) = CasesBoolβ {A = λ x → joinR Bool* (A x)} x (inlR f) (inrR (p (not* Bool* x))) .snd
    s x (push (f , p , q) i) =
      compPath-filler (CasesBoolβ {A = λ x → joinR Bool* (A x)} x (inlR (f x)) (inrR (p (not x))) .snd)
                       (sym (push* (f (not* Bool* x)) (p (not* Bool* x)) (q (not* Bool* x)))) (~ i)

  ΠR-extend-Bool' : ΠR-bool →  ((x : Bool) → joinR Bool* (A x))
  ΠR-extend-Bool' (inl x) = ΠR-extend-Bool-inl x
  ΠR-extend-Bool' (inr x) = ΠR-extend-Bool-inr x
  ΠR-extend-Bool' (push a i) x = ΠR-extend-Bool-push a x i

  ΠR-extend-Bool : ΠR-bool → joinR Bool* (A true) × joinR Bool* (A false)
  ΠR-extend-Bool (inl (false , a , c)) = (inrR c) , (inlR a)
  ΠR-extend-Bool (inl (true , a , c)) = inlR a , inrR c
  ΠR-extend-Bool (inr (inl x)) = inlR (x true) , inlR (x false)
  ΠR-extend-Bool (inr (inr x)) = (inrR (x true)) , inrR (x false)
  ΠR-extend-Bool (inr (push (f , q , p) i)) = (push* (f true) (q true) (p true) i)
                                            , (push* (f false) (q false) (p false) i)
  ΠR-extend-Bool (push (false , inl (f , f2 , p)) i) = (push* (f true) f2 p (~ i)) , (inlR (f false))
  ΠR-extend-Bool (push (false , inr (f , f2 , p)) i) = inrR (f2 true) , push* f (f2 false) p i
  ΠR-extend-Bool (push (false , push (f , f2 , p) i₁) i) = (push* (f true) (f2 true) (p true) (i₁ ∨ ~ i))
                                                         , push* (f false) (f2 false) (p false) (i₁ ∧ i)
  ΠR-extend-Bool (push (true , inl (f , f2 , p)) i) = (inlR (f true)) , (push* (f false) f2 p (~ i))
  ΠR-extend-Bool (push (true , inr (f , f2 , p)) i) = (push* f (f2 true) p i) , (inrR (f2 false))
  ΠR-extend-Bool (push (true , push (f , f2 , p) i₁) i) = push* (f true) (f2 true) (p true) (i₁ ∧ i) , (push* (f false) (f2 false) (p false) (i₁ ∨ ~ i))

  ΠR-extend-Bool'≡ : (x : ΠR-bool) → ΠR-extend-Bool' x true ≡ fst (ΠR-extend-Bool x)
  ΠR-extend-Bool'≡ (inl (false , p)) = refl
  ΠR-extend-Bool'≡ (inl (true , p)) = refl
  ΠR-extend-Bool'≡ (inr (inl x)) = refl
  ΠR-extend-Bool'≡ (inr (inr x)) = refl
  ΠR-extend-Bool'≡ (inr (push a i)) = refl
  ΠR-extend-Bool'≡ (push (false , inl x) i) j = lUnit (sym (push* (fst x true) (fst (snd x)) (snd (snd x)))) (~ j) i
  ΠR-extend-Bool'≡ (push (false , inr x) i) = refl
  ΠR-extend-Bool'≡ (push (false , push a i₁) i) j =
    hcomp (λ r → λ {(i = i0) → {!!}
                   ; (i = i1) → {!!}
                   ; (j = i0) → {!ΠR-extend-Bool-push (false , push a i₁) true i!}
                   ; (j = i1) → {!!}
                   ; (i₁ = i0) → {!lUnit-filler (sym (push* (fst a true) (fst (snd a) true) (snd (snd a) true))) r i j!}
                   ; (i₁ = i1) → {!!}}) {!!}
  ΠR-extend-Bool'≡ (push (true , snd₁) i) =
    {!j = i0 ⊢ ΠR-extend-Bool-push (false , push a i₁) true i
j = i1 ⊢ push* (fst a true) (fst (snd a) true) (snd (snd a) true)
         (i₁ ∨ ~ i)
i = i0 ⊢ inrR (fst (snd a) (not* Bool* false))
i = i1 ⊢ push* (fst a true) (fst (snd a) true) (snd (snd a) true)
         i₁
i₁ = i0 ⊢ lUnit
          (λ i₂ →
             push* (fst (fat→ₗ Bool* Bool* false a) true)
             (fst (snd (fat→ₗ Bool* Bool* false a)))
             (snd (snd (fat→ₗ Bool* Bool* false a))) (~ i₂))
          (~ j) i
i₁ = i1 ⊢ inrR
          (fst (snd (fat→ᵣ Bool* Bool* false a)) (not* Bool* false))!}


  →Pair : ∀ {ℓ} {A : Bool → Type ℓ} → ((x : Bool) → A x) → A true × A false
  →Pair f = f true , f false

  hitl : (w : ΠR-extend Bool* Bool* {A = A})
    → joinR Bool* (A true) × joinR Bool* (A false)
  hitl w = →Pair (ΠR-extend→Π Bool* Bool* {A} w)



--  CasesRP I i (inlR p) (inrR r)
  hitl' : (w : _) → hitl w ≡ ΠR-extend-Bool w
  hitl' (inl (b , a , x)) = {!!} -- cong (→Pair {A = joinR Bool* ∘ A}) {!!} -- cong →Pair {!!}
  hitl' (inr x) = {!!}
  hitl' (push a i) = {!!}


--   ΠR-extend-Bool* : ΠR-bool → joinR Bool* (A true) × joinR Bool* (A false)
--   ΠR-extend-Bool* (inl (false , a , c)) = (inrR c) , (inlR a)
--   ΠR-extend-Bool* (inl (true , a , c)) = inlR a , inrR c
--   ΠR-extend-Bool* (inr (inl x)) = inlR (x true) , inlR (x false)
--   ΠR-extend-Bool* (inr (inr x)) = (inrR (x true)) , inrR (x false)
--   ΠR-extend-Bool* (inr (push (f , q , p) i)) =
--     ((λ i → push* (f true) (q true) (p true) i , inlR (f false))
--     ∙∙ refl
--     ∙∙  λ i → inrR (q true) , push* (f false) (q false) (p false) i) i
--   ΠR-extend-Bool* (push (false , inl (f , f2 , p)) i) = (push* (f true) f2 p (~ i)) , (inlR (f false))
--   ΠR-extend-Bool* (push (false , inr (f , f2 , p)) i) = inrR (f2 true) , push* f (f2 false) p i
--   ΠR-extend-Bool* (push (false , push (f , f2 , p) i₁) i) =
--     doubleCompPath-filler (λ i → push* (f true) (f2 true) (p true) i , inlR (f false))
--                           refl
--                           (λ i → inrR (f2 true) , push* (f false) (f2 false) (p false) i) i i₁
--   ΠR-extend-Bool* (push (true , inl (f , f2 , p)) i) = (inlR (f true)) , (push* (f false) f2 p (~ i))
--   ΠR-extend-Bool* (push (true , inr (f , f2 , p)) i) = (push* f (f2 true) p i) , (inrR (f2 false))
--   ΠR-extend-Bool* (push (true , push (f , q , p) i₁) i) =
--     hcomp (λ k → λ {(i = i0) → {!!}
--                    ; (i = i1) → doubleCompPath-filler (λ i₂ →  push* (f true) (q true) (p true) i₂ , inlR (f false))
--                                                        refl
--                                                        (λ i₂ → inrR (q true) , push* (f false) (q false) (p false) i₂) i1 i₁
--                    ; (i₁ = i0) → {!!}
--                    ; (i₁ = i1) → {!!}})
--           {!!}

--   Square-filler : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : z ≡ y)
--     → I → I → I → A
--   Square-filler p q i j k =
--     hfill (λ k → λ {(i = i0) → p (~ j ∨ ~ k)
--                    ; (i = i1) → q j
--                    ; (j = i0) → q (~ i)
--                    ; (j = i1) → p (i ∨ ~ k)})
--            (inS (q (~ i ∨ j)))
--            k

--   module _ {ℓ : Level} {A : Type ℓ} (inl[true∶a∶b₁] inr-inl[BoolElim-a-a₁] : A)
--                 (push[true∶inl[BoolElim-a-a₁∶b₁∶x₁] : inl[true∶a∶b₁] ≡ inr-inl[BoolElim-a-a₁])
--                 (inl[false∶a₁∶b] inr-inr[BoolElim-b-b₁] : A)
--                 (push[false∶inr[a₁∶BoolElim-b-b₁∶x₁]] : inl[false∶a₁∶b] ≡ inr-inr[BoolElim-b-b₁])
--                 (push[false∶inl[BoolElim-a-a₁∶b∶x]] : inl[false∶a₁∶b] ≡ inr-inl[BoolElim-a-a₁])
--                 (inr-push[BoolElim-a-a₁:BoolElim-b-b₁∶BoolElim-x-x₁] : inr-inl[BoolElim-a-a₁] ≡ inr-inr[BoolElim-b-b₁])
--                 (push[false∶push[BoolElim-a-a₁:BoolElim-b-b₁∶BoolElim-x-x₁]] :
--                   Square push[false∶inl[BoolElim-a-a₁∶b∶x]]
--                          push[false∶inr[a₁∶BoolElim-b-b₁∶x₁]]
--                          refl
--                          inr-push[BoolElim-a-a₁:BoolElim-b-b₁∶BoolElim-x-x₁])
--         (push[true∶inr[a∶BoolElim-b-b₁∶x]] : inl[true∶a∶b₁] ≡ inr-inr[BoolElim-b-b₁])
--         (push[true∶push[BoolElim-a-a₁:BoolElim-b-b₁∶BoolElim-x-x₁]] :
--              Square push[true∶inl[BoolElim-a-a₁∶b₁∶x₁] push[true∶inr[a∶BoolElim-b-b₁∶x]] refl inr-push[BoolElim-a-a₁:BoolElim-b-b₁∶BoolElim-x-x₁])
--     where

--     FF-gen : I → I → I → A
--     FF-gen i j k =
--            hfill (λ k → λ {(i = i0) → push[true∶inl[BoolElim-a-a₁∶b₁∶x₁] (~ j)
--                           ; (i = i1) → push[false∶push[BoolElim-a-a₁:BoolElim-b-b₁∶BoolElim-x-x₁]] k j
--                           ; (j = i0) → push[false∶inl[BoolElim-a-a₁∶b∶x]] (~ i)
--                           ; (j = i1) → push[true∶push[BoolElim-a-a₁:BoolElim-b-b₁∶BoolElim-x-x₁]] k i})
--                  (inS (Square-filler push[true∶inl[BoolElim-a-a₁∶b₁∶x₁] push[false∶inl[BoolElim-a-a₁∶b∶x]] i j i1))
--                  k

--     FF-gen' : Square (sym (push[true∶inl[BoolElim-a-a₁∶b₁∶x₁]))
--                push[false∶inr[a₁∶BoolElim-b-b₁∶x₁]]
--                (sym push[false∶inl[BoolElim-a-a₁∶b∶x]])
--                push[true∶inr[a∶BoolElim-b-b₁∶x]]
--     FF-gen' i j = FF-gen i j i1

--     FF-case₁-gen* : (inr-inl-f1 : A) (p : inr-inl[BoolElim-a-a₁] ≡ inr-inl-f1)
--                     (inr-inr-f2 : A) (q : inr-inr[BoolElim-b-b₁] ≡ inr-inr-f2)
--                     (push[false∶inl[f∶b∶x]] : inl[false∶a₁∶b] ≡ inr-inl-f1)
--                     (push-id₁ : Square push[false∶inl[BoolElim-a-a₁∶b∶x]] push[false∶inl[f∶b∶x]] refl p)
--                     (push[false∶inr[a₁∶f2∶x₁]] : inl[false∶a₁∶b] ≡ inr-inr-f2)
--                     (push-id₂ : Square push[false∶inr[a₁∶BoolElim-b-b₁∶x₁]] push[false∶inr[a₁∶f2∶x₁]]  refl q)
--                     (pash : inr-inl-f1 ≡ inr-inr-f2)
--                  → (bot : inl[false∶a₁∶b] ≡ inl[false∶a₁∶b])
--                  → (pr : refl ≡ bot)
--                  → (pash-coh : Square bot pash push[false∶inl[f∶b∶x]] push[false∶inr[a₁∶f2∶x₁]])
--       → Square p q (λ i → FF-gen' i i) pash
--     FF-case₁-gen* inr-inl-f1 p inr-inl-f2 q push[false∶inl[f∶b∶x]] push-id₁ push[false∶inr[a₁∶f2∶x₁]] push-id₂ pash bot pr pash-coh i i' =
--       hcomp (λ w → λ {(i = i0) → push-id₁ i' w
--                       ; (i = i1) → push-id₂ i' w
--                       ; (i' = i0) → FF-gen' (i ∨ ~ w) (i ∧ w)
--                       ; (i' = i1) → pash-coh w i})
--              (pr i' i)


--   module _ (a : Σ (fst Bool*) (A true)) (b : (i₂ : fst Bool*) → A true i₂) (x : b (fst a) ≡ snd a)
--        (a₁ : Σ (fst Bool*) (A false)) (b₁ : (i₂ : fst Bool*) → A false i₂) (x₁ : b₁ (fst a₁) ≡ snd a₁)
--         where
--     btmFF : (i i₁ j : I) → ΠR-bool
--     btmFF i i₁ j = Square-filler (push (false , inl (BoolElim a a₁ , b , x)))
--                                  (push (true , inl (BoolElim a a₁ , b₁ , x₁))) i₁ i j

--     push** : (x : _) → Path (Pushout (PushTop→left-push Bool* Bool* {A = A})
--       (PushTop→ΠR-base Bool* Bool*)) _ _
--     push** = push

--     push*** : (x : _) → Path (Pushout (fat→ₗ Bool* Bool* {A = A} false) (fat→ᵣ Bool* Bool* false)) _ _
--     push*** = push

--     FF : I → I → I → ΠR-bool
--     FF = FF-gen (inl(true , a , b₁)) (inr (inl (BoolElim a a₁)))
--                 (push (true , inl (BoolElim a a₁ , b₁ , x₁)))
--                 (inl (false , a₁ , b))
--                 (inr (inr (BoolElim b b₁)))
--                 (push (false , inr (a₁ , BoolElim b b₁ , x₁)))
--                 (push (false , inl (BoolElim a a₁ , b , x)))
--                 (λ i → inr (push (BoolElim a a₁ , BoolElim b b₁ , BoolElim x x₁) i))
--                 (λ i j → push (false , push (BoolElim a a₁ , BoolElim b b₁ , BoolElim x x₁) i) j)
--                 (push(true , inr (a , BoolElim b b₁ , x)))
--                 λ i j → push(true , push (BoolElim a a₁ , BoolElim b b₁ , BoolElim x x₁) i) j

--     FF' : Square (sym (push (true , inl (BoolElim a a₁ , b₁ , x₁))))
--       (push (false , inr (a₁ , BoolElim b b₁ , x₁)))
--       (sym (push (false , inl (BoolElim a a₁ , b , x))))
--       (push (true , inr (a , BoolElim b b₁ , x)))
--     FF' = FF-gen' {A = ΠR-bool} (inl(true , a , b₁)) (inr (inl (BoolElim a a₁)))
--                 (push (true , inl (BoolElim a a₁ , b₁ , x₁)))
--                 (inl (false , a₁ , b))
--                 (inr (inr (BoolElim b b₁)))
--                 (push (false , inr (a₁ , BoolElim b b₁ , x₁)))
--                 (push (false , inl (BoolElim a a₁ , b , x)))
--                 (λ i → inr (push (BoolElim a a₁ , BoolElim b b₁ , BoolElim x x₁) i))
--                 (λ i j → push (false , push (BoolElim a a₁ , BoolElim b b₁ , BoolElim x x₁) i) j)
--                 (push(true , inr (a , BoolElim b b₁ , x)))
--                 λ i j → push(true , push (BoolElim a a₁ , BoolElim b b₁ , BoolElim x x₁) i) j


--   ΠR-extend-Bool← : joinR Bool* (A true) × joinR Bool* (A false) → ΠR-bool
--   ΠR-extend-Bool← (inlR (j , a) , inlR (j' , a')) = inr (inl (BoolElim (j , a) (j' , a')))
--   ΠR-extend-Bool← (inlR (j , a) , inrR x) = inl (true , ((j , a) , x))
--   ΠR-extend-Bool← (inlR (j , a) , push* a₁ b x i) = push (true , inl (BoolElim (j , a) a₁ , b , x)) (~ i)
--   ΠR-extend-Bool← (inrR x , inlR y) = inl (false , y , x)
--   ΠR-extend-Bool← (inrR x , inrR x₁) = inr (inr (BoolElim x x₁))
--   ΠR-extend-Bool← (inrR x , push* a b x₁ i) = push (false , inr (a , (BoolElim x b) , x₁)) i
--   ΠR-extend-Bool← (push* a b x i , inlR x₁) = push (false , inl (BoolElim a x₁ , b , x)) (~ i)
--   ΠR-extend-Bool← (push* a b x i , inrR x₁) = push (true , inr (a , (BoolElim b x₁) , x)) i
--   ΠR-extend-Bool← (push* a b x i , push* a₁ b₁ x₁ i₁) = FF a b x a₁ b₁ x₁ i i₁ i1

--   ΠR-extend-Bool** : {!!} -- joinR Bool* (A true) × joinR Bool* (A false) → ΠR-bool
--   ΠR-extend-Bool** = {!!}



-- --   module _ {ℓ} {A : Type ℓ} (x y : A) (p : x ≡ y) (z : A) (q : y ≡ z) (w : A) (bot : x ≡ w) (r : w ≡ z)
-- --     (FF : Square p r bot q)
-- --      (x' : A) (coh1 : x ≡ x')
-- --      (z' : A) (coh2 : z ≡ z')
-- --      (top : x' ≡ z')
-- --      (ba : A) (temp : ba ≡ x') (temp2 : ba ≡ z')
-- --      (p' : w ≡ ba) (q' : w ≡ ba)
-- --      (p'≡q' : p' ≡ q')
-- --      (temp3 : y ≡ x') (temp4 : y ≡ z')
-- --      (q1 : Square p' coh1 (sym bot) temp)
-- --      (q2 : Square q' coh2 r temp2)
-- --      (q3 : Square refl top temp temp2)
-- --      (q4 : Square refl coh1 (sym p) temp3)
-- --      (q5 : Square (λ _ → y) coh2 q temp4)
-- --      (q6 : Square temp3 temp4 refl top)
-- --      where
-- --      FF-case₁-gen : Square (λ i → FF i i) top coh1 coh2
-- --      FF-case₁-gen i' i =
-- --        hcomp (λ w → λ {(i = i0) → q1 w i'
-- --                       ; (i = i1) → q2 w i'
-- --                       ; (i' = i0) → FF (i ∨ ~ w) (i ∧ w)
-- --                       ; (i' = i1) → q3 w i})
-- --              (p'≡q' i i')

-- --   PP-gen : ∀ {ℓ} {A : Type ℓ} (x y : A) (p : x ≡ y) (z : A) (q : y ≡ z) (w : A) (bot : x ≡ w) (r : w ≡ z)
-- --       (FF : Square p r bot q)
-- --        (x' : A) (coh1 : x ≡ x')
-- --        (z' : A) (coh2 : z ≡ z')
-- --        (top : x' ≡ z')
-- --        (ba : A) (temp : ba ≡ x') (temp2 : ba ≡ z')
-- --        (p' : w ≡ ba) (q' : w ≡ ba)
-- --        (p'≡q' : p' ≡ q')
-- --        (temp3 : y ≡ x') (temp4 : y ≡ z')
-- --        (q1 : Square p' coh1 (sym bot) temp)
-- --        (q2 : Square q' coh2 r temp2)
-- --        (q3 : Square refl top temp temp2)
-- --        (q4 : Square refl coh1 (sym p) temp3)
-- --        (q5 : Square (λ _ → y) coh2 q temp4)
-- --        (q6 : Square temp3 temp4 refl top)
-- --        (h : ba ≡ y)
-- --        (temp≡l : Square refl temp3 h temp)
-- --        (temp≡r : Square top temp4 {!temp2!} refl)
-- --        → Cube q3 {!q6!} {!!} {!q6!} {!q6!} {!q6!}
-- --        → Cube {A = A}
-- --                 q4
-- --                 q5
-- --                 (λ _ _ → y)
-- --                 (λ i₁ i' → FF-case₁-gen x y p z q w bot r FF x' coh1 z' coh2 top ba temp temp2 p' q' p'≡q' temp3 temp4 q1 q2 q3 q4 q5 q6 i' i₁)
-- --                 (λ i₁ i → FF (i₁ ∧ i) (i₁ ∨ ~ i))
-- --                 q6
-- --   PP-gen x = {!!} -- J> (J> (J> (J> (J> (J> λ top → J>' λ temp p' → J> λ temp3 temp4 → {!J>' ?!})))))



-- --      {-
-- --      Cube {A = ΠR-bool}
-- --               (λ i i' → push (true , inl ((BoolElimη f i') , ((p false) , (q false)))) i)
-- --               (λ i i' → push (true , inr ((f true) , ((BoolElimη p i') , (q true)))) i)
-- --               (λ i₁ i' → inl (true , f true , p false))
-- --               (λ i₁ i' → FF-case₁ f p q i' i₁)
-- --               (λ i₁ i → FF (f true) (p true) (q true) (f false) (p false) (q false) (i₁ ∧ i) (i₁ ∨ ~ i) i1)
-- --               λ i₁ i → push (true , push (f , p , q) i₁) i
-- --      -}
-- -- {-
-- --      FF-case₁-gen' : Square (λ i → FF i i) top coh1 coh2
-- --      FF-case₁-gen' i' i =
-- --        hcomp (λ w → λ {(i = i0) → q4 w i'
-- --                       ; (i = i1) → q5 w i'
-- --                       ; (i' = i0) → FF (i ∧ w) (i ∨ ~ w)
-- --                       ; (i' = i1) → q6 w i})
-- --                (r'≡s' i i')
-- -- -}
     




-- --   FF-case₁* : (f : TotΠ (λ i₁ → Σ-syntax (fst Bool*) (A i₁)))
-- --     (p : (i₁ j : fst Bool*) → A i₁ j)
-- --     (q : (i₁ : fst Bool*) → p i₁ (f i₁ .fst) ≡ f i₁ .snd)
-- --     → Square (λ i → FF' (f true) (p true) (q true) (f false) (p false) (q false) i i)
-- --               (λ i → inr (push (f , p , q) i))
-- --               (λ i' → inr (inl (BoolElimη f i')))
-- --               λ i' → inr (inr (BoolElimη p i'))
-- --   FF-case₁* f p q = {!!}

-- --   FF-case₁' : (f : TotΠ (λ i₁ → Σ-syntax (fst Bool*) (A i₁)))
-- --     (p : (i₁ j : fst Bool*) → A i₁ j)
-- --     (q : (i₁ : fst Bool*) → p i₁ (f i₁ .fst) ≡ f i₁ .snd)
-- --     → Square (λ i → FF' (f true) (p true) (q true) (f false) (p false) (q false) i i)
-- --               (λ i → inr (push (f , p , q) i))
-- --               (λ i' → inr (inl (BoolElimη f i')))
-- --               λ i' → inr (inr (BoolElimη p i'))
-- --   FF-case₁' f p q i' i =
-- --     hcomp (λ r → λ {(i = i0) → push (true , inl (BoolElimη f i' , p false , q false)) r
-- --                    ; (i = i1) → push (true , inr (f true , BoolElimη p i' , q true)) r
-- --                    ; (i' = i0) → FF (f true) (p true) (q true)
-- --                                      (f false) (p false) (q false) (i ∧ r) (i ∨ ~ r) i1
-- --                    ; (i' = i1) → {!push (true , (push (f , p , q) i)) r!}})
-- --           {!FF' (f true) (p true) (q true) (f false) (p false) (q false) i0 i!} -- (inl (false , BoolElimη f i' false , p true))

-- --   FF-case₁ : (f : TotΠ (λ i₁ → Σ-syntax (fst Bool*) (A i₁)))
-- --     (p : (i₁ j : fst Bool*) → A i₁ j)
-- --     (q : (i₁ : fst Bool*) → p i₁ (f i₁ .fst) ≡ f i₁ .snd)
-- --     → Square (λ i → FF (f true) (p true) (q true) (f false) (p false) (q false) i i i1)
-- --               (λ i → inr (push (f , p , q) i))
-- --               (λ i' → inr (inl (BoolElimη f i')))
-- --               λ i' → inr (inr (BoolElimη p i'))
-- --   FF-case₁ f p q i' i =
-- --     hcomp (λ r → λ {(i = i0) → push (false , inl (BoolElimη f i' , p true , q true)) r
-- --                    ; (i = i1) → push (false , (inr ((f false) , ((BoolElimη p i') , (q false))))) r
-- --                    ; (i' = i0) → FF (f true) (p true) (q true)
-- --                                      (f false) (p false) (q false) (i ∨ ~ r) (i ∧ r) i1
-- --                    ; (i' = i1) → push (false , push (f , (p , q)) i) r})
-- --                    (inl (false , BoolElimη f i' false , p true))

-- --   BoolElim-refl-refl : ∀ {ℓ} {A : Bool → Type ℓ} {p : (x : Bool) → A x}
-- --     → BoolElim {A = λ x → p x ≡ p x} refl refl ≡ (λ x → refl)
-- --   BoolElim-refl-refl {p = p} i false = refl
-- --   BoolElim-refl-refl {p = p} i true = refl

-- --   ΠR-extend-Bool→←→ : (x : _) → ΠR-extend-Bool (ΠR-extend-Bool← x) ≡ x
-- --   ΠR-extend-Bool→←→ (inlR x , inlR x₁) = refl
-- --   ΠR-extend-Bool→←→ (inlR x , inrR x₁) = refl
-- --   ΠR-extend-Bool→←→ (inlR x , push* a b x₁ i) = refl
-- --   ΠR-extend-Bool→←→ (inrR x , inlR x₁) = refl
-- --   ΠR-extend-Bool→←→ (inrR x , inrR x₁) = refl
-- --   ΠR-extend-Bool→←→ (inrR x , push* a b x₁ i) = refl
-- --   ΠR-extend-Bool→←→ (push* a b x i , inlR x₁) = refl
-- --   ΠR-extend-Bool→←→ (push* a b x i , inrR x₁) = refl
-- --   fst (ΠR-extend-Bool→←→ (push* a b x i , push* a₁ b₁ x₁ i₁) i₂) = {!!}
-- --   snd (ΠR-extend-Bool→←→ (push* a b x i , push* a₁ b₁ x₁ i₁) i₂) = {!!}
  

-- --   ΠR-extend-Bool←→← : (x : _) → ΠR-extend-Bool← (ΠR-extend-Bool x) ≡ x
-- --   ΠR-extend-Bool←→← (inl (false , p)) = refl
-- --   ΠR-extend-Bool←→← (inl (true , p)) = refl
-- --   ΠR-extend-Bool←→← (inr (inl x)) i = inr (inl (BoolElimη x i))
-- --   ΠR-extend-Bool←→← (inr (inr x)) i = inr (inr (BoolElimη x i))
-- --   ΠR-extend-Bool←→← (inr (push (f , p , q) i)) i' = FF-case₁ f p q i' i
-- --   ΠR-extend-Bool←→← (push (false , inl (f , p)) i) i' =
-- --     push (false , (inl (BoolElimη f i' , p))) i
-- --   ΠR-extend-Bool←→← (push (false , inr x) i) j =
-- --     push (false , inr (fst x , (BoolElimη (fst (snd x)) j) , (snd (snd x)))) i
-- --   ΠR-extend-Bool←→← (push (false , push (f , p , q) i₁) i) i' = ts f p q i₁ i i'
-- --     where
-- --     ts : (f : (i₂ : fst Bool*) → Σ-syntax (fst Bool*) (A i₂))
-- --          (p : (i₂ j : fst Bool*) → A i₂ j)
-- --          (q : (i₂ : fst Bool*) → p i₂ (f i₂ .fst) ≡ f i₂ .snd)
-- --       → Cube {A = ΠR-bool} (λ i i' → push (false , inl ((BoolElimη f i') , (p true , q true))) i)
-- --                             (λ i i' → push (false , inr ((f false) , ((BoolElimη p i') , (q false)))) i)
-- --               (λ i₁ i' → inl (false , f false , p true))
-- --               (λ i₁ i' → FF-case₁ f p q i' i₁)
-- --               (λ i₁ i → FF (f true) (p true) (q true) (f false) (p false) (q false) (i₁ ∨ ~ i) (i₁ ∧ i) i1)
-- --               (λ i₁ i → push (false , push (f , p , q) i₁) i) 
-- --     ts f p q i₁ i i' =
-- --       hcomp (λ k → λ {(i₁ = i0) → push (false , inl (BoolElimη f i' , p true , q true)) (i ∧ k)
-- --                      ; (i₁ = i1) → push (false , inr ((f false , BoolElimη p i' , q false))) (i ∧ k)
-- --                      ; (i = i0) → inl (false , f false , p true)
-- --                      ; (i' = i0) → FF (f true) (p true) (q true)
-- --                                        (f false) (p false) (q false) (i₁ ∨ ~ (i ∧ k)) (i₁ ∧ (i ∧ k)) i1
-- --                      ; (i' = i1) → push (false , push (f , p , q) i₁) (i ∧ k)})
-- --             (inl (false , f false , p true))
-- --   ΠR-extend-Bool←→← (push (true , inl (f , p)) i) j = push (true , (inl (BoolElimη f j , p))) i
-- --   ΠR-extend-Bool←→← (push (true , inr (f , p)) i) j = push (true , (inr (f , BoolElimη (fst p) j , snd p))) i
-- --   ΠR-extend-Bool←→← (push (true , push (f , p , q) i₁) i) i' = {!!} -- ts f p q i₁ i i'
-- --     where
-- --     ts' : (f1 : Bool → Bool) (p : (i₂ j : fst Bool*) → A i₂ j)
-- --       → (f2 : (x : Bool) → A x (f1 x))
-- --       → (q : (λ i → p i (f1 i)) ≡ f2)
-- --       → Cube {A = ΠR-bool}
-- --               (λ i i' → push (true , inl ((BoolElimη (λ i → f1 i , f2 i) i') , ((p false) , (funExt⁻ q false)))) i)
-- --               (λ i i' → push (true , inr ((f1 true , f2 true) , ((BoolElimη p i') , (funExt⁻ q true)))) i)
-- --               (λ i₁ i' → inl (true , (f1 true , f2 true) , p false))
-- --               (λ i₁ i' → FF-case₁ ((λ i → f1 i , f2 i)) p (funExt⁻ q) i' i₁)
-- --               (λ i₁ i → FF (f1 true , f2 true) (p true) (funExt⁻ q true) (f1 false , f2 false) (p false) (funExt⁻ q false) (i₁ ∧ i) (i₁ ∨ ~ i) i1)
-- --               λ i₁ i → push (true , push ((λ i → f1 i , f2 i) , p , funExt⁻ q) i₁) i
-- --     ts' f1 p = J> λ i₁ i i' →
-- --       hcomp (λ k → λ {(i₁ = i0) → {!!} -- push (true , inl (BoolElimη (λ i → f1 i , p i (f1 i)) i' , p false , refl)) i
-- --                      ; (i₁ = i1) → {!!} -- push (true , push ((BoolElimη (λ i → f1 i , p i (f1 i)) i') , ((BoolElim (p true) (p false)) , BoolElim refl refl)) k) i
-- --                      ; (i = i0) →  {!FF (f1 true , p true (f1 true)) (p true) refl (f1 false , p false (f1 false)) (p false) refl (i₁ ∧ i) (i₁ ∨ ~ i) k!} -- inl (true , f true , p false)
-- --                      ; (i = i1) → {!!} -- FF (f true) (p true) (q true) (f false) (p false) (q false) (~ k) k i1
-- --                      ; (i' = i0) → {!FF (f1 true , f2 true) (p true) (funExt⁻ q true) (f1 false , f2 false) (p false) (funExt⁻ q false) (i₁ ∧ (i ∧ k)) (i₁ ∨ ~ (i ∧ k)) i1!} -- FF (f1 true , p true (f1 true)) (p true) refl (f1 false , p false (f1 false)) (p false) refl (i₁ ∧ i) (i₁ ∨ ~ i) k
-- --                      ; (i' = i1) → {!!}})
-- --             {!!}


-- --     ts : (f : (i₂ : fst Bool*) → Σ-syntax (fst Bool*) (A i₂))
-- --          (p : (i₂ j : fst Bool*) → A i₂ j)
-- --          (q : (i₂ : fst Bool*) → p i₂ (f i₂ .fst) ≡ f i₂ .snd)
-- --       → Cube {A = ΠR-bool}
-- --               (λ i i' → push (true , inl ((BoolElimη f i') , ((p false) , (q false)))) i)
-- --               (λ i i' → push (true , inr ((f true) , ((BoolElimη p i') , (q true)))) i)
-- --               (λ i₁ i' → inl (true , f true , p false))
-- --               (λ i₁ i' → FF-case₁ f p q i' i₁)
-- --               (λ i₁ i → FF (f true) (p true) (q true) (f false) (p false) (q false) (i₁ ∧ i) (i₁ ∨ ~ i) i1)
-- --               λ i₁ i → push (true , push (f , p , q) i₁) i
-- --     ts f p q i₁ i i' =
-- --       hcomp (λ k → λ {(i₁ = i0) → {!!} --  push (true , inl (BoolElimη f i' , p false , q false)) i
-- --                      ; (i₁ = i1) → {!!} -- push (true , push (BoolElim (f true) (f false) , BoolElimη p i' , BoolElim (q true) (q false)) k) i
-- --                      ; (i = i0) →  {!!} -- inl (true , f true , p false) -- inl (true , f true , p false)
-- --                      ; (i' = i0) → {!!} -- FF (f true) (p true) (q true) (f false) (p false) (q false) ((i₁ ∨ ~ k) ∧ i) ((i₁ ∧ k) ∨ ~  i) i1
-- --                      ; (i' = i1) → Square-filler {A = ΠR-bool} (push (true , push (f , p , q) i₁)) (push (false , push (f , p , q) i₁)) i k i1 }) --push (true , push ({!!} , p , λ x → {!BoolElimη q ((k ∧ i₁) ∨ (i₁ ∨ ~ k)) x!}) (k ∧ i₁)) i})
-- --             {!FF (f true) (p true) (q true) (f false) (p false) (q false) i (~ i) i0!}
-- --     {-
-- --       hcomp (λ k → λ {(i₁ = i0) → push (true , inl (BoolElimη f i' , p false , q false)) i
-- --                      ; (i₁ = i1) → push (true , push (BoolElimη f i' , BoolElimη p i' , {! q true -- FF (f true) (p true) (q true) (f false) (p false) (q false) (i₁ ∧ i) (i₁ ∨ ~ i) k!}) k) i
-- --                      ; (i = i0) →  {!!} -- inl (true , f true , p false)
-- --                      ; (i = i1) → {!!} -- FF (f true) (p true) (q true) (f false) (p false) (q false) (~ k) k i1
-- --                      ; (i' = i0) → FF (f true) (p true) (q true) (f false) (p false) (q false) (i₁ ∧ i) (i₁ ∨ ~ i) k
-- --                      ; (i' = i1) → {!!}})
-- --             {!!}-}
-- --   {-
-- --   i₁ = i0 ⊢ push (false , inl (BoolElim a a₁ , b , x)) (~ i)
-- -- i₁ = i1 ⊢ push (true , inr (a , BoolElim b b₁ , x)) i
-- -- i = i0 ⊢ push (true , inl (BoolElim (fst a , snd a) a₁ , b₁ , x₁))
-- --          (~ i₁)
-- -- i = i1 ⊢ push (false , inr (a₁ , BoolElim b b₁ , x₁)) i₁
-- --   -}


-- -- --   ΠR-extend' : Type _
-- -- --   ΠR-extend' = Pushout PushTop'→left-push PushTop→ΠR-base'

-- -- --   ΠR-extend'Iso' : Iso ΠR-extend' ΠR-extend
-- -- --   ΠR-extend'Iso' = pushoutIso _ _ _ _
-- -- --     (isoToEquiv (PushTopIso'))
-- -- --     (idEquiv _)
-- -- --     (isoToEquiv (compIso ΠR-base-iso₂ (invIso ΠR-base-iso)))
-- -- --     (funExt (λ { (x , inl x₁) → refl ; (x , inr x₁) → refl ; (x , push a i) → {!a -- refl!}}))
-- -- --     (funExt λ { (i , inl x) → refl ; (i , inr x) → refl ; (i , push a i₁) → {!refl!}})
-- -- --       where
-- -- --       help : (x : fst I) (a : fat') → cong (PushTop'→left-push) (λ j → (x , push a j))
-- -- --                                      ≡ λ i → (PushTop→left-push ∘ PushTopIso' .Iso.fun) (x , push a i)
-- -- --       help x a = {!!} ∙ cong (cong PushTop→left-push) (rUnit λ j → x , {!push ? j!})

    

-- -- --   ΠR-extend'Iso : Iso ΠR-extend ΠR-extend'
-- -- --   ΠR-extend'Iso = pushoutIso _ _ _ _
-- -- --     (isoToEquiv (invIso PushTopIso'))
-- -- --     (idEquiv _)
-- -- --     (isoToEquiv (compIso ΠR-base-iso (invIso ΠR-base-iso₂)))
-- -- --     {!!}
-- -- --     (funExt λ { (i , inl x) → refl ; (i , inr x) → refl ; (i , push a i₁) → {!refl!}})




-- -- --   ΠR-extend-iso :
-- -- --     Iso ΠR-extend (ΠR I (λ i → Σ[ j ∈ fst J ] A i j)
-- -- --       (λ i → TotΠ (A i)) λ x f → f (fst x) ≡ snd x)
-- -- --   Iso.fun ΠR-extend-iso (inl (f , g , p)) = ab f g p
-- -- --   Iso.fun ΠR-extend-iso (inr (inl x)) = aa x
-- -- --   Iso.fun ΠR-extend-iso (inr (inr x)) = bb x
-- -- --   Iso.fun ΠR-extend-iso (inr (push (f , g , p) i)) = rr f g p i
-- -- --   Iso.fun ΠR-extend-iso (push (i , inl (f , g , p)) k) = ar i f g p (~ k)
-- -- --   Iso.fun ΠR-extend-iso (push (i , inr (f , g , p)) k) = br i f g p k
-- -- --   Iso.fun ΠR-extend-iso (push (i , push (f , g , p) i₁) k) = {!rr' i f g p (~ k) i₁!}
-- -- --   Iso.inv ΠR-extend-iso = {!!}
-- -- --   Iso.rightInv ΠR-extend-iso = {!!}
-- -- --   Iso.leftInv ΠR-extend-iso = {!!}






-- -- -- -- module _ {ℓ ℓ' ℓ'' : Level} (I : RP∞) (A A' : Type ℓ') (B : Type ℓ'') (e : Iso A A')
-- -- -- --    (A-d : fst I → Type ℓ')
-- -- -- --    (B-d : fst I → Type ℓ'')
-- -- -- --    (A-eval : (i : fst I) (f : A) → A-d i)
-- -- -- --    (A-eval' : (i : fst I) (f : A') → A-d i)
-- -- -- --    (A-agr : (i : fst I) (f : A) → A-eval i f ≡ A-eval' i (Iso.fun e f)) 
-- -- -- --    (B-eval : (i : fst I) (f : B) → B-d i)
-- -- -- --    (R : {i : fst I} → A-d i → B-d i → Type ℓ) where

-- -- -- --    private
-- -- -- --      Ty1 = ΠRgen I A B A-d B-d A-eval B-eval R
-- -- -- --      Ty2 = ΠRgen I A' B A-d B-d A-eval' B-eval R

-- -- -- --    ref-iso : Iso Ty1 Ty2
-- -- -- --    Iso.fun ref-iso (aa* x) = aa* (Iso.fun e x)
-- -- -- --    Iso.fun ref-iso (bb* x) = bb* x
-- -- -- --    Iso.fun ref-iso (ab* i x x₁) = ab* i x x₁
-- -- -- --    Iso.fun ref-iso (ar* i x b x₁ i₁) = hcomp {!!} (ar* i (Iso.fun e x) b {!subst R!} i₁)
-- -- -- --    Iso.fun ref-iso (br* i a b x i₁) = {!!}
-- -- -- --    Iso.fun ref-iso (rr* a b r i) = {!!}
-- -- -- --    Iso.fun ref-iso (rr** i a b r j i₁) = {!!}
-- -- -- --    Iso.inv ref-iso = {!!}
-- -- -- --    Iso.rightInv ref-iso = {!!}
-- -- -- --    Iso.leftInv ref-iso = {!!}



-- -- -- -- module _ {ℓ :  Level} (I J : RP∞) (A : fst I → fst J → Type ℓ) where
-- -- -- --   ΠR-J : Type _
-- -- -- --   ΠR-J = ΠR I (λ i → Σ (fst J) (A i)) (λ i → TotΠ (A i)) λ x f → f (fst x) ≡ snd x

-- -- -- --   πr-gen : Type _
-- -- -- --   πr-gen = ΠRgen I (TotΠ λ i → Σ (fst J) (A i)) (TotΠ (λ i → TotΠ (A i)))
-- -- -- --                    (λ i → Σ (fst J) (A i)) (λ i → TotΠ (A i))
-- -- -- --                    (λ i f → f i) (λ i f → f i)
-- -- -- --                    λ x f → f (fst x) ≡ snd x

-- -- -- --   aT = Σ[ r ∈ fst J ⊎ (fst I ≃ fst J) ] ((i : fst I) → A i (fst (2-eltFun {I = I} {J = J}) r i))


-- -- -- --   sect : (i : fst I) → aT → Σ (fst J) (A i)
-- -- -- --   sect i (inl x , p) = x , p i
-- -- -- --   sect i (inr x , p) = fst x i , p i


-- -- -- --   πr-gen' : {!ΠRgen I (TotΠ λ i → Σ (fst J) (A i)) (TotΠ (λ i → TotΠ (A i)))
-- -- -- --                    (λ i → Σ (fst J) (A i)) (λ i → TotΠ (A i))
-- -- -- --                    (λ i f → f i) (λ i f → f i)
-- -- -- --                    λ x f → f (fst x) ≡ snd x!}
-- -- -- --   πr-gen' = ΠRgen I aT (TotΠ (λ i → TotΠ (A i)))
-- -- -- --                    (λ i → Σ (fst J) (A i)) (λ i → TotΠ (A i))
-- -- -- --                    sect (λ i f → f i)
-- -- -- --                    λ x f → f (fst x) ≡ snd x

-- -- -- --   πr-gen-iso : Iso πr-gen ΠR-J
-- -- -- --   πr-gen-iso = invIso (ΠR≡ _ _ _ _)

-- -- -- --   myIs : aT → joinRD J I λ j i → A i j
-- -- -- --   myIs (inl j , p) = inlR (j , inrR p) 
-- -- -- --   myIs (inr x , p) =
-- -- -- --     inrR λ j
-- -- -- --       → inlR (invEq x j , subst (A (invEq x j)) (secEq x j)
-- -- -- --            (p (invEq x j)))

-- -- -- --   m2 : (i : fst I) (j : fst J) (aij : A i j) (f : TotΠ (A (not* I i)))
-- -- -- --     → (i : fst I) → A i j
-- -- -- --   m2 i j aij f = CasesRP I i aij (f j)

-- -- -- --   m2≡ : (i : fst I) (b : TotΠ (A (not* I i))) (r : aT)
-- -- -- --     → b (Iso.inv (TotAIso I J {A = A}) r (not* I i) .fst)
-- -- -- --      ≡ Iso.inv (TotAIso I J {A = A}) r (not* I i) .snd
-- -- -- --     → myIs r ≡ inlR (Iso.inv (TotAIso I J {A = A}) r i .fst
-- -- -- --               , inrR (m2 i (Iso.inv (TotAIso I J {A = A}) r i .fst)
-- -- -- --                 (Iso.inv (TotAIso I J {A = A}) r i .snd) b))
-- -- -- --   m2≡ i b (inl x , y) r = cong inlR (ΣPathP (refl , (cong inrR {!!})))
-- -- -- --   m2≡ i b (inr x , y) r = {!inlR (fst x i , inrR (m2 i (fst x i) (y i) b))!}
-- -- -- --     ∙ sym (push* (fst x i , inrR {!!}) {!!} {!!}) -- sym (push* ((fst x i) , inrR (m2 i (fst x i) (y i) b)) (λ j → inlR (not* I i , b j)) {!r!})

-- -- -- --   whata : ΠR-J ≃ ((i : fst I) → joinR J (A i))
-- -- -- --   whata = {!!}

-- -- -- --   l3 : (a : aT) (b : TotΠ (λ i₁ → TotΠ (A i₁)))
-- -- -- --      → ((i : fst I) → b i (2-eltFun {I = I} {J = J} .fst (fst a) i) ≡ snd a i)
-- -- -- --      → Path (joinRD J I (λ j i₁ → A i₁ j)) (myIs a) (inrR (λ j → inrR (λ i₁ → b i₁ j)))
-- -- -- --   l3 (inl x , l) b k i = push* ((x , inrR l))
-- -- -- --                                ((λ i₁ → inrR (λ i₂ → b i₂ i₁)))
-- -- -- --                                (λ i → inrR λ j → k j i) i
-- -- -- --   l3 (inr x , l) b k i = inrR {!!}

-- -- -- --   ΠR-J→ : ΠR-J → joinRD J I λ j i → A i j
-- -- -- --   ΠR-J→ (aa f) = myIs (Iso.fun (TotAIso I J) f)
-- -- -- --   ΠR-J→ (bb f) = inrR λ j → inrR λ i → f i j
-- -- -- --   ΠR-J→ (ab i (j , aij) f) = inlR (j , inrR (m2 i j aij f))
-- -- -- --   ΠR-J→ (ar i f b r i₁) = {!!}
-- -- -- --   ΠR-J→ (br i a b r i₁) = {!i -- b -- Iso.fun (TotAIso I J) f .fst!}
-- -- -- --   ΠR-J→ (rr a b r i) = l3 (f1 I J a) b (λ i → {!!}) i
-- -- -- --   ΠR-J→ (rr' i a b r j i₁) = {!f1 I J a)!}

-- -- -- --   FFR : (i : fst I) → joinR J (A i) → joinRD J I λ j i → A i j
-- -- -- --   FFR i (inlR (j , a)) = inlR (j , inlR (i , a))
-- -- -- --   FFR i (inrR x) = inrR λ j → inlR (i , x j)
-- -- -- --   FFR i (push* (j , a) b x i₁) =
-- -- -- --     push* (j , inlR (i , a)) (λ j → inlR (i , b j))
-- -- -- --       (λ t → inlR (i , x t)) i₁

-- -- -- --   FFR≡ : (i : fst I) (r : ΠR-J) (a : joinR J (A i)) → fst whata r i ≡ a
-- -- -- --     → FFR i a ≡ ΠR-J→ r
-- -- -- --   FFR≡ i r = J> {!!}
  
-- -- -- --   maiin : joinRD I J A → joinRD J I λ j i → A i j
-- -- -- --   maiin (inlR (i , a)) = FFR i a
-- -- -- --   maiin (inrR f) = ΠR-J→ (invEq whata f)
-- -- -- --   maiin (push* (i , a) b x i₁) = FFR≡ i (invEq whata b) a (funExt⁻ (secEq whata b) i ∙ x) i₁

  

-- -- -- -- -- open import Cubical.HITs.PropositionalTruncation

-- -- -- -- -- module _ {ℓ ℓ' : Level} (S : Type ℓ) where
-- -- -- -- --   data genr (B : S → Type ℓ') : Type (ℓ-max ℓ ℓ') where
-- -- -- -- --     mid : ((x : _) → B x) → genr B
-- -- -- -- --     corn : (x : S) (t : B x) → genr B
-- -- -- -- --     mide : (x : S) (f : (x : S) → B x) → mid f ≡ corn x (f x)

-- -- -- -- -- module _ {ℓ ℓ' ℓ'' : Level} (A : Type ℓ) (S : A → Type ℓ') where
-- -- -- -- --   genJ : (a : A) (B : S a → Type ℓ'') → Type (ℓ-max ℓ' ℓ'')
-- -- -- -- --   genJ a B = genr (S a) B

-- -- -- -- -- genJ* : {!!}
-- -- -- -- -- genJ* = {!!}


-- -- -- -- -- -- -- åå : {!!}
-- -- -- -- -- -- -- åå = {!!}

-- -- -- -- -- -- Two : ∀ {ℓ ℓ' ℓ''} (A : Type ℓ) (S : A → Type ℓ') (a b : A) (B : S a → S b → Type ℓ'')
-- -- -- -- -- --   → Type _
-- -- -- -- -- -- Two A S a b B = genJ A S a λ a → genJ A S b λ b → B a b





-- -- -- -- -- -- Two↔' : ∀ {ℓ ℓ' ℓ''}  {A : Type ℓ} (A' : Type ℓ) (p : A ≡ A')
-- -- -- -- -- --   → (S : A → Type ℓ')
-- -- -- -- -- --   → (S' : A' → Type ℓ')
-- -- -- -- -- --   → (a b : A)
-- -- -- -- -- --   → (a' : A')
-- -- -- -- -- --   → transport p a ≡ a'
-- -- -- -- -- --   → (b' : A')
-- -- -- -- -- --   → transport p b ≡ b'
-- -- -- -- -- --   → (B : S a → S b → Type ℓ'')
-- -- -- -- -- --   → (f1 : S' a' ≃ S b)
-- -- -- -- -- --   → (f2  : S' b' ≃ S a)
-- -- -- -- -- --   → Two A S a b B
-- -- -- -- -- --   → Two A' S' a' b' λ a* b* → B (f2 .fst b*) (f1 .fst a*)
-- -- -- -- -- -- Two↔' {ℓ'' = ℓ''} {A = A} = J> λ S1 S2 a b
-- -- -- -- -- --   → J> (J>
-- -- -- -- -- --     λ B
-- -- -- -- -- --     →  transport (λ i
-- -- -- -- -- --     → (f1 : S2 (transportRefl a (~ i)) ≃ S1 b)
-- -- -- -- -- --       (f2 : S2 (transportRefl b (~ i)) ≃ S1 a) →
-- -- -- -- -- --       Two A S1 a b B →
-- -- -- -- -- --       Two A S2 (transportRefl a (~ i)) (transportRefl b (~ i))
-- -- -- -- -- --       (λ a₁ b₁ → B (f2 .fst b₁) (f1 .fst a₁)))
-- -- -- -- -- --       λ e1 e2 → kaha (S1 a) (S1 b) (S2 b) e2 (S2 a) e1 B)
-- -- -- -- -- --   where
-- -- -- -- -- --   module _ {ℓ : Level} (S1a S1b : Type ℓ)  where
-- -- -- -- -- --     kaha : (S2b : Type ℓ) → (f1 : S2b ≃ S1a)
-- -- -- -- -- --       → (S2a : Type ℓ) (f2 : S2a ≃ S1b)
-- -- -- -- -- --       → (B : S1a → S1b → Type ℓ'')
-- -- -- -- -- --       → genr S1a (λ a' → genr S1b (B a'))
-- -- -- -- -- --       → genr S2a λ a' → genr S2b λ b → B (fst f1 b) (fst f2 a')
-- -- -- -- -- --     kaha = {!!}
-- -- -- -- -- --     cool : {!!}
-- -- -- -- -- --     cool = {!!}
    

-- -- -- -- -- -- Two↔* : ∀ {ℓ ℓ' ℓ''}  {A : Type ℓ} (A' : Type ℓ) (p : A ≡ A')
-- -- -- -- -- --   → (S : A → Type ℓ')
-- -- -- -- -- --   → (S' : A' → Type ℓ')
-- -- -- -- -- --   → (pp : PathP (λ i → p i → Type ℓ') S S')
-- -- -- -- -- --   → (a b : A)
-- -- -- -- -- --   → (a' : A')
-- -- -- -- -- --   → transport p a ≡ a'
-- -- -- -- -- --   → (b' : A')
-- -- -- -- -- --   → transport p b ≡ b'
-- -- -- -- -- --   → (B : S a → S b → Type ℓ'')
-- -- -- -- -- --   → (f1 : S' a' ≃ S b)
-- -- -- -- -- --   → (f2  : S' b' ≃ S a)
-- -- -- -- -- --   → Two A S a b B → Two A' S' a' b' λ a b → B (f2 .fst b) (f1 .fst a)
-- -- -- -- -- -- Two↔* {A = A} =
-- -- -- -- -- --   J> λ S → J> λ a b
-- -- -- -- -- --   → J> (J> λ B
-- -- -- -- -- --   → transport (λ i
-- -- -- -- -- --     → (f1 : S (transportRefl a (~ i)) ≃ S b)
-- -- -- -- -- --       (f2 : S (transportRefl b (~ i)) ≃ S a) →
-- -- -- -- -- --       Two A S a b B →
-- -- -- -- -- --       Two A S (transportRefl a (~ i)) (transportRefl b (~ i))
-- -- -- -- -- --       (λ a₁ b₁ → B (f2 .fst b₁) (f1 .fst a₁))) -- () (f1 .fst a₁)))
-- -- -- -- -- --       λ f1 f2 → subst (Two A S a b) (funExt {!p → fu!}))
      
-- -- -- -- -- -- Two↔ : ∀ {ℓ ℓ' ℓ''}  {A : Type ℓ} (A' : Type ℓ) (p : A ≡ A')
-- -- -- -- -- --   → (S : A → Type ℓ')
-- -- -- -- -- --   → (S' : A' → Type ℓ')
-- -- -- -- -- --   → (pp : PathP (λ i → p i → Type ℓ') S S')
-- -- -- -- -- --   → (a b : A)
-- -- -- -- -- --   → (a' : A')
-- -- -- -- -- --   → transport p a ≡ a'
-- -- -- -- -- --   → (b' : A')
-- -- -- -- -- --   → transport p b ≡ b'
-- -- -- -- -- --   → (B : S a → S b → Type ℓ'')
-- -- -- -- -- --   → (f1 : S' a' → S a)
-- -- -- -- -- --   → (f2  : S' b' → S b)
-- -- -- -- -- --   → Two A S a b B → Two A' S' a' b' λ a b → B (f1 a) (f2 b)
-- -- -- -- -- -- Two↔ {A = A} =
-- -- -- -- -- --   J> λ S → J> λ a b
-- -- -- -- -- --   → J> (J> λ B
-- -- -- -- -- --   → transport (λ i
-- -- -- -- -- --     → (f1 : S (transportRefl a (~ i)) → S a)
-- -- -- -- -- --       (f2 : S (transportRefl b (~ i)) → S b) →
-- -- -- -- -- --       Two A S a b B →
-- -- -- -- -- --       Two A S (transportRefl a (~ i)) (transportRefl b (~ i))
-- -- -- -- -- --       (λ a₁ b₁ → B (f1 a₁) (f2 b₁)))
-- -- -- -- -- --       λ f1 f2 → λ { (mid x) → {!!}
-- -- -- -- -- --                    ; (corn x x₁) → {!!}
-- -- -- -- -- --                    ; (mide x f i) → {!!}})
-- -- -- -- -- -- {-
-- -- -- -- -- -- Goal: (f1 : S (transport refl a) → S a)
-- -- -- -- -- --       (f2 : S (transport refl b) → S b) →
-- -- -- -- -- --       Two A S a b B →
-- -- -- -- -- --       Two A S (transport refl a) (transport refl b)
-- -- -- -- -- --       (λ a₁ b₁ → B (f1 a₁) (f2 b₁))
-- -- -- -- -- -- -}

-- -- -- -- -- -- module _ (X Y : RP∞) (A : fst X → fst Y → Type) where
-- -- -- -- -- --   p1 : (X +∞ Y) +∞ Y ≡ X
-- -- -- -- -- --   p1 = sym (+∞-assoc X Y Y) ∙ cong (X +∞_) (rCancel∞ Y) ∙ +∞rId X

-- -- -- -- -- --   p2 : ((X +∞ Y) +∞ X) ≡ Y
-- -- -- -- -- --   p2 = cong (_+∞ X) (+∞-comm X Y) ∙ sym (+∞-assoc Y X X) ∙ cong (Y +∞_) (rCancel∞ X) ∙ +∞rId Y

-- -- -- -- -- --   T12 : Two RP∞ fst X Y A
-- -- -- -- -- --      → Two RP∞ fst Y X λ y x → A x y
-- -- -- -- -- --   T12 = ps
-- -- -- -- -- --     where
-- -- -- -- -- --     l : RP∞ ≡ RP∞
-- -- -- -- -- --     l = isoToPath (+∞-iso (X +∞ Y))
-- -- -- -- -- --     t = _+∞_

-- -- -- -- -- --     ps : _
-- -- -- -- -- --     ps = Two↔' RP∞ l fst fst X Y Y (transportRefl _ ∙ p2) X (transportRefl _ ∙ p1) A (idEquiv (fst Y)) (idEquiv (fst X))


-- -- -- -- -- --   T1 : Two RP∞ fst X Y A → Two RP∞ (λ x → fst ((X +∞ Y) +∞ x)) Y X λ t r → A (subst fst p1 t) (subst fst p2 r)
-- -- -- -- -- --   T1 =
-- -- -- -- -- --     Two↔ {A = RP∞} RP∞ l fst _ (toPathP refl) X Y Y (transportRefl _ ∙ p2) X (transportRefl _ ∙ p1) A
-- -- -- -- -- --       {!!}
-- -- -- -- -- --       {!!}
-- -- -- -- -- --     where
-- -- -- -- -- --     l : RP∞ ≡ RP∞
-- -- -- -- -- --     l = isoToPath (+∞-iso (X +∞ Y))
-- -- -- -- -- --     t = _+∞_

-- -- -- -- -- --   pa2 : (Two RP∞ (λ x → fst ((X +∞ Y) +∞ x)) Y X λ t r → A (subst fst p1 t) (subst fst p2 r))
-- -- -- -- -- --       ≡ Two RP∞ fst Y X λ y x → A x y
-- -- -- -- -- --   pa2 i = Two RP∞ {!!} {!l i!} {!!} {!!}
-- -- -- -- -- --     where
-- -- -- -- -- --     l : RP∞ ≡ RP∞
-- -- -- -- -- --     l = isoToPath (+∞-iso (X +∞ Y))
-- -- -- -- -- --     t = _+∞_

-- -- -- -- -- --     p4 : {!!}
-- -- -- -- -- --     p4 = {!!}
  
-- -- -- -- -- --   elim4 : (Two RP∞ (λ x → fst ((X +∞ Y) +∞ x)) Y X λ t r → A (subst fst p1 t) (subst fst p2 r)) → RP∞
-- -- -- -- -- --   elim4 (mid x) = {!!}
-- -- -- -- -- --   elim4 (corn x adk) = {!!}
-- -- -- -- -- --   elim4 (mide x f i) = {!!}

-- -- -- -- -- -- --   T1 = Two↔ {A = RP∞} RP∞ l fst fst (toPathP (funExt λ x → cong fst (ms x)))
-- -- -- -- -- -- --     X Y Y (transportRefl _ ∙ cong (_+∞ X) (+∞-comm X Y) ∙ sym (+∞-assoc Y X X) ∙ cong (Y +∞_) (rCancel∞ X) ∙ +∞rId Y) X {!!} A (idfun _) (idfun _)
-- -- -- -- -- -- --     where
-- -- -- -- -- -- --     ms : (x : RP∞) → (X +∞ Y) +∞ x ≡ x
-- -- -- -- -- -- --     ms = {!!}

-- -- -- -- -- -- --     l : RP∞ ≡ RP∞
-- -- -- -- -- -- --     l = isoToPath (+∞-iso (X +∞ Y))
-- -- -- -- -- -- --     t = _+∞_
  
-- -- -- -- -- -- -- why : {!transport (λ i → l i → Type) (λ r → fst r) x!}
-- -- -- -- -- -- -- why = {!!}


-- -- -- -- -- -- -- -- data abr' (A : Bool → Type) : Type where
-- -- -- -- -- -- -- --   ins' : (b : Bool) → A b → A (not b) → abr' A
-- -- -- -- -- -- -- --   gl'₁ : (a : A true) (b : A false) → ins' true a b ≡ ins' false b a
-- -- -- -- -- -- -- --   gl'₂ : (a : A false) (b : A true) → ins' false a b ≡ ins' true b a

-- -- -- -- -- -- -- --   -- xs


-- -- -- -- -- -- -- --   -- (x : X) × ((x : X) → A x)  --->
-- -- -- -- -- -- -- --    --     |
-- -- -- -- -- -- -- --     --    v
-- -- -- -- -- -- -- --   -- Σ[ x ∈ X ] (A x × A ?) ,,, Σ[ x ∈ A x ]
-- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- (A × B) + (A × B) → (A + B)
-- -- -- -- -- -- -- --        |
-- -- -- -- -- -- -- --        |
-- -- -- -- -- -- -- --        v
-- -- -- -- -- -- -- -- (A × B) + (A × B)

-- -- -- -- -- -- -- -- A → B
-- -- -- -- -- -- -- -- ||   ↓
-- -- -- -- -- -- -- -- A → C
-- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- InS : ∀ {ℓ} (X : RP∞) (A : Type ℓ) → Type ℓ
-- -- -- -- -- -- -- -- InS X A = join A (fst X)



-- -- -- -- -- -- -- -- data JJ {ℓ : Level} (X : RP∞) (A : fst X → Type ℓ) : Type ℓ where
-- -- -- -- -- -- -- --   mid : (f : (x : fst X) → A x) → JJ X A
-- -- -- -- -- -- -- --   sf : (x : fst X) → A x → JJ X A
-- -- -- -- -- -- -- --   sl : (x : fst X) (f : (x : fst X) → A x) → mid f ≡ sf x (f x)

-- -- -- -- -- -- -- -- le' : (X : RP∞) (A : fst X → Pointed₀)
-- -- -- -- -- -- -- --   → JJ X (fst ∘ A)  → InS X (SM X A)
-- -- -- -- -- -- -- -- le' X A (mid f) = inl (inr f)
-- -- -- -- -- -- -- -- le' X A (sf x t) = inr x
-- -- -- -- -- -- -- -- le' X A (sl x f i) = push (inr f) x i


-- -- -- -- -- -- -- -- Bool→ : ∀ {ℓ} {A : Bool → Type ℓ} → A true → A false → (x : _) → A x
-- -- -- -- -- -- -- -- Bool→ x y false = y
-- -- -- -- -- -- -- -- Bool→ x y true = x

-- -- -- -- -- -- -- -- BoolDiag : ∀ {ℓ } {A : Type ℓ} (x : A) → Bool→ {A = λ _ → A} x x ≡ λ _ → x
-- -- -- -- -- -- -- -- BoolDiag x i false = x
-- -- -- -- -- -- -- -- BoolDiag x i true = x

-- -- -- -- -- -- -- -- Boolβ : ∀ {ℓ } {A : Bool → Type ℓ} (f : (x : Bool) → A x)
-- -- -- -- -- -- -- --   → Bool→ {A = A} (f true) (f false) ≡ f
-- -- -- -- -- -- -- -- Boolβ f i false = f false
-- -- -- -- -- -- -- -- Boolβ f i true = f true

-- -- -- -- -- -- -- -- module _ (A : Type) where
-- -- -- -- -- -- -- --   InS→Susp : Iso (InS Bool* A) (Susp A)
-- -- -- -- -- -- -- --   InS→Susp = invIso Susp-iso-joinBool


-- -- -- -- -- -- -- -- module _ (A : Bool → Pointed₀) where
-- -- -- -- -- -- -- --   JJ-Bool→ : JJ Bool* (fst ∘ A) → join (A true .fst) (A false .fst)
-- -- -- -- -- -- -- --   JJ-Bool→ (mid f) = inl (f true)
-- -- -- -- -- -- -- --   JJ-Bool→ (sf false x₁) = inr x₁
-- -- -- -- -- -- -- --   JJ-Bool→ (sf true x₁) = inl x₁
-- -- -- -- -- -- -- --   JJ-Bool→ (sl false f i) = push (f true) (f false) i
-- -- -- -- -- -- -- --   JJ-Bool→ (sl true f i) = inl (f true)

-- -- -- -- -- -- -- --   JJ-Bool← : join (A true .fst) (A false .fst) → JJ Bool* (fst ∘ A)
-- -- -- -- -- -- -- --   JJ-Bool← (inl x) = sf true x
-- -- -- -- -- -- -- --   JJ-Bool← (inr x) = sf false x
-- -- -- -- -- -- -- --   JJ-Bool← (push a b i) = (sym (sl true (Bool→ a b)) ∙ sl false (Bool→ a b)) i

-- -- -- -- -- -- -- --   JJ-Bool→← : (x : join (A true .fst) (A false .fst)) → JJ-Bool→ (JJ-Bool← x) ≡ x
-- -- -- -- -- -- -- --   JJ-Bool→← (inl x) = refl
-- -- -- -- -- -- -- --   JJ-Bool→← (inr x) = refl
-- -- -- -- -- -- -- --   JJ-Bool→← (push a b i) j = h j i
-- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- --     h : cong JJ-Bool→ (sym (sl true (Bool→ a b)) ∙ sl false (Bool→ a b)) ≡ push a b
-- -- -- -- -- -- -- --     h = cong-∙ JJ-Bool→ (sym (sl true (Bool→ a b))) (sl false (Bool→ a b))
-- -- -- -- -- -- -- --         ∙ sym (lUnit _)

-- -- -- -- -- -- -- --   JJ-Bool←→ : (x : JJ Bool* (fst ∘ A) ) → JJ-Bool← (JJ-Bool→ x) ≡ x
-- -- -- -- -- -- -- --   JJ-Bool←→ (mid f) = sym (sl true f)
-- -- -- -- -- -- -- --   JJ-Bool←→ (sf false x₁) = refl
-- -- -- -- -- -- -- --   JJ-Bool←→ (sf true x₁) = refl
-- -- -- -- -- -- -- --   JJ-Bool←→ (sl false f i) j =
-- -- -- -- -- -- -- --     hcomp (λ k → λ {(i = i0) → sl true f (~ j)
-- -- -- -- -- -- -- --                    ; (i = i1) → sf false (f false)
-- -- -- -- -- -- -- --                    ; (j = i0) → (sym (sl true (Boolβ f (~ k))) ∙ sl false (Boolβ f (~ k))) i
-- -- -- -- -- -- -- --                    ; (j = i1) → sl false f i})
-- -- -- -- -- -- -- --           (hcomp (λ k → λ {(i = i0) → sl true f (~ j)
-- -- -- -- -- -- -- --                    ; (i = i1) → sl false f k
-- -- -- -- -- -- -- --                    ; (j = i1) → sl false f (i ∧ k)})
-- -- -- -- -- -- -- --                  (sl true f (~ i ∧ ~ j)))
-- -- -- -- -- -- -- --   JJ-Bool←→ (sl true f i) j = sl true f (~ j ∨ i)

-- -- -- -- -- -- -- --   JJ-Bool-Iso : Iso (JJ Bool* (fst ∘ A)) (join (A true .fst) (A false .fst))
-- -- -- -- -- -- -- --   Iso.fun JJ-Bool-Iso = JJ-Bool→
-- -- -- -- -- -- -- --   Iso.inv JJ-Bool-Iso = JJ-Bool←
-- -- -- -- -- -- -- --   Iso.rightInv JJ-Bool-Iso = JJ-Bool→←
-- -- -- -- -- -- -- --   Iso.leftInv JJ-Bool-Iso = JJ-Bool←→



-- -- -- -- -- -- -- -- le : (X : RP∞) (A : fst X → Pointed₀)
-- -- -- -- -- -- -- --   → InS X (SM X A) → JJ X (fst ∘ A) 
-- -- -- -- -- -- -- -- le X A (inl (inl x)) = sf x (A x .snd)
-- -- -- -- -- -- -- -- le X A (inl (inr x)) = mid x
-- -- -- -- -- -- -- -- le X A (inl (push (x , f) i)) =
-- -- -- -- -- -- -- --   hcomp (λ j → λ {(i = i0) → sf x {!CasesRPβ X x f (snd (A (not* X x))) .fst!}
-- -- -- -- -- -- -- --                  ; (i = i1) → {!!}})
-- -- -- -- -- -- -- --         (sl x (CasesRP X x f (snd (A (not* X x)))) (~ i))
-- -- -- -- -- -- -- -- le X A (inr x) = sf x (A x .snd)
-- -- -- -- -- -- -- -- le X A (push a b i) = {!o!}

-- -- -- -- -- -- -- -- t2 : (X : RP∞) (A : fst X → Pointed₀) →
-- -- -- -- -- -- -- --   JJ X (fst ∘ A) → Path (SM X A) (inr (λ x → A x .snd)) (inr (λ x → A x .snd))
-- -- -- -- -- -- -- -- t2 X A (mid f) = {!!} ∙∙ push ({!!} , {!!}) ∙∙ {!!}
-- -- -- -- -- -- -- -- t2 X A (sf x x₁) = {!!}
-- -- -- -- -- -- -- -- t2 X A (sl x f i) = {!!}

-- -- -- -- -- -- -- -- SuspSM* : (X : RP∞) (A : fst X → Pointed₀)
-- -- -- -- -- -- -- --   → SM X A
-- -- -- -- -- -- -- --   → Path (JJ X (fst ∘ A)) (mid (λ x → A x .snd)) (mid (λ x → A x .snd))
-- -- -- -- -- -- -- -- SuspSM* X A (inl x) = refl
-- -- -- -- -- -- -- -- SuspSM* X A (inr f) = {!!}
-- -- -- -- -- -- -- -- SuspSM* X A (push a i) = {!!}

-- -- -- -- -- -- -- -- SuspSM : (X : RP∞) (A : fst X → Pointed₀) → Susp (SM X A) → JJ X (fst ∘ A) -- SM
-- -- -- -- -- -- -- -- SuspSM X A north = {!!} 
-- -- -- -- -- -- -- -- SuspSM X A south = {!!}
-- -- -- -- -- -- -- -- SuspSM X A (merid a i) = {!a!}

-- -- -- -- -- -- -- -- pushoutidf : (A B : Type) (f : A → B) → Iso (Pushout (idfun A) f) B
-- -- -- -- -- -- -- -- Iso.fun (pushoutidf A B f) (inl x) = f x
-- -- -- -- -- -- -- -- Iso.fun (pushoutidf A B f) (inr x) = x
-- -- -- -- -- -- -- -- Iso.fun (pushoutidf A B f) (push a i) = f a
-- -- -- -- -- -- -- -- Iso.inv (pushoutidf A B f) = inr
-- -- -- -- -- -- -- -- Iso.rightInv (pushoutidf A B f) x = refl
-- -- -- -- -- -- -- -- Iso.leftInv (pushoutidf A B f) (inl x) = sym (push x)
-- -- -- -- -- -- -- -- Iso.leftInv (pushoutidf A B f) (inr x) = refl
-- -- -- -- -- -- -- -- Iso.leftInv (pushoutidf A B f) (push a i) j = push a (~ j ∨ i)


-- -- -- -- -- -- -- -- mafat : {!!}
-- -- -- -- -- -- -- -- mafat = {!!}

-- -- -- -- -- -- -- -- st : (X : RP∞) (x : fst X) → Bool → fst X
-- -- -- -- -- -- -- -- st X x false = not* X x
-- -- -- -- -- -- -- -- st X x true = x

-- -- -- -- -- -- -- -- st-id : (X : RP∞) (x : fst X) → isEquiv (st X x)
-- -- -- -- -- -- -- -- st-id = uncurry λ X → PT.elim (λ _ → isPropΠ λ _ → isPropIsEquiv _)
-- -- -- -- -- -- -- --   (EquivJ (λ X e → (p : _) → isEquiv (st (X , ∣ e ∣₁) p))
-- -- -- -- -- -- -- --     λ { false → subst isEquiv (funExt (λ { false → refl ; true → refl})) (notEquiv .snd)
-- -- -- -- -- -- -- --       ; true → subst isEquiv (funExt (λ { false → refl ; true → refl})) (idIsEquiv Bool)})

-- -- -- -- -- -- -- -- FF : (X : RP∞) → (fst X) → (fst X ≃ Bool)
-- -- -- -- -- -- -- -- FF X x = invEquiv (_ , st-id X x)

-- -- -- -- -- -- -- -- GG : (X : RP∞) → (fst X ≃ Bool) → (fst X)
-- -- -- -- -- -- -- -- GG X t = invEq t true

-- -- -- -- -- -- -- -- tta : (X : RP∞) → Iso (fst X) (fst X ≃ Bool)
-- -- -- -- -- -- -- -- Iso.fun (tta X) = FF X
-- -- -- -- -- -- -- -- Iso.inv (tta X) = GG X
-- -- -- -- -- -- -- -- Iso.rightInv (tta (X , e)) t =
-- -- -- -- -- -- -- --   (λ i → FF (X , squash₁ e ∣ t ∣₁ i) (GG (X , squash₁ e ∣ t ∣₁ i) t))
-- -- -- -- -- -- -- --   ∙ EquivJ (λ Y e → FF (Y , ∣ e ∣₁) (GG (Y , ∣ e ∣₁) e) ≡ e)
-- -- -- -- -- -- -- --            (Σ≡Prop (λ _ → isPropIsEquiv _) refl) t
-- -- -- -- -- -- -- -- Iso.leftInv (tta X) a = refl

-- -- -- -- -- -- -- -- cf : (X : RP∞) → Iso (fst X) (X ≡ Bool*)
-- -- -- -- -- -- -- -- cf X = compIso (tta X) (compIso (invIso (equivToIso univalence)) h)
-- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- --   h : Iso (fst X ≡ Bool) (X ≡ Bool*)
-- -- -- -- -- -- -- --   Iso.fun h = Σ≡Prop λ _ → squash₁
-- -- -- -- -- -- -- --   Iso.inv h = cong fst
-- -- -- -- -- -- -- --   Iso.rightInv h e = ΣSquareSet (λ _ → isProp→isSet squash₁) λ _ i → fst (e i)
-- -- -- -- -- -- -- --   Iso.leftInv h e = refl


-- -- -- -- -- -- -- -- module _ {ℓ : Level} (X : RP∞) (A : Pointed ℓ) where
-- -- -- -- -- -- -- --   Ω* : Type ℓ
-- -- -- -- -- -- -- --   Ω* = Σ[ a ∈ fst A ] (fst X → pt A ≡ a)

-- -- -- -- -- -- -- --   Ω*∙ : Pointed ℓ
-- -- -- -- -- -- -- --   Ω*∙ = Ω* , (pt A) , (λ _ → refl)


-- -- -- -- -- -- -- --   Susp* : Pointed ℓ
-- -- -- -- -- -- -- --   Susp* = join (fst A) (fst X) , inl (pt A)


-- -- -- -- -- -- -- -- Ω*-bool : ∀ {ℓ} (A : Pointed ℓ) → Iso (Ω* Bool* A) (fst (Ω A))
-- -- -- -- -- -- -- -- Iso.fun (Ω*-bool A) (b , q) = q true ∙ sym (q false)
-- -- -- -- -- -- -- -- fst (Iso.inv (Ω*-bool A) t) = pt A
-- -- -- -- -- -- -- -- snd (Iso.inv (Ω*-bool A) t) false = refl
-- -- -- -- -- -- -- -- snd (Iso.inv (Ω*-bool A) t) true = t
-- -- -- -- -- -- -- -- Iso.rightInv (Ω*-bool A) x = sym (rUnit x)
-- -- -- -- -- -- -- -- fst (Iso.leftInv (Ω*-bool A) (b , q) i) = q false i
-- -- -- -- -- -- -- -- snd (Iso.leftInv (Ω*-bool A) (b , q) i) false j = q false (i ∧ j)
-- -- -- -- -- -- -- -- snd (Iso.leftInv (Ω*-bool A) (b , q) i) true j = compPath-filler (q true) (sym (q false)) (~ i) j

-- -- -- -- -- -- -- -- Ω*→ : {ℓ ℓ' : Level} (X : RP∞) {A : Pointed ℓ} {B : Pointed ℓ'}
-- -- -- -- -- -- -- --   → (f : A →∙ B)
-- -- -- -- -- -- -- --   → Ω* X A → Ω* X B
-- -- -- -- -- -- -- -- fst (Ω*→ X f (a , t)) = fst f a
-- -- -- -- -- -- -- -- snd (Ω*→ X f (a , t)) x = sym (snd f) ∙ cong (fst f) (t x)

-- -- -- -- -- -- -- -- Ω*→-Iso :
-- -- -- -- -- -- -- --   {ℓ : Level} (X : RP∞) {A B : Pointed ℓ}
-- -- -- -- -- -- -- --   → (f : A ≃∙ B)
-- -- -- -- -- -- -- --   → Ω*∙ X A ≃∙ Ω*∙ X B
-- -- -- -- -- -- -- -- fst (Ω*→-Iso X f) = (Ω*→ X (≃∙map f)) , t f
-- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- --   t : ∀ {ℓ} {A B : Pointed ℓ} (f : A ≃∙ B) → isEquiv (Ω*→ X (≃∙map f))
-- -- -- -- -- -- -- --   t {B = B}= Equiv∙J  (λ A f → isEquiv (Ω*→ X (≃∙map f)))
-- -- -- -- -- -- -- --     (subst isEquiv (funExt (λ {(x , p)
-- -- -- -- -- -- -- --       → ΣPathP (refl , funExt λ x → lUnit _)})) (idIsEquiv (Ω* X B)))
-- -- -- -- -- -- -- -- fst (snd (Ω*→-Iso X f) i) = snd f i
-- -- -- -- -- -- -- -- snd (snd (Ω*→-Iso X {B = B} f) i) x j =
-- -- -- -- -- -- -- --   hcomp (λ k → λ {(i = i1) → snd B ; (j = i0) → snd B ; (j = i1) → snd f i})
-- -- -- -- -- -- -- --         (snd f (i ∨ ~ j))

-- -- -- -- -- -- -- -- Susp*-Bool : ∀ {ℓ} (A : Pointed ℓ) → Iso (Susp* Bool* A .fst) (Susp (typ A))
-- -- -- -- -- -- -- -- Susp*-Bool A = invIso Susp-iso-joinBool

-- -- -- -- -- -- -- -- Susp*-Bool∙ : ∀ {ℓ} (A : Pointed ℓ) → (Susp* Bool* A) ≃∙ (Susp∙ (typ A))
-- -- -- -- -- -- -- -- fst (Susp*-Bool∙ A) = isoToEquiv (Susp*-Bool A)
-- -- -- -- -- -- -- -- snd (Susp*-Bool∙ A) = refl

-- -- -- -- -- -- -- -- merider : ∀ {ℓ} (X : RP∞) (A : Pointed ℓ) → fst A → Ω* X (Susp* X A)
-- -- -- -- -- -- -- -- fst (merider X A x) = inl x
-- -- -- -- -- -- -- -- snd (merider X A a) x =
-- -- -- -- -- -- -- --   (push (pt A) x ∙ sym (push a x)) -- (push a (not* X x) ∙ sym (push (pt A) (not* X x)))

-- -- -- -- -- -- -- -- Booler : ∀ {ℓ} (A : Pointed ℓ) → Iso (Ω* Bool* (Susp* Bool* A)) (Ω (Susp∙ (fst A)) .fst)
-- -- -- -- -- -- -- -- Booler A = compIso (equivToIso (Ω*→-Iso Bool* (Susp*-Bool∙ A) .fst)) (Ω*-bool (Susp∙ (fst A)))

-- -- -- -- -- -- -- -- -- myFun : ∀ {ℓ} (A : Pointed ℓ) (a : fst A) → Iso.fun (Booler A) (merider Bool* A a) ≡ toSusp A a
-- -- -- -- -- -- -- -- -- myFun A a = cong (Iso.fun (Ω*-bool (Susp∙ (fst A)))) t ∙ {!!}
-- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- --   lp : (a : fst A) (x : Bool) → Path (join (typ A) Bool) (inl (pt A)) (inr x)
-- -- -- -- -- -- -- -- --   lp = {!!}


-- -- -- -- -- -- -- -- --   toSusp? : Bool → A .fst → Path (Susp (typ A)) north north
-- -- -- -- -- -- -- -- --   toSusp? false a = refl
-- -- -- -- -- -- -- -- --   toSusp? true a = toSusp A a

-- -- -- -- -- -- -- -- --   t : Ω*→-Iso Bool* (Susp*-Bool∙ A) .fst .fst (merider Bool* A a) ≡ (north , λ x → toSusp? x a)
-- -- -- -- -- -- -- -- --   t = ΣPathP (refl , funExt
-- -- -- -- -- -- -- -- --     λ { false → sym (lUnit _)
-- -- -- -- -- -- -- -- --       ∙ cong-∙ (Susp*-Bool A .Iso.fun)
-- -- -- -- -- -- -- -- --           (push (pt A) false ∙ sym (push a false))
-- -- -- -- -- -- -- -- --           (push a true ∙ sym (push (pt A) true)) -- (cong-∙ (Susp*-Bool A .Iso.fun) {!push (pt A) false ∙ ?!} {!!})
-- -- -- -- -- -- -- -- --       ∙ cong₂ _∙_ (cong-∙ (Susp*-Bool A .Iso.fun) (push (pt A) false) (sym (push a false))
-- -- -- -- -- -- -- -- --                   ∙ cong sym (symDistr (merid (pt A)) (sym (merid a))))
-- -- -- -- -- -- -- -- --                   (cong-∙ (Susp*-Bool A .Iso.fun) (push a true) (sym (push (pt A) true))
-- -- -- -- -- -- -- -- --                   ∙ sym (rUnit refl))
-- -- -- -- -- -- -- -- --       ∙ sym (rUnit _)
-- -- -- -- -- -- -- -- --     ; true → sym (lUnit _)
-- -- -- -- -- -- -- -- --       ∙ cong-∙ (Susp*-Bool A .Iso.fun)
-- -- -- -- -- -- -- -- --           (push (pt A) true ∙ sym (push a true))
-- -- -- -- -- -- -- -- --           (push a false ∙ sym (push (pt A) false))
-- -- -- -- -- -- -- -- --       ∙ cong₂ _∙_ (cong-∙ (Susp*-Bool A .Iso.fun)
-- -- -- -- -- -- -- -- --                     (push (pt A) true) (sym (push a true))
-- -- -- -- -- -- -- -- --                 ∙ sym (rUnit refl))
-- -- -- -- -- -- -- -- --                   (cong-∙ (Susp*-Bool A .Iso.fun)
-- -- -- -- -- -- -- -- --                     (push a false) (sym (push (pt A) false))
-- -- -- -- -- -- -- -- --                 ∙ λ _ → toSusp A a)
-- -- -- -- -- -- -- -- --       ∙ sym (lUnit _) })
-- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- --     help : (a : fst A) (x : Bool) → cong (Susp*-Bool A .Iso.fun) (push a x) ≡ {!cong (Susp*-Bool A .Iso.fun) (push a true)!} 
-- -- -- -- -- -- -- -- --     help = {!!}


-- -- -- -- -- -- -- -- -- Test : (X Y : RP∞) → X ≡ Y → fst Y
-- -- -- -- -- -- -- -- -- Test X Y = {!InS!}

-- -- -- -- -- -- -- -- -- -- JJ* : (X Y : RP∞) (A : fst X → fst Y → Type)
-- -- -- -- -- -- -- -- -- --   → JJ X (λ x → JJ Y (A x)) → JJ Y λ y → JJ X λ x → A x y
-- -- -- -- -- -- -- -- -- -- JJ* X Y A (mid f) = {!(A * B) × (C * D)!} -- mid λ y → {!f!}
-- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- --   c : {!!} (A × B) × (C * D) ----> A × (C * D)
-- -- -- -- -- -- -- -- -- --   c = {!!}
-- -- -- -- -- -- -- -- -- -- JJ* X Y A (sf x (mid f)) = mid λ y → sf x (f y)
-- -- -- -- -- -- -- -- -- -- JJ* X Y A (sf x (sf a b)) = sf a (sf x b)
-- -- -- -- -- -- -- -- -- -- JJ* X Y A (sf x (sl x₁ f i)) = {!!}
-- -- -- -- -- -- -- -- -- -- JJ* X Y A (sl x f i) = {!x!}

-- -- -- -- -- -- -- -- -- -- open import Cubical.Data.Bool as BL
-- -- -- -- -- -- -- -- -- -- Belim : ∀ {ℓ} {A : Bool → Type ℓ}
-- -- -- -- -- -- -- -- -- --   → A true
-- -- -- -- -- -- -- -- -- --   → A false
-- -- -- -- -- -- -- -- -- --   → (x : _) → A x
-- -- -- -- -- -- -- -- -- -- Belim a b false = b
-- -- -- -- -- -- -- -- -- -- Belim a b true = a

-- -- -- -- -- -- -- -- -- -- module _ (A : Bool → Type) where
-- -- -- -- -- -- -- -- -- --   JJ-B : JJ Bool* A → join (A true) (A false)
-- -- -- -- -- -- -- -- -- --   JJ-B (mid f) = inl (f true)
-- -- -- -- -- -- -- -- -- --   JJ-B (sf false y) = inr y
-- -- -- -- -- -- -- -- -- --   JJ-B (sf true y) = inl y
-- -- -- -- -- -- -- -- -- --   JJ-B (sl false f i) = push (f true) (f false) i
-- -- -- -- -- -- -- -- -- --   JJ-B (sl true f i) = inl (f true)

-- -- -- -- -- -- -- -- -- --   B-JJ : join (A true) (A false) → JJ Bool* A
-- -- -- -- -- -- -- -- -- --   B-JJ (inl x) = sf true x
-- -- -- -- -- -- -- -- -- --   B-JJ (inr x) = sf false x
-- -- -- -- -- -- -- -- -- --   B-JJ (push a b i) =
-- -- -- -- -- -- -- -- -- --     (sym (sl true (Belim a b)) ∙ sl false (Belim a b)) i

-- -- -- -- -- -- -- -- -- --   B-JJ-B : (x : join (A true) (A false)) → JJ-B (B-JJ x) ≡ x
-- -- -- -- -- -- -- -- -- --   B-JJ-B (inl x) = refl
-- -- -- -- -- -- -- -- -- --   B-JJ-B (inr x) = refl
-- -- -- -- -- -- -- -- -- --   B-JJ-B (push a b i) j = h j i
-- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- --     h : cong JJ-B ((sym (sl true (Belim a b)) ∙ sl false (Belim a b))) ≡ push a b
-- -- -- -- -- -- -- -- -- --     h = cong-∙ JJ-B (sym (sl true (Belim a b))) (sl false (Belim a b))
-- -- -- -- -- -- -- -- -- --         ∙ sym (lUnit _)

-- -- -- -- -- -- -- -- -- --   JJ-B-JJ : (x : JJ Bool* A) → B-JJ (JJ-B x) ≡ x
-- -- -- -- -- -- -- -- -- --   JJ-B-JJ (mid f) = sym (sl true f)
-- -- -- -- -- -- -- -- -- --   JJ-B-JJ (sf false y) = refl
-- -- -- -- -- -- -- -- -- --   JJ-B-JJ (sf true y) = refl
-- -- -- -- -- -- -- -- -- --   JJ-B-JJ (sl false f i) j =
-- -- -- -- -- -- -- -- -- --     hcomp (λ k → λ { (i = i0) → sl true f (~ j)
-- -- -- -- -- -- -- -- -- --                    ; (i = i1) → sl false (tl (~ k)) (k ∨ j)
-- -- -- -- -- -- -- -- -- --                    ; (j = i0) → compPath-filler
-- -- -- -- -- -- -- -- -- --                                   (sym (sl true (tl (~ k))))
-- -- -- -- -- -- -- -- -- --                                   (sl false (tl (~ k))) k i
-- -- -- -- -- -- -- -- -- --                    ; (j  = i1) → sl false f i })
-- -- -- -- -- -- -- -- -- --           (ppf _ (sym (sl true f)) _ (sl false f) i j)
-- -- -- -- -- -- -- -- -- --       where
-- -- -- -- -- -- -- -- -- --       ppf : ∀ {ℓ} {A : Type ℓ} {x : A} (y : A) (p : x ≡ y) (z : A) (q : y ≡ z) →
-- -- -- -- -- -- -- -- -- --         Square p q p q
-- -- -- -- -- -- -- -- -- --       ppf = J> (J> refl)
-- -- -- -- -- -- -- -- -- --       tl : Belim (f true) (f false) ≡ f
-- -- -- -- -- -- -- -- -- --       tl = funExt λ { false → refl ; true → refl}
-- -- -- -- -- -- -- -- -- --   JJ-B-JJ (sl true f i) j = sl true f (~ j ∨ i)

-- -- -- -- -- -- -- -- -- -- -- module _ (X : RP∞) (A : fst X → Type) where
-- -- -- -- -- -- -- -- -- -- --   data abr (X : RP∞) (A : fst X → Type)  : Type where
-- -- -- -- -- -- -- -- -- -- --     inss : (x : fst X) → A x → A (not* X x) → abr X A
-- -- -- -- -- -- -- -- -- -- --     gl : (x : fst X) (a : _) (b : _)
-- -- -- -- -- -- -- -- -- -- --       → inss x a b
-- -- -- -- -- -- -- -- -- -- --        ≡ inss (not* X x) b (subst A (sym (not*not* X x)) a)

-- -- -- -- -- -- -- -- -- -- --   abr→Atrue : (A : Bool → Type) → abr Bool* A → A true
-- -- -- -- -- -- -- -- -- -- --   abr→Atrue A (inss false y l) = l
-- -- -- -- -- -- -- -- -- -- --   abr→Atrue A (inss true y l) = y
-- -- -- -- -- -- -- -- -- -- --   abr→Atrue A (gl false a b i) = b
-- -- -- -- -- -- -- -- -- -- --   abr→Atrue A (gl true a b i) = transportRefl a (~ i)

-- -- -- -- -- -- -- -- -- -- --   typs : (X : RP∞) (x : fst X) (A : fst X → Type) → abr X A → A x
-- -- -- -- -- -- -- -- -- -- --   typs = J2-elem _ .fst abr→Atrue

-- -- -- -- -- -- -- -- -- -- --   typs' : (X : RP∞) (A : fst X → Type) → abr X A → (x : fst X) → A x
-- -- -- -- -- -- -- -- -- -- --   typs' X A p x = typs X x A p


-- -- -- -- -- -- -- -- -- -- -- -- true , const -> true , true
-- -- -- -- -- -- -- -- -- -- -- -- false , const -> false , false
-- -- -- -- -- -- -- -- -- -- -- -- true , not ->  true , false
-- -- -- -- -- -- -- -- -- -- -- -- false , not , -> false ,true 

-- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- --   uncurry λ X
-- -- -- -- -- -- -- -- -- -- --     → elim→Set
-- -- -- -- -- -- -- -- -- -- --          (λ _ → isSetΠ λ _ → isSet⊎ {!!} {!!})
-- -- -- -- -- -- -- -- -- -- --          {!!}
-- -- -- -- -- -- -- -- -- -- --          {!!}
-- -- -- -- -- -- -- -- -- -- --          -}

-- -- -- -- -- -- -- -- -- -- -- module _ (X Y : RP∞) where
-- -- -- -- -- -- -- -- -- -- --   toFunz : (fst Y ⊎ (fst X ≃ fst Y)) → fst X → fst Y
-- -- -- -- -- -- -- -- -- -- --   toFunz (inl y) _ = y
-- -- -- -- -- -- -- -- -- -- --   toFunz (inr z) = fst z

-- -- -- -- -- -- -- -- -- -- -- isEq-toFunz : (X Y : RP∞) → isEquiv (toFunz X Y)
-- -- -- -- -- -- -- -- -- -- -- isEq-toFunz = RP∞pt→Prop (λ _ → isPropΠ λ _ → isPropIsEquiv _)
-- -- -- -- -- -- -- -- -- -- --   (RP∞pt→Prop (λ _ → isPropIsEquiv _)
-- -- -- -- -- -- -- -- -- -- --     (isoToIsEquiv myIso))
-- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- --   invFunz : Bool × Bool → (Bool ⊎ (Bool ≃ Bool))
-- -- -- -- -- -- -- -- -- -- --   invFunz (false , false) = inl false
-- -- -- -- -- -- -- -- -- -- --   invFunz (false , true) = inr notEquiv
-- -- -- -- -- -- -- -- -- -- --   invFunz (true , false) = inr (idEquiv _)
-- -- -- -- -- -- -- -- -- -- --   invFunz (true , true) = inl true

-- -- -- -- -- -- -- -- -- -- --   myIso : Iso _ _
-- -- -- -- -- -- -- -- -- -- --   Iso.fun myIso = toFunz Bool* Bool*
-- -- -- -- -- -- -- -- -- -- --   Iso.inv myIso f = invFunz (f true , f false)
-- -- -- -- -- -- -- -- -- -- --   Iso.rightInv myIso f =
-- -- -- -- -- -- -- -- -- -- --     funExt (h (f true) (f false)) ∙ sym (f≡ f)
-- -- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- -- --     mkbool : {A : Type} (x y : A) → Bool → A
-- -- -- -- -- -- -- -- -- -- --     mkbool x y true = x
-- -- -- -- -- -- -- -- -- -- --     mkbool x y false = y

-- -- -- -- -- -- -- -- -- -- --     f≡ : {A : Type} (f : Bool → A) → f ≡ mkbool (f true) (f false)
-- -- -- -- -- -- -- -- -- -- --     f≡ f i false = f false
-- -- -- -- -- -- -- -- -- -- --     f≡ f i true = f true

-- -- -- -- -- -- -- -- -- -- --     h : (x y z : Bool) → toFunz Bool* Bool* (invFunz (x , y)) z ≡ mkbool x y z
-- -- -- -- -- -- -- -- -- -- --     h false false false = refl
-- -- -- -- -- -- -- -- -- -- --     h false false true = refl
-- -- -- -- -- -- -- -- -- -- --     h false true false = refl
-- -- -- -- -- -- -- -- -- -- --     h false true true = refl
-- -- -- -- -- -- -- -- -- -- --     h true false false = refl
-- -- -- -- -- -- -- -- -- -- --     h true false true = refl
-- -- -- -- -- -- -- -- -- -- --     h true true false = refl
-- -- -- -- -- -- -- -- -- -- --     h true true true = refl
-- -- -- -- -- -- -- -- -- -- --   Iso.leftInv myIso (inl false) = refl
-- -- -- -- -- -- -- -- -- -- --   Iso.leftInv myIso (inl true) = refl
-- -- -- -- -- -- -- -- -- -- --   Iso.leftInv myIso (inr x) =
-- -- -- -- -- -- -- -- -- -- --     ((λ i → invFunz (fst (Iso.leftInv Bool≃Charac x (~ i)) true
-- -- -- -- -- -- -- -- -- -- --       , fst (Iso.leftInv Bool≃Charac x (~ i)) false))
-- -- -- -- -- -- -- -- -- -- --       ∙ h (Iso.fun Bool≃Charac x))
-- -- -- -- -- -- -- -- -- -- --     ∙
-- -- -- -- -- -- -- -- -- -- --     (λ i → inr (Iso.leftInv Bool≃Charac x i))
-- -- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- -- --     h : (t : Bool) → invFunz (fst (Iso.inv Bool≃Charac t) true
-- -- -- -- -- -- -- -- -- -- --                              , fst (Iso.inv Bool≃Charac t) false)
-- -- -- -- -- -- -- -- -- -- --                     ≡ inr (Iso.inv Bool≃Charac t)
-- -- -- -- -- -- -- -- -- -- --     h false = refl
-- -- -- -- -- -- -- -- -- -- --     h true = refl

-- -- -- -- -- -- -- -- -- -- -- toFunz-Eq : (X Y : RP∞)
-- -- -- -- -- -- -- -- -- -- --   → (fst Y ⊎ (fst X ≃ fst Y)) ≃ (fst X → fst Y)
-- -- -- -- -- -- -- -- -- -- -- toFunz-Eq X Y = toFunz X Y , isEq-toFunz X Y

-- -- -- -- -- -- -- -- -- -- -- toFunz-ind : ∀ {ℓ} (X Y : RP∞) (A : (fst X → fst Y) → Type ℓ)
-- -- -- -- -- -- -- -- -- -- --   → ((x : _) → A (toFunz X Y x))
-- -- -- -- -- -- -- -- -- -- --   → (x : _) → A x
-- -- -- -- -- -- -- -- -- -- -- toFunz-ind X Y A x f =
-- -- -- -- -- -- -- -- -- -- --   subst A (secEq (_ , isEq-toFunz X Y) f) (x (invEq (_ , isEq-toFunz X Y) f))

-- -- -- -- -- -- -- -- -- -- -- module _ {ℓ : Level} (X : RP∞) (A : fst X → Type ℓ) where
-- -- -- -- -- -- -- -- -- -- --   data jo : Type ℓ where
-- -- -- -- -- -- -- -- -- -- --     makel : {x : fst X} → A x → jo
-- -- -- -- -- -- -- -- -- -- --     maker : ((x : _) → A x) → jo
-- -- -- -- -- -- -- -- -- -- --     pusher : {x : fst X} (f : ((x : _) → A x)) → makel (f x) ≡ maker f

-- -- -- -- -- -- -- -- -- -- --   jo* : Type ℓ
-- -- -- -- -- -- -- -- -- -- --   jo* = Pushout {A = fst X × ((x : _) → A x)}
-- -- -- -- -- -- -- -- -- -- --                 {B = Σ[ x ∈ fst X ] A x}
-- -- -- -- -- -- -- -- -- -- --                 {C = ((x : _) → A x)}
-- -- -- -- -- -- -- -- -- -- --                 (λ f → fst f , snd f (fst f))
-- -- -- -- -- -- -- -- -- -- --                 snd

-- -- -- -- -- -- -- -- -- -- -- eval-⊎ : (X Y : RP∞)
-- -- -- -- -- -- -- -- -- -- --   → fst Y ⊎ (fst X ≃ fst Y)
-- -- -- -- -- -- -- -- -- -- --   → (x : fst X)
-- -- -- -- -- -- -- -- -- -- --   → fst Y
-- -- -- -- -- -- -- -- -- -- -- eval-⊎ X Y (inl y) x = y
-- -- -- -- -- -- -- -- -- -- -- eval-⊎ X Y (inr g) x = fst g x

-- -- -- -- -- -- -- -- -- -- -- DD : {ℓ : Level} (X Y : RP∞) (A : fst X → fst Y → Type ℓ)
-- -- -- -- -- -- -- -- -- -- --   → ((x : fst X) → Σ (fst Y) (A x))
-- -- -- -- -- -- -- -- -- -- --   → Σ[ f ∈ (fst Y ⊎ (fst X ≃ fst Y)) ]
-- -- -- -- -- -- -- -- -- -- --        ((x : fst X) → A x (eval-⊎ X Y f x))
-- -- -- -- -- -- -- -- -- -- -- fst (DD X Y A g) = invEq (toFunz-Eq X Y) (fst ∘ g)
-- -- -- -- -- -- -- -- -- -- -- snd (DD X Y A g) x = subst (A x) help (g x .snd)
-- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- --   hh' : (r : fst Y ⊎ (fst X ≃ fst Y)) (x : fst X)
-- -- -- -- -- -- -- -- -- -- --     → eval-⊎ X Y r x ≡ toFunz X Y r x 
-- -- -- -- -- -- -- -- -- -- --   hh' (inl x₁) x = refl
-- -- -- -- -- -- -- -- -- -- --   hh' (inr x₁) x = refl

-- -- -- -- -- -- -- -- -- -- --   help : fst (g x)
-- -- -- -- -- -- -- -- -- -- --        ≡ eval-⊎ X Y (invEq (toFunz-Eq X Y) (λ x₁ → fst (g x₁))) x
-- -- -- -- -- -- -- -- -- -- --   help =
-- -- -- -- -- -- -- -- -- -- --       funExt⁻ (sym (secEq (toFunz-Eq X Y) (fst ∘ g))) x
-- -- -- -- -- -- -- -- -- -- --     ∙ sym (hh' (invEq (toFunz-Eq X Y) (λ x₁ → fst (g x₁))) x)
-- -- -- -- -- -- -- -- -- -- --   {- J2-elem _ .fst
-- -- -- -- -- -- -- -- -- -- --     (J2-elem _ .fst
-- -- -- -- -- -- -- -- -- -- --       λ A g → {!invEq (toFunz-Eq Bool* Bool*) g!})
-- -- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- -- --     k : (r : fst Bool* ⊎ (fst Bool* ≃ fst Bool*))
-- -- -- -- -- -- -- -- -- -- --       → eval-⊎ Bool* Bool* r true ≡ toFunz Bool* Bool* r true
-- -- -- -- -- -- -- -- -- -- --     k (inl x) = refl
-- -- -- -- -- -- -- -- -- -- --     k (inr x) = refl
-- -- -- -- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- characMapsBool : (f : Bool → Bool) → (isEquiv f) ⊎ (Σ[ y ∈ Bool ] ((x : _) → f x ≡ y))
-- -- -- -- -- -- -- -- characMapsBool f = h _ _ refl refl
-- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- --   h : (x y : Bool) → f true ≡ x → f false ≡ y → (isEquiv f) ⊎ (Σ[ y ∈ Bool ] ((x : _) → f x ≡ y))
-- -- -- -- -- -- -- --   h false false p q = inr (false , λ { false → q ; true → p})
-- -- -- -- -- -- -- --   h false true p q = inl (isoToIsEquiv (iso f f help help))
-- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- --     help : (x : Bool) → f (f x) ≡ x
-- -- -- -- -- -- -- --     help false = cong f q ∙ p
-- -- -- -- -- -- -- --     help true = cong f p ∙ q
-- -- -- -- -- -- -- --   h true false p q = inl (isoToIsEquiv (iso f f help help))
-- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- --     help : (x : Bool) → f (f x) ≡ x
-- -- -- -- -- -- -- --     help false = cong f q ∙ q
-- -- -- -- -- -- -- --     help true = cong f p ∙ p
-- -- -- -- -- -- -- --   h true true p q = inr (true , λ { false → q ; true → p})
  

-- -- -- -- -- -- -- -- funS : (X Y : RP∞) → (fst X ≃ fst Y) ⊎ fst Y → fst X → fst Y
-- -- -- -- -- -- -- -- funS X Y (inl f) x = fst f x
-- -- -- -- -- -- -- -- funS X Y (inr y) x = y

-- -- -- -- -- -- -- -- funSBool : (X Y : RP∞) → isEquiv (funS X Y)
-- -- -- -- -- -- -- -- funSBool = RP∞pt→Prop (λ _ → isPropΠ λ _ → isPropIsEquiv _)
-- -- -- -- -- -- -- --   (RP∞pt→Prop (λ _ → isPropIsEquiv _)
-- -- -- -- -- -- -- --     (isoToIsEquiv (iso (funS Bool* Bool*)
-- -- -- -- -- -- -- --                        (λ f → ⊎.rec (λ t → inl (f , t)) (λ g → inr (g .fst)) (characMapsBool f))
-- -- -- -- -- -- -- --                        (λ f → funExt λ { false → {!!} ; true → {!!}})
-- -- -- -- -- -- -- --                        λ { (inl x) → {!!}
-- -- -- -- -- -- -- --                          ; (inr false) → refl
-- -- -- -- -- -- -- --                          ; (inr true) → refl})))

-- -- -- -- -- -- -- -- funS-bool : (X Y : RP∞) → ((fst X ≃ fst Y) ⊎ fst Y) ≃ (fst X → fst Y)
-- -- -- -- -- -- -- -- funS-bool X Y = funS X Y , funSBool X Y


-- -- -- -- -- -- -- -- module _ {ℓ : Level} (X Y : RP∞) (A : fst X → fst Y → Type ℓ) where
-- -- -- -- -- -- -- --   ¬' = not* X

-- -- -- -- -- -- -- --   A' B' : fst X → Type ℓ
-- -- -- -- -- -- -- --   A' x = Σ[ y ∈ fst Y ] A x y
-- -- -- -- -- -- -- --   B' x = (y : _) → A x y

-- -- -- -- -- -- -- --   data mjo : Type ℓ where
-- -- -- -- -- -- -- --     aa : ((x : fst X) → A' x) → mjo
-- -- -- -- -- -- -- --     bb : ((x : fst X) → B' x) → mjo
-- -- -- -- -- -- -- --     ab : (x : fst X) → A' x → B' (¬' x) → mjo
-- -- -- -- -- -- -- --     ar : (x : fst X) (a : (k : fst X) → A' k) (b : B' (¬' x))
-- -- -- -- -- -- -- --       → snd (a (¬' x)) ≡ b _ →  aa a ≡ ab _ (a x) b
-- -- -- -- -- -- -- --     br : (x : fst X) (a : A' x) (b : (k : fst X) → B' k)
-- -- -- -- -- -- -- --       → a .snd ≡ b x (fst a)
-- -- -- -- -- -- -- --       → ab x a (b (¬' x)) ≡ bb b
-- -- -- -- -- -- -- --     rr : (a : (x : fst X) → A' x) (b : (x : fst X) → B' x)
-- -- -- -- -- -- -- --          (c : (x : fst X) → a x .snd ≡ b x (fst (a x)))
-- -- -- -- -- -- -- --       → aa a ≡ bb b
-- -- -- -- -- -- -- --     rr' : (a : (x : fst X) → A' x) (b : (x : fst X) → B' x)
-- -- -- -- -- -- -- --          (c : (x : fst X) → a x .snd ≡ b x (fst (a x)))
-- -- -- -- -- -- -- --          (x : fst X)
-- -- -- -- -- -- -- --          → PathP (λ i → ar x a (b (¬' x)) (c _) i ≡ bb b)
-- -- -- -- -- -- -- --                   (rr a b c) (br x (a x) b (c x))

-- -- -- -- -- -- -- --   M1 : {!(fst X ≃ fst Y) ⊎ fst Y!}
-- -- -- -- -- -- -- --   M1 = {!!}

-- -- -- -- -- -- -- --   mjo→ : mjo → JJ Y λ y → JJ X λ x → A x y
-- -- -- -- -- -- -- --   mjo→ (aa f) = mid {!(snd ∘ f) -- invEq (funS-bool X Y) (fst ∘ f)!} -- mid λ y → mid λ x → CasesRP Y {λ y → A x y} (fst (f x)) (f x .snd) {!!} y
-- -- -- -- -- -- -- --   mjo→ (bb f) = mid λ y → mid λ x → f x y
-- -- -- -- -- -- -- --   mjo→ (ab x (y , a) nb) = sf y (mid (CasesRP X x a (nb y)))
-- -- -- -- -- -- -- --   mjo→ (ar x a b x₁ i) = {!åååååååååååpoooooiioooooooooo¨ååååååååååå¨åååååååååååååppooåååååååååååååpoooooooooiiiio!}
-- -- -- -- -- -- -- --   mjo→ (br x a b x₁ i) = {!!}
-- -- -- -- -- -- -- --   mjo→ (rr a b c i) = {!!}
-- -- -- -- -- -- -- --   mjo→ (rr' a b c x i j) = {!!}




-- -- -- -- -- -- -- -- --   Σf = Σ[ f ∈ (fst Y ⊎ (fst X ≃ fst Y)) ]
-- -- -- -- -- -- -- -- --          ((x : fst X) → A x (eval-⊎ X Y f x))

-- -- -- -- -- -- -- -- --   data mjo* : Type ℓ where
-- -- -- -- -- -- -- -- --     aa* : Σf → mjo*
-- -- -- -- -- -- -- -- --     bb* : ((x : fst X) → B' x) → mjo*
-- -- -- -- -- -- -- -- --     ab* : (x : fst X) (y : fst Y) → A x y → B' (¬' x) → mjo*
-- -- -- -- -- -- -- -- --     ar* : (x : fst X) (fh : Σf) (b : B' (¬' x))
-- -- -- -- -- -- -- -- --       → fh .snd (¬' x) ≡ b _
-- -- -- -- -- -- -- -- --       → aa* fh ≡ ab* x (eval-⊎ X Y (fh .fst) x) (fh .snd x) b
-- -- -- -- -- -- -- -- --     br* : (x : fst X) (y : fst Y) (a : A x y)
-- -- -- -- -- -- -- -- --           (b : (k : fst X) → B' k)
-- -- -- -- -- -- -- -- --        → a ≡ b x y
-- -- -- -- -- -- -- -- --        → ab* x y a (b (¬' x)) ≡ bb* b
-- -- -- -- -- -- -- -- --     rr* : (fh : Σf) (b : (x : fst X) → B' x)
-- -- -- -- -- -- -- -- --           (c : (x : fst X) → fh .snd x ≡ b x _)
-- -- -- -- -- -- -- -- --           → aa* fh ≡ bb* b
-- -- -- -- -- -- -- -- --     rr** : (fh : Σf) (b : (x : fst X) → B' x)
-- -- -- -- -- -- -- -- --           (c : (x : fst X) → fh .snd x ≡ b x _)
-- -- -- -- -- -- -- -- --           (x : fst X)
-- -- -- -- -- -- -- -- --        → PathP (λ i → ar* x fh (b (¬' x)) (c (¬' x)) i ≡ bb* b)
-- -- -- -- -- -- -- -- --                 (rr* fh b c)
-- -- -- -- -- -- -- -- --                 (br* x (eval-⊎ X Y (fh .fst) x) (fh .snd x) b (c x))

-- -- -- -- -- -- -- -- --   TP = jo* Y λ y → jo* X λ x → A x y

-- -- -- -- -- -- -- -- --   F1 : (x : fst Y ⊎ (fst X ≃ fst Y))
-- -- -- -- -- -- -- -- --        (q : (x₁ : fst X) → A x₁ (eval-⊎ X Y x x₁))
-- -- -- -- -- -- -- -- --        (y : fst Y) → jo* X (λ x₂ → A x₂ y)
-- -- -- -- -- -- -- -- --   F1 x q y = {!!}

-- -- -- -- -- -- -- -- --   THEF : mjo* → TP
-- -- -- -- -- -- -- -- --   THEF (aa* (inl x , q)) = inl (x , inr q)
-- -- -- -- -- -- -- -- --   THEF (aa* (inr x , q)) =
-- -- -- -- -- -- -- -- --     inr λ y → inl (invEq x y
-- -- -- -- -- -- -- -- --              , subst (A (invEq x y)) (secEq x y) (q (invEq x y)))
-- -- -- -- -- -- -- -- --   THEF (bb* g) = inr λ y → inr (λ x → g x y)
-- -- -- -- -- -- -- -- --   THEF (ab* x y xy bn) =
-- -- -- -- -- -- -- -- --     inr (CasesRP Y y (inr (CasesRP X x xy (bn y)))
-- -- -- -- -- -- -- -- --                      (inl ((¬' x) , bn (not* Y y))))
-- -- -- -- -- -- -- -- --   THEF (ar* x (inl y , m) b x₁ i) = {!!} -- pst* i
-- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- --     pst* : Path TP (inl (y , inr m)) (inr
-- -- -- -- -- -- -- -- --          (CasesRP Y y (inr (CasesRP X x (m x) (b y)))
-- -- -- -- -- -- -- -- --           (inl (¬' x , b (not* Y y)))))
-- -- -- -- -- -- -- -- --     pst* = {!λ i → !}
-- -- -- -- -- -- -- -- --       ∙ push (y , CasesRP Y y (inr m) (inl (¬' x , b _)))
-- -- -- -- -- -- -- -- --       ∙ {!!}
-- -- -- -- -- -- -- -- --   THEF (ar* x (inr f , m) b x₁ i) = inr (pth i)
-- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- --     inr* : _ → TP
-- -- -- -- -- -- -- -- --     inr* = inr
-- -- -- -- -- -- -- -- --     pth : Path ((y : fst Y) → jo* X (λ x → A x y))
-- -- -- -- -- -- -- -- --                 (λ y →
-- -- -- -- -- -- -- -- --             inl (invEq f y
-- -- -- -- -- -- -- -- --               , subst (A (invEq f y)) (secEq f y) (m (invEq f y))))
-- -- -- -- -- -- -- -- --                 ((CasesRP Y (fst f x)
-- -- -- -- -- -- -- -- --                   (inr (CasesRP X x (m x) (b (fst f x))))
-- -- -- -- -- -- -- -- --                   (inl (¬' x , b (not* Y (fst f x))))))
-- -- -- -- -- -- -- -- --     pth = funExt λ y'yyyyyyyyy
-- -- -- -- -- -- -- -- --       → {!!}

-- -- -- -- -- -- -- -- --   THEF (br* x y a b x₁   i) = {!!}
-- -- -- -- -- -- -- -- --   THEF (rr* (inl x , m) b c i) = {!c!}
-- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- --     help : Path TP (inl (x , inr m)) (inr (λ y → inr (λ x₁ → b x₁ y)))
-- -- -- -- -- -- -- -- --     help = (λ i → inl (x , inr (λ x' → c x' i)))
-- -- -- -- -- -- -- -- --          ∙ push (x , λ y → inr (λ x → b x y))
-- -- -- -- -- -- -- -- --   THEF (rr* (inr x , m) b c i) = {!!}
-- -- -- -- -- -- -- -- --   THEF (rr** fh b c x i i₁) = {!!}

-- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- Σ[ f ∈ (fst Y ⊎ (fst X ≃ fst Y)) ]
-- -- -- -- -- -- -- -- --        ((x : fst X) → A x (eval-⊎ X Y f x))
-- -- -- -- -- -- -- -- -- -}
  

-- -- -- -- -- -- -- -- -- --   mjo-ind'' : {!!}
-- -- -- -- -- -- -- -- -- --   mjo-ind'' = {!!}

-- -- -- -- -- -- -- -- -- --   module _ {ℓ : Level} {B : Type ℓ}
-- -- -- -- -- -- -- -- -- --            (bb' : ((x : fst X) → B' x) → B)
-- -- -- -- -- -- -- -- -- --            (ab' : (x₂ : fst X) → A' x₂ → B' (¬' x₂) → B)
-- -- -- -- -- -- -- -- -- --            (x : fst X)
-- -- -- -- -- -- -- -- -- --            (b : (k : fst X) → B' k)
-- -- -- -- -- -- -- -- -- --            (a : A' x)
-- -- -- -- -- -- -- -- -- --            (qdr : (n : (k : fst X) → A' k)
-- -- -- -- -- -- -- -- -- --             → n x .snd ≡ b x (n x .fst)
-- -- -- -- -- -- -- -- -- --             → ab' x (n x) (b (¬' x)) ≡ bb' b)
-- -- -- -- -- -- -- -- -- --            (x₁ : a .snd ≡ b x (fst a)) where
 
-- -- -- -- -- -- -- -- -- --     n : (k : fst X) → A' k
-- -- -- -- -- -- -- -- -- --     fst (n k) = a .fst
-- -- -- -- -- -- -- -- -- --     snd (n k) =
-- -- -- -- -- -- -- -- -- --       CasesRP X {A = λ k → A k (a .fst)}
-- -- -- -- -- -- -- -- -- --               x (a .snd) (b (¬' x) (a .fst)) k

-- -- -- -- -- -- -- -- -- --     n-x≡ : n x ≡ a
-- -- -- -- -- -- -- -- -- --     fst (n-x≡ i) = a .fst
-- -- -- -- -- -- -- -- -- --     snd (n-x≡ i) =
-- -- -- -- -- -- -- -- -- --       CasesRPβ X {A = λ k → A k (a .fst)}
-- -- -- -- -- -- -- -- -- --               x (a .snd) (b (¬' x) (a .fst)) .fst i

-- -- -- -- -- -- -- -- -- --     h* : ab' x a (b (¬' x)) ≡ bb' b
-- -- -- -- -- -- -- -- -- --     h* = cong (λ z → ab' x z (b (¬' x))) (sym n-x≡)
-- -- -- -- -- -- -- -- -- --       ∙ qdr n (cong snd n-x≡ ∙ x₁)
 

-- -- -- -- -- -- -- -- -- --   mjo-ind* : ∀ {ℓ} {B : Type ℓ}
-- -- -- -- -- -- -- -- -- --     → (aa' : ((x : fst X) → A' x) → B)
-- -- -- -- -- -- -- -- -- --     → (bb' : ((x : fst X) → B' x) → B)
-- -- -- -- -- -- -- -- -- --     → (ab' : (x : fst X) → A' x → B' (¬' x) → B)
-- -- -- -- -- -- -- -- -- --     → ((a : (k : fst X) → A' k)
-- -- -- -- -- -- -- -- -- --       → Σ[ br' ∈ ((b : (k : fst X) → B' k) (x : fst X) → a x .snd ≡ b x (a x .fst)
-- -- -- -- -- -- -- -- -- --                → ab' x (a x) (b (¬' x)) ≡ bb' b) ]
-- -- -- -- -- -- -- -- -- --           Σ[ ar' ∈ ((x : fst X) (b : B' (¬' x))
-- -- -- -- -- -- -- -- -- --       → snd (a (¬' x)) ≡ b _ →  aa' a ≡ ab' _ (a x) b) ]
-- -- -- -- -- -- -- -- -- --             ((b : (k : fst X) → B' k) (c : (x : fst X) → a x .snd ≡ b x (fst (a x)))
-- -- -- -- -- -- -- -- -- --           → Σ[ rr ∈ aa' a ≡ bb' b ] ((x : fst X)
-- -- -- -- -- -- -- -- -- --             → PathP (λ i → ar' x (b (¬' x)) (c _) i ≡ bb' b)
-- -- -- -- -- -- -- -- -- --                      rr (br' b x (c x) ))))
-- -- -- -- -- -- -- -- -- --     → mjo → B
-- -- -- -- -- -- -- -- -- --   mjo-ind* aa' bb' ab' qdr (aa x) = aa' x
-- -- -- -- -- -- -- -- -- --   mjo-ind* aa' bb' ab' qdr (bb x) = bb' x
-- -- -- -- -- -- -- -- -- --   mjo-ind* aa' bb' ab' qdr (ab x x₁ x₂) = ab' x x₁ x₂
-- -- -- -- -- -- -- -- -- --   mjo-ind* aa' bb' ab' qdr (ar x a b x₁ i) = qdr a .snd .fst x b x₁ i
-- -- -- -- -- -- -- -- -- --   mjo-ind* aa' bb' ab' qdr (br x a b x₁ i) =
-- -- -- -- -- -- -- -- -- --     h* bb' ab' x b a (λ n → qdr n .fst b x) x₁ i -- h i
-- -- -- -- -- -- -- -- -- --   mjo-ind* aa' bb' ab' qdr (rr a b c i) = qdr a .snd .snd b c .fst i
-- -- -- -- -- -- -- -- -- --   mjo-ind* aa' bb' ab' qdr (rr' a b c x i j) = {!qdr a .snd .snd b c .snd x!}
-- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- --     lem : h* bb' ab' x b (a x) (λ n₁ → qdr n₁ .fst b x) (c x)
-- -- -- -- -- -- -- -- -- --        ≡ fst (qdr a) b x (c x)
-- -- -- -- -- -- -- -- -- --     lem = {!!}
-- -- -- -- -- -- -- -- -- --     cb : PathP (λ i → qdr a .snd .snd b c .fst i
-- -- -- -- -- -- -- -- -- --                      ≡ h* bb' ab' x b (a x) (λ n₁ → qdr n₁ .fst b x) (c x) i)
-- -- -- -- -- -- -- -- -- --           (qdr a .snd .fst x (b (¬' x)) (c (¬' x)))
-- -- -- -- -- -- -- -- -- --           (refl {x = bb' b})
-- -- -- -- -- -- -- -- -- --     cb i j = hcomp (λ k → λ {(i = i0) → qdr a .snd .snd b c .snd x j (~ k)
-- -- -- -- -- -- -- -- -- --                             ; (i = i1) → bb' b
-- -- -- -- -- -- -- -- -- --                             ; (j = i0) → fst (qdr a .snd .snd b c) (~ k ∨ i)
-- -- -- -- -- -- -- -- -- --                             ; (j = i1) → {!qdr a .snd .snd b c .snd x j (~ k)!}})
-- -- -- -- -- -- -- -- -- --                    {!!}
-- -- -- -- -- -- -- -- -- --   mjo-ind' : ∀ {ℓ} {B : Type ℓ}
-- -- -- -- -- -- -- -- -- --     → (aa' : ((x : fst X) → A' x) → B)
-- -- -- -- -- -- -- -- -- --     → (bb' : ((x : fst X) → B' x) → B)
-- -- -- -- -- -- -- -- -- --     → (ab' : (x : fst X) → A' x → B' (¬' x) → B)
-- -- -- -- -- -- -- -- -- --     → (br' : (b : (k : fst X) → B' k)
-- -- -- -- -- -- -- -- -- --                (x : fst X) (a : A' x)
-- -- -- -- -- -- -- -- -- --               → a .snd ≡ b x (fst a)
-- -- -- -- -- -- -- -- -- --                  → ab' x a (b (¬' x)) ≡ bb' b)
-- -- -- -- -- -- -- -- -- --     → ((a : (k : fst X) → A' k)
-- -- -- -- -- -- -- -- -- --         → Σ[ ar' ∈ ((x : fst X) (a : (k : fst X) → A' k) (b : B' (¬' x))
-- -- -- -- -- -- -- -- -- --       → snd (a (¬' x)) ≡ b _ →  aa' a ≡ ab' _ (a x) b) ]
-- -- -- -- -- -- -- -- -- --             ((b : (k : fst X) → B' k) (c : (x : fst X) → a x .snd ≡ b x (fst (a x)))
-- -- -- -- -- -- -- -- -- --           → Σ[ rr ∈ aa' a ≡ bb' b ] ((x : fst X)
-- -- -- -- -- -- -- -- -- --             → PathP (λ i → ar' x a (b (¬' x)) (c _) i ≡ bb' b)
-- -- -- -- -- -- -- -- -- --                      rr (br' b x (a x) (c x)))))
-- -- -- -- -- -- -- -- -- --     → mjo → B
-- -- -- -- -- -- -- -- -- --   mjo-ind' aa' bb' ab' b' tr (aa x) = aa' x
-- -- -- -- -- -- -- -- -- --   mjo-ind' aa' bb' ab' b' tr (bb x) = bb' x
-- -- -- -- -- -- -- -- -- --   mjo-ind' aa' bb' ab' b' tr (ab x x₁ x₂) = ab' x x₁ x₂
-- -- -- -- -- -- -- -- -- --   mjo-ind' aa' bb' ab' b' tr (ar x a b x₁ i) = tr a .fst x a b x₁ i
-- -- -- -- -- -- -- -- -- --   mjo-ind' aa' bb' ab' b' tr (br x a b x₁ i) = b' b x a x₁ i
-- -- -- -- -- -- -- -- -- --   mjo-ind' aa' bb' ab' b' tr (rr a b c i) = tr a .snd b c .fst i
-- -- -- -- -- -- -- -- -- --   mjo-ind' aa' bb' ab' b' tr (rr' a b c x i i₁) = tr a .snd b c .snd x i i₁
-- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- --   mjo-ind : ∀ {ℓ} {B : Type ℓ}
-- -- -- -- -- -- -- -- -- --     → (aa' : ((x : fst X) → A' x) → B)
-- -- -- -- -- -- -- -- -- --     → (bb' : ((x : fst X) → B' x) → B)
-- -- -- -- -- -- -- -- -- --     → (ab' : (x : fst X) → A' x → B' (¬' x) → B)
-- -- -- -- -- -- -- -- -- --     → (ar' : (x : fst X) (a : (k : fst X) → A' k) (b : B' (¬' x))
-- -- -- -- -- -- -- -- -- --       → snd (a (¬' x)) ≡ b _ →  aa' a ≡ ab' _ (a x) b)
-- -- -- -- -- -- -- -- -- --     → ((b : (k : fst X) → B' k)
-- -- -- -- -- -- -- -- -- --         → Σ[ br' ∈ ((x : fst X) (a : A' x)
-- -- -- -- -- -- -- -- -- --                  → a .snd ≡ b x (fst a)
-- -- -- -- -- -- -- -- -- --                  → ab' x a (b (¬' x)) ≡ bb' b) ]
-- -- -- -- -- -- -- -- -- --             ((a : (x : fst X) → A' x) (c : (x : fst X) → a x .snd ≡ b x (fst (a x)))
-- -- -- -- -- -- -- -- -- --           → Σ[ rr ∈ aa' a ≡ bb' b ] ((x : fst X)
-- -- -- -- -- -- -- -- -- --             → PathP (λ i → ar' x a (b (¬' x)) (c _) i ≡ bb' b)
-- -- -- -- -- -- -- -- -- --                      rr (br' x (a x) (c x)))))
-- -- -- -- -- -- -- -- -- --     → mjo → B
-- -- -- -- -- -- -- -- -- --   mjo-ind aa' bb' ab' ar' tr (aa x) = aa' x
-- -- -- -- -- -- -- -- -- --   mjo-ind aa' bb' ab' ar' tr (bb x) = bb' x
-- -- -- -- -- -- -- -- -- --   mjo-ind aa' bb' ab' ar' tr (ab x x₁ x₂) = ab' x x₁ x₂
-- -- -- -- -- -- -- -- -- --   mjo-ind aa' bb' ab' ar' tr (ar x a b x₁ i) = ar' x a b x₁ i
-- -- -- -- -- -- -- -- -- --   mjo-ind aa' bb' ab' ar' tr (br x a b x₁ i) = tr b .fst x a x₁ i
-- -- -- -- -- -- -- -- -- --   mjo-ind aa' bb' ab' ar' tr (rr a b c i) = tr b .snd a c .fst i
-- -- -- -- -- -- -- -- -- --   mjo-ind aa' bb' ab' ar' tr (rr' a b c x i i₁) = tr b .snd a c .snd x i i₁
-- -- -- -- -- -- -- -- -- --   -}

-- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- module mjoind {ℓ} (X Y : RP∞) where
-- -- -- -- -- -- -- -- -- --   aa* : (A : fst X → fst Y → Type ℓ)
-- -- -- -- -- -- -- -- -- --   aa* = ?
-- -- -- -- -- -- -- -- -- -- -}
-- -- -- -- -- -- -- -- -- --   F : (f : fst X ≃ fst Y)
-- -- -- -- -- -- -- -- -- --     → ((x : _) → A x (fst f x))
-- -- -- -- -- -- -- -- -- --     → (y : fst Y)
-- -- -- -- -- -- -- -- -- --     → Σ (fst X) (λ x → A x y)
-- -- -- -- -- -- -- -- -- --   fst (F e f y) = invEq e y
-- -- -- -- -- -- -- -- -- --   snd (F e f y) = subst (A (invEq e y)) (secEq e y) (f (invEq e y))

-- -- -- -- -- -- -- -- -- --   M : (t : fst Y ⊎ (fst X ≃ fst Y))
-- -- -- -- -- -- -- -- -- --       → ((x : _) → A x (toFunz X Y t x))
-- -- -- -- -- -- -- -- -- --       → jo* Y λ y → jo* X λ x → A x y
-- -- -- -- -- -- -- -- -- --   M (inl x) p = inl (x , inr p)
-- -- -- -- -- -- -- -- -- --   M (inr x) p = inr λ y → inl (F x p y)

-- -- -- -- -- -- -- -- -- --   G : (fst X → fst Y) → fst Y ⊎ (fst X ≃ fst Y)
-- -- -- -- -- -- -- -- -- --   G = invEq (_ , isEq-toFunz X Y)

-- -- -- -- -- -- -- -- -- --   M₂ : (f : (x : fst X) → A' x) (x : fst X) → A x (toFunz X Y (G (λ x₁ → fst (f x₁))) x)
-- -- -- -- -- -- -- -- -- --   M₂ f x = subst (A x) (funExt⁻ (sym ((secEq (_ , isEq-toFunz X Y)) (fst ∘ f))) x)
-- -- -- -- -- -- -- -- -- --              (f x .snd)

-- -- -- -- -- -- -- -- -- --   test' : mjo → jo* Y λ y → jo* X λ x → A x y
-- -- -- -- -- -- -- -- -- --   test' =
-- -- -- -- -- -- -- -- -- --     mjo-ind' F1 F2 F3 F4
-- -- -- -- -- -- -- -- -- --       {!!}
-- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- --     TYP = jo* Y (λ y → jo* X (λ x → A x y))

-- -- -- -- -- -- -- -- -- --     F1 : ((x : fst X) → A' x) → TYP
-- -- -- -- -- -- -- -- -- --     F1 a = M (G (fst ∘ a)) (M₂ a)

-- -- -- -- -- -- -- -- -- --     F2 : ((x : fst X) → B' x) → TYP
-- -- -- -- -- -- -- -- -- --     F2 b = inr λ y → inr λ x → b x y

-- -- -- -- -- -- -- -- -- --     F3 : (x : fst X) → A' x → B' (¬' x) → TYP
-- -- -- -- -- -- -- -- -- --     F3 x (y , t) b = inl (y , inr (CasesRP X x t (b y)))

-- -- -- -- -- -- -- -- -- --     F4-gen : {!!}
-- -- -- -- -- -- -- -- -- --     F4-gen = {!!}

-- -- -- -- -- -- -- -- -- --     F4 : (b : (k : fst X) → B' k) (x : fst X) (a : A' x) →
-- -- -- -- -- -- -- -- -- --       a .snd ≡ b x (fst a) → F3 x a (b (¬' x)) ≡ F2 b
-- -- -- -- -- -- -- -- -- --     F4 b x (y , t) p =
-- -- -- -- -- -- -- -- -- --         {!!} -- cong (inl ∘ (y ,_)) {!!}
-- -- -- -- -- -- -- -- -- --       ∙ push (y , CasesRP Y y (inr (CasesRP X x t (b (¬' x) y))) (inr λ x → b x (not* Y y)))
-- -- -- -- -- -- -- -- -- --       ∙ {!!}
-- -- -- -- -- -- -- -- -- --       where
-- -- -- -- -- -- -- -- -- --       h : {!!} -- CasesRP Y y (inr (CasesRP X x t (b (¬' x) y))) (inr λ x → b x (not* Y y)) y ≡ {!inr !}
-- -- -- -- -- -- -- -- -- --       h = {!!}
  

-- -- -- -- -- -- -- -- -- --   test : mjo → jo* Y λ y → jo* X λ x → A x y
-- -- -- -- -- -- -- -- -- --   test (aa f) = M (G (fst ∘ f)) (M₂ f)
-- -- -- -- -- -- -- -- -- --   {- 
-- -- -- -- -- -- -- -- -- --     M (invEq (_ , isEq-toFunz X Y) (fst ∘ f))
-- -- -- -- -- -- -- -- -- --       λ x → subst (A x) (funExt⁻ (sym (secEq (_ , isEq-toFunz X Y) (fst ∘ f))) x)
-- -- -- -- -- -- -- -- -- --                      (f x .snd) -}
-- -- -- -- -- -- -- -- -- --   test (bb f) = inr λ y → inr λ x → f x y
-- -- -- -- -- -- -- -- -- --   test (ab x (y , a) f) = {!!}
-- -- -- -- -- -- -- -- -- --   test (ar x a b x₁ i) = {!!}
-- -- -- -- -- -- -- -- -- --   test (br x a b p i) = {!!}
-- -- -- -- -- -- -- -- -- --   test (rr a b c i) = Ml (G (λ x → fst (a x))) (M₂ a)
-- -- -- -- -- -- -- -- -- --     (funExt (λ x → (λ i → transp (λ j → A x (secEq (_ , isEq-toFunz X Y) (fst ∘ a) (i ∧ ~ j) x))
-- -- -- -- -- -- -- -- -- --                              (~ i) (b x (secEq (_ , isEq-toFunz X Y) (fst ∘ a) i x)))
-- -- -- -- -- -- -- -- -- --          ∙ cong (subst (A x) (funExt⁻ (sym ((secEq (_ , isEq-toFunz X Y)) (fst ∘ a))) x))
-- -- -- -- -- -- -- -- -- --              (sym (c x)))) i
-- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- --     inr* : _ → jo* Y λ y → jo* X λ x → A x y
-- -- -- -- -- -- -- -- -- --     inr* = inr

-- -- -- -- -- -- -- -- -- --     inl' : (y : _) → _ → jo* X λ x → A x y
-- -- -- -- -- -- -- -- -- --     inl' y = inl

-- -- -- -- -- -- -- -- -- --     Ml : (a : fst Y ⊎ (fst X ≃ fst Y)) (p : (x : fst X) → A x (toFunz X Y a x))
-- -- -- -- -- -- -- -- -- --       → (λ x → b _ _) ≡ p -- ((x : fst X) → p x ≡ b _ _)
-- -- -- -- -- -- -- -- -- --       → M a p
-- -- -- -- -- -- -- -- -- --       ≡ inr λ x → inr λ y → b y x
-- -- -- -- -- -- -- -- -- --     Ml (inl x) = J> push (x , λ y → inr λ x → b x y)
-- -- -- -- -- -- -- -- -- --     Ml (inr x) = J> cong inr* (funExt λ y
-- -- -- -- -- -- -- -- -- --        → cong (inl' y) (ΣPathP (refl
-- -- -- -- -- -- -- -- -- --                                , ((λ i → subst (A (invEq x y)) (λ j → secEq x y (j ∨ i))
-- -- -- -- -- -- -- -- -- --                                    (b (invEq x y) (secEq x y i ))) ∙ transportRefl (b (invEq x y) y))))
-- -- -- -- -- -- -- -- -- --       ∙ push ((invEq x y) , (λ x → b x y)))
-- -- -- -- -- -- -- -- -- --   test (rr' a b c x i i₁) = {!!}




-- -- -- -- -- -- -- -- -- -- module _ {ℓ : Level} (X Y : RP∞) (A : fst X → fst Y → Type ℓ) where
-- -- -- -- -- -- -- -- -- --   data jo' : Type ℓ where
-- -- -- -- -- -- -- -- -- --     aa : ((x : fst X) → Σ[ y ∈ fst Y ] (A x y)) → jo'
-- -- -- -- -- -- -- -- -- --     bb : ((x : fst X) (y : _) → A x y) → jo'
-- -- -- -- -- -- -- -- -- --     ac : (m : (x : fst X) → fst Y
-- -- -- -- -- -- -- -- -- --        × ((y : _) → (A x y))) → aa (λ x → m x .fst , m x .snd (m x .fst))
-- -- -- -- -- -- -- -- -- --        ≡ bb λ x → m x .snd

-- -- -- -- -- -- -- -- -- --   jo'' : jo' → (x : fst X) → jo Y (A x)
-- -- -- -- -- -- -- -- -- --   jo'' (aa f) x = makel (f x .snd)
-- -- -- -- -- -- -- -- -- --   jo'' (bb g) x = maker (g x)
-- -- -- -- -- -- -- -- -- --   jo'' (ac m i) x = pusher {x = m x .fst} (m x .snd) i

-- -- -- -- -- -- -- -- -- -- t2 : ∀ {ℓ} (A : Bool → Bool → Type ℓ)
-- -- -- -- -- -- -- -- -- --   → Iso (jo' Bool* Bool* A)
-- -- -- -- -- -- -- -- -- --   ((x : _) → jo Bool* (A x))
-- -- -- -- -- -- -- -- -- -- Iso.fun (t2 A) = jo'' Bool* Bool* A
-- -- -- -- -- -- -- -- -- -- Iso.inv (t2 A) f = h (f true) (f false)
-- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- --   B→B : (x y : Bool) → Bool → Bool
-- -- -- -- -- -- -- -- -- --   B→B x y false = y
-- -- -- -- -- -- -- -- -- --   B→B x y true = x

-- -- -- -- -- -- -- -- -- --   B→B' : (x y : Bool) (t : Bool) → A true x → A false y → A t (B→B x y t)
-- -- -- -- -- -- -- -- -- --   B→B' x y false le ri = ri
-- -- -- -- -- -- -- -- -- --   B→B' x y true le ri = le


-- -- -- -- -- -- -- -- -- --   h : jo Bool* (A true) → jo Bool* (A false) → jo' Bool* Bool* A
-- -- -- -- -- -- -- -- -- --   h (makel {x = x} a) (makel {x = y} b) = aa λ t → B→B x y t , B→B' x y t a b
-- -- -- -- -- -- -- -- -- --   h (makel {x = x} a) (maker f) = {!!}
-- -- -- -- -- -- -- -- -- --   h (makel x) (pusher f i) = {!!}
-- -- -- -- -- -- -- -- -- --   h (maker x) y = {!!}
-- -- -- -- -- -- -- -- -- --   h (pusher f i) y = {!!}



-- -- -- -- -- -- -- -- -- -- Iso.rightInv (t2 A) = {!!}
-- -- -- -- -- -- -- -- -- -- Iso.leftInv (t2 A) = {!!}

-- -- -- -- -- -- -- -- -- -- isEq'' : {ℓ : Level} (X Y : RP∞) (A : fst X → fst Y → Type ℓ)
-- -- -- -- -- -- -- -- -- --   → isEquiv ((jo'' X Y A))
-- -- -- -- -- -- -- -- -- -- isEq'' =
-- -- -- -- -- -- -- -- -- --   RP∞pt→Prop (λ _ → isPropΠ2 λ _ _ → isPropIsEquiv _)
-- -- -- -- -- -- -- -- -- --     (RP∞pt→Prop (λ _ → isPropΠ λ _ → isPropIsEquiv _ )
-- -- -- -- -- -- -- -- -- --       λ A → isoToIsEquiv (t2 A))

-- -- -- -- -- -- -- -- -- -- module palal' {ℓ : Level} (X Y : RP∞) (A : fst X → fst Y → Type ℓ) where

-- -- -- -- -- -- -- -- -- -- --   to' : jo' → ((x : fst X) → jo Y (A x))
-- -- -- -- -- -- -- -- -- -- --   to' (aa f) x = makel {X = Y} {A = A x} {x = f x .fst} (f x .snd)
-- -- -- -- -- -- -- -- -- -- --   to' (bb f) x = maker (f x)

-- -- -- -- -- -- -- -- -- -- --   2-j : jo X (λ x → jo Y (A x)) → (jo Y λ y → jo X (λ x → A x y))
-- -- -- -- -- -- -- -- -- -- --   2-j (makel (makel x)) = makel (makel x)
-- -- -- -- -- -- -- -- -- -- --   2-j (makel (maker f)) = maker λ y → makel (f y)
-- -- -- -- -- -- -- -- -- -- --   2-j (makel (pusher {x = x} f i)) = {!!} -- maker λ y → makel {!f y!}
-- -- -- -- -- -- -- -- -- -- --   2-j (maker f) = {!f!}
-- -- -- -- -- -- -- -- -- -- --   2-j (pusher f i) = {!!}



-- -- -- -- -- -- -- -- -- -- -- joinish : ∀ {ℓ} (X : RP∞) (A : fst X → Type ℓ) → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- joinish X A = Pushout {A = (x : _) → A x} {B = Σ _ A} {C = {!!}} {!!} {!!}


-- -- -- -- -- -- -- -- -- -- -- SM→Homogeneous≡ : ∀ {ℓ ℓ'} (X : RP∞) (x : fst X) {A : fst X → Pointed ℓ} {B : Pointed ℓ'}
-- -- -- -- -- -- -- -- -- -- --   → {f g : SM∙ X A →∙ B}
-- -- -- -- -- -- -- -- -- -- --   → isHomogeneous B
-- -- -- -- -- -- -- -- -- -- --   → ((t : (x : fst X) → A x .fst)
-- -- -- -- -- -- -- -- -- -- --   → fst f (inr t) ≡ fst g (inr t)) → f ≡ g -- f ≡ g
-- -- -- -- -- -- -- -- -- -- -- SM→Homogeneous≡ {ℓ = ℓ} {ℓ' = ℓ'} = J2-elem _ .fst f≡g
-- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- --   module _ {A : Bool → Pointed ℓ} {B : Pointed ℓ'} {f g : SM∙ Bool* A →∙ B}
-- -- -- -- -- -- -- -- -- -- --            (hom : isHomogeneous B)
-- -- -- -- -- -- -- -- -- -- --            (r : ((t : (x : fst Bool*) → A x .fst)
-- -- -- -- -- -- -- -- -- -- --               → fst f (inr t) ≡ fst g (inr t)))where
-- -- -- -- -- -- -- -- -- -- --     F = isoToEquiv (Iso-Smash-SM' {A = A})
-- -- -- -- -- -- -- -- -- -- --     G = Iso-Smash-SM'∙ {A = A} .snd

-- -- -- -- -- -- -- -- -- -- --     theIso : Iso (Smash∙ (A false) (A true) →∙ B) (SM∙ Bool* A →∙ B)
-- -- -- -- -- -- -- -- -- -- --     theIso = post∘∙equiv Iso-Smash-SM'∙

-- -- -- -- -- -- -- -- -- -- --     s = Iso.inv theIso

-- -- -- -- -- -- -- -- -- -- --     fs : (x : A true .fst) (y : A false .fst) (x₁ : Bool) → fst (A x₁)
-- -- -- -- -- -- -- -- -- -- --     fs x y true = x
-- -- -- -- -- -- -- -- -- -- --     fs x y false = y

-- -- -- -- -- -- -- -- -- -- --     lem : s f ≡ s g
-- -- -- -- -- -- -- -- -- -- --     lem = Smash→∙Homogeneous≡ hom λ x y
-- -- -- -- -- -- -- -- -- -- --       → cong (fst f) (Iso-Smash-SM'-proj' (fs y x))
-- -- -- -- -- -- -- -- -- -- --        ∙∙ r (fs y x)
-- -- -- -- -- -- -- -- -- -- --        ∙∙ sym (cong (fst g) (Iso-Smash-SM'-proj' (fs y x)))

-- -- -- -- -- -- -- -- -- -- --     f≡g : f ≡ g
-- -- -- -- -- -- -- -- -- -- --     f≡g = sym (Iso.rightInv theIso f)
-- -- -- -- -- -- -- -- -- -- --        ∙∙ cong (Iso.fun theIso) lem
-- -- -- -- -- -- -- -- -- -- --        ∙∙ Iso.rightInv theIso g



-- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- --   ΣPathP ((funExt (λ { (inl x) → {!!}
-- -- -- -- -- -- -- -- -- -- --                      ; (inr x) → {!!}
-- -- -- -- -- -- -- -- -- -- --                      ; (push a i) → {!!}}))
-- -- -- -- -- -- -- -- -- -- --         , {!!})
-- -- -- -- -- -- -- -- -- -- -- -}


-- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- module _ (I J : RP∞) (A : fst I → fst J → Pointed₀) where
-- -- -- -- -- -- -- -- -- -- --   ΠJA : fst I → Type
-- -- -- -- -- -- -- -- -- -- --   ΠJA i = (j : fst J) → A i j .fst

-- -- -- -- -- -- -- -- -- -- --   n : fst I → fst I
-- -- -- -- -- -- -- -- -- -- --   n = not* I

-- -- -- -- -- -- -- -- -- -- --   R : {i : fst I} → fst J → ΠJA i → Type
-- -- -- -- -- -- -- -- -- -- --   R {i = i} j f = Σ[ x ∈ fst (A i j) ] f ≡ CasesRP J j x (A i (not* J j) .snd)

-- -- -- -- -- -- -- -- -- -- --   data toSm : Type where
-- -- -- -- -- -- -- -- -- -- --     aa : ((i : fst I) → fst J) → toSm
-- -- -- -- -- -- -- -- -- -- --     bb : ((i : fst I) → ΠJA i) → toSm
-- -- -- -- -- -- -- -- -- -- --     ab : (i : fst I) →  fst J → ΠJA i → toSm
-- -- -- -- -- -- -- -- -- -- --     ar : (i : fst I) (a : fst I → fst J) (b : ΠJA i) → R (a i) b → aa a ≡ ab i (a i) b
-- -- -- -- -- -- -- -- -- -- --     br : (i : fst I) (a : fst J) (b : (i : fst I) → ΠJA i) → R a (b i) → ab i a (b (i)) ≡ bb b
-- -- -- -- -- -- -- -- -- -- --     rr : (a : (i : fst I) → fst J) (b : (i : fst I) → ΠJA i)
-- -- -- -- -- -- -- -- -- -- --       → ((i : fst I) → R (a i) (b i)) → aa a ≡ bb b
-- -- -- -- -- -- -- -- -- -- --     rr' :  (i : fst I) (a : (i : fst I) → fst J)
-- -- -- -- -- -- -- -- -- -- --            (b : (i : fst I) → ΠJA i)
-- -- -- -- -- -- -- -- -- -- --            (r : (i : fst I) → R (a i) (b i))
-- -- -- -- -- -- -- -- -- -- --         → PathP (λ k → aa a ≡ br i (a i) b (r i) (~ k)) (rr a b r) (ar i a (b (i)) (r (i)))

-- -- -- -- -- -- -- -- -- -- --   HH = SM J λ j → SM I (λ i → A i j) , inr λ i → A i j .snd
-- -- -- -- -- -- -- -- -- -- --   HH' : (j : fst J) → Type
-- -- -- -- -- -- -- -- -- -- --   HH' j = SM I (λ i → A i j)

-- -- -- -- -- -- -- -- -- -- --   ploink : toSm → SM J λ j → SM I (λ i → A i j) , inr λ i → A i j .snd
-- -- -- -- -- -- -- -- -- -- --   ploink (aa g) = inr λ j → inr λ i → A i j .snd -- inr λ j → inr {!!}
-- -- -- -- -- -- -- -- -- -- --   ploink (bb f) = inr λ j → inr λ i → f i j
-- -- -- -- -- -- -- -- -- -- --   ploink (ab i j t) = inl j
-- -- -- -- -- -- -- -- -- -- --   ploink (ar i a b (x , y) i₁) = {!!}
-- -- -- -- -- -- -- -- -- -- --     where

-- -- -- -- -- -- -- -- -- -- --     P1 : (j : _) → Path ((i : fst I) → A i j .fst) (λ i → A i j .snd) {!CasesRP J j ? ?!}
-- -- -- -- -- -- -- -- -- -- --     P1 = {!!}

-- -- -- -- -- -- -- -- -- -- --     PP' : (j : fst J) → (j ≡ a i) ⊎ (j ≡ {!a i!}) → Path (HH' j) (inr (λ i₂ → A i₂ j .snd)) (inr {!!}) -- (CasesRP I i (b j) (A (not* I i) j .snd)))
-- -- -- -- -- -- -- -- -- -- --     PP' j p = {!!}

-- -- -- -- -- -- -- -- -- -- --     PP : Path HH (inr (λ j → inr (λ i₂ → A i₂ j .snd))) (inl (a i))
-- -- -- -- -- -- -- -- -- -- --     PP = {!!} ∙ {!!} ∙ sym (push ((a i) , (inr (λ i₂ → A i₂ (a i) .snd))))
-- -- -- -- -- -- -- -- -- -- --   ploink (br i a b (x , y) i₁) = {!!}
-- -- -- -- -- -- -- -- -- -- --   ploink (rr g f h i) = {!!}
-- -- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- -- --     c2 : (j : fst J) → Path ((i : fst I) → A i j .fst)
-- -- -- -- -- -- -- -- -- -- --                         {!CasesRP I ? ?!}
-- -- -- -- -- -- -- -- -- -- --                         λ i₂ → CasesRP J (g i₂)
-- -- -- -- -- -- -- -- -- -- --                             (fst (h i₂)) (A i₂ (not* J (g i₂)) .snd) j
-- -- -- -- -- -- -- -- -- -- --     c2 j = {!!}

-- -- -- -- -- -- -- -- -- -- --     brr : Path ((j : fst J) → HH' j) (λ j → inr (λ i₁ → A i₁ j .snd)) λ j → inr (λ i₁ → f i₁ j)
-- -- -- -- -- -- -- -- -- -- --     brr = funExt λ j → ({!!} ∙ sym (push ({!!} , {!!})) ∙ {!!}) ∙ λ k → inr λ i → h i .snd (~ k) j
-- -- -- -- -- -- -- -- -- -- --   ploink (rr' i a b r k i₁) = {!!}



-- -- -- -- -- -- -- -- -- -- -- data asd (X : RP∞) (A : fst X → Type) (B : Type) : Type where
-- -- -- -- -- -- -- -- -- -- --   incc : ((x : fst X) → A x → A (not* X x) → B) → asd X A B
-- -- -- -- -- -- -- -- -- -- --   incr : ((x : fst X) → A x → B) → {!? !}
-- -- -- -- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- -- -- -- SS₀ : Type
-- -- -- -- -- -- -- -- -- -- -- SS₀ = Bool

-- -- -- -- -- -- -- -- -- -- -- data genSusp {ℓ : Level} (X : RP∞) (A : Type ℓ) : Type ℓ where
-- -- -- -- -- -- -- -- -- -- --   pts : fst X → genSusp X A
-- -- -- -- -- -- -- -- -- -- --   mrd : (x : fst X) (a : A) → pts x ≡ pts (not* X x)

-- -- -- -- -- -- -- -- -- -- -- data seq-colim {ℓ : Level} (A : ℕ → Type ℓ) (f : (n : ℕ) → A n → A (suc n)) : Type ℓ where
-- -- -- -- -- -- -- -- -- -- --   mk : (n : ℕ) → A n → seq-colim A f
-- -- -- -- -- -- -- -- -- -- --   tr : (n : ℕ) (x : A n) → mk n x ≡ mk (suc n) (f n x)


-- -- -- -- -- -- -- -- -- -- -- SS-g : (X : RP∞) (n : ℕ) → Type
-- -- -- -- -- -- -- -- -- -- -- SS-g X zero = fst X
-- -- -- -- -- -- -- -- -- -- -- SS-g X (suc n) = genSusp X (SS-g X n)

-- -- -- -- -- -- -- -- -- -- -- SS-fun : (X : RP∞) (n : ℕ) → SS-g X n → SS-g X (suc n)
-- -- -- -- -- -- -- -- -- -- -- bataclan : (X : RP∞) (A : fst X → Pointed₀)
-- -- -- -- -- -- -- -- -- -- --   → ((x y : fst X) → isContr (A x ≡ A y))
-- -- -- -- -- -- -- -- -- -- --   → ∥ fst X ∥₁ → Pointed₀
-- -- -- -- -- -- -- -- -- -- -- bataclan X A t ∣ x ∣₁ = A x
-- -- -- -- -- -- -- -- -- -- -- bataclan X A t (squash₁ m a i) = PT.elim2 {P = λ a m → isContr (bataclan X A t a ≡ bataclan X A t m)} (λ _ _ → isPropIsContr) t m a .fst i

-- -- -- -- -- -- -- -- -- -- -- SS-fun X zero t = pts t
-- -- -- -- -- -- -- -- -- -- -- SS-fun X (suc n) (pts x) = pts x
-- -- -- -- -- -- -- -- -- -- -- SS-fun X (suc n) (mrd x a i) = mrd x (SS-fun X n a) i

-- -- -- -- -- -- -- -- -- -- -- SS-fun-const : (n : ℕ) (t : SS-g Bool* n)
-- -- -- -- -- -- -- -- -- -- --   → SS-fun Bool* n t ≡ pts true
-- -- -- -- -- -- -- -- -- -- -- SS-fun-const zero false = mrd false true
-- -- -- -- -- -- -- -- -- -- -- SS-fun-const zero true = refl
-- -- -- -- -- -- -- -- -- -- -- SS-fun-const (suc n) (pts false) = mrd false (pts true)
-- -- -- -- -- -- -- -- -- -- -- SS-fun-const (suc n) (pts true) = refl
-- -- -- -- -- -- -- -- -- -- -- SS-fun-const (suc n) (mrd false a i) j =
-- -- -- -- -- -- -- -- -- -- --   hcomp (λ k → λ {(i = i0) → mrd false (pts true) j
-- -- -- -- -- -- -- -- -- -- --                  ; (i = i1) → pts true
-- -- -- -- -- -- -- -- -- -- --                  ; (j = i0) → mrd false (SS-fun-const n a (~ k)) i
-- -- -- -- -- -- -- -- -- -- --                  ; (j = i1) → pts true})
-- -- -- -- -- -- -- -- -- -- --         (mrd false (pts true) (j ∨ i))
-- -- -- -- -- -- -- -- -- -- -- SS-fun-const (suc n) (mrd true a i) j =
-- -- -- -- -- -- -- -- -- -- --   hcomp (λ k → λ {(i = i0) → pts true
-- -- -- -- -- -- -- -- -- -- --                  ; (i = i1) → mrd false (pts true) j
-- -- -- -- -- -- -- -- -- -- --                  ; (j = i0) → mrd true (SS-fun-const n a (~ k)) i
-- -- -- -- -- -- -- -- -- -- --                  ; (j = i1) → pts true})
-- -- -- -- -- -- -- -- -- -- --         {!!} -- (mrd false (pts {!!}) {!i0!})

-- -- -- -- -- -- -- -- -- -- -- SSP = seq-colim (SS-g Bool*) (SS-fun Bool*)

-- -- -- -- -- -- -- -- -- -- -- SS-fun-const' : (n : ℕ) (t : SS-g Bool* n)
-- -- -- -- -- -- -- -- -- -- --   → Path SSP (mk (suc n) (SS-fun Bool* n t)) -- 
-- -- -- -- -- -- -- -- -- -- --               (mk (suc n) (pts true))
-- -- -- -- -- -- -- -- -- -- -- SS-fun-const' zero false = cong (mk 1) (mrd false true)
-- -- -- -- -- -- -- -- -- -- -- SS-fun-const' zero true = refl
-- -- -- -- -- -- -- -- -- -- -- SS-fun-const' (suc n) (pts false) = cong (mk (2 + n)) (mrd false (pts true))
-- -- -- -- -- -- -- -- -- -- -- SS-fun-const' (suc n) (pts true) = refl
-- -- -- -- -- -- -- -- -- -- -- SS-fun-const' (suc n) (mrd false a i) j =
-- -- -- -- -- -- -- -- -- -- --   hcomp (λ k → λ {(i = i0) → {!cong (mk (2 + n)) (mrd false (pts true)) k!} -- tr {f = SS-fun Bool*} (suc n) (mrd {!!} {!!} {!j!}) k
-- -- -- -- -- -- -- -- -- -- --                     ; (i = i1) → {!tr (suc n) (pts true) k ?!}
-- -- -- -- -- -- -- -- -- -- --                     ; (j = i0) → tr {f = SS-fun Bool*} (suc n) (mrd false a i) k -- 
-- -- -- -- -- -- -- -- -- -- --                     ; (j = i1) → {!!}})
-- -- -- -- -- -- -- -- -- -- --            {!!}
-- -- -- -- -- -- -- -- -- -- -- SS-fun-const' (suc n) (mrd true a i) j = {!!}
-- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- --   hcomp (λ k → λ {(i = i0) → {!SS-fun-const' (suc n) (pts t) j!}
-- -- -- -- -- -- -- -- -- -- --                     ; (i = i1) → {!tr (suc n) (mrd t a i) k!}
-- -- -- -- -- -- -- -- -- -- --                     ; (j = i0) → tr (suc n) (mrd t a i) k
-- -- -- -- -- -- -- -- -- -- --                     ; (j = i1) → {!!}})
-- -- -- -- -- -- -- -- -- -- --            {!!}
-- -- -- -- -- -- -- -- -- -- -- -}
-- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- i = i0 ⊢ SS-fun-const' (suc n) (pts t) j
-- -- -- -- -- -- -- -- -- -- -- i = i1 ⊢ SS-fun-const' (suc n) (pts (not* Bool* t)) j
-- -- -- -- -- -- -- -- -- -- -- j = i0 ⊢ mk (suc (suc n)) (SS-fun Bool* (suc n) (mrd t a i))
-- -- -- -- -- -- -- -- -- -- -- j = i1 ⊢ mk (suc (suc n)) (pts true)
-- -- -- -- -- -- -- -- -- -- -- -}
-- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- --    mk (2 + n)
-- -- -- -- -- -- -- -- -- -- --     (hcomp (λ k → λ {(i = i0) → mrd false (pts true) j
-- -- -- -- -- -- -- -- -- -- --                     ; (i = i1) → pts true
-- -- -- -- -- -- -- -- -- -- --                     ; (j = i0) → mrd false (SS-fun-const n a (~ k)) i
-- -- -- -- -- -- -- -- -- -- --                     ; (j = i1) → pts true})
-- -- -- -- -- -- -- -- -- -- --            (mrd false (pts true) (j ∨ i)))

-- -- -- -- -- -- -- -- -- -- -- {-


-- -- -- -- -- -- -- -- -- -- -- -}
-- -- -- -- -- -- -- -- -- -- -- SS-fun-const' (suc n) (mrd true a i) j =
-- -- -- -- -- -- -- -- -- -- --   hcomp (λ k → λ {(i = i0) → mk (2 + n) (pts true)
-- -- -- -- -- -- -- -- -- -- --                  ; (i = i1) → mk (2 + n) (mrd false (pts true) j)
-- -- -- -- -- -- -- -- -- -- --                  ; (j = i0) → {!!}  -- mk (2 + n) (mrd true (SS-fun-const n a (~ k)) i)
-- -- -- -- -- -- -- -- -- -- --                  ; (j = i1) → mk (2 + n) (pts true)})
-- -- -- -- -- -- -- -- -- -- --          {!SS-fun-const' n a i0!} -}
-- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- --   hcomp (λ k → λ {(i = i0) → mk (2 + n) (pts true)
-- -- -- -- -- -- -- -- -- -- --                  ; (i = i1) → mk (2 + n) (mrd false (pts true) j)
-- -- -- -- -- -- -- -- -- -- --                  ; (j = i0) → mk (2 + n) (mrd true (SS-fun-const n a (~ k)) i)
-- -- -- -- -- -- -- -- -- -- --                  ; (j = i1) → mk (2 + n) (pts true)})
-- -- -- -- -- -- -- -- -- -- --    (hcomp (λ k → λ {(i = i0) → {!!}
-- -- -- -- -- -- -- -- -- -- --                  ; (i = i1) → tr (suc n) {!pts true!} k
-- -- -- -- -- -- -- -- -- -- --                  ; (j = i0) → {!!}
-- -- -- -- -- -- -- -- -- -- --                  ; (j = i1) → {!!}})
-- -- -- -- -- -- -- -- -- -- --           {!!})
-- -- -- -- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- -- -- -- contr : (n : ℕ) (t : SS-g Bool* (suc n)) → Path SSP (mk (suc n) t) (mk n {!!})
-- -- -- -- -- -- -- -- -- -- -- contr = {!!}
-- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- fst contr = mk 0 true
-- -- -- -- -- -- -- -- -- -- -- snd contr (mk zero false) =
-- -- -- -- -- -- -- -- -- -- --   tr 0 true ∙∙ cong (mk 1) (mrd true true) ∙∙ sym (tr 0 false)
-- -- -- -- -- -- -- -- -- -- -- snd contr (mk zero true) = refl
-- -- -- -- -- -- -- -- -- -- -- snd contr (mk (suc zero) (pts false)) = tr 0 true ∙ cong (mk 1) (mrd true true)
-- -- -- -- -- -- -- -- -- -- -- snd contr (mk (suc zero) (pts true)) = tr 0 true
-- -- -- -- -- -- -- -- -- -- -- snd contr (mk (suc zero) (mrd false false i)) j = {!!}
-- -- -- -- -- -- -- -- -- -- -- snd contr (mk (suc zero) (mrd false true i)) j = {!!}
-- -- -- -- -- -- -- -- -- -- -- snd contr (mk (suc zero) (mrd true false i)) j = {!!}
-- -- -- -- -- -- -- -- -- -- -- snd contr (mk (suc zero) (mrd true true i)) j = {!!}
-- -- -- -- -- -- -- -- -- -- -- snd contr (mk (suc (suc n)) x) = {!!}
-- -- -- -- -- -- -- -- -- -- -- snd contr (tr zero false i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- snd contr (tr zero true i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- snd contr (tr (suc zero) x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- snd contr (tr (suc (suc n)) x i) = {!x!}
-- -- -- -- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- -- -- -- BIG : ∀ {ℓ} (X Y : RP∞) (A : fst X → fst Y → Pointed ℓ)
-- -- -- -- -- -- -- -- -- -- --   → (x : fst X) (y : fst Y)
-- -- -- -- -- -- -- -- -- -- --   → Pointed ℓ
-- -- -- -- -- -- -- -- -- -- -- BIG X Y A x y =
-- -- -- -- -- -- -- -- -- -- --   Smash∙ (Smash∙ (A (not* X x) (not* Y y)) (A (not* X x) y))
-- -- -- -- -- -- -- -- -- -- --              (Smash∙ (A x (not* Y y)) (A x y))

-- -- -- -- -- -- -- -- -- -- -- myG-innerest : ∀ {ℓ ℓ'} (B : Pointed ℓ)  (A : fst Bool* → fst Bool* → Pointed ℓ') →
-- -- -- -- -- -- -- -- -- -- --       BIG Bool* Bool* A true true →∙ SM∙ Bool* (λ x₁ → SM∙ Bool* (A x₁))
-- -- -- -- -- -- -- -- -- -- -- myG-innerest B A = ≃∙map (Iso-Smash-SM'∙)
-- -- -- -- -- -- -- -- -- -- --             ∘∙ (Smash-map (≃∙map (Iso-Smash-SM'∙ {A = λ x → A false x}))
-- -- -- -- -- -- -- -- -- -- --                 (≃∙map (Iso-Smash-SM'∙ {A = λ x → A true x})) , refl)

-- -- -- -- -- -- -- -- -- -- -- myG-inner : ∀ {ℓ ℓ'} (B : Pointed ℓ) (Y : RP∞) (y : fst Y)
-- -- -- -- -- -- -- -- -- -- --   (A : fst Bool* → fst Y → Pointed ℓ') →
-- -- -- -- -- -- -- -- -- -- --       BIG Bool* Y A true y →∙ SM∙ Bool* (λ x₁ → SM∙ Y (A x₁))
-- -- -- -- -- -- -- -- -- -- -- myG-inner {ℓ' = ℓ'} B =
-- -- -- -- -- -- -- -- -- -- --   J2-elem (λ Y y → (A : fst Bool* → fst Y → Pointed ℓ') →
-- -- -- -- -- -- -- -- -- -- --       BIG Bool* Y A true y →∙ SM∙ Bool* (λ x₁ → SM∙ Y (A x₁))) .fst
-- -- -- -- -- -- -- -- -- -- --       (myG-innerest B)

-- -- -- -- -- -- -- -- -- -- -- myG :  ∀ {ℓ ℓ'} (B : Pointed ℓ)
-- -- -- -- -- -- -- -- -- -- --   (X : RP∞) (x : fst X)
-- -- -- -- -- -- -- -- -- -- --   (Y : RP∞) (y : fst Y)
-- -- -- -- -- -- -- -- -- -- --   (A : fst X → fst Y → Pointed ℓ')
-- -- -- -- -- -- -- -- -- -- --   → BIG X Y A x y
-- -- -- -- -- -- -- -- -- -- --   →∙ (SM∙ X (λ x → SM∙ Y (A x)))
-- -- -- -- -- -- -- -- -- -- -- myG {ℓ}{ℓ'} B = J2-elem (λ X x → (Y : RP∞) (y : fst Y)
-- -- -- -- -- -- -- -- -- -- --       (A : fst X → fst Y → Pointed ℓ') →
-- -- -- -- -- -- -- -- -- -- --       BIG X Y A x y →∙ SM∙ X (λ x₁ → SM∙ Y (A x₁)))
-- -- -- -- -- -- -- -- -- -- --       .fst
-- -- -- -- -- -- -- -- -- -- --       (myG-inner B)
-- -- -- -- -- -- -- -- -- -- --       {-
-- -- -- -- -- -- -- -- -- -- --       (J2-elem (λ Y y → (A : fst Bool* → fst Y → Pointed ℓ') →
-- -- -- -- -- -- -- -- -- -- --       BIG Bool* Y A true y →∙ SM∙ Bool* (λ x₁ → SM∙ Y (A x₁))) .fst
-- -- -- -- -- -- -- -- -- -- --       λ A → ≃∙map (Iso-Smash-SM'∙)
-- -- -- -- -- -- -- -- -- -- --             ∘∙ (Smash-map (≃∙map (Iso-Smash-SM'∙ {A = λ x → A false x}))
-- -- -- -- -- -- -- -- -- -- --                 (≃∙map (Iso-Smash-SM'∙ {A = λ x → A true x})) , refl))
-- -- -- -- -- -- -- -- -- -- -- -}
-- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- --  J2-elem _ .fst
-- -- -- -- -- -- -- -- -- -- --   (J2-elem _ .fst λ A → ≃∙map (Iso-Smash-SM'∙)
-- -- -- -- -- -- -- -- -- -- --             ∘∙ (Smash-map (≃∙map (Iso-Smash-SM'∙ {A = λ x → A false x}))
-- -- -- -- -- -- -- -- -- -- --                 (≃∙map (Iso-Smash-SM'∙ {A = λ x → A true x})) , refl))
-- -- -- -- -- -- -- -- -- -- -- -}
-- -- -- -- -- -- -- -- -- -- -- theF : ∀ {ℓ ℓ'} (B : Pointed ℓ)
-- -- -- -- -- -- -- -- -- -- --   (X : RP∞) (x : fst X)
-- -- -- -- -- -- -- -- -- -- --   (Y : RP∞) (y : fst Y)
-- -- -- -- -- -- -- -- -- -- --   (A : fst X → fst Y → Pointed ℓ')
-- -- -- -- -- -- -- -- -- -- --   → (SM∙ X (λ x → SM∙ Y (A x)) →∙ B)
-- -- -- -- -- -- -- -- -- -- --   →  BIG X Y A x y →∙ B
-- -- -- -- -- -- -- -- -- -- -- theF B X x Y y A = _∘∙ myG B X x Y y A

-- -- -- -- -- -- -- -- -- -- -- myGβ : ∀ {ℓ ℓ'} (B : Pointed ℓ)
-- -- -- -- -- -- -- -- -- -- --   (X : RP∞) (x : fst X)
-- -- -- -- -- -- -- -- -- -- --   (Y : RP∞) (y : fst Y)
-- -- -- -- -- -- -- -- -- -- --   (A : fst X → fst Y → Pointed ℓ')
-- -- -- -- -- -- -- -- -- -- --   (f : (x : fst X) (y : fst Y) → A x y .fst)
-- -- -- -- -- -- -- -- -- -- --   → myG B X x Y y A .fst (proj (proj (f _ _) (f _ _)) (proj (f _ _) (f _ _)))
-- -- -- -- -- -- -- -- -- -- --     ≡ inr (λ x → inr λ y → f x y)
-- -- -- -- -- -- -- -- -- -- -- myGβ {ℓ} {ℓ'} B = J2-elem _ .fst (J2-elem _ .fst
-- -- -- -- -- -- -- -- -- -- --   λ A f → t A _
-- -- -- -- -- -- -- -- -- -- --         ∙ cong (Iso.fun (Iso-Smash-SM' {A = λ x → SM∙ Bool* (A x)}))
-- -- -- -- -- -- -- -- -- -- --                (λ i → proj (l1 A f i) (l2 A f i))
-- -- -- -- -- -- -- -- -- -- --         ∙ cong (inr* A) (funExt λ { false → transportRefl (inr (f false))
-- -- -- -- -- -- -- -- -- -- --                                   ; true → transportRefl (inr (f true))}))
-- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- --   inr* : (A : Bool → Bool → Pointed _) → _ → SM Bool* (λ x → SM∙ Bool* (A x))
-- -- -- -- -- -- -- -- -- -- --   inr* A = inr
-- -- -- -- -- -- -- -- -- -- --   module _ (A : fst Bool* → fst Bool* → Pointed ℓ')
-- -- -- -- -- -- -- -- -- -- --            (f : (x y : fst Bool*) → A x y .fst) where
-- -- -- -- -- -- -- -- -- -- --     l1 : Iso.fun (Iso-Smash-SM' {A = A false})
-- -- -- -- -- -- -- -- -- -- --           (proj (f false false) (f false true))
-- -- -- -- -- -- -- -- -- -- --        ≡ inr (f false)
-- -- -- -- -- -- -- -- -- -- --     l1  = Iso-Smash-SM'-proj' (f false)

-- -- -- -- -- -- -- -- -- -- --     l2 : Iso.fun (Iso-Smash-SM' {A = A true})
-- -- -- -- -- -- -- -- -- -- --           (proj (f true false) (f true true))
-- -- -- -- -- -- -- -- -- -- --        ≡ inr (f true)
-- -- -- -- -- -- -- -- -- -- --     l2 = Iso-Smash-SM'-proj' (f true)

-- -- -- -- -- -- -- -- -- -- --   help : myG B Bool* true ≡ myG-inner B
-- -- -- -- -- -- -- -- -- -- --   help = J2-elem (λ X x → (Y : RP∞) (y : fst Y)
-- -- -- -- -- -- -- -- -- -- --       (A : fst X → fst Y → Pointed ℓ') →
-- -- -- -- -- -- -- -- -- -- --       BIG X Y A x y →∙ SM∙ X (λ x₁ → SM∙ Y (A x₁)))
-- -- -- -- -- -- -- -- -- -- --       .snd (myG-inner B)
-- -- -- -- -- -- -- -- -- -- --       ∙ refl

-- -- -- -- -- -- -- -- -- -- --   help2 : myG-inner B Bool* true ≡ myG-innerest B
-- -- -- -- -- -- -- -- -- -- --   help2 = J2-elem (λ Y y → (A : fst Bool* → fst Y → Pointed ℓ') →
-- -- -- -- -- -- -- -- -- -- --       BIG Bool* Y A true y →∙ SM∙ Bool* (λ x₁ → SM∙ Y (A x₁))) .snd
-- -- -- -- -- -- -- -- -- -- --       (myG-innerest B)

-- -- -- -- -- -- -- -- -- -- --   t : (A : _) (z : _) → myG B Bool* true Bool* true A .fst z
-- -- -- -- -- -- -- -- -- -- --                       ≡  myG-innerest B A .fst z
-- -- -- -- -- -- -- -- -- -- --   t A z = (λ i → help i Bool* true A .fst z) ∙ (λ i → help2 i A .fst z)

-- -- -- -- -- -- -- -- -- -- -- theF-real : ∀ {ℓ ℓ'} (B : Pointed ℓ)
-- -- -- -- -- -- -- -- -- -- --   (X Y : RP∞)
-- -- -- -- -- -- -- -- -- -- --   (A : fst X → fst Y → Pointed ℓ')
-- -- -- -- -- -- -- -- -- -- --   → (SM∙ X (λ x → SM∙ Y (A x)) →∙ B)
-- -- -- -- -- -- -- -- -- -- --   → ((x : fst X) (y : fst Y) → BIG X Y A x y →∙ B)
-- -- -- -- -- -- -- -- -- -- -- theF-real B X Y A f x y = theF B X x Y y A f

-- -- -- -- -- -- -- -- -- -- -- theF-real-β : ∀ {ℓ ℓ'} (B : Pointed ℓ)
-- -- -- -- -- -- -- -- -- -- --   (X : RP∞) (Y : RP∞)
-- -- -- -- -- -- -- -- -- -- --   (A : fst X → fst Y → Pointed ℓ')
-- -- -- -- -- -- -- -- -- -- --   (r : _)
-- -- -- -- -- -- -- -- -- -- --   (f : (x : fst X) (y : fst Y) → A x y .fst)
-- -- -- -- -- -- -- -- -- -- --   (x : fst X) (y : fst Y)
-- -- -- -- -- -- -- -- -- -- --   → theF-real B X Y A r x y .fst ((proj (proj (f _ _) (f _ _)) (proj (f _ _) (f _ _))))
-- -- -- -- -- -- -- -- -- -- --   ≡ fst r (inr (λ x → inr λ y → f x y))
-- -- -- -- -- -- -- -- -- -- -- theF-real-β B X Y A r f x y = cong (fst r) (myGβ B X x Y y A f)

-- -- -- -- -- -- -- -- -- -- -- data _** (X : RP∞) : Type where
-- -- -- -- -- -- -- -- -- -- --   [[_]] : fst X → X **
-- -- -- -- -- -- -- -- -- -- --   sq : (x : fst X) → [[ x ]] ≡ [[ not* X x ]]

-- -- -- -- -- -- -- -- -- -- -- module _ (A : Bool* ** → Pointed₀) (ppp : (x : _) → PathP (λ i → A [[ notnot x (~ i) ]] .fst ≡ A [[ not x ]] .fst) (cong (fst ∘ A) (sq x)) (cong (fst ∘ A) (sym (sq (not x))))) where
-- -- -- -- -- -- -- -- -- -- --   module _ (Z : (x : _) → (fst (A x)) → Type) where
-- -- -- -- -- -- -- -- -- -- --     p1 : (a : _) (b : _) → PathP (λ i → (x : fst (A (sq false i))) → Z (sq false i) x) a b
-- -- -- -- -- -- -- -- -- -- --                          → PathP (λ i → (x : fst (A (sq true (~ i)))) → Z (sq true (~ i)) x) a b
-- -- -- -- -- -- -- -- -- -- --     p1 a b Q = toPathP (funExt λ x → {!!} ∙ {!!})

-- -- -- -- -- -- -- -- -- -- --     FF : S¹ → Bool* **
-- -- -- -- -- -- -- -- -- -- --     FF base = [[ true ]]
-- -- -- -- -- -- -- -- -- -- --     FF (loop i) = (sq true ∙ sq false) i

-- -- -- -- -- -- -- -- -- -- --     FF* : Bool* ** → S¹
-- -- -- -- -- -- -- -- -- -- --     FF* [[ false ]] = base
-- -- -- -- -- -- -- -- -- -- --     FF* [[ true ]] = base
-- -- -- -- -- -- -- -- -- -- --     FF* (sq false i) = loop i
-- -- -- -- -- -- -- -- -- -- --     FF* (sq true i) = base

-- -- -- -- -- -- -- -- -- -- --     Is1 : Iso (Bool* **) S¹
-- -- -- -- -- -- -- -- -- -- --     Iso.fun Is1 = FF*
-- -- -- -- -- -- -- -- -- -- --     Iso.inv Is1 = FF
-- -- -- -- -- -- -- -- -- -- --     Iso.rightInv Is1 base = refl
-- -- -- -- -- -- -- -- -- -- --     Iso.rightInv Is1 (loop i) j = (cong-∙ FF* (sq true) (sq false) ∙ sym (lUnit _)) j i 
-- -- -- -- -- -- -- -- -- -- --     Iso.leftInv Is1 [[ false ]] = sq true
-- -- -- -- -- -- -- -- -- -- --     Iso.leftInv Is1 [[ true ]] = refl
-- -- -- -- -- -- -- -- -- -- --     Iso.leftInv Is1 (sq false i) j = compPath-filler' (sq true) (sq false) (~ j) i
-- -- -- -- -- -- -- -- -- -- --     Iso.leftInv Is1 (sq true i) j = sq true (j ∧ i)

-- -- -- -- -- -- -- -- -- -- --     A* : (t : (x : _) → Z [[ true ]] x)
-- -- -- -- -- -- -- -- -- -- --        → PathP (λ i → (x : A ((sq true ∙ sq false) i) .fst) → Z ((sq true ∙ sq false) i) x) t t
-- -- -- -- -- -- -- -- -- -- --        → (x : _) (s : _)
-- -- -- -- -- -- -- -- -- -- --        → Z x s 
-- -- -- -- -- -- -- -- -- -- --     A* a b x s = {!!}

-- -- -- -- -- -- -- -- -- -- --     help1 : Iso ((x : _) (y : _) → Z x y)
-- -- -- -- -- -- -- -- -- -- --              (Σ[ a ∈ ((y : _) → Z [[ false ]] y) ]
-- -- -- -- -- -- -- -- -- -- --                Σ[ b ∈ ((y : _) → Z [[ true ]] y) ]
-- -- -- -- -- -- -- -- -- -- --                  PathP (λ i → (x : fst (A (sq false i))) → Z (sq false i) x) a b
-- -- -- -- -- -- -- -- -- -- --                × PathP (λ i → (x : fst (A (sq true i))) → Z (sq true i) x) b a)
-- -- -- -- -- -- -- -- -- -- --     help1 = {!!}
-- -- -- -- -- -- -- -- -- -- --   inda : (Z : (x : _) → (fst (A x)) → Type)
-- -- -- -- -- -- -- -- -- -- --        → ((x : _) → Z [[ false ]] x)
-- -- -- -- -- -- -- -- -- -- --        → (x : _) (y : _) → Z x y
-- -- -- -- -- -- -- -- -- -- --   inda Z a = {!!}

-- -- -- -- -- -- -- -- -- -- --   brs : (x : _) → (fst (A x)) → A [[ false ]] .fst
-- -- -- -- -- -- -- -- -- -- --   brs [[ false ]] p = p
-- -- -- -- -- -- -- -- -- -- --   brs [[ true ]] p = subst (fst ∘ A) (sq true) p
-- -- -- -- -- -- -- -- -- -- --   brs (sq false i) = h i
-- -- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- -- --     h : PathP (λ i → fst (A (sq false i)) → A [[ false ]] .fst) (idfun _) (subst (fst ∘ A) (sq true))
-- -- -- -- -- -- -- -- -- -- --     h = toPathP (funExt λ t → transportRefl _ ∙ {!!})
-- -- -- -- -- -- -- -- -- -- --   brs (sq true i) p = h i p
-- -- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- -- --     h : PathP (λ i → fst (A (sq true i)) → A [[ false ]] .fst) (subst (fst ∘ A) (sq true)) (idfun _)
-- -- -- -- -- -- -- -- -- -- --     h = {!!}

-- -- -- -- -- -- -- -- -- -- --   T : Iso (Σ _ (fst ∘ A)) (A [[ false ]] .fst)
-- -- -- -- -- -- -- -- -- -- --   Iso.fun T (x , p) = brs x p
-- -- -- -- -- -- -- -- -- -- --   Iso.inv T l = [[ false ]] , l
-- -- -- -- -- -- -- -- -- -- --   Iso.rightInv T l = refl
-- -- -- -- -- -- -- -- -- -- --   Iso.leftInv T = uncurry {!A* _ ? ?!}

-- -- -- -- -- -- -- -- -- -- -- -- BoolT : (A B : Type) → Bool → Type
-- -- -- -- -- -- -- -- -- -- -- -- BoolT A B false = A
-- -- -- -- -- -- -- -- -- -- -- -- BoolT A B true = B

-- -- -- -- -- -- -- -- -- -- -- -- data mYT (A : Bool → Pointed₀) (e : (x : _) → A x →∙ A (not x)) : Type where
-- -- -- -- -- -- -- -- -- -- -- --   constr : (x : Bool) → A x .fst → mYT A e
-- -- -- -- -- -- -- -- -- -- -- --   kil : (x : Bool) (r : A x .fst) → constr x r ≡ constr (not x) (e x .fst r)

-- -- -- -- -- -- -- -- -- -- -- -- hr : {!(A : Bool → Pointed₀) (e : (x : _) → A x →∙ A (not x)) → Σ[ x ∈ Bool ] ?!}
-- -- -- -- -- -- -- -- -- -- -- -- hr = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- tte : (A : Bool → Type) → Iso (A false) (Σ[ F ∈ (Σ[ x ∈ Bool ] A x) ]
-- -- -- -- -- -- -- -- -- -- -- --   ((x : Bool) → {!F x ≡ ?!}))
-- -- -- -- -- -- -- -- -- -- -- -- tte = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- my-gen-lem : {X : Type} (B C : Pointed₀) (A : X → Pointed₀) (e : (λ _ → B) ≡ A)
-- -- -- -- -- -- -- -- -- -- -- --   → (t : isEquiv {A = B →∙ C} {B = (x : X) → A x →∙ C}
-- -- -- -- -- -- -- -- -- -- -- --         λ f x → subst (_→∙ C) (funExt⁻ e x) f)

-- -- -- -- -- -- -- -- -- -- -- --   → (F : (x : X) → A x →∙ C)
-- -- -- -- -- -- -- -- -- -- -- --   → (b : fst B) (c : fst C)
-- -- -- -- -- -- -- -- -- -- -- --   → ((x : _) → F x .fst (transport (cong fst (funExt⁻ e x)) b) ≡ c)
-- -- -- -- -- -- -- -- -- -- -- --   → invEq (_ , t) F .fst b ≡ c
-- -- -- -- -- -- -- -- -- -- -- -- my-gen-lem {X = X} B C = J> transport (λ i → (t : isEquiv (λ f x → transportRefl f (~ i)))
-- -- -- -- -- -- -- -- -- -- -- --       (F : (x : X) → B →∙ C) (b : fst B) (c : fst C) →
-- -- -- -- -- -- -- -- -- -- -- --       ((x : X) →
-- -- -- -- -- -- -- -- -- -- -- --        F x .fst (transportRefl b (~ i)) ≡ c) →
-- -- -- -- -- -- -- -- -- -- -- --       invEq ((λ f x → transportRefl f (~ i)) , t) F .fst b ≡ c)
-- -- -- -- -- -- -- -- -- -- -- --         λ t f b → {!λ !}
-- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- --     module _ (t : isEquiv (λ (f : B →∙ C) (x : X) → f)) (F : X → B →∙ C) (b : fst B)
-- -- -- -- -- -- -- -- -- -- -- --       (c : fst C) where
-- -- -- -- -- -- -- -- -- -- -- --       h : isProp X
-- -- -- -- -- -- -- -- -- -- -- --       h x y = {!!}
-- -- -- -- -- -- -- -- -- -- -- --         where
-- -- -- -- -- -- -- -- -- -- -- --         f1 f2 : ((x₁ : X) → Σ (fst B → fst C) (λ f → f (snd B) ≡ snd C)) → B →∙ C
-- -- -- -- -- -- -- -- -- -- -- --         f1 F = F x
-- -- -- -- -- -- -- -- -- -- -- --         f2 F = F y

-- -- -- -- -- -- -- -- -- -- -- --         f1comp : invEq (_ , t) F ≡ F x
-- -- -- -- -- -- -- -- -- -- -- --         f1comp = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- module _ {ℓ ℓ'} (B : Pointed ℓ) (isE : (X : _) (Y : _) (A : fst X → fst Y → Pointed ℓ') → isEquiv (theF-real B X Y A)) where
-- -- -- -- -- -- -- -- -- -- -- --   isEq* : (X : RP∞) (Y : RP∞) (A : fst X → fst Y → Pointed ℓ')
-- -- -- -- -- -- -- -- -- -- -- --     → (F : ((x : fst X) (y : fst Y) → BIG X Y A x y →∙ B))
-- -- -- -- -- -- -- -- -- -- -- --     → (f : (x : fst X) (y : fst Y) → A x y .fst)
-- -- -- -- -- -- -- -- -- -- -- --     → (b : fst B)
-- -- -- -- -- -- -- -- -- -- -- --     → Path (fst X → fst Y → _)
-- -- -- -- -- -- -- -- -- -- -- --          (λ x y → F x y .fst (((proj (proj (f _ _) (f _ _)) (proj (f _ _) (f _ _))))))
-- -- -- -- -- -- -- -- -- -- -- --          (λ _ _ → pt B)
-- -- -- -- -- -- -- -- -- -- -- --     → invEq (_ , isE X Y A) F .fst ((inr (λ x → inr λ y → f x y))) ≡ b
-- -- -- -- -- -- -- -- -- -- -- --   isEq* X Y A F f b p = {!p!} ∙ {!!}
-- -- -- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- -- -- --     G = invEq (_ , isE X Y A) F

-- -- -- -- -- -- -- -- -- -- -- --     h : F ≡ theF-real B X Y A G
-- -- -- -- -- -- -- -- -- -- -- --     h = sym (secEq (_ , isE X Y A) F)


-- -- -- -- -- -- -- -- -- -- -- -- module _ (X Y : RP∞) (A : fst X → fst Y → Pointed₀) where
-- -- -- -- -- -- -- -- -- -- -- --   -- →∙not² : (x : fst X) → A x →∙ A (not* X (not* X x))
-- -- -- -- -- -- -- -- -- -- -- --   -- fst (→∙not² x) = subst (fst ∘ A) (sym (not*not* X x))
-- -- -- -- -- -- -- -- -- -- -- --   -- snd (→∙not² x) = ?

-- -- -- -- -- -- -- -- -- -- -- --   Big : (x : fst X) (y : fst Y) → Pointed₀
-- -- -- -- -- -- -- -- -- -- -- --   Big x y = Smash∙ (Smash∙ (A x y) (A (not* X x) y))
-- -- -- -- -- -- -- -- -- -- -- --                    (Smash∙ (A x (not* Y y)) (A (not* X x) (not* Y y)))

-- -- -- -- -- -- -- -- -- -- -- --   SMFD : (B : Pointed₀) → Type
-- -- -- -- -- -- -- -- -- -- -- --   SMFD B = Σ[ f ∈ ((x : fst X) (y : fst Y)
-- -- -- -- -- -- -- -- -- -- -- --          → Big x y
-- -- -- -- -- -- -- -- -- -- -- --          →∙ B) ]
-- -- -- -- -- -- -- -- -- -- -- --     ∥ ((x : fst X) (y : fst Y) → ¬ f x y ≡ const∙ _ _) ∥₁

-- -- -- -- -- -- -- -- -- -- -- --   SM-non-const' : (B : Pointed₀) → Type
-- -- -- -- -- -- -- -- -- -- -- --   SM-non-const' B = Σ[ f ∈ SM∙ X (λ x → SM∙ Y (A x)) →∙ B ] ¬ f ≡ const∙ _ _

-- -- -- -- -- -- -- -- -- -- -- --   module _ (B : Pointed₀) (st : (x : fst X) (y : fst Y) → isSet (Big x y →∙ B))
-- -- -- -- -- -- -- -- -- -- -- --            (ispr : (x : fst X) (y : fst Y)
-- -- -- -- -- -- -- -- -- -- -- --            → isProp (Σ[ f ∈ (Big x y →∙ B) ] ¬ f ≡ const∙ _ B))
-- -- -- -- -- -- -- -- -- -- -- --            (hom : isHomogeneous B)
-- -- -- -- -- -- -- -- -- -- -- --            where

-- -- -- -- -- -- -- -- -- -- -- --     isPropSMFD : isProp (SMFD B)
-- -- -- -- -- -- -- -- -- -- -- --     isPropSMFD (f , p) (g , q) = Σ≡Prop (λ _ → squash₁)
-- -- -- -- -- -- -- -- -- -- -- --       (funExt λ x → funExt λ y → cong fst (ispr x y (f' x y) (g' x y)))
-- -- -- -- -- -- -- -- -- -- -- --       where
-- -- -- -- -- -- -- -- -- -- -- --       f' g' : (x : fst X) (y : fst Y) → Σ[ f ∈ (Big x y →∙ B) ] ¬ f ≡ const∙ _ B
-- -- -- -- -- -- -- -- -- -- -- --       f' x y = (f x y) , (λ t → PT.rec (λ {()}) (λ r → r x y t) p)
-- -- -- -- -- -- -- -- -- -- -- --       g' x y = g x y , λ t → PT.rec (λ {()}) (λ r → r x y t) q

-- -- -- -- -- -- -- -- -- -- -- --     G : (f : SM∙ X (λ x₁ → SM∙ Y (A x₁)) →∙ B)
-- -- -- -- -- -- -- -- -- -- -- --       → {!isHomogeneous→∙!}
-- -- -- -- -- -- -- -- -- -- -- --       → {!!}
-- -- -- -- -- -- -- -- -- -- -- --     G = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- module _ (X : RP∞) (A : fst X → Pointed₀) where
-- -- -- -- -- -- -- -- -- -- -- --   →∙not² : (x : fst X) → A x →∙ A (not* X (not* X x))
-- -- -- -- -- -- -- -- -- -- -- --   fst (→∙not² x) = subst (fst ∘ A) (sym (not*not* X x))
-- -- -- -- -- -- -- -- -- -- -- --   snd (→∙not² x) j =
-- -- -- -- -- -- -- -- -- -- -- --     transp (λ i → fst (A (not*not* X x (~ i ∧ ~ j)))) j (snd (A (not*not* X x (~ j))))

-- -- -- -- -- -- -- -- -- -- -- --   SMF : (B : Pointed₀) → Type
-- -- -- -- -- -- -- -- -- -- -- --   SMF B = Σ[ f ∈ ((x : fst X) → Smash∙ (A x) (A (not* X x)) →∙ B) ]
-- -- -- -- -- -- -- -- -- -- -- --     ∥ ((x : fst X) → ¬ f x ≡ const∙ _ _) ∥₁

-- -- -- -- -- -- -- -- -- -- -- --   SM-non-const : (B : Pointed₀) → Type
-- -- -- -- -- -- -- -- -- -- -- --   SM-non-const B = Σ[ f ∈ (SM X A , inr λ x → A x .snd) →∙ B ] ¬ f ≡ const∙ _ _

-- -- -- -- -- -- -- -- -- -- -- --   module _ (B : Pointed₀) (st : (x : fst X) → isSet (Smash∙ (A x) (A (not* X x)) →∙ B))
-- -- -- -- -- -- -- -- -- -- -- --            (homl : (A B C : Pointed₀)
-- -- -- -- -- -- -- -- -- -- -- --           (f g : Smash∙ A B →∙ C)
-- -- -- -- -- -- -- -- -- -- -- --        → isHomogeneous C
-- -- -- -- -- -- -- -- -- -- -- --        → (((x : fst A) (y : fst B) → fst f (proj x y) ≡ fst g (proj x y)))
-- -- -- -- -- -- -- -- -- -- -- --        → f ≡ g)
-- -- -- -- -- -- -- -- -- -- -- --            (ispr : (x : fst X)
-- -- -- -- -- -- -- -- -- -- -- --            → isProp (Σ[ f ∈ (Smash∙ (A x) (A (not* X x)) →∙ B) ] ¬ f ≡ const∙ _ B))
-- -- -- -- -- -- -- -- -- -- -- --            (hom : isHomogeneous B)
-- -- -- -- -- -- -- -- -- -- -- --            where
-- -- -- -- -- -- -- -- -- -- -- --     isPropSMF : isProp (SMF B)
-- -- -- -- -- -- -- -- -- -- -- --     isPropSMF (f , p) (g , q) = Σ≡Prop (λ _ → squash₁) (funExt λ x → cong fst (ispr x (f' x) (g' x)))
-- -- -- -- -- -- -- -- -- -- -- --       where
-- -- -- -- -- -- -- -- -- -- -- --       f' g' : (x : fst X) → Σ[ f ∈ (Smash∙ (A x) (A (not* X x)) →∙ B) ] ¬ f ≡ const∙ _ B
-- -- -- -- -- -- -- -- -- -- -- --       f' x = (f x) , (PT.rec (isProp¬ _) (λ a → a x) p)
-- -- -- -- -- -- -- -- -- -- -- --       g' x = (g x) , (PT.rec (isProp¬ _) (λ a → a x) q)

-- -- -- -- -- -- -- -- -- -- -- --     St : SM-non-const B → SMF B
-- -- -- -- -- -- -- -- -- -- -- --     St (f , q) = (λ x → (λ { basel → pt B ; baser → pt B
-- -- -- -- -- -- -- -- -- -- -- --                            ; (proj a b) → fst f (inr (CasesRP X x a b))
-- -- -- -- -- -- -- -- -- -- -- --                            ; (gluel a i) → (cong (fst f) (sym (push (x , a)) ∙ push (x , pt (A x)))
-- -- -- -- -- -- -- -- -- -- -- --                                           ∙ {!snd f!}) i
-- -- -- -- -- -- -- -- -- -- -- --                            ; (gluer b i) → {!!}}) , refl)
-- -- -- -- -- -- -- -- -- -- -- --                 , {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- RPpt→BoolEquiv : {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- RPpt→BoolEquiv = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- pss : (X : RP∞) (x : fst X) (Y : RP∞) (A : fst X → fst Y → Pointed₀)
-- -- -- -- -- -- -- -- -- -- -- -- --   → (Smash∙ (SM∙ Y (A x)) (SM∙ Y (A (not* X x))) →∙ SM∙ Y λ y → SM∙ X λ x → A x y)
-- -- -- -- -- -- -- -- -- -- -- -- -- pss = J2-elem _ .fst λ Y A
-- -- -- -- -- -- -- -- -- -- -- -- --   → (λ { basel → inr λ y → inl true
-- -- -- -- -- -- -- -- -- -- -- -- --         ; baser → inr λ y → inl false
-- -- -- -- -- -- -- -- -- -- -- -- --         ; (proj x y) → h Y A x y
-- -- -- -- -- -- -- -- -- -- -- -- --         ; (gluel (inl x) i) → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --         ; (gluel (inr x) i) → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --         ; (gluel (push a i₁) i) → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --         ; (gluer b i) → {!!}}) , {!refl!}
-- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- --   module _ (Y : RP∞) (A : fst Bool* → fst Y → Pointed₀) where
-- -- -- -- -- -- -- -- -- -- -- -- --     g-mid : (f : (x : fst Y) → A true x .fst)
-- -- -- -- -- -- -- -- -- -- -- -- --             (g : (x : fst Y) → A false x .fst)
-- -- -- -- -- -- -- -- -- -- -- -- --             (y : fst Y) (x : Bool) → A x y .fst
-- -- -- -- -- -- -- -- -- -- -- -- --     g-mid f g y false = g y
-- -- -- -- -- -- -- -- -- -- -- -- --     g-mid f g y true = f y

-- -- -- -- -- -- -- -- -- -- -- -- --     g : (f : (x : fst Y) → A true x .fst)
-- -- -- -- -- -- -- -- -- -- -- -- --       → SM Y (A false) → SM Y (λ y₁ → SM∙ Bool* (λ x₁ → A x₁ y₁))
-- -- -- -- -- -- -- -- -- -- -- -- --     g f (inl x) = inl x
-- -- -- -- -- -- -- -- -- -- -- -- --     g f (inr g) = inr (λ y → inr (g-mid f g y))
-- -- -- -- -- -- -- -- -- -- -- -- --     g f (push (y , g) i) =
-- -- -- -- -- -- -- -- -- -- -- -- --         (push (y , (inr (CasesRP Bool* true (f y) g)))
-- -- -- -- -- -- -- -- -- -- -- -- --       ∙ λ i → inr ((h ∙ F≡) (~ i))) i
-- -- -- -- -- -- -- -- -- -- -- -- --       where
-- -- -- -- -- -- -- -- -- -- -- -- --       inr* : (y₁ : fst Y) →  _ → SM Bool* (λ x₁ → A x₁ y₁)
-- -- -- -- -- -- -- -- -- -- -- -- --       inr* y₁ = inr

-- -- -- -- -- -- -- -- -- -- -- -- --       F : ((y₁ : fst Y) → SM Bool* (λ x₁ → A x₁ y₁))
-- -- -- -- -- -- -- -- -- -- -- -- --       F = (CasesRP Y {A = λ y₁ → SM Bool* (λ x₁ → A x₁ y₁)} y
-- -- -- -- -- -- -- -- -- -- -- -- --                      (inr (CasesRP Bool* true (f y) g))
-- -- -- -- -- -- -- -- -- -- -- -- --                      (inr (CasesRP Bool* true (f (not* Y y)) (A _ _ .snd))))

-- -- -- -- -- -- -- -- -- -- -- -- --       F≡ : F ≡ CasesRP Y {A = λ y₁ → SM Bool* (λ x₁ → A x₁ y₁)} y
-- -- -- -- -- -- -- -- -- -- -- -- --                      (inr (CasesRP Bool* true (f y) g))
-- -- -- -- -- -- -- -- -- -- -- -- --                      (inr (λ x → A x (not* Y y) .snd))
-- -- -- -- -- -- -- -- -- -- -- -- --       F≡ = funExt (λ z → CasesRP≡ Y y z refl (sym (push (true , (f (not* Y y))))
-- -- -- -- -- -- -- -- -- -- -- -- --                   ∙ push (true , A true (not* Y y) .snd)
-- -- -- -- -- -- -- -- -- -- -- -- --                   ∙ cong (inr* (not* Y y))
-- -- -- -- -- -- -- -- -- -- -- -- --                   (funExt λ { false → transportRefl (A false _ .snd)
-- -- -- -- -- -- -- -- -- -- -- -- --                             ; true → transportRefl (A true _ .snd)})))


-- -- -- -- -- -- -- -- -- -- -- -- --       h : Path ((y₁ : fst Y)
-- -- -- -- -- -- -- -- -- -- -- -- --         → SM Bool* (λ x₁ → A x₁ y₁))
-- -- -- -- -- -- -- -- -- -- -- -- --             (λ y₁ → inr (g-mid f
-- -- -- -- -- -- -- -- -- -- -- -- --                       (CasesRP Y y g (snd (A false (not* Y y)))) y₁))
-- -- -- -- -- -- -- -- -- -- -- -- --                F
-- -- -- -- -- -- -- -- -- -- -- -- --       h = funExt (CasesRP Y y (cong (inr* y)
-- -- -- -- -- -- -- -- -- -- -- -- --             (funExt (λ { false → CasesRPβ Y {A = λ y → fst (A false y)}
-- -- -- -- -- -- -- -- -- -- -- -- --                                    y g (snd (A false (not* Y y))) .fst
-- -- -- -- -- -- -- -- -- -- -- -- --                        ; true → refl}))
-- -- -- -- -- -- -- -- -- -- -- -- --             ∙ sym ((CasesRPβ Y {A = λ y₁ → SM Bool* (λ x₁ → A x₁ y₁)} y
-- -- -- -- -- -- -- -- -- -- -- -- --                  (inr λ { false → g ; true → f y})
-- -- -- -- -- -- -- -- -- -- -- -- --                  (inr (λ { false → A false _ .snd ; true → f (not* Y y)}))) .fst)
-- -- -- -- -- -- -- -- -- -- -- -- --             ∙ CasesRP≡ Y y _ (cong (inr* y)
-- -- -- -- -- -- -- -- -- -- -- -- --                                (funExt (λ { false → sym (transportRefl g)
-- -- -- -- -- -- -- -- -- -- -- -- --                                           ; true → sym (transportRefl (f y))})))
-- -- -- -- -- -- -- -- -- -- -- -- --                              (cong (inr* (not* Y y))
-- -- -- -- -- -- -- -- -- -- -- -- --                                (funExt (λ { false → sym (transportRefl (A false _ .snd))
-- -- -- -- -- -- -- -- -- -- -- -- --                                           ; true → sym (transportRefl (f (not* Y y)))}))))
-- -- -- -- -- -- -- -- -- -- -- -- --                  (cong (inr* (not* Y y)) (funExt (λ { false → CasesRPβ Y {A = λ y → A false y .fst} y g (snd (A false (not* Y y))) .snd
-- -- -- -- -- -- -- -- -- -- -- -- --                                                     ; true → refl}))
-- -- -- -- -- -- -- -- -- -- -- -- --                ∙∙ sym ((CasesRPβ Y {A = λ y₁ → SM Bool* (λ x₁ → A x₁ y₁)} y
-- -- -- -- -- -- -- -- -- -- -- -- --                  (inr λ { false → g ; true → f y})
-- -- -- -- -- -- -- -- -- -- -- -- --                  (inr (λ { false → A false _ .snd ; true → f (not* Y y)}))) .snd)
-- -- -- -- -- -- -- -- -- -- -- -- --                ∙∙ CasesRP≡ Y y _ (cong (inr* y) (funExt (λ { false → sym (transportRefl g)
-- -- -- -- -- -- -- -- -- -- -- -- --                                                            ; true → sym (transportRefl (f y))})))
-- -- -- -- -- -- -- -- -- -- -- -- --                                  (cong (inr* (not* Y y))
-- -- -- -- -- -- -- -- -- -- -- -- --                                    (funExt (λ { false → sym (transportRefl (A _ _ .snd))
-- -- -- -- -- -- -- -- -- -- -- -- --                                               ; true → sym (transportRefl (f (not* Y y)))})))))

-- -- -- -- -- -- -- -- -- -- -- -- --     F* G* : (y' : fst Y) (f : fst (A true y')) → (x : typ (SM∙ Y (A true))) → SM∙ Y (A false) →∙ (SM∙ Y (λ y₁ → SM∙ Bool* (λ x₁ → A x₁ y₁)))
-- -- -- -- -- -- -- -- -- -- -- -- --     F* y' f x = (λ _ → inl y') , (push (y' , (inr (λ x → A x y' .snd)))
-- -- -- -- -- -- -- -- -- -- -- -- --                                 ∙ {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --                                 ∙ {!!})
-- -- -- -- -- -- -- -- -- -- -- -- --       where
-- -- -- -- -- -- -- -- -- -- -- -- --       f* : {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --       f* = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --     G* y' f x = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- --     h : typ (SM∙ Y (A true)) → typ (SM∙ Y (A false)) → SM Y (λ y₁ → SM∙ Bool* (λ x₁ → A x₁ y₁))
-- -- -- -- -- -- -- -- -- -- -- -- --     h (inl x) y = inl x
-- -- -- -- -- -- -- -- -- -- -- -- --     h (inr f) y = g f y
-- -- -- -- -- -- -- -- -- -- -- -- --     h (push (y' , f) i) (inl x) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --     h (push (y' , f) i) (inr x) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --     h (push (y' , f) i) (push a i₁) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- --   → (λ { basel → inr λ y → inl true ; baser → inr λ y → inl false
-- -- -- -- -- -- -- -- -- -- -- -- --        ; (proj (inl x) g) → inl x
-- -- -- -- -- -- -- -- -- -- -- -- --        ; (proj (inr f) (inl x)) → inl x
-- -- -- -- -- -- -- -- -- -- -- -- --        ; (proj (inr f) (inr g)) → inr λ y → inr λ { false → g y ; true → f y}
-- -- -- -- -- -- -- -- -- -- -- -- --        ; (proj (inr f) (push a i)) → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --        ; (proj (push a i) g) → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --        ; (gluel a i) → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- --        ; (gluer b i) → {!!}}) , {!!} -}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- ∑∑RP : (X Y : RP∞) (n : fst X → fst Y → ℕ) → ℕ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- ∑∑RP = uncurry λ X
-- -- -- -- -- -- -- -- -- -- -- -- -- --   → rec→Set
-- -- -- -- -- -- -- -- -- -- -- -- -- --        (isSetΠ2 (λ _ _ → isSetℕ))
-- -- -- -- -- -- -- -- -- -- -- -- -- --        (λ e → λ Y n → ∑RP Y (n (invEq e false)) + ∑RP Y (n (invEq e true)))
-- -- -- -- -- -- -- -- -- -- -- -- -- --        (EquivJ (λ X e → (y : X ≃ Bool) →
-- -- -- -- -- -- -- -- -- -- -- -- -- --       (λ (Y : RP∞) (n : X → fst Y → ℕ)
-- -- -- -- -- -- -- -- -- -- -- -- -- --         → ∑RP Y (n (invEq e false)) + ∑RP Y (n (invEq e true))) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- --       (λ Y n → ∑RP Y (n (invEq y false)) + ∑RP Y (n (invEq y true))))
-- -- -- -- -- -- -- -- -- -- -- -- -- --       (BoolAutoElim refl
-- -- -- -- -- -- -- -- -- -- -- -- -- --         (funExt λ Y → funExt λ n
-- -- -- -- -- -- -- -- -- -- -- -- -- --           → +-comm _ _)))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- gen⋁ : {ℓ : Level} (X : RP∞) (A : fst X → Pointed ℓ)
-- -- -- -- -- -- -- -- -- -- -- -- -- --   → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- gen⋁ X A = cofib {B = Σ (fst X) (fst ∘ A)} λ x → x , pt (A x)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- gen⋁-comm : {ℓ : Level} (X Y : RP∞) (A : fst X → fst Y → Pointed ℓ)
-- -- -- -- -- -- -- -- -- -- -- -- -- --   → gen⋁ X (λ x → gen⋁ Y (A x) , inl tt) → gen⋁ Y (λ y → gen⋁ X (λ x → A x y) , inl tt)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- gen⋁-comm X Y A (inl x) = inl tt
-- -- -- -- -- -- -- -- -- -- -- -- -- -- gen⋁-comm X Y A (inr (x , inl y)) = inl tt
-- -- -- -- -- -- -- -- -- -- -- -- -- -- gen⋁-comm X Y A (inr (x , inr (y , z))) = inr (y , inr (x , z))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- gen⋁-comm X Y A (inr (x , push a i)) = (push a ∙ λ i → inr (a , push x i)) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- gen⋁-comm X Y A (push a i) = inl tt

-- -- -- -- -- -- -- -- -- -- -- -- -- -- gen⋁-comm* : {ℓ : Level} (X Y : RP∞) (A : fst X → fst Y → Pointed ℓ)
-- -- -- -- -- -- -- -- -- -- -- -- -- --   → Iso (gen⋁ X (λ x → gen⋁ Y (A x) , inl tt)) (gen⋁ Y (λ y → gen⋁ X (λ x → A x y) , inl tt))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.fun (gen⋁-comm* X Y A) = gen⋁-comm X Y A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.inv (gen⋁-comm* X Y A) = gen⋁-comm Y X λ y x → A x y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (gen⋁-comm* X Y A) (inl x) = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (gen⋁-comm* X Y A) (inr (x , inl x₁)) = push x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (gen⋁-comm* X Y A) (inr (x , inr x₁)) = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (gen⋁-comm* {ℓ} X Y A) (inr (x , push a i)) j = help j i
-- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- --   help : PathP (λ i → Path (gen⋁ Y (λ y → gen⋁ X (λ x → A x y) , inl tt)) (push x i) (inr (x , inr (a , pt (A a x)))))
-- -- -- -- -- -- -- -- -- -- -- -- -- --                (cong (gen⋁-comm X Y A) (push a ∙ λ i → inr (a , push x i)))
-- -- -- -- -- -- -- -- -- -- -- -- -- --                (λ i → inr (x , push a i))
-- -- -- -- -- -- -- -- -- -- -- -- -- --   help = (cong-∙ (gen⋁-comm X Y A) (push a) (λ i₁ → inr (a , push x i₁))
-- -- -- -- -- -- -- -- -- -- -- -- -- --        ∙ sym (lUnit _)
-- -- -- -- -- -- -- -- -- -- -- -- -- --        ∙ refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- --        ◁ (λ i j → compPath-filler' {ℓ} {gen⋁ Y (λ y → gen⋁ X (λ x → A x y) , inl tt)}
-- -- -- -- -- -- -- -- -- -- -- -- -- --            (push x) (λ i₁ → inr (x , push a i₁)) (~ i) j)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (gen⋁-comm* X Y A) (push a i) = λ j → push a (i ∧ j)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.leftInv (gen⋁-comm* X Y A) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- module _ {X : Type} {A : X → X → Pointed₀} (B : (x y : X) → A x y →∙ A y x)
-- -- -- -- -- -- -- -- -- -- -- -- -- --   (hom : (x y : X) → isHomogeneous (A x y))
-- -- -- -- -- -- -- -- -- -- -- -- -- --   (Bid : (x y : X) → (B y x ∘∙ B x y) ≡ id∙ _) where
-- -- -- -- -- -- -- -- -- -- -- -- -- --   TT : {!isProp ?!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --   TT = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- test2 : (X : RP∞) → (fst X × ℕ) → (fst X → ℕ)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- test2 = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- module _  {A : Type} (_+A_ : A → A → A)
-- -- -- -- -- -- -- -- -- -- -- -- -- --   (isEq+ : (x : A) → isEquiv (x +A_))
-- -- -- -- -- -- -- -- -- -- -- -- -- --   (is-comm : (x y : A) → x +A y ≡ y +A x)
-- -- -- -- -- -- -- -- -- -- -- -- -- --   (⋆ : A)
-- -- -- -- -- -- -- -- -- -- -- -- -- --   (rid : (x : A) → x +A ⋆ ≡ x)
-- -- -- -- -- -- -- -- -- -- -- -- -- --   (lid : (x : A) → ⋆ +A x ≡ x)
-- -- -- -- -- -- -- -- -- -- -- -- -- --   (rlid : lid ⋆ ≡ rid ⋆) where

-- -- -- -- -- -- -- -- -- -- -- -- -- --   +Eq : A → A ≃ A
-- -- -- -- -- -- -- -- -- -- -- -- -- --   +Eq x = (x +A_) , (isEq+ x)

-- -- -- -- -- -- -- -- -- -- -- -- -- --   B-gen : {!(x : A) → !}
-- -- -- -- -- -- -- -- -- -- -- -- -- --   B-gen = {!δ Δ ∇ !}
  
-- -- -- -- -- -- -- -- -- -- -- -- -- --   sf : (B : A → Type) (x : A) → PathP (λ i → ua (+Eq x) (~ i) → Type)
-- -- -- -- -- -- -- -- -- -- -- -- -- --                                        B
-- -- -- -- -- -- -- -- -- -- -- -- -- --                                        λ a → B (x +A a)
-- -- -- -- -- -- -- -- -- -- -- -- -- --   sf B x = toPathP (funExt λ a → cong B (transportRefl _))

-- -- -- -- -- -- -- -- -- -- -- -- -- --   thm : (B : A → Type) (x a : A) → B a → B (x +A a) 
-- -- -- -- -- -- -- -- -- -- -- -- -- --   thm B x a z = {!sf B x!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- module genSmash {ℓ : Level} (X : RP∞) (A : fst X → Pointed ℓ)
-- -- -- -- -- -- -- -- -- -- -- -- -- --                 (f : (x : fst X) (a : fst (A x)) → (x : fst X) → A x .fst ) where
-- -- -- -- -- -- -- -- -- -- -- -- -- --   data ⋀∞gen  : Type ℓ where
-- -- -- -- -- -- -- -- -- -- -- -- -- --     proj : ((x : fst X) → A x .fst) → ⋀∞gen
-- -- -- -- -- -- -- -- -- -- -- -- -- --     base : fst X → ⋀∞gen
-- -- -- -- -- -- -- -- -- -- -- -- -- --     gl : (x : fst X) (a : fst (A x)) → proj (f x a) ≡ base x

-- -- -- -- -- -- -- -- -- -- -- -- -- --   proj* : ((x : fst X) → A x .fst) → ⋀∞gen
-- -- -- -- -- -- -- -- -- -- -- -- -- --   proj* = proj

-- -- -- -- -- -- -- -- -- -- -- -- -- -- module _ {ℓ : Level} (X : RP∞) (A : fst X → Pointed ℓ) where
-- -- -- -- -- -- -- -- -- -- -- -- -- --   module M = genSmash X A (λ x a → CasesRP X {fst ∘ A} x a ((snd ∘ A) (not* X x)))
-- -- -- -- -- -- -- -- -- -- -- -- -- --   open M public renaming (⋀∞gen to ⋀∞)

-- -- -- -- -- -- -- -- -- -- -- -- -- --   ⋀∞∙ : Pointed _
-- -- -- -- -- -- -- -- -- -- -- -- -- --   fst ⋀∞∙ = ⋀∞
-- -- -- -- -- -- -- -- -- -- -- -- -- --   snd ⋀∞∙ = proj λ x → A x .snd


-- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- -- -- -- -- -- -- -- -- -- -- -- -- -- module _ {ℓ : Level} {A B C D : Pointed ℓ} where
-- -- -- -- -- -- -- -- -- -- -- -- -- --   data ×Smash : Type ℓ where
-- -- -- -- -- -- -- -- -- -- -- -- -- --     cent : ×Smash

-- -- -- -- -- -- -- -- -- -- -- -- -- --     ptsr : fst A → fst B → ×Smash
-- -- -- -- -- -- -- -- -- -- -- -- -- --     ptsl : fst C → fst D → ×Smash

-- -- -- -- -- -- -- -- -- -- -- -- -- --     centrl : (a : fst A) → ptsr a (pt B) ≡ cent
-- -- -- -- -- -- -- -- -- -- -- -- -- --     centrr : (b : fst B) → ptsr (pt A) b ≡ cent
-- -- -- -- -- -- -- -- -- -- -- -- -- --     centll : (c : fst C) → ptsl c (pt D) ≡ cent
-- -- -- -- -- -- -- -- -- -- -- -- -- --     centlr : (d : fst D) → ptsl (pt C) d ≡ cent

-- -- -- -- -- -- -- -- -- -- -- -- -- --     pts : fst A → fst B → fst C → fst D → ×Smash

-- -- -- -- -- -- -- -- -- -- -- -- -- --     gluell : (b : fst B) (c : fst C) (d : fst D) → pts (pt A) b c d ≡ ptsl c d
-- -- -- -- -- -- -- -- -- -- -- -- -- --     gluelr : (a : fst A) (c : fst C) (d : fst D) → pts a (pt B) c d ≡ ptsl c d

-- -- -- -- -- -- -- -- -- -- -- -- -- --     gluerl : (a : fst A) (b : fst B) (d : fst D) → pts a b (pt C) d ≡ ptsr a b
-- -- -- -- -- -- -- -- -- -- -- -- -- --     gluerr : (a : fst A) (b : fst B) (c : fst C) → pts a b c (pt D) ≡ ptsr a b

-- -- -- -- -- -- -- -- -- -- -- -- -- --     hgluell : (a : fst A) (c : fst C) → PathP (λ i → gluerr a (pt B) c i ≡ centll c i) (gluelr a c (pt D)) (centrl a)
-- -- -- -- -- -- -- -- -- -- -- -- -- --     hgluelr : (a : fst A) (d : fst D) → PathP (λ i → gluelr a (pt C) d i ≡ centrl a i) (gluerl a (pt B) d) (centlr d)
-- -- -- -- -- -- -- -- -- -- -- -- -- --     hgluerl : (b : fst B) (c : fst C) → PathP (λ i → gluell b c (pt D) i ≡ centrr b i) (gluerr (pt A) b c) (centll c)
-- -- -- -- -- -- -- -- -- -- -- -- -- --     hgluerr : (b : fst B) (d : fst D) → PathP (λ i → gluell b (pt C) d i ≡ centrr b i) (gluerl (pt A) b d) (centlr d)
    

-- -- -- -- -- -- -- -- -- -- -- -- -- -- tq : {!(!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- tq = {!!}
    
    

-- -- -- -- -- -- -- -- -- -- -- -- -- -- module _ {ℓ : Level} (X Y : RP∞) (A : fst X → fst Y → Pointed ℓ) where
-- -- -- -- -- -- -- -- -- -- -- -- -- --   tr : {!{A : fst X → Type ℓ} ((x : fst X) → A x) → ?!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --   tr = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- --   TTT = ((x : fst X) → ⋀∞ Y (A x))
-- -- -- -- -- -- -- -- -- -- -- -- -- --   data ΠgenSmash* : Type ℓ where
-- -- -- -- -- -- -- -- -- -- -- -- -- --     [_]* : ((x : fst X) (y : fst Y) → A x y .fst) → ΠgenSmash* -- pts
-- -- -- -- -- -- -- -- -- -- -- -- -- --     cent : fst X → fst Y → ΠgenSmash*
-- -- -- -- -- -- -- -- -- -- -- -- -- --     bases : (x : fst X) → ((y : fst Y) → A x y .fst) → ΠgenSmash*
-- -- -- -- -- -- -- -- -- -- -- -- -- --     cenrs : (x : fst X) (y : fst Y) (a : A x y .fst) → bases x (CasesRP Y y a (A x (not* Y y) .snd)) ≡ cent x y
-- -- -- -- -- -- -- -- -- -- -- -- -- --     gluez : (x : fst X) (y : fst Y) (y' : fst Y) (aₗ : A x y .fst) (ar : A x (not* Y y) .fst) (a' : A (not* X x) y .fst) --  (f : (y : _) → A x y .fst) (a' : A (not* X x) y .fst)
-- -- -- -- -- -- -- -- -- -- -- -- -- --       → [ CasesRP X x (CasesRP Y y aₗ ar) (CasesRP Y y a' (A (not* X x) (not* Y y) .snd))  ]* ≡ bases x (CasesRP Y y aₗ ar)
-- -- -- -- -- -- -- -- -- -- -- -- -- --     gluez-coh : (x : fst X) (y : fst Y) (a : A x y .fst) (f : {!Σ[ y ∈ Y ] !} → {!!}) -- (b : A (not* X x) y .fst) (b : A (not* X x) (not* Y y) .fst)
-- -- -- -- -- -- -- -- -- -- -- -- -- --       → {!!} -- (gluez x y (CasesRP Y y a (A x (not* Y y) .snd)) a') {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --     gluez-coh' : (x : fst X) (y : fst Y) (a : A x y .fst) (b : A (not* X x) (not* Y y) .fst)
-- -- -- -- -- -- -- -- -- -- -- -- -- --       → {!!} -- PathP (λ i → {!!} ≡ {!!}) (gluez x y {!!} {!!}) {!!} 

-- -- -- -- -- -- -- -- -- -- -- -- -- --       {-
-- -- -- -- -- -- -- -- -- -- -- -- -- --       a₀ 
-- -- -- -- -- -- -- -- -- -- -- -- -- --       -}
    

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data unord {ℓ : Level} (X : RP∞) (A : fst X → Type ℓ) (B : Type ℓ) : Type ℓ where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   killa : ((x : fst X) → A x → B) → unord X A B
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   bz : (B × B → B) → unord X A B


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- unordEq : {ℓ : Level} (X : RP∞) (A : fst X → Type ℓ) (a : (x : fst X) → A x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → (a : (x : fst X) → A x) → Type
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- unordEq X A a a' = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- gen* : (X : RP∞) (A : fst X → Type) (B : Type)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → (f : ((x : fst X) → A x) → B)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → Σ[ f ∈ ((x : fst X) → A x → A (not* X x) → B) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ((x : fst X) (a : A x) (a' : A (not* X x)) → Σ[ b ∈ B ] {!!}) -- → Σ[ g ∈ {!f x a a'!} ] {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- gen* = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- 2CaseBool : {ℓ : Level} (A : Bool → Pointed ℓ)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → (x : Bool) → fst (A x) → (x₁ : Bool) → A x₁ .fst
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- 2CaseBool A false p false = p
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- 2CaseBool A false p true = A true .snd
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- 2CaseBool A true p false = A false .snd
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- 2CaseBool A true p true = p

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data coeq {ℓ ℓ' : Level} (A : Type ℓ) (R : A → A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   [_]' : A → coeq A R
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   eq/ : (a a' : A) → R a a' → [ a ]' ≡ [ a' ]'

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- open import Cubical.Data.Empty
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- push-rel : {A B C : Type} (f : A → B) (g : A → C) → B ⊎ C → B ⊎ C → Type
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- push-rel {C = C} f g (inl x) (inl x₁) = ⊥
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- push-rel {A = A} f g (inl b) (inr c) = Σ[ x ∈ A ] (f x ≡ b) × (g x ≡ c)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- push-rel {C = C} f g (inr x) (inl x₁) = ⊥
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- push-rel {C = C} f g (inr x) (inr x₁) = ⊥

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _ {A B C : Type} {f : A → B} {g : A → C} where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   private
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     t : Pushout f g → coeq (B ⊎ C) (push-rel f g)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     t (inl x) = [ inl x ]'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     t (inr x) = [ inr x ]'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     t (push a i) = eq/ (inl (f a)) (inr (g a)) (a , (refl , refl)) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     s : coeq (B ⊎ C) (push-rel f g) → Pushout f g
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     s [ inl x ]' = inl x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     s [ inr x ]' = inr x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     s (eq/ (inl x₁) (inr x₂) x i) = (sym (cong inl (snd x .fst)) ∙∙ push (fst x) ∙∙ cong inr (snd x .snd)) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     s (eq/ (inr x₁) (inl x₂) () i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     s (eq/ (inr x₁) (inr x₂) () i)

  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Pushout≃Coeq : Iso (Pushout f g) (coeq (B ⊎ C) (push-rel f g))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Iso.fun Pushout≃Coeq = t
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Iso.inv Pushout≃Coeq = s
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Iso.rightInv Pushout≃Coeq [ inl x ]' = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Iso.rightInv Pushout≃Coeq [ inr x ]' = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Iso.rightInv Pushout≃Coeq (eq/ (inl x₁) (inr x₂) x i) = flipSquare (help x) i 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       help : (x : _) → cong t (sym (cong inl (snd x .fst)) ∙∙ push (fst x) ∙∙ cong inr (snd x .snd)) ≡ eq/ (inl x₁) (inr x₂) x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       help x = cong-∙∙ t (sym (cong inl (snd x .fst))) (push (fst x)) (cong inr (snd x .snd))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ∙ (λ i → (λ j → [ inl (snd x .fst (i ∨ ~ j)) ]')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     ∙∙ eq/ (inl (snd x .fst i)) (inr (snd x .snd i)) ((fst x) , ((λ j → snd x .fst (i ∧ j)) , ((λ j → snd x .snd (i ∧ j)))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     ∙∙ λ j → [ inr (snd x .snd (i ∨ j)) ]')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ∙ sym (rUnit _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Iso.rightInv Pushout≃Coeq (eq/ (inr x₁) (inl x₂) () i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Iso.rightInv Pushout≃Coeq (eq/ (inr x₁) (inr x₂) () i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Iso.leftInv Pushout≃Coeq (inl x) = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Iso.leftInv Pushout≃Coeq (inr x) = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Iso.leftInv Pushout≃Coeq (push a i) j = rUnit (push a) (~ j) i

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data SM {ℓ : Level} (X : RP∞) (A : fst X → Pointed ℓ) : Type ℓ where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   l : ((x : fst X) → A x .fst) → SM X A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   r : {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   c : {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _ {ℓ ℓ' : Level} (X : RP∞) (A : fst X → Type ℓ) (R : (x : fst X) → A x → A x → Type ℓ')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   (coh₁ : (x : fst X) (f : ((x : fst X) → A x)) → f ≡ CasesRP X x (f x) (f (not* X x)) )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   (coh₂ : (x : fst X) (f g : ((x : fst X) → A x)) → CasesRP X {A = A} x (g x) (f (not* X x)) ≡ CasesRP X (not* X x) (f (not* X x)) (g (not* X (not* X x))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   (coh₃ : (x : fst X) (g : ((x : fst X) → A x)) → g ≡ CasesRP X (not* X x) (g (not* X x)) (g (not* X (not* X x)))) where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   data Π-coeq  : Type (ℓ-max ℓ ℓ') where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     [_] : ((x : fst X) → A x) → Π-coeq
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     p : (x : fst X) (a a' : A x) (b : A (not* X x)) → R x a a' → [ CasesRP X x a b ] ≡ [ CasesRP X x a' b ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- alt: (f g : _) (x : _) → f x = g x → R (¬ x) (f (not x)) (g (not x)) → [ f ] ≡ [ g ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     q : (f g : (x : fst X) → A x) → ((x : fst X) → R x (f x) (g x)) → [ f ] ≡ [ g ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     q' : (x : fst X) (f g : (x : fst X) → A x) (r : ((x : fst X) → R x (f x) (g x)) )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       → PathP (λ i → [ coh₁ x f i ] ≡ [ coh₃ x g i ]) (q f g r)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    (p x (f x) (g x) (f (not* X x)) (r x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 ∙∙ cong [_] (coh₂ x f g)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 ∙∙ p (not* X x) (f (not* X x)) (g (not* X x)) (g (not* X (not* X x))) (r (not* X x)))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   data Π-coeq'  : Type (ℓ-max ℓ ℓ') where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     [_] : ((x : fst X) → A x) → Π-coeq'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     zZz : (f g : (x : fst X) → A x) (x : _) → f x ≡ g x → R (not* X x) (f (not* X x)) (g (not* X x)) → [ f ] ≡ [ g ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     q : (f g : (x : fst X) → A x) → ((x : fst X) → R x (f x) (g x)) → [ f ] ≡ [ g ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     q' : (x : fst X) (f g : (x : fst X) → A x) (r : ((x : fst X) → R x (f x) (g x)) )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       → PathP (λ i → {!!} ≡ {!!}) (q f g r) {!zZz f g x !} -- {- (x : fst X) (f g : (x : fst X) → A x) (r : ((x : fst X) → R x (f x) (g x)) )
 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- SM : {ℓ : Level} (X : RP∞) (A : fst X → Pointed ℓ) → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- SM X A = Pushout {A = Σ (fst X) (fst ∘ A)} fst λ x → CasesRP X {A = fst ∘ A} (fst x) (snd x) (snd (A (not* X (fst x))))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _ {ℓ : Level} (X Y : RP∞) (A : fst X → fst Y → Pointed₀)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   (c1 : _) (c2 : _) (c3 : _) where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   F : (x : fst X) (y : fst Y) → (fst Y ⊎ ((x₁ : fst Y) → (fst ∘ A x) x₁)) → fst (A x y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   F x y (inl z) = snd (A x y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   F x y (inr z) = z y

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   F-lem : (x x* : fst X) (y y₁ y' : fst Y) (f : _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     → F x y₁ (CasesRP X {A = λ x → fst Y ⊎ ((y : fst Y) → fst (A x y))} x* {!inl y!} {!!} x) ≡ {!!} 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   F-lem = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   SM* : Π-coeq X _ (λ x → (push-rel fst (λ y → CasesRP Y {A = fst ∘ (A x)} (fst y) (snd y) (snd (A x (not* Y (fst y))))))) c1 c2 c3
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     → SM Y λ y → SM X (λ x → A x y) , inr λ x → A x y .snd
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   SM* [ f ] = inr λ y → inr λ x → F x y (f x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   SM* (p x (inl y) (inr f) G ((y' , r) , P , Q) i) = {!cool x y f G y' P r Q i!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     cool : (x : fst X) (y : fst Y) (f : (x' : _) → fst (A x x'))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       → (G : fst Y ⊎ ((x₁ : fst Y) → (fst ∘ A (not* X x)) x₁))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       → (y' : fst Y) (P : y' ≡ y) (y₁ : fst Y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (r : fst (A x y'))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (Q : CasesRP Y y' r (snd (A x (not* Y y'))) ≡ f)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       → Path (SM X (λ x₁ → A x₁ y₁))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (inr (λ x₁ → F x₁ y₁ (CasesRP X x (inl y) G x₁)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (inr (λ x₁ → F x₁ y₁ (CasesRP X x (inr f) G x₁)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     cool x y f (inl x₁) y' P y₁ r Q = {!!} ∙∙ push (x , (f y₁)) ∙∙ {!f y'!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     cool x y f (inr x₁) y' P y₁ r Q = {!!} ∙ sym (push (x , (f y₁))) ∙ {!!} -- refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   SM* (p x (inr x₁) (inl x₂) G () i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   SM* (p x (inr x₁) (inr x₂) G () i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   SM* (q f g x i) = {!g!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   SM* (q' x f g r i i₁) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- TOSM : (X Y : RP∞) (A : fst X → fst Y → Pointed₀) → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- TOSM = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _ {ℓ : Level} (A : Bool → Pointed ℓ) where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open genSmash renaming (⋀∞gen to ⋀∞)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ⋀∞→Smash : ⋀∞ Bool* A (2CaseBool A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --            → Smash (A true) (A false)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ⋀∞→Smash (proj f) = proj (f true) (f false)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ⋀∞→Smash (base false) = baser
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ⋀∞→Smash (base true) = basel
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ⋀∞→Smash (gl false a i) = gluer a i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ⋀∞→Smash (gl true a i) = gluel a i

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   toBool→ : (x : A true .fst) (y : A false .fst) → (x : Bool) → A x .fst
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   toBool→ x y false = y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   toBool→ x y true = x

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   toBool→≡₁ : (x : A true .fst) → toBool→ x (pt (A false)) ≡ 2CaseBool A true x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   toBool→≡₁ x = funExt λ { false → refl ; true → refl}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   toBool→≡₂ : (x : A false .fst) → toBool→ (pt (A true)) x ≡ 2CaseBool A false x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   toBool→≡₂ x = funExt λ { false → refl ; true → refl}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Smash→⋀∞ : Smash (A true) (A false)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     → ⋀∞ Bool* A (2CaseBool A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Smash→⋀∞ basel = base true
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Smash→⋀∞ baser = base false
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Smash→⋀∞ (proj x y) = proj (toBool→ x y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Smash→⋀∞ (gluel a i) = ((λ i → proj (toBool→≡₁ a i)) ∙ gl true a) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Smash→⋀∞ (gluer b i) = ((λ i → proj (toBool→≡₂ b i)) ∙ gl false b) i

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Smash→⋀∞→Smash : (x : Smash (A true) (A false)) → ⋀∞→Smash (Smash→⋀∞ x) ≡ x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Smash→⋀∞→Smash basel = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Smash→⋀∞→Smash baser = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Smash→⋀∞→Smash (proj x y) = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Smash→⋀∞→Smash (gluel a i) j = help j i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     help : cong (⋀∞→Smash) ((λ i → proj (toBool→≡₁ a i)) ∙ gl true a)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --          ≡ gluel a
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     help = cong-∙ ⋀∞→Smash (λ i → proj (toBool→≡₁ a i)) (gl true a)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --          ∙ sym (lUnit _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Smash→⋀∞→Smash (gluer b i) j = help j i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     help : cong (⋀∞→Smash) ((λ i → proj (toBool→≡₂ b i)) ∙ gl false b)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --          ≡ gluer b
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     help = cong-∙ ⋀∞→Smash (λ i → proj (toBool→≡₂ b i)) (gl false b)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --          ∙ sym (lUnit _)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   toBool→diag : (f : ((x : Bool) → A x .fst))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     →  (toBool→ (f true) (f false)) ≡ f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   toBool→diag f = funExt λ { false → refl ; true → refl}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ⋀∞→Smash→⋀∞ : (x : ⋀∞ Bool* A (2CaseBool A))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     → (Smash→⋀∞ (⋀∞→Smash x)) ≡ x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ⋀∞→Smash→⋀∞ (proj x) i = proj (toBool→diag x i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ⋀∞→Smash→⋀∞ (base false) = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ⋀∞→Smash→⋀∞ (base true) = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ⋀∞→Smash→⋀∞ (gl false a i) j = lem j i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     help' : toBool→diag (2CaseBool A false a) ≡ toBool→≡₂ a
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     help' = cong funExt (funExt λ { false → refl ; true → refl})


-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     lem : PathP (λ j → Path (⋀∞ Bool* A (2CaseBool A))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                              (proj (toBool→diag (2CaseBool A false a) j))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                              (base false))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 (((λ i₁ → proj (toBool→≡₂ a i₁)) ∙ gl false a)) (gl false a)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     lem = cong (_∙ gl false a) (λ i j → proj (help' (~ i) j))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --         ◁ λ i j → compPath-filler'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (λ i → proj (toBool→diag (2CaseBool A false a) i))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (gl false a) (~ i) j

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ⋀∞→Smash→⋀∞ (gl true a i) j = lem j i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     help' : toBool→diag (2CaseBool A true a) ≡ toBool→≡₁ a
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     help' = cong funExt (funExt λ { false → refl ; true → refl})


-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     lem : PathP (λ j → Path (⋀∞ Bool* A (2CaseBool A))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                              (proj (toBool→diag (2CaseBool A true a) j))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                              (base true))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 (((λ i₁ → proj (toBool→≡₁ a i₁)) ∙ gl true a)) (gl true a)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     lem = cong (_∙ gl true a) (λ i j → proj (help' (~ i) j))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --         ◁ λ i j → compPath-filler'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (λ i → proj (toBool→diag (2CaseBool A true a) i))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (gl true a) (~ i) j

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ⋀∞≃Smash : Iso (⋀∞ Bool* A (2CaseBool A)) (Smash (A true) (A false))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Iso.fun ⋀∞≃Smash = ⋀∞→Smash
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Iso.inv ⋀∞≃Smash = Smash→⋀∞
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Iso.rightInv ⋀∞≃Smash = Smash→⋀∞→Smash
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Iso.leftInv ⋀∞≃Smash = ⋀∞→Smash→⋀∞


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- myInd : {!∀ {ℓ} {A : Type ℓ} → ?!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- myInd = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- pathF : {A : Type} (x y : A) → (B : x ≡ y → Pointed₀) → ((p : _) → B p .fst)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- pathF {A = A} x y B p = transport (λ i → (B : x ≡ p i → Pointed₀) (q : _) → B q .fst) (λ B q → l2 x x q B) B p
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   l2 : (x y : A) (q : x ≡ y) (B : x ≡ y → Pointed₀) → B q .fst
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   l2 x = J> λ B → B refl .snd

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data myDat {ℓ} (A : Bool → Type ℓ) : Type ℓ where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   incl : Σ[ r ∈ Bool ] (A r × A (not r)) → myDat A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   idr : (p : Σ[ r ∈ Bool ] (A r × A (not r)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     → incl p
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --      ≡ incl ((not (fst p)) , ((p .snd .snd) , (subst A (sym (notnot (fst p))) (p .snd .fst))))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Σ-r : {A : Bool → Type} → Iso ((x : _) → A x) (myDat A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.fun Σ-r f = incl (true , ((f true) , (f false)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.inv Σ-r (incl (false , r , s)) false = r
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.inv Σ-r (incl (true , r , s)) false = s
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.inv Σ-r (incl (false , r , s)) true = s
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.inv Σ-r (incl (true , r , s)) true = r
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.inv Σ-r (idr (false , r , s) i) false = transportRefl r (~ i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.inv Σ-r (idr (true , r , s) i) false = s
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.inv Σ-r (idr (false , r , s) i) true = s
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.inv Σ-r (idr (true , r , s) i) true = transportRefl r (~ i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv Σ-r (incl (false , r , s)) = (λ i → incl (true , s , transportRefl r (~ i))) ∙ sym (idr (false , r , s)) -- idr (true , s , r) ∙ λ i → incl (false , r , transportRefl s i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv Σ-r (incl (true , r , s)) = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv Σ-r (idr (false , r , s) i) j = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv Σ-r (idr (true , r , s) i) j = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.leftInv Σ-r f = {!!} -- funExt λ { false → refl ; true → refl}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _ {ℓ : Level} (X : RP∞) (A : fst X → Pointed ℓ) where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   module M = genSmash X A (λ x a → CasesRP X {fst ∘ A} x a ((snd ∘ A) (not* X x)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open M public renaming (⋀∞gen to ⋀∞)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ⋀∞∙ : Pointed _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst ⋀∞∙ = ⋀∞
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   snd ⋀∞∙ = proj λ x → A x .snd

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ΣRP = Σ[ X ∈ RP∞ ] (Σ[ A ∈ (fst X → Pointed₀) ] ⋀∞ X A)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- TTT : (e : RP∞ ≡ RP∞) (x : RP∞) → RP∞
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- TTT e = transport e



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- BOol× : (A : Bool → Type) → Iso ((x : Bool) → A x) (Σ[ x ∈ Bool ] (A x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.fun (BOol× A) f = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.inv (BOol× A) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (BOol× A) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.leftInv (BOol× A) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- T* : (e : RP∞ ≡ RP∞) → ΣRP ≡ ΣRP
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- T* e i = {!Σ[ X ∈ e i ] (Σ[ A ∈ (fst X → Pointed₀) ] ⋀∞ X A)!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   C : PathP (λ j → {!Σ[ !}) ((x : RP∞) → Pointed₀) ((x : RP∞) → Pointed₀)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   C = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _ {ℓ : Level} (X Y : RP∞) (A : fst X → fst Y → Pointed ℓ) where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   F : ⋀∞∙ X (λ x → ⋀∞∙ Y (A x)) .fst → ⋀∞∙ Y (λ y → ⋀∞∙ X (λ x → A x y)) .fst
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   F (genSmash.proj f) = proj λ y → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   F (genSmash.base x) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   F (genSmash.gl x a i) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- anId : {ℓ : Level} (A : Bool → Pointed ℓ)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → Path ((x : Bool) (a : fst (A x)) → (x : Bool) → A x .fst)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (λ x a → CasesRP Bool* {fst ∘ A} x a ((snd ∘ A) (not* Bool* x)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (2CaseBool A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- anId A =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   funExt λ { false → funExt λ a
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     → funExt λ { false → transportRefl a
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 ; true → transportRefl (A true .snd)}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 ; true → funExt λ a
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          → funExt λ { false → transportRefl (A false .snd)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                      ; true → transportRefl a}}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso-⋀∞Bool : ∀ {ℓ} (A : Bool → Pointed ℓ)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → Iso (⋀∞ Bool* A) (Smash (A true) (A false))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso-⋀∞Bool A =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   compIso (pathToIso (cong (genSmash.⋀∞gen Bool* A) (anId A))) (⋀∞≃Smash A)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso-⋀∞Bool-funId : ∀ {ℓ} (A : Bool → Pointed ℓ)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   (e : (x : fst Bool*) → A x .fst)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → Iso.fun (Iso-⋀∞Bool A) (proj e) ≡ proj (e true) (e false)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso-⋀∞Bool-funId A e i = proj (transportRefl (e true) i) (transportRefl (e false) i)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Kgen : (X : RP∞) (n : fst X → ℕ) → Pointed₀
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Kgen X n = EM∙ ℤ/2 (∑RP X n)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- K∙ = EM∙ ℤ/2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- K = EM ℤ/2

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _ (⌣gen : (X : RP∞) (n : fst X → ℕ)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        → ⋀∞∙ X (λ x → K∙ (n x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        →∙ K∙ (∑RP X n)) where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   module _ (X : RP∞) (n : fst X → ℕ) where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Πpt :  (((x : fst X) → K (n x)) , λ x → 0ₖ (n x)) →∙ K∙ (∑RP X n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     fst Πpt f = ⌣gen X n .fst (proj f)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     snd Πpt = ⌣gen X n .snd

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   lem' : (n : ℕ) (X : RP∞) → ∑RP X (λ _ → n) ≡ n + n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   lem' n = RP∞pt→Prop (λ _ → isSetℕ _ _) refl

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Sq : (n : ℕ) → K n × RP∞ → K (n + n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Sq n (x , t) = subst K (lem' n t) (Πpt t (λ _ → n) .fst λ _ → x)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   genconst : (t : RP∞) (n : fst t → ℕ)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     → ((x : fst t) → K (n x)) → K (∑RP t n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   genconst t n s = Πpt t n .fst s

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   doubler : (t s : RP∞) (n : fst t → fst s → ℕ)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (a : (x : fst t) (y : fst s) → K (n x y))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     → K (∑RP t (λ z → ∑RP s (n z)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   doubler t s n a =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     genconst t (λ z → ∑RP s (n z))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        λ x → genconst s (n x) (a x)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   S'S' : (X Y : RP∞) (n : fst X → fst Y → ℕ) → (x : fst X) (y : fst Y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     → (K∙ (n x y) ⋀∙ K∙ (n x (not* Y y))) ⋀ (K∙ (n (not* X x) y) ⋀∙ K∙ (n (not* X x) (not* Y y))) → K (∑RP X (λ x → ∑RP Y (n x))) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   S'S' X Y n x y (inl x₁) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   S'S' X Y n x y (inr (inl x₁ , b)) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   S'S' X Y n x y (inr (inr x₁ , inl x₂)) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   S'S' X Y n x y (inr (inr x₁ , inr x₂)) = Πpt X (λ x → ∑RP Y (n x)) .fst λ x' → Πpt Y (n x') .fst λ y → {!⌣gen X ? .fst ? .fst ?!} --  ⌣gen X (λ x → {!n x y!}) .fst (proj {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   S'S' X Y n x y (inr (inr x₁ , push a i)) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   S'S' X Y n x y (inr (push a i , b)) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   S'S' X Y n x y (push a i) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   SS : (X Y : RP∞) (n : fst X → fst Y → ℕ) → Pointed₀ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   SS X Y n = ⋀∞∙ X λ x → ⋀∞∙ Y λ y → K∙ (n x y)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   SS' : (X Y : RP∞) (n : fst X → fst Y → ℕ) → Pointed₀ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   SS' X Y n = ⋀∞∙ Y λ y → ⋀∞∙ X λ x → K∙ (n x y)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test123 : (X : RP∞) (A : fst X → Pointed₀) → Susp (Susp (⋀∞ X A)) → ⋀∞ X (λ x → Susp∙ (fst (A x)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test123 X A north = proj λ _ → north
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test123 X A south = proj λ _ → south
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test123 X A (merid north i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test123 X A (merid south i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test123 X A (merid (merid a i₁) i) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   SS→ : (X Y : RP∞) (n : fst X → fst Y → ℕ)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     → SS X Y n .fst
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     → K (∑RP X (λ x → ∑RP Y (n x)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   SS→ X Y n (genSmash.proj f) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     genconst X (λ x → ∑RP Y (n x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       λ x → ⌣gen Y (n x) .fst (f x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   SS→ X Y n (genSmash.base x) = 0ₖ (∑RP X (λ x₁ → ∑RP Y (n x₁)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   SS→ X Y n (genSmash.gl x (genSmash.proj x₁) i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   SS→ X Y n (genSmash.gl x (genSmash.base x₁) i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   SS→ X Y n (genSmash.gl x (genSmash.gl x₁ a i) j) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   SS→* : (X Y : RP∞) (n : fst X → fst Y → ℕ)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     → SS X Y n .fst
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     → K (∑RP Y (λ y → ∑RP X (λ x → n x y)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   SS→* X Y n (genSmash.proj x) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ⌣gen Y (λ y → ∑RP X (λ x₁ → n x₁ y)) .fst
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (proj λ y → {!x ?!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   SS→* X Y n (genSmash.base x) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   SS→* X Y n (genSmash.gl x a i) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- hPropFib : ∀ {ℓ} (X : RP∞) (A : fst X → fst X → Pointed ℓ)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → ((x y : _) → isProp (typ (A x y)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → hProp ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- hPropFib = uncurry (λ X
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → rec→Set {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (λ e A pr → A (invEq e true) (invEq e false) .fst , {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     λ e g → funExt λ A → funExt λ z → Σ≡Prop {!!} {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _ (⌣gen : (X : RP∞) (n : fst X → ℕ)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        → ⋀∞∙ X (λ x → K∙ (n x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        →∙ K∙ (∑RP X n)) where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   h : (m : ℕ) (x : K m) (y y' : RP∞)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     → Sq ⌣gen (m + m) ((Sq ⌣gen m (x , y')) , y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      ≡ Sq ⌣gen (m + m) ((Sq ⌣gen m (x , y)) , y')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   h m x y y' = {!Πpt ⌣gen y (λ _ → m + m) .fst (λ _ → Sq ⌣gen m (x , y'))!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- SqA : (n : ℕ) → K n × RP∞ → K (n + n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Sq n (x , t) = subst K (lem' n t) (Πpt t (λ _ → n) .fst λ _ → x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- flipBool : {X : Type₀} → X ≃ Bool → X ≃ Bool
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- flipBool e = compEquiv e notEquiv

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- notComm : (X : RP∞) (e : fst X ≃ Bool)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → not* X (invEq e true) ≡ invEq e false
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- notComm =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   RP∞pt→Prop (λ X → isPropΠ λ _ → isSetRPpt X _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     λ e → {!funExt⁻ (cong fst (Iso.leftInv Bool≃Charac (invEquiv e))) x!} ∙∙ {!!} ∙∙ funExt⁻ (cong invEq (Iso.leftInv Bool≃Charac e)) false

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- liftHom : (X : RP∞) (A : fst X → Pointed₀) (C : Type)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → (e : fst X ≃ Bool)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → (((x : fst X) → A x .fst) → C)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → A (invEq e true) .fst → A (invEq e false) .fst → C
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- liftHom X A C e f x y =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   f (CasesRP X (invEq e true) x (subst (fst ∘ A) (sym (notComm X e)) y))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- test123 : (A B C : Pointed₀)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → Iso (A →∙ (B →∙ C ∙))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (Σ[ f ∈ (fst A → fst B → fst C) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         Σ[ l ∈ ((x : fst A) → f x (pt B) ≡ pt C) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           Σ[ r ∈ ((y : fst B) → f (pt A) y ≡ pt C) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               PathP (λ i → r (pt B) i ≡ snd C)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (l (pt A)) (λ _ → pt C) )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.fun (test123 A B C) f = (λ x y → f .fst x .fst y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                           , ((λ x → f .fst x .snd)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                           , (λ y i → f .snd i .fst y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                           , cong snd (snd f))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.inv (test123 A B C) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (test123 A B C) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.leftInv (test123 A B C) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ind* : (X : RP∞) → fst X → fst X ≃ Bool
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ind* X x = isoToEquiv (iso (F⁻ X x) (F X x) (F-F X x .snd) (F-F X x .fst))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   F : (X : RP∞) → fst X → Bool → fst X
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   F X x false = not* X x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   F X x true = x

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   F⁻ : (X : RP∞) → fst X → fst X → Bool
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   F⁻ X x = CasesRP X x true false

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   F-F : (X : RP∞) (x : fst X) → ((y : fst X) → F X x (F⁻ X x y) ≡ y) × ((y : Bool) → F⁻ X x (F X x y) ≡ y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   F-F =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     uncurry λ X → PT.elim (λ p
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       → isPropΠ λ _ → isProp× (isPropΠ (λ _ → isSetRPpt (X , p) _ _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (isPropΠ (λ _ → isSetBool _ _)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (EquivJ (λ X x₁ → (x₂ : X) → ((y : X) → F (X , ∣ x₁ ∣₁) x₂ (F⁻ (X , ∣ x₁ ∣₁) x₂ y) ≡ y) ×
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ((y : Bool) → F⁻ (X , ∣ x₁ ∣₁) x₂ (F (X , ∣ x₁ ∣₁) x₂ y) ≡ y))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         λ { false → (λ { false → refl ; true → refl}) , λ { false → refl ; true → refl}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ; true → (λ { false → refl ; true → refl}) , λ { false → refl ; true → refl}})

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ind** : ∀ {ℓ} (A : (X : RP∞) → fst X → Type ℓ)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → Σ[ F ∈ (A Bool* true → (x : _) (y : _) → A x y) ] ((p : A Bool* true) → F p Bool* true ≡ p)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ind** A = (λ p x y → subst A' (sym (Path1 x y)) p)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         , λ p → cong (λ x → subst A' (sym x) p) Path1≡refl ∙ transportRefl p
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   help : (x : RP∞) (y : fst x) → x ≡ Bool*
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   help x y = Σ≡Prop (λ _ → squash₁) (ua (ind* x y))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ind*-lem : ind* Bool* true ≡ idEquiv _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ind*-lem = Σ≡Prop isPropIsEquiv (funExt λ { false → refl ; true → refl})

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   abstract
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     help-base : help Bool* true ≡ refl 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     help-base = (λ i → Σ≡Prop (λ _ → squash₁) (ua (ind*-lem i)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ∙ ΣSquareSet (λ _ → isProp→isSet squash₁) uaIdEquiv

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   p2 : (x : RP∞) (y : fst x) → PathP (λ i → help x y i .fst) y true
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   p2 = uncurry λ X → PT.elim (λ _ → isPropΠ λ _ → isOfHLevelPathP' 1 isSetBool _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (EquivJ (λ X x → (y : X) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       PathP (λ i → help (X , ∣ x ∣₁) y i .fst) y true)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         λ { false → toPathP refl ; true → toPathP refl})

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   p2-pp : PathP (λ i → PathP (λ X → help-base i X .fst) true true) (p2 Bool* true) refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   p2-pp = isOfHLevelPathP' 0 (isOfHLevelPathP' 1 isSetBool _ _) _ _ .fst

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   A' : Σ RP∞ fst → Type _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   A' (x , p) = A x p

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Path1 : (x : RP∞) (y : fst x) → Path (Σ RP∞ fst) (x , y) (Bool* , true)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Path1 x y = ΣPathP ((help x y ) , (p2 x y))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Path1≡refl : Path1 Bool* true ≡ refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Path1≡refl = ΣSquareSet (λ X → isSetRPpt X) help-base

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   pst' : (x : RP∞) (y : fst x) → A x y ≡ A Bool* true
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   pst' x y i = A (help x y i) (p2 x y i)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- bakam : (A B C : Pointed₀)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → isHomogeneous C
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → isSet (A →∙ (B →∙ C ∙))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → isSet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (Σ[ f ∈ (fst A → (fst B → fst C)) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (Σ[ l ∈ ((b : fst B) → f (pt A) b ≡ pt C) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            Σ[ r ∈ ((a : fst A) → f a (pt B) ≡ pt C) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ∥ PathP (λ i → l (pt B) i ≡ pt C) (r (pt A)) refl ∥₂))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- bakam A B C hom c =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   uncurry λ f1 → uncurry λ l1 → uncurry
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     λ r1 → ST.elim (λ _ → isSetΠ λ _ → isProp→isSet isPropIsProp)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       λ q1
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       → uncurry λ f2 → uncurry λ l2 → uncurry
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     λ r2 → ST.elim (λ _ → isProp→isSet isPropIsProp)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       λ q2 → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   T' : Type _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   T' = Σ[ q ∈ Σ[ f ∈ (fst A → (fst B → fst C)) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (Σ[ l ∈ ((b : fst B) → f (pt A) b ≡ pt C) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 ((a : fst A) → f a (pt B) ≡ pt C)) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         ∥ PathP (λ i → q .snd .fst (pt B) i ≡ pt C) (q .snd .snd (pt A)) refl ∥₂

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   T = (Σ[ f ∈ (fst A → (fst B → fst C)) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (Σ[ l ∈ ((b : fst B) → f (pt A) b ≡ pt C) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            Σ[ r ∈ ((a : fst A) → f a (pt B) ≡ pt C) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ∥ PathP (λ i → l (pt B) i ≡ pt C) (r (pt A)) refl ∥₂))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   to : (A →∙ (B →∙ C ∙)) → T
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   to f = (λ x y → fst f x .fst y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        , ((λ b → λ i → snd f i .fst b)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        , ((λ a → fst f a .snd) , ∣ cong snd (snd f) ∣₂)) -- (f , l , r , ∣ p ∣₂)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   back : T → A →∙ (B →∙ C ∙)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   back = uncurry λ f → uncurry λ l → uncurry λ r → ST.rec c λ q → (λ x → f x , r x) , (λ i → (λ b → l b i) , (q i))



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ptsd : isSet T'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ptsd = λ {((f , l , r) , p) → J> λ y → {!!}}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {- uncurry λ {(f , l  , r)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     → ST.elim (λ _ → isSetΠ λ _ → isProp→isSet isPropIsProp)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          λ q1 → uncurry λ {(f2 , l2  , r2)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     → ST.elim (λ _ → isProp→isSet isPropIsProp)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       λ q2 → λ p q → ΣSquareSet (λ _ → squash₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         {!c (back (f , (l , (r , ∣ q1 ∣₂)))) ((back (f , (l , (r , ∣ q1 ∣₂))))) !}}}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open import Cubical.Functions.Embedding



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   back-emb : isEmbedding back
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   back-emb x y = isoToIsEquiv (iso _ (h x y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (λ q → {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      λ q → {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     h : (x y : _) → back x ≡ back y → x ≡ y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     h x y p = {!!} --  ΣPathP ((λ i a b → {!p i .fst a .fst b!}) , {!!}) -- →∙Homogeneous≡ (isHomogeneous→∙ hom) (funExt λ a → →∙Homogeneous≡ hom (λ i b → fst (q i) a b))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     h⁻ : {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     h⁻ = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- foo : ∀ {ℓ} (A : (X : RP∞) → fst X → Type ℓ) → Iso ((x : _) (y : _) → A x y) (A Bool* true)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.fun (foo A) F = F Bool* true
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.inv (foo A) = ind** A .fst
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (foo A) p = ind** A .snd p
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.leftInv (foo A) F = funExt λ X → funExt (help X)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   help : (X : RP∞) (y : fst X) → ind** A .fst (F Bool* true) X y ≡ F X y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   help = ind** (λ X y → ind** A .fst (F Bool* true) X y ≡ F X y) .fst (ind** A .snd (F Bool* true))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- majp : {!(A : (X : RP∞) (x : fst X) → Pointed₀) (B : (X : RP∞) (x : fst X) → Pointed₀) → ?!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- majp = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ind**a : (A : (X : RP∞) (x : fst X) → Pointed₀) (B : (X : RP∞) (x : fst X) → Pointed₀)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → (((X : RP∞) (x : fst X) → A X x .fst) → (X : RP∞) (x : fst X) → B X x .fst)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → Σ[ X ∈ RP∞ ] (⋀∞ X (A X)) → Σ[ X ∈ RP∞ ] ((x : fst X) → B X x .fst)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ind**a A B ind (X , genSmash.proj x) = {!x!} , (ind (λ X q → {!!}) X )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ind**a A B ind (X , genSmash.base x) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ind**a A B ind (X , genSmash.gl x a i) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _ (A : (X : RP∞) → (x : fst X) → (Y : RP∞) → (y : fst Y) → (fst X → fst Y → ℕ) → Pointed₀)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   l' : (X : RP∞) (Y : RP∞) (n : fst X → fst Y → ℕ) → Type _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   l' X Y n = ⋀∞ X λ x → ⋀∞ Y (λ y → A X x Y y n) , proj (λ y → A X x Y y n .snd)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   r' : (X : RP∞) (Y : RP∞) (n : fst X → fst Y → ℕ) → Type _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   r' X Y n = ⋀∞ Y λ y → ⋀∞ X (λ x → A X x Y y n) , proj (λ x → A X x Y y n .snd)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   IS1 : (Y : RP∞) → Iso ((X : RP∞) (x₁ : fst X) → (n : fst X → fst Y → ℕ) → ⋀∞ Y (λ Y₁ → A X x₁ Y Y₁ n)) ((n : Bool → fst Y → ℕ) → ⋀∞ Y (λ Y₁ → A Bool* true Y Y₁ n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   IS1 Y = foo _

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   blahem : (X : RP∞) (Y : RP∞) (n : fst X → fst Y → ℕ) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       l' X Y n → r' X Y n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   blahem X Y n (genSmash.proj x) = proj λ y → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   blahem X Y n (genSmash.base x) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   blahem X Y n (genSmash.gl x a i) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- BiHom' : (X : RP∞) (A : fst X → Pointed₀) (C : Pointed₀) → Type
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- BiHom' X A C =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Σ[ f ∈ (((x : fst X) → A x .fst) → C .fst) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Σ[ g ∈ ((e : fst X ≃ Bool)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       → A (invEq e true) →∙ (A (invEq e false) →∙ C ∙)) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- RPfun-gen : (X : RP∞) (A : fst X → Pointed₀) (x : fst X)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → A x .fst
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → (x' : fst X) → Dec (x ≡ x') → A x' .fst
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- RPfun-gen X A x a x' (yes p) = subst (fst ∘ A) p a
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- RPfun-gen X A x a x' (no ¬p) = A x' .snd

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- RPfun : (X : RP∞) (A : fst X → Pointed₀) (x : fst X)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → A x .fst
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → (x : fst X) → A x .fst
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- RPfun X A x p y = RPfun-gen X A x p y (decPt X x y)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- RPfun-const : (X : RP∞) (A : fst X → Pointed₀) (x₀ : fst X)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → (x : fst X)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → (p : Dec (x₀ ≡ x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → RPfun-gen X A x₀ (A x₀ .snd) x p
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ≡ A x .snd
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- RPfun-const X A x₀ x (yes p) i =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   transp (λ j → fst (A (p (i ∨ j)))) i (A (p i) .snd)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- RPfun-const X A x₀ x (no ¬p) = refl

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- BiHom* : (X : RP∞) (A : fst X → Pointed₀) (C : Pointed₀) → Type
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- BiHom* X A C =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Σ[ c ∈ (fst X → fst C) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Σ[ f ∈ ((((x : fst X) → A x .fst) , λ x → A x .snd) →∙ C) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ((x : fst X) (a : A x .fst) → fst f (RPfun X A x a) ≡ c x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isBihom : (X : RP∞) (A : fst X → Pointed₀) (C : Pointed₀)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → (((x : fst X) → A x .fst) , λ x → A x .snd) →∙ C → Type
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isBihom X A C f =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Σ[ c ∈ (fst X → fst C) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ((x : fst X) (a : A x .fst) → fst f (RPfun X A x a) ≡ c x)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- BiHom* : (X : RP∞) (A : fst X → Pointed₀) (C : Pointed₀) → Type
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- BiHom* X A C = Σ[ f ∈ ((((x : fst X) → A x .fst) , λ x → A x .snd) →∙ C) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     isBihom X A C f

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- BiHom's : (X Y : RP∞) (A : fst X → fst Y → Pointed₀) (C : Pointed₀)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → BiHom* X (λ x → ((y : fst Y) → A x y .fst) , (λ y → A x y .snd)) C
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → Type
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- BiHom's X Y A C (F , c) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Σ[ l ∈ ((x : fst X) (f : (y : _) → A x y .fst) → {!F .fst !}) ] {!is!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   c' : {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   c' = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- QHom** : (X Y : RP∞) (A : fst X → fst Y → Pointed₀) (C : Pointed₀) → Type
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- QHom** X Y A C = Σ[ F ∈ BiHom* X (λ x → BiHom* Y (λ y → A x y) C , {!!}) C ] {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- BiHom** : (X : RP∞) (A : fst X → Pointed₀) (C : Pointed₀) → Type
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- BiHom** X A C =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Σ[ f ∈ ((((x : fst X) → A x .fst) , snd ∘ A) →∙ C) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    Σ[ f-coh ∈ ((x : fst X) (z : A x .fst) → fst f (RPfun X A x z) ≡ pt C) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      ((x : fst X)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        → PathP (λ i → fst f (λ x' → RPfun-const X A x x' (decPt X x x') (~ i)) ≡ pt C)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 (f .snd) (f-coh x (A x .snd)))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- 4-elt : Type₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- 4-elt = Σ[ X ∈ Type ] ∥ X ≃ Bool × Bool ∥₁

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSet-4 : (x : 4-elt) → isSet (fst x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSet-4 = uncurry λ X → PT.elim (λ _ → isPropIsOfHLevel 2)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   λ p → subst isSet (sym (ua p))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (isSet× isSetBool isSetBool)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- perm : (X : 4-elt) → hSet ℓ-zero
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- perm = uncurry λ X → {!PT.rec ? ?!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Z ONE TWO THREE : Bool × Bool
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Z = false , false
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ONE = true , false
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- TWO = false , true
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- THREE = true , true

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- suc' : Bool × Bool → Bool × Bool
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- suc' (false , false) = ONE
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- suc' (false , true) = THREE
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- suc' (true , false) = TWO
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- suc' (true , true) = Z

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data sub2 (X : 4-elt) : Type where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   [_,_] : (x y : fst X) → ¬ (x ≡ y) → sub2 X
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   pz : (x y : fst X) (p : ¬ (x ≡ y))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     → [ x , y ] p ≡ [ y , x ] (p ∘ sym)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isCyclic : (X : 4-elt)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → (fst X ≃ Bool × Bool)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → hProp ℓ-zero
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isCyclic =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   uncurry λ X
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    → rec→Set
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        {!X!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        {!X!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        {!X!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   F : (X : Type) → X ≃ Bool × Bool → X ≃ Bool × Bool → hProp ℓ-zero
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst (F X e p) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   snd (F X e p) = {!p!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- sub2-4 : (X : 4-elt) → sub2 X
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → {!1,2,3,4!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- sub2-4 = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- sub2* : (X : 4-elt) → isSet (sub2 X)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- sub2* =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   uncurry (λ X → PT.elim (λ p → isPropIsOfHLevel 2)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (EquivJ (λ X x → isSet (sub2 (X , ∣ x ∣₁)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {!!}))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- bram : (X : 4-elt) → fst X → fst X
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- bram = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- BiHom^ : (x : 4-elt) → fst x → fst x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- BiHom^ = uncurry λ X
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → elim→Set (λ p → isSetΠ λ _ → isSet-4 (X , p))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (λ e x → invEq e (suc' (fst e x)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       λ e e' → funExt λ x → {!e .fst x ≡ ?!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- QuadHomIso* : (X : 4-elt) {A : fst X → Pointed₀}  (C : Pointed₀) → Type₁ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- QuadHomIso* X {A = A} C =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Σ[ F ∈ (((x : fst X) → A x .fst) → typ C) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Σ[ Fl ∈ {!!} ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Q* : (X Y : RP∞) (A : fst X → fst Y → Pointed₀) (B : Pointed₀)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → Type 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Q* X Y A B =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Σ[ F ∈ (((x : fst X) (y : fst Y) → A x y .fst) → B .fst) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Σ[ e ∈ ((y : fst Y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (f : (x : fst X) → A x y .fst)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          → {!!}) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- QuadHomIso : {A B C D E : Pointed₀}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → Iso (A →∙ (B →∙ C →∙ D →∙ E ∙ ∙ ∙))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (Σ[ f ∈ (fst A → fst B → fst C → fst D → fst E) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           Σ[ f-a ∈ ((b : fst B) (c : fst C) (d : fst D) → f (pt A) b c d ≡ pt E) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           Σ[ f-b ∈ ((a : fst A) (c : fst C) (d : fst D) → f a (pt B) c d ≡ pt E) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           Σ[ f-c ∈ ((a : fst A) (b : fst B) (d : fst D) → f a b (pt C) d ≡ pt E) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           Σ[ f-d ∈ ((a : fst A) (b : fst B) (c : fst C) → f a b c (pt D) ≡ pt E) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           Σ[ f-ab ∈ ((c : fst C) (d : fst D)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             → PathP (λ i → f-a (pt B) c d i ≡ pt E) (f-b (pt A) c d) refl) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           Σ[ f-bc ∈ ((a : fst A) (d : fst D)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             → PathP (λ i → f-b a (pt C) d i ≡ pt E) (f-c a (pt B) d) refl) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           Σ[ f-cd ∈ ((a : fst A) (b : fst B)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             → PathP (λ i → f-c a b (pt D) i ≡ pt E) (f-d a b (pt C)) refl) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           Σ[ f-ac ∈ ((b : fst B) (d : fst D)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             → PathP (λ i → f-a b (pt C) d i ≡ pt E) (f-c (pt A) b d) refl) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           Σ[ f-ad ∈ ((b : fst B) (c : fst C)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             → PathP (λ i → f-a b c (pt D) i ≡ pt E) (f-d (pt A) b c) refl) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           Σ[ f-bd ∈ ((a : fst A) (c : fst C)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             → PathP (λ i → f-b a c (pt D) i ≡ pt E) (f-d a (pt B) c) refl) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           Σ[ f-bcd ∈ ((a : typ A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             → Cube (f-cd a (pt B)) (λ _ _ → pt E)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     (f-bd a (pt C)) (λ _ _ → pt E)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     (f-bc a (pt D)) (λ _ _ → pt E)) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           Σ[ f-acd ∈ ((b : typ B)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             → Cube (f-cd (pt A) b) (λ _ _ → pt E)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     (f-ad b (pt C)) (λ _ _ → pt E)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     (f-ac b (pt D)) (λ _ _ → pt E)) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           Σ[ f-abd ∈ ((c : typ C)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             → Cube (f-bd (pt A) c) (λ _ _ → pt E)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     (f-ad (pt B) c) (λ _ _ → pt E)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     (f-ab c (pt D)) (λ _ _ → pt E)) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           Σ[ f-abc ∈ ((d : typ D)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             → Cube (f-bc (pt A) d) (λ _ _ → pt E)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     (f-ac (pt B) d) (λ _ _ → pt E)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     (f-ab (pt C) d) (λ _ _ → pt E)) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           PathP (λ i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            → Cube (f-acd (pt B) i) (λ _ _ → pt E)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    (f-abd (pt C) i) (λ _ _ → pt E)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    (f-abc (pt D) i) λ _ _ → pt E)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (f-bcd (pt A))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.fun (QuadHomIso {A} {B} {C} {D} {E}) f =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   (λ x y z w → f .fst x .fst y .fst z .fst w)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   , ((λ b c d i → f .snd i .fst b .fst c .fst d)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   , (λ a c d i → f .fst a .snd i .fst c .fst d)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   , ((λ a b d i → f .fst a .fst b .snd i .fst d)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   , ((λ a b c → f .fst a .fst b .fst c .snd)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   , ((λ c d i j → f .snd i .snd j .fst c .fst d)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   , (λ a d i j → f .fst a .snd i .snd j .fst d)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   , (λ a b i j → f .fst a .fst b .snd i .snd j)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   , ((λ b d i j → f .snd i .fst b .snd j .fst d)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   , (λ b c i → f .snd i .fst b .fst c .snd)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   , (λ a c i → f .fst a .snd i .fst c .snd)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   , ((λ a i j k → f .fst a .snd i .snd j .snd k)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   , (λ b i j k  → f .snd i .fst b .snd j .snd k)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   , (λ c i j k → f .snd i .snd j .fst c .snd k)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   , (λ d i j k → f .snd i .snd j .snd k .fst d)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   , λ i j k w → f .snd i .snd j .snd k .snd w))))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.inv (QuadHomIso {A} {B} {C} {D} {E})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   (f , f-a , f-b , f-c , f-d , f-ab , f-bc , f-cd , f-ac , f-ad , f-bd
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      , f-bcd , f-acd , f-abd , f-abc , co) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (λ a → (λ b → (λ c → (λ d → f a b c d)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          , f-d a b c)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            , λ i → (λ d → f-c a b d i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   , (f-cd a b i))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           , λ i → (λ c → (λ d → f-b a c d i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  , f-bd a c i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  , (λ j → (λ d → f-bc a d i j)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  , (f-bcd a i j)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      , λ i → (λ b → (λ c → (λ d → f-a b c d i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             , f-ad b c i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             , λ j → (λ d → f-ac b d i j)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    , f-acd b i j)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             , (λ j → (λ c → (λ d → f-ab c d i j)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     , (f-abd c i j))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     , (λ k → (λ d → f-abc d i j k)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     , (co i j k)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (QuadHomIso {A} {B} {C} {D} {E}) _ = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.leftInv (QuadHomIso {A} {B} {C} {D} {E}) _ = refl

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- TriHom* : {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- TriHom* = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Bool→ : ∀ {ℓ} → (A : (x : Bool) → Type ℓ)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → Iso ((x : Bool) → A x) (A true × A false)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.fun (Bool→ A) f = f true , f false
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.inv (Bool→ A) (a , b) false = b
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.inv (Bool→ A) (a , b) true = a
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (Bool→ A) _ = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.leftInv (Bool→ A) f = funExt λ { false → refl ; true → refl}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso-BiHom** : (A : Bool → Pointed₀) (C : Pointed₀)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → Iso (BiHom** Bool* A C)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          ((Σ[ f ∈ (A true .fst × A false .fst → fst C) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            Σ[ l ∈ ((x : A true .fst) → f (x , A false .snd) ≡ pt C) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              Σ[ r ∈ ((b : A false .fst) → f (A true .snd , b) ≡ pt C) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                PathP (λ i → r (A false .snd) i ≡ pt C) (l (A true .snd)) refl)) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso-BiHom** A C =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   compIso
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (compIso
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (invIso (Σ-cong-iso-fst (Σ-cong-iso-fst (invIso (domIso (Bool→ (fst ∘ A)))))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (Σ-cong-iso-snd λ f → invIso
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (Σ-cong-iso-fst (invIso (Bool→ (λ x → (z : A x .fst) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           f .fst (RPfun Bool* A x z true , RPfun Bool* A x z false) ≡ pt C))))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (compIso
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       Σ-assoc-Iso
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (Σ-cong-iso-snd
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         λ f → {!!}))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- →∙→∙Iso : ∀ {ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → Iso (A →∙ (B →∙ C ∙))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (Σ[ f ∈ (fst A → fst B → fst C) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            Σ[ l ∈ ((x : fst A) → f x (pt B) ≡ pt C) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              Σ[ r ∈ ((b : fst B) → f (pt A) b ≡ pt C) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                PathP (λ i → r (pt B) i ≡ pt C) (l (pt A)) refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.fun →∙→∙Iso f =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (λ x y → f .fst x .fst y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    , ((λ x → f .fst x .snd)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    , ((λ y i → f .snd i .fst y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    , cong snd (snd f)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.inv →∙→∙Iso = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv →∙→∙Iso = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.leftInv →∙→∙Iso = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- BiHom**-bool : {!BiHom**!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- BiHom**-bool = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- BiBiHom : (X Y : RP∞) (A : fst X → fst Y → Pointed₀)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   (C : Pointed₀) → Type
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- BiBiHom X Y A C =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Σ[ F ∈ (((x : fst X) (y : fst Y) → A x y .fst)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               , λ x y → A x y .snd)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           →∙ C ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Σ[ pts ∈ (fst Y → fst C × fst C)  ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Σ[ l∧ ∈ ((x : fst X) → BiHom* Y (A x) C) ] 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Σ[ r ∈ ((y : fst Y) → ((x : fst X) → A x y .fst) → fst C) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Σ[ F-lr ∈ ((y : fst Y) (f : ((x : fst X) → A x y .fst))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            → F .fst (λ x → RPfun Y (A x) y (f x)) ≡ r y f) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Σ[ l∧-r ∈ ((x : fst X) (y : fst Y) (z : A x y .fst) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              → r y (RPfun X (λ x → A x y) x z) ≡ l∧ x .fst y) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Σ[ F-coh ∈ ((x : fst X) (f : (y : fst Y) → A x y .fst)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                → F .fst
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  (RPfun X (λ x → (((y : fst Y) → A x y .fst) , λ y → A x y .snd))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                         x f)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 ≡ l∧ x .snd .fst .fst f) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Σ[ high ∈ ((x : fst X) (y : fst Y) (z : A x y .fst)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       → PathP (λ i → F-coh x (RPfun Y (A x) y z) i ≡ l∧-r x y z i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (cong (F .fst) (funExt
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  (λ x' → funExt λ y'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    → cool x y z x' y' (decPt X x x') (decPt Y y y')))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                ∙ F-lr y (RPfun X (λ x₁ → A x₁ y) x z))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (l∧ x .snd .snd y z)) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Σ[ l∧-pt ∈ ((x : fst X) → l∧ x .snd .fst .fst (λ y → A x y .snd) ≡ pts .fst) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Σ[ F-2r ∈ ((y : fst Y) (f : ((x : fst X) → A x y .fst))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     → F .fst (λ x → RPfun Y (A x) y (f x)) ≡ pts .fst) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   cool : (x : fst X) (y : fst Y) (z : A x y .fst) (x' : fst X) (y' : fst Y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     → (p : Dec (x ≡ x')) (q : Dec (y ≡ y'))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     → Path (A x' y' .fst)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               ((RPfun-gen X
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (λ x₁ → ((y₁ : fst Y) → A x₁ y₁ .fst) , (λ y₁ → A x₁ y₁ .snd)) x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (λ y' → RPfun-gen Y (A x) y z y' (decPt Y y y'))) x' p y')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (RPfun-gen Y (A x') y (RPfun-gen X (λ x → A x y) x z x' p) y' q)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   cool x y z x' y' (yes p) (yes q) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (λ j → subst2 (λ x₁ y' → A x₁ y' .fst) p
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (λ i → transportRefl y' (i ∨ j))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                      (RPfun-gen Y (A x) y z (transportRefl y' j)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                        (decPt Y y (transportRefl y' j))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ∙ cong (subst (λ x₁ → A x₁ y' .fst) p)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            (cong (RPfun-gen Y (A x) y z y')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (isPropDec (isSetRPpt Y y y') (decPt Y y y') (yes q)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ∙ {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ∙ {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   cool x y z x' y' (yes p) (no ¬q) = {!(λ y'' → RPfun-gen Y (A x) y z y'' (decPt Y y y'')) y'!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   cool x y z x' y' (no ¬p) q = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _ (A B C D E : Pointed₀) (ptl ptr : fst E)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (l∧ r∧ : typ (Smash⋆ C D) → fst E) -- ok
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (l r : typ A → typ B → typ E) -- ok
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (F : typ A → typ B → typ C → typ D → typ E) -- ok
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (F-l : (x : typ A) (y : fst B) (c : fst C)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            → F x y c (pt D)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            ≡ l x y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (F-r : (x : typ A) (y : fst B) (d : fst D)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            → F x y (pt C) d
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            ≡ r x y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (l∧-l : (a : typ A) → l a (pt B) ≡ l∧ basel)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (r∧-r : (a : typ A) → r a (pt B) ≡ l∧ baser)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (Fg : (a : typ A) (x : fst C) (y : fst D) → F a (pt B) x y ≡ l∧ (proj x y))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (Gg : (b : typ B) (x : fst C) (y : fst D) → F (pt A) b x y ≡ r∧ (proj x y))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (Fg-high-l : (a : typ A) (c : fst C)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            → PathP (λ i → Fg a c (pt D) i ≡ l∧-l a i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 (F-l a (pt B) c)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 (cong l∧ (gluel c)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (Fg-high-r : (a : typ A) (d : fst D)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            → PathP (λ i → Fg a (pt C) d i ≡ r∧-r a i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 (F-r a (pt B) d) -- ()
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 (cong l∧ (gluer d)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (l-r∧ : (b : typ B) → l (pt A) b ≡ r∧ basel)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (r-r∧ : (b : typ B) → r (pt A) b ≡ r∧ baser)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (l∧-pt : l∧ (proj (pt C) (pt D)) ≡ ptl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (r∧-pt : r∧ (proj (pt C) (pt D)) ≡ ptl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (F-2r : (x : typ A) (y : typ B) → F x y (pt C) (pt D) ≡ ptl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test : Smash⋆ (Smash⋆ A B) (Smash⋆ C D) →∙ E
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst test basel = ptl -- ∙l
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst test baser = ptr -- ∙r
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst test (proj basel y) = l∧ y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst test (proj baser y) = r∧ y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst test (proj (proj x y) basel) = l x y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst test (proj (proj x y) baser) = r x y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst test (proj (proj x y) (proj z w)) = F x y z w
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst test (proj (proj x y) (gluel a i)) = F-l x y a i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst test (proj (proj x y) (gluer b i)) = F-r x y b i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst test (proj (gluel a i) basel) = l∧-l a i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst test (proj (gluel a i) baser) = r∧-r a i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst test (proj (gluel a i) (proj x y)) = Fg a x y i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst test (proj (gluel a i) (gluel b j)) = Fg-high-l a b i j
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst test (proj (gluel a i) (gluer b j)) = Fg-high-r a b i j
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst test (proj (gluer b i) basel) = l-r∧ b i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst test (proj (gluer b i) baser) = r-r∧ b i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst test (proj (gluer b i) (proj x y)) = Gg b x y i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst test (proj (gluer b i) (gluel c j)) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst test (proj (gluer b i) (gluer d j)) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst test (gluel basel i) = l∧-pt i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst test (gluel baser i) = r∧-pt i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst test (gluel (proj x y) i) = F-2r x y i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst test (gluel (gluel a j) i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst test (gluel (gluer b j) i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst test (gluer basel i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst test (gluer baser i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst test (gluer (proj x y) i) = {!F-2r!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst test (gluer (gluel a i₁) i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst test (gluer (gluer b i₁) i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   snd test = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- BiHomBool : (A : Bool → Pointed₀) (C : Pointed₀)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → Iso (BiHom* Bool* A C) (Smash⋆ (A true) (A false) →∙ C)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- BiHomBool A C =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   compIso
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (invIso (Σ-cong-iso-fst (invIso (Bool→ (λ _ → fst C)))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (compIso
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (Σ-cong-iso-snd
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (λ c → invIso (Σ-cong-iso-fst
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (compIso idIso
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (Σ-cong-iso-fst (invIso (domIso (Bool→ (fst ∘ A)))))))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (compIso
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (Σ-cong-iso-snd (λ p
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          → Σ-cong-iso-snd λ r
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            → compIso
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (Bool→ (λ x → (a : A x .fst) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               r .fst (Iso.fun (Bool→ (λ x → A x .fst)) (RPfun Bool* A x a))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               ≡ Iso.inv (Bool→ (λ _ → fst C)) p x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (pathToIso
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (cong₂ _×_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 (λ i → (a : A true .fst)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   → r .fst ((transportRefl a i) , (A false .snd))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    ≡ fst p)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 λ i → (a : A false .fst)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   → r .fst (A true .snd , transportRefl a i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    ≡ snd p))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        AS))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   AS : Iso
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (Σ[ p ∈ fst C × fst C ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       Σ[ f ∈ (A true ×∙ A false) →∙ C ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         ((a : A true .fst) → fst f (a , A false .snd) ≡ fst p)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       × (((a : A false .fst) → fst f (A true .snd , a) ≡ snd p)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (Smash⋆ (A true) (A false) →∙ C)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst (Iso.fun AS ((c1 , c2) , (f , p) , l , r)) basel = c1
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst (Iso.fun AS ((c1 , c2) , (f , p) , l , r)) baser = c2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst (Iso.fun AS ((c1 , c2) , (f , p) , l , r)) (proj x y) = f (x , y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst (Iso.fun AS ((c1 , c2) , (f , p) , l , r)) (gluel a i) = l a i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst (Iso.fun AS ((c1 , c2) , (f , p) , l , r)) (gluer b i) = r b i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   snd (Iso.fun AS ((c1 , c2) , (f , p) , l , r)) = p
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Iso.inv AS (f , p) = (f basel , f baser)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     , ((λ x → f (proj (x .fst) (x .snd)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     , p)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     , (λ a → cong f (gluel a))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     , (λ a → cong f (gluer a))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Iso.rightInv AS (f , p) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ΣPathP ((funExt (λ { basel → refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ; baser → refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ; (proj x y) → refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ; (gluel a i) → refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ; (gluer b i) → refl})) , refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Iso.leftInv AS _ = refl


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- BiHom : (X : RP∞) (A : fst X → Pointed₀) (C : Pointed₀) → Type
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- BiHom X A C =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Σ[ f ∈ (((x : fst X) → A x .fst) → C .fst) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Σ[ r ∈ ((e : fst X ≃ Bool) (x : {!!}) (y : _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       → liftHom X A (fst C) e f {!!} {!!} ≡ {!!}) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ((e : fst X ≃ Bool)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       → {!!} ≡ {!funExt⁻ (r (compEquiv e notEquiv) (A (invEq (compEquiv e notEquiv) true) .snd)) !})

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- BiHomK : (X : RP∞) (n : fst X → ℕ) → hProp ℓ-zero
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- BiHomK = uncurry λ X → rec→Set (isSetΠ (λ _ → isSetHProp))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   (λ f n → (Σ[ g ∈ ((K∙ (n (invEq f true))) ⋀∙ (K∙ (n (invEq f false))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 →∙ K∙ (n (invEq f true)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                       + n (invEq f false)) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             , {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PushT : (A B C : Pointed₀) → Type
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PushT A B C = {!Pushout ? ?!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data ASD (X Y : RP∞) (A : fst X → fst Y → Pointed₀) : Type where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   marp : ((x : _) (y : _) → A x y .fst) → ASD X Y A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   marp' : (y : fst Y) (z : (x : fst X) → A x y .fst)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     → marp (λ x → CasesRP Y y (z x) (A x (not* Y y) .snd))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ≡ marp λ x y → A x y .snd

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- mapInto : (X Y : RP∞) (A : fst X → fst Y → Pointed₀)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → ASD X Y A  → ((y : fst Y) → ⋀∞ X (λ x → A x y)) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- mapInto X Y A (marp x) = λ y → proj λ z → x z y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- mapInto X Y A (marp' y z i) p = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   lem : (λ (z₁ : fst X) → CasesRP Y {A = λ y → A z₁ y .fst} y (z z₁) (A z₁ (not* Y y) .snd) p)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ≡ CasesRP X {!p !} {!!} {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   lem = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   (({!!} ∙ gl {X = X} {!z x!} {!!}) ∙ {!!}) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- i = i0 ⊢ proj (λ z₁ → CasesRP Y y (z z₁) (A z₁ (not* Y y) .snd) p)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- i = i1 ⊢ proj (λ z₁ → A z₁ p .snd)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- mapInto X Y A (marp x) y = proj (λ s → x s y)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   SS→' : (X Y : RP∞) (n : fst X → fst Y → ℕ)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     → SS' X Y n .fst
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     → K (∑RP Y (λ y → ∑RP X (λ x → n x y)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   SS→' X Y n (genSmash.proj x) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ⌣gen Y (λ y → ∑RP X (λ x₁ → n x₁ y)) .fst
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (proj λ y → {!⌣gen Y ?!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   SS→' X Y n (genSmash.base x) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   SS→' X Y n (genSmash.gl x a i) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {-
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     help : ⌣gen X (λ x₁ → ∑RP Y (n x₁)) .fst (proj (λ x₂ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             ⌣gen Y (n x₂) .fst
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (CasesRP X x a (proj (λ x₃ → K∙ (n (not* X x) x₃) .snd)) x₂)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          ≡ 0ₖ (∑RP X (λ x₁ → ∑RP Y (n x₁)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     help = cong (⌣gen X (λ x₁ → ∑RP Y (n x₁)) .fst)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               {!genSmash.gl x a !}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ∙ {!a!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       lem : (z : _) → CasesRP X {A = λ x → ⋀∞ Y (λ X₁ → K∙ (n x X₁))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                x a (proj (λ x₃ → K∙ (n (not* X x) x₃) .snd)) z
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             ≡ proj (CasesRP Y {!!} {!!} {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       lem z = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   doublerMash : {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   doublerMash = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ⌣gen : {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ⌣gen = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- myP : {!{ℓ : Level} (A : Bool → Pointed ℓ) → Iso (genSmash.⋀∞ !}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- myP = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ⋀∞Bool : Iso (⋀∞ Bool* A) (Smash (A true) (A false))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Iso.fun ⋀∞Bool = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Iso.inv ⋀∞Bool = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Iso.rightInv ⋀∞Bool = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Iso.leftInv ⋀∞Bool = {!!}

