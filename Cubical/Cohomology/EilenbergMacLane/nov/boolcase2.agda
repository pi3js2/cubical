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


open import Cubical.Cohomology.EilenbergMacLane.nov.base
open import Cubical.Cohomology.EilenbergMacLane.nov.boolcase

module Cubical.Cohomology.EilenbergMacLane.nov.boolcase2 where
open import Cubical.HITs.Join
open import Cubical.Functions.FunExtEquiv

BaseF : ∀ {ℓ} (I : RP∞' ℓ)
  (i : fst I) (J : RP∞' ℓ)
  (A : fst I → fst J → Type ℓ)
  → (j : fst J) (a : A i j) (q : (j : fst J) → A (RP'.notI I i) j)
  → (j' : fst J)
  → joinR-gen (fst I) λ i → A i j'
BaseF I i J A j a q = RP'.elimI J j (inrR (RP'.elimI I i a (q j))) (inlR (RP'.notI I i , q (RP'.notI J j)))

GOALTY : ∀ {ℓ} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) → Type ℓ
GOALTY I J A = joinR-gen (fst J) λ j → joinR-gen (fst I) λ i → A i j

CasesBoolId : ∀ {ℓ} {A : Bool → Type ℓ} {f g : (x : Bool) → A x}
  → f true ≡ g true
  → f false ≡ g false 
  → f ≡ g
CasesBoolId p q = funExt (CasesBool true p q)

CasesBoolη' : ∀ {ℓ} {A : Bool → Type ℓ} (f : (x : Bool) → A x)
  → CasesBool true (f true) (f false) ≡ f
CasesBoolη' f = CasesBoolId refl refl



module _ {ℓ : Level} where
  pre-inler : (A : Bool → Bool → Type ℓ) (a : A true true)
        (b : TotΠ (A false))
      → (i : Bool) → joinR-gen (fst (RP∞'· ℓ)) (λ i₁ → A i₁ i)
  pre-inler A a b = CasesBool true (inrR (CasesBool true a (b true))) (inlR (false , b false))

  inler : (A : Bool → Bool → Type ℓ) (a : A true true)
        (b : TotΠ (A false)) →
        GOALTY (RP∞'· ℓ) (RP∞'· ℓ) A
  inler A a b = inrR (pre-inler A a b)

  inrerr : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
           (t : (i : fst I) (j : fst J) → A i j) → GOALTY I J A
  inrerr I J A t = inrR λ j → inrR λ i → t i j

  inr-inl-inl : (I : RP∞' ℓ) (A : fst I → Bool → Type ℓ)
    (f : (x : fst I) → A x true)
    → Σ[ x ∈ GOALTY I (RP∞'· ℓ) A ]
        ((p : (i : fst I) (j : Bool) → A i j)
         (q : (i : fst I) → p i true ≡ f i)
        → x ≡ inrerr I (RP∞'· ℓ) A p)
  fst (inr-inl-inl I A f) = inlR (true , inrR f)
  snd (inr-inl-inl I A f) p q =
    push* (true , inrR f) (λ i → inrR λ j → p j i) (cong inrR (funExt q))

  inr-inl-inr : (I : RP∞' ℓ) (A : fst I → fst I → Type ℓ)
    (f : (x : fst I) → A x x)
    → Σ[ x ∈ GOALTY I I A ]
        ((p : (i j : fst I) → A i j)
         (q : (i : fst I) → p i i ≡ f i)
        → x ≡ inrerr I I A p)
  fst (inr-inl-inr I A f) = inrR λ i → inlR (i , (f i))
  snd (inr-inl-inr I A f) p q k = inrR (λ i → push* (i , f i) (λ j → p j i) (q i) k)

  push-inl : (A : Bool → Bool → Type ℓ)
      (f : (i : fst (RP∞'· ℓ)) → A i true)
      (g : (j : Bool) → A false j)
      (p : g true ≡ f false) →
      inler A (f true) g ≡ inlR (true , inrR f)
  push-inl A f g p =
    sym (push* (true , inrR f)
        (CasesBool true (inrR (CasesBool true (f true) (g true))) (inlR (false , g false)))
        (cong inrR (CasesBoolId refl p)))


  push-inr : (A : Bool → Bool → Type ℓ) (g : (i : fst (RP∞'· ℓ)) → A i i)
      (p : (j : Bool) → A false j) (q : p false ≡ g false) →
      inler A (g true) p ≡ inrR (λ i → inlR (i , g i))
  push-inr A g p q =
    cong inrR
    (CasesBoolId (sym (push* (true , g true) (CasesBool true (g true) (p true)) refl))
                 λ i → inlR (false , q i))

  
  pre-inler-id : (A : Bool → Bool → Type ℓ) (g : (i j : Bool) → A i j)
    → pre-inler A (g true true) (g false) ≡ (λ j → inrR (λ i → g i j))
  pre-inler-id A g =
    funExt (CasesBool true
      (cong inrR (CasesBoolη' λ x → g x true))
      (push* (false , g false false) (λ i → g i false) refl))

  pre-inler-id2 :  (A : Bool → Bool → Type ℓ) (g : (i : Bool) → A i i)
      (f : TotΠ (A false)) (p : f false ≡ g false) 
    → pre-inler A (g true) f ≡ (λ i → inlR (i , g i))
  pre-inler-id2 A g f p =
    CasesBoolId (sym (push* (true , g true) (CasesBool true (g true) (f true)) refl))
                λ i → inlR (false , p i) 

  coh-inr : (A : Bool → Bool → Type ℓ) (g : (i j : Bool) → A i j)
     → inler A (g true true) (g false) ≡ inrerr (RP∞'· ℓ) (RP∞'· ℓ) A g
  coh-inr A g = cong inrR (pre-inler-id A g)

  coh-eq1 : (A : Bool → Bool → Type ℓ) (g : (i : Bool) → A i i)
      (f : TotΠ (A false)) (p : f false ≡ g false) →
      inler A (g true) f ≡ inrR (λ i → inlR (i , g i))
  coh-eq1 A g f p = cong inrR (pre-inler-id2 A g f p)

  coh-eq2-coh : (A : Bool → Bool → Type ℓ) (g : (i j : Bool) → A i j) (i : Bool)
    → Square (λ j → pre-inler A (g true true) (g false) i)
              (push* (i , g i i) (λ x → g x i) refl)
              (λ j → pre-inler-id2 A (λ i₁ → g i₁ i₁) (g false) refl j i)
              (λ j → pre-inler-id A g j i)
  coh-eq2-coh A g false i j = push* (false , g false false) (λ i₁ → g i₁ false) refl (i ∧ j)
  coh-eq2-coh A g true i j =
    hcomp (λ k → λ {(i = i0) → inrR (CasesBoolη' (λ x → g x true) (~ k))
                   ; (i = i1) → push* (true , g true true) (λ x → g x true) (λ _ → g true true) j
                   ; (j = i0) → push* (true , g true true) (CasesBoolη' (λ x → g x true) (~ k)) (λ _ → g true true) (~ i)
                   ; (j = i1) → inrR (CasesBoolη' (λ x → g x true) (i ∨ ~ k))})
          (push* (true , g true true) (λ x → g x true) refl (j ∨ ~ i))

  coh-eq2 : (A : Bool → Bool → Type ℓ) (g : (i j : Bool) → A i j)
     → Square (coh-eq1 A (λ i → g i i) (g false) refl)
               (coh-inr A g)
               (λ _ → inler A (g true true) (g false))
               (inr-inl-inr (RP∞'· ℓ) A (λ i → g i i) .snd g (λ _ → refl))
  coh-eq2 A g i j = inrR (λ x → coh-eq2-coh A g x j i)

  coh-eq-l-coh : (A : Bool → Bool → Type ℓ) (g : (i j : Bool) → A i j) (i : Bool)
    → Path (joinR-gen Bool (λ i₂ → A i₂ i))
            (inrR (λ i₂ → g i₂ i))
            (pre-inler A (g true true) (g false) i)
  coh-eq-l-coh A g =
    CasesBool true (cong inrR (sym (CasesBoolη' (λ i → g i true))))
                   (sym (push* (false , g false false) (λ i → g i false) refl))


  coh-eq-l-coh-coh : (A : Bool → Bool → Type ℓ) (g : (i j : Bool) → A i j) (i : Bool)
    → Square refl (funExt⁻ (pre-inler-id A g) i) (coh-eq-l-coh A g i) refl
  coh-eq-l-coh-coh A g false i j =
    push* (false , g false false) (λ i₂ → g i₂ false)
         (λ _ → g false false) (~ i ∨ j)
  coh-eq-l-coh-coh A g true i j =
    inrR (CasesBoolη' (λ i₁ → g i₁ true) (~ i ∨ j))

  coh-eq-l :
    (A : Bool → Bool → Type ℓ) (g : (i j : Bool) → A i j) →
      Square
      (push-inl A (λ i₁ → g i₁ true) (g false) (λ _ → g false true))
      (coh-inr A g)
      (λ _ → inler A (g true true) (g false))
      (inr-inl-inl (RP∞'· ℓ) A (λ i → g i true) .snd g (λ z → refl))
  coh-eq-l A g i j =
    hcomp (λ k → λ {(i = i0) → push* (true , inrR (λ i₁ → g i₁ true)) (λ x → coh-eq-l-coh A g x k)
                                       (λ s → inrR (CasesBoolη' (λ i₁ → g i₁ true) (~ k ∨ s))) (~ j)
                   ; (i = i1) → inrR λ i → coh-eq-l-coh-coh A g i k j
                   ; (j = i0) → inrR λ i₁ → coh-eq-l-coh A g i₁ k
                   ; (j = i1) → push* (true , inrR (λ i₁ → g i₁ true))
                                       (λ j₁ → inrR (λ i₁ → g i₁ j₁))
                                       refl i})
          ((push* (true , inrR (λ i₁ → g i₁ true))
                 (λ j₁ → inrR (λ i₁ → g i₁ j₁))
                 refl (i ∨ ~ j) ))

  module M = MEGA {ℓ = ℓ} {Targ = λ I J A _ → GOALTY I J A}
    inler
    inrerr
    inr-inl-inl
    inr-inl-inr
    push-inl
    push-inr
    coh-inr
    coh-eq1
    coh-eq2
    coh-eq-l

  open M

  G : (I₁ J₁ : RP∞' ℓ) (A : fst I₁ → fst J₁ → Type ℓ)
      (x : ΠR-extend** I₁ J₁ A) →
      fst I₁ → GOALTY I₁ J₁ A
  G I J A x i = btm-map I J A (i , leftMap** I J A i x)

  GB : (A : Bool → Bool → Type ℓ)
    → ΠR-extend** (RP∞'· ℓ) (RP∞'· ℓ) A
    → Bool → GOALTY (RP∞'· ℓ) (RP∞'· ℓ) A
  GB A x i = btm-map (RP∞'· ℓ) (RP∞'· ℓ) A (i , leftMapBool (RP∞'· ℓ) A i x)

  G≡ : (A : Bool → Bool → Type ℓ) (x : _) (i : _)
    → G (RP∞'· ℓ) (RP∞'· ℓ) A x i ≡ GB A x i
  G≡ A x i k = btm-map (RP∞'· ℓ) (RP∞'· ℓ) A (i , leftMapBool≡ (RP∞'· ℓ) A i x (~ k))

--
  module _ (A : Bool → Bool → Type ℓ) (a : A true true) (b : TotΠ (A false)) where
    pre-inler-true : pre-inler A a b true ≡ inlR (true , a)
    pre-inler-true = sym (push* (true , a) (CasesBool true a (b true)) refl)

    G-inlerₗ : (λ j → inlR (false , b j)) ≡ pre-inler A a b
    G-inlerₗ = CasesBoolId (push* (false , b true) (CasesBool true a (b true)) refl)
                   refl

    G-inler : (i : Bool) →
        G (RP∞'· ℓ) (RP∞'· ℓ) A (inl (true , (true , a) , b)) i ≡
        inler A a b
    G-inler false = cong inrR G-inlerₗ
    G-inler true =
      push* (true , inlR (true , a))
            (pre-inler A a b)
            pre-inler-true

  G-inrer : (I₁ J₁ : RP∞' ℓ) (A : fst I₁ → fst J₁ → Type ℓ)
      (t : (i : fst I₁) (j : fst J₁) → A i j) (i : fst I₁) →
      G I₁ J₁ A (inr (inr t)) i ≡ inrerr I₁ J₁ A t
  G-inrer I J A t k i = inrR λ j → push* (k , t k j) (λ i → t i j) refl i


  G-inr-inl-inl₁ : (I₁ : RP∞' ℓ) (A : fst I₁ → Bool → Type ℓ)
      (f : (x : fst I₁) → A x true) (i : fst I₁) →
      G I₁ (RP∞'· ℓ) A (inr (inl (inl true , f))) i ≡
      inlR (true , inrR f)
  G-inr-inl-inl₁ I A f i k = inlR (true , push* (i , f i) f refl k)

  G-inr-inl-inl₂ :
    (I : RP∞' ℓ) (A : fst I → Bool → Type ℓ)
      (f : (x : fst I) → A x true) (i : fst I)
      (p : (i₁ : fst I) (j : Bool) → A i₁ j)
      (q : (x : fst I) → p x true ≡ f x)
     → Square
      (λ k → G I (RP∞'· ℓ) A (inr (push ((inl true , f) , p , q) k)) i)
      (push* (true , inrR f) (λ j → inrR (λ i₁ → p i₁ j))
       (λ i₁ → inrR (funExt q i₁)))
      (G-inr-inl-inl₁ I A f i) (G-inrer I (RP∞'· ℓ) A p i)
  G-inr-inl-inl₂ I A f i p q i' j =
    push* (true , push* (i , f i) f refl i')
          (λ t → push* (i , p i t) (λ i₁ → p i₁ t) refl i')
          (λ s → push* (i , q i s) (λ i₁ → q i₁ s) refl i') j


  G-inr-inl-inr₁ : (I₁ : RP∞' ℓ) (A : fst I₁ → fst I₁ → Type ℓ)
      (f : (i : fst I₁) → A i i) (i : fst I₁)
      → G I₁ I₁ A (inr (inl (inr (idEquiv (fst I₁)) , f))) i
      ≡ inrR (λ i₁ → inlR (i₁ , f i₁))
  G-inr-inl-inr₁ I A f i = push* (i , inlR (i , f i)) (λ i₁ → inlR (i₁ , f i₁)) refl


  G-inr-inl-inr₂-refl : (I₁ : RP∞' ℓ) (A : fst I₁ → fst I₁ → Type ℓ)
      (p : (i₁ j : fst I₁) → A i₁ j)
      (i : fst I₁) →
      Square
        (λ k → G I₁ I₁ A (inr (push ((inr (idEquiv (fst I₁)) , λ i → p i i) , p , λ _ → refl) k)) i)
        (λ k → inrR (λ i₁ → push* (i₁ , p i₁ i₁) (λ j → p j i₁) refl k))
        (G-inr-inl-inr₁ I₁ A (λ k → p k k) i)
        (G-inrer I₁ I₁ A p i)
  G-inr-inl-inr₂-refl I A p i' i j =
    hcomp (λ r → λ {(i = i0) → push* (i' , inlR (i' , p i' i'))
                                        (λ i → push* (i' , p i' i) (λ t → p t i) refl (~ r))
                                        (λ t → push* (i' , p i' i') (λ t → p t i') refl (~ r ∧ ~ t)) j
                   ; (i = i1) → inrR (λ v → push* (v , p v v) (λ a → p a v) (λ _ → p v v) (~ r ∨ j))
                   ; (j = i0) → push* (i' , inlR (i' , p i' i'))
                                       (λ x → push* (x , p x x) (λ a → p a x) refl (~ r))
                                       (λ j → push* (i' , p i' i') (λ a → p a i') refl (~ r ∧ ~ j)) i
                   ; (j = i1) → inrR (λ v → push* (i' , p i' v) (λ t → p t v) (λ _ → p i' v) (~ r ∨ i))})
           (push* (i' , inlR (i' , p i' i'))
             (λ v → inrR (λ a → p a v))
             (sym (push* (i' , p i' i') (λ a → p a i') refl))
             (i ∨ j))

  G-inr-inl-inr₂ : (I₁ : RP∞' ℓ) (A : fst I₁ → fst I₁ → Type ℓ)
       (p : (i₁ j : fst I₁) → A i₁ j)
       (f : (i : fst I₁) → A i i)
      (q : (λ x → p x x) ≡ f) (i : fst I₁) →
      Square
        (λ k → G I₁ I₁ A (inr (push ((inr (idEquiv (fst I₁)) , f) , p , (funExt⁻ q)) k)) i)
        (λ k → inrR (λ i₁ → push* (i₁ , f i₁) (λ j → p j i₁) (funExt⁻ q i₁) k))
        (G-inr-inl-inr₁ I₁ A f i)
        (G-inrer I₁ I₁ A p i)
  G-inr-inl-inr₂ I A p = J> G-inr-inl-inr₂-refl I A p

  G-push-inl : (A : Bool → Bool → Type ℓ)
      (f : (i : fst (RP∞'· ℓ)) → A i true) (g : (j : Bool) → A false j)
      (p : g true ≡ f false) (i : Bool) →
      Square
        (λ k → GB A (push (true , true , inl (inl (f , g , p))) k) i)
        (push-inl A f g p)
        (G-inler A (f true) g i)
        (G-inr-inl-inl₁ (RP∞'· ℓ) A f i)
  G-push-inl A f g p false i j =
    push* (true , push* (false , f false) f refl i)
      (λ x → help x i j)
      (λ k → push* (false , p k) (CasesBoolId {f = CasesBool true (f true) (g true)} {g = f} refl p k) refl i) (~ j)
      where
      help : (x : Bool)
        → Square (λ _ → inlR (false , g x))
                  refl
                  (λ i → G-inlerₗ A (f true) g i x)
                  ((funExt⁻ (CasesBoolId {f = λ x → inlR (false , g x)} {g = pre-inler A (f true) g}
                    (push* (false , g true) (CasesBool true (f true) (g true)) refl) refl) x))
      help false = refl
      help true i j = push* (false , g true) (CasesBool true (f true) (g true)) refl i
  G-push-inl A f g p true i j = {!!}
  


  module GG = ID G
     G-inler
     G-inrer
     G-inr-inl-inl₁
     G-inr-inl-inl₂
     G-inr-inl-inr₁
     (λ A g x p q → G-inr-inl-inr₂ A g p x (funExt q))
     (λ A f g p i → (λ r k → G≡ A (push (true , true , inl (inl (f , g , p))) k) i r)
                   ◁ G-push-inl A f g p i)
     (λ A g p q i → {!!})
     {!!}
     {!!}
     {!!}
     {!!}

  open GG
  module _ (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) where
    Better→ : Better! I J A → GOALTY I J A
    Better→ (inl x) = btm-map I J A x
    Better→ (inr x) = ΠR-extend→ I J A x
    Better→ (push a i) = GID I (fst a) J A (snd a) i

-- left : ∀ {ℓ} (I J : RP∞' ℓ) (i : fst I) (A : fst I → fst J → Type ℓ)
--      → joinR-gen (fst J) (A i)
--      → joinR-gen (fst J) λ j → joinR-gen (fst I) λ i → A i j
-- left I J i A (inlR x) = inlR (fst x , inlR (i , snd x))
-- left I J i A (inrR x) = inrR λ j → inlR (i , x j)
-- left I J i A (push* a b x i₁) =
--   push* (fst a , inlR (i , snd a))
--         (λ k → inlR (i , b k))
--         (λ j → inlR (i , x j)) i₁

-- GOALTY : ∀ {ℓ} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) → Type ℓ
-- GOALTY I J A = joinR-gen (fst J) λ j → joinR-gen (fst I) λ i → A i j

-- eqr-ty : ∀ {ℓ} (I J : RP∞' ℓ) (e : fst I ≃ fst J)
--   (A : fst I → fst J → Type ℓ) → Type ℓ
-- eqr-ty I J e A = 
--    Σ[ f1 ∈ ((j : fst J) (f : (i : fst I) → A i (fst e i)) → A (invEq e j) j) ]
--        Σ[ f2 ∈ ((j : fst J) (f : (i : fst I) → A i (fst e i))
--                (p : (i : fst I) (j : fst J) → A i j) (q : (x : fst I) → p x (fst e x) ≡ f x)
--             → Path (joinR-gen (fst I) (λ i₁ → A i₁ j))
--                 (inlR (invEq e j , f1 j f)) (inrR λ i₁ → p i₁ j) ) ]
--           Σ[ f3 ∈ ((i : fst I) (f : (i : fst I) → A i (fst e i))
--                   (p : (j : fst J) → A (RP'.notI I i) j)
--                   (q : p (fst e (RP'.notI I i)) ≡ f (RP'.notI I i))
--             → Path (joinR-gen (fst J) λ j → joinR-gen (fst I) (λ i → A i j))
--                     (inrR (BaseF I i J A (fst e i) (f i) p))
--                     (inrR λ j → inlR (invEq e j , f1 j f))) ] Unit

-- eqr-b↓ : ∀ {ℓ} (A : Bool → Bool → Type ℓ)
--          (p : (j : Bool) → A false j)
--          (f : (i : Bool) → A i i)
--          (q : p false ≡ f false)
--   → Path (joinR-gen Bool (λ j → joinR-gen Bool (λ i₁ → A i₁ j)))
--           (inrR (BaseF (RP∞'· ℓ) true (RP∞'· ℓ) A true (f true) p))
--           (inrR (λ j → inlR ( j , f j)))
-- eqr-b↓ A p f q =
--   cong inrR (funExt
--     (CasesBool true (sym (push* (true , f true)
--     (CasesBool true (f true) (p true)) refl))
--     λ i → inlR (false , q i)))

-- abstract
--   eqr-b₃ : ∀ {ℓ} (I : RP∞' ℓ) (i : fst I) (A : fst I → fst I → Type ℓ)
--            (p : (j : fst I) → A (RP'.notI I i) j)
--            (f : (i : fst I) → A i i)
--            (q : p (RP'.notI I i) ≡ f (RP'.notI I i))
--     → Path
--         (joinR-gen (fst I) (λ j → joinR-gen (fst I) (λ i₁ → A i₁ j)))
--         (inrR (BaseF I i I A (idfun (fst I) i) (f i) p))
--         (inrR (λ j → inlR (invEq (idEquiv (fst I)) j , f j)))
--   eqr-b₃ = JRP∞' eqr-b↓

--   eqr-b₃∙ : ∀ {ℓ} (A : Bool → Bool → Type ℓ)
--            (p : (j : Bool) → A false j)
--            (f : (i : Bool) → A i i)
--            (q : p false ≡ f false)
--            → eqr-b₃ (RP∞'· ℓ) true A p f q ≡ eqr-b↓ A p f q
--   eqr-b₃∙ {ℓ = ℓ} A p f q i = help i A p f q
--     where
--     help : eqr-b₃ (RP∞'· ℓ) true ≡ eqr-b↓
--     help = JRP∞'∙ eqr-b↓


-- eqr-b : ∀ {ℓ} (I : RP∞' ℓ) (A : fst I → fst I → Type ℓ)
--   → eqr-ty I I (idEquiv (fst I)) A
-- fst (eqr-b I A) j f = f j
-- fst (snd (eqr-b I A)) j f p q = push* (j , f j) (λ i → p i j) (q j)
-- fst (snd (snd (eqr-b I A))) i f p q = eqr-b₃ I i A  p f q
-- snd (snd (snd (eqr-b I A))) = tt

-- abstract
--   eqr : ∀ {ℓ} (I J : RP∞' ℓ) (e : fst I ≃ fst J)
--     (A : fst I → fst J → Type ℓ)
--     → eqr-ty I J e A
--   eqr I = JRP∞'' I (eqr-b I)

--   eqr≡ : ∀ {ℓ} (I : RP∞' ℓ)
--     (A : fst I → fst I → Type ℓ)
--     → eqr I I (idEquiv _) A ≡ eqr-b I A
--   eqr≡ I = funExt⁻ (JRP∞''-refl I (eqr-b I))

-- ΠR-extend→ᵣ : ∀ {ℓ} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
--   → ΠR-base-ab* I J A
--   → joinR-gen (fst J) λ j → joinR-gen (fst I) λ i → A i j
-- ΠR-extend→ᵣ I J A (inl (inl x , f)) = inlR (x , inrR f)
-- ΠR-extend→ᵣ I J A (inl (inr x , f)) = inrR λ j → inlR (invEq x j , eqr I J x A .fst j f )
-- ΠR-extend→ᵣ I J A (inr x) = inrR λ j → inrR λ i → x i j
-- ΠR-extend→ᵣ I J A (push ((inl x , f) , p , q) i) =
--   push* (x , inrR f) (λ j → inrR λ k → p k j) (cong inrR (funExt q)) i
-- ΠR-extend→ᵣ I J A (push ((inr x , f) , p , q) i) =
--   inrR (λ j → eqr I J x A .snd .fst j f p q i)

-- main-inr-base∙ :  ∀ {ℓ} (A : Bool → Bool → Type ℓ)
--   (f : (i j : Bool) → A i j)
--   → Square refl
--             (λ i → inrR (λ j → eqr (RP∞'· ℓ) (RP∞'· ℓ) (idEquiv Bool) A .snd .fst j (λ i → f i i) f (λ _ → refl) i))
--             (eqr (RP∞'· _) (RP∞'· ℓ) (idEquiv Bool) A .snd .snd .fst true (λ i → f i i) (f false) refl)
--             (ΠR-extend→ₘb-inr (RP∞'· ℓ) true A (f true true) f refl)
-- main-inr-base∙ {ℓ = ℓ} A f i j =
--   hcomp (λ k → λ {(i = i0) → inrR (BaseF (RP∞'· ℓ) true (RP∞'· ℓ) A
--                                     true (f true true) (f false))
--                  ; (i = i1) → inrR (λ j' → eqr≡ (RP∞'· ℓ) A (~ k) .snd .fst j' (λ i → f i i) f (λ _ → refl) j)
--                  ; (j = i0) → eqr≡ (RP∞'· ℓ) A (~ k) .snd .snd .fst true (λ i → f i i) (f false) refl i
--                  ; (j = i1) → ΠR-extend→ₘb∙ A (f true true) f refl (~ k) i})
--     (hcomp (λ k → λ {(i = i0) → inrR (BaseF (RP∞'· ℓ) true (RP∞'· ℓ) A true (f true true) (f false))
--                     ; (i = i1) → inrR (λ j' → push* (j' , f j' j') (λ i₁ → f i₁ j') refl j) 
--                     ; (j = i0) → eqr-b₃∙ A (f false) (λ i → f i i) refl (~ k) i
--                     ; (j = i1) → ΠR-extend→ₘb-inrBool A (f true true) f refl i})
--               (inrR (help i j)))
--       where
--       sqₗ-lem : Path ((x : Bool) → A x true) (λ j → f j true) (CasesBool true (f true true) (f false true))
--       sqₗ-lem = funExt (CasesBool true refl refl)

--       sqₗ-lem-coh : Square sqₗ-lem (λ _ i → f i true )
--                            refl
--                            (funExt (CasesBool true refl refl))
--       sqₗ-lem-coh = funExtSq (CasesBool true (λ _ _ → f true true) λ _ _ → f false true)


--       sqₗ : Square {A = (joinR-gen Bool (λ x → A x true))}
--                    (λ _ → inrR (CasesBool true (f true true) (f false true)))
--                    (push* (true , f true true) (λ j → f j true) refl)
--                    (sym (push* (true , f true true) (CasesBool true (f true true) (f false true)) refl))
--                    (cong inrR (funExt (CasesBool true refl refl)))
--       sqₗ i j = 
--         hcomp (λ k → λ {(i = i0) → inrR (sqₗ-lem k)
--                       ; (i = i1) → push* (true , f true true) (sqₗ-lem i0) refl j
--                       ; (j = i0) → push* (true , f true true) (sqₗ-lem k) refl (~ i)
--                       ; (j = i1) → inrR (sqₗ-lem-coh i k)})
--                 (push* (true , f true true) (λ j₂ → f j₂ true) refl (j ∨ ~ i))

--       help : Square {A = ((y : Bool) → joinR-gen Bool (λ x → A x y))}
--                     (λ _ → CasesBool true (inrR (CasesBool true (f true true) (f false true))) (inlR (false , f false false)))
--                     (λ j i₁ → push* (i₁ , f i₁ i₁) (λ i₂ → f i₂ i₁) refl j)
--                     (funExt (CasesBool true (sym (push* (true , f true true) (CasesBool true (f true true) (f false true)) refl))
--                             (λ j → inlR (false , f false false))))
--                     (funExt (CasesBool true
--                               (cong inrR (funExt (CasesBool true refl refl)))
--                               (push* (false , f false false) (λ j → f j false) refl)))
--       help = funExtSq (CasesBool true
--         sqₗ
--         λ i j → push* (false , f false false) (λ i₂ → f i₂ false) refl (i ∧ j))

-- main-inr-base :  ∀ {ℓ} (A : Bool → Bool → Type ℓ)
--   (f : (i j : Bool) → A i j)
--   (p : (i : Bool) → A i i)
--   (q : (λ i → f i i) ≡ p)
--   → Square refl
--             (λ i → inrR (λ j → eqr (RP∞'· ℓ) (RP∞'· ℓ) (idEquiv Bool) A .snd .fst j p f (funExt⁻ q) i))
--             (eqr (RP∞'· _) (RP∞'· ℓ) (idEquiv Bool) A .snd .snd .fst true p (f false) (funExt⁻ q false))
--             (ΠR-extend→ₘb-inr (RP∞'· ℓ) true A (p true) f (funExt⁻ q true))
-- main-inr-base {ℓ = ℓ} A f =
--   J> main-inr-base∙ A f

-- main-inr :  ∀ {ℓ} (J : RP∞' ℓ) (e : Bool ≃ fst J)
--   (A : Bool → fst J → Type ℓ)
--   (p : (i : Bool) → A i (fst e i))
--   (f : (i : Bool) (j : fst J) → A i j)
--   (q : (i : Bool) → f i (fst e i) ≡ p i)
--   → Square refl
--             (λ i → inrR (λ j → eqr (RP∞'· _) J e A .snd .fst j p f q i))
--             (eqr (RP∞'· _) J e A .snd .snd .fst true p (f false) (q false))
--             (ΠR-extend→ₘb-inr J (e .fst true) A (p true) f (q true))
-- main-inr  = JRP∞'' (RP∞'· _) (λ A f p q → main-inr-base A p f (funExt q))

-- inl-lem-ty : ∀ {ℓ} (J : RP∞' ℓ) (j : fst J) (A : Bool → fst J → Type ℓ)
--   → Type ℓ
-- inl-lem-ty {ℓ} J j A = Σ[ r ∈ ((f : (x : Bool) → A x j) (p : (j : fst J) → A false j) (q : p j ≡ f false)
--      → Path (joinR-gen (fst J) (λ j₁ → joinR-gen Bool (λ i → A i j₁)))
--              (inrR (BaseF (RP∞'· ℓ) true J A j (f true) p))  (inlR (j , inrR f))) ]
--      ((p : (i₁ : Bool) (j₁ : fst J) → A i₁ j₁) (f : (x : Bool) → A x j) (q : (λ x → p x j) ≡ f)
--      → Square (r f (p false) (funExt⁻ q false)) (ΠR-extend→ₘb-inr J j A (f true) p  (funExt⁻ q true))
--          refl
--          (push* (j , inrR f) (λ j₁ → inrR (λ k → p k j₁))
--                 (cong inrR q)))

-- inl-lem∙ : ∀ {ℓ} (A : Bool → Bool → Type ℓ) → inl-lem-ty (RP∞'· ℓ) true A 
-- fst (inl-lem∙ A) f p q =
--   sym (push* (true , (inrR f))
--              (CasesBool true (inrR (CasesBool true (f true) (p true)))
--                              (inlR (false , p false)))
--              (cong inrR (funExt (CasesBool true refl q))))
-- snd (inl-lem∙ A) p = J> {!!}

-- inl-lem : ∀ {ℓ} (J : RP∞' ℓ) (j : fst J) (A : Bool → fst J → Type ℓ)
--   → inl-lem-ty J j A
-- inl-lem = JRP∞' inl-lem∙

-- ΠR-extend→ₘb : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
--   (x : _)
--   → inrR (BaseF (RP∞'· ℓ) true J A
--          (PushTop→left-push'-ab* (RP∞'· ℓ) J A true x .fst .fst)
--          (PushTop→left-push'-ab* (RP∞'· ℓ) J A true x .fst .snd)
--          (PushTop→left-push'-ab* (RP∞'· ℓ) J A true x .snd))
--     ≡ ΠR-extend→ᵣ (RP∞'· ℓ) J A (PushTop→ΠR-base-ab* (RP∞'· ℓ) J A true x)
-- ΠR-extend→ₘb J A (inl ((inl j , f) , p , q)) = inl-lem J j A .fst f p q
-- ΠR-extend→ₘb J A (inl ((inr e , p) , f , q)) = eqr (RP∞'· _) J e A .snd .snd .fst true p f q
-- ΠR-extend→ₘb J A (inr ((j , a) , b , q)) = ΠR-extend→ₘb-inr J j A a b q
-- ΠR-extend→ₘb J A (push ((inl j , f) , p , q) i) = inl-lem J j A .snd p f (funExt q) i
-- ΠR-extend→ₘb J A (push ((inr e , p) , f , q) i) j = main-inr J e A p f q j i

-- ΠR-extend→ₘ : ∀ {ℓ} (I : RP∞' ℓ) (i : fst I) (J : RP∞' ℓ)
--   (A : fst I → fst J → Type ℓ)
--   (x : _)
--   → inrR (BaseF I i J A
--          (PushTop→left-push'-ab* I J A i x .fst .fst)
--          (PushTop→left-push'-ab* I J A i x .fst .snd)
--          (PushTop→left-push'-ab* I J A i x .snd))
--     ≡ ΠR-extend→ᵣ I J A (PushTop→ΠR-base-ab* I J A i x)
-- ΠR-extend→ₘ = JRP∞' ΠR-extend→ₘb

-- ΠR-extend→ₘ≡ : ∀ {ℓ} (J : RP∞' ℓ)
--   (A : Bool → fst J → Type ℓ)
--   (x : _)
--   → ΠR-extend→ₘ (RP∞'· ℓ) true J A x ≡ ΠR-extend→ₘb J A x
-- ΠR-extend→ₘ≡ {ℓ = ℓ} J A x i = help i J A x
--   where
--   help : ΠR-extend→ₘ (RP∞'· ℓ) true ≡ ΠR-extend→ₘb
--   help = JRP∞'∙ ΠR-extend→ₘb

-- ΠR-extend→ : ∀ {ℓ} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
--   → ΠR-extend* I J A
--   → joinR-gen (fst J) λ j → joinR-gen (fst I) λ i → A i j
-- ΠR-extend→ I J A (inl (i , f , p)) = inrR (BaseF I i J A (fst f) (snd f) p)
-- ΠR-extend→ I J A (inr x) = ΠR-extend→ᵣ I J A x
-- ΠR-extend→ I J A (push (i , a) k) = ΠR-extend→ₘ I i J A a k

-- bahaₗ : ∀ {ℓ} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
--   → (i : fst I)
--   → (x : _)
--   → left I J i A (leftFun'-inl I (fst J) A (fst x) (fst (snd x)) (snd (snd x)) i)
--    ≡ ΠR-extend→ I J A (inl x)
-- bahaₗ = {!!}

-- baha : ∀ {ℓ} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
--   → (i : fst I)
--   → (x : ΠR-extend* I J A)
--   → left I J i A (leftFun*-full I J A i x) ≡ ΠR-extend→ I J A x
-- baha I J A i (inl (i' , p , q)) = {!leftFun'-inl I (fst J) A (fst x) (fst (snd x)) (snd (snd x)) i!}
-- baha I J A i (inr x) = {!!}
-- baha I J A i (push a i₁) = {!!}

-- -- ΠR-extend→ : ∀ {ℓ} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
-- --   → ΠR-extend* I J A
-- --   → joinR-gen (fst J) λ j → joinR-gen (fst I) λ i → A i j
-- -- ΠR-extend→ I J A (inl (i , ((j , a) , q))) = inrR (BaseF I i J A j a q)
-- -- ΠR-extend→ I J A (inr x) = ΠR-extend→ᵣ I J A x
-- -- ΠR-extend→ I J A (push (i' , a) i) = {!!}
-- -- -- ΠR-extend→ I J A (push (i' , inl ((inl j , f) , p , q)) i) = {!!}
-- -- -- ΠR-extend→ I J A (push (i' , inl ((inr e , f) , p , q)) i) = {!!}
-- -- -- ΠR-extend→ I J A (push (i' , inr ((j , a) , f , q)) i) = {!!}
-- -- -- ΠR-extend→ I J A (push (i' , push ((inl x , f) , p , q) i₁) i) = {!!}
-- -- -- ΠR-extend→ I J A (push (i' , push ((inr x , f) , p , q) i₁) i) = {!!}



-- -- -- --   push-inl-inl-coh : (j : fst J) (i' i : fst I)
-- -- -- --     (p : (i : fst I) → A i j) (f : (x : fst J) → A (RP'.notI I i') x)
-- -- -- --     → f j ≡ p (I .snd .fst .fst i')
-- -- -- --     → inler-g j i' i (p i') f ≡ inlR (j , p i)
-- -- -- --   push-inl-inl-coh j i' =
-- -- -- --     RP'.elimI I i' (λ p f q → inler-g-id j i' (p i') f .fst)
-- -- -- --                    λ p f q → inler-g-id j i' (p i') f .snd
-- -- -- --                             ∙ sym (push* (j , p (RP'.notI I i')) f q)

-- -- -- -- {-
-- -- -- --   push-inl-inr-coh : (e : fst I ≃ fst J) (i' i : fst I)
-- -- -- --     (p : (i : fst I) → A i j) (f : (x : fst J) → A (RP'.notI I i') x)
-- -- -- --     → f j ≡ p (I .snd .fst .fst i')
-- -- -- --     → inler-g j i' i (p i') f ≡ inlR (j , p i)
-- -- -- --   push-inl-inr-coh j i' =
-- -- -- --     RP'.elimI I i' (λ p f q → inler-g-id j i' (p i') f .fst)
-- -- -- --                    λ p f q → inler-g-id j i' (p i') f .snd
-- -- -- --                             ∙ sym (push* (j , p (RP'.notI I i')) f q)
-- -- -- -- -}
-- -- -- --   leftFun*-full : (i : fst I) → ΠR-extend* I J A → joinR-gen (fst J) (A i)
-- -- -- --   leftFun*-full i (inl (i' , (j ,  a) , b)) = inler-g j i' i a b
-- -- -- --   leftFun*-full i (inr (inl (inl x , y))) = inlR (x , y i)
-- -- -- --   leftFun*-full i (inr (inl (inr x , y))) = inlR (fst x i , y i)
-- -- -- --   leftFun*-full i (inr (inr x)) = inrR (x i)
-- -- -- --   leftFun*-full i (inr (push ((inl j , p) , f , q) i₁)) = push* (j , p i) (f i) (q i) i₁
-- -- -- --   leftFun*-full i (inr (push ((inr e , p) , f , q) i₁)) = push* (fst e  i , p i) (f i) (q i) i₁
-- -- -- --   leftFun*-full i (push (i' , inl ((inl j , p) , f , q)) i₁) = push-inl-inl-coh j i' i p f q i₁
-- -- -- --   leftFun*-full i (push (i' , inl ((inr e , p) , f , q)) i₁) = {!!}
-- -- -- --   leftFun*-full i (push (i' , inr ((j , a) , p , q)) i₁) = {!!}
-- -- -- --   leftFun*-full i (push (i' , push ((inl j , p) , f , q) i₂) i₁) = {!snd₂!}
-- -- -- --   leftFun*-full i (push (i' , push ((inr e , p) , f , q) i₂) i₁) = {!!}


-- -- -- -- -- -- module _ {ℓ : Level} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) where
-- -- -- -- -- --   module RPI = RP' I
-- -- -- -- -- --   module RPJ = RP' J
-- -- -- -- -- --   leftFun**-inl : (i i' : fst I) (a : Σ (fst J) (A i'))
-- -- -- -- -- --     (b : (j : fst J) → A (RPI.notI i') j)
-- -- -- -- -- --     → joinR-gen (fst J) (A i)
-- -- -- -- -- --   leftFun**-inl i = RPI.elimI i {!!} λ ab p → inrR {!p!}

-- -- -- -- -- --   leftFun** : (i : fst I) → ΠR-extend* I J A → joinR-gen (fst J) (A i)
-- -- -- -- -- --   leftFun** i (inl (i' , (a , b))) = {!b!}
-- -- -- -- -- --   leftFun** i (inr x) = {!!}
-- -- -- -- -- --   leftFun** i (push a i₁) = {!!}

-- -- -- -- module ΠR-extendINL {ℓ : Level} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) where
-- -- -- --   ΠR-extend→inlₗ : (i : fst I) (j : fst J) (p : TotΠ (A (RP'.notI I i))) (a : A i j)
-- -- -- --                 → (i : fst I) → A i j
-- -- -- --   ΠR-extend→inlₗ i j p a = RP'.elimI I i a (p j)

-- -- -- --   ΠR-extend→inlₗ-id : (i : fst I) (j : fst J)
-- -- -- --                       (p : (x : fst I) → A x j)
-- -- -- --                       (f : (j : fst J) → A (RP'.notI I i) j)
-- -- -- --                       (q : f j ≡ p (I .snd .fst .fst i))
-- -- -- --                    → ΠR-extend→inlₗ i j f (p i) ≡ p
-- -- -- --   ΠR-extend→inlₗ-id i j p f q =
-- -- -- --     funExt (RP'.elimI I i (RP'.elimIβ I {B = λ i → A i j} i (p i) (f j) .fst)
-- -- -- --                           (RP'.elimIβ I {B = λ i → A i j} i (p i) (f j) .snd ∙ q))

-- -- -- --   ΠR-extend→inl : (i : fst I) (j : fst J) (p : TotΠ (A (RP'.notI I i))) (a : A i j)
-- -- -- --                 → (i₁ : fst J)
-- -- -- --                 → joinR-gen (fst I) (λ i₂ → A i₂ i₁)
-- -- -- --   ΠR-extend→inl i j p a = RP'.elimI J {B = λ j → joinR-gen (fst I) (λ i₂ → A i₂ j)} j
-- -- -- --                             (inrR (ΠR-extend→inlₗ i j p a))
-- -- -- --                             (inlR ((RP'.notI I i) , (p (RP'.notI J j))))

-- -- -- --   ΠR-extend→inlβ : (i : fst I) (j : fst J) (p : TotΠ (A (RP'.notI I i))) (a : A i j)
-- -- -- --                 → (ΠR-extend→inl i j p a j ≡ inrR (ΠR-extend→inlₗ i j p a))
-- -- -- --                 × (ΠR-extend→inl i j p a (RP'.notI J j) ≡ inlR ((RP'.notI I i) , (p (RP'.notI J j))))
-- -- -- --   ΠR-extend→inlβ i j p a =
-- -- -- --     RP'.elimIβ J {B = λ j → joinR-gen (fst I) (λ i₂ → A i₂ j)} j
-- -- -- --                             (inrR (ΠR-extend→inlₗ i j p a))
-- -- -- --                             (inlR ((RP'.notI I i) , (p (RP'.notI J j))))

-- -- -- --   ΠR-extend→inl-id₁ : (i : fst I) (j : fst J)
-- -- -- --                       (p : (x : fst I) → A x j)
-- -- -- --                       (f : (j : fst J) → A (RP'.notI I i) j)
-- -- -- --                       (q : f j ≡ p (I .snd .fst .fst i))
-- -- -- --                    → ΠR-extend→inl i j f (p i) j ≡ inrR p
-- -- -- --   ΠR-extend→inl-id₁ i j p f q =
-- -- -- --     RP'.elimIβ J {B = λ j → joinR-gen (fst I) (λ i₂ → A i₂ j)} j
-- -- -- --                  (inrR (ΠR-extend→inlₗ i j f (p i)))
-- -- -- --                  (inlR ((RP'.notI I i) , f (RP'.notI J j))) .fst
-- -- -- --     ∙ cong inrR (ΠR-extend→inlₗ-id i j p f q)

-- -- -- --   GOAL = joinR-gen (fst J) λ j → joinR-gen (fst I) λ i → A i j

-- -- -- --   ΠR-extend→inl-id : (i : fst I) (j : fst J)
-- -- -- --                       (p : (x : fst I) → A x j)
-- -- -- --                       (f : (j : fst J) → A (RP'.notI I i) j)
-- -- -- --                       (q : f j ≡ p (I .snd .fst .fst i))
-- -- -- --                 → Path GOAL (inrR (ΠR-extend→inl i j f (p i))) (inlR (j , inrR p))
-- -- -- --   ΠR-extend→inl-id i j p f q =
-- -- -- --     sym (push* (j , inrR p) (ΠR-extend→inl i j f (p i))
-- -- -- --         (ΠR-extend→inl-id₁ i j p f q))

-- -- -- --   module _ (i : fst I) (j : fst J) (p : A i j)
-- -- -- --     (f : (i₁ : fst I) (j₁ : fst J) → A i₁ j₁) (q : f i j ≡ p)
-- -- -- --     where
-- -- -- --     push-inr-cohₗ : ΠR-extend→inl i j (f _) p j ≡ inrR λ i → f i j
-- -- -- --     push-inr-cohₗ =
-- -- -- --         ΠR-extend→inlβ i j (f (RP'.notI I i)) p .fst
-- -- -- --       ∙ cong inrR (funExt (RP'.elimI I i (RP'.elimIβ I i p (f (RP'.notI I i) j) .fst ∙ sym q)
-- -- -- --                                          (RP'.elimIβ I i p (f (RP'.notI I i) j) .snd)))

-- -- -- --     push-inr-cohᵣ : ΠR-extend→inl i j (f _) p (RP'.notI J j)
-- -- -- --                  ≡ inrR λ i → f i (RP'.notI J j)
-- -- -- --     push-inr-cohᵣ =
-- -- -- --         ΠR-extend→inlβ i j (f (RP'.notI I i)) p .snd
-- -- -- --       ∙ push* (RP'.notI I i , f _ _) (λ i → f i (RP'.notI J j)) refl

-- -- -- --   push-inr-coh :
-- -- -- --     (i : fst I) (j : fst J) (p : A i j)
-- -- -- --     (f : (i₁ : fst I) (j₁ : fst J) → A i₁ j₁) (q : f i j ≡ p)
-- -- -- --     (j' : fst J)
-- -- -- --     → ΠR-extend→inl i j (f _) p j' ≡ inrR λ i → f i j'
-- -- -- --   push-inr-coh i j p f q =
-- -- -- --     RP'.elimI J
-- -- -- --       {B = λ j' → ΠR-extend→inl i j (f _) p j' ≡ inrR λ i → f i j'} j
-- -- -- --       (push-inr-cohₗ i j p f q)
-- -- -- --       (push-inr-cohᵣ i j p f q)

-- -- -- --   push-inr-cohβ : (i : fst I) (j : fst J) (p : A i j)
-- -- -- --     (f : (i₁ : fst I) (j₁ : fst J) → A i₁ j₁) (q : f i j ≡ p)
-- -- -- --     → (push-inr-coh i j p f q j ≡ push-inr-cohₗ i j p f q)
-- -- -- --      × (push-inr-coh i j p f q (RP'.notI J j) ≡ push-inr-cohᵣ i j p f q)
-- -- -- --   push-inr-cohβ i j p f q =
-- -- -- --     RP'.elimIβ J
-- -- -- --       {B = λ j' → ΠR-extend→inl i j (f _) p j' ≡ inrR λ i → f i j'} j
-- -- -- --       (push-inr-cohₗ i j p f q)
-- -- -- --       (push-inr-cohᵣ i j p f q)

-- -- -- -- module _ {ℓ : Level}  (I : RP∞' ℓ) (A : fst I → fst I → Type ℓ)
-- -- -- --   (i : fst I) (f : TotΠ (A (RP'.notI I i)))
-- -- -- --   (p : (i : fst I) → A i i)
-- -- -- --   (q : f (RP'.notI I i) ≡ p (RP'.notI I i))
-- -- -- --   where
-- -- -- --   ΠR-extend→inl-diag'ₗ :
-- -- -- --       ΠR-extendINL.ΠR-extend→inl I I A i i f (p i) i
-- -- -- --     ≡ inlR (i , p i)
-- -- -- --   ΠR-extend→inl-diag'ₗ =
-- -- -- --     ΠR-extendINL.ΠR-extend→inlβ I I A i i f (p i) .fst
-- -- -- --      ∙ sym (push* (i , p i)
-- -- -- --              (RP'.elimI I i (p i) (f i))
-- -- -- --              (RP'.elimIβ I i (p i) (f i) .fst))

-- -- -- --   ΠR-extend→inl-diag'ᵣ :
-- -- -- --       ΠR-extendINL.ΠR-extend→inl I I A i i f (p i) (RP'.notI I i)
-- -- -- --     ≡ inlR ((RP'.notI I i) , p (RP'.notI I i))
-- -- -- --   ΠR-extend→inl-diag'ᵣ =
-- -- -- --     (ΠR-extendINL.ΠR-extend→inlβ I I A i i f (p i) .snd
-- -- -- --                       ∙ λ k → inlR (RP'.notI I i , q k))

-- -- -- -- ΠR-extend→inl-diag' : ∀ {ℓ} (I : RP∞' ℓ) (A : fst I → fst I → Type ℓ)
-- -- -- --   (i : fst I)
-- -- -- --   (f : TotΠ (A (RP'.notI I i)))
-- -- -- --   (p : (i : fst I) → A i i)
-- -- -- --   → f (RP'.notI I i) ≡ p (RP'.notI I i)
-- -- -- --   → ΠR-extendINL.ΠR-extend→inl I I A i i f (p i)
-- -- -- --   ≡ λ i → inlR (i , p i)
-- -- -- -- ΠR-extend→inl-diag' I A i f p q =
-- -- -- --   funExt (RP'.elimI I {B = λ i' → ΠR-extendINL.ΠR-extend→inl I I A i i f (p i) i'
-- -- -- --                                 ≡ inlR (i' , p i')} i
-- -- -- --           (ΠR-extend→inl-diag'ₗ I A i f p q)
-- -- -- --           (ΠR-extend→inl-diag'ᵣ I A i f p q))

-- -- -- -- ΠR-extend→inl-diag'β : ∀ {ℓ} (I : RP∞' ℓ) (A : fst I → fst I → Type ℓ)
-- -- -- --   (i : fst I)
-- -- -- --   (f : TotΠ (A (RP'.notI I i)))
-- -- -- --   (p : (i : fst I) → A i i)
-- -- -- --   (q : f (RP'.notI I i) ≡ p (RP'.notI I i))
-- -- -- --   → (funExt⁻ (ΠR-extend→inl-diag' I A i f p q) i
-- -- -- --             ≡ ΠR-extend→inl-diag'ₗ I A i f p q)
-- -- -- --    × ((funExt⁻ (ΠR-extend→inl-diag' I A i f p q) _
-- -- -- --             ≡ ΠR-extend→inl-diag'ᵣ I A i f p q))
-- -- -- -- fst (ΠR-extend→inl-diag'β I A i f p q) k =
-- -- -- --   RP'.elimIβ I {B = λ i' → ΠR-extendINL.ΠR-extend→inl I I A i i f (p i) i'
-- -- -- --                           ≡ inlR (i' , p i')} i
-- -- -- --                (ΠR-extend→inl-diag'ₗ I A i f p q)
-- -- -- --                (ΠR-extend→inl-diag'ᵣ I A i f p q) .fst k
-- -- -- -- snd (ΠR-extend→inl-diag'β I A i f p q) k =
-- -- -- --   RP'.elimIβ I {B = λ i' → ΠR-extendINL.ΠR-extend→inl I I A i i f (p i) i'
-- -- -- --                           ≡ inlR (i' , p i')} i
-- -- -- --                (ΠR-extend→inl-diag'ₗ I A i f p q)
-- -- -- --                (ΠR-extend→inl-diag'ᵣ I A i f p q) .snd k

-- -- -- -- ≃s* : {ℓ : Level} (I J : RP∞' ℓ) (e : fst I ≃ fst J) (A : fst I → fst J → Type ℓ)
-- -- -- --  → (p : (x : fst I) → A x (fst e x))
-- -- -- --  → Σ[ inr-inr ∈ ((j : fst J) → joinR-gen (fst I) (λ i₁ → A i₁ j)) ]
-- -- -- --          Σ[ push-inl-inr ∈ ((i : fst I) (f : TotΠ (A (RP'.notI I i)))
-- -- -- --                            (q : f (fst e (RP'.notI I i)) ≡ p (RP'.notI I i))
-- -- -- --            → ΠR-extendINL.ΠR-extend→inl I J A i (fst e i) f (p i) ≡ inr-inr) ]
-- -- -- --            Σ[ inr-push-inr ∈ ((f : (i₁ : fst I) (j : fst J) → A i₁ j)
-- -- -- --                           (q : (x : fst I) → f x (fst e x) ≡ p x)
-- -- -- --                        → inr-inr ≡ λ j → inrR λ i → f i j) ]
-- -- -- --            ((i : fst I) (j : fst J) (f : (i₂ : fst I) (j : fst J) → A i₂ j)
-- -- -- --             (q : (i' : fst I) → f i' (fst e i') ≡ p i')
-- -- -- --             → (Square refl
-- -- -- --                   (λ k → inr-push-inr f q k j)
-- -- -- --                   (λ k → push-inl-inr i (f (RP'.notI I i)) (q (RP'.notI I i)) k j)
-- -- -- --                   (ΠR-extendINL.push-inr-coh I J A i (fst e i) (p i) f (q i) j)))
-- -- -- -- ≃s* {ℓ = ℓ} I = JRP∞'' I λ A p → (λ i → inlR (i , p i))
-- -- -- --                         , ((λ i f q → ΠR-extend→inl-diag' I A i f p q)
-- -- -- --                         , (λ f q → funExt λ i → push* (i , p i) (λ i' → f i' i) (q i))
-- -- -- --                         , λ i j f q → main I A p f q i j)
-- -- -- --   where
-- -- -- --   main : (I : RP∞' ℓ) (A : fst I → fst I → Type ℓ)
-- -- -- --       (p : (i : fst I) → A i i)
-- -- -- --       (f : (i₂ j₁ : fst I) → A i₂ j₁)
-- -- -- --       (q : (i' : fst I) → f i' i' ≡ p i')
-- -- -- --       (i j : fst I) →
-- -- -- --       Square {A = joinR-gen (fst I) λ i → A i j} refl
-- -- -- --       (push* (j , p j) (λ i₂ → f i₂ j) (q j))
-- -- -- --       (λ k →
-- -- -- --          ΠR-extend→inl-diag' I A i (f (RP'.notI I i)) p (q (RP'.notI I i)) k
-- -- -- --          j)
-- -- -- --       (ΠR-extendINL.push-inr-coh I I A i (idfun (fst I) i) (p i) f (q i)
-- -- -- --        j)
-- -- -- --   main I A p f q i =
-- -- -- --     RP'.elimI I i
-- -- -- --       (flipSquare ((ΠR-extend→inl-diag'β I A i (f (RP'.notI I i)) p (q (RP'.notI I i)) .fst)
-- -- -- --               ◁ pp1
-- -- -- --               ▷ sym (ΠR-extendINL.push-inr-cohβ I I A i i (p i) f (q i) .fst)))
-- -- -- --       (flipSquare (ΠR-extend→inl-diag'β I A i (f (RP'.notI I i)) p (q (RP'.notI I i)) .snd
-- -- -- --               ◁ {!!}
-- -- -- --               ▷ sym (ΠR-extendINL.push-inr-cohβ I I A i i (p i) f (q i) .snd)))
-- -- -- --     where
-- -- -- --     pp1 : PathP
-- -- -- --       (λ i₁ → ΠR-extendINL.ΠR-extend→inl I I A i i (f (RP'.notI I i)) (p i) i
-- -- -- --               ≡ push* (i , p i) (λ v → f v i) (q i) i₁)
-- -- -- --       (ΠR-extend→inl-diag'ₗ I A i (f (RP'.notI I i)) p (q (RP'.notI I i)))
-- -- -- --       (ΠR-extendINL.push-inr-cohₗ I I A i i (p i) f (q i))
-- -- -- --     pp1 k l =
-- -- -- --       hcomp (λ r → λ {(k = i0) → compPath-filler'
-- -- -- --                                      (ΠR-extendINL.ΠR-extend→inlβ I I A i i
-- -- -- --                                        (f (RP'.notI I i)) (p i) .fst)
-- -- -- --                                      (sym (push* (i , p i)
-- -- -- --                                             (RP'.elimI I i (p i) (f (RP'.notI I i) i))
-- -- -- --                                             (RP'.elimIβ I i (p i) (f (RP'.notI I i) i) .fst))) r l
-- -- -- --                      ; (k = i1) → compPath-filler'
-- -- -- --                                      (ΠR-extendINL.ΠR-extend→inlβ I I A i i (f (RP'.notI I i)) (p i) .fst)
-- -- -- --                                      (cong inrR (funExt
-- -- -- --                                        (RP'.elimI I
-- -- -- --                                            {B = λ i' → ΠR-extendINL.ΠR-extend→inlₗ I I A i i (f (RP'.notI I i)) (p i) i'
-- -- -- --                                                       ≡ f i' i} i
-- -- -- --                                        (RP'.elimIβ I {B = λ i' → A i' i}
-- -- -- --                                            i (p i) (f (RP'.notI I i) i) .fst
-- -- -- --                                          ∙ sym (q i))
-- -- -- --                                        (RP'.elimIβ I {B = λ i' → A i' i} i (p i) (f (fst (snd I .fst) i) i) .snd)))) r l
-- -- -- --                      ; (l = i0) → ΠR-extendINL.ΠR-extend→inlβ I I A i i
-- -- -- --                                     (f (RP'.notI I i)) (p i) .fst (~ r)
-- -- -- --                      ; (l = i1) → push* (i , p i) (λ v → f v i) (q i) k})
-- -- -- --          (hcomp (λ r → λ {(k = i0) → {!!}
-- -- -- --                      ; (k = i1) → push* (i , p i)
-- -- -- --                                          (funExt
-- -- -- --                                        (RP'.elimI I
-- -- -- --                                            {B = λ i' → ΠR-extendINL.ΠR-extend→inlₗ I I A i i (f (RP'.notI I i)) (p i) i'
-- -- -- --                                                       ≡ f i' i} i
-- -- -- --                                        (RP'.elimIβ I {B = λ i' → A i' i}
-- -- -- --                                            i (p i) (f (RP'.notI I i) i) .fst
-- -- -- --                                          ∙ sym (q i))
-- -- -- --                                        (RP'.elimIβ I {B = λ i' → A i' i} i (p i) (f (fst (snd I .fst) i) i) .snd)) l)
-- -- -- --                                          {!!} r
-- -- -- --                      {- push* (i , (RP'.elimIβ I {B = λ i' → A i' i} i (p i) (f (RP'.notI I i) i) .fst ∙ (λ i₁ → q i (~ i₁))) l)
-- -- -- --                                     (λ i' → RP'.elimI I
-- -- -- --                                            {B = λ i' → ΠR-extendINL.ΠR-extend→inlₗ I I A i i (f (RP'.notI I i)) (p i) i'
-- -- -- --                                                       ≡ f i' i} i
-- -- -- --                                            (RP'.elimIβ I i (p i) (f (RP'.notI I i) i) .fst ∙ (sym (q i)))
-- -- -- --                                            (RP'.elimIβ I i (p i) (f (fst (snd I .fst) i) i) .snd) i' l)
-- -- -- --                                     (λ j → RP'.elimIβ I {B = λ i' → ΠR-extendINL.ΠR-extend→inlₗ I I A i i (f (RP'.notI I i)) (p i) i'
-- -- -- --                                                    ≡ f i' i} i ((RP'.elimIβ I i (p i) (f (RP'.notI I i) i) .fst ∙
-- -- -- --                                     (λ i₁ → q i (~ i₁)))) (RP'.elimIβ I i (p i) (f (RP'.notI I i) i) .snd) .fst j l) r
-- -- -- --                                     -}
-- -- -- --                      ; (l = i0) → {!!} -- inrR (RP'.elimI I i (p i) (f (RP'.notI I i) i))
-- -- -- --                      ; (l = i1) → {!push* (i , ?) (λ v → f v i) ? k!}})
-- -- -- --                 {!!})

-- -- -- -- ≃s : {ℓ : Level} (I J : RP∞' ℓ) (e : fst I ≃ fst J) (A : fst I → fst J → Type ℓ)
-- -- -- --  → (p : (x : fst I) → A x (fst e x))
-- -- -- --  → Σ[ inr-inr ∈ ((j : fst J) → joinR-gen (fst I) (λ i₁ → A i₁ j)) ]
-- -- -- --        Σ[ inr-push-inr ∈ ((f : (i₁ : fst I) (j : fst J) → A i₁ j)
-- -- -- --                           (q : (x : fst I) → f x (fst e x) ≡ p x)
-- -- -- --                        → inr-inr ≡ λ j → inrR λ i → f i j) ]
-- -- -- --          Σ[ push-inl-inr ∈ ((i : fst I) (f : TotΠ (A (RP'.notI I i)))
-- -- -- --                            (q : f (fst e (RP'.notI I i)) ≡ p (RP'.notI I i))
-- -- -- --            → ΠR-extendINL.ΠR-extend→inl I J A i (fst e i) f (p i) ≡ inr-inr) ]
-- -- -- --            Unit
-- -- -- -- ≃s = {!!}




-- -- -- -- module _ {ℓ : Level} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) where
-- -- -- --   private
-- -- -- --     GOAL = joinR-gen (fst J) λ j → joinR-gen (fst I) λ i → A i j

-- -- -- --   open ΠR-extendINL I J A
-- -- -- --   ΠR-extend→ : ΠR-extend* I J A → joinR-gen (fst J) λ j → joinR-gen (fst I) λ i → A i j
-- -- -- --   ΠR-extend→ (inl (i , (j , a) , p)) = inrR (ΠR-extend→inl i j p a)
-- -- -- --   ΠR-extend→ (inr (inl (inl x , p))) = inlR (x , inrR p)
-- -- -- --   ΠR-extend→ (inr (inl (inr e , p))) = inrR (≃s* I J e A p .fst)
-- -- -- --   ΠR-extend→ (inr (inr x)) = inrR λ j → inrR λ i → x i j
-- -- -- --   ΠR-extend→ (inr (push ((inl j , p) , f , q) i)) = push* (j , inrR p) (λ j → inrR λ i → f i j) (cong inrR (funExt q)) i
-- -- -- --   ΠR-extend→ (inr (push ((inr e , p) , f , q) i)) = inrR (≃s* I J e A p .snd .snd .fst f q i)
-- -- -- --   ΠR-extend→ (push (i , inl ((inl j , p) , f , q)) k) = ΠR-extend→inl-id i j p f q k
-- -- -- --   ΠR-extend→ (push (i , inl ((inr e , p) , f , q)) k) = inrR (≃s* I J e A p .snd .fst i f q k)
-- -- -- --   ΠR-extend→ (push (i , inr ((j , p) , f , q)) k) = inrR λ j' → push-inr-coh i j p f q j' k
-- -- -- --   ΠR-extend→ (push (i , push ((inl j , p) , f , q) i₁) k) = {!!}
-- -- -- --   ΠR-extend→ (push (i , push ((inr e , p) , f , q) i₁) k) = inrR λ j → ≃s* I J e A p .snd .snd .snd i j f q k i₁


-- -- -- -- leftFunExtCurry* : {ℓ : Level} (I : RP∞' ℓ) (i : fst I)
-- -- -- --   (J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
-- -- -- --   → ΠR-extend* I J A → joinR-gen (fst J) (A i)
-- -- -- -- leftFunExtCurry* = JRP∞' leftFun*

-- -- -- -- module _ {ℓ : Level} (I J : RP∞' ℓ)(A : fst I → fst J → Type ℓ) where
-- -- -- --   leftFunExt*' : (i : fst I) → ΠR-extend* I J A → joinR-gen (fst J) (A i)
-- -- -- --   leftFunExt*' i = leftFunExtCurry* I i J A

-- -- -- --   leftFunExt* :  fst I × ΠR-extend* I J A
-- -- -- --              → Σ[ i ∈ fst I ] (joinR-gen (fst J) (A i))
-- -- -- --   leftFunExt* (i , p) = i , leftFunExt*' i p


-- -- -- -- leftFunExtId* : {ℓ : Level} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
-- -- -- --   → leftFunExt*' (RP∞'· ℓ) J A true ≡ leftFun* J A
-- -- -- -- leftFunExtId* {ℓ = ℓ} J A i = lem i J A
-- -- -- --   where
-- -- -- --   lem : leftFunExtCurry* (RP∞'· ℓ) true ≡ leftFun*
-- -- -- --   lem = JRP∞'∙ leftFun*

-- -- -- -- joinR-Push'' : ∀ {ℓ} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) → Type ℓ 
-- -- -- -- joinR-Push'' I J A =
-- -- -- --   Pushout {A = fst I × ΠR-extend* I J A} (leftFunExt* I J A) snd


-- -- -- -- module _ {ℓ ℓ' : Level}
-- -- -- --   {B : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) → Type ℓ'}
-- -- -- --   (ri : (I J : RP∞' ℓ) (A : _) (x : ΠR-extend* I J A) → B I J A)
-- -- -- --   (lef : (J : RP∞' ℓ) (A : _) (x : _) → B (RP∞'· ℓ) J A)
-- -- -- --   (coh : (J : RP∞' ℓ) (A : _) (x : _)
-- -- -- --     → lef J A (leftFun* J A x) ≡ ri (RP∞'· ℓ) J A x) where


-- -- -- --   cool : (J : RP∞' ℓ) (I : RP∞' ℓ) (i : fst I)
-- -- -- --     (A : fst I → fst J → Type ℓ)
-- -- -- --     → Σ[ f ∈ (joinR-gen (fst J) (A i) → B I J A) ]
-- -- -- --          ((t : ΠR-extend* I J A) → f (leftFunExt* I J A (i , t) .snd) ≡ ri I J A t )
-- -- -- --   cool J = JRP∞' λ A → (lef J A)
-- -- -- --                 , (λ t → cong (lef J A) (funExt⁻ (leftFunExtId* J A) t) ∙ coh J A t)

-- -- -- --   joinR-Push''-rec : (I J : _) (A : _) → joinR-Push'' I J A → B I J A
-- -- -- --   joinR-Push''-rec I J A (inl (i , x)) = cool J I i A .fst x
-- -- -- --   joinR-Push''-rec I J A (inr x) = ri I J A x
-- -- -- --   joinR-Push''-rec I J A (push (i , t) j) = cool J I i A .snd t j

-- -- -- -- -- third type
-- -- -- -- -- ΠR-extend** : ∀ {ℓ} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) → Type ℓ
-- -- -- -- -- ΠR-extend** I J A =
-- -- -- -- --   Rewrite1.ΠR-extend-ab I (fst J) A
-- -- -- -- --     ((Σ[ j ∈ (fst J) ] ((i : fst I) → A i j))
-- -- -- -- --    ⊎ (Σ[ e ∈ fst J ≃ fst I ] ((j : fst J) → A (fst e j) j)))
-- -- -- -- --       (λ i → ⊎.rec fst λ p → invEq (fst p) i)
-- -- -- -- --       {!λ i → ?!}

-- -- -- -- -- joinR-Push''' : {!
-- -- -- -- --        (Σ[ x ∈ fst J ⊎ (fst J ≃ fst I) ]
-- -- -- -- --          ((i : fst I) → )) -- A i (fst (2-eltFun {I = I} {J = J}) (invEq x) i)))
-- -- -- -- --        (λ i p → Iso.inv (TotAIso I J {A}) p i .fst)
-- -- -- -- --        (λ i x → Iso.inv (TotAIso I J {A}) x i .snd)!}
-- -- -- -- -- joinR-Push''' = {!!}

-- -- -- -- -- record ext-data {ℓ : Level} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) : Type ℓ where
-- -- -- -- --   field
-- -- -- -- --     s : {!!}




-- -- -- -- -- module ΠR-extend*→-elim {ℓ ℓ' : Level} (I : RP∞' ℓ)
-- -- -- -- --   (B : (J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) → ΠR-extend* I J A → Type ℓ')
-- -- -- -- --   (inl* : (J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
-- -- -- -- --            (j : fst J) (i : fst I) (a : A i j)
-- -- -- -- --            (b : ((j : fst J) → A (2-elter.notI I (fst J) A i) j))
-- -- -- -- --          → B J A (inl (i , (j , a) , b)))
-- -- -- -- --   (inr-inl-inl* : (J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
-- -- -- -- --                   (j : fst J) (p : (i : fst I) → A i j)
-- -- -- -- --                 → B J A (inr (inl (inl j , p))))
-- -- -- -- --   (inr-inr* : (J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
-- -- -- -- --               (f : (i : fst I) (j : fst J) → A i j)
-- -- -- -- --             → B J A (inr (inr f)))
-- -- -- -- --   (inr-push-inl* : (J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
-- -- -- -- --                   (j : fst J) (p : (i : fst I) → A i j)
-- -- -- -- --                   (q : Σ[ t ∈ ((i : fst I) (j : fst J) → A i j) ]
-- -- -- -- --                         ((i : fst I) → t i j ≡ p i))
-- -- -- -- --             → PathP (λ i → B J A (inr (push ((inl j , p) , q) i)))
-- -- -- -- --                      (inr-inl-inl* J A j p)
-- -- -- -- --                      (inr-inr* J A (fst q)))
-- -- -- -- --   (push-inl-inl* : (J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) (j : fst J)
-- -- -- -- --                   (i : fst I)
-- -- -- -- --                   (p : (i : fst I) → A i j)
-- -- -- -- --                   (q : Σ[ f ∈ TotΠ (A (snd I .fst .fst i )) ] f j ≡ p (snd I .fst .fst i))
-- -- -- -- --             → PathP (λ k → B J A (push (i , inl ((inl j , p) , q)) k))
-- -- -- -- --                      (inl* J A j i (p i) (fst q))
-- -- -- -- --                      (inr-inl-inl* J A j p))
-- -- -- -- --   (push-inr* : (J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) (j : fst J)
-- -- -- -- --                (i : fst I) (a : A i j)
-- -- -- -- --                (p : Σ[ f ∈ ((i : fst I) (j : fst J) → A i j) ]
-- -- -- -- --                    f i j ≡ a)
-- -- -- -- --          → PathP (λ k → B J A (push (i , inr ((j , a) , p)) k))
-- -- -- -- --                   (inl* J A j i a (fst p (2-elter.notI I (fst J) A i)))
-- -- -- -- --                   (inr-inr* J A (fst p)))
-- -- -- -- --   (push-push* : (J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) (j : fst J)
-- -- -- -- --                (i : fst I) (p : _) (q : _)
-- -- -- -- --             → SquareP (λ l k → B J A (push (i , push ((inl j , p) , q) k) l))
-- -- -- -- --                        (λ k → inl* J A j i (p i) (fst q (I .snd .fst .fst i)))
-- -- -- -- --                        (inr-push-inl* J A j p q)
-- -- -- -- --                        (push-inl-inl* J A j i p
-- -- -- -- --                          (fst q (I .snd .fst .fst i) , snd q (I .snd .fst .fst i)))
-- -- -- -- --                        (push-inr* J A j i (p i) (fst q , snd q i)))
-- -- -- -- --   (mega : (J : RP∞' ℓ) (e : fst I ≃ fst J)
-- -- -- -- --           (A : fst I → fst J → Type ℓ)
-- -- -- -- --           (p : (i : fst I) → A i (fst e i))
-- -- -- -- --     → Σ[ inr-inl-inr*≃ ∈ B J A (inr (inl (inr e , p))) ]
-- -- -- -- --         Σ[ inr-push-inr*≃ ∈ ((q : Σ[ f ∈ ((i : fst I) (j : fst J) → A i j) ]
-- -- -- -- --                                   ((i : fst I) → f i (fst e i) ≡ p i))
-- -- -- -- --           → PathP (λ i → B J A (inr (push ((inr e , p) , q) i)))
-- -- -- -- --                      inr-inl-inr*≃
-- -- -- -- --                      (inr-inr* J A (fst q))) ]
-- -- -- -- --           Σ[ push-inl-inr*≃ ∈ ((i : fst I) (q : Σ[ f ∈ ((j : fst J) → A (snd I .fst .fst i) j) ]
-- -- -- -- --                                                    f (fst e (snd I .fst .fst i)) ≡ p _)
-- -- -- -- --             → PathP (λ k → B J A (push (i , inl ((inr e , p) , q)) k))
-- -- -- -- --                      (inl* J A (fst e i) i (p i) (fst q))
-- -- -- -- --                      (inr-inl-inr*≃)) ]
-- -- -- -- --             ((i : fst I) (q : Σ[ f ∈ ((i : fst I) (j : fst J) → A i j) ]
-- -- -- -- --                          ((i : fst I) → f i (fst e i) ≡ p i))
-- -- -- -- --             → SquareP (λ l k → B J A (push (i , push ((inr e , p) , q) k) l))
-- -- -- -- --                        (λ _ → inl* J A (fst e i) i (p i) (fst q (I .snd .fst .fst i)))
-- -- -- -- --                        (inr-push-inr*≃ q)
-- -- -- -- --                        (push-inl-inr*≃ i
-- -- -- -- --                          (fst q (I .snd .fst .fst i) , snd q (I .snd .fst .fst i)))
-- -- -- -- --                        (push-inr* J A (fst e i) i (p i) (fst q , snd q i))))
-- -- -- -- --   where
-- -- -- -- --   ΠR-extend*-elim : (J : _) (A : _) (x : _) → B J A x
-- -- -- -- --   ΠR-extend*-elim J A (inl (i , ((j , a) , b))) = inl* J A j i a b
-- -- -- -- --   ΠR-extend*-elim J A (inr (inl (inl x , p))) = inr-inl-inl* J A x p
-- -- -- -- --   ΠR-extend*-elim J A (inr (inl (inr e , p))) = mega J e A p .fst
-- -- -- -- --   ΠR-extend*-elim J A (inr (inr x)) = inr-inr* J A x
-- -- -- -- --   ΠR-extend*-elim J A (inr (push ((inl j , p) , q) i)) = inr-push-inl* J A j p q i
-- -- -- -- --   ΠR-extend*-elim J A (inr (push ((inr e , p) , q) i)) = mega J e A p .snd .fst q i
-- -- -- -- --   ΠR-extend*-elim J A (push (i , inl ((inl j , p) , q)) k) = push-inl-inl* J A j i p q k
-- -- -- -- --   ΠR-extend*-elim J A (push (i , inl ((inr e , p) , q)) k) = mega J e A p .snd .snd .fst i q k
-- -- -- -- --   ΠR-extend*-elim J A (push (i , inr ((j , a) , p)) k) = push-inr* J A j i a p k
-- -- -- -- --   ΠR-extend*-elim J A (push (i , push ((inl j , p) , q) k) l) = push-push* J A j i p q l k
-- -- -- -- --   ΠR-extend*-elim J A (push (i , push ((inr f , p) , q) k) l) = mega J f A p .snd .snd .snd i q l k

-- -- -- -- -- {-
-- -- -- -- -- data PASHR {ℓ ℓ' : Level} (I J : RP∞' ℓ)
-- -- -- -- --   (A : fst I → fst J → Type ℓ) : Type (ℓ-max ℓ ℓ') where
-- -- -- -- --   inl* : (j : fst J) (i : fst I) (a : A i j)
-- -- -- -- --          (b : ((j : fst J) → A (2-elter.notI I (fst J) A i) j))
-- -- -- -- --        → PASHR I J A
-- -- -- -- --   inr-inl-inl* : (j : fst J) (p : (i : fst I) → A i j) → PASHR I J A
-- -- -- -- --   inr-inr* : (f : (i : fst I) (j : fst J) → A i j) → PASHR I J A
-- -- -- -- -- -}

-- -- -- -- -- module EL {ℓ : Level} (I : RP∞' ℓ)  where
-- -- -- -- --   TP : (J₁ : RP∞' ℓ) (A : fst I → fst J₁ → Type ℓ)
-- -- -- -- --       → ΠR-extend* I J₁ A → Type ℓ
-- -- -- -- --   TP J A _ = joinR-gen (fst J) λ j → joinR-gen (fst I) λ i → A i j

-- -- -- -- --   module _ (J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
-- -- -- -- --     (i : fst I) (j : fst J) (a : A i j)
-- -- -- -- --     (b : (j₁ : fst J) → A (Rewrite1.M.notI I (fst J) A i) j₁)
-- -- -- -- --     where
-- -- -- -- --     module Ilem = 2-elter I (fst J) A
-- -- -- -- --     open 2-elter J (fst I) (λ i j → A j i)
-- -- -- -- --     inl*-fun : (i₁ : fst J) → joinR-gen (fst I) (λ i₂ → A i₂ i₁)
-- -- -- -- --     inl*-fun = elimI j (inrR (Ilem.elimI i a (b j))) (inlR (Ilem.notI i , b (notI j)))
    
    

-- -- -- -- --   inl* : (J₁ : RP∞' ℓ) (A : fst I → fst J₁ → Type ℓ) (j : fst J₁)
-- -- -- -- --       (i : fst I) (a : A i j)
-- -- -- -- --       (b : (j₁ : fst J₁) → A (Rewrite1.M.notI I (fst J₁) A i) j₁)
-- -- -- -- --       → TP J₁ A (inl (i , (j , a) , b))
-- -- -- -- --   inl* J A j i a b  = inrR (inl*-fun J A i j a b)

-- -- -- -- --   inr-inl-inl* : (J₁ : RP∞' ℓ) (A : fst I → fst J₁ → Type ℓ) (j : fst J₁)
-- -- -- -- --       (p : (i : fst I) → A i j) →
-- -- -- -- --       TP J₁ A (inr (inl (inl j , p)))
-- -- -- -- --   inr-inl-inl* J A j p = inlR (j , inrR p)

-- -- -- -- --   inr-inl-inr* : (J₁ : RP∞' ℓ) (A : fst I → fst J₁ → Type ℓ)
-- -- -- -- --       (f : (i : fst I) (j : fst J₁) → A i j) →
-- -- -- -- --       TP J₁ A (inr (inr f))
-- -- -- -- --   inr-inl-inr* J A f = inrR (λ j → inrR (λ i → f i j))

-- -- -- -- --   inr-push-inl* : (J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) (j : fst J)
-- -- -- -- --       (p : (i : fst I) → A i j)
-- -- -- -- --       (q : Σ[ t ∈ ((i : fst I) (j : fst J) → A i j) ]
-- -- -- -- --              ((i : fst I) → t i j ≡ p i))
-- -- -- -- --       → inr-inl-inl* J A j p ≡ inr-inl-inr* J A (fst q)
-- -- -- -- --   inr-push-inl* J A j p q =
-- -- -- -- --     push* (j , inrR p) (λ j → inrR λ i → fst q i j)
-- -- -- -- --                        (cong inrR (funExt (snd q)))

-- -- -- -- --   push-inl-inl* : (J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) (j : fst J)
-- -- -- -- --       (i : fst I) (p : (i₁ : fst I) → A i₁ j)
-- -- -- -- --       (q : Σ[ g ∈ ((j : fst J) → A (snd I .fst .fst i) j) ]
-- -- -- -- --              g j ≡ p (I .snd .fst .fst i))
-- -- -- -- --       → inl* J A j i (p i) (fst q)
-- -- -- -- --        ≡ inr-inl-inl* J A j p
-- -- -- -- --   push-inl-inl* J A j i p q = {!!}

-- -- -- -- --   module M = ΠR-extend*→-elim {ℓ = ℓ} {ℓ' = ℓ} I TP
-- -- -- -- --     inl*
-- -- -- -- --     inr-inl-inl*
-- -- -- -- --     inr-inl-inr*
-- -- -- -- --     inr-push-inl*
-- -- -- -- --     (λ J A j i p q → {!!}) -- push-inl-inl* -- 
-- -- -- -- --     {!!}
-- -- -- -- --     {!!}
-- -- -- -- --     (λ J e A p → {!!} , ({!inr-inl-inr*!} , ({!!} , {!!})))
-- -- -- -- --   theF : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
-- -- -- -- --     → {!!}
-- -- -- -- --   theF = {!!}


-- -- -- -- -- module joinR-Push''-rec {ℓ ℓ' : Level}
-- -- -- -- --   (B : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
-- -- -- -- --     → Type ℓ')
-- -- -- -- --   (inl* : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
-- -- -- -- --            (j : fst J) (i : fst I) (a : A i j)
-- -- -- -- --            (b : ((j : fst J) → A (2-elter.notI I (fst J) A i) j))
-- -- -- -- --          → B I J A)
-- -- -- -- --   (inr-inl-inl* : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
-- -- -- -- --                   (j : fst J) (p : (i : fst I) → A i j)
-- -- -- -- --                 → B I J A)
-- -- -- -- --   (inr-inr* : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
-- -- -- -- --               (f : (i : fst I) (j : fst J) → A i j)
-- -- -- -- --             → B I J A)
-- -- -- -- --   (inr-push-inl* : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
-- -- -- -- --                   (j : fst J) (p : (i : fst I) → A i j)
-- -- -- -- --                   (q : Σ[ t ∈ ((i : fst I) (j : fst J) → A i j) ]
-- -- -- -- --                         ((i : fst I) → t i (f3 I J {A} (inl j , p) i .fst)
-- -- -- -- --                                           ≡ f3 I J {A} (inl j , p) i .snd))
-- -- -- -- --             → inr-inl-inl* I J A j p ≡ inr-inr* I J A (fst q))
-- -- -- -- --   (push-inl-inl* : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) (j : fst J)
-- -- -- -- --                   (i : fst I)
-- -- -- -- --                   (p : (i : fst I) → A i j)
-- -- -- -- --                   (q : _)
-- -- -- -- --             → inl* I J A j i (p i) (fst q) ≡ inr-inl-inl* I J A j p)
-- -- -- -- --   (push-inr* : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) (j : fst J)
-- -- -- -- --                (i : fst I) (a : A i j) (p : _)
-- -- -- -- --          → inl* I J A j i a (fst p (2-elter.notI I (fst J) A i)) ≡ inr-inr* I J A (fst p))
-- -- -- -- --   (push-push* : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) (j : fst J)
-- -- -- -- --                (i : fst I) (p : _) (q : _)
-- -- -- -- --             → Square (λ k → inl* I J A j i (p i) (fst q (I .snd .fst .fst i)))
-- -- -- -- --                        (inr-push-inl* I J A j p q)
-- -- -- -- --                        (push-inl-inl* I J A j i p
-- -- -- -- --                          (fst q (I .snd .fst .fst i) , snd q (I .snd .fst .fst i)))
-- -- -- -- --                        (push-inr* I J A j i (p i) (fst q , snd q i)))
-- -- -- -- --   (mega : (I J : RP∞' ℓ) (e : fst I ≃ fst J)
-- -- -- -- --           (A : fst I → fst J → Type ℓ)
-- -- -- -- --           (p : (i : fst I) → A i (fst e i))
-- -- -- -- --     → Σ[ inr-inl-inr*≃ ∈ B I J A ]
-- -- -- -- --         Σ[ inr-push-inr*≃ ∈ ((q : _)
-- -- -- -- --           → inr-inl-inr*≃ ≡ inr-inr* I J A (fst q)) ]
-- -- -- -- --           Σ[ push-inl-inr*≃ ∈ ((i : fst I) (q : _)
-- -- -- -- --             → inl* I J A (fst e i) i (p i) (fst q) ≡ inr-inl-inr*≃) ]
-- -- -- -- --             ((i : fst I) (q : _)
-- -- -- -- --             → Square (λ _ → inl* I J A (fst e i) i (p i) (fst q (I .snd .fst .fst i)))
-- -- -- -- --                        (inr-push-inr*≃ q)
-- -- -- -- --                        (push-inl-inr*≃ i
-- -- -- -- --                          (fst q (I .snd .fst .fst i) , snd q (I .snd .fst .fst i)))
-- -- -- -- --                        (push-inr* I J A (fst e i) i (p i) (fst q , snd q i))))
-- -- -- -- --   (left-inl : (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
-- -- -- -- --               (j : fst J) (a : A true j) → B (RP∞'· ℓ) J A)
-- -- -- -- --   (left-inr : (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
-- -- -- -- --               (f : TotΠ (A true))
-- -- -- -- --            → B (RP∞'· ℓ) J A)
-- -- -- -- --   (left-push : (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
-- -- -- -- --                (j : fst J) (a : A true j)
-- -- -- -- --                (f : TotΠ (A true))
-- -- -- -- --                (p : f j ≡ a)
-- -- -- -- --             → left-inl J A j a ≡ left-inr J A f)
-- -- -- -- --   where
-- -- -- -- --   open ΠR-extend*→-elim (λ I J A _ → B I J A)
-- -- -- -- --          inl* inr-inl-inl* inr-inr*
-- -- -- -- --          inr-push-inl* push-inl-inl* push-inr*
-- -- -- -- --          push-push* mega

-- -- -- -- --   lef-fun : (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
-- -- -- -- --       → PushoutR (Σ (fst J) (A true)) (TotΠ (A true)) (λ x f → f (fst x) ≡ snd x)
-- -- -- -- --       → B (RP∞'· ℓ) J A
-- -- -- -- --   lef-fun J A (inlR (j , a)) = left-inl J A j a
-- -- -- -- --   lef-fun J A (inrR f) = left-inr J A f
-- -- -- -- --   lef-fun J A (push* (j , a) b x i) = left-push J A j a b x i


-- -- -- -- --   pusher : (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
-- -- -- -- --            (x : ΠR-extend* (RP∞'· ℓ) J A)
-- -- -- -- --          → lef-fun J A (leftFun* J A x)
-- -- -- -- --           ≡ ΠR-extend*-elim (RP∞'· ℓ) J A x
-- -- -- -- --   pusher J A (inl (t , (j , a) , f)) = {!!}
-- -- -- -- --   pusher J A (inr (inl (inl j , p))) = {!!}
-- -- -- -- --   pusher J A (inr (inl (inr e , p))) = {!!}
-- -- -- -- --   pusher J A (inr (inr x)) = {!!}
-- -- -- -- --   pusher J A (inr (push a i)) = {!!}
-- -- -- -- --   pusher J A (push a i) = {!!}

-- -- -- -- --   main : (I J : RP∞' ℓ)
-- -- -- -- --          (A : fst I → fst J → Type ℓ)
-- -- -- -- --       → joinR-Push'' I J A
-- -- -- -- --       → B I J A
-- -- -- -- --   main =
-- -- -- -- --     joinR-Push''-rec
-- -- -- -- --       ΠR-extend*-elim
-- -- -- -- --       lef-fun
-- -- -- -- --       {!!}


-- -- -- -- -- ΠR-extend*-full : (I J : _) (A : _) (x : _) → B I J A x
-- -- -- -- -- ΠR-extend*-full I J A x = {!!}

-- -- -- -- --     ΠR-extend*→ : ΠR-extend* I J A → GOAL
-- -- -- -- --     ΠR-extend*→ (inl (i , (j , a) , f)) = inrR (basf i j a f)
-- -- -- -- --     ΠR-extend*→ (inr (inl (inl x , p))) = inlR (x , inrR p)
-- -- -- -- --     ΠR-extend*→ (inr (inl (inr f , p))) = inrR λ j → inlR (eq1 I J f .fst p j)
-- -- -- -- --     ΠR-extend*→ (inr (inr x)) = inrR λ j → inrR (λ i → x i j)
-- -- -- -- --     ΠR-extend*→ (inr (push ((inl x , p) , q) i)) =
-- -- -- -- --       push* (x , inrR p) (λ j → inrR λ i → fst q i j) (cong inrR (funExt (snd q))) i
-- -- -- -- --     ΠR-extend*→ (inr (push ((inr f , p) , q) i)) =
-- -- -- -- --       inrR λ j → push* (eq1 I J f .fst p j) (λ i → fst q i j) (eq1 I J f .snd p j q) i
-- -- -- -- --     ΠR-extend*→ (push (i , inl ((inl j , p) , q)) k) =
-- -- -- -- --       push* (j , inrR p) (basf i j (p i) (fst q))
-- -- -- -- --         (basf≡ i j (p i) (fst q)
-- -- -- -- --        ∙ cong inrR (push-inl i j p q)) (~ k)
-- -- -- -- --     ΠR-extend*→ (push (i , inl ((inr f , p) , q)) k) = inrR {!!}
-- -- -- -- --     ΠR-extend*→ (push (i , inr ((f , p) , q)) k) = inrR {!!}
-- -- -- -- --     ΠR-extend*→ (push (i , push (f , p) j) k) = {!!}

-- -- -- -- -- -- module _ (eq1 : {ℓ : Level} (I J : RP∞' ℓ) (f : fst I ≃ fst J) {A : fst I → fst J → Type ℓ} 
-- -- -- -- -- --               → Σ[ eq1 ∈ ((p : (x : fst I) → A x (fst f x)) (j : fst J)
-- -- -- -- -- --                        → Σ[ i ∈ fst I ] A i j) ]
-- -- -- -- -- --                        ((p : _) (j : fst J)
-- -- -- -- -- --                         (q : Σ[ g ∈ ((i : fst I) (j : fst J) → A i j) ]
-- -- -- -- -- --                               ((i : fst I) → g i (f3 I J {A} (inr f , p) i .fst)
-- -- -- -- -- --                                             ≡ f3 I J {A} (inr f , p) i .snd))
-- -- -- -- -- --                        → fst q (fst (eq1 p j)) j ≡ snd (eq1 p j)))
-- -- -- -- -- --        where
-- -- -- -- -- --   module _ {ℓ : Level} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) where
-- -- -- -- -- --     module N1 = 2-elter I (fst J) A
-- -- -- -- -- --     module N2 = 2-elter J (fst I) (λ x y → A y x)
-- -- -- -- -- --     private
-- -- -- -- -- --       GOAL = joinR-gen (fst J) λ j → joinR-gen (fst I) λ i → A i j

-- -- -- -- -- --     basf : (i : fst I) (j : fst J) (a : A i j)
-- -- -- -- -- --             (f : (j : fst J) → A (N1.notI i) j)
-- -- -- -- -- --          → (j : fst J) → (joinR-gen (fst I) (λ i₂ → A i₂ j))
-- -- -- -- -- --     basf i j a f = N2.elimI j (inrR (N1.elimI i a (f j))) (inlR (N1.notI i , f (N2.notI j)))

-- -- -- -- -- --     basf≡ : (i : fst I) (j : fst J) (a : A i j)
-- -- -- -- -- --             (f : (j : fst J) → A (N1.notI i) j)
-- -- -- -- -- --          → basf i j a f j ≡ inrR (N1.elimI i a (f j))
-- -- -- -- -- --     basf≡ i j a f = N2.elimIβ j (inrR (N1.elimI i a (f j))) (inlR (N1.notI i , f (N2.notI j))) .fst

-- -- -- -- -- --     push-inl : (i : fst I) (j : fst J) (p : (i : fst I) → A i j)
-- -- -- -- -- --         (q : Σ[ g ∈ ((j : fst J) → A (N1.notI i) j) ]
-- -- -- -- -- --                  g (f3 I J (inl j , p) (N1.notI i) .fst)
-- -- -- -- -- --                ≡ f3 I J {A} (inl j , p) (N1.notI i) .snd)
-- -- -- -- -- --       → N1.elimI i (p i) (fst q j) ≡ p
-- -- -- -- -- --     push-inl i j p q =
-- -- -- -- -- --       funExt (N1.elimI i (N1.elimIβ i (p i) (fst q j) .fst)
-- -- -- -- -- --              (N1.elimIβ i (p i) (fst q j) .snd ∙ snd q))

-- -- -- -- -- --     ΠR-extend*→ : ΠR-extend* I J A → GOAL
-- -- -- -- -- --     ΠR-extend*→ (inl (i , (j , a) , f)) = inrR (basf i j a f)
-- -- -- -- -- --     ΠR-extend*→ (inr (inl (inl x , p))) = inlR (x , inrR p)
-- -- -- -- -- --     ΠR-extend*→ (inr (inl (inr f , p))) = inrR λ j → inlR (eq1 I J f .fst p j)
-- -- -- -- -- --     ΠR-extend*→ (inr (inr x)) = inrR λ j → inrR (λ i → x i j)
-- -- -- -- -- --     ΠR-extend*→ (inr (push ((inl x , p) , q) i)) =
-- -- -- -- -- --       push* (x , inrR p) (λ j → inrR λ i → fst q i j) (cong inrR (funExt (snd q))) i
-- -- -- -- -- --     ΠR-extend*→ (inr (push ((inr f , p) , q) i)) =
-- -- -- -- -- --       inrR λ j → push* (eq1 I J f .fst p j) (λ i → fst q i j) (eq1 I J f .snd p j q) i
-- -- -- -- -- --     ΠR-extend*→ (push (i , inl ((inl j , p) , q)) k) =
-- -- -- -- -- --       push* (j , inrR p) (basf i j (p i) (fst q))
-- -- -- -- -- --         (basf≡ i j (p i) (fst q)
-- -- -- -- -- --        ∙ cong inrR (push-inl i j p q)) (~ k)
-- -- -- -- -- --     ΠR-extend*→ (push (i , inl ((inr f , p) , q)) k) = inrR {!!}
-- -- -- -- -- --     ΠR-extend*→ (push (i , inr ((f , p) , q)) k) = inrR {!!}
-- -- -- -- -- --     ΠR-extend*→ (push (i , push (f , p) j) k) = {!!}


-- -- -- -- -- -- -- module BoolC {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ) where
-- -- -- -- -- -- --   open 2-elter (RP∞'· ℓ) (fst J) A
-- -- -- -- -- -- --   left-push→' : left-push → joinR-gen (fst J) (A true)
-- -- -- -- -- -- --   left-push→' (false , t , f) = inrR f
-- -- -- -- -- -- --   left-push→' (true , t , f) = inlR t

-- -- -- -- -- -- --   ΠR-base→' : ΠR-base → joinR-gen (fst J) (A true)
-- -- -- -- -- -- --   ΠR-base→' (inl x) = inlR (x true)
-- -- -- -- -- -- --   ΠR-base→' (inr x) = inrR (x true)
-- -- -- -- -- -- --   ΠR-base→' (push (a , b , c) i) = push* (a true) (b true) (c true) i

-- -- -- -- -- -- --   cohs : (a : Bool) (b : Pushout (fat→ₗ a) (fat→ᵣ a))
-- -- -- -- -- -- --        → left-push→' (a , PushTop→left-push' a b) ≡ ΠR-base→' (PushTop→ΠR-base (a , b))
-- -- -- -- -- -- --   cohs false (inl (a , b , c)) = sym (push* (a true) b c) 
-- -- -- -- -- -- --   cohs false (inr x) = refl
-- -- -- -- -- -- --   cohs false (push (a , b , c) i) j = push* (a true) (b true) (c true) (i ∨ ~ j)
-- -- -- -- -- -- --   cohs true (inl (a , b , c)) = refl
-- -- -- -- -- -- --   cohs true (inr (a , b , c)) = push* a (b true) c
-- -- -- -- -- -- --   cohs true (push (a , b , c) i) j = push* (a true) (b true) (c true) (i ∧ j)

-- -- -- -- -- -- --   T : ΠR-extend → joinR-gen (fst J) (A true)
-- -- -- -- -- -- --   T (inl x) = left-push→' x
-- -- -- -- -- -- --   T (inr x) = ΠR-base→' x
-- -- -- -- -- -- --   T (push (a , b) i) = cohs a b i

-- -- -- -- -- -- --   T-alt : ΠR-extend → joinR-gen (fst J) (A true)
-- -- -- -- -- -- --   T-alt x = ΠR-extend→Π x true

-- -- -- -- -- -- --   idPL : (x : _) → left-push→' x ≡ T-alt (inl x)
-- -- -- -- -- -- --   idPL (false , b) = refl
-- -- -- -- -- -- --   idPL (true , b) = refl

-- -- -- -- -- -- --   idP : (x : ΠR-extend) → T x ≡ T-alt x
-- -- -- -- -- -- --   idP x = l x ∙ ΠR-extend→Π-alt≡ {J = J} A x true
-- -- -- -- -- -- --     where
-- -- -- -- -- -- --     l : (x : _) → T x ≡ ΠR-extend→Π-alt J A x true
-- -- -- -- -- -- --     l (inl (false , snd₁)) = refl
-- -- -- -- -- -- --     l (inl (true , snd₁)) = refl
-- -- -- -- -- -- --     l (inr (inl x)) = refl
-- -- -- -- -- -- --     l (inr (inr x)) = refl
-- -- -- -- -- -- --     l (inr (push a i)) = refl
-- -- -- -- -- -- --     l (push (false , inl x) i) = refl
-- -- -- -- -- -- --     l (push (false , inr x) i) = refl
-- -- -- -- -- -- --     l (push (false , push a i₁) i) = refl
-- -- -- -- -- -- --     l (push (true , inl x) i) = refl
-- -- -- -- -- -- --     l (push (true , inr x) i) = refl
-- -- -- -- -- -- --     l (push (true , push a i₁) i) = refl

-- -- -- -- -- -- --   module MM = 2-elter' (RP∞'· ℓ) (fst J) A

-- -- -- -- -- -- --   left-push→2 : MM.left-push → joinR-gen (fst J) (A true)
-- -- -- -- -- -- --   left-push→2 (false , a , b) = inrR b
-- -- -- -- -- -- --   left-push→2 (true , a , b) = inlR a

-- -- -- -- -- -- --   ΠR-base→2 : MM.ΠR-base → joinR-gen (fst J) (A true)
-- -- -- -- -- -- --   ΠR-base→2 (inl (inl x , b)) = inlR (x , b true)
-- -- -- -- -- -- --   ΠR-base→2 (inl (inr x , b)) = inlR ((fst x true) , (b true))
-- -- -- -- -- -- --   ΠR-base→2 (inr x) = inrR (x true)
-- -- -- -- -- -- --   ΠR-base→2 (push (inl x , b) i) = push* (x , b true x) (b true) refl i
-- -- -- -- -- -- --   ΠR-base→2 (push (inr x , b) i) = push* (fst x true , b true (fst x true)) (b true) refl i

-- -- -- -- -- -- --   coh-false : (s : _) → left-push→2 (false , MM.PushTop→left-push' false s) ≡ ΠR-base→2 (MM.PushTop→ΠR-base (false , s))
-- -- -- -- -- -- --   coh-false (inl (inl x , (a , b))) = sym (push* (x , b x) b refl)
-- -- -- -- -- -- --   coh-false (inl (inr x , (a , b))) = sym (push* (fst x true , b (fst x true)) b refl)
-- -- -- -- -- -- --   coh-false (inr x) = refl
-- -- -- -- -- -- --   coh-false (push (inl x , b) i) j = {!!}
-- -- -- -- -- -- --   coh-false (push (inr x , b) i) = {!!}

-- -- -- -- -- -- --   T-alt2 : MM.ΠR-extend → joinR-gen (fst J) (A true)
-- -- -- -- -- -- --   T-alt2 (inl x) = left-push→2 x
-- -- -- -- -- -- --   T-alt2 (inr x) = ΠR-base→2 x
-- -- -- -- -- -- --   T-alt2 (push (f , s) i) = {!s!}
  

-- -- -- -- -- -- -- -- module _ (I J : RP∞' ℓ-zero) {A : fst I → fst J → Type} where
-- -- -- -- -- -- -- --   private
-- -- -- -- -- -- -- --     GOAL = joinR-gen (fst J) λ j → joinR-gen (fst I) λ x → A x j
-- -- -- -- -- -- -- --   module IM = 2-elter' I (fst J) A
-- -- -- -- -- -- -- --   module JM = 2-elter' J (fst I) (λ x y → A y x)

-- -- -- -- -- -- -- --   extenderₗ : IM.left-push → GOAL
-- -- -- -- -- -- -- --   extenderₗ (i , (j , a) , f) = inrR (JM.elimI j (inrR (IM.elimI i a (f j))) (inlR (IM.notI i , f (JM.notI j))))

-- -- -- -- -- -- -- --   extenderᵣ : IM.ΠR-base → GOAL
-- -- -- -- -- -- -- --   extenderᵣ (inl (inl j , p)) = inlR (j , inrR p)
-- -- -- -- -- -- -- --   extenderᵣ (inl (inr e , p)) = inrR λ j → inlR ((invEq e j) , {!e!})
-- -- -- -- -- -- -- --   extenderᵣ (inr x) = inrR λ j → inrR (λ i → x i j)
-- -- -- -- -- -- -- --   extenderᵣ (push a i) = {!!}
  
-- -- -- -- -- -- -- --   extender : IM.ΠR-extend → GOAL
-- -- -- -- -- -- -- --   extender (inl x) = extenderₗ x
-- -- -- -- -- -- -- --   extender (inr x) = extenderᵣ x
-- -- -- -- -- -- -- --   extender (push (a , inl (inl x , p)) i) = {!!}
-- -- -- -- -- -- -- --   extender (push (a , inl (inr x , p)) i) = {!!}
-- -- -- -- -- -- -- --   extender (push (a , inr x) i) = {!!}
-- -- -- -- -- -- -- --   extender (push (a , push a₁ i₁) i) = {!!}

-- -- -- -- -- -- -- -- module _ (J : RP∞' ℓ-zero) {A : Bool → fst J → Type} where
-- -- -- -- -- -- -- --   open 2-elter' J Bool (λ x y → A y x)
-- -- -- -- -- -- -- --   private
-- -- -- -- -- -- -- --     GOAL = joinR-gen (fst J) λ j → joinR-gen Bool λ x → A x j

-- -- -- -- -- -- -- --   inl-inlₗ : (x : fst J) (f : A true x) (f' : A false x) → GOAL
-- -- -- -- -- -- -- --   inl-inlₗ x f f' = inlR (x , inrR (CasesBool true f f'))

-- -- -- -- -- -- -- --   inl-inlᵣ : (x : fst J) (f : A true x) (f' : A false (notI x)) → GOAL
-- -- -- -- -- -- -- --   inl-inlᵣ x f f' = inrR (elimI x (inlR (true , f)) (inlR (false , f')))

-- -- -- -- -- -- -- --   inl-inl : (x : fst J) → (A true x) → (x' : fst J) → A false x' → GOAL
-- -- -- -- -- -- -- --   inl-inl x f = elimI x (inl-inlₗ x f) (inl-inlᵣ x f)

-- -- -- -- -- -- -- --   inl-inlₗid : (x : fst J) (f : A true x) (f' : A false x) → inl-inl x f x f' ≡ inl-inlₗ x f f'
-- -- -- -- -- -- -- --   inl-inlₗid x f f' = funExt⁻ (elimIβ x (inl-inlₗ x f) (inl-inlᵣ x f) .fst) f'

-- -- -- -- -- -- -- --   inl-inlᵣid : (x : fst J) (f : A true x) (f' : A false (notI x)) → inl-inl x f (notI x) f' ≡ inl-inlᵣ x f f'
-- -- -- -- -- -- -- --   inl-inlᵣid x f f' = funExt⁻ (elimIβ x (inl-inlₗ x f) (inl-inlᵣ x f) .snd) f'

-- -- -- -- -- -- -- --   inl-pushₗ : (x : fst J) (f : A true x) (f' : A false x) (b : TotΠ (A false)) (x₁ : b x ≡ f')
-- -- -- -- -- -- -- --            → inl-inl x f x f'
-- -- -- -- -- -- -- --             ≡ inrR (elimI x (inrR (CasesBool true f (b x))) (inlR (false , b (notI x))))
-- -- -- -- -- -- -- --   inl-pushₗ x f f' b x₁ =
-- -- -- -- -- -- -- --       inl-inlₗid x f f'
-- -- -- -- -- -- -- --     ∙ push* (x , inrR (CasesBool true f f'))
-- -- -- -- -- -- -- --             _
-- -- -- -- -- -- -- --             (elimIβ x (inrR (CasesBool true f (b x)))
-- -- -- -- -- -- -- --                       (inlR (false , b (notI x))) .fst
-- -- -- -- -- -- -- --           ∙ λ i → inrR (CasesBool true f (x₁ i)))



-- -- -- -- -- -- -- --   inl-pushᵣ : (x : fst J) (f : A true x) (f' : A false (notI x)) (b : TotΠ (A false)) (x₁ : b (notI x) ≡ f')
-- -- -- -- -- -- -- --            → inl-inl x f (notI x) f'
-- -- -- -- -- -- -- --             ≡ inrR (elimI x (inrR (CasesBool true f (b x))) (inlR (false , b (notI x))))
-- -- -- -- -- -- -- --   inl-pushᵣ x f f' b x₁ =
-- -- -- -- -- -- -- --       inl-inlᵣid x f f'
-- -- -- -- -- -- -- --     ∙ cong inrR (funExt (elimI x (elimIβ x (inlR (true , f)) (inlR (false , f')) .fst
-- -- -- -- -- -- -- --                               ∙∙ push* (true , f) (CasesBool true f (b x)) refl
-- -- -- -- -- -- -- --                               ∙∙ sym (elimIβ x (inrR (CasesBool true f (b x))) (inlR (false , b (notI x))) .fst))
-- -- -- -- -- -- -- --                                  (elimIβ x (inlR (true , f)) (inlR (false , f')) .snd
-- -- -- -- -- -- -- --                                ∙∙ (λ j → inlR (false , x₁ (~ j)))
-- -- -- -- -- -- -- --                                ∙∙ sym (elimIβ x (inrR (CasesBool true f (b x))) (inlR (false , b (notI x))) .snd))))

-- -- -- -- -- -- -- --   inl-push : (x : fst J) (f : A true x) (x' : fst J) (f' : A false x') (b : TotΠ (A false)) (x₁ : b x' ≡ f')
-- -- -- -- -- -- -- --     → inl-inl x f x' f'
-- -- -- -- -- -- -- --      ≡ inrR (elimI x (inrR (CasesBool true f (b x))) (inlR (false , b (notI x))))
-- -- -- -- -- -- -- --   inl-push x f = elimI x (inl-pushₗ x f) (inl-pushᵣ x f)

-- -- -- -- -- -- -- --   ×→Goal : (x : joinR-gen (fst J) (A true) × joinR-gen (fst J) (A false))
-- -- -- -- -- -- -- --          → GOAL
-- -- -- -- -- -- -- --   ×→Goal (inlR (x , f) , inlR (x' , f')) = inl-inl x f x' f'
-- -- -- -- -- -- -- --   ×→Goal (inlR (x , f) , inrR y) = inrR (elimI x (inrR (CasesBool true f (y x))) (inlR (false , y (notI x))))
-- -- -- -- -- -- -- --   ×→Goal (inlR (j , f) , push* (j' , f') b x₁ i) = inl-push j f j' f' b x₁ i
-- -- -- -- -- -- -- --   ×→Goal (inrR x , inlR x₁) = {!!}
-- -- -- -- -- -- -- --   ×→Goal (inrR x , inrR x₁) = inrR λ j → inrR (CasesBool true (x j) (x₁ j))
-- -- -- -- -- -- -- --   ×→Goal (inrR x , push* a b x₁ i) = {!!}
-- -- -- -- -- -- -- --   ×→Goal (push* a b₁ x i , b) = {!!}

-- -- -- -- -- -- -- --   ⊎→Goal : joinR-gen (fst J) (A true) → GOAL
-- -- -- -- -- -- -- --   ⊎→Goal (inlR (j , a)) = inlR (j , inlR (true , a))
-- -- -- -- -- -- -- --   ⊎→Goal (inrR f) = inrR λ j → inlR (true , f j)
-- -- -- -- -- -- -- --   ⊎→Goal (push* a b x i) = push* (fst a , inlR (true , snd a)) (λ i → inlR (true , b i)) (λ i → inlR (true , x i)) i

-- -- -- -- -- -- -- --   coher : (f : _) → ×→Goal f ≡ ⊎→Goal (fst f)
-- -- -- -- -- -- -- --   coher f = {!f!}

-- -- -- -- -- -- -- --   LType : {!!}
-- -- -- -- -- -- -- --   LType = {!!}

-- -- -- -- -- -- -- -- module final {J : RP∞' ℓ-zero}
-- -- -- -- -- -- -- --          (main-fun : (I : RP∞' ℓ-zero) → {A : fst I → fst J → Type}
-- -- -- -- -- -- -- --                    → TotΠ (λ i → joinR-gen (typ J) (A i))
-- -- -- -- -- -- -- --                    → (joinR-gen (fst J) λ j → joinR-gen (fst I) λ i → A i j))
-- -- -- -- -- -- -- --          (main-fun-id : {A : Bool → fst J → Type}
-- -- -- -- -- -- -- --                      → (x : joinR-gen (fst J) (A true) × joinR-gen (fst J) (A false))
-- -- -- -- -- -- -- --                      → main-fun (RP∞'· ℓ-zero) {A = A} (Iso.inv ΠBool×Iso x)
-- -- -- -- -- -- -- --                       ≡ ×→Goal J x) where

-- -- -- -- -- -- -- --   mainₗ : (I : RP∞' ℓ-zero) (i : fst I) (A : fst I → fst J → Type)
-- -- -- -- -- -- -- --     → joinR-gen (fst J) (A i)
-- -- -- -- -- -- -- --     → joinR-gen (fst J) λ j → joinR-gen (fst I) λ i → A i j
-- -- -- -- -- -- -- --   mainₗ = JRP∞' λ A → ⊎→Goal J

-- -- -- -- -- -- -- --   mainₗ≡ : (A : _) → mainₗ (RP∞'· ℓ-zero) true A ≡ ⊎→Goal J
-- -- -- -- -- -- -- --   mainₗ≡ = funExt⁻ (JRP∞'∙ (λ A → ⊎→Goal J))

-- -- -- -- -- -- -- --   main : (I : RP∞' ℓ-zero) (A : fst I → fst J → Type)
-- -- -- -- -- -- -- --     → (joinR-gen (fst I) λ i → joinR-gen (fst J) (A i))
-- -- -- -- -- -- -- --     → joinR-gen (fst J) λ j → joinR-gen (fst I) λ i → A i j 
-- -- -- -- -- -- -- --   main I A (inlR (i , j)) = mainₗ I i A j
-- -- -- -- -- -- -- --   main I A (inrR x) = main-fun I x
-- -- -- -- -- -- -- --   main I A (push* (i , a) b x k) = help I i b a x k
-- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- --     help : (I : RP∞' ℓ-zero) (i : fst I) {A : fst I → fst J → Type}
-- -- -- -- -- -- -- --            (b : (i₁ : fst I) → joinR-gen (fst J) (A i₁))
-- -- -- -- -- -- -- --          → (a : joinR-gen (fst J) (A i)) 
-- -- -- -- -- -- -- --          → b i ≡ a
-- -- -- -- -- -- -- --          → mainₗ I i A a ≡ main-fun I b 
-- -- -- -- -- -- -- --     help = JRP∞' λ {A} → λ f → J> funExt⁻ (mainₗ≡ A) (f true)
-- -- -- -- -- -- -- --                                ∙ sym (coher J (f true , f false))
-- -- -- -- -- -- -- --                                ∙ sym (main-fun-id {A} (f true , f false))
-- -- -- -- -- -- -- --                                ∙ cong (main-fun (RP∞'· ℓ-zero))
-- -- -- -- -- -- -- --                                       (funExt λ { false → refl
-- -- -- -- -- -- -- --                                                 ; true → refl})


-- -- -- -- -- -- -- -- joinGen : ∀ {ℓ} (I : Type ℓ)(A : I → Type ℓ) → Type ℓ
-- -- -- -- -- -- -- -- joinGen I A = Pushout {A = I × TotΠ A} {B = Σ I A} (λ fi → (fst fi , snd fi (fst fi))) snd

-- -- -- -- -- -- -- -- join-funct : ∀ {ℓ} (I : Type ℓ) {A B : I → Type ℓ} (f : (i : I) → A i → B i) → joinGen I A → joinGen I B
-- -- -- -- -- -- -- -- join-funct I f (inl x) = inl (fst x , f (fst x) (snd x))
-- -- -- -- -- -- -- -- join-funct I f (inr x) = inr (λ k → f k (x k))
-- -- -- -- -- -- -- -- join-funct I f (push (i , g) k) = push (i , (λ x → f x (g x))) k

-- -- -- -- -- -- -- -- JoinEqFunct : ∀ {ℓ} (I J : Type ℓ) {A : I → J → Type ℓ}
-- -- -- -- -- -- -- --   → joinGen (I ≃ J) (λ e → joinGen J λ j → A (invEq e j) j)
-- -- -- -- -- -- -- --   → joinGen (I ≃ J) (λ e → joinGen I λ i → A i (fst e i))
-- -- -- -- -- -- -- -- JoinEqFunct {ℓ} I J {A = A} = join-funct (I ≃ J)
-- -- -- -- -- -- -- --   λ e → EquivJ (λ I e → (A : I → J → Type ℓ) → (joinGen J λ j → A (invEq e j) j)
-- -- -- -- -- -- -- --       → joinGen I λ i → A i (fst e i)) (λ A → idfun _) e A


-- -- -- -- -- -- -- -- module _ {ℓ} (I J : Type ℓ) {A : I → J → Type ℓ} (mk : (i : I) (j : J) → Σ[ e ∈ I ≃ J ] (fst e i ≡ j)) where
-- -- -- -- -- -- -- --   JoinEq'* :
-- -- -- -- -- -- -- --       (joinGen (I ≃ J) (λ e → joinGen J λ j → A (invEq e j) j))
-- -- -- -- -- -- -- --     → (joinGen I λ i → joinGen J λ j → A i j)
-- -- -- -- -- -- -- --   JoinEq'* (inl (e , t)) = {!!}
-- -- -- -- -- -- -- --   JoinEq'* (inr e) = inr λ i → {!!}
-- -- -- -- -- -- -- --   JoinEq'* (push (e , t) i) = {!!}
  

-- -- -- -- -- -- -- --   JoinEq' : (joinGen I λ i → joinGen J λ j → A i j)
-- -- -- -- -- -- -- --     → joinGen (I ≃ J) (λ e → joinGen J λ j → A (invEq e j) j)
-- -- -- -- -- -- -- --   JoinEq' (inl (i , inl (j , t))) = inl (mk i j .fst , inl (j , subst (λ k → A k j) {!snd (mk i j)!} t))
-- -- -- -- -- -- -- --   JoinEq' (inl (i , inr x)) = inr λ e → inl (fst e i , subst (λ k → A k (fst e i)) (sym (retEq e i)) (x (fst e i)))
-- -- -- -- -- -- -- --   JoinEq' (inl (i , push a i₁)) = {!!}
-- -- -- -- -- -- -- --   JoinEq' (inr x) = {!!}
-- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- --     s : (e : I ≃ J) (j : _) → joinGen J (λ j₁ → A (invEq e j) j₁) → A (invEq e j) j
-- -- -- -- -- -- -- --     s e j (inl x) = {!snd x!}
-- -- -- -- -- -- -- --     s e j (inr x) = x j
-- -- -- -- -- -- -- --     s e j (push a i) = {!!}
-- -- -- -- -- -- -- --   JoinEq' (push (e , t) i) = {!!}
