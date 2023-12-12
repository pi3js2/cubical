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
module Cubical.Cohomology.EilenbergMacLane.nov.boolcase-alt where
open import Cubical.HITs.Join
open import Cubical.Functions.FunExtEquiv


EquivJ* : ∀ {ℓ ℓ'} (C : (A : Bool → Bool → Type ℓ) → Type ℓ)
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


record 𝕄 {ℓ : Level} (Targ : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) → ΠR-extend** I J A → Type ℓ)
        (Targ' : (A : Bool → Bool → Type ℓ) → ΠR-extend** (RP∞'· ℓ) (RP∞'· ℓ) A → Type ℓ)
        (e : (A : Bool → Bool → Type ℓ) (x : ΠR-extend** (RP∞'· ℓ) (RP∞'· ℓ) A)
          → Targ (RP∞'· ℓ) (RP∞'· ℓ) A x ≃ Targ' A x)
        (G : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) → (x : ΠR-extend** I J A) → (i : fst I) → Targ I J A x)
        (pushG : (A : Bool → Bool → Type ℓ) (x : newBack (RP∞'· ℓ) (RP∞'· ℓ) A) (a : Bool)
          → PathP (λ i → Targ' A (push x i))
                   (fst (e A _) (G (RP∞'· ℓ) (RP∞'· ℓ) A (inl (newBack→ₗ (RP∞'· ℓ) (RP∞'· ℓ) A x)) a))
                   (fst (e A _) (G (RP∞'· ℓ) (RP∞'· ℓ) A (inr (newBack→ᵣ (RP∞'· ℓ) (RP∞'· ℓ) A x)) a))) : Type (ℓ-suc ℓ)
        where
  field
    inler : (A : Bool → Bool → Type ℓ) (a : A true true) (b : TotΠ (A false))
      → Targ' A (inl (true , (true , a) , b))
    inr-inr : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) (t : (i : fst I) (j : fst J) → A i j)
           → Targ I J A (inr (inr t))
    inr-inl-inl : (I : RP∞' ℓ) (A : fst I → Bool → Type ℓ)
                 (f : (x : fst I) → A x true)
                   → Σ[ k ∈ Targ I (RP∞'· ℓ) A (inr (inl (inl true , f))) ]
                     ((p : (i : fst I) (j : Bool) → A i j) (q : (x : fst I) → p x true ≡ f x)
                   → PathP (λ r → Targ I (RP∞'· ℓ) A (inr (push ((inl true , f) , (p , q)) r)))
                            k (inr-inr I (RP∞'· ℓ) A p))
    inr-inl-inr : (I : RP∞' ℓ) (A : fst I → fst I → Type ℓ) (f : (i : fst I) → A i i)
         → Σ[ k ∈ Targ I I A (inr (inl (inr (idEquiv (fst I)) , f))) ]
             ((p : (i : fst I) (j : fst I) → A i j) (q : (x : fst I) → p x x ≡ f x)
          → PathP (λ r → Targ I I A (inr (push ((inr (idEquiv (fst I)) , f) , (p , q)) r)))
                                 k (inr-inr I I A p))
    push-inl : (A : Bool → Bool → Type ℓ) (f : (i : Bool) → A i true)
     (g : (j : Bool) → A false j) (p : g true ≡ f false)
     → PathP (λ k → Targ' A
              (push (true , true , inl (inl (f , g , p))) k))
            (inler A (f true) g)
            (fst (e A _) (inr-inl-inl (RP∞'· ℓ) A f .fst))
    coh-inr : (A : Bool → Bool → Type ℓ) (g : (i j : Bool) → A i j)
       → PathP (λ k → Targ' A (push (true , true , inr g) k))
                (inler A (g true true) (g false))
                (fst (e A _) (inr-inr (RP∞'· ℓ) (RP∞'· ℓ) A g))
    coh-eq1 : (A : Bool → Bool → Type ℓ) (g : (i : Bool) → A i i) (f : TotΠ (A false)) (p : f false ≡ g false)
                 → PathP (λ k → Targ' A (push (true , true , inl (inr (idEquiv Bool , refl , g , f , p))) k))
                         (inler A (g true) f)
                   (fst (e A _) (inr-inl-inr (RP∞'· ℓ) A g .fst))
    coh-eq2 : (A : Bool → Bool → Type ℓ) (g : (i j : Bool) → A i j)
       → SquareP (λ i j → Targ' A
                            (push (true , true , push (inr (idEquiv Bool , refl , g)) i) j))
                 (coh-eq1 A (λ i → g i i) (g false) refl)
                 (coh-inr A g)
                 (λ _ → inler A (g true true) (g false))
                 λ i → fst (e A _) (inr-inl-inr (RP∞'· ℓ) A (λ i₁ → g i₁ i₁) .snd g (λ _ → refl) i)
    coh-eq-l : (A : Bool → Bool → Type ℓ) (g : (i j : Bool) → A i j)
       → SquareP (λ i j → Targ' A
                           (push (true , true , push (inl g) i) j))
                   (push-inl A (λ i₁ → g i₁ true) (g false) (λ _ → g false true))
                   (coh-inr A g)
                   (λ _ → inler A (g true true) (g false))
                   (λ i → fst (e A _) (inr-inl-inl (RP∞'· ℓ) A (λ i → g i true) .snd g (λ _ → refl) i))
    G-inler : (A : Bool → Bool → Type ℓ) (a : A true true) (b : TotΠ (A false)) (i : Bool)
                    → fst (e A _) (G (RP∞'· ℓ) (RP∞'· ℓ) A (inl (true , (true , a) , b)) i) ≡ inler A a b
    G-inr-inr : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) (t : (i : fst I) (j : fst J) → A i j)
                       (i : fst I)
                  → G I J A (inr (inr t)) i ≡ inr-inr I J A t
    G-inr-inl-inl₁ : (I : RP∞' ℓ) (A : fst I → Bool → Type ℓ)
                        (f : (x : fst I) → A x true) (i : fst I)
                     → (G I (RP∞'· ℓ) A (inr (inl (inl true , f))) i)
                       ≡ inr-inl-inl I A f .fst
    G-inr-inl-inl₂ : (I : RP∞' ℓ) (A : fst I → Bool → Type ℓ)
                        (f : (x : fst I) → A x true) (i : fst I)
                        (p : (i₁ : fst I) (j : Bool) → A i₁ j) (q : (x : fst I) → p x true ≡ f x)
                     → SquareP (λ i j → Targ I (RP∞'· ℓ) A (inr (push ((inl true , f) , p , q) j)))
                                (λ k → G I (RP∞'· ℓ) A (inr (push ((inl true , f) , p , q) k)) i)
                                (inr-inl-inl I A f .snd p q)
                                (G-inr-inl-inl₁ I A f i)
                                (G-inr-inr I (RP∞'· ℓ) A p i)
    G-inr-inl-inr₁ : (I : RP∞' ℓ) (A : fst I → fst I → Type ℓ)
              (f : (i : fst I) → A i i) (i : fst I)
              → G I I A (inr (inl (inr (idEquiv (fst I)) , f))) i ≡ inr-inl-inr I A f .fst
    G-inr-inl-inr₂ : (I : RP∞' ℓ) (A : fst I → fst I → Type ℓ)
              (f : (i : fst I) → A i i) (p : (i₁ j : fst I) → A i₁ j)
                 (q : ((x : fst I) → p x x ≡ f x))
                 (i : fst I)
              → SquareP (λ i j → Targ I I A (inr (push ((inr (idEquiv (fst I)) , f) , p , q) j)))
                         (λ k → G I I A (inr (push ((inr (idEquiv (fst I)) , f) , p , q) k)) i)
                         (inr-inl-inr I A f .snd p q)
                         (G-inr-inl-inr₁ I A f i)
                         (G-inr-inr I I A p i)

    G-push-inl : (A : Bool → Bool → Type ℓ) (f : (i : fst (RP∞'· ℓ)) → A i true)
              (g : (j : Bool) → A false j) (p : g true ≡ f false) (i : Bool)
              → SquareP (λ i j → Targ' A
                                   (push (true , true , inl (inl (f , g , p))) j))
                         (λ k → pushG A (true , true , inl (inl (f , g , p))) i k)
                         (push-inl A f g p)
                         (G-inler A (f true) g i)
                         λ k → fst (e A _) (G-inr-inl-inl₁ (RP∞'·  ℓ) A f i k)
    G-coh-inr : (A : Bool → Bool → Type ℓ) (g : (i j : Bool) → A i j) (i : Bool)
           → SquareP (λ i j → Targ' A (push (true , true , inr g) j))
                      (pushG A (true , true , inr g) i)
                      (coh-inr A g)
                      (G-inler A (g true true) (g false) i)
                      (λ k → fst (e A _) (G-inr-inr (RP∞'· ℓ) (RP∞'· ℓ) A g i k))
    G-coh-eq1 : (A : Bool → Bool → Type ℓ) (g : (i : Bool) → A i i) (f : TotΠ (A false)) (p : f false ≡ g false) (x : Bool)
                     → SquareP (λ i j → Targ' A (push (true , true , inl (inr (idEquiv Bool , refl , g , f , p))) j))
                       (pushG A (true , true , inl (inr (idEquiv Bool , refl , g , f , p))) x)
                       (coh-eq1 A g f p)
                       (G-inler A (g true) f x)
                       (λ t → fst (e A _) (G-inr-inl-inr₁ (RP∞'· ℓ) A g x t))
    G-coh-eq2 : (A : Bool → Bool → Type ℓ) (g : (i j : Bool) → A i j) (x : Bool)
           → CubeP (λ k i j → Targ' A
                                (push (true , true , push (inr (idEquiv Bool , refl , g)) i) j))
               (λ i j → pushG A (true , true , push (inr (idEquiv Bool , refl , g)) i) x j)
               (coh-eq2 A g)
               (G-coh-eq1 A (λ i → g i i) (g false) refl x)
               (G-coh-inr A g x)
               (λ i _ → G-inler A (g true true) (g false) x i)
               λ s t → fst (e A _) (G-inr-inl-inr₂ (RP∞'· ℓ) A (λ i → g i i) g (λ i → refl) x s t)
    G-coh-eq-l :
              (A : Bool → Bool → Type ℓ) (g : (i j : Bool) → A i j) (x : Bool)
           → CubeP (λ k i j → Targ' A
                                (push (true , true , push (inl g) i) j))
               (λ i j → pushG A (true , true , push (inl g) i) x j)
               (coh-eq-l A g)
               (G-push-inl A (λ i → g i true) (g false) refl x)
               (G-coh-inr A g x)
               (λ i _ → G-inler A (g true true) (g false) x i)
               λ s t → fst (e A _) (G-inr-inl-inl₂ (RP∞'· ℓ) A (λ i → g i true) x g (λ _ → refl) s t)

MEGA-inst↓ : ∀ {ℓ} (Targ : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) → ΠR-extend** I J A → Type ℓ)
        (G : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) → (x : ΠR-extend** I J A) → (i : fst I) → Targ I J A x)
     → 𝕄 Targ (Targ _ _) (λ _ _ → idEquiv _) G (λ A e a i → G (RP∞'· ℓ) (RP∞'· ℓ) A (push e i) a)
     →  (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
     → Σ[ f ∈ ((x : _) → Targ I J A x) ] ((i : fst I) (x : _) → G _ _ A x i ≡ f x)
MEGA-inst↓ Targ G M I J A = (ΠR-extend→ I J A) , (λ i → G.GID I i J A)
  where
  open 𝕄 M
  module MEG = MEGA {Targ = Targ}
    inler inr-inr inr-inl-inl inr-inl-inr push-inl coh-inr
    coh-eq1 coh-eq2 coh-eq-l
  open MEG
  module G = ID G G-inler G-inr-inr G-inr-inl-inl₁ G-inr-inl-inl₂ G-inr-inl-inr₁ G-inr-inl-inr₂
                   G-push-inl G-coh-inr G-coh-eq1 G-coh-eq2 G-coh-eq-l
MEGA-inst :
  ∀ {ℓ} (Targ : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) → ΠR-extend** I J A → Type ℓ)
        (Targ' : (A : Bool → Bool → Type ℓ) → ΠR-extend** (RP∞'· ℓ) (RP∞'· ℓ) A → Type ℓ)
        (e : (A : Bool → Bool → Type ℓ) (x : ΠR-extend** (RP∞'· ℓ) (RP∞'· ℓ) A)
          → Targ (RP∞'· ℓ) (RP∞'· ℓ) A x ≃ Targ' A x)
        (G : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) → (x : ΠR-extend** I J A) → (i : fst I) → Targ I J A x)
        (pushG : (A : Bool → Bool → Type ℓ) (x : newBack (RP∞'· ℓ) (RP∞'· ℓ) A) (a : Bool)
          → PathP (λ i → Targ' A (push x i))
                   (fst (e A _) (G (RP∞'· ℓ) (RP∞'· ℓ) A (inl (newBack→ₗ (RP∞'· ℓ) (RP∞'· ℓ) A x)) a))
                   (fst (e A _) (G (RP∞'· ℓ) (RP∞'· ℓ) A (inr (newBack→ᵣ (RP∞'· ℓ) (RP∞'· ℓ) A x)) a)))
     → ((λ A x a i → fst (e A _) (G (RP∞'· ℓ) (RP∞'· ℓ) A (push x i) a)) ≡ pushG)
     → 𝕄 Targ Targ' e G pushG
     → (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
     → Σ[ f ∈ ((x : _) → Targ I J A x) ] ((i : fst I) (x : _) → G _ _ A x i ≡ f x)
MEGA-inst {ℓ = ℓ} Targ = EquivJ* (λ A → ΠR-extend** (RP∞'· ℓ) (RP∞'· ℓ) A)
  λ G → J> MEGA-inst↓ _ _


ΣBool→ : ∀ {ℓ} {A : Bool → Type ℓ} → Σ Bool A → A true × A false → Type ℓ
ΣBool→ (false , a) (b , c) = c ≡ a
ΣBool→ (true , a) (b , c) = b ≡ a


joinR-gen' : ∀ {ℓ} (A : Bool → Type ℓ) → Type ℓ
joinR-gen' A = PushoutR  (Σ Bool A) (A true × A false) ΣBool→

joinR→ : ∀ {ℓ} (A : Bool → Type ℓ) →  joinR-gen Bool A → joinR-gen' A
joinR→ A (inlR x) = inlR x
joinR→ A (inrR x) = inrR (x true , x false)
joinR→ A (push* (false , a) b x i) = push* (false , a) (b true , b false) x i
joinR→ A (push* (true , a) b x i) = push* (true , a) (b true , b false) x i

joinRIso : ∀ {ℓ} (A : Bool → Type ℓ) → Iso (joinR-gen Bool A) (joinR-gen' A)
Iso.fun (joinRIso A) = joinR→ A
Iso.inv (joinRIso A) (inlR x) = inlR x
Iso.inv (joinRIso A) (inrR (a , b)) = inrR (CasesBool true a b)
Iso.inv (joinRIso A) (push* (false , a) (b , c) x i) = push* (false , a) (CasesBool true b c) x i
Iso.inv (joinRIso A) (push* (true , a) (b , c) x i) = push* (true , a) (CasesBool true b c) x i
Iso.rightInv (joinRIso A) (inlR x) = refl
Iso.rightInv (joinRIso A) (inrR x) = refl
Iso.rightInv (joinRIso A) (push* (false , a) b x i) = refl
Iso.rightInv (joinRIso A) (push* (true , a) b x i) = refl
Iso.leftInv (joinRIso A) (inlR x) = refl
Iso.leftInv (joinRIso A) (inrR x) = cong inrR (CasesBoolη x)
Iso.leftInv (joinRIso A) (push* (false , a) f x i) j = push* (false , a) (CasesBoolη f j) x i
Iso.leftInv (joinRIso A) (push* (true , a) f x i) j = push* (true , a) (CasesBoolη f j) x i

joinR'Funct : ∀ {ℓ} {A B : Bool → Type ℓ} → ((x : Bool) → A x → B x) → joinR-gen' A → joinR-gen' B
joinR'Funct f (inlR (i , x)) = inlR (i , f i x)
joinR'Funct f (inrR (a , b)) = inrR (f true a , f false b)
joinR'Funct f (push* (false , a) (b , c) x i) = push* (false , f false a) (f true b , f false c) (cong (f false) x) i
joinR'Funct f (push* (true , a) (b , c) x i) = push* (true , f true a) (f true b , f false c) (cong (f true) x) i

joinR'Funct'isEq : ∀ {ℓ} {A B : Bool → Type ℓ} → (e : (x : Bool) → A x ≃ B x)
  → section (joinR'Funct (fst ∘ e)) (joinR'Funct (invEq ∘ e))
  × retract (joinR'Funct (fst ∘ e)) (joinR'Funct (invEq ∘ e))
joinR'Funct'isEq {ℓ = ℓ} {A} {B} e = subst TYP (isContr→isProp help _ (B , e)) main
  where
  help : isContr (Σ[ B ∈ (Bool → Type ℓ) ] ((x : Bool) → A x ≃ B x))
  help = isOfHLevelRetractFromIso 0
           (Σ-cong-iso-snd (λ B → compIso (codomainIsoDep
             (λ b → equivToIso (invEquiv univalence))) funExtIso))
           (isContrSingl A)

  TYP : (Σ[ B ∈ (Bool → Type ℓ) ] ((x : Bool) → A x ≃ B x)) → Type ℓ
  TYP (B , e) = section (joinR'Funct (fst ∘ e)) (joinR'Funct (invEq ∘ e))
              × retract (joinR'Funct (fst ∘ e)) (joinR'Funct (invEq ∘ e))

  main : TYP (A , λ x → idEquiv (A x))
  fst main (inlR x) = refl
  fst main (inrR x) = refl
  fst main (push* (false , a) b x i) = refl
  fst main (push* (true , a) b x i) = refl
  snd main (inlR x) = refl
  snd main (inrR x) = refl
  snd main (push* (false , a) b x i) = refl
  snd main (push* (true , a) b x i) = refl

joinR'FunctIso : ∀ {ℓ} {A B : Bool → Type ℓ} (e : (x : Bool) → A x ≃ B x)
  → Iso (joinR-gen' A) (joinR-gen' B)
Iso.fun (joinR'FunctIso e) = joinR'Funct (fst ∘ e)
Iso.inv (joinR'FunctIso e) = joinR'Funct (invEq ∘ e)
Iso.rightInv (joinR'FunctIso e) = joinR'Funct'isEq e .fst
Iso.leftInv (joinR'FunctIso e) = joinR'Funct'isEq e .snd

joinRIso≃ : ∀ {ℓ} (A : Bool → Type ℓ) → joinR-gen Bool A ≃ joinR-gen' A
joinRIso≃ A = isoToEquiv (joinRIso A)

GOALTY : ∀ {ℓ} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) → Type ℓ
GOALTY I J A = joinR-gen (fst J) λ j → joinR-gen (fst I) λ i → A i j

GOALTY' : ∀ {ℓ} (A : Bool → Bool → Type ℓ) → Type ℓ
GOALTY' A = joinR-gen' λ a → joinR-gen' λ b → A b a

GOALTY≃ : ∀ {ℓ} (A : Bool → Bool → Type ℓ)
  → Iso (GOALTY (RP∞'· ℓ) (RP∞'· ℓ) A) (GOALTY' A)
GOALTY≃ A = compIso (joinRIso (λ y → joinR-gen Bool λ x → A x y))
                    (joinR'FunctIso λ y → isoToEquiv (joinRIso (λ x → A x y)))

GFUN : ∀ {ℓ} (A : Bool → Bool → Type ℓ)
  → GOALTY (RP∞'· ℓ) (RP∞'· ℓ) A → GOALTY' A
GFUN A = Iso.fun (GOALTY≃ A)


GFUNEq : ∀ {ℓ} (A : Bool → Bool → Type ℓ)
  → GOALTY (RP∞'· ℓ) (RP∞'· ℓ) A ≃ GOALTY' A
fst (GFUNEq A) = GFUN A
snd (GFUNEq A) = isoToIsEquiv (GOALTY≃ A)


𝕄inst : ∀ {ℓ} → Type (ℓ-suc ℓ)
𝕄inst {ℓ = ℓ} =
  𝕄 (λ I J A _ → GOALTY I J A)
     (λ A _ → GOALTY' A)
     (λ A _ → GFUNEq A)
     (λ I J A x i → btm-map I J A (i , leftMap** I J A i x))
     λ A x a j → GFUN A (btm-map (RP∞'· ℓ) (RP∞'· ℓ) A (a , leftMapBool (RP∞'· ℓ) A a (push x j)))


private
  variable
    ℓ : Level

inrerr : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
         (t : (i : fst I) (j : fst J) → A i j) → GOALTY I J A
inrerr I J A t = inrR λ j → inrR λ i → t i j

G-inr-inr* : (I₁ J₁ : RP∞' ℓ) (A : fst I₁ → fst J₁ → Type ℓ)
      (t : (i : fst I₁) (j : fst J₁) → A i j) (i : fst I₁) →
      inrR (λ j → inlR (i , t i j)) ≡ inrerr I₁ J₁ A t
G-inr-inr* I J A t i = cong inrR λ k j → push* (i , t i j) (λ i → t i j) refl k

inr-inl-inl* : (I : RP∞' ℓ) (A : fst I → Bool → Type ℓ)
  (f : (x : fst I) → A x true)
  → Σ[ x ∈ GOALTY I (RP∞'· ℓ) A ]
      ((p : (i : fst I) (j : Bool) → A i j)
       (q : (i : fst I) → p i true ≡ f i)
      → x ≡ inrerr I (RP∞'· ℓ) A p)
fst (inr-inl-inl* I A f) = inlR (true , inrR f)
snd (inr-inl-inl* I A f) p q =
  push* (true , inrR f) (λ i → inrR λ j → p j i) (cong inrR (funExt q))

G-inr-inl-inl*₁ : (I₁ : RP∞' ℓ) (A : fst I₁ → Bool → Type ℓ)
      (f : (x : fst I₁) → A x true) (i : fst I₁) →
      Path (GOALTY I₁ (RP∞'· ℓ) A) (inlR (true , inlR (i , f i))) (inlR (true , inrR f))
G-inr-inl-inl*₁ I A f i k = inlR (true , push* (i , f i) f refl k)

G-inr-inl-inl*₂ : (I₁ : RP∞' ℓ) (A : fst I₁ → Bool → Type ℓ)
      (f : (x : fst I₁) → A x true) (i : fst I₁)
      (p : (i₁ : fst I₁) (j : Bool) → A i₁ j)
      (q : (x : fst I₁) → p x true ≡ f x) →
      Square {A = GOALTY I₁ (RP∞'· ℓ) A}
      (λ k → push* (true , inlR (i , f i)) (λ j → inlR (i , p i j))
                    (λ t → inlR (i , q i t)) k)
      (push* (true , inrR f) (λ j → inrR (λ i₁ → p i₁ j))
      (λ i₁ → inrR (funExt q i₁)))
      (G-inr-inl-inl*₁ I₁ A f i) (G-inr-inr* I₁ (RP∞'· ℓ) A p i)
G-inr-inl-inl*₂ I A f i p q k j =
  push* (true , push* (i , f i) f (λ _ → f i) k)
        (λ i₁ → push* (i , p i i₁) (λ i₂ → p i₂ i₁) (λ _ → p i i₁) k)
        (λ t → push* (i , q i t) (λ x → q x t) refl k) j

inr-inl-inr* : (I : RP∞' ℓ) (A : fst I → fst I → Type ℓ)
  (f : (x : fst I) → A x x)
  → Σ[ x ∈ GOALTY I I A ]
      ((p : (i j : fst I) → A i j)
       (q : (i : fst I) → p i i ≡ f i)
      → x ≡ inrerr I I A p)
fst (inr-inl-inr* I A f) = inrR λ i → inlR (i , (f i))
snd (inr-inl-inr* I A f) p q k = inrR (λ i → push* (i , f i) (λ j → p j i) (q i) k)


G-inr-inl-inr*₁ : (I₁ : RP∞' ℓ) (A : fst I₁ → fst I₁ → Type ℓ)
      (f : (i : fst I₁) → A i i) (i : fst I₁) →
      Path (GOALTY I₁ I₁ A) (inlR (idfun (fst I₁) i , inlR (i , f i)))
                            (inrR (λ i₁ → inlR (i₁ , f i₁)))
G-inr-inl-inr*₁ I A f i = push* (i , (inlR (i , f i))) (λ j → inlR (j , f j)) refl

module _ (I₁ : RP∞' ℓ) (A : fst I₁ → fst I₁ → Type ℓ)
      (p : (i₁ j : fst I₁) → A i₁ j) (i : fst I₁) where
  G-inr-inl-inr*₂-b-fill : (j k r : _) →  GOALTY I₁ I₁ A
  G-inr-inl-inr*₂-b-fill j k r =
    hfill (λ r → λ {(j = i0) → push* (i , inlR (i , p i i))
                                        (λ s → push* (i , p i s) (λ t → p t s) refl (~ r))
                                        (λ t → push* (i , p i i) (λ t → p t i) refl (~ r ∧ ~ t)) k
                   ; (j = i1) → inrR (λ v → push* (v , p v v) (λ a → p a v) (λ _ → p v v) (~ r ∨ k))
                   ; (k = i0) → push* (i , inlR (i , p i i))
                                       (λ x → push* (x , p x x) (λ a → p a x) refl (~ r))
                                       (λ j → push* (i , p i i) (λ a → p a i) refl (~ r ∧ ~ j)) j
                   ; (k = i1) → inrR (λ v → push* (i , p i v) (λ t → p t v) refl (~ r ∨ j))})
           (inS (push* (i , inlR (i , p i i))
             (λ v → inrR (λ a → p a v))
             (sym (push* (i , p i i) (λ a → p a i) refl))
             (j ∨ k)))
           r

  G-inr-inl-inr*₂-b :
    Square (λ k → push* (i , inlR (i , p i i)) (λ v → inlR (i , p i v)) refl k)
            (λ k → inrR (λ i₁ → push* (i₁ , p i₁ i₁) (λ j → p j i₁) refl k))
            (G-inr-inl-inr*₁ I₁ A (λ x → p x x) i)
            (G-inr-inr* I₁ I₁ A p i)
  G-inr-inl-inr*₂-b j k = G-inr-inl-inr*₂-b-fill j k i1

  G-inr-inl-inr*₂ :
        (f : (i : fst I₁) → A i i) (q : (λ x → p x x) ≡ f) →
        Square
        (λ k → push* (i , inlR (i , f i)) (λ j → inlR (i , p i j))
                      (λ t → inlR (i , q t i)) k)
        (λ k → inrR (λ i₁ → push* (i₁ , f i₁) (λ j → p j i₁) (funExt⁻ q i₁) k))
        (G-inr-inl-inr*₁ I₁ A f i)
        (G-inr-inr* I₁ I₁ A p i)
  G-inr-inl-inr*₂ = J> G-inr-inl-inr*₂-b

  G-inr-inl-inr*₂-refl : G-inr-inl-inr*₂ (λ x → p x x) refl ≡ G-inr-inl-inr*₂-b
  G-inr-inl-inr*₂-refl = transportRefl G-inr-inl-inr*₂-b

module Sol {ℓ : Level} (A : Bool → Bool → Type ℓ) where
  inler : A true true → TotΠ (A false) → GOALTY' A
  inler a b = inrR ((inrR (a , b true)) , (inlR (false , b false)))

  push-inl :
      (f : (i : fst (RP∞'· ℓ)) → A i true)
      (g : (j : Bool) → A false j)
      (p : g true ≡ f false) →
      inler (f true) g ≡ GFUN A (inlR (true , inrR f))
  push-inl f g p =
    sym (push* (true , inrR (f true , f false))
               ((inrR (f true , g true)) , (inlR (false , g false)))
               λ k → inrR (f true , p k))

  coh-inr : (g : (i j : Bool) → A i j) →
      inler (g true true) (g false) ≡
      GFUN A (inrerr (RP∞'· ℓ) (RP∞'· ℓ) A g)
  coh-inr g i =
    inrR (inrR (g true true , g false true)
        , push* (false , g false false)
                (g true false , g false false)
                refl i)

  coh-eq1 : (g : (i : Bool) → A i i)
      (f : TotΠ (A false)) (p : f false ≡ g false) →
      inler (g true) f ≡ GFUN A (inrR (λ i → inlR (i , g i)))
  coh-eq1 g f p i = inrR ((push* (true , g true) (g true , f true) refl (~ i)) , (inlR (false , p i)))

  coh-eq2 : (g : (i j : Bool) → A i j) →
      Square
      (coh-eq1 (λ i → g i i) (g false) refl) (coh-inr g)
      (λ _ → inler (g true true) (g false))
      (λ i →
         GFUN A (inrR (λ i₁ → push* (i₁ , g i₁ i₁) (λ j → g j i₁) refl i)))
  coh-eq2 g i j = inrR ((push* (true , g true true) (g true true , g false true) refl (i ∨ ~ j))
                      , (push* (false , g false false) (g true false , g false false) refl (i ∧ j)))

  coh-eq-l : (g : (i j : Bool) → A i j) →
      Square
      (push-inl (λ i₁ → g i₁ true) (g false) (λ _ → g false true))
      (coh-inr g)
      (λ _ → inler (g true true) (g false))
      (λ i →
         GFUN A (push* (true , inrR (λ i₁ → g i₁ true))
          (λ j → inrR (λ i₁ → g i₁ j)) refl
          i))
  coh-eq-l g i j =
    hcomp (λ k → λ {(i = i0) → push* (true , inrR (g true true , g false true))
                                        (inrR (g true true , g false true) , inlR (false , g false false))
                                        (λ _ → inrR (g true true , g false true)) (k ∧ ~ j)
                   ; (i = i1) → push* (true , inrR (g true true , g false true))
                                       (inrR (g true true , g false true) , push* (false , g false false) (g true false , g false false) refl j)
                                       refl k
                   ; (j = i0) → push* (true , inrR (g true true , g false true))
                                       (inrR (g true true , g false true) , inlR (false , g false false))
                                       (λ _ → inrR (g true true , g false true)) k
                   ; (j = i1) → push* (true , inrR (g true true , g false true))
                                       (inrR (g true true , g false true) ,
                                        inrR (g true false , g false false)) refl (i ∧ k)})
          (inlR (true , inrR (g true true , g false true)))

  G-inler : (a : A true true)
      (b : TotΠ (A false)) (i : Bool) →
      GFUN A
      (btm-map (RP∞'· ℓ) (RP∞'· ℓ) A
       (i , leftFun'-inl (RP∞'· ℓ) (fst (RP∞'· ℓ)) A true (true , a) b i))
      ≡ inler a b
  G-inler a b false i = inrR (push* (false , b true) (a , b true) refl i , inlR (false , b false))
  G-inler a b true i =
    push* (true , inlR (true , a))
          (inrR (a , b true) , inlR (false , b false))
          (sym (push* (true , a) (a , b true) refl)) i

  G-push-inl :
      (f : (i : Bool) → A i true) (g : (j : Bool) → A false j)
      (p : g true ≡ f false) (i : Bool) →
      Square
      (λ k →
         GFUN A (btm-map (RP∞'· ℓ) (RP∞'· ℓ) A
          (i , leftMapBool (RP∞'· ℓ) A i
           (push (true , true , inl (inl (f , g , p))) k))))
      (push-inl f g p)
      (G-inler (f true) g i)
      (λ k → GFUN A (G-inr-inl-inl*₁ (RP∞'· ℓ) A f i k))
  G-push-inl f g p false j k =
    push* (true , push* (false , f false) (f true , f false) refl j)
         ((push* (false , g true) (f true , g true) refl j) , (inlR (false , g false)))
         (λ s → push* (false , p s) (f true , p s) refl j) (~ k)
  G-push-inl f g p true i j =
    hcomp (λ k → λ {(j = i0) → push*
                                   (true , inlR (true , f true))
                                   (inrR (f true , p (~ k)) , inlR (false , g false))
                                   (sym (push* (true , f true) (f true , p (~ k)) refl)) i
                     ; (j = i1) → inlR (true , push* (true , f true) (f true , f false) refl (i ∧ k))
                     ; (i = i0) → inlR (true , inlR (true , f true))
                     ; (i = i1) → push* (true , push* (true , f true) (f true , f false) refl k)
                                          (inrR (f true , p (~ k)) , inlR (false , g false))
                                          (λ i → push* (true , f true) (f true , p (~ k ∨ i)) refl
                                          (k ∨ ~ i)) (~ j)})
            (push* (true , inlR (true , f true))
                   (inrR (f true , f false) , inlR (false , g false))
                   (sym (push* (true , f true) (f true , f false) refl))
                   (i ∧ ~ j))

  G-coh-inr-t-fill : (g : (i j : Bool) → A i j) (i j k : _)
    → GOALTY' A
  G-coh-inr-t-fill g i j k =
    hfill (λ k → λ {(j = i0) → push* (true , inlR (true , g true true))
                                       (inrR (g true true , g false true) , inlR (false , g false false))
                                       (sym (push* (true , g true true) (g true true , g false true) refl))
                                       (i ∧ k)
                   ; (j = i1) → push* (true , inlR (true , g true true))
                                        ((push* (true , g true true) (g true true , g false true) refl i)
                                       , (push* (true , g true false) (g true false , g false false) refl i))
                                       (λ s → push* (true , g true true) (g true true , g false true) refl (~ s ∧ i)) k
                   ; (i = i0) → push* (true , inlR (true , g true true))
                                        (inlR (true , g true true) , inlR (true , g true false))
                                        (λ i₁ → inlR (true , g true true)) (j ∧ k)
                   ; (i = i1) → push* (true , inlR (true , g true true)) (inrR (g true true , g false true)
                                           , push* (false , g false false) (g true false , g false false) refl j)
                                           (sym (push* (true , g true true) (g true true , g false true) refl)) k})
           (inS (inlR (true , inlR (true , g true true))))
           k

  G-coh-inr : (g : (i j : Bool) → A i j)
      (i : Bool) →
      Square
      (λ j → GFUN A (btm-map (RP∞'· ℓ) (RP∞'· ℓ) A
               (i , leftMapBool (RP∞'· ℓ) A i (push (true , true , inr g) j))))
      (coh-inr g)
      (G-inler (g true true) (g false) i)
      λ k → GFUN A (G-inr-inr* (RP∞'· ℓ) (RP∞'· ℓ) A g i k)
  G-coh-inr g false i j =
    inrR ((push* (false , g false true) (g true true , g false true) refl i)
        , (push* (false , g false false) (g true false , g false false) refl (i ∧ j)))
  G-coh-inr g true i j = G-coh-inr-t-fill g i j i1

  G-coh-eq1-fill : (g : (i : Bool) → A i i)
        (f : TotΠ (A false)) (p : f false ≡ g false)
     → (i j k : _) → GOALTY' A
  G-coh-eq1-fill g f p i j k =
    hfill (λ k → λ {(i = i0) → push* (false , inlR (false , g false))
                                       (inlR (false , f true) , inlR (false , f false))
                                       (λ i₁ → inlR (false , p i₁)) (~ j ∧ k)
                   ; (i = i1) → push* (false , inlR (false , g false))
                                       (push* (true , g true) (g true , f true) refl (~ j)
                                       , inlR (false , p j))
                                       (λ i → inlR (false , p (i ∨ j))) k
                   ; (j = i0) → push* (false , inlR (false , g false))
                                       (push* (false , f true) (g true , f true) refl i , inlR (false , f false))
                                       (λ i → inlR (false , p i)) k
                   ; (j = i1) → push* (false , inlR (false , g false))
                                       (inlR (true , g true) , inlR (false , g false))
                                       (λ i₁ → inlR (false , g false)) (i ∧ k)})
          (inS (inlR (false , inlR (false , g false))))
          k

  G-coh-eq1 : (g : (i : Bool) → A i i)
        (f : TotΠ (A false)) (p : f false ≡ g false) (x : Bool) →
        Square
        (λ j → GFUN A
           (btm-map (RP∞'· ℓ) (RP∞'· ℓ) A
            (x , leftMapBool (RP∞'· ℓ) A x (push (true , true , inl (inr (idEquiv Bool , refl , g , f , p))) j))))
        (coh-eq1 g f p)
        (G-inler (g true) f x)
        (λ t → GFUN A (G-inr-inl-inr*₁ (RP∞'· ℓ) A g x t))
  G-coh-eq1 g f p false i j = G-coh-eq1-fill g f p i j i1
  G-coh-eq1 g f p true i j =
    push* (true , inlR (true , g true))
          (push* (true , g true) (g true , f true) refl (~ j) , inlR (false , p j))
          (λ k → push* (true , g true) (g true , f true) refl (~ j ∧ ~ k)) i

  G-coh-eq2-main :  (g : (i j : Bool) → A i j)
      (x : Bool) →
      Cube
      (λ i _ → G-inler (g true true) (g false) x i)
      (λ s t →
         GFUN A
         (G-inr-inl-inr*₂-b (RP∞'· ℓ) A g x s t))
      (λ i j → GFUN A
         (btm-map (RP∞'· ℓ) (RP∞'· ℓ) A
          (x , leftMapBool (RP∞'· ℓ) A x
           (push (true , true , push (inr (idEquiv Bool , refl , g)) j) i)))) -- ()
      (λ i j → coh-eq2 g j i) -- (G-coh-inr g x)
      (λ i j → G-coh-eq1 (λ i → g i i) (g false) refl x j i)
      λ i j → G-coh-inr g x j i
  G-coh-eq2-main g false k i j =
    hcomp (λ r → λ {(i = i0) → push* (false , inlR (false , g false false))
                                        (inlR (false , g false true) , inlR (false , g false false))
                                        (λ i₁ → inlR (false , g false false)) ((~ k ∨ j) ∧ r)
                   ; (i = i1) → push* (false , inlR (false , g false false))
                                       ((push* (true , g true true) (g true true , g false true) refl (j ∨ ~ k))
                                      , (push* (false , g false false) (g true false , g false false) refl (j ∧ k)))
                                       (λ s → push* (false , g false false) (g true false , g false false) refl (j ∧ k ∧ ~ s)) r
                   ; (j = i0) → G-coh-eq1-fill (λ i → g i i) (g false) refl i k r
                   ; (j = i1) → push* (false , inlR (false , g false false))
                                       ((push* (false , g false true) (g true true , g false true) refl i)
                                      , (push* (false , g false false) (g true false , g false false) refl (i ∧ k)))
                                       (λ s → push* (false , g false false) (g true false , g false false) refl (i ∧ k ∧ ~ s)) r
                   ; (k = i0) → push* (false , inlR (false , g false false))
                                       ((push* (false , g false true) (g true true , g false true) refl i)
                                      , (inlR (false , g false false)))
                                       refl r
                   ; (k = i1) → h r i j
                   })
            (inlR (false , inlR (false , g false false)))
    where
    hah : ∀ {ℓ} {A : Type ℓ} {x : A} (y : A) (p : x ≡ y) -- s k j
      → Cube (λ k j → p (~ k ∨ j)) (λ _ _ → x)
              (λ s j → p (~ s)) (λ s j → p (j ∧ ~ s))
              (λ s k → p (~ s ∧ ~ k)) λ i _ → p (~ i)
    hah = J> refl 
  
    h : Cube (λ _ _ → inlR (false , inlR (false , g false false)))
             (λ i j → GFUN A (G-inr-inl-inr*₂-b-fill (RP∞'· ℓ) A g false i j i1))
             (λ r j → push* (false , inlR (false , g false false))
                             (inlR (false , g false true) , inlR (false , g false false))
                             refl (j ∧ r))
             (λ r j → push* (false , inlR (false , g false false))
                             (push* (true , g true true) (g true true , g false true) refl j
                            , push* (false , g false false) (g true false , g false false) refl j)
                            (λ s →  push* (false , g false false) (g true false , g false false) refl (j ∧ ~ s))
                            r)
             (λ r i → G-coh-eq1-fill (λ i₁ → g i₁ i₁) (g false) refl i i1 r)
             λ r i → push* (false , inlR (false , g false false))
                            (push* (false , g false true) (g true true , g false true) refl i
                           , push* (false , g false false) (g true false , g false false) refl i)
                            (λ s →  push* (false , g false false) (g true false , g false false) refl (i ∧ ~ s))
                            r
    h r i j =
        hcomp (λ k → λ {(i = i0) → push* (false , inlR (false , g false false))
                                          ((push* (false , g false true) (g true true , g false true) refl (~ k))
                                         , (push* (false , g false false) (g true false , g false false) refl (~ k)))
                                          (λ s → push* (false , g false false) (g true false , g false false) refl (~ k ∧ ~ s)) (r ∧ j)
                   ; (i = i1) → push* (false , inlR (false , g false false))
                                       ((push* (true , g true true) (g true true , g false true) refl (~ k ∨ j))
                                      , (push* (false , g false false) (g true false , g false false) refl (~ k ∨ j)))
                                       (λ s → hah _ (push* (false , g false false) (g true false , g false false) refl) s k j) r
                   ; (j = i0) → push* (false , inlR (false , g false false))
                                       ((push* (true , g true true) (g true true , g false true) refl (~ k))
                                       , (push* (false , g false false) (g true false , g false false) refl (~ k)))
                                       (λ t → push* (false , g false false) (g true false , g false false) refl (~ k ∧ ~ t)) (i ∧ r)
                   ; (j = i1) → push* (false , inlR (false , g false false))
                                       ((push* (false , g false true) (g true true , g false true) refl (~ k ∨ i))
                                       , (push* (false , g false false) (g true false , g false false) refl (~ k ∨ i)))
                                       (λ s → hah _ (push* (false , g false false) (g true false , g false false) refl) s k i) r
                   ; (r = i0) → inlR (false , inlR (false , g false false))
                   ; (r = i1) → GFUN A (G-inr-inl-inr*₂-b-fill (RP∞'· ℓ) A g false i j k)
                   })
           (push* (false , inlR (false , g false false))
          (inrR (g true true , g false true) ,
           inrR (g true false , g false false))
          (sym (push* (false , g false false) (g true false , g false false) refl))
          ((i ∨ j) ∧ r))
  G-coh-eq2-main g true k i j =
    hcomp (λ r → λ {(i = i0) → GFUN A (btm-map (RP∞'· ℓ) (RP∞'· ℓ) A
                                  (true , leftFun-cohₗ**-fill (RP∞'· _) (RP∞'· _) A true true (idEquiv Bool) refl g j k r))
                   ; (i = i1) → inrR ((push* (true , g true true) (g true true , g false true) refl (j ∨ ~ k)
                               , push* (false , g false false) (g true false , g false false) refl (j ∧ k)))
                   ; (j = i0) → push* (true , inlR (true , g true true))
                                        (push* (true , g true true) (g true true , g false true) refl (~ k)
                                        , inlR (false , g false false))
                                       (λ s → push* (true , g true true) (g true true , g false true)
                                          (λ _ → g true true) (~ k ∧ ~ s)) i
                   ; (j = i1) → cong-GFUN r i k
                   ; (k = i0) → push* (true , inlR (true , g true true))
                                       (inrR (g true true , g false true) , inlR (false , g false false))
                                       (sym (push* (true , g true true) (g true true , g false true) refl)) i
                   ; (k = i1) → GFUN A (G-inr-inl-inr*₂-b-fill (RP∞'· ℓ) A g true i j i1)
                   })
       (hcomp (λ r → λ {(i = i0) → push* (true , inlR (true , g true true))
                                            (inlR (true , g true true) , inlR (true , g true false))
                                            (λ i₁ → inlR (true , g true true)) (j ∧ (k ∧ r))
                   ; (i = i1) → push* (true , inlR (true , g true true))
                                       ((push* (true , g true true) (g true true , g false true)
                                               refl (j ∨ ~ k))
                                      , (push* (false , g false false) (g true false , g false false) refl (j ∧ k)))
                                       (λ s → push* (true , g true true) (g true true , g false true)
                                                     refl ((~ k ∨ j) ∧ (~ s))) r
                   ; (j = i0) → push* (true , inlR (true , g true true))
                                       (push* (true , g true true) (g true true , g false true)
                                        refl (~ k)
                                        , inlR (false , g false false))
                                       (λ s → push* (true , g true true) (g true true , g false true)
                                                     refl (~ k ∧ ~ s))
                                       (i ∧ r)
                   ; (j = i1) → G-coh-inr-t-fill g i k r
                   ; (k = i0) → push* (true , inlR (true , g true true))
                                       (inrR (g true true , g false true) , inlR (false , g false false))
                                       (sym (push* (true , g true true) (g true true , g false true) refl))
                                       (i ∧ r)
                   ; (k = i1) → F2 r i j
                   })
              (inlR (true , inlR (true , g true true))))
    where -- r i j
    F2 : Cube (λ _ _ → inlR (true , inlR (true , g true true)))
              (λ i j → GFUN A (G-inr-inl-inr*₂-b-fill (RP∞'· ℓ) A g true i j i1))
              (λ r j → push* (true , inlR (true , g true true))
                              (inlR (true , g true true) , inlR (true , g true false))
                              refl (j ∧ r))
              (λ r j → push* (true , inlR (true , g true true))
                              (push* (true , g true true) (g true true , g false true) refl j
                             , push* (false , g false false) (g true false , g false false) refl j)
                              (λ s → push* (true , g true true) (g true true , g false true) refl (j ∧ ~ s)) r)
              (λ r i → push* (true , inlR (true , g true true))
                              (inlR (true , g true true) , inlR (false , g false false))
                              refl (i ∧ r))
              λ r i → G-coh-inr-t-fill g i i1 r
    F2 r i j =
      hcomp (λ k → λ {(i = i0) → push* (true , inlR (true , g true true))
                                          (push* (true , g true true) (g true true , g false true) refl (~ k)
                                        , push* (true , g true false) (g true false , g false false) refl (~ k))
                                          (λ i₂ → push* (true , g true true)
                                                         (g true true , g false true) refl (~ k ∧ ~ i₂)) (r ∧ j)
                   ; (i = i1) →  push* (true , inlR (true , g true true))
                                        ((push* (true , g true true) (g true true , g false true) refl (~ k ∨ j))
                                       , (push* (false , g false false) (g true false , g false false) refl (~ k ∨ j)))
                                        (λ t → push* (true , g true true) (g true true , g false true) refl ((j ∨ ~ k) ∧ (~ t))) r
                   ; (j = i0) → push* (true , inlR (true , g true true))
                                       ((push* (true , g true true) (g true true , g false true) refl (~ k))
                                       , (push* (false , g false false) (g true false , g false false) refl (~ k)))
                                       (λ i → push* (true , g true true) (g true true , g false true) refl (~ i ∧ ~ k))
                                       (r ∧ i)
                   ; (j = i1) → push* (true , inlR (true , g true true))
                                       ((push* (true , g true true) (g true true , g false true) refl (~ k ∨ i))
                                     , (push* (true , g true false) (g true false , g false false) refl (~ k ∨ i)))
                                       (λ t → push* (true , g true true) (g true true , g false true) refl (~ t ∧ (i ∨ ~ k))) r
                   ; (r = i0) → inlR (true , inlR (true , g true true))
                   ; (r = i1) → GFUN A (G-inr-inl-inr*₂-b-fill (RP∞'· ℓ) A g true i j k)
                   })
                  (push* (true , inlR (true , g true true))
                         (inrR (g true true , g false true)
                        , inrR (g true false , g false false))
                         (sym (push* (true , g true true) (g true true , g false true) refl))
                         (r ∧ (i ∨ j)))

    cong-GFUN : Cube (λ i k → G-coh-inr-t-fill g i k i1)
                     (λ i k → G-coh-inr-t-fill g i k i1)
                     (λ r k → push* (true , inlR (true , g true true))
                                      (inlR (true , g true true) , inlR (true , g true false))
                                      refl k)
                     (λ r k → inrR (inrR (g true true , g false true)
                             , push* (false , g false false) (g true false , g false false) refl k))
                     (λ r i → push* (true , inlR (true , g true true))
                                       (inrR (g true true , g false true) , inlR (false , g false false))
                                       (sym (push* (true , g true true) (g true true , g false true) refl)) i)
                     λ r i → inrR (push* (true , g true true) (g true true , g false true) refl i
                            , push* (true , g true false) (g true false , g false false) refl i)
    cong-GFUN r i k =
      hcomp (λ j → λ {(r = i0) → G-coh-inr-t-fill g i k j
                   ; (r = i1) → G-coh-inr-t-fill g i k j
                   ; (i = i0) → G-coh-inr-t-fill g i k j
                   ; (i = i1) → G-coh-inr-t-fill g i k j
                   ; (k = i0) → G-coh-inr-t-fill g i k j
                   ; (k = i1) → G-coh-inr-t-fill g i k j
                   })
              (inlR (true , inlR (true , g true true)))

  G-coh-eq2 : (g : (i j : Bool) → A i j)
      (x : Bool) →
      Cube
      (λ i _ → G-inler (g true true) (g false) x i)
      (λ s t →
         GFUN A
         (G-inr-inl-inr*₂ (RP∞'· ℓ) A g x (λ i → g i i) refl s t))
      (λ i j → GFUN A
         (btm-map (RP∞'· ℓ) (RP∞'· ℓ) A
          (x , leftMapBool (RP∞'· ℓ) A x
           (push (true , true , push (inr (idEquiv Bool , refl , g)) j) i)))) -- ()
      (λ i j → coh-eq2 g j i) -- (G-coh-inr g x)
      (λ i j → G-coh-eq1 (λ i → g i i) (g false) refl x j i)
      λ i j → G-coh-inr g x j i
  G-coh-eq2 g x =
    G-coh-eq2-main g x
    ▷ λ a s t → GFUN A (G-inr-inl-inr*₂-refl (RP∞'· ℓ) A g x (~ a) s t)

open 𝕄
𝕄inst· : ∀ {ℓ} → 𝕄inst {ℓ = ℓ}
inler 𝕄inst· = Sol.inler
inr-inr 𝕄inst· = inrerr
inr-inl-inl 𝕄inst· = inr-inl-inl*
inr-inl-inr 𝕄inst· = inr-inl-inr*
push-inl 𝕄inst· = Sol.push-inl
coh-inr 𝕄inst· = Sol.coh-inr
coh-eq1 𝕄inst· = Sol.coh-eq1
coh-eq2 𝕄inst· = Sol.coh-eq2
coh-eq-l 𝕄inst· = Sol.coh-eq-l
G-inler 𝕄inst· = Sol.G-inler
G-inr-inr 𝕄inst· = G-inr-inr*
G-inr-inl-inl₁ 𝕄inst· = G-inr-inl-inl*₁
G-inr-inl-inl₂ 𝕄inst· = G-inr-inl-inl*₂
G-inr-inl-inr₁ 𝕄inst· = G-inr-inl-inr*₁
G-inr-inl-inr₂ 𝕄inst· I A f p q i = G-inr-inl-inr*₂ I A p i f (funExt q)
G-push-inl 𝕄inst· = Sol.G-push-inl
G-coh-inr 𝕄inst· = Sol.G-coh-inr
G-coh-eq1 𝕄inst· = Sol.G-coh-eq1
G-coh-eq2 𝕄inst· A g x i j k = Sol.G-coh-eq2 A g x k i j
G-coh-eq-l 𝕄inst· = {!!}

TheId : ∀ {ℓ} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
  → Better! I J A → GOALTY I J A
TheId {ℓ = ℓ} I J A = elimPushout (btm-map I J A) (FF I J A .fst) λ {(i , x) → FF I J A .snd i x}
  where
  FF = MEGA-inst (λ I J A _ → GOALTY I J A) (λ A _ → GOALTY' A) (λ A _ → GFUNEq A)
                 (λ I J A x i → btm-map I J A (i , leftMap** I J A i x))
                 (λ A x a j → GFUN A (btm-map (RP∞'· ℓ) (RP∞'· ℓ) A (a , leftMapBool (RP∞'· ℓ) A a (push x j))))
                 (λ t A x y i → GFUN A (btm-map (RP∞'· ℓ) (RP∞'· ℓ) A (y , leftMapBool≡ (RP∞'· ℓ) A y (push x i) (~ t))))
                 𝕄inst·
