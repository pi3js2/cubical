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
module Cubical.Cohomology.EilenbergMacLane.nov.boolcase where
open import Cubical.HITs.Join
open import Cubical.Functions.FunExtEquiv

EquivJ' : ∀ {ℓ ℓ'} {B : Type ℓ} {P : (A : Type ℓ) → A ≃ B → Type ℓ'}
         → P B (idEquiv _)
         → (A : _) (e : _) → P A e 
EquivJ' {P = P} ind A = EquivJ P ind

PushoutR-equiv :
  ∀ {ℓ ℓ' ℓ''} {A' : Type ℓ} {B' : Type ℓ'}
    → (A : Type ℓ) (e : A ≃ A') (B : Type ℓ') (e2 : B ≃ B')
    → (R : A → B → Type ℓ'')
       (R' : A' → B' → Type ℓ'')
    → ((a : A) (b : B) → R a b ≃ R' (fst e a) (fst e2 b))
    → PushoutR A B R ≃ PushoutR A' B' R'
PushoutR-equiv {A' = A'} {B' = B'} =
  EquivJ'
    (EquivJ' λ R R' s
      → help _ _ (funExt λ a → funExt λ b → ua (s a b)))
  where
  help : ∀ {ℓ} (R R' : A' → B' → Type ℓ) → R ≡ R' → PushoutR A' B' R ≃ PushoutR A' B' R'
  help R = J> idEquiv _

joinR-Push : ∀ {ℓ ℓ'} (A : Type ℓ) (B : A → Type ℓ') → Type _
joinR-Push A B = Pushout {A = A × TotΠ B} (λ a → fst a , snd a (fst a)) snd

module _ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} where
  private
    F : joinR-Push A B → joinR-gen A B
    F (inl x) = inlR x
    F (inr x) = inrR x
    F (push (i' , a) i) = push* (i' , a i') a refl i

  joinR-Equiv : Iso (joinR-gen A B) (joinR-Push A B)
  Iso.fun joinR-Equiv (inlR x) = inl x
  Iso.fun joinR-Equiv (inrR x) = inr x
  Iso.fun joinR-Equiv (push* a b x i) =
    ((λ i → inl (fst a , x (~ i))) ∙ push (fst a , b)) i
  Iso.inv joinR-Equiv = F
  Iso.rightInv joinR-Equiv (inl x) = refl
  Iso.rightInv joinR-Equiv (inr x) = refl
  Iso.rightInv joinR-Equiv (push a i) j = lUnit (push a) (~ j) i
  Iso.leftInv joinR-Equiv (inlR x) = refl
  Iso.leftInv joinR-Equiv (inrR x) = refl
  Iso.leftInv joinR-Equiv (push* a b x i) j =
    hcomp (λ k → λ{(i = i0) → inlR (fst a , x k)
                  ; (i = i1) → inrR b
                  ; (j = i0) → F (compPath-filler' (λ i → inl (fst a , x (~ i)))
                                         (push (fst a , b)) k i)
                  ; (j = i1) → push* (fst a , x k) b (λ i → x (i ∧ k)) i})
          (push* (fst a , b (fst a)) b (λ _ → b (fst a)) i)

doubleJoin : ∀ {ℓ} (I : RP∞' ℓ) (J : Type) (A : fst I → J → Type ℓ) → Type ℓ
doubleJoin I J A = joinR-Push (fst I) λ i → joinR-gen J (A i)


module _ {ℓ : Level} (J : Type) (A : Bool → J → Type ℓ) where
  leftFun : 2-elter.ΠR-extend (RP∞'· ℓ) J A → joinR-gen J (A true)
  leftFun (inl (false , t , p)) = inrR p
  leftFun (inl (true , t , p)) = inlR t
  leftFun (inr (inl x)) = inlR (x true)
  leftFun (inr (inr x)) = inrR (x true)
  leftFun (inr (push (t , s , q) i)) = push* (t true) (s true) (q true) i
  leftFun (push (false , inl (f , g , h)) i) = push* (f true) g h (~ i)
  leftFun (push (true , inl (f , s)) i) = inlR (f true)
  leftFun (push (false , inr (a , b)) i) = inrR (fst b true)
  leftFun (push (true , inr (a , b)) i) = push* a (fst b true) (snd b) i
  leftFun (push (false , push (a , b) j) i) = push* (a true) (fst b true) (snd b true) (~ i ∨ j)
  leftFun (push (true , push (a , b) j) i) = push* (a true) (fst b true) (snd b true) (j ∧ i)

leftFunExtCurry : {ℓ : Level} (I : RP∞' ℓ) (i : fst I)
  (J : Type) (A : fst I → J → Type ℓ)
  → 2-elter.ΠR-extend I J A → joinR-gen J (A i)
leftFunExtCurry = JRP∞' leftFun


module _ {ℓ : Level} (I : RP∞' ℓ) (J : Type) (A : fst I → J → Type ℓ) where
  leftFunExt' : (i : fst I) → 2-elter.ΠR-extend I J A → joinR-gen J (A i)
  leftFunExt' i = leftFunExtCurry I i J A

  leftFunExt :  fst I × 2-elter.ΠR-extend I J A
             → Σ[ i ∈ fst I ] (joinR-gen J (A i))
  leftFunExt (i , p) = i , leftFunExt' i p

leftFunExtId : {ℓ : Level} (J : Type) (A : Bool → J → Type ℓ)
  → leftFunExt' (RP∞'· ℓ) J A true ≡ leftFun J A
leftFunExtId {ℓ = ℓ} J A i = lem i J A
  where
  lem : leftFunExtCurry (RP∞'· ℓ) true ≡ leftFun
  lem = JRP∞'∙ leftFun

joinR-Push' : ∀ {ℓ} (I : RP∞' ℓ) (J : Type) (A : fst I → J → Type ℓ) → Type ℓ 
joinR-Push' I J A = Pushout {A = fst I × 2-elter.ΠR-extend I J A} (leftFunExt I J A) snd

module _ {ℓ ℓ' : Level} (J : Type) (B : (I : RP∞' ℓ) (A : fst I → J → Type ℓ) → Type ℓ')
  (lef : (I : RP∞' ℓ) (A : fst I → J → Type ℓ) → 2-elter.ΠR-extend I J A → B I A)
  (ri : (A : Bool → J → Type ℓ) → joinR-gen J (A true) → B (RP∞'· ℓ) A)
  (coh : ((A : Bool → J → Type ℓ) (x : _) → lef (RP∞'· ℓ) A x ≡ ri A (leftFun J A x)))
  where
  inder : (I : RP∞' ℓ) (i : fst I) (A : fst I → J → Type ℓ)
    → Σ[ F ∈ (joinR-gen J (A i) → B I A) ]
              ((f : _) → F (leftFunExt I J A (i , f) .snd) ≡ lef I A f)
  inder = JRP∞' λ A → ri A , λ f → cong (ri A) (funExt⁻ (leftFunExtId J A) f) ∙ sym (coh A f) 

  joinR-Push'-rec : (I : RP∞' ℓ) (A : fst I → J → Type ℓ) → joinR-Push' I J A → B I A
  joinR-Push'-rec I A (inl (i , t)) = inder I i A .fst t
  joinR-Push'-rec I A (inr x) = lef I A x
  joinR-Push'-rec I A (push (i , t) k) = inder I i A .snd t k

FullIso₁ : ∀ {ℓ} (I : RP∞' ℓ) (J : RP∞' ℓ)
  (A : fst I → fst J → Type ℓ)
  → Iso (doubleJoin I (fst J) A) (joinR-Push' I (fst J) A)
FullIso₁ {ℓ = ℓ} I J A =
  pushoutIso _ _ _ _
    (Σ-cong-equiv-snd λ _ → invEquiv (_ , ΠR-extend→Π-equiv I J A))
     (idEquiv _)
     (invEquiv (_ , ΠR-extend→Π-equiv I J A))
     (funExt (λ {(i , f) → ΣPathP (refl , help J I i A f)}))
     refl
  where
  help : (J : RP∞' ℓ)  (I : RP∞' ℓ) (i : fst I)
    (A : fst I → fst J → Type ℓ)
    (f : TotΠ (λ i₁ → joinR-gen (fst J) (A i₁)))
    → f i ≡ leftFunExt' I (fst J) A i (invEq (_ , ΠR-extend→Π-equiv I J A) f)
  help J = JRP∞' λ A f
    → main J A (f true , f false)
    ∙ cong (leftFun (fst J) A) (sym (funExt⁻ (help' J A) f))
    ∙ sym (funExt⁻ (leftFunExtId (fst J) A) _) 
    where
    module _ (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ) where
      open ΠR-extend→Π-equiv-base-lemmas J A
      help' : invEq (2-elter.ΠR-extend→Π (RP∞'· ℓ) (fst J) A , ΠR-extend→Π-equiv (RP∞'· ℓ) J A)
            ≡ invEq alt
      help' = cong invEq (Σ≡Prop (λ _ → isPropIsEquiv _)
               (funExt λ f → funExt λ t → sym (ΠR-extend→Π-alt≡ A f t)
              ∙ funExt⁻ (funExt⁻ (sym altid) f) t))

      pre-main : (f : _) → ΠR-extend→× J A f .fst ≡ leftFun (fst J) A f
      pre-main (inl (false , b)) = refl
      pre-main (inl (true , b)) = refl
      pre-main (inr (inl x)) = refl
      pre-main (inr (inr x)) = refl
      pre-main (inr (push a i)) = refl
      pre-main (push (false , inl x) i) = refl
      pre-main (push (false , inr x) i) = refl
      pre-main (push (false , push a i₁) i) = refl
      pre-main (push (true , inl x) i) = refl
      pre-main (push (true , inr x) i) = refl
      pre-main (push (true , push a i₁) i) = refl

      main : (f : joinR-gen (fst J) (A true) × joinR-gen (fst J) (A false))
           → fst f
            ≡ leftFun (fst J) A (×→ΠR-extend J A f)
      main f = cong fst (sym (×→ΠR-extend→× {J = J} A f))
             ∙ pre-main (×→ΠR-extend J A f) 

module Rewrite1 {ℓ} (I : RP∞' ℓ) (J : Type) (A : fst I → J → Type ℓ) where
  module M = 2-elter I J A
  module _ (AB : Type ℓ) (AB→J : (i : fst I) → AB → J)
           (AB→A : (i : fst I) (a : AB) → A i (AB→J i a))  where
    fat-ab : Type ℓ
    fat-ab = Σ[ a ∈ AB ]
             Σ[ g ∈ ((i : fst I) (j : J) → A i j) ]
               ((i : fst I) → g i (AB→J i a) ≡ AB→A i a)
    ΠR-base-ab : Type ℓ
    ΠR-base-ab = Pushout {A = fat-ab} {B = AB} {C = ((i : fst I) (j : J) → A i j)}
                         fst (fst ∘ snd)

    left-push-ab : Type _
    left-push-ab = Σ[ i ∈ fst I ] (Σ[ j ∈ J ] (A i j)) × ((j : J) → A (M.notI i) j)

    left-push↑ₗ-ab : fst I → Type _
    left-push↑ₗ-ab i = Σ[ f ∈ AB ]
      Σ[ g ∈ ((j : J) → A (M.notI i) j) ] g (AB→J (M.notI i) f) ≡ AB→A (M.notI i) f

    left-push↑ᵣ-ab : fst I → Type _
    left-push↑ᵣ-ab i = Σ[ f ∈ (Σ[ j ∈ J ] A i j) ]
        Σ[ g ∈ ((i : fst I) (j : J) → A i j) ] g i (fst f) ≡ snd f

    fat→ₗ-ab : (i : fst I) → fat-ab → left-push↑ₗ-ab i
    fat→ₗ-ab  i (f , g , r) = (f , (g (M.notI i)) , (r (M.notI i)))

    fat→ᵣ-ab : (i : fst I) → fat-ab → left-push↑ᵣ-ab i
    fat→ᵣ-ab i (f , g , r) =  (AB→J i f , AB→A i f) , g , r i

    PushTop-ab : Type _
    PushTop-ab = Σ[ i ∈ fst I ] (Pushout (fat→ₗ-ab i) (fat→ᵣ-ab i))

    AB→Σ : (i : fst I) → AB → Σ J (A i)
    fst (AB→Σ a f) = AB→J a f
    snd (AB→Σ a f) = AB→A a f

    PushTop→left-push'-ab : (i : fst I)
      → (Pushout (fat→ₗ-ab i) (fat→ᵣ-ab i))
      → (Σ[ j ∈ J ] (A i j)) × ((j : J) → A (M.notI i) j)
    PushTop→left-push'-ab i (inl (f , g , p)) = AB→Σ i f , g
    PushTop→left-push'-ab i (inr (f , g , p)) = f , (g (M.notI i))
    PushTop→left-push'-ab i (push (f , g , p) k) = (AB→Σ i f) , g (M.notI i)

    PushTop→left-push-ab : PushTop-ab → left-push-ab
    PushTop→left-push-ab (i , x) = (i , PushTop→left-push'-ab i x)

    PushTop→ΠR-base-ab : PushTop-ab → ΠR-base-ab
    PushTop→ΠR-base-ab (i , inl (f , g , p)) = inl f
    PushTop→ΠR-base-ab (i , inr (f , g , p)) = inr g
    PushTop→ΠR-base-ab (i , push (f , g , p)  i₁) = push (f , g , p) i₁

    ΠR-extend-ab : Type _
    ΠR-extend-ab = Pushout PushTop→left-push-ab PushTop→ΠR-base-ab

  module _ (AB1 AB2 : Type ℓ) (is : AB1 ≃ AB2)
           (AB→J : (i : fst I) → AB1 → J)
           (AB→Tot : (i : fst I) (a : AB1) → A i (AB→J i a))
           where
    AB2→J : (i : fst I) → AB2 → J
    AB2→J i a = AB→J i (invEq is a)

    AB2→Tot : (i : fst I) (a : AB2) → A i (AB2→J i a)
    AB2→Tot i a = AB→Tot i (invEq is a)

    push-case-gen : (b : AB1) (i : fst I) (f : (j : J) → A i j)
                  → (p : f (AB→J i b) ≡ AB→Tot i b)
                  → (k r : _) → A i (AB→J i (retEq is b (~ r)))
    push-case-gen b i f p k r =
      fill (λ r → A i (AB→J i (retEq is b (~ r))))
           (λ r → λ {(k = i0) → f (AB→J i (retEq is b (~ r)))
                    ; (k = i1) → AB→Tot i (retEq is b (~ r))})
           (inS (p k))
           r

    inr-push-case : (b : AB1) (f : (i₂ : fst I) (j : J) → A i₂ j)
                    (c : (i₂ : fst I) → f i₂ (AB→J i₂ b) ≡ AB→Tot i₂ b)
                  → (i : fst I)
                  → f i (AB2→J i (fst is b)) ≡ AB2→Tot i (fst is b)
    inr-push-case b f c i k = push-case-gen b i (f i) (c i) k i1

    push-inl-case : (a : fst I) (c : AB1) (f : (j : J) → A (M.notI a) j)
                    (p : f (AB→J (M.notI a) c) ≡ AB→Tot (M.notI a) c)
                  → f (AB2→J (M.notI a) (fst is c)) ≡ AB2→Tot (M.notI a) (fst is c)
    push-inl-case a c f p k = push-case-gen c (M.notI a) f p k i1

    kalas : (a : fst I) (c : AB1)
            (f : (i₂ : fst I) (j : J) → A i₂ j)
            (p : (i₂ : fst I) → f i₂ (AB→J i₂ c) ≡ AB→Tot i₂ c)
         → Square {A = ΠR-extend-ab AB2 AB2→J AB2→Tot}
                   (λ _ → inl (a , AB→Σ AB1 AB→J AB→Tot a c , f (M.notI a)))
                   (λ r → inr (push (fst is c , f , λ k j → push-case-gen c k (f k) (p k) j i1) r))
                   ((λ i → inl (a , AB→Σ AB1 AB→J AB→Tot a (retEq is c (~ i)) , (f (M.notI a))))
                  ∙ push (a , inl (fst is c , f (M.notI a)
                                 , λ j → push-case-gen c (M.notI a) (f (M.notI a)) (p (M.notI a)) j i1)))
                   (push (a , inr ((AB→J a c , AB→Tot a c) , f , p a)))
    kalas a c f p i j =
      hcomp (λ r → λ {(i = i0) → inl (a , AB→Σ AB1 AB→J AB→Tot a (retEq is c r) , f (M.notI a))
                     ; (i = i1) → inr (push (fst is c , f , (λ k j → push-case-gen c k (f k) (p k) j i1)) j)
                     ; (j = i0) → compPath-filler'
                                    (λ i → inl (a , AB→Σ AB1 AB→J AB→Tot a (retEq is c (~ i)) , (f (M.notI a))))
                                    (push (a , inl (fst is c , f (M.notI a)
                                             , λ j → push-case-gen c (M.notI a)
                                                       (f (M.notI a)) (p (M.notI a)) j i1))) r i
                     ; (j = i1) → push (a , inr (AB→Σ AB1 AB→J AB→Tot a (retEq is c r)
                                 , f
                                 , (λ j → push-case-gen c a (f a) (p a) j (~ r)))) i})
            (push (a , push (fst is c , f , (λ k j → push-case-gen c k (f k) (p k) j i1)) j) i)

    ΠR-extend-ab-iso : ΠR-extend-ab AB1 AB→J AB→Tot
                    → ΠR-extend-ab AB2 AB2→J AB2→Tot
    ΠR-extend-ab-iso (inl x) = inl x
    ΠR-extend-ab-iso (inr (inl x)) = inr (inl (fst is x))
    ΠR-extend-ab-iso (inr (inr x)) = inr (inr x)
    ΠR-extend-ab-iso (inr (push (b , f , p) i)) = inr (push (fst is b , f , inr-push-case b f p) i)
    ΠR-extend-ab-iso (push (a , inl (c , f , p)) i) =
      ((λ j → inl (a , ((AB→J a (retEq is c (~ j)))
                      , AB→Tot a (retEq is c (~ j)))
                 , f))
      ∙ push (a , inl (fst is c , f , push-inl-case a c f p))) i
    ΠR-extend-ab-iso (push (a , inr x) i) = push (a , inr x) i
    ΠR-extend-ab-iso (push (a , push (c , f , p) i₁) i) = kalas a c f p i i₁

  Iso1 : Iso M.ΠR-extend (ΠR-extend-ab ((i : fst I) → Σ[ j ∈ J ] A i j)
                         (λ i f → f i .fst)
                         λ i f → f i .snd)
  Iso.fun Iso1 (inl x) = inl x
  Iso.fun Iso1 (inr x) = inr x
  Iso.fun Iso1 (push (a , inl x) i) = push (a , inl x) i
  Iso.fun Iso1 (push (a , inr x) i) = push (a , inr x) i
  Iso.fun Iso1 (push (a , push a₁ i₁) i) = push (a , push a₁ i₁) i
  Iso.inv Iso1 (inl x) = inl x
  Iso.inv Iso1 (inr x) = inr x
  Iso.inv Iso1 (push (a , inl x) i) = push (a , inl x) i
  Iso.inv Iso1 (push (a , inr x) i) = push (a , inr x) i
  Iso.inv Iso1 (push (a , push a₁ i₁) i) = push (a , push a₁ i₁) i
  Iso.rightInv Iso1 (inl x) = refl
  Iso.rightInv Iso1 (inr x) = refl
  Iso.rightInv Iso1 (push (fst₁ , inl x) i) = refl
  Iso.rightInv Iso1 (push (fst₁ , inr x) i) = refl
  Iso.rightInv Iso1 (push (fst₁ , push a i₁) i) = refl
  Iso.leftInv Iso1 (inl x) = refl
  Iso.leftInv Iso1 (inr x) = refl
  Iso.leftInv Iso1 (push (fst₁ , inl x) i) = refl
  Iso.leftInv Iso1 (push (fst₁ , inr x) i) = refl
  Iso.leftInv Iso1 (push (fst₁ , push a i₁) i) = refl

ΠR-extend-ab-bool : {!!}
ΠR-extend-ab-bool = {!!}

-- 2-elter.ΠR-extend
Lift→ : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'}
  (f : A → B) → Lift {j = ℓ''} A → Lift {j = ℓ''} B
Lift→ f (lift a) = lift (f a)

-- TODO --verify is iso
ΠR-extend* : (I J : RP∞' ℓ-zero) (A : fst I → fst J → Type ℓ-zero)
  → Rewrite1.ΠR-extend-ab I (fst J) A
       (Σ[ x ∈ fst J ⊎ (fst I ≃ fst J) ]
         ((i : fst I) → A i (fst (2-eltFun {I = I} {J = J}) x i)))
       (λ i p → Iso.inv (TotAIso I J {A}) p i .fst)
       (λ i x → Iso.inv (TotAIso I J {A}) x i .snd)
  → Rewrite1.ΠR-extend-ab I (fst J) A
       ((i : fst I) → Σ[ j ∈ fst J ] A i j)
       (λ i f → f i .fst)
       λ i f → f i .snd
ΠR-extend* I J A (inl x) = inl x
ΠR-extend* I J A (inr (inl x)) = inr (inl (Iso.inv (TotAIso I J {A}) x))
ΠR-extend* I J A (inr (inr x)) = inr (inr x)
ΠR-extend* I J A (inr (push ((x , s2) , q , t) i)) =
  inr (push ((Iso.inv (TotAIso I J {A}) (x , s2)) , q , t) i)
ΠR-extend* I J A (push (i' , inl (a , b)) i) =
  push (i' , inl (Iso.inv (TotAIso I J {A}) a , b)) i
ΠR-extend* I J A (push (i' , inr x) i) =
  push (i' , inr x) i
ΠR-extend* I J A (push (i' , push (a , b) i₁) i) =
  push (i' , push ((Iso.inv (TotAIso I J {A}) a) , b) i₁) i

thePush'' : {!!}
thePush'' = {!!}

ΠR-extend-iso : {!!}
ΠR-extend-iso = {!!}


-- module BoolC {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ) where
--   open 2-elter (RP∞'· ℓ) (fst J) A
--   left-push→' : left-push → joinR-gen (fst J) (A true)
--   left-push→' (false , t , f) = inrR f
--   left-push→' (true , t , f) = inlR t

--   ΠR-base→' : ΠR-base → joinR-gen (fst J) (A true)
--   ΠR-base→' (inl x) = inlR (x true)
--   ΠR-base→' (inr x) = inrR (x true)
--   ΠR-base→' (push (a , b , c) i) = push* (a true) (b true) (c true) i

--   cohs : (a : Bool) (b : Pushout (fat→ₗ a) (fat→ᵣ a))
--        → left-push→' (a , PushTop→left-push' a b) ≡ ΠR-base→' (PushTop→ΠR-base (a , b))
--   cohs false (inl (a , b , c)) = sym (push* (a true) b c) 
--   cohs false (inr x) = refl
--   cohs false (push (a , b , c) i) j = push* (a true) (b true) (c true) (i ∨ ~ j)
--   cohs true (inl (a , b , c)) = refl
--   cohs true (inr (a , b , c)) = push* a (b true) c
--   cohs true (push (a , b , c) i) j = push* (a true) (b true) (c true) (i ∧ j)

--   T : ΠR-extend → joinR-gen (fst J) (A true)
--   T (inl x) = left-push→' x
--   T (inr x) = ΠR-base→' x
--   T (push (a , b) i) = cohs a b i

--   T-alt : ΠR-extend → joinR-gen (fst J) (A true)
--   T-alt x = ΠR-extend→Π x true

--   idPL : (x : _) → left-push→' x ≡ T-alt (inl x)
--   idPL (false , b) = refl
--   idPL (true , b) = refl

--   idP : (x : ΠR-extend) → T x ≡ T-alt x
--   idP x = l x ∙ ΠR-extend→Π-alt≡ {J = J} A x true
--     where
--     l : (x : _) → T x ≡ ΠR-extend→Π-alt J A x true
--     l (inl (false , snd₁)) = refl
--     l (inl (true , snd₁)) = refl
--     l (inr (inl x)) = refl
--     l (inr (inr x)) = refl
--     l (inr (push a i)) = refl
--     l (push (false , inl x) i) = refl
--     l (push (false , inr x) i) = refl
--     l (push (false , push a i₁) i) = refl
--     l (push (true , inl x) i) = refl
--     l (push (true , inr x) i) = refl
--     l (push (true , push a i₁) i) = refl

--   module MM = 2-elter' (RP∞'· ℓ) (fst J) A

--   left-push→2 : MM.left-push → joinR-gen (fst J) (A true)
--   left-push→2 (false , a , b) = inrR b
--   left-push→2 (true , a , b) = inlR a

--   ΠR-base→2 : MM.ΠR-base → joinR-gen (fst J) (A true)
--   ΠR-base→2 (inl (inl x , b)) = inlR (x , b true)
--   ΠR-base→2 (inl (inr x , b)) = inlR ((fst x true) , (b true))
--   ΠR-base→2 (inr x) = inrR (x true)
--   ΠR-base→2 (push (inl x , b) i) = push* (x , b true x) (b true) refl i
--   ΠR-base→2 (push (inr x , b) i) = push* (fst x true , b true (fst x true)) (b true) refl i

--   coh-false : (s : _) → left-push→2 (false , MM.PushTop→left-push' false s) ≡ ΠR-base→2 (MM.PushTop→ΠR-base (false , s))
--   coh-false (inl (inl x , (a , b))) = sym (push* (x , b x) b refl)
--   coh-false (inl (inr x , (a , b))) = sym (push* (fst x true , b (fst x true)) b refl)
--   coh-false (inr x) = refl
--   coh-false (push (inl x , b) i) j = {!!}
--   coh-false (push (inr x , b) i) = {!!}

--   T-alt2 : MM.ΠR-extend → joinR-gen (fst J) (A true)
--   T-alt2 (inl x) = left-push→2 x
--   T-alt2 (inr x) = ΠR-base→2 x
--   T-alt2 (push (f , s) i) = {!s!}
  

-- -- module _ (I J : RP∞' ℓ-zero) {A : fst I → fst J → Type} where
-- --   private
-- --     GOAL = joinR-gen (fst J) λ j → joinR-gen (fst I) λ x → A x j
-- --   module IM = 2-elter' I (fst J) A
-- --   module JM = 2-elter' J (fst I) (λ x y → A y x)

-- --   extenderₗ : IM.left-push → GOAL
-- --   extenderₗ (i , (j , a) , f) = inrR (JM.elimI j (inrR (IM.elimI i a (f j))) (inlR (IM.notI i , f (JM.notI j))))

-- --   extenderᵣ : IM.ΠR-base → GOAL
-- --   extenderᵣ (inl (inl j , p)) = inlR (j , inrR p)
-- --   extenderᵣ (inl (inr e , p)) = inrR λ j → inlR ((invEq e j) , {!e!})
-- --   extenderᵣ (inr x) = inrR λ j → inrR (λ i → x i j)
-- --   extenderᵣ (push a i) = {!!}
  
-- --   extender : IM.ΠR-extend → GOAL
-- --   extender (inl x) = extenderₗ x
-- --   extender (inr x) = extenderᵣ x
-- --   extender (push (a , inl (inl x , p)) i) = {!!}
-- --   extender (push (a , inl (inr x , p)) i) = {!!}
-- --   extender (push (a , inr x) i) = {!!}
-- --   extender (push (a , push a₁ i₁) i) = {!!}

-- -- module _ (J : RP∞' ℓ-zero) {A : Bool → fst J → Type} where
-- --   open 2-elter' J Bool (λ x y → A y x)
-- --   private
-- --     GOAL = joinR-gen (fst J) λ j → joinR-gen Bool λ x → A x j

-- --   inl-inlₗ : (x : fst J) (f : A true x) (f' : A false x) → GOAL
-- --   inl-inlₗ x f f' = inlR (x , inrR (CasesBool true f f'))

-- --   inl-inlᵣ : (x : fst J) (f : A true x) (f' : A false (notI x)) → GOAL
-- --   inl-inlᵣ x f f' = inrR (elimI x (inlR (true , f)) (inlR (false , f')))

-- --   inl-inl : (x : fst J) → (A true x) → (x' : fst J) → A false x' → GOAL
-- --   inl-inl x f = elimI x (inl-inlₗ x f) (inl-inlᵣ x f)

-- --   inl-inlₗid : (x : fst J) (f : A true x) (f' : A false x) → inl-inl x f x f' ≡ inl-inlₗ x f f'
-- --   inl-inlₗid x f f' = funExt⁻ (elimIβ x (inl-inlₗ x f) (inl-inlᵣ x f) .fst) f'

-- --   inl-inlᵣid : (x : fst J) (f : A true x) (f' : A false (notI x)) → inl-inl x f (notI x) f' ≡ inl-inlᵣ x f f'
-- --   inl-inlᵣid x f f' = funExt⁻ (elimIβ x (inl-inlₗ x f) (inl-inlᵣ x f) .snd) f'

-- --   inl-pushₗ : (x : fst J) (f : A true x) (f' : A false x) (b : TotΠ (A false)) (x₁ : b x ≡ f')
-- --            → inl-inl x f x f'
-- --             ≡ inrR (elimI x (inrR (CasesBool true f (b x))) (inlR (false , b (notI x))))
-- --   inl-pushₗ x f f' b x₁ =
-- --       inl-inlₗid x f f'
-- --     ∙ push* (x , inrR (CasesBool true f f'))
-- --             _
-- --             (elimIβ x (inrR (CasesBool true f (b x)))
-- --                       (inlR (false , b (notI x))) .fst
-- --           ∙ λ i → inrR (CasesBool true f (x₁ i)))



-- --   inl-pushᵣ : (x : fst J) (f : A true x) (f' : A false (notI x)) (b : TotΠ (A false)) (x₁ : b (notI x) ≡ f')
-- --            → inl-inl x f (notI x) f'
-- --             ≡ inrR (elimI x (inrR (CasesBool true f (b x))) (inlR (false , b (notI x))))
-- --   inl-pushᵣ x f f' b x₁ =
-- --       inl-inlᵣid x f f'
-- --     ∙ cong inrR (funExt (elimI x (elimIβ x (inlR (true , f)) (inlR (false , f')) .fst
-- --                               ∙∙ push* (true , f) (CasesBool true f (b x)) refl
-- --                               ∙∙ sym (elimIβ x (inrR (CasesBool true f (b x))) (inlR (false , b (notI x))) .fst))
-- --                                  (elimIβ x (inlR (true , f)) (inlR (false , f')) .snd
-- --                                ∙∙ (λ j → inlR (false , x₁ (~ j)))
-- --                                ∙∙ sym (elimIβ x (inrR (CasesBool true f (b x))) (inlR (false , b (notI x))) .snd))))

-- --   inl-push : (x : fst J) (f : A true x) (x' : fst J) (f' : A false x') (b : TotΠ (A false)) (x₁ : b x' ≡ f')
-- --     → inl-inl x f x' f'
-- --      ≡ inrR (elimI x (inrR (CasesBool true f (b x))) (inlR (false , b (notI x))))
-- --   inl-push x f = elimI x (inl-pushₗ x f) (inl-pushᵣ x f)

-- --   ×→Goal : (x : joinR-gen (fst J) (A true) × joinR-gen (fst J) (A false))
-- --          → GOAL
-- --   ×→Goal (inlR (x , f) , inlR (x' , f')) = inl-inl x f x' f'
-- --   ×→Goal (inlR (x , f) , inrR y) = inrR (elimI x (inrR (CasesBool true f (y x))) (inlR (false , y (notI x))))
-- --   ×→Goal (inlR (j , f) , push* (j' , f') b x₁ i) = inl-push j f j' f' b x₁ i
-- --   ×→Goal (inrR x , inlR x₁) = {!!}
-- --   ×→Goal (inrR x , inrR x₁) = inrR λ j → inrR (CasesBool true (x j) (x₁ j))
-- --   ×→Goal (inrR x , push* a b x₁ i) = {!!}
-- --   ×→Goal (push* a b₁ x i , b) = {!!}

-- --   ⊎→Goal : joinR-gen (fst J) (A true) → GOAL
-- --   ⊎→Goal (inlR (j , a)) = inlR (j , inlR (true , a))
-- --   ⊎→Goal (inrR f) = inrR λ j → inlR (true , f j)
-- --   ⊎→Goal (push* a b x i) = push* (fst a , inlR (true , snd a)) (λ i → inlR (true , b i)) (λ i → inlR (true , x i)) i

-- --   coher : (f : _) → ×→Goal f ≡ ⊎→Goal (fst f)
-- --   coher f = {!f!}

-- --   LType : {!!}
-- --   LType = {!!}

-- -- module final {J : RP∞' ℓ-zero}
-- --          (main-fun : (I : RP∞' ℓ-zero) → {A : fst I → fst J → Type}
-- --                    → TotΠ (λ i → joinR-gen (typ J) (A i))
-- --                    → (joinR-gen (fst J) λ j → joinR-gen (fst I) λ i → A i j))
-- --          (main-fun-id : {A : Bool → fst J → Type}
-- --                      → (x : joinR-gen (fst J) (A true) × joinR-gen (fst J) (A false))
-- --                      → main-fun (RP∞'· ℓ-zero) {A = A} (Iso.inv ΠBool×Iso x)
-- --                       ≡ ×→Goal J x) where

-- --   mainₗ : (I : RP∞' ℓ-zero) (i : fst I) (A : fst I → fst J → Type)
-- --     → joinR-gen (fst J) (A i)
-- --     → joinR-gen (fst J) λ j → joinR-gen (fst I) λ i → A i j
-- --   mainₗ = JRP∞' λ A → ⊎→Goal J

-- --   mainₗ≡ : (A : _) → mainₗ (RP∞'· ℓ-zero) true A ≡ ⊎→Goal J
-- --   mainₗ≡ = funExt⁻ (JRP∞'∙ (λ A → ⊎→Goal J))

-- --   main : (I : RP∞' ℓ-zero) (A : fst I → fst J → Type)
-- --     → (joinR-gen (fst I) λ i → joinR-gen (fst J) (A i))
-- --     → joinR-gen (fst J) λ j → joinR-gen (fst I) λ i → A i j 
-- --   main I A (inlR (i , j)) = mainₗ I i A j
-- --   main I A (inrR x) = main-fun I x
-- --   main I A (push* (i , a) b x k) = help I i b a x k
-- --     where
-- --     help : (I : RP∞' ℓ-zero) (i : fst I) {A : fst I → fst J → Type}
-- --            (b : (i₁ : fst I) → joinR-gen (fst J) (A i₁))
-- --          → (a : joinR-gen (fst J) (A i)) 
-- --          → b i ≡ a
-- --          → mainₗ I i A a ≡ main-fun I b 
-- --     help = JRP∞' λ {A} → λ f → J> funExt⁻ (mainₗ≡ A) (f true)
-- --                                ∙ sym (coher J (f true , f false))
-- --                                ∙ sym (main-fun-id {A} (f true , f false))
-- --                                ∙ cong (main-fun (RP∞'· ℓ-zero))
-- --                                       (funExt λ { false → refl
-- --                                                 ; true → refl})


-- -- joinGen : ∀ {ℓ} (I : Type ℓ)(A : I → Type ℓ) → Type ℓ
-- -- joinGen I A = Pushout {A = I × TotΠ A} {B = Σ I A} (λ fi → (fst fi , snd fi (fst fi))) snd

-- -- join-funct : ∀ {ℓ} (I : Type ℓ) {A B : I → Type ℓ} (f : (i : I) → A i → B i) → joinGen I A → joinGen I B
-- -- join-funct I f (inl x) = inl (fst x , f (fst x) (snd x))
-- -- join-funct I f (inr x) = inr (λ k → f k (x k))
-- -- join-funct I f (push (i , g) k) = push (i , (λ x → f x (g x))) k

-- -- JoinEqFunct : ∀ {ℓ} (I J : Type ℓ) {A : I → J → Type ℓ}
-- --   → joinGen (I ≃ J) (λ e → joinGen J λ j → A (invEq e j) j)
-- --   → joinGen (I ≃ J) (λ e → joinGen I λ i → A i (fst e i))
-- -- JoinEqFunct {ℓ} I J {A = A} = join-funct (I ≃ J)
-- --   λ e → EquivJ (λ I e → (A : I → J → Type ℓ) → (joinGen J λ j → A (invEq e j) j)
-- --       → joinGen I λ i → A i (fst e i)) (λ A → idfun _) e A


-- -- module _ {ℓ} (I J : Type ℓ) {A : I → J → Type ℓ} (mk : (i : I) (j : J) → Σ[ e ∈ I ≃ J ] (fst e i ≡ j)) where
-- --   JoinEq'* :
-- --       (joinGen (I ≃ J) (λ e → joinGen J λ j → A (invEq e j) j))
-- --     → (joinGen I λ i → joinGen J λ j → A i j)
-- --   JoinEq'* (inl (e , t)) = {!!}
-- --   JoinEq'* (inr e) = inr λ i → {!!}
-- --   JoinEq'* (push (e , t) i) = {!!}
  

-- --   JoinEq' : (joinGen I λ i → joinGen J λ j → A i j)
-- --     → joinGen (I ≃ J) (λ e → joinGen J λ j → A (invEq e j) j)
-- --   JoinEq' (inl (i , inl (j , t))) = inl (mk i j .fst , inl (j , subst (λ k → A k j) {!snd (mk i j)!} t))
-- --   JoinEq' (inl (i , inr x)) = inr λ e → inl (fst e i , subst (λ k → A k (fst e i)) (sym (retEq e i)) (x (fst e i)))
-- --   JoinEq' (inl (i , push a i₁)) = {!!}
-- --   JoinEq' (inr x) = {!!}
-- --     where
-- --     s : (e : I ≃ J) (j : _) → joinGen J (λ j₁ → A (invEq e j) j₁) → A (invEq e j) j
-- --     s e j (inl x) = {!snd x!}
-- --     s e j (inr x) = x j
-- --     s e j (push a i) = {!!}
-- --   JoinEq' (push (e , t) i) = {!!}
