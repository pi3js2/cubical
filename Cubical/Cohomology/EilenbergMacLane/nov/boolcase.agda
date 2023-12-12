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

CubeP : ∀ {ℓ} (A : I → I → I → Type ℓ)
  {a₀₀₀ : A i0 i0 i0} {a₀₀₁ : A i0 i0 i1} {a₀₀₋ : PathP (λ i → A i0 i0 i) a₀₀₀ a₀₀₁}
  {a₀₁₀ : A i0 i1 i0} {a₀₁₁ : A i0 i1 i1} {a₀₁₋ : PathP (λ i → A i0 i1 i) a₀₁₀ a₀₁₁}
  {a₀₋₀ : PathP (λ j → A i0 j i0) a₀₀₀ a₀₁₀} {a₀₋₁ : PathP (λ j → A i0 j i1) a₀₀₁ a₀₁₁}
  (a₀₋₋ : SquareP (λ j k → A i0 j k) a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁)
  {a₁₀₀ : A i1 i0 i0} {a₁₀₁ : A i1 i0 i1}  {a₁₀₋ : PathP (λ k → A i1 i0 k) a₁₀₀ a₁₀₁}
  {a₁₁₀ : A i1 i1 i0} {a₁₁₁ : A i1 i1 i1} {a₁₁₋ : PathP (λ k → A i1 i1 k) a₁₁₀ a₁₁₁}
  {a₁₋₀ : PathP (λ j → A i1 j i0) a₁₀₀ a₁₁₀} {a₁₋₁ : PathP (λ j → A i1 j i1) a₁₀₁ a₁₁₁}
  (a₁₋₋ : SquareP (λ j k → A i1 j k) a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁)
  {a₋₀₀ : PathP (λ i → A i i0 i0) a₀₀₀ a₁₀₀} {a₋₀₁ : PathP (λ i → A i i0 i1) a₀₀₁ a₁₀₁}
  (a₋₀₋ : SquareP (λ i k → A i i0 k) a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁)
  {a₋₁₀ : PathP (λ i → A i i1 i0) a₀₁₀ a₁₁₀} {a₋₁₁ : PathP (λ i → A i i1 i1) a₀₁₁ a₁₁₁}
  (a₋₁₋ : SquareP (λ i k → A i i1 k) a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁)
  (a₋₋₀ : SquareP (λ i j → A i j i0) a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀)
  (a₋₋₁ : SquareP (λ i j → A i j i1) a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁)
  → Type ℓ
CubeP A a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁ =
  PathP (λ i → SquareP (λ j k → A i j k) (a₋₀₋ i) (a₋₁₋ i) (a₋₋₀ i) (a₋₋₁ i)) a₀₋₋ a₁₋₋

private
  Bool≃Bool-elim' : ∀ {ℓ} (A : Bool ≃ Bool → Type ℓ)
    → (a : A (idEquiv _)) (b : A notEquiv)
    → Σ[ f ∈ ((a : Bool) → A (Iso.inv Bool≃Charac a)) ] (f true ≡ a) × (f false ≡ b)
  fst (Bool≃Bool-elim' A a b) false = b
  fst (Bool≃Bool-elim' A a b) true = a
  snd (Bool≃Bool-elim' A a b) = refl , refl

  Bool≃Bool-elim : ∀ {ℓ} (A : Bool ≃ Bool → Type ℓ)
    → (a : A (idEquiv _)) (b : A notEquiv)
    → Σ[ f ∈ TotΠ A ] (f (idEquiv _) ≡ a) × (f notEquiv ≡ b)
  Bool≃Bool-elim  {ℓ} =
    transport (λ i → (A : isoToPath Bool≃Charac (~ i) → Type ℓ)
                     (a : A (ua-gluePt (isoToEquiv Bool≃Charac) (~ i) (idEquiv _)))
                     (b : A (ua-gluePt (isoToEquiv Bool≃Charac) (~ i) (notEquiv)))
                  → Σ[ f ∈ TotΠ A ] (f _ ≡ a) × (f _ ≡ b))
              λ A a b → (CasesBool true a b) , (refl , refl)

module _ {ℓ} (A : (e : Bool ≃ Bool) (p : fst e true ≡ true) → Type ℓ)
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

module RP' {ℓ} (I : RP∞' ℓ) where
  notI = snd I .fst .fst
  elimI : {B : fst I → Type ℓ} → _
  elimI {B = B} = snd I .fst .snd .snd B .fst
  elimIβ : {B : fst I → Type ℓ} → _
  elimIβ {B = B} = snd I .fst .snd .snd B .snd

fold : ∀ {ℓ} {A B : Type ℓ} → (f : A → B) → A ⊎ A → B
fold f = ⊎.rec f f

makeRP≃ : (I J : RP∞' ℓ-zero) (i : fst I) (j : fst J) → fst I ≃ fst J
makeRP≃ I J i j = isoToEquiv is
  where
  main : (I : RP∞' ℓ-zero) (i : fst I) (J : RP∞' ℓ-zero) (j : fst J) (x : _)
    → RP'.elimI I i j (RP'.notI J j) (RP'.elimI J j i (RP'.notI I i) x) ≡ x
  main = JRP∞' (JRP∞' λ { false → refl ; true → refl})

  is : Iso (fst I) (fst J)
  Iso.fun is = RP'.elimI I i j (RP'.notI J j)
  Iso.inv is = RP'.elimI J j i (RP'.notI I i)
  Iso.rightInv is = main I i J j
  Iso.leftInv is = main J j I i

funExtSq : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
  {f g h l : (x : A) → B x}
  {p : f ≡ g} {q : h ≡ l} {r : f ≡ h} {s : g ≡ l}
  → ((x : _) → Square (funExt⁻ p x) (funExt⁻ q x) (funExt⁻ r x) (funExt⁻ s x))
  → Square {A = (x : A) → B x} p q r s
funExtSq ind i j x = ind x i j

-- not≡RP∞'· : ∀ {ℓ} → RP∞'· ℓ ≡ RP∞'· ℓ
-- not≡RP∞'· = Σ≡Prop (isPropIsRP∞ _) (ua notEquiv)
-- I-elim : ∀ {ℓ} (A : (I : RP∞' ℓ) (i : fst I) → Type ℓ)
--   → (at : A (RP∞'· ℓ) true)
--   → (af : A (RP∞'· ℓ) false)
--   → (coh : PathP (λ j → A (not≡RP∞'· j) (ua-gluePt notEquiv j true)) at af)
--   → Σ[ F ∈ ((I : RP∞' ℓ) (i : fst I) → A I i) ]
--        (F (RP∞'· ℓ) true ≡ at)
--      × (F (RP∞'· ℓ) false ≡ af)
-- fst (I-elim A at af c) = JRP∞' at
-- snd (I-elim A at af c) = (JRP∞'∙ at) , {!!}

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

module _ {ℓ : Level} (I : RP∞' ℓ) (J : Type) (A : fst I → J → Type ℓ) where
  open 2-elter I J A
  leftFun'-inl : (i' : fst I) → Σ J (A i') → TotΠ (A (RP'.notI I i')) → (i : fst I) → joinR-gen J (A i)
  leftFun'-inl i' t p = RP'.elimI I {B = λ i → joinR-gen J (A i)} i' (inlR t) (inrR p)

  leftFun'-inr : (i : fst I) → 2-elter.ΠR-base I J A → joinR-gen J (A i)
  leftFun'-inr i (inl x) = inlR (x i)
  leftFun'-inr i (inr x) = inrR (x i)
  leftFun'-inr i (push (t , s , q) k) = push* (t i) (s i) (q i) k

  leftFun'-inlβ : (i : fst I) (a : _) (b : _)
    → (leftFun'-inl i a b i ≡ inlR a)
     × (leftFun'-inl i a b (RP'.notI I i) ≡ inrR b)
  fst (leftFun'-inlβ i a b) = RP'.elimIβ I i (inlR a) (inrR b) .fst
  snd (leftFun'-inlβ i a b) = RP'.elimIβ I i (inlR a) (inrR b) .snd

  leftFun'-pushₗ : (i' : fst I) (x : _)
     → inlR (PushTop→left-push' i' x .fst)
      ≡ leftFun'-inr i' (PushTop→ΠR-base (i' , x))
  leftFun'-pushₗ i' (inl x) = refl
  leftFun'-pushₗ i' (inr (a , b , c)) = push* a (b i') c
  leftFun'-pushₗ i' (push (a , b , c) i) j = push* (a i') (b i') (c i') (i ∧ j)

  leftFun'-pushᵣ : (i' : fst I) (x : _)
     → inrR (PushTop→left-push' i' x .snd)
      ≡ leftFun'-inr (RP'.notI I i') (PushTop→ΠR-base (i' , x))
  leftFun'-pushᵣ i' (inl (a , b , c)) = sym (push* (a (RP'.notI I i')) b c)
  leftFun'-pushᵣ i' (inr x) = refl
  leftFun'-pushᵣ i' (push (a , b , c) i) j =
    push* (a (RP'.notI I i')) (b (RP'.notI I i')) (c (RP'.notI I i')) (i ∨ ~ j)

  leftFun'-push : (i' : fst I) (x : _) (i : fst I)
    → leftFun'-inl i' (PushTop→left-push' i' x .fst) (PushTop→left-push' i' x .snd) i
    ≡ leftFun'-inr i (PushTop→ΠR-base (i' , x))
  leftFun'-push i' x =
    RP'.elimI I i' (leftFun'-inlβ i' (PushTop→left-push' i' x .fst)
                                     (PushTop→left-push' i' x .snd) .fst
                  ∙ leftFun'-pushₗ i' x)
                   (leftFun'-inlβ i' (PushTop→left-push' i' x .fst)
                                     (PushTop→left-push' i' x .snd) .snd
                  ∙ leftFun'-pushᵣ i' x)

  leftFun' :  (i : fst I) → 2-elter.ΠR-extend I J A → joinR-gen J (A i)
  leftFun' i (inl (i' , t , p)) = leftFun'-inl i' t p i
  leftFun' i (inr x) = leftFun'-inr i x
  leftFun' i (push (i' , x) k) = leftFun'-push i' x i k

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

module _ {ℓ : Level} (J : Type) (A : Bool → J → Type ℓ) where
  open 2-elter (RP∞'· ℓ) J A
  private
    leftFun'≡-inl : (x : left-push)
      → leftFun' (RP∞'· ℓ) J A true (inl x) ≡ leftFun J A (inl x)
    leftFun'≡-inl (false , t , p) = refl
    leftFun'≡-inl (true , t , p) = refl

    leftFun'≡-inr : (x : _)
      → leftFun' (RP∞'· ℓ) J A true (inr x) ≡ leftFun J A (inr x)
    leftFun'≡-inr (inl x) = refl
    leftFun'≡-inr (inr x) = refl
    leftFun'≡-inr (push a i) = refl

  leftFun'≡ : (x : _) → leftFun' (RP∞'· ℓ) J A true x ≡ leftFun J A x
  leftFun'≡ (inl x) = leftFun'≡-inl x
  leftFun'≡ (inr x) = leftFun'≡-inr x
  leftFun'≡ (push (false , b) i) = help i
    where
    main : (b : _) → PathP (λ i → inrR (PushTop→left-push' false b .snd)
                                  ≡ leftFun'≡-inr (PushTop→ΠR-base (false , b)) i)
                            (leftFun'-pushᵣ (RP∞'· ℓ) J A false b)
                            (cong (leftFun J A) (push (false , b)))
    main (inl x) = refl
    main (inr x) = refl
    main (push a i) = refl
    help : PathP (λ i → leftFun'-push (RP∞'· ℓ) J A false b true i
                        ≡ leftFun J A (push (false , b) i))
                 refl
                 (leftFun'≡-inr (PushTop→ΠR-base (false , b)))
    help = flipSquare (sym (lUnit _) ◁ main b)
  leftFun'≡ (push (true , b) i) = help i
     where
     main : (b : _) → PathP (λ i → inlR (PushTop→left-push' true b .fst)
                                  ≡ leftFun'≡-inr (PushTop→ΠR-base (true , b)) i)
                            (leftFun'-pushₗ (RP∞'· ℓ) J A true b)
                            (cong (leftFun J A) (push (true , b)))
     main (inl x) = refl
     main (inr x) = refl
     main (push a i) = refl

     help : PathP (λ i → leftFun'-push (RP∞'· ℓ) J A true b true i
                        ≡ leftFun J A (push (true , b) i))
                 refl
                 (leftFun'≡-inr (PushTop→ΠR-base (true , b)))
     help = flipSquare (sym (lUnit _) ◁ main b)

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
  module AB (AB : Type ℓ) (AB→J : (i : fst I) → AB → J)
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

    open AB
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

  Iso1 : Iso M.ΠR-extend (AB.ΠR-extend-ab ((i : fst I) → Σ[ j ∈ J ] A i j)
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

-- 2-elter.ΠR-extend
Lift→ : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'}
  (f : A → B) → Lift {j = ℓ''} A → Lift {j = ℓ''} B
Lift→ f (lift a) = lift (f a)

-- TODO --verify is iso

module _ {ℓ} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) where
  open Rewrite1 I (fst J) A
  open AB (Σ[ x ∈ fst J ⊎ (fst I ≃ fst J) ]
         ((i : fst I) → A i (fst (2-eltFun {I = I} {J = J}) x i)))
         (λ i p → Iso.inv (TotAIso I J {A}) p i .fst)
         (λ i x → Iso.inv (TotAIso I J {A}) x i .snd)
  ΠR-base-ab* : Type ℓ
  ΠR-base-ab* = ΠR-base-ab

  ΠR-Pushout-ab* : (i : fst I) → Type ℓ
  ΠR-Pushout-ab* i = Pushout (fat→ₗ-ab i) (fat→ᵣ-ab i)

  ΠR-extend* : Type ℓ
  ΠR-extend* = ΠR-extend-ab

  PushTop→ΠR-base-ab* : (i : fst I) → ΠR-Pushout-ab* i → ΠR-base-ab*
  PushTop→ΠR-base-ab* i x = PushTop→ΠR-base-ab (i , x)

  PushTop→left-push'-ab* : (i : fst I) → ΠR-Pushout-ab* i → Σ (fst J) (A i) × ((j : fst J) → A (M.notI i) j)
  PushTop→left-push'-ab* = PushTop→left-push'-ab


  module _ (i : fst I) (j : fst J) where

    Tyᵣ : Type ℓ
    Tyᵣ = ((i : fst I) (j : fst J) → A i j)

    Tyₘ : Type ℓ
    Tyₘ = ((i : fst I) (j : fst J) → A i j)
        ⊎ (Σ[ e ∈ fst I ≃ fst J ]
          ((fst e i ≡ j) × ((i : fst I) (j : fst J) → A i j)))

    Tyₗ-left : Type ℓ
    Tyₗ-left = Σ[ f ∈ ((i : fst I) → A i j) ]
                (Σ[ g ∈ ((j : fst J) → A (RP'.notI I i) j) ]
                  g j ≡ f (RP'.notI I i))

    Tyₗ-right : Type ℓ
    Tyₗ-right = Σ[ e ∈ fst I ≃ fst J ]
                   ((fst e i ≡ j)
             × (Σ[ f ∈ ((i : fst I) → A i (fst e i)) ]
                 (Σ[ g ∈ ((j : fst J) → A (RP'.notI I i) j) ]
                   g (fst e (RP'.notI I i)) ≡ f (RP'.notI I i))))

    Tyₗ : Type ℓ
    Tyₗ = Tyₗ-left ⊎ Tyₗ-right

    Tyₘ→ₗ : Tyₘ → Tyₗ
    Tyₘ→ₗ (inl g) = inl ((λ i → g i j) , ((g (RP'.notI I i)) , refl))
    Tyₘ→ₗ (inr (e , p , g)) = inr (e , (p , (λ i → g i (fst e i)) , ((g (RP'.notI I i)) , refl)))

    Tyₘ→ᵣ : Tyₘ → Tyᵣ
    Tyₘ→ᵣ (inl x) = x
    Tyₘ→ᵣ (inr x) = snd (snd x)

    TY = Pushout Tyₘ→ₗ Tyₘ→ᵣ

{-
 Σ[ f ∈ AB ]
      Σ[ g ∈ ((j : J) → A (M.notI i) j) ] g (AB→J (M.notI i) f) ≡ AB→A (M.notI i) f


    fat→ₗ-ab : (i : fst I) → fat-ab → left-push↑ₗ-ab i
    fat→ₗ-ab  i (f , g , r) = (f , (g (M.notI i)) , (r (M.notI i)))

    fat→ᵣ-ab : (i : fst I) → fat-ab → left-push↑ᵣ-ab i
    fat→ᵣ-ab i (f , g , r) =  (AB→J i f , AB→A i f) , g , r i

    PushTop-ab : Type _--
    PushTop-ab = Σ[ i ∈ fst I ] (Pushout (fat→ₗ-ab i) (fat→ᵣ-ab i))

-}

    TY→R : TY → ΠR-base-ab
    TY→R (inl (inl (a , g , p))) = inl ((inl j) , a)
    TY→R (inl (inr (e , p , a , g))) = inl ((inr e) , a)
    TY→R (inr x) = inr x
    TY→R (push (inl x) i) = push (((inl j) , (λ i → x i j)) , x , λ _ → refl) i
    TY→R (push (inr (x , (p , g))) i) = push ((inr x , λ i → g i (fst x i)) , g , λ _ → refl) i

    TY→Lₗ : (x : TY) →  Σ (fst J) (A i) × ((j₁ : fst J) → A (M.notI i) j₁)
    TY→Lₗ (inl (inl (f , p , q))) = (j , f i) , p
    TY→Lₗ (inl (inr (e , p , f , q , r))) = (fst e i , f i) , q
    TY→Lₗ (inr x) = (j , x i j) , (x (RP'.notI I i))
    TY→Lₗ (push (inl x) _) = (j , x i j) , x (RP'.notI I i)
    TY→Lₗ (push (inr (e , p , f)) k) = (p k , f i (p k)) , f (RP'.notI I i)

    TY→L : TY → left-push-ab
    TY→L x = i , TY→Lₗ x

    {- ⊎.rec (λ ab → (j , fst ab) , snd ab)
                        (λ ab → (fst (fst ab) i , snd ab .fst .fst i) , snd ab .fst .snd .fst) x
    -}
-- {-
--   newBack₂ : (i : fst I) → ΠR-Pushout-ab* i → Σ[ j ∈ fst J ] Pushout (Tyₗ→ i j) (Tyᵣ→ i j)
--   newBack₂ i (inl ((x , f) , p , q)) = evalG x i , inl (inl (x , f))
--   newBack₂ i (inr ((j , a) , p , q)) = j , inr (i , ((j , a) , p (RP'.notI I i)))
--   newBack₂ i (push ((inl x , f) , p , q) k) = x , push (f , ((p (RP'.notI I i)) , (q (RP'.notI I i)))) k
--   newBack₂ i (push ((inr x , f) , p , q) k) = fst x i , P k
--     where
--     P : Path (Pushout (Tyₗ→ i (fst x i)) (Tyᵣ→ i (fst x i)))
--              (inl (inl (inr x , f)))
--              (inr (i , (fst x i , f i) , p (RP'.notI I i)))
--     P =  (((λ k → inl (push (((inr x) , f) , (p , q)) k))
--          ∙ λ k → inl (push (((inl (fst x i)) , (λ k → p k (fst x i))) , (p , (λ i → refl))) (~ k)))
--          ∙∙ push ((λ k → p k (fst x i)) , (p (RP'.notI I i) , refl))
--          ∙∙ λ k → inr (i , (fst x i , q i k) , p (RP'.notI I i)))
-- -}

  newBack : Type ℓ
  newBack = Σ[ i ∈ fst I ] Σ[ j ∈ fst J ] (TY i j)

  newBack→ₗ : newBack → left-push-ab
  newBack→ₗ (i , j , x) = TY→L i j x

  newBack→ᵣ : newBack → ΠR-base-ab
  newBack→ᵣ (i , j , x) = TY→R i j x

  ΠR-extend** : Type ℓ
  ΠR-extend** = Pushout {A = newBack} {B = left-push-ab} {C = ΠR-base-ab}
                        newBack→ₗ
                        newBack→ᵣ

  push-case-filler-inl : (i : fst I) (x : fst J) (f : (i : fst I) → A i x)
    (p : (i : fst I) (j : fst J) → A i j) (q : (i : fst I) → p i x ≡ f i)
    (i' j' k' : Cubical.Foundations.Prelude.I) → ΠR-extend**
  push-case-filler-inl i x f p q i' j' k' =
    hfill (λ k → λ {(i' = i0) → push (i , x , (inl (inl ((λ i → q i k) , (p (RP'.notI I i)) , (λ j → q (RP'.notI I i) (k ∧ j)))))) j'
                   ; (i' = i1) → compPath-filler' (λ j → (inl (i , (x , q i (~ j)) , p (RP'.notI I i))))
                                   (push (i , x , inr p)) k j'
                   ; (j' = i0) → inl (i , (x , q i k) , p (RP'.notI I i))
                   ; (j' = i1) → inr (push (((inl x) , (λ i → q i k)) , (p , (λ i j → q i (k ∧ j)))) i')})
          (inS (push (i , x , push (inl p) i') j'))
          k'

  push-case-filler-inr : (i : fst I) (x : fst I ≃ fst J) (f : (i : fst I) → A i (fst x i))
    (p : (i : fst I) (j : fst J) → A i j) (q : (i : fst I) → p i (fst x i) ≡ f i)
    (i' j' k' : Cubical.Foundations.Prelude.I) → ΠR-extend**
  push-case-filler-inr i x f p q i' j' k' =
    hfill (λ k → λ {(i' = i0) → push (i , ((fst x i) , (inl (inr (x , (refl , (λ i → q i k) , ((p (RP'.notI I i)) , (λ j → q (RP'.notI I i) (k ∧ j))))))))) j'
                   ; (i' = i1) → compPath-filler' (λ j → (inl (i , (fst x i , q i (~ j)) , p (RP'.notI I i))))
                                   (push (i , fst x i , inr p)) k j'
                   ; (j' = i0) → inl (i , (fst x i , q i k) , p (RP'.notI I i))
                   ; (j' = i1) → inr (push (((inr x) , (λ i → q i k)) , (p , (λ i j → q i (k ∧ j)))) i')})
           (inS (push (i , fst x i , push (inr (x , (refl , p))) i') j'))
           k'

  push-case : (i : fst I) (x : _) → Path ΠR-extend**
                         (inl (i , PushTop→left-push'-ab* i x))
                         (inr (PushTop→ΠR-base-ab* i x))
  push-case i (inl ((inl x , f) , p , q)) = push (i , x , inl (inl (f , (p , q))))
  push-case i (inl ((inr x , f) , p , q)) = push (i , fst x i , inl (inr (x , refl , f , p , q)))
  push-case i (inr ((j , a) , g , p))  =
    ((λ t → inl (i , (j , p (~ t)) , g (RP'.notI I i)) ) ∙ push (i , j , inr g))
  push-case i (push ((inl x , f) , p , q) i') j' =
    push-case-filler-inl i x f p q i' j' i1
  push-case i (push ((inr x , f) , p , q) i') j' =
    push-case-filler-inr i x f p q i' j' i1

  ΠR-extend→New : ΠR-extend* → ΠR-extend**
  ΠR-extend→New (inl x) = inl x
  ΠR-extend→New (inr x) = inr x
  ΠR-extend→New (push (i , x) k) = push-case i x k

-- todo prove is iso
ΠR-extend*Iso : (I J : RP∞' ℓ-zero) (A : fst I → fst J → Type ℓ-zero)
  → ΠR-extend* I J A
  → Rewrite1.AB.ΠR-extend-ab I (fst J) A
       ((i : fst I) → Σ[ j ∈ fst J ] A i j)
       (λ i f → f i .fst)
       λ i f → f i .snd
ΠR-extend*Iso I J A (inl x) = inl x
ΠR-extend*Iso I J A (inr (inl x)) = inr (inl (Iso.inv (TotAIso I J {A}) x))
ΠR-extend*Iso I J A (inr (inr x)) = inr (inr x)
ΠR-extend*Iso I J A (inr (push ((x , s2) , q , t) i)) =
  inr (push ((Iso.inv (TotAIso I J {A}) (x , s2)) , q , t) i)
ΠR-extend*Iso I J A (push (i' , inl (a , b)) i) =
  push (i' , inl (Iso.inv (TotAIso I J {A}) a , b)) i
ΠR-extend*Iso I J A (push (i' , inr x) i) =
  push (i' , inr x) i
ΠR-extend*Iso I J A (push (i' , push (a , b) i₁) i) =
  push (i' , push ((Iso.inv (TotAIso I J {A}) a) , b) i₁) i

-- second type
module _ {ℓ : Level} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ) where
  leftFun* : ΠR-extend* (RP∞'· ℓ) J A → joinR-gen (fst J) (A true)
  leftFun* (inl (false , (a , b))) = inrR b
  leftFun* (inl (true , y)) = inlR (fst y)
  leftFun* (inr (inl x)) = inlR (Iso.inv (TotAIso (RP∞'· _) J {A}) x true)
  leftFun* (inr (inr x)) = inrR (x true)
  leftFun* (inr (push (t , s , q) i)) =
    push* (f3 (RP∞'· ℓ) J {A = A} t true) (s true) (q true) i
  leftFun* (push (false , inl (a , b)) i) =
    push* (f3 (RP∞'· ℓ) J {A = A} a true) (fst b) (snd b) (~ i)
  leftFun* (push (true , inl x) i) = inlR (f3 (RP∞'· ℓ) J {A = A} (fst x) true)
  leftFun* (push (false , inr x) i) = inrR (fst (snd x) true)
  leftFun* (push (true , inr (a , b , c)) i) = push* a (b true) c i
  leftFun* (push (false , push (a , b) j) i) =
    push* (f3 (RP∞'· ℓ) J {A = A} a true) (fst b true) (snd b true) (~ i ∨ j)
  leftFun* (push (true , push (a , b) j) i) =
    push* (f3 (RP∞'· ℓ) J {A = A} a true) (fst b true) (snd b true) (i ∧ j)

-- more general
module _ {ℓ : Level} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) where
{-
  inler-g :  (j : fst J) (i' : fst I) (a : A i' j)
             (b : (j₁ : fst J) → A (RP'.notI I i') j₁) (i : fst I)
        → joinR-gen (fst J) (A i)
  inler-g j i' =
    RP'.elimI I {B = λ i → A i' j → ((j₁ : fst J) → A (RP'.notI I i') j₁) → joinR-gen (fst J) (A i)} i'
                (λ a f → inlR (j , a))
                λ a f → inrR f

  inler-g-id : (j : fst J) (i' : fst I) (a : A i' j)
             (b : (j₁ : fst J) → A (RP'.notI I i') j₁)
        → (inler-g j i' i' a b ≡ inlR (j , a))
         × ((inler-g j i' (RP'.notI I i') a b ≡ inrR b))
  fst (inler-g-id j i' a b) k =
    RP'.elimIβ I {B = λ i → A i' j → ((j₁ : fst J) → A (RP'.notI I i') j₁) → joinR-gen (fst J) (A i)} i'
                (λ a f → inlR (j , a))
                (λ a f → inrR f) .fst k a b
  snd (inler-g-id j i' a b) k =
    RP'.elimIβ I {B = λ i → A i' j → ((j₁ : fst J) → A (RP'.notI I i') j₁) → joinR-gen (fst J) (A i)} i'
                (λ a f → inlR (j , a))
                (λ a f → inrR f) .snd k a b
-}

  leftFun-inr : (i : fst I) → ΠR-base-ab* I J A → joinR-gen (fst J) (A i)
  leftFun-inr i (inl (inl x , y)) = inlR (x , y i)
  leftFun-inr i (inl (inr x , y)) = inlR (fst x i , y i)
  leftFun-inr i (inr x) = inrR (x i)
  leftFun-inr i (push ((inl e , y) , b) j) = push* (e , y i) (fst b i) (b .snd i) j
  leftFun-inr i (push ((inr e , y) , b) j) = push* (fst e i , y i) (fst b i) (snd b i) j

  leftFun-cohₗ : (i : fst I) (x : ΠR-Pushout-ab* I J A i)
    → inlR (PushTop→left-push'-ab* I J A i x .fst)
      ≡ leftFun-inr i (PushTop→ΠR-base-ab* I J A i x)
  leftFun-cohₗ i (inl ((inl x , p) , f , q)) = refl
  leftFun-cohₗ i (inl ((inr x , p) , f , q)) = refl
  leftFun-cohₗ i (inr ((j , a) , f , q)) = push* (j , a) (f i) q
  leftFun-cohₗ i (push ((inl j , p) , f) k) l = push* (j , p i) (fst f i) (snd f i) (k ∧ l)
  leftFun-cohₗ i (push ((inr x , p) , f) k) l = push* (fst x i , p i) (fst f i) (snd f i) (k ∧ l)

  leftFun-cohᵣ : (i : fst I) (x : ΠR-Pushout-ab* I J A i)
      → inrR (PushTop→left-push'-ab* I J A i x .snd) ≡
      leftFun-inr (fst (snd I .fst) i) (PushTop→ΠR-base-ab* I J A i x)
  leftFun-cohᵣ i (inl ((inl x , p) , f , q)) =
    sym (push* (x , p (RP'.notI I i)) f q)
  leftFun-cohᵣ i (inl ((inr x , p) , f , q)) =
    sym (push* (fst x (RP'.notI I i) , p (RP'.notI I i)) f q)
  leftFun-cohᵣ i (inr ((j , a) , f , q)) = refl
  leftFun-cohᵣ i (push ((inl j , p) , f) k) l =
    push* (j , p (fst (snd I .fst) i))
         (fst f (I .snd .fst .fst i)) (snd f (I .snd .fst .fst i)) (~ l ∨ k)
  leftFun-cohᵣ i (push ((inr x , p) , f) k) l =
    push* (fst x (snd I .fst .fst i) , p (fst (snd I .fst) i))
         (fst f (I .snd .fst .fst i)) (snd f (I .snd .fst .fst i)) (~ l ∨ k)

  leftFun-coh : (i' : fst I) (x : ΠR-Pushout-ab* I J A i') (i : fst I)
    → leftFun'-inl I (fst J) A i'
          (PushTop→left-push'-ab* I J A i' x .fst)
          (PushTop→left-push'-ab* I J A i' x .snd) i
     ≡ leftFun-inr i (PushTop→ΠR-base-ab* I J A i' x)
  leftFun-coh i' x =
    RP'.elimI I i'
      (leftFun'-inlβ I (fst J) A i'
         (PushTop→left-push'-ab* I J A i' x .fst)
         (PushTop→left-push'-ab* I J A i' x .snd) .fst
    ∙ leftFun-cohₗ i' x)
      (leftFun'-inlβ I (fst J) A i'
         (PushTop→left-push'-ab* I J A i' x .fst)
         (PushTop→left-push'-ab* I J A i' x .snd) .snd
     ∙ leftFun-cohᵣ i' x)

  leftFun*-full : (i : fst I) → ΠR-extend* I J A → joinR-gen (fst J) (A i)
  leftFun*-full i (inl (i' , a , b)) = leftFun'-inl I (fst J) A i' a b i
  leftFun*-full i (inr x) = leftFun-inr i x
  leftFun*-full i (push (i' , x) i₁) = leftFun-coh i' x i i₁

  leftFun-cohₗ**-fill : (i' : fst I) (j : fst J) (e : fst I ≃ fst J)
    (p : fst e i' ≡ j) (f : (i₁ : fst I) (j₁ : fst J) → A i₁ j₁)
    → (i k r : _) → joinR-gen (fst J) (A i')
  leftFun-cohₗ**-fill i' j e p f i k r =
    hfill (λ r → λ {(i = i0) → inlR (p (~ r) , f i' (p (~ r)))
                   ; (i = i1) → push* (j , f i' j) (f i') (λ _ → f i' j) k
                   ; (k = i0) → inlR ((p (i ∨ ~ r)) , (f i' (p (i ∨ ~ r))))
                   ; (k = i1) → push* (p (~ r) , f i' (p (~ r))) (f i') (λ i → f i' (p (~ r))) i})
          (inS (push* (j , f i' j) (f i') (λ _ → f i' j) (i ∧ k)))
          r

  leftFun-cohₗ** : (i' : fst I) (j : fst J) (a : TY I J A i' j)
    → inlR (TY→L I J A i' j a .snd .fst) ≡ leftFun-inr i' (TY→R I J A i' j a)
  leftFun-cohₗ** i' j (inl (inl x)) = refl
  leftFun-cohₗ** i' j (inl (inr x)) = refl
  leftFun-cohₗ** i' j (inr x) = push* (j , (x i' j)) (x i') refl
  leftFun-cohₗ** i' j (push (inl x) i) k = push* (j , x i' j) (x i') (λ _ → x i' j) (i ∧ k)
  leftFun-cohₗ** i' j (push (inr (e , p , f)) i) k = leftFun-cohₗ**-fill i' j e p f i k i1

  leftFun-cohᵣ** : (i' : fst I) (j : fst J) (a : TY I J A i' j)
    → inrR (TY→L I J A i' j a .snd .snd) ≡
      leftFun-inr (fst (snd I .fst) i') (TY→R I J A i' j a)
  leftFun-cohᵣ** i' j (inl (inl (f , p , q))) = sym (push* (j , f (RP'.notI I i')) p q)
  leftFun-cohᵣ** i' j (inl (inr (e , p , f , q , r))) = sym (push* (fst e (RP'.notI I i') , f (RP'.notI I i')) q r)
  leftFun-cohᵣ** i' j (inr x) = refl
  leftFun-cohᵣ** i' j (push (inl x) i) k =
    push* (j , x (RP'.notI I i') j) (x (RP'.notI I i')) (λ _ → x (RP'.notI I i') j) (i ∨ ~ k)
  leftFun-cohᵣ** i' j (push (inr (e , p , f)) i) k =
    push*
         (fst e (fst (snd I .fst) i') ,
          f (fst (snd I .fst) i') (fst e (fst (snd I .fst) i')))
         (f (fst (snd I .fst) i'))
         (λ _ → f (fst (snd I .fst) i') (fst e (fst (snd I .fst) i'))) (i ∨ ~ k)

  leftFun-coh** : (i' : fst I) (j : fst J) (a : TY I J A i' j) (i : fst I)
    → leftFun'-inl I (fst J) A i' (TY→L I J A i' j a .snd .fst) (TY→L I J A i' j a .snd .snd) i
     ≡ leftFun-inr i (TY→R I J A i' j a)
  leftFun-coh** i' j a =
    RP'.elimI I i'
      (leftFun'-inlβ I (fst J) A i' _ _ .fst
      ∙ leftFun-cohₗ** i' j a)
      (leftFun'-inlβ I (fst J) A i' _ _ .snd
      ∙ leftFun-cohᵣ** i' j a)

  leftMap** : (i : fst I)
    → ΠR-extend** I J A → joinR-gen (fst J) (A i)
  leftMap** i (inl (i' , a , b)) = leftFun'-inl I (fst J) A i' a b i
  leftMap** i (inr x) = leftFun-inr i x
  leftMap** i (push (i' , j , a) k) = leftFun-coh** i' j a i k

leftMapBool : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
  → (i : Bool)
  → ΠR-extend** (RP∞'· ℓ) J A → joinR-gen (fst J) (A i)
leftMapBool J A i (inl (i' , a , b)) = leftFun'-inl (RP∞'· _) (fst J) A i' a b i
leftMapBool J A i (inr x) = leftFun-inr (RP∞'· _) J A i x
leftMapBool J A false (push (false , j , a) k) = leftFun-cohₗ** (RP∞'· _) J A false j a k
leftMapBool J A false (push (true , j , a) k) = leftFun-cohᵣ** (RP∞'· _) J A true j a k
leftMapBool J A true (push (false , j , a) k) = leftFun-cohᵣ** (RP∞'· _) J A false j a k
leftMapBool J A true (push (true , j , a) k) = leftFun-cohₗ** (RP∞'· _) J A true j a k

leftMapBool≡ : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
  → (i : Bool) (x : ΠR-extend** (RP∞'· ℓ) J A)
  → leftMapBool J A i x ≡ leftMap** (RP∞'· _) J A i x
leftMapBool≡ J A i (inl x) = refl
leftMapBool≡ J A i (inr x) = refl
leftMapBool≡ J A false (push (false , j , a) i₁) k = lUnit (leftFun-cohₗ** (RP∞'· _) J A false j a) k i₁
leftMapBool≡ J A true (push (false , j , a) i₁) k = lUnit (leftFun-cohᵣ** (RP∞'· _) J A false j a) k i₁
leftMapBool≡ J A false (push (true , j , a) i₁) k = lUnit (leftFun-cohᵣ** (RP∞'· _) J A true j a) k i₁
leftMapBool≡ J A true (push (true , j , a) i₁) k = lUnit (leftFun-cohₗ** (RP∞'· _) J A true j a) k i₁

leftFun*-fullBool : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ) (i : Bool)
  → ΠR-extend* (RP∞'· ℓ) J A → joinR-gen (fst J) (A i)
leftFun*-fullBool J A i (inl (i' , a , b)) = leftFun'-inl (RP∞'· _) (fst J) A i' a b i
leftFun*-fullBool J A i (inr x) = leftFun-inr (RP∞'· _) J A i x
leftFun*-fullBool J A false (push (false , a) k) = leftFun-cohₗ (RP∞'· _) J A false a k
leftFun*-fullBool J A false (push (true , y) k) = leftFun-cohᵣ (RP∞'· _) J A true y k
leftFun*-fullBool J A true (push (false , a) k) = leftFun-cohᵣ (RP∞'· _) J A false a k
leftFun*-fullBool J A true (push (true , y) k) = leftFun-cohₗ (RP∞'· _) J A true y k


leftFunBool≡' : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
  → (i : Bool) (x : ΠR-extend* (RP∞'· ℓ) J A)
  → leftFun*-full (RP∞'· _) J A i x ≡ leftFun*-fullBool J A i x
leftFunBool≡' J A i (inl x) = refl
leftFunBool≡' J A i (inr x) = refl
leftFunBool≡' J A false (push (false , a) k) j = lUnit (leftFun-cohₗ (RP∞'· _) J A false a) (~ j) k
leftFunBool≡' J A false (push (true , a) k) j = lUnit (leftFun-cohᵣ (RP∞'· _) J A true a) (~ j) k
leftFunBool≡' J A true (push (false , a) k) j = lUnit (leftFun-cohᵣ (RP∞'· _) J A false a) (~ j) k
leftFunBool≡' J A true (push (true , a) k) j = lUnit (leftFun-cohₗ (RP∞'· _) J A true a) (~ j) k

Better! : ∀ {ℓ} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) → Type ℓ
Better! I J A =
  Pushout {A = fst I × ΠR-extend** I J A}
  {B = Σ[ i ∈ fst I ] joinR-gen (fst J) (A i)} {C = ΠR-extend** I J A} (λ x → fst x , leftMap** I J A (fst x) (snd x)) snd

module _ {ℓ} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) where
  btm-map :  (Σ[ i ∈ fst I ] (joinR-gen (fst J) (A i)))
    → joinR-gen (fst J) λ j → joinR-gen (fst I) λ i → A i j
  btm-map (i , inlR x) = inlR (fst x , inlR (i , snd x))
  btm-map (i , inrR x) = inrR λ j → inlR (i , x j)
  btm-map (i , push* a b x i₁) = push* (fst a , inlR (i , snd a)) (λ j → inlR (i , b j)) (λ t → inlR (i , x t)) i₁

leftMapsAgree : ∀ {ℓ} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) (i : fst I) (x : ΠR-extend* I J A)
  → leftMap** I J A i (ΠR-extend→New I J A x) ≡ leftFun*-full I J A i x
leftMapsAgree I J A i (inl x) = refl
leftMapsAgree I J A i (inr x) = refl
leftMapsAgree {ℓ = ℓ} I J A i (push (i' , a) k) l = help I i' A i a l k
  where
  module _ (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ) where

    fill1-refl : (f : fst J) (g : (i : Bool) (j : fst J) → A i j)
               → cong (leftMapBool J A false) ((λ j → inl (true , (f , g true f) , g false)) ∙ push (true , f , inr g)) ≡ refl
    fill1-refl f g i j = leftMapBool J A false (compPath-filler' refl (push (true , f , inr g)) (~ i) j)

    fill1 :  (f : fst J) (g : (i : Bool) (j : fst J) → A i j) (a : A true f)  (q : g true f ≡ a)
             → cong (leftMapBool J A false) ((λ j → inl (true , (f , q (~ j)) , g false)) ∙ push (true , f , inr g)) ≡ refl
    fill1 f g = J> (fill1-refl f g)

    fill1-refl≡ : (f : fst J) (g : (i : Bool) (j : fst J) → A i j) → fill1 f g (g true f) refl ≡ fill1-refl f g
    fill1-refl≡ f g =
      JRefl (λ a q → cong (leftMapBool J A false)
                ((λ j → inl (true , (f , q (~ j)) , g false)) ∙ push (true , f , inr g)) ≡ refl)
        (fill1-refl f g)

    fill2-refl : (f : fst J) (g : (i : Bool) (j : fst J) → A i j)
               → cong (leftMapBool J A true) ((λ j → inl (true , (f , g true f) , g false)) ∙ push (true , f , inr g)) ≡ push* (f , g true f) (g true) refl
    fill2-refl f g i j = leftMapBool J A true (compPath-filler' refl (push (true , f , inr g)) (~ i) j)

    fill2 :  (f : fst J) (g : (i : Bool) (j : fst J) → A i j) (a : A true f)  (q : g true f ≡ a)
             → cong (leftMapBool J A true) ((λ j → inl (true , (f , q (~ j)) , g false)) ∙ push (true , f , inr g)) ≡ push* (f , a) (g true) q
    fill2 f g = J> (fill2-refl f g)

    fill2-refl≡ : (f : fst J) (g : (i : Bool) (j : fst J) → A i j) → fill2 f g (g true f) refl ≡ fill2-refl f g
    fill2-refl≡ f g =
      JRefl (λ a q → cong (leftMapBool J A true)
                ((λ j → inl (true , (f , q (~ j)) , g false)) ∙ push (true , f , inr g)) ≡  push* (f , a) (g true) q)
        (fill2-refl f g)


    fill-inl : (x : fst J) (p : (i : Bool) (j : fst J) → A i j)
               (f : (i : Bool) → A i x) (q : (λ j → p j x) ≡ f)
            → Cube (λ j k → push* (x , f false)  (p false) (funExt⁻ q false) (~ k))
                    (fill1 x p (f true) (funExt⁻ q true)) -- i j k
                    (λ i k → leftMapBool J A false (push-case (RP∞'· ℓ) J A true (push ((inl x , f) , p , (funExt⁻ q)) i) k))
                    (λ i k → push* (x , f false)  (p false) (funExt⁻ q false) (~ k ∨ i))
                    (λ _ _ → inrR (p false)) λ i j → push* (x , f false) (p false) (funExt⁻ q false) i
    fill-inl x p = J> ((λ i j k → leftMapBool J A false
                        (push-case-filler-inl (RP∞'· _) J A true x _ p (λ _ → refl) i k (~ j)))
                     ▷ sym (fill1-refl≡ x p))

    fill-inr : (x : Bool ≃ fst J) (p : (i : Bool) (j : fst J) → A i j)
               (f : (i : Bool) → A i (fst x i)) (q : (λ j → p j (fst x j)) ≡ f)
            → Cube (λ j k → push* (fst x false , f false)  (p false) (funExt⁻ q false) (~ k))
                    (fill1 (fst x true) p (f true) (funExt⁻ q true))
                    (λ i k → leftMapBool J A false (push-case (RP∞'· ℓ) J A true (push ((inr x , f) , p , (funExt⁻ q)) i) k))
                    (λ i k → push* (fst x false , f false)  (p false) (funExt⁻ q false) (~ k ∨ i))
                    (λ _ _ → inrR (p false))
                    λ i j → push* (fst x false , f false) (p false) (funExt⁻ q false) i
    fill-inr x p = J> ((λ i j k → leftMapBool J A false (push-case-filler-inr (RP∞'· _) J A true x _ p (λ _ → refl) i k (~ j)))
                      ▷ sym (fill1-refl≡ (fst x true) p))

    fill2-inl : (x : fst J) (p : (i : Bool) (j : fst J) → A i j)
               (f : (i : Bool) → A i x) (q : (λ j → p j x) ≡ f)
            → Cube (λ j k → inlR (x , f true))
                    (fill2 x p (f true) (funExt⁻ q true))
                    (λ i k → leftMapBool J A true (push-case (RP∞'· ℓ) J A true (push ((inl x , f) , p , (funExt⁻ q)) i) k))
                    (λ i k → push* (x , f true)  (p true) (funExt⁻ q true) (k ∧ i))
                    (λ i j → inlR (x , f true))
                    λ i j → push* (x , f true) (p true) (funExt⁻ q true) i
    fill2-inl x p =
      J> ((λ i j k → leftMapBool J A true
           (push-case-filler-inl (RP∞'· _) J A true x
             _ p (λ _ → refl) i k (~ j)))
      ▷ sym (fill2-refl≡ x p))

    fill2-inr : (x : Bool ≃ fst J) (p : (i : Bool) (j : fst J) → A i j)
               (f : (i : Bool) → A i (fst x i)) (q : (λ j → p j (fst x j)) ≡ f)
            → Cube (λ j k → inlR (fst x true , f true))
                    (fill2 (fst x true) p (f true) (funExt⁻ q true))
                    (λ i k → leftMapBool J A true (push-case (RP∞'· ℓ) J A true (push ((inr x , f) , p , (funExt⁻ q)) i) k))
                    (λ i k → push* (fst x true , f true)  (p true) (funExt⁻ q true) (k ∧ i))
                    (λ i j → inlR (fst x true , f true))
                    λ i j → push* (fst x true , f true) (p true) (funExt⁻ q true) i
    fill2-inr x p =
      J> ((λ i j k → asd i j k)
      ▷ sym (fill2-refl≡ (fst x true) p))
      where
      asd : (i j k : _) → _
      asd i j k =
        hcomp (λ r → λ {(i = i0) → inlR (fst x true , p true (fst x true))
                   ; (i = i1) → leftMapBool J A true (compPath-filler' refl (push (true , (fst x true) , (inr p))) (~ j ∧ r) k)
                   ; (j = i0) → leftMapBool J A true
                                  (push-case-filler-inr (RP∞'· ℓ) J A true x
                                    (λ i → p i (fst x i)) p (λ _ → refl) i k r)
                   ; (j = i1) → push* (fst x true , p true (fst x true)) (p true) refl (k ∧ i)
                   ; (k = i0) → inlR (fst x true , p true (fst x true))
                   ; (k = i1) → push* (fst x true , p true (fst x true)) (p true) refl i})
          (hcomp (λ r → λ {(i = i0) → inlR (fst x true , p true (fst x true))
                   ; (i = i1) →  push* (fst x true , p true (fst x true)) (p true) refl k
                   ; (j = i1) → push* (fst x true , p true (fst x true)) (p true) refl (k ∧ i)
                   ; (k = i0) → inlR (fst x true , p true (fst x true))
                   ; (k = i1) → push* (fst x true , p true (fst x true)) (p true) refl i})
                   (push* (fst x true , p true (fst x true)) (p true) refl (k ∧ i)))

    mainₗ : (x : _)
      → cong (leftMapBool J A false) (push-case (RP∞'· ℓ) J A true x)
      ≡ leftFun-cohᵣ (RP∞'· ℓ) J A true x
    mainₗ (inl ((inl x , snd₂) , snd₁)) = refl
    mainₗ  (inl ((inr x , snd₂) , snd₁)) = refl
    mainₗ  (inr ((f , a) , g , q)) = fill1 f g a q
    mainₗ  (push ((inl x , f) , p , q) i) j k = fill-inl x p f (funExt q) i j k
    mainₗ (push ((inr x , f) , p , q) i) j k = fill-inr x p f (funExt q) i j k

    mainᵣ : (x : _)
      → cong (leftMapBool J A true) (push-case (RP∞'· ℓ) J A true x)
      ≡ leftFun-cohₗ (RP∞'· ℓ) J A true x
    mainᵣ (inl ((inl x , snd₂) , snd₁)) = refl
    mainᵣ  (inl ((inr x , snd₂) , snd₁)) = refl
    mainᵣ  (inr ((f , a) , g , q)) = fill2 f g a q
    mainᵣ  (push ((inl x , f) , p , q) i) j k = fill2-inl x p f (funExt q) i j k
    mainᵣ (push ((inr x , f) , p , q) i) j k = fill2-inr x p f (funExt q) i j k


    main : (k : _) (x : _)
      → cong (leftMapBool J A k) (push-case (RP∞'· ℓ) J A true x)
      ≡ cong (leftFun*-full (RP∞'· ℓ) J A k) (push (true , x))
    main false x = mainₗ x ∙ lUnit _
    main  true x = mainᵣ x ∙ lUnit _

  h1 : (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ) (k : _) → leftMapBool J A k ≡ leftMap** (RP∞'· _) J A k
  h1 J A k = funExt (leftMapBool≡ J A k)
  help : (I : RP∞' ℓ) (i' : fst I) (A : fst I → fst J → Type ℓ) (i : fst I) (a : _)
    → cong (leftMap** I J A i) (cong (ΠR-extend→New I J A) (push (i' , a)))
     ≡ cong (leftFun*-full I J A i) (push (i' , a))
  help = JRP∞' λ A k x → (λ j → cong (h1 J A k (~ j))
      (cong (ΠR-extend→New (RP∞'· ℓ) J A) (push (true , x))))
      ∙ main J A k x


ΠR-pushout→Better! : ∀ {ℓ} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
  → Pushout {A = fst I × ΠR-extend* I J A}
       (λ i → fst i , leftFun*-full I J A (fst i) (snd i)) snd
  → Better! I J A
ΠR-pushout→Better! I J A (inl x) = inl x
ΠR-pushout→Better! I J A (inr x) = inr (ΠR-extend→New I J A x)
ΠR-pushout→Better! I J A (push a i) =
  ((λ t → inl (fst a , leftMapsAgree I J A (fst a) (snd a) (~ t)))
  ∙ push (fst a , ΠR-extend→New I J A (snd a))) i

{-
HAHA : {ℓ : Level} {Targ : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) → ΠR-extend** I J A → Type ℓ}
  → (f : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) (i : fst I) (p : ΠR-extend** I J A) → Targ I J A p)
  → (f-coh : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) (i : fst I) (p : ΠR-extend** I J A) → f I J A i ≡ f I J A (RP'.notI I i))
  → (inl : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) (p : _) → Targ I J A (inl p))
  → (inr : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) (p : _) → Targ I J A (inr p))
  → Unit
  → (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) (p : ΠR-extend** I J A) → Targ I J A p
HAHA {Targ = T} f f-coh inler inrer ind I J A (inl x) = inler I J A x
HAHA {Targ = T} f f-coh inler inrer ind I J A (inr x) = inrer I J A x
HAHA {ℓ = ℓ} {Targ = T} f f-coh inler inrer ind I J A (push (i , j , a) k) =
  hcomp (λ r → λ {(k = i0) → {!!}
                 ; (k = i1) → {!!}})
        (f I J A i (push (i , j , a) k))
  where
  help : (I : RP∞' ℓ) (i : fst I) (J : RP∞' ℓ) (j : fst J) (A : fst I → fst J → Type ℓ) (a : TY I J A i j)
    → PathP (λ k → T I J A (push (i , j , a) k))
             (inler I J A (newBack→ₗ I J A (i , j , a)))
             (inrer I J A (newBack→ᵣ I J A (i , j , a)))
  help = JRP∞' (JRP∞' λ A a → {!!}
              ◁ (λ j → f (RP∞'· ℓ) (RP∞'· ℓ) A true (push (true , true , a) j))
              ▷ {!!})
-}

module MEGA {ℓ : Level} {Targ : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) → ΠR-extend** I J A → Type ℓ}
         (inler : (A : Bool → Bool → Type ℓ) (a : A true true) (b : TotΠ (A false))
         → Targ (RP∞'· ℓ) (RP∞'· ℓ) A (inl (true , (true , a) , b)))
         (inr-inr : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) (t : (i : fst I) (j : fst J) → A i j)
                  → Targ I J A (inr (inr t)))
         (inr-inl-inl : (I : RP∞' ℓ) (A : fst I → Bool → Type ℓ)
                        (f : (x : fst I) → A x true)
                          → Σ[ k ∈ Targ I (RP∞'· ℓ) A (inr (inl (inl true , f))) ]
                            ((p : (i : fst I) (j : Bool) → A i j) (q : (x : fst I) → p x true ≡ f x)
                          → PathP (λ r → Targ I (RP∞'· ℓ) A (inr (push ((inl true , f) , (p , q)) r)))
                                   k (inr-inr I (RP∞'· ℓ) A p)))
         (inr-inl-inr : (I : RP∞' ℓ) (A : fst I → fst I → Type ℓ) (f : (i : fst I) → A i i)
           → Σ[ k ∈ Targ I I A (inr (inl (inr (idEquiv (fst I)) , f))) ]
               ((p : (i : fst I) (j : fst I) → A i j) (q : (x : fst I) → p x x ≡ f x)
            → PathP (λ r → Targ I I A (inr (push ((inr (idEquiv (fst I)) , f) , (p , q)) r)))
                                   k (inr-inr I I A p)))
         (push-inl : (A : Bool → Bool → Type ℓ) (f : (i : fst (RP∞'· ℓ)) → A i true)
           (g : (j : Bool) → A false j) (p : g true ≡ f false)
         → PathP (λ k → Targ (RP∞'· ℓ) (RP∞'· ℓ) A
                    (push (true , true , inl (inl (f , g , p))) k))
                  (inler A (f true) g)
                  (inr-inl-inl (RP∞'· ℓ) A f .fst))
         (coh-inr : (A : Bool → Bool → Type ℓ) (g : (i j : Bool) → A i j)
           → PathP (λ k → Targ (RP∞'· ℓ) (RP∞'· ℓ) A (push (true , true , inr g) k))
                    (inler A (g true true) (g false)) (inr-inr (RP∞'· ℓ) (RP∞'· ℓ) A g))
         (coh-eq1 : (A : Bool → Bool → Type ℓ) (g : (i : Bool) → A i i) (f : TotΠ (A false)) (p : f false ≡ g false)
                     → PathP (λ k → Targ (RP∞'· ℓ) (RP∞'· ℓ) A (push (true , true , inl (inr (idEquiv Bool , refl , g , f , p))) k))
                             (inler A (g true) f)
                       (inr-inl-inr (RP∞'· ℓ) A g .fst))
         (coh-eq2 : (A : Bool → Bool → Type ℓ) (g : (i j : Bool) → A i j)
           → SquareP (λ i j → Targ (RP∞'· ℓ) (RP∞'· ℓ) A
                                (push (true , true , push (inr (idEquiv Bool , refl , g)) i) j))
                     (coh-eq1 A (λ i → g i i) (g false) refl)
                     (coh-inr A g)
                     (λ _ → inler A (g true true) (g false))
                     (inr-inl-inr (RP∞'· ℓ) A (λ i → g i i) .snd g (λ _ → refl)))
          (coh-eq-l : (A : Bool → Bool → Type ℓ) (g : (i j : Bool) → A i j)
            → SquareP (λ i j → Targ (RP∞'· ℓ) (RP∞'· ℓ) A
                                (push (true , true , push (inl g) i) j))
                        (push-inl A (λ i₁ → g i₁ true) (g false) (λ _ → g false true))
                        (coh-inr A g)
                        (λ _ → inler A (g true true) (g false))
                        (inr-inl-inl (RP∞'· ℓ) A (λ i → g i true) .snd g (λ _ → refl)))
         where

  inr-inl-inl* : (I J : RP∞' ℓ) (j : fst J) (A : fst I → fst J → Type ℓ)
                        (f : (x : fst I) → A x j)
                          → Σ[ k ∈ Targ I J A (inr (inl (inl j , f))) ]
                            ((p : (i : fst I) (j : fst J) → A i j) (q : (x : fst I) → p x j ≡ f x)
                          → PathP (λ r → Targ I J A (inr (push ((inl j , f) , (p , q)) r)))
                                   k (inr-inr I J A p))
  inr-inl-inl* I = JRP∞' (inr-inl-inl I)

  inr-inl-inl*≡ : (I : RP∞' ℓ) (A : fst I → Bool → Type ℓ)
                        (f : (x : fst I) → A x true)
                          → inr-inl-inl* I (RP∞'· ℓ) true A f ≡ inr-inl-inl I A f
  inr-inl-inl*≡ I A f i = help i A f
    where
    help : inr-inl-inl* I (RP∞'· ℓ) true ≡ inr-inl-inl I
    help = JRP∞'∙ (inr-inl-inl I)

  inr-inl-inr* : (I J : RP∞' ℓ) (e : fst I ≃ fst J) (A : fst I → fst J → Type ℓ)
               (f : (i : fst I) → A i (fst e i))
           → Σ[ k ∈ Targ I J A (inr (inl (inr e , f))) ]
               ((p : (i : fst I) (j : fst J) → A i j) (q : (x : fst I) → p x (fst e x) ≡ f x)
            → PathP (λ r → Targ I J A (inr (push ((inr e , f) , (p , q)) r)))
                                   k (inr-inr I J A p))
  inr-inl-inr* I = JRP∞'' I (inr-inl-inr I)

  inr-inl-inr*≡ : (I : RP∞' ℓ) (A : fst I → fst I → Type ℓ)
               (f : (i : fst I) → A i i)
           → inr-inl-inr* I I (idEquiv (fst I)) A f ≡ inr-inl-inr I A f
  inr-inl-inr*≡ I A f i = help i A f
    where
    help : inr-inl-inr* I I (idEquiv (fst I)) ≡ inr-inl-inr I
    help = JRP∞''-refl I (inr-inl-inr I)

  ΠR-extend→Inl' : (J : RP∞' ℓ) (j : fst J) (A : Bool → fst J → Type ℓ)
     (a : A true j)
     (b : TotΠ (A false))
    → Targ (RP∞'· ℓ) J A (inl (true , (j , a) , b))
  ΠR-extend→Inl' = JRP∞' inler

  ΠR-extend→Inl : (I : RP∞' ℓ) (i : fst I) (J : RP∞' ℓ) (j : fst J) (A : fst I → fst J → Type ℓ)
     (a : A i j)
     (b : TotΠ (A (RP'.notI I i)))
    → Targ I J A (inl (i , (j , a) , b))
  ΠR-extend→Inl = JRP∞' ΠR-extend→Inl'

  ΠR-extend→Inl≡ : (A : Bool → Bool → Type ℓ) (a : A true true) (b : TotΠ (A false))
    → ΠR-extend→Inl (RP∞'· ℓ) true (RP∞'· ℓ) true A a b ≡ inler A a b
  ΠR-extend→Inl≡ A a b =
     (λ k → h k (RP∞'· ℓ) true A a b)
    ∙ λ k → h' k A a b
    where
    h : ΠR-extend→Inl (RP∞'· ℓ) true ≡ ΠR-extend→Inl'
    h = JRP∞'∙ ΠR-extend→Inl'

    h' : ΠR-extend→Inl' (RP∞'· ℓ) true ≡ inler
    h' = JRP∞'∙ inler


  ΠR-extend→Inr : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) (x : ΠR-base-ab* I J A)
    → Targ I J A (inr x)
  ΠR-extend→Inr I J A (inl (inl j , f)) = inr-inl-inl* I J j A f .fst
  ΠR-extend→Inr I J A (inl (inr e , f)) = inr-inl-inr* I J e A f .fst
  ΠR-extend→Inr I J A (inr x) = inr-inr I J A x
  ΠR-extend→Inr I J A (push ((inl j , f) , p , q) i) = inr-inl-inl* I J j A f .snd p q i
  ΠR-extend→Inr I J A (push ((inr e , f) , p , q) i) = inr-inl-inr* I J e A f .snd p q i

  push-inr*-ty : (A : Bool → Bool → Type ℓ) (e : Bool ≃ Bool) (pf : fst e true ≡ true)
    → Type ℓ
  push-inr*-ty A e pf =
    Σ[ t ∈
         (((g : (i : fst (RP∞'· ℓ)) → A i (fst e i))
         (f : (t : Bool) → A false t)
         (p : f (fst e false) ≡ g false)
         → PathP (λ k → Targ (RP∞'· ℓ) (RP∞'· ℓ) A (push (true , true , inl (inr (e , pf , g , f , p))) k))
                  (ΠR-extend→Inl (RP∞'· ℓ) true (RP∞'· ℓ) (fst e true) A (g true) f)
                  (inr-inl-inr* (RP∞'· ℓ) (RP∞'· ℓ) e A g .fst))) ]
         ((g : (i j : Bool) → A i j)
         → SquareP (λ i j → Targ (RP∞'· ℓ) (RP∞'· ℓ) A
                               (push (true , true , push (inr (e , pf , g)) i) j))
                    (t (λ i → g i (fst e i)) (g false) refl)
                    (ΠR-extend→Inl≡ A (g true true) (g false) ◁ coh-inr A g)
                    (λ i → ΠR-extend→Inl (RP∞'· ℓ) true (RP∞'· ℓ) (pf i) A (g true (pf i)) (g false))
                    (inr-inl-inr* (RP∞'· ℓ) (RP∞'· ℓ) e A (λ i → g i (fst e i)) .snd g λ _ → refl))

  push-inr*-bool-filler : (A : Bool → Bool → Type ℓ)
    → (g : (i j : Bool) → A i j)
    → (i j k : _) → _
  push-inr*-bool-filler A g i j k =
    hfill (λ k
      → λ {(i = i0) → doubleWhiskFiller
                         (ΠR-extend→Inl≡ A (g true true) (g false))
                         (coh-eq1 A (λ i → g i i) (g false) refl)
                         (cong fst (sym (inr-inl-inr*≡ (RP∞'· ℓ) A (λ i → g i i)))) k j
          ; (i = i1) → doubleWhiskFiller
                         (ΠR-extend→Inl≡ A (g true true) (g false))
                         (coh-inr A g)
                         (λ _ → inr-inr (RP∞'· ℓ) (RP∞'· ℓ) A g) k j
          ; (j = i0) → ΠR-extend→Inl≡ A (g true true) (g false) (~ k)
          ; (j = i1) → inr-inl-inr*≡ (RP∞'· ℓ) A (λ i → g i i) (~ k) .snd g (λ _ → refl) i})
          (inS (coh-eq2 A g i j))
          k

  push-inr*-bool : (A : Bool → Bool → Type ℓ) → push-inr*-ty A (idEquiv _) refl
  fst (push-inr*-bool A) g f p =
      ΠR-extend→Inl≡ A (g true) f
    ◁ coh-eq1 A g f p
    ▷ cong fst (sym (inr-inl-inr*≡ (RP∞'· ℓ) A g))
  snd (push-inr*-bool A) g i j = push-inr*-bool-filler A g i j i1

  push-inl*-bool : (A : Bool → Bool → Type ℓ) (g : (i j : Bool) → A i j)
    → SquareP
        (λ i j → Targ (RP∞'· ℓ) (RP∞'· ℓ) A (push (true , true , push (inl g) i) j))
        (ΠR-extend→Inl≡ A (g true true) (g false)
          ◁ push-inl A (λ i₁ → g i₁ true) (g false) refl
          ▷ cong fst (sym (inr-inl-inl*≡ (RP∞'· ℓ) A (λ i₂ → g i₂ true))))
        (ΠR-extend→Inl≡ A (g true true) (g false) ◁ coh-inr A g)
        (λ _ → ΠR-extend→Inl (RP∞'· ℓ) true (RP∞'· ℓ) true A
                 (g true true) (g (RP'.notI (RP∞'· ℓ) true)))
         (inr-inl-inl* (RP∞'· ℓ) (RP∞'· ℓ) true A (λ i₁ → g i₁ true) .snd g λ _ → refl)
  push-inl*-bool A g i j =
    hcomp (λ k
      → λ {(i = i0) → doubleWhiskFiller
                         (ΠR-extend→Inl≡ A (g true true) (g false))
                         (push-inl A (λ i₁ → g i₁ true) (g false) refl)
                         (cong fst (sym (inr-inl-inl*≡ (RP∞'· ℓ) A (λ i → g i true)))) k j
          ; (i = i1) → doubleWhiskFiller
                         (ΠR-extend→Inl≡ A (g true true) (g false))
                         (coh-inr A g)
                         (λ _ → inr-inr (RP∞'· ℓ) (RP∞'· ℓ) A g) k j
          ; (j = i0) → ΠR-extend→Inl≡ A (g true true) (g false) (~ k)
          ; (j = i1) → inr-inl-inl*≡ (RP∞'· ℓ) A (λ i → g i true) (~ k) .snd g (λ _ → refl) i})
          (coh-eq-l A g i j)

  push-inr* : (A : Bool → Bool → Type ℓ) (e : Bool ≃ Bool) (pf : fst e true ≡ true)
    → push-inr*-ty A e pf
  push-inr* A = Bool≃Bool-elim-id _ (push-inr*-bool A)

  push-inr*≡ : (A : Bool → Bool → Type ℓ)
    → push-inr* A (idEquiv _) refl ≡ push-inr*-bool A
  push-inr*≡ A = Bool≃Bool-elim-idβ _ (push-inr*-bool A)

  cohr-b : (A : Bool → Bool → Type ℓ)
      (x : TY (RP∞'· ℓ) (RP∞'· ℓ) A true true)
        → PathP (λ k → Targ (RP∞'· ℓ) (RP∞'· ℓ) A (push (true , true , x) k))
         (ΠR-extend→Inl (RP∞'· ℓ) true (RP∞'· ℓ) (fst (fst (TY→Lₗ (RP∞'· ℓ) (RP∞'· ℓ) A true true x))) A
           (snd (fst (TY→Lₗ (RP∞'· ℓ) (RP∞'· ℓ) A true true x))) (snd (TY→Lₗ (RP∞'· ℓ) (RP∞'· ℓ) A true true x)))
         (ΠR-extend→Inr (RP∞'· ℓ) (RP∞'· ℓ) A (TY→R (RP∞'· ℓ) (RP∞'· ℓ) A true true x))
  cohr-b A (inl (inl (f , g , p))) =
      ΠR-extend→Inl≡ A (f true) g
    ◁ push-inl A f g p
    ▷ cong fst (sym (inr-inl-inl*≡ (RP∞'· ℓ) A f))
  cohr-b A (inl (inr (e , pf , g , p , q))) = push-inr* A e pf .fst g p q
  cohr-b A (inr x) = ΠR-extend→Inl≡ A (x true true) (x false) ◁ coh-inr A x
  cohr-b A (push (inl g) i) j = push-inl*-bool A g i j
  cohr-b A (push (inr (e , pf , g)) i) j = push-inr* A e pf .snd g i j

  cohr' : (J : RP∞' ℓ) (j : fst J) (A : Bool → fst J → Type ℓ)
    → (x : TY (RP∞'· ℓ) J A true j) → PathP (λ k → Targ (RP∞'· ℓ) J A (push (true , j , x) k))
         (ΠR-extend→Inl (RP∞'· ℓ) true J (fst (fst (TY→Lₗ (RP∞'· ℓ)  J A true j x))) A
           (snd (fst (TY→Lₗ (RP∞'· ℓ) J A true j x))) (snd (TY→Lₗ (RP∞'· ℓ) J A true j x)))
         (ΠR-extend→Inr (RP∞'· ℓ) J A (TY→R (RP∞'· ℓ) J A true j x))
  cohr' = JRP∞' cohr-b

  cohr : (I : RP∞' ℓ) (i : fst I) (J : RP∞' ℓ) (j : fst J) (A : fst I → fst J → Type ℓ)
    → (x : TY I J A i j) → PathP (λ k → Targ I J A (push (i , j , x) k))
         (ΠR-extend→Inl I i J (fst (fst (TY→Lₗ I J A i j x))) A
           (snd (fst (TY→Lₗ I J A i j x))) (snd (TY→Lₗ I J A i j x)))
         (ΠR-extend→Inr I J A (TY→R I J A i j x))
  cohr = JRP∞' cohr'

  ΠR-extend→ : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) → (x : ΠR-extend** I J A) → Targ I J A x
  ΠR-extend→ I J A (inl (f , (j , a) , b)) = ΠR-extend→Inl I f J j A a b
  ΠR-extend→ I J A (inr x) = ΠR-extend→Inr I J A x
  ΠR-extend→ I J A (push (i , j , x) k) = cohr I i J j A x k


  module ID (G : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) → (x : ΠR-extend** I J A) → (i : fst I) → Targ I J A x)
            (G-inler : (A : Bool → Bool → Type ℓ) (a : A true true) (b : TotΠ (A false)) (i : Bool)
                    → G (RP∞'· ℓ) (RP∞'· ℓ) A (inl (true , (true , a) , b)) i ≡ inler A a b)
            (G-inr-inr : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) (t : (i : fst I) (j : fst J) → A i j)
                       (i : fst I)
                  → G I J A (inr (inr t)) i ≡ inr-inr I J A t)
            (G-inr-inl-inl₁ : (I : RP∞' ℓ) (A : fst I → Bool → Type ℓ)
                        (f : (x : fst I) → A x true) (i : fst I)
                     → (G I (RP∞'· ℓ) A (inr (inl (inl true , f))) i)
                       ≡ inr-inl-inl I A f .fst)
            (G-inr-inl-inl₂ : (I : RP∞' ℓ) (A : fst I → Bool → Type ℓ)
                        (f : (x : fst I) → A x true) (i : fst I)
                        (p : (i₁ : fst I) (j : Bool) → A i₁ j) (q : (x : fst I) → p x true ≡ f x)
                     → SquareP (λ i j → Targ I (RP∞'· ℓ) A (inr (push ((inl true , f) , p , q) j)))
                                (λ k → G I (RP∞'· ℓ) A (inr (push ((inl true , f) , p , q) k)) i)
                                (inr-inl-inl I A f .snd p q)
                                (G-inr-inl-inl₁ I A f i)
                                (G-inr-inr I (RP∞'· ℓ) A p i))
            (G-inr-inl-inr₁ : (I : RP∞' ℓ) (A : fst I → fst I → Type ℓ)
              (f : (i : fst I) → A i i) (i : fst I)
              → G I I A (inr (inl (inr (idEquiv (fst I)) , f))) i ≡ inr-inl-inr I A f .fst)
            (G-inr-inl-inr₂ : (I : RP∞' ℓ) (A : fst I → fst I → Type ℓ)
              (f : (i : fst I) → A i i) (p : (i₁ j : fst I) → A i₁ j)
                 (q : ((x : fst I) → p x x ≡ f x))
                 (i : fst I)
              → SquareP (λ i j → Targ I I A (inr (push ((inr (idEquiv (fst I)) , f) , p , q) j)))
                         (λ k → G I I A (inr (push ((inr (idEquiv (fst I)) , f) , p , q) k)) i)
                         (inr-inl-inr I A f .snd p q)
                         (G-inr-inl-inr₁ I A f i)
                         (G-inr-inr I I A p i))
            (G-push-inl : (A : Bool → Bool → Type ℓ) (f : (i : fst (RP∞'· ℓ)) → A i true)
              (g : (j : Bool) → A false j) (p : g true ≡ f false) (i : Bool)
              → SquareP (λ i j → Targ (RP∞'· ℓ) (RP∞'· ℓ) A
                                   (push (true , true , inl (inl (f , g , p))) j))
                         (λ k → G (RP∞'· ℓ) (RP∞'· ℓ) A (push (true , true , inl (inl (f , g , p))) k) i)
                         (push-inl A f g p)
                         (G-inler A (f true) g i)
                         (G-inr-inl-inl₁ (RP∞'·  ℓ) A f i))
            (G-coh-inr : (A : Bool → Bool → Type ℓ) (g : (i j : Bool) → A i j) (i : Bool)
           → SquareP (λ i j → Targ (RP∞'· ℓ) (RP∞'· ℓ) A (push (true , true , inr g) j))
                      (λ k → G (RP∞'· ℓ) (RP∞'· ℓ) A (push (true , true , inr g) k) i)
                      (coh-inr A g)
                      (G-inler A (g true true) (g false) i)
                      (G-inr-inr (RP∞'· ℓ) (RP∞'· ℓ) A g i))
            (G-coh-eq1 : (A : Bool → Bool → Type ℓ) (g : (i : Bool) → A i i) (f : TotΠ (A false)) (p : f false ≡ g false) (x : Bool)
                     → SquareP (λ i j → Targ (RP∞'· ℓ) (RP∞'· ℓ) A (push (true , true , inl (inr (idEquiv Bool , refl , g , f , p))) j))
                       (λ i → G (RP∞'· ℓ) (RP∞'· ℓ) A (push (true , true , inl (inr (idEquiv Bool , refl , g , f , p))) i) x)
                       (coh-eq1 A g f p)
                       (G-inler A (g true) f x)
                       (G-inr-inl-inr₁ (RP∞'· ℓ) A g x))
            (G-coh-eq2 : (A : Bool → Bool → Type ℓ) (g : (i j : Bool) → A i j) (x : Bool)
           → CubeP (λ k i j → Targ (RP∞'· ℓ) (RP∞'· ℓ) A
                                (push (true , true , push (inr (idEquiv Bool , refl , g)) i) j))
               (λ i j → G (RP∞'· ℓ) (RP∞'· ℓ) A (push (true , true , push (inr (idEquiv Bool , refl , g)) i) j) x)
               (coh-eq2 A g)
               (G-coh-eq1 A (λ i → g i i) (g false) refl x)
               (G-coh-inr A g x)
               (λ i _ → G-inler A (g true true) (g false) x i)
               (G-inr-inl-inr₂ (RP∞'· ℓ) A (λ i → g i i) g (λ i → refl) x))
            (G-coh-eq-l :
              (A : Bool → Bool → Type ℓ) (g : (i j : Bool) → A i j) (x : Bool)
           → CubeP (λ k i j → Targ (RP∞'· ℓ) (RP∞'· ℓ) A
                                (push (true , true , push (inl g) i) j))
               (λ i j → G (RP∞'· ℓ) (RP∞'· ℓ) A (push (true , true , push (inl g) i) j) x)
               (coh-eq-l A g)
               (G-push-inl A (λ i → g i true) (g false) refl x)
               (G-coh-inr A g x)
               (λ i _ → G-inler A (g true true) (g false) x i)
               (G-inr-inl-inl₂ (RP∞'· ℓ) A (λ i → g i true) x g (λ _ → refl)))
            where
    GID-inl'' : (A : Bool → Bool → Type ℓ)
      (a : A true true) (f : (j : Bool) → A false j) (x : Bool)
      → G (RP∞'· ℓ) (RP∞'· ℓ) A (inl (true , (true , a) , f)) x ≡ ΠR-extend→Inl (RP∞'· ℓ) true (RP∞'· ℓ) true A a f
    GID-inl'' A a f x = G-inler A a f x ∙ sym (ΠR-extend→Inl≡ A a f)

    GID-inl' : (J : RP∞' ℓ) (j : fst J) (A : Bool → fst J → Type ℓ)
      (a : A true j) (f : (j : fst J) → A false j) (x : Bool)
      → G (RP∞'· ℓ) J A (inl (true , (j , a) , f)) x ≡ ΠR-extend→Inl (RP∞'· ℓ) true J j A a f
    GID-inl' = JRP∞' GID-inl''

    GID-inl : (I : RP∞' ℓ) (i : fst I) (J : RP∞' ℓ) (j : fst J) (A : fst I → fst J → Type ℓ)
      (a : A i j) (f : (j : fst J) → A (RP'.notI I i) j) (x : fst I)
      → G I J A (inl (i , (j , a) , f)) x ≡ ΠR-extend→Inl I i J j A a f
    GID-inl = JRP∞' GID-inl'

    GID-inl≡ : (A : Bool → Bool → Type ℓ)
      (a : A true true) (f : (j : Bool) → A false j) (x : Bool)
        → GID-inl (RP∞'· ℓ) true (RP∞'· ℓ) true A a f x
        ≡ GID-inl'' A a f x -- G-inler A a f x ∙ sym (ΠR-extend→Inl≡ A a f)
    GID-inl≡ A a f x =
        (λ i → h1 i (RP∞'· ℓ) true A a f x)
      ∙ λ i → h2 i A a f x
      where
      h1 : GID-inl (RP∞'· ℓ) true ≡ GID-inl'
      h1 = JRP∞'∙ GID-inl'

      h2 : GID-inl' (RP∞'· ℓ) true ≡ GID-inl''
      h2 = JRP∞'∙ GID-inl''

    G-inr-inl-inl*-TY : (I : RP∞' ℓ) (J : RP∞' ℓ) (j : fst J)
      (A : fst I → fst J → Type ℓ)
      (f : (i : fst I) → A i j) (i : fst I)
      → Type ℓ
    G-inr-inl-inl*-TY I J j A f i =
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
      hfill (λ r → λ {(k = i0) → compPath-filler
                                      (G-inr-inl-inl₁ I A f i)
                                      (λ i₁ → fst (inr-inl-inl*≡ I A f (~ i₁))) r j
                        ; (k = i1) → G-inr-inr I (RP∞'· ℓ) A g i j
                        ; (j = i0) → G I (RP∞'· ℓ) A (inr (push (((inl true) , f) , g , p) k)) i
                        ; (j = i1) → snd (inr-inl-inl*≡ I A f (~ r)) g p k})
              (inS (G-inr-inl-inl₂ I A f i g p j k))
              r

    G-inr-inl-inl*-bool : (I : RP∞' ℓ)
      (A : fst I → Bool → Type ℓ)
      (f : (i : fst I) → A i true) (i : fst I)
      → G-inr-inl-inl*-TY I (RP∞'· ℓ) true A f i
    fst (G-inr-inl-inl*-bool I A f i) =
      G-inr-inl-inl₁ I A f i ∙ cong fst (sym (inr-inl-inl*≡ I A f))
    snd (G-inr-inl-inl*-bool I A f i) g p j k =
      G-inr-inl-inl*-bool-diag-fill I A f i g p j k i1

    abstract
      G-inr-inl-inl*-full : (I : RP∞' ℓ) (J : RP∞' ℓ) (j : fst J)
        (A : fst I → fst J → Type ℓ)
        (f : (i : fst I) → A i j) (i : fst I)
        → G-inr-inl-inl*-TY I J j A f i
      G-inr-inl-inl*-full I = JRP∞' (G-inr-inl-inl*-bool I)

      G-inr-inl-inl*-full≡ : (I : RP∞' ℓ)
        (A : fst I → Bool → Type ℓ)
        (f : (i : fst I) → A i true) (i : fst I)
        → G-inr-inl-inl*-full I (RP∞'· ℓ) true A f i ≡ G-inr-inl-inl*-bool I A f i
      G-inr-inl-inl*-full≡ I A f i w = cool w A f i
        where
        cool : G-inr-inl-inl*-full I (RP∞'· ℓ) true ≡ G-inr-inl-inl*-bool I
        cool = JRP∞'∙ (G-inr-inl-inl*-bool I)

    G-inr-inl-inl*₁ : (I : RP∞' ℓ) (J : RP∞' ℓ) (j : fst J) (A : fst I → fst J → Type ℓ)
      → (f : (i : fst I) → A i j)
      → (i : fst I)
      → G I J A (inr (inl (inl j , f))) i ≡ inr-inl-inl* I J j A f .fst
    G-inr-inl-inl*₁ I = JRP∞' λ A f x
      → G-inr-inl-inl₁ I A f x ∙ cong fst (sym (inr-inl-inl*≡ I A f))

    G-inr-inl-inr*-TY : (I J : RP∞' ℓ) (e : fst I ≃ fst J)
      (A : fst I → fst J → Type ℓ)
      (i : fst I)
      → Type ℓ
    G-inr-inl-inr*-TY I J e A i =
      Σ[ p1 ∈ ((f : (i : fst I) → A i (fst e i))
              → G I J A (inr (inl (inr e , f))) i
               ≡ ΠR-extend→ I J A (inr (inl (inr e , f)))) ]
          ((f : (i₁ : fst I) → A i₁ (fst e i₁))
                (g : (i : fst I) (j : fst J) → A i j)
                (p : (i : fst I) → g i (fst e i) ≡ f i)
          → SquareP (λ k j → Targ I J A (inr (push ((inr e , f) , g , p) j)))
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
      hfill (λ r → λ {(k = i0) → compPath-filler
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
      → G-inr-inl-inr*-TY I I (idEquiv (fst I)) A i
    fst (G-inr-inl-inr*-diag I A i) f =
        G-inr-inl-inr₁ I A f i
      ∙ cong fst (sym (inr-inl-inr*≡ I A f))
    snd (G-inr-inl-inr*-diag I A i) f g p j k =
      G-inr-inl-inr*-diag-fill I A f g p i j k i1

    abstract
      G-inr-inl-inr*-full : (I J : RP∞' ℓ) (e : fst I ≃ fst J)
        (A : fst I → fst J → Type ℓ)
        (i : fst I)
        → G-inr-inl-inr*-TY I J e A i
      G-inr-inl-inr*-full I =
        JRP∞'' I (G-inr-inl-inr*-diag I)

      G-inr-inl-inr*≡ : (I : RP∞' ℓ)
        (A : fst I → fst I → Type ℓ)
        (i : fst I)
        → G-inr-inl-inr*-full I I (idEquiv _) A i ≡ G-inr-inl-inr*-diag I A i
      G-inr-inl-inr*≡ I A i k = help k A i
        where
        help : G-inr-inl-inr*-full I I (idEquiv _) ≡ G-inr-inl-inr*-diag I
        help = JRP∞''-refl I (G-inr-inl-inr*-diag I)

    GID-inr : (I : RP∞' ℓ) (i : fst I) (J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) (x : _)
      → G I J A (inr x) i
      ≡ ΠR-extend→ I J A (inr x)
    GID-inr I i J A (inl (inl x , f)) = G-inr-inl-inl*-full I J x A f i .fst
    GID-inr I i J A (inl (inr e , f)) = G-inr-inl-inr*-full I J e A i .fst f
    GID-inr I i J A (inr x) = G-inr-inr I J A x i
    GID-inr I i J A (push ((inl x , f) , g , p) j) k = G-inr-inl-inl*-full I J x A f i .snd g p k j
    GID-inr I i J A (push ((inr x , f) , g , p) j) k = G-inr-inl-inr*-full I J x A i .snd f g p k j

    module _ (A : Bool → Bool → Type ℓ)
            (k : Bool)
            (x : _) where

      help-inr''-fill : (i j r : _)
              → _
      help-inr''-fill i j r =
        hfill (λ r → λ { (i = i0) → G (RP∞'· ℓ) (RP∞'· ℓ) A (push (true , true , inr x) j) k
                        ; (i = i1) → doubleWhiskFiller (ΠR-extend→Inl≡ A (x true true) (x false)) (coh-inr A x) refl r j
                        ; (j = i0) → compPath-filler
                                        (G-inler A (x true true) (x false) k)
                                        (sym (ΠR-extend→Inl≡ A (x true true) (x false))) r i
                        ; (j = i1) → G-inr-inr (RP∞'· ℓ) (RP∞'· ℓ) A x k i})
              (inS (G-coh-inr A x k i j))
              r

      help-inr'' :
          SquareP (λ t s → Targ (RP∞'· ℓ) (RP∞'· ℓ) A (push (true , true , inr x) s))
             (λ s → G (RP∞'· ℓ) (RP∞'· ℓ) A (push (true , true , inr x) s) k)
             (ΠR-extend→Inl≡ A (x true true) (x false) ◁ coh-inr A x)
             (G-inler A (x true true) (x false) k ∙ sym (ΠR-extend→Inl≡ A (x true true) (x false)))
             (G-inr-inr (RP∞'· ℓ) (RP∞'· ℓ) A x k)
      help-inr'' i j = help-inr''-fill i j i1

      help-inr'-fill : (i j r : _)
              → _
      help-inr'-fill i j r =
        hfill (λ r → λ { (i = i0) →  G (RP∞'· ℓ) (RP∞'· ℓ) A (push (true , true , inr x) j) k
                        ; (i = i1) → (ΠR-extend→Inl≡ A (x true true) (x false) ◁ coh-inr A x) j
                        ; (j = i0) → GID-inl≡ A (x true true) (x false) k (~ r) i
                        ; (j = i1) → G-inr-inr (RP∞'· ℓ) (RP∞'· ℓ) A x k i})
               (inS (help-inr'' i j))
              r

      help-inr' :
         SquareP (λ t s → Targ (RP∞'· ℓ) (RP∞'· ℓ) A (push (true , true , inr x) s))
             (λ s → G (RP∞'· ℓ) (RP∞'· ℓ) A (push (true , true , inr x) s) k)
             (ΠR-extend→Inl≡ A (x true true) (x false) ◁ coh-inr A x)
             (GID-inl (RP∞'· ℓ) true (RP∞'· ℓ) true A (x true true)
              (x false) k)
             (G-inr-inr (RP∞'· ℓ) (RP∞'· ℓ) A x k)
      help-inr' i j = help-inr'-fill i j i1

    module _ (A : Bool → Bool → Type ℓ)
            (k : Bool) (f : (i : Bool) → A i true) (g : (j : Bool) → A false j)
            (p : g true ≡ f false) where

      help-inl-inl-btm-fill : (i j r : _) → _
      help-inl-inl-btm-fill i j r =
        hfill (λ r → λ {(i = i0) → G (RP∞'· ℓ) (RP∞'· ℓ) A
                                    (push (true , true , inl (inl (f , g , p))) j) k
                     ; (i = i1) → doubleWhiskFiller
                                    (ΠR-extend→Inl≡ A (f true) g)
                                    (push-inl A f g p)
                                    (sym (cong fst (inr-inl-inl*≡ (RP∞'· ℓ) A f))) r j
                     ; (j = i0) → compPath-filler
                                      (G-inler A (f true) g k)
                                      (sym (ΠR-extend→Inl≡ A (f true) g)) r i
                     ; (j = i1) → compPath-filler
                                    (G-inr-inl-inl₁ (RP∞'· ℓ) A f k)
                                    (λ i₁ → fst (inr-inl-inl*≡ (RP∞'· ℓ) A f (~ i₁))) r i
                     })
              (inS (G-push-inl A f g p k i j))
              r


      help-inl-inl :
             SquareP (λ t s → Targ (RP∞'· ℓ) (RP∞'· ℓ) A
                                (push (true , true , inl (inl (f , g , p))) s))
                (λ s → G (RP∞'· ℓ) (RP∞'· ℓ) A
                    (push (true , true , inl (inl (f , g , p))) s) k)
                (cohr-b A (inl (inl (f , g , p))))
                (GID-inl (RP∞'· ℓ) true (RP∞'· ℓ) true A (f true) g k)
                (G-inr-inl-inl*-full (RP∞'· ℓ) (RP∞'· ℓ) true A f k .fst)
      help-inl-inl i j =
        hcomp (λ r → λ {(i = i0) → G (RP∞'· ℓ) (RP∞'· ℓ) A
                                    (push (true , true , inl (inl (f , g , p))) j) k
                     ; (i = i1) → cohr-b A (inl (inl (f , g , p))) j
                     ; (j = i0) → GID-inl≡ A (f true) g k (~ r) i
                     ; (j = i1) → G-inr-inl-inl*-full≡ (RP∞'· ℓ) A f k (~ r) .fst i})
         (help-inl-inl-btm-fill i j i1)

    help-inl-inr-TY : (A : Bool → Bool → Type ℓ) (k : Bool)
      (e : Bool ≃ Bool) (pf : fst e true ≡ true)
        → Type ℓ
    help-inl-inr-TY A k e pf =
      Σ[ h ∈ (
        (f : (i : Bool) → A i (fst e i))
        (g : (j : Bool) → A false j)
        (p : g (fst e false) ≡ f false)
        → SquareP (λ i j → Targ (RP∞'· ℓ) (RP∞'· ℓ) A
                             (push (true , true , inl (inr (e , pf , f , g , p))) j))
                  (λ j → G (RP∞'· ℓ) (RP∞'· ℓ) A (push (true , true , inl (inr (e , pf , f , g , p))) j) k)
                  (push-inr* A e pf .fst f g p)
                  (GID-inl (RP∞'· ℓ) true (RP∞'· ℓ) (fst e true) A (f true) g k)
                  (G-inr-inl-inr*-full (RP∞'· ℓ) (RP∞'· ℓ) e A k .fst f)
               ) ]
          ((g : (i j : Bool) → A i j)
          → (CubeP (λ j i l → Targ (RP∞'· ℓ) (RP∞'· ℓ) A
                (push (true , true , push (inr (e , pf , g)) i) l))
                (λ i l → G (RP∞'· ℓ) (RP∞'· ℓ) A (push (true , true , push (inr (e , pf , g)) i) l) k)
                (push-inr* A e pf .snd g) -- j = i1
                (h (λ i₁ → g i₁ (fst e i₁)) (g false) refl)
                (help-inr' A k g)
                (λ j i → GID-inl (RP∞'· ℓ) true (RP∞'· ℓ) (pf i) A (g true (pf i)) (g (RP'.notI (RP∞'· ℓ) true)) k j)
                (G-inr-inl-inr*-full (RP∞'· ℓ) (RP∞'· ℓ) e A k .snd (λ i₁ → g i₁ (fst e i₁)) g (λ _ → refl))))

    help-inl-inr-id : (A : Bool → Bool → Type ℓ) (k : Bool)
      → help-inl-inr-TY A k (idEquiv _) refl
    fst (help-inl-inr-id A k) f g p i j =
      hcomp (λ r → λ {(i = i0) → G (RP∞'· ℓ) (RP∞'· ℓ) A (push (true , true , inl (inr (idEquiv Bool , refl , f , g , p))) j) k
                     ; (i = i1) → push-inr*≡ A (~ r) .fst f g p j
                     ; (j = i0) → GID-inl≡ A (f true) g k (~ r) i
                     ; (j = i1) → G-inr-inl-inr*≡ (RP∞'· ℓ) A k (~ r) .fst f i})
       (hcomp (λ r → λ {(i = i0) → G (RP∞'· ℓ) (RP∞'· ℓ) A (push (true , true , inl (inr (idEquiv Bool , refl , f , g , p))) j) k
                     ; (i = i1) → doubleWhiskFiller
                                     (ΠR-extend→Inl≡ A (f true) g)
                                     (coh-eq1 A f g p)
                                     (cong fst (sym (inr-inl-inr*≡ (RP∞'· ℓ) A f)))
                                     r j
                     ; (j = i0) → compPath-filler (G-inler A (f true) g k) (sym (ΠR-extend→Inl≡ A (f true) g)) r i
                     ; (j = i1) → compPath-filler (G-inr-inl-inr₁ (RP∞'· ℓ) A f k)
                                    (λ i₁ → fst (inr-inl-inr*≡ (RP∞'· ℓ) A f (~ i₁)))
                                    r i})
              (G-coh-eq1 A f g p k i j))
    snd (help-inl-inr-id A k) g j i l =
      hcomp (λ r → λ {(i = i1) → help-inr'-fill A k g j l r
                     ; (j = i0) → G (RP∞'· ℓ) (RP∞'· ℓ) A (push (true , true , push (inr (idEquiv Bool , refl , g)) i) l) k
                     ; (j = i1) → push-inr*≡ A (~ r) .snd g i l
                     ; (l = i0) → GID-inl≡ A (g true true) (g false) k (~ r) j
                     ; (l = i1) → G-inr-inl-inr*≡ (RP∞'· ℓ) A k (~ r) .snd (λ i → g i i) g (λ _ → refl) j i
                     })
       (hcomp (λ r → λ {(i = i1) → help-inr''-fill A k g j l r
                     ; (j = i0) → G (RP∞'· ℓ) (RP∞'· ℓ) A (push (true , true , push (inr (idEquiv Bool , refl , g)) i) l) k
                     ; (j = i1) → push-inr*-bool-filler A g i l r
                     ; (l = i0) → compPath-filler (G-inler A (g true true) (g false) k)
                                                   (sym (ΠR-extend→Inl≡ A (g true true) (g false))) r j
                     ; (l = i1) → G-inr-inl-inr*-diag-fill (RP∞'· ℓ) A (λ i → g i i) g (λ _ → refl) k j i r
                     })
             (G-coh-eq2 A g k j i l))

    help-inl-inr : (A : Bool → Bool → Type ℓ) (k : Bool)
      (e : Bool ≃ Bool) (pf : fst e true ≡ true)
      → help-inl-inr-TY A k e pf
    help-inl-inr A k = Bool≃Bool-elim-id _ (help-inl-inr-id A k)

    help' : (A : Bool → Bool → Type ℓ)
            (k : Bool)
            (a : TY (RP∞'· ℓ) (RP∞'· ℓ) A true true)
         → SquareP (λ t s → Targ (RP∞'· ℓ) (RP∞'· ℓ) A (push (true , true , a) s))
                    (λ s → G (RP∞'· ℓ) (RP∞'· ℓ) A (push (true , true , a) s) k)
                    (cohr-b A a)
                    (GID-inl (RP∞'· ℓ) true (RP∞'· ℓ)
                      (fst (fst (TY→Lₗ (RP∞'· ℓ) (RP∞'· ℓ) A true true a))) A
                      (snd (fst (TY→Lₗ (RP∞'· ℓ) (RP∞'· ℓ) A true true a)))
                      (snd (TY→Lₗ (RP∞'· ℓ) (RP∞'· ℓ) A true true a)) k)
                    (GID-inr (RP∞'· ℓ) k (RP∞'· ℓ) A
                      (TY→R (RP∞'· ℓ) (RP∞'· ℓ) A true true a))
    help' A k (inl (inl (f , g , p))) = help-inl-inl A k f g p
    help' A k (inl (inr (e , pf , f , g , p))) = help-inl-inr A k e pf .fst f g p
    help' A k (inr x) = help-inr' A k x
    help' A k (push (inl g) i) j l =
      hcomp (λ r → λ {(i = i1) → help-inr'-fill A k g j l r
                    ; (j = i0) → G (RP∞'· ℓ) (RP∞'· ℓ) A (push (true , true , push (inl g) i) l) k
                    ; (j = i1) → push-inl*-bool A g i l
                    ; (l = i0) → GID-inl≡ A (g true true) (g false) k (~ r) j
                    ; (l = i1) → G-inr-inl-inl*-full≡ (RP∞'· ℓ) A (λ i → g i true) k (~ r) .snd g (λ _ → refl) j i
                    })
            (hcomp (λ r → λ {
                    (i = i0) → help-inl-inl-btm-fill A k (λ i → g i true) (g false) refl j l r
                    ; (i = i1) → help-inr''-fill A k g j l r
                    ; (j = i0) → G (RP∞'· ℓ) (RP∞'· ℓ) A (push (true , true , push (inl g) i) l) k
                    ; (l = i0) → help-inl-inl-btm-fill A k (λ i₁ → g i₁ true) (g false) (λ _ → g false true) j i0 r
                    ; (l = i1) → G-inr-inl-inl*-bool-diag-fill (RP∞'· ℓ) A (λ i → g i true) k g (λ _ → refl) j i r
                    })
              (G-coh-eq-l A g k j i l))
    help' A k (push (inr (e , pf , g)) i) j l = help-inl-inr A k e pf .snd g j i l

    GID : (I : RP∞' ℓ) (i : fst I) (J : RP∞' ℓ)
      (A : fst I → fst J → Type ℓ) (x : _)
      → G I J A x i ≡ ΠR-extend→ I J A x
    GID I k J A (inl (i , (j , a) , f)) = GID-inl I i J j A a f k
    GID I k J A (inr x) = GID-inr I k J A x
    GID I k J A (push (i , j , a) s) t = help I i J j A k a t s
      where
      cohr-id : (A : Bool → Bool → Type ℓ) (k : Bool)
        (a : TY (RP∞'· ℓ) (RP∞'· ℓ) A true true)
        → cohr (RP∞'· ℓ) true (RP∞'· ℓ) true A a
        ≡ cohr-b A a
      cohr-id A k a = (λ i → h i (RP∞'· ℓ) true A a)
                     ∙ λ i → h2 i A a
        where
        h : cohr (RP∞'· ℓ) true ≡ cohr'
        h = JRP∞'∙ cohr'

        h2 : cohr' (RP∞'· ℓ) true ≡ cohr-b
        h2 = JRP∞'∙ cohr-b

      help : (I : RP∞' ℓ) (i : fst I) (J : RP∞' ℓ) (j : fst J)
             (A : fst I → fst J → Type ℓ)
             (k : fst I) (a : TY I J A i j)
          → SquareP (λ t s → Targ I J A (push (i , j , a) s))
                     (λ s → G I J A (push (i , j , a) s) k)
                     (cohr I i J j A a)
                     (GID-inl I i J (fst (fst (TY→Lₗ I J A i j a))) A
                       (snd (fst (TY→Lₗ I J A i j a))) (snd (TY→Lₗ I J A i j a)) k)
                     (GID-inr I k J A (TY→R I J A i j a))
      help = JRP∞' (JRP∞' λ A k a → help' A k a ▷ sym (cohr-id A k a))
