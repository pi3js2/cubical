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

Bool≃Bool-elim-id : ∀ {ℓ} (A : (e : Bool ≃ Bool) (p : fst e true ≡ true) → Type ℓ)
  → (a : A (idEquiv _) refl)
  → Σ[ f ∈ ((e : Bool ≃ Bool) (p : fst e true ≡ true) → A e p) ] (f (idEquiv _) refl ≡ a)
Bool≃Bool-elim-id A a = (λ e p → l .fst e p)
  , funExt⁻ (l .snd .fst) refl
  ∙ cong (λ x → subst (A (idEquiv Bool)) x a)
      (isSet→isGroupoid isSetBool true true refl refl
        (isSetBool true true refl refl) refl)
  ∙ transportRefl a -- (funExt⁻ (l .snd .fst) refl)
  where
  l = Bool≃Bool-elim (λ e → (p : fst e true ≡ true) → A e p)
        (λ p → subst (A (idEquiv Bool)) (isSetBool _ _ refl p) a)
        λ p → ⊥.rec (false≢true p)

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


  leftFun-cohₗ** : (i' : fst I) (j : fst J) (a : TY I J A i' j)
    → inlR (TY→L I J A i' j a .snd .fst) ≡ leftFun-inr i' (TY→R I J A i' j a)
  leftFun-cohₗ** i' j (inl (inl x)) = refl
  leftFun-cohₗ** i' j (inl (inr x)) = refl
  leftFun-cohₗ** i' j (inr x) = push* (j , (x i' j)) (x i') refl
  leftFun-cohₗ** i' j (push (inl x) i) k = push* (j , x i' j) (x i') (λ _ → x i' j) (i ∧ k)
  leftFun-cohₗ** i' j (push (inr (e , p , f)) i) k =
    hcomp (λ r → λ {(i = i0) → inlR (p (~ r) , f i' (p (~ r)))
                   ; (i = i1) → push* (j , f i' j) (f i') (λ _ → f i' j) k
                   ; (k = i0) → inlR ((p (i ∨ ~ r)) , (f i' (p (i ∨ ~ r))))
                   ; (k = i1) → push* (p (~ r) , f i' (p (~ r))) (f i') (λ i → f i' (p (~ r))) i})
          (push* (j , f i' j) (f i') (λ _ → f i' j) (i ∧ k))

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

Better! : ∀ {ℓ} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) → Type ℓ
Better! I J A =
  Pushout {A = fst I × ΠR-extend** I J A}
  {B = Σ[ i ∈ fst I ] joinR-gen (fst J) (A i)} {C = ΠR-extend** I J A} (λ x → fst x , leftMap** I J A (fst x) (snd x)) snd

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


module _ {ℓ : Level} {Targ : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) → ΠR-extend** I J A → Type ℓ}
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
         where

  inr-inl-inl* : (I J : RP∞' ℓ) (j : fst J) (A : fst I → fst J → Type ℓ)
                        (f : (x : fst I) → A x j)
                          → Σ[ k ∈ Targ I J A (inr (inl (inl j , f))) ]
                            ((p : (i : fst I) (j : fst J) → A i j) (q : (x : fst I) → p x j ≡ f x)
                          → PathP (λ r → Targ I J A (inr (push ((inl j , f) , (p , q)) r)))
                                   k (inr-inr I J A p))
  inr-inl-inl* I = JRP∞' (inr-inl-inl I)

  inr-inl-inr* : (I J : RP∞' ℓ) (e : fst I ≃ fst J) (A : fst I → fst J → Type ℓ)
               (f : (i : fst I) → A i (fst e i))
           → Σ[ k ∈ Targ I J A (inr (inl (inr e , f))) ]
               ((p : (i : fst I) (j : fst J) → A i j) (q : (x : fst I) → p x (fst e x) ≡ f x)
            → PathP (λ r → Targ I J A (inr (push ((inr e , f) , (p , q)) r)))
                                   k (inr-inr I J A p))
  inr-inl-inr* I = JRP∞'' I (inr-inl-inr I)

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

  cohr-b : (A : Bool → Bool → Type ℓ)
      (x : TY (RP∞'· ℓ) (RP∞'· ℓ) A true true) → PathP (λ k → Targ (RP∞'· ℓ) (RP∞'· ℓ) A (push (true , true , x) k))
         (ΠR-extend→Inl (RP∞'· ℓ) true (RP∞'· ℓ) (fst (fst (TY→Lₗ (RP∞'· ℓ) (RP∞'· ℓ) A true true x))) A
           (snd (fst (TY→Lₗ (RP∞'· ℓ) (RP∞'· ℓ) A true true x))) (snd (TY→Lₗ (RP∞'· ℓ) (RP∞'· ℓ) A true true x)))
         (ΠR-extend→Inr (RP∞'· ℓ) (RP∞'· ℓ) A (TY→R (RP∞'· ℓ) (RP∞'· ℓ) A true true x))
  cohr-b A (inl (inl (f , g , p))) = {!!}
  cohr-b A (inl (inr x)) = {!!}
  cohr-b A (inr x) = {!Tyᵣ (RP∞'· ℓ) (RP∞'· ℓ) A true true!}
  cohr-b A (push (inl x) i) = {!!}
  cohr-b A (push (inr (e , p , s)) i) = {!Bool≃Bool-elim-id!}

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


-- BaseF : ∀ {ℓ} (I : RP∞' ℓ)
--   (i : fst I) (J : RP∞' ℓ)
--   (A : fst I → fst J → Type ℓ)
--   → (j : fst J) (a : A i j) (q : (j : fst J) → A (RP'.notI I i) j)
--   → (j' : fst J)
--   → joinR-gen (fst I) λ i → A i j'
-- BaseF I i J A j a q = RP'.elimI J j (inrR (RP'.elimI I i a (q j))) (inlR (RP'.notI I i , q (RP'.notI J j)))

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


-- record toData↓ {ℓ : Level}  : Type (ℓ-suc ℓ) where
--   field
--     BaseF* : (A : Bool → Bool → Type ℓ) (a : A true true)
--              (p : (j : Bool) → A false j)
--            → Σ[ goal ∈ ((i₁ : Bool) → joinR-gen Bool (λ i₂ → A i₂ i₁)) ]
--                 Path (GOALTY (RP∞'· ℓ) (RP∞'· ℓ) A) (inrR goal) (left (RP∞'· ℓ) (RP∞'· ℓ) true A (inlR (true , a)))
--               × Path (GOALTY (RP∞'· ℓ) (RP∞'· ℓ) A) (inrR goal) (left (RP∞'· ℓ) (RP∞'· ℓ) false A (inrR p))
--     eqs* : (I : RP∞' ℓ) (A : fst I → fst I → Type ℓ)
--         → Σ[ p2 ∈ ((p : (i : fst I) (j : fst I) → A i j)
--                  (f : (i : fst I) → A i i)
--                  (q : (λ i → p i i) ≡ f)
--               → (j' : fst I) → Path (joinR-gen (fst I) (λ k → A k j'))
--                 (inlR (j' , f j')) (inrR (λ j → p j j'))) ] Unit

-- record toData {ℓ : Level} : Type (ℓ-suc ℓ) where
--   field
--     BaseF** : (I : RP∞' ℓ) (i : fst I) (J : RP∞' ℓ) (j : fst J) (A : fst I → fst J → Type ℓ)
--              (a : A i j)
--              (p : (j : fst J) → A (RP'.notI I i) j)
--            → Σ[ goal ∈ ((i₁ : fst J) → joinR-gen (fst I) (λ i₂ → A i₂ i₁)) ]
--                 Path (GOALTY I J A) (inrR goal) (left I J i A (inlR (j , a)))
--               × Path (GOALTY I J A) (inrR goal) (left I J (RP'.notI I i) A (inrR p))
--     eqs** : (I J : RP∞' ℓ) (e : fst I ≃ fst J) (A : fst I → fst J → Type ℓ)
--       → Σ[ p1 ∈ ((j : fst J) → A (invEq e j) (fst e (invEq e j)) → A (invEq e j) j) ]
--         Σ[ p2 ∈ ((p : (i : fst I) (j : fst J) → A i j)
--                  (f : (i : fst I) → A i (fst e i))
--                  (q : (λ i → p i (fst e i)) ≡ f)
--               → (j' : fst J) → Path (joinR-gen (fst I) (λ k → A k j'))
--                 (inlR (invEq e j' , p1 j' (f (invEq e j')))) (inrR (λ j → p j j'))) ] Unit


-- module _ {ℓ} (e : toData {ℓ}) (e' : toData↓ {ℓ}) where
--   open toData e
--   open toData↓ e'
  
--   ΠR-extend*→ᵣ : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
--     → ΠR-base-ab* I J A → GOALTY I J A
--   ΠR-extend*→ᵣ I J A (inl (inl j , f)) = inlR (j , inrR f)
--   ΠR-extend*→ᵣ I J A (inl (inr e , f)) = inrR λ j → inlR (invEq e j , eqs** I J e A .fst j (f (invEq e j)))
--   ΠR-extend*→ᵣ I J A (inr f) = inrR λ j → inrR (λ i → f i j)
--   ΠR-extend*→ᵣ I J A (push ((inl x , f) , p , q) i) = push* (x , inrR f) (λ j → inrR λ k → p k j) (cong inrR (funExt q)) i
--   ΠR-extend*→ᵣ I J A (push ((inr e , f) , p , q) i) = inrR λ j' → eqs** I J e A .snd .fst p f (funExt q) j' i

--   ΠR-extend*→' : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) → ΠR-extend* I J A → GOALTY I J A
--   ΠR-extend*→' I J A (inl (i , (j , a) , p)) = inrR (BaseF** I i J j A a p .fst)
--   ΠR-extend*→' I J A (inr x) = ΠR-extend*→ᵣ I J A x
--   ΠR-extend*→' I J A (push (t , x) i) = {!!}

--   ΠR-extend*→'EqₗJJ : (A : Bool → Bool → Type ℓ)
--                     (a : A true true) (p : (j₁ : Bool) → A false j₁)
--                  → (i' : Bool)
--                  → left (RP∞'· ℓ) (RP∞'· ℓ) i' A (leftFun'-inl (RP∞'· ℓ) Bool A true (true , a) p i')
--                   ≡ inrR (BaseF** (RP∞'· ℓ) true (RP∞'· ℓ) true A a p .fst)
--   ΠR-extend*→'EqₗJJ A a p =
--     CasesBool true (sym (BaseF** (RP∞'· ℓ) true (RP∞'· ℓ) true A a p .snd .fst))
--                    (sym (BaseF** (RP∞'· ℓ) true (RP∞'· ℓ) true A a p .snd .snd))

--   ΠR-extend*→'EqₗJ : (J : RP∞' ℓ) (j : fst J) (A : Bool → fst J → Type ℓ)
--                     (a : A true j) (p : (j₁ : fst J) → A false j₁)
--                  → (i' : Bool)
--                  → left (RP∞'· ℓ) J i' A (leftFun'-inl (RP∞'· ℓ) (fst J) A true (j , a) p i')
--                   ≡ inrR (BaseF** (RP∞'· ℓ) true J j A a p .fst)
--   ΠR-extend*→'EqₗJ = JRP∞' ΠR-extend*→'EqₗJJ

--   ΠR-extend*→'Eqₗ : (I : RP∞' ℓ) (i : fst I) (J : RP∞' ℓ) (j : fst J) (A : fst I → fst J → Type ℓ)
--                     (a : A i j) (p : (j₁ : fst J) → A (RP'.notI I i) j₁)
--                  → (i' : fst I)
--                  → left I J i' A (leftFun'-inl I (fst J) A i (j , a) p i')
--                   ≡ inrR (BaseF** I i J j A a p .fst)
--   ΠR-extend*→'Eqₗ = JRP∞' ΠR-extend*→'EqₗJ

--   ΠR-extend*→'Eqᵣ : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
--                      (x : ΠR-base-ab* I J A)
--                    → (i' : fst I)
--                    → left I J i' A (leftFun-inr I J A i' x) ≡ ΠR-extend*→ᵣ I J A x
--   ΠR-extend*→'Eqᵣ = {!!}

--   PushoutMAP : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
--     → Pushout {A = fst I × ΠR-extend* I J A}
--                (λ x → (fst x) , leftFun*-full I J A (fst x) (snd x)) snd
--      → GOALTY I J A
--   PushoutMAP I J A (inl x) = left I J (fst x) A (snd x)
--   PushoutMAP I J A (inr x) = ΠR-extend*→' I J A x
--   PushoutMAP I J A (push (i' , x) k) = PushoutCoh I J A i' x k
--     where
--     PushoutCohL : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) (i' : fst I)
--       → (x : _)
--       → left I J i' A (leftFun*-full I J A i' (inl x)) ≡ ΠR-extend*→' I J A (inl x)
--     PushoutCohL I J A i' (i , (j , a) , p) = ΠR-extend*→'Eqₗ I i J j A a p i'

--     PushoutMain-b : {!!}
--     PushoutMain-b = {!!}

--     PMTY : (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ) (i' : Bool)
--                 → (a : ΠR-Pushout-ab* (RP∞'· ℓ) J A true)
--                   → Type ℓ
--     PMTY J A i' a =
--       Square
--       (PushoutCohL (RP∞'· ℓ) J A i' (true , ((PushTop→left-push'-ab* (RP∞'· ℓ) J A true a .fst) , (PushTop→left-push'-ab* (RP∞'· ℓ) J A true a .snd))))
--       (λ k → ΠR-extend*→'Eqᵣ (RP∞'· ℓ) J A (PushTop→ΠR-base-ab* (RP∞'· ℓ) J A true a) i' k)
--       (λ k → left (RP∞'· ℓ) J i' A (leftFun-coh (RP∞'· ℓ) J A true a i' k))
--       λ k → ΠR-extend*→' (RP∞'· ℓ) J A (push (true , a) k)

--     PushoutMainₜ : (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
--                 → (a : ΠR-Pushout-ab* (RP∞'· ℓ) J A true)
--                   → PMTY J A true a
--     PushoutMainₜ J A a = {!!} ◁ {!!} ▷ {!!}

--     PushoutMainf : (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
--                 → (a : ΠR-Pushout-ab* (RP∞'· ℓ) J A true)
--                   → PMTY J A false a
--     PushoutMainf J A a = {!!}

--     PushoutMainₗ : (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ) (i' : Bool)
--                 → (a : ΠR-Pushout-ab* (RP∞'· ℓ) J A true)
--                   → PMTY J A i' a 
--     PushoutMainₗ J A i' a = {!!} ◁ {!!} -- CasesBool true (PushoutMainₜ J A) (PushoutMainf J A)
--       where
--       help : PushoutCohL (RP∞'· ℓ) J A i' (true , PushTop→left-push'-ab* (RP∞'· ℓ) J A true a)
--            ≡ {!!}
--       help = {!!}

--     PushoutMain : (I : RP∞' ℓ) (i : fst I) (J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) (i' : fst I)
--                 → (a : ΠR-Pushout-ab* I J A i)
--                   → Square
--                      (PushoutCohL I J A i' (i , ((PushTop→left-push'-ab* I J A i a .fst) , (PushTop→left-push'-ab* I J A i a .snd))))
--                      (λ k → ΠR-extend*→'Eqᵣ I J A (PushTop→ΠR-base-ab* I J A i a) i' k)
--                      (λ k → left I J i' A (leftFun-coh I J A i a i' k))
--                      λ k → ΠR-extend*→' I J A (push (i , a) k)
--     PushoutMain = JRP∞' PushoutMainₗ

--     PushoutCoh : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) (i' : fst I)
--       → (x : ΠR-extend* I J A)
--       → left I J i' A (leftFun*-full I J A i' x) ≡ ΠR-extend*→' I J A x
--     PushoutCoh I J A i' = elimPushout
--       (PushoutCohL I J A i')
--       (λ (c : ΠR-base-ab* I J A) → ΠR-extend*→'Eqᵣ I J A c i')
--       (uncurry λ i → PushoutMain I i J A i') 

--   PushoutMAP I J A (push (i' , inl (i , (j , a) , p)) k) = ΠR-extend*→'Eqₗ I i J j A a p i' k
--   PushoutMAP I J A (push (i' , inr x) i) = ΠR-extend*→'Eqᵣ I J A x i' i
--   PushoutMAP I J A (push (i' , push (i , a) j) k) = {!!}
--     where
--     help : {!Square ? ? ?!}
--     help = {!!}

-- ΠR-extend→ₘb-inrBool : ∀ {ℓ} (A : Bool → Bool → Type ℓ)
--   (a : A true true) (b : (i : Bool) (j₁ : Bool) → A i j₁) (q : b true true ≡ a)
--   → Path (joinR-gen Bool λ j → joinR-gen Bool λ i → A i j)
--           (inrR (CasesBool true (inrR (CasesBool true a (b false true))) (inlR (false , b false false))))
--           (inrR (λ j₁ → inrR (λ i → b i j₁)))
-- ΠR-extend→ₘb-inrBool A a b q = cong inrR
--   (funExt (CasesBool {A = λ x → CasesBool {A = λ x → joinR-gen Bool λ i → A i x} true
--                      (inrR (CasesBool true a (b false true))) (inlR (false , b false false)) x
--                    ≡ inrR (λ i → b i x)} true
--     (cong inrR (funExt (CasesBool true (sym q) refl)))
--     (push* (false , b false false) (λ i → b i false) refl)))

-- abstract
--   ΠR-extend→ₘb-inr : ∀ {ℓ} (J : RP∞' ℓ) (j : fst J) (A : Bool → fst J → Type ℓ)
--     (a : A true j) (b : (i : Bool) (j₁ : fst J) → A i j₁) (q : b true j ≡ a)
--     → Path (joinR-gen (fst J) λ j → joinR-gen Bool λ i → A i j)
--             (inrR (RP'.elimI J j (inrR (CasesBool true a (b false j))) (inlR (false , b false (RP'.notI J j)))))
--             (inrR (λ j₁ → inrR (λ i → b i j₁)))
--   ΠR-extend→ₘb-inr = JRP∞' ΠR-extend→ₘb-inrBool

--   ΠR-extend→ₘb∙ : ∀ {ℓ} (A : Bool → Bool → Type ℓ)
--     (a : A true true) (b : (i : Bool) (j₁ : Bool) → A i j₁) (q : b true true ≡ a)
--     → ΠR-extend→ₘb-inr (RP∞'· ℓ) true A a b q
--      ≡ ΠR-extend→ₘb-inrBool A a b q
--   ΠR-extend→ₘb∙ {ℓ = ℓ} A a b q j = main j A a b q
--     where
--     main : ΠR-extend→ₘb-inr (RP∞'· ℓ) true ≡ ΠR-extend→ₘb-inrBool
--     main = JRP∞'∙ ΠR-extend→ₘb-inrBool



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
