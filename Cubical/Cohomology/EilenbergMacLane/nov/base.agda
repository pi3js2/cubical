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
open import Cubical.Data.Bool hiding (_≤_ ; Bool*)

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


module Cubical.Cohomology.EilenbergMacLane.nov.base where
open import Cubical.HITs.Join
open import Cubical.Functions.FunExtEquiv

sqr : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z)
  → Square p q p q
sqr p q i j =
  hcomp (λ k → λ {(i = i0) → p (j ∨ ~ k)
                 ; (i = i1) → q j
                 ; (j = i0) → p (i ∨ ~ k)
                 ; (j = i1) → q i})
        (q (i ∧ j))

evalG : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → B ⊎ (A ≃ B) → A → B
evalG (inl x) _ = x
evalG (inr x) = fst x

elimPushout : ∀ {ℓ ℓ' ℓ'' ℓ'''} {A : Type ℓ}
  {B : Type ℓ'} {C : Type ℓ''} {f : A → B} {g : A → C}
  {D : Pushout f g → Type ℓ'''}
  → (left : (b : B) → D (inl b))
  → (right : (c : C) → D (inr c))
  → (coh : (a : A) → PathP (λ i → D (push a i)) (left (f a)) (right (g a)))
  → (x : _) → D x
elimPushout l r c (inl x) = l x
elimPushout l r c (inr x) = r x
elimPushout l r c (push a i) = c a i

uncurryΠ : ∀ {ℓ ℓ' ℓ'' ℓ'''}
  {A : Type ℓ} {B : A → Type ℓ'}
  {C : (a : A) (b : B a) → Type ℓ''}
  {D : ((a : A) → Σ (B a) (C a)) → Type ℓ'''}
  → ((f : (a : A) → B a) (g : (a : A) → C a (f a)) → D λ a → f a , g a)
  → (x : _) → D x
uncurryΠ ind x = ind (λ a → x a .fst) λ a → x a .snd

J>Sq : ∀ {ℓ ℓ'} {A : Type ℓ} {x y : A} {p : x ≡ y} 
  {A : (q : x ≡ y) → Square refl refl p q → Type ℓ'}
  → A p (λ i _ → p i)
  → (x : _) (p : _) → A x p
J>Sq {x = x}  {y}{p = p} {A} bas q sq = t q (flipSquare sq)
  where
  t : (q : x ≡ y) (r : p ≡ q) → A q (flipSquare r)
  t = J> bas


→×Iso : ∀ {ℓ ℓ'} {A : Type ℓ} {B C : A → Type ℓ'}
  → Iso ((a : A) → B a × C a) (((a : A) → B a) × ((a : A) → C a))
Iso.fun →×Iso f = fst ∘ f , snd ∘ f
Iso.inv →×Iso (f , g) a = f a , g a
Iso.rightInv →×Iso _ = refl
Iso.leftInv →×Iso _ = refl

ΠBool→× : ∀ {ℓ} {A : Bool → Type ℓ} → ((x : _) → A x) → A true × A false
ΠBool→× f = f true , f false

×→Bool : ∀ {ℓ} {A : Bool → Type ℓ} → A true × A false → ((x : _) → A x)
×→Bool (a , b) = CasesBool true a b

ΠBool×Iso : ∀ {ℓ} {A : Bool → Type ℓ} → Iso ((x : _) → A x) (A true × A false)
Iso.fun ΠBool×Iso = ΠBool→×
Iso.inv ΠBool×Iso = ×→Bool
Iso.rightInv ΠBool×Iso a = refl
Iso.leftInv ΠBool×Iso a i false = a false
Iso.leftInv ΠBool×Iso a i true = a true

CasesBoolη : ∀ {ℓ} {A : Bool → Type ℓ} (f : (x : Bool) → A x)
  → CasesBool {A = A} true (f true) (f false) ≡ f
CasesBoolη f i false = f false
CasesBoolη f i true = f true

CasesBoolη-coh :  ∀ {ℓ} {A : Bool → Type ℓ} → (a : A true) (b : A false)
  → CasesBoolη {A = A} (CasesBool true a b) ≡ refl
CasesBoolη-coh a b i j false = b
CasesBoolη-coh a b i j true = a

BoolFun-elim : ∀ {ℓ ℓ'} {A : Bool → Type ℓ} (C : ((x : Bool) → A x) → Type ℓ')
  → ((a : A true) (b : A false) → C (CasesBool true a b))
  → (f : _) → C f
BoolFun-elim C ind f = subst C (CasesBoolη f) (ind (f true) (f false))

BoolFun-elimη : ∀ {ℓ ℓ'} {A : Bool → Type ℓ} (C : ((x : Bool) → A x) → Type ℓ')
  → (g : (a : A true) (b : A false) → C (CasesBool true a b))
  → (a : A true) (b : A false)
  → BoolFun-elim C g (CasesBool true a b) ≡ g a b
BoolFun-elimη {A = A} C g a b i = transp (λ j → C (help i j)) i (g a b)
  where
  help : CasesBoolη {A = A} (CasesBool true a b) ≡ refl
  help i j false = b
  help i j true = a

funTypePP : ∀ {ℓ ℓ'} {A : Type ℓ} {B : I → A → Type ℓ'}
  {f : (a : A) → B i0 a} {g : (a : A) → B i1 a}
  → ((a : A) → PathP (λ i → B i a) (f a) (g a))
  → PathP (λ i → (a : A) → B i a) f g
funTypePP p i a = p a i

funTypeSq : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
  → {f g h l : (x : A) → B x}
  → {p : f ≡ g} {q : h ≡ l}
  → {le : f ≡ h} {r : g ≡ l}
  → ((x : A) → Square {A = B x}
                 (funExt⁻ p x) (funExt⁻ q x)
                 (funExt⁻ le x) (funExt⁻ r x))
  → Square {A = (x : A) → B x} p q le r
funTypeSq sq i j x = sq x i j

Boolhigherη : ∀ {ℓ} {A : Bool → Type ℓ} (f g : (x : Bool) → A x) (p : (x : Bool) → f x ≡ g x)
  → PathP (λ i → (x : Bool) → CasesBoolη f i x ≡ CasesBoolη g i x)
               (CasesBool true (p true) (p false)) p
Boolhigherη f g p i false = p false
Boolhigherη f g p i true = p true

module _ {ℓ ℓ' : Level} {A : Type ℓ} {x : A} {P : ∀ y → y ≡ x → Type ℓ'} (d : P x refl) where

  infix 10 J>'_
  
  J>'_ : ∀ y → (p : y ≡ x) → P y p
  J>'_ _ p = transport (λ i → P (p (~ i)) λ j → p (~ i ∨ j)) d

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

is2Type : (ℓ' : Level) (X : Type) → Type (ℓ-suc ℓ')
is2Type ℓ' X =
  Σ[ nope ∈ (X → X) ]
    (¬ ((x : X) → nope x ≡ x)) × (((B : X → Type ℓ')
      → Σ[ elim ∈ ((x : X) (a : B x) (a' : B (nope x)) → (x : _) → B x) ]
         ((x : X) (a : B x) (a' : B (nope x)) → (elim x a a' x ≡ a) × (elim x a a' (nope x) ≡ a'))))

isRP∞ : (ℓ : Level) → (X : Type) → Type (ℓ-suc ℓ)
isRP∞ ℓ X = is2Type ℓ X × ∥ X ∥₁

isRP∞→≃Bool : (ℓ : Level) (X : Type) → is2Type ℓ X → X → X ≃ Bool
isRP∞→≃Bool ℓ X f x = compEquiv (isoToEquiv (theIs f x)) (invEquiv LiftEquiv)
  where
  module _ (f : is2Type ℓ X) (x : X) where
    help : X → Lift Bool
    help = fst (f .snd .snd (λ _ → Lift Bool)) x (lift true)
      (lift false)

    LiftB→X : Lift Bool → X
    LiftB→X (lift false) = fst f x
    LiftB→X (lift true) = x

    theIs : Iso X (Lift Bool)
    Iso.fun theIs = help
    Iso.inv theIs = LiftB→X
    Iso.rightInv theIs (lift false) =
      f .snd .snd (λ _ → Lift Bool) .snd x (lift true) (lift false) .snd
    Iso.rightInv theIs (lift true) =
      f .snd .snd (λ _ → Lift Bool) .snd x (lift true) (lift false) .fst
    Iso.leftInv theIs x' = cong (invEq (LiftEquiv {ℓ' = ℓ})) (liftEq x')
      where
      liftEq : (x' : X) → lift (LiftB→X (help x')) ≡ lift x'
      liftEq =  f .snd .snd _ .fst x
        (cong lift (cong LiftB→X
          (f .snd .snd (λ _ → Lift Bool) .snd x (lift true) (lift false) .fst)))
        (cong lift (cong LiftB→X (f .snd .snd (λ _ → Lift Bool) .snd
          x (lift true) (lift false) .snd)))

not*-notConst : (X : RP∞) → ¬ ((x : fst X) → not* X x ≡ x)
not*-notConst = uncurry λ X → PT.elim (λ _ → isProp¬ _)
  (EquivJ (λ X x → ¬ ((x₁ : X) → not* (X , ∣ x ∣₁) x₁ ≡ x₁))
    λ p → true≢false (p false))


Bool-2Type : (ℓ : Level) → is2Type ℓ Bool
fst (Bool-2Type ℓ) = not
fst (snd (Bool-2Type ℓ)) = not*-notConst Bool*
fst (snd (snd (Bool-2Type ℓ)) B) = CasesBool
snd (snd (snd (Bool-2Type ℓ)) B) = CasesBoolβ


≃Bool→isRP∞ : (ℓ : Level) (X : Type) → X ≃ Bool → is2Type ℓ X × X
fst (≃Bool→isRP∞ ℓ X eq) = help eq
  where
  help : X ≃ Bool → is2Type ℓ X
  help = EquivJ (λ X _ → is2Type ℓ X) (Bool-2Type _)
snd (≃Bool→isRP∞ ℓ X eq) = invEq eq true


RP∞-2Type : (ℓ : Level) (X : RP∞) → is2Type ℓ (fst X)
fst (RP∞-2Type ℓ X) = not* X
fst (snd (RP∞-2Type ℓ X)) = not*-notConst X
fst (snd (snd (RP∞-2Type ℓ X)) B) = CasesRP X
snd (snd (snd (RP∞-2Type ℓ X)) B) = CasesRPβ X {B}


isPr-is2TypeBool : ∀ {ℓ} → isContr (is2Type ℓ Bool)
fst isPr-is2TypeBool = Bool-2Type _
snd (isPr-is2TypeBool {ℓ}) (f , (n , p)) =
  ΣPathP ((sym f≡not) , isProp→PathP (λ j → isProp× (isProp¬ _)
    (isPropΠ λ B → transport (λ k → isProp
      (Σ-syntax
       ((x : Bool) → B x → B (f≡not (~ j ∨ ~ k) x) → (x₁ : Bool) → B x₁)
       (λ elim₁ →
          (x : Bool) (a : B x) (a' : B (f≡not (~ j ∨ ~ k) x)) →
          (elim₁ x a a' x ≡ a) × (elim₁ x a a' (f≡not (~ j ∨ ~ k) x) ≡ a'))))
            (isPr B))) _ _)
  where
  isPr : (B : Bool → Type ℓ) → isProp _
  isPr B (f , p) (g , q) =
    ΣPathP ((λ i x a b y → help1 x a b y i)
          , λ i x a a' → pp x a a' i)
    where
    help1 : (x : Bool) (a : _) (b : _) (y : Bool) → f x a b y ≡ g x a b y
    help1 false a b false = p false a b .fst  ∙∙ refl ∙∙ sym (q false a b .fst)
    help1 false a b true = p false a b .snd ∙∙ refl ∙∙ sym (q false a b .snd)
    help1 true a b false = p true a b .snd ∙∙ refl ∙∙ sym (q true a b .snd)
    help1 true a b true = p true a b .fst ∙∙ refl ∙∙ sym (q true a b .fst)

    pp : (x : Bool) (a : B x) (a' : B (not x))
      → PathP (λ i → Σ (help1 x a a' x i ≡ a) (λ _ → help1 x a a' (not x) i ≡ a')) (p x a a') (q x a a')
    fst (pp false a a' i) j = doubleCompPath-filler (fst (p false a a')) refl (sym (fst (q false a a'))) (~ j) i
    snd (pp false a a' i) j = doubleCompPath-filler (snd (p false a a')) refl (sym (snd (q false a a'))) (~ j) i
    fst (pp true a a' i) j = doubleCompPath-filler (fst (p true a a')) refl (sym (fst (q true a a'))) (~ j) i
    snd (pp true a a' i) j = doubleCompPath-filler (snd (p true a a')) refl (sym (snd (q true a a'))) (~ j) i
  notConst : f false ≡ f true → ⊥
  notConst r = true≢false (isContr→isProp isContrBool _ _)
    where
    Lift→ : ∀ {ℓ'} {A : Type} → Lift {ℓ-zero} {ℓ'} A → A
    Lift→ (lift lower₁) = lower₁

    hel-l : f false ≡ true → (x : Bool) → lift x ≡ lift (f false)
    hel-l ha = p _ .fst true (cong lift (sym ha)) (cong lift (sym r))

    hel : f false ≡ true → (x : Bool) → x ≡ f false
    hel ha x = cong (Lift→ {ℓ}) (hel-l ha x)

    hel2 : f false ≡ false → (x : Bool) → x ≡ f false 
    hel2 ha x = cong (Lift→ {ℓ}) (p (λ x → lift x ≡ lift (f false)) .fst false (cong lift (sym ha)) refl x)

    ing : (x : _) → f false ≡ x → (z : Bool) → z ≡ f false
    ing false = hel2
    ing true = hel

    isContrBool : isContr Bool
    isContrBool = (f false) , sym ∘ ing (f false) refl

  help* : (y y' : Bool) → f true ≡ y → f false ≡ y' → (x : _) → f x ≡ not x
  help* false false p q = ⊥.rec (notConst (q ∙ sym p))
  help* false true p q = λ { false → q ; true → p}
  help* true false p q = ⊥.rec (n λ { false → q ; true → p})
  help* true true p q = ⊥.rec (notConst (q ∙ sym p))

  f≡not : f ≡ not
  f≡not = funExt (help* (f true) (f false) refl refl)

isPropis2Type : ∀ {ℓ} (X : RP∞) → isProp (is2Type ℓ (fst X))
isPropis2Type = RP∞pt→Prop (λ _ → isPropIsProp) (isContr→isProp isPr-is2TypeBool)


RP∞' : (ℓ : Level) → Type _
RP∞' ℓ = Σ[ X ∈ Type ] isRP∞ ℓ X

isPropIsRP∞' : ∀ (ℓ) (X : Type) → ∥ X ∥₁ → isProp (is2Type ℓ X)
isPropIsRP∞' ℓ X = PT.rec isPropIsProp λ y totY totY'
  → isPropis2Type (X , ∣ isRP∞→≃Bool ℓ X totY y ∣₁) _ _

isPropIsRP∞ : ∀ (ℓ) (X : Type) → isProp (isRP∞ ℓ X)
isPropIsRP∞ ℓ X (totY , y) (totY' , y') =
  isPropΣ (isPropis2Type (X , PT.map (isRP∞→≃Bool ℓ X totY) y')) (λ _ → squash₁) _ _

RP∞'≃RP∞ : (ℓ : Level) → RP∞' ℓ ≃ RP∞
RP∞'≃RP∞ ℓ =
  isoToEquiv
    (iso
     (λ X → fst X , PT.map (isRP∞→≃Bool ℓ (fst X) (snd X .fst)) (snd X .snd))
     (λ X → (fst X) , (PT.rec (isPropΣ (isPropis2Type X) (λ _ → squash₁))
       ((λ x → fst x , ∣ x .snd ∣₁)
       ∘ (≃Bool→isRP∞ ℓ (fst X))) (snd X)))
     (λ X → Σ≡Prop (λ _ → squash₁) refl)
     λ X → Σ≡Prop (isPropIsRP∞ ℓ) refl)


2Type≡ : ∀ {ℓ} → RP∞-2Type ℓ Bool* ≡ Bool-2Type ℓ
2Type≡ = isPropis2Type Bool* _ _

joinR-gen : ∀ {ℓ ℓ'} (I : Type ℓ) (A : I → Type ℓ') → Type _
joinR-gen I A = PushoutR (Σ I A) ((i : I) → A i)  λ x f → f (fst x) ≡ snd x

joinR : ∀ {ℓ} (I : RP∞) (A : fst I → Type ℓ) → Type _
joinR I A = PushoutR (Σ (fst I) A) ((i : fst I) → A i)  λ x f → f (fst x) ≡ snd x

joinRD : ∀ {ℓ} (I J : RP∞) (A : fst I → fst J → Type ℓ) → Type _
joinRD I J A = joinR I λ i → joinR J (A i)

RP∞'· : (ℓ : Level) → RP∞' ℓ
RP∞'· ℓ = Bool , ((Bool-2Type ℓ) , ∣ true ∣₁)

isContrSigl∞ : (ℓ : Level) → isContr (Σ[ I ∈ RP∞' ℓ ] fst I)
fst (isContrSigl∞ ℓ) = RP∞'· ℓ , true
snd (isContrSigl∞ ℓ) (I , i) = ΣPathP ((pst' I i)
  , (toPathP λ j → transp (λ _ → fst I) j i))
  where
  pst' : (I : RP∞' ℓ) (i : fst I) → RP∞'· ℓ ≡ I
  pst' I i = Σ≡Prop (λ _ → isPropIsRP∞ _ _)
                (ua (invEquiv (isRP∞→≃Bool ℓ (fst I) (snd I .fst) i)))

module _ {ℓ ℓ' : Level} {B : (I : RP∞' ℓ) → fst I → Type ℓ'} (c : B (RP∞'· _) true) where
  private
    B* : Σ[ I ∈ RP∞' ℓ ] fst I → Type ℓ'
    B* (I , i) = B I i

    JRP∞'-c : (x : _) → B* x
    JRP∞'-c p = subst B* (isContrSigl∞ ℓ .snd p) c

  JRP∞' : (I : RP∞' ℓ) (i : fst I) → B I i 
  JRP∞' I i = JRP∞'-c (I , i)

  JRP∞'∙ : JRP∞' (RP∞'· _) true ≡ c
  JRP∞'∙ = (λ i → subst B* (isProp→isSet (isContr→isProp (isContrSigl∞ ℓ)) _ _
    (isContrSigl∞ ℓ .snd (RP∞'· _ , true)) refl i) c) ∙ transportRefl c

PathRP∞' : {ℓ : Level} (I J : RP∞' ℓ) → Iso (I ≡ J) (fst I ≃ fst J)
PathRP∞' {ℓ} I J = 
  (iso (λ p → pathToEquiv (cong fst p ))
       (λ p → Σ≡Prop (isPropIsRP∞ ℓ) (ua p))
       (λ p → Σ≡Prop (λ _ → isPropIsEquiv _) (funExt λ a → transportRefl (fst p a)))
       λ p → ΣSquareSet (λ _ → isProp→isSet (isPropIsRP∞ ℓ _))
               (retEq univalence (cong fst p)))

module _ {ℓ ℓ' : Level} (I : RP∞' ℓ) {B : (J : RP∞' ℓ) → fst I ≃ fst J → Type ℓ'} (c : B I (idEquiv _)) where
  private
    isContrTot : isContr (Σ[ J ∈ RP∞' ℓ ] fst I ≃ fst J)
    isContrTot = isOfHLevelRetractFromIso 0 (Σ-cong-iso-snd (λ J → invIso (PathRP∞' I J))) (isContrSingl I)
    B* : Σ[ J ∈ RP∞' ℓ ] fst I ≃ fst J → Type _
    B* (J , e) = B J e

  JRP∞'' : (J : RP∞' ℓ) (i : fst I ≃ fst J) → B J i
  JRP∞'' J i = subst B* (isContr→isProp isContrTot (I , idEquiv (fst I)) (J , i)) c

  JRP∞''-refl : JRP∞'' I (idEquiv (fst I)) ≡ c
  JRP∞''-refl = (λ i → subst B* (isProp→isSet (isContr→isProp isContrTot) _ _ (isContr→isProp isContrTot (I , idEquiv (fst I)) (I , idEquiv (fst I))) refl i) c)
              ∙ transportRefl c


RP∞'pt→Prop : ∀ {ℓ ℓ'} {B : (I : RP∞' ℓ) → Type ℓ'}
  → ((x : _) → isProp (B x))
  → B (RP∞'· ℓ)
  → (x : _) → B x
RP∞'pt→Prop {ℓ} {B = B} pr c = uncurry λ X
  → uncurry λ 2t
  → PT.elim (λ _ → pr _)
      λ x → subst B (Σ≡Prop (λ _ → isPropIsRP∞ _ _)
        (sym (ua (isRP∞→≃Bool ℓ X 2t x)))) c

RP∞'pt→Propβ : ∀ {ℓ ℓ'} {B : (I : RP∞' ℓ) → Type ℓ'}
  (pr : (x : _) → isProp (B x)) (e : B (RP∞'· ℓ))
  → RP∞'pt→Prop pr e (RP∞'· ℓ) ≡ e
RP∞'pt→Propβ {ℓ} {B = B} pr e =
     (λ j → subst B (help j) e)
   ∙ transportRefl e
  where
  help : Path (RP∞'· ℓ ≡ RP∞'· ℓ)
    (Σ≡Prop (λ _ → isPropIsRP∞ _ _)
      (sym (ua (isRP∞→≃Bool ℓ Bool (Bool-2Type ℓ) true))))
    refl
  help = ΣSquareSet (λ _ → isProp→isSet (isPropIsRP∞ _ _))
          ((λ j → sym (ua (h2 j)))
         ∙ λ j → sym (uaIdEquiv j))
    where
    h2 : isRP∞→≃Bool ℓ Bool (Bool-2Type ℓ) true ≡ idEquiv _ 
    h2 = Σ≡Prop (λ _ → isPropIsEquiv _)
           (funExt (CasesBool true refl refl))

2-eltFun : ∀ {ℓ} {I J : RP∞' ℓ}
  → (fst J ⊎ (fst I ≃ fst J)) ≃ (fst I → fst J)
2-eltFun {ℓ} {I} {J} = evalG , RP∞'pt→Prop {B = λ I → isEquiv {A = fst J ⊎ (fst I ≃ fst J)} evalG} (λ _ → isPropIsEquiv _) (isoToIsEquiv (invIso isEquivG)) I
  where
  back : (J : RP∞' ℓ) → fst J × fst J → Lift (fst J ⊎ (Bool ≃ fst J))
  back J = uncurry λ j → snd J .fst .snd .snd (λ _ → Lift (fst J ⊎ (Bool ≃ fst J))) .fst j
    (lift (inl j))
    (lift (inr (invEquiv (isRP∞→≃Bool _ (fst J) (snd J .fst) j))))

  T : (J : RP∞' ℓ) → (j : fst J) → _
  T J j = snd J .fst .snd .snd (λ _ → Lift (fst J ⊎ (Bool ≃ fst J))) .snd j (lift (inl j))
    (lift (inr (invEquiv (isRP∞→≃Bool _ (fst J) (snd J .fst) j))))

  inr* : _ → Bool ⊎ (Bool ≃ Bool)
  inr* = inr

  FF : (J : RP∞' ℓ) → Lift (fst J ⊎ (Bool ≃ fst J)) → _
  FF J = invEq LiftEquiv

  Iso1 : Iso (fst J × fst J) (fst J ⊎ (Bool ≃ fst J))
  Iso.fun Iso1 = FF J ∘ (back J)
  Iso.inv Iso1 f = Iso.fun ΠBool×Iso (evalG f)
  Iso.rightInv Iso1 (inl j) =
    cong (invEq (LiftEquiv {ℓ' = ℓ})) (T J j .fst)
  Iso.rightInv Iso1 (inr eq) =
    JRP∞'' (RP∞'· ℓ) {B = λ J eq → invEq LiftEquiv (back J (ΠBool→× (fst eq))) ≡ inr eq}
      (cong inr* (Σ≡Prop (λ _ → isPropIsEquiv _)
        (funExt (CasesBool true refl refl)))) J eq
  Iso.leftInv Iso1 =
    uncurry (JRP∞' {B = λ J x → (y : fst J)
                → ΠBool→× (evalG (FF J (back J (x , y)))) ≡ (x , y)}
      (CasesBool true refl refl) J)

  isEquivG : Iso (Bool → fst J) (fst J ⊎ (Bool ≃ fst J))
  Iso.fun isEquivG = invEq LiftEquiv ∘ back J ∘ Iso.fun ΠBool×Iso
  Iso.inv isEquivG = evalG
  Iso.rightInv isEquivG x = Iso.rightInv Iso1 x
  Iso.leftInv isEquivG x =
    (sym (Iso.leftInv ΠBool×Iso (evalG (FF J (back J (x true , x false)))))
    ∙ cong (Iso.inv ΠBool×Iso) (Iso.leftInv Iso1 (x true , x false)))
    ∙ funExt (CasesBool true refl refl)


EquivContr' : ∀ {ℓ} (A : Type ℓ) → ∃![ T ∈ Type ℓ ] (A ≃ T)
EquivContr' {ℓ = ℓ} A =
  ( (A , idEquiv A)
  , idEquiv≡ )
 where
  idEquiv≡ : (y : Σ (Type ℓ) (_≃_ A)) → (A , idEquiv A) ≡ y
  idEquiv≡ y = ΣPathP ((ua (snd y)) , (ΣPathPProp (λ _ → isPropIsEquiv _)
    (toPathP (funExt λ a → λ i → transportRefl (fst (snd y) (transportRefl a i)) i ))))

contrSinglEquiv' : ∀ {ℓ} {A B : Type ℓ} (e : A ≃ B) → (A , idEquiv A) ≡ (B , e)
contrSinglEquiv' {A = A} {B = B} e =
  isContr→isProp (EquivContr' A) (A , idEquiv A) (B , e)

EquivJrev : {ℓ ℓ' : Level} {A B : Type ℓ}
      (P : (B : Type ℓ) → A ≃ B → Type ℓ') →
      P A (idEquiv A) → (e : A ≃ B) → P B e
EquivJrev P r e = subst (λ x → P (x .fst) (x .snd)) (contrSinglEquiv' e) r

EquivJrevβ : {ℓ ℓ' : Level} {A B : Type ℓ}
      (P : (B : Type ℓ) → A ≃ B → Type ℓ') →
      (e : P A (idEquiv A)) → EquivJrev P e (idEquiv A) ≡ e 
EquivJrevβ {A = A} P e =
  (λ i → subst (λ x → P (x .fst) (x .snd)) (isProp→isSet (isContr→isProp (EquivContr' A)) _ _
     (contrSinglEquiv' (idEquiv A)) refl i ) e)
    ∙ transportRefl e

2-eltFun-elim' : ∀ {ℓ ℓ'} {A B : Type ℓ} {C : B → Type ℓ'} (e : A ≃ B)
  → (ind : (a : A) → C (fst e a))
  → (x : _) → subst C (secEq e _) (ind (invEq e (fst e x))) ≡ ind x
2-eltFun-elim' {A = A} {B = B} {C = C} =
  EquivJ (λ A e → (ind : (a : A) → C (fst e a))
    → (x : _) → subst C (secEq e _) (ind (invEq e (fst e x))) ≡ ind x)
    λ ind x → transportRefl (ind x)


module _ {ℓ : Level} {I J : RP∞' ℓ} {A : (fst I → fst J) → Type ℓ}
  (ind : (x : _) → A (fst (2-eltFun {I = I} {J}) x)) where
  2-eltFun-elim : (x : _) → A x
  2-eltFun-elim f = subst A (secEq (2-eltFun {ℓ} {I} {J}) f) (ind (invEq (2-eltFun {I = I} {J}) f))

  2-eltFun-elim-coh : (x : _) → 2-eltFun-elim  (fst (2-eltFun {I = I} {J}) x) ≡ ind x
  2-eltFun-elim-coh = 2-eltFun-elim' {C = A} (2-eltFun {I = I} {J}) ind

module _ {ℓ : Level} (I J : RP∞' ℓ) {A : fst I → fst J → Type ℓ} where
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
  

module _ {ℓ : Level} (I J : RP∞' ℓ) {A : fst I → fst J → Type ℓ} where
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


module 2-elter {ℓ : Level} (I : RP∞' ℓ) (J : Type) (A : fst I → J → Type ℓ) where
  I2 = I .snd
  notI : fst I → fst I
  notI = I2 .fst .fst

  elimI : {B : fst I → Type ℓ} → _
  elimI {B} = I2 .fst .snd .snd B .fst

  elimIβ : {B : fst I → Type ℓ} → _
  elimIβ {B} = I2 .fst .snd .snd B .snd

  fat : Type _
  fat = (Σ[ f ∈ ((i : fst I) → Σ[ j ∈ J ] A i j) ]
          Σ[ g ∈ ((i : fst I) (j : J) → A i j) ]
            ((i : fst I) → g i (f i .fst) ≡ f i .snd))
  
  ΠR-base : Type _
  ΠR-base =
    Pushout {A = fat}
            {B = TotΠ λ i → Σ[ j ∈ J ] (A i j)}
            {C = (i : fst I) (j : J) → A i j}
            fst
            (fst ∘ snd)

  left-push : Type _
  left-push = Σ[ i ∈ fst I ] (Σ[ j ∈ J ] (A i j)) × ((j : J) → A (notI i) j)

  left-push↑ₗ : fst I → Type _
  left-push↑ₗ i = Σ[ f ∈ ((i : fst I) → Σ[ j ∈ J ] A i j) ]
    Σ[ g ∈ ((j : J) → A (notI i) j) ] (g (f (notI i) .fst) ≡ f (notI i) .snd)

  left-push↑ᵣ : fst I → Type _
  left-push↑ᵣ i = Σ[ f ∈ (Σ[ j ∈ J ] A i j) ]
      Σ[ g ∈ ((i : fst I) (j : J) → A i j) ] g i (fst f) ≡ snd f

  fat→ₗ : (i : fst I) → fat → left-push↑ₗ i
  fat→ₗ  i (f , g , r) = (f , (g (notI i)) , (r (notI i)))

  fat→ᵣ : (i : fst I) → fat → left-push↑ᵣ i
  fat→ᵣ i (f , g , r) =  f i , g , r i

  PushTop : Type _
  PushTop = Σ[ i ∈ fst I ] (Pushout (fat→ₗ i) (fat→ᵣ i))

  PushTop→left-push' : (i : fst I)
    → (Pushout (fat→ₗ i) (fat→ᵣ i))
    → (Σ[ j ∈ J ] (A i j)) × ((j : J) → A (notI i) j)
  PushTop→left-push' i (inl (f , g , p)) = (f i) , g
  PushTop→left-push' i (inr (f , g , p)) = f , (g (notI i))
  PushTop→left-push' i (push (f , g , p) k) = (f i) , λ j → g (notI i) j

  PushTop→left-push : PushTop → left-push
  PushTop→left-push (i , x) = (i , PushTop→left-push' i x)

  PushTop→ΠR-base : PushTop → ΠR-base
  PushTop→ΠR-base (i , inl (f , g , p)) = inl f
  PushTop→ΠR-base (i , inr (f , g , p)) = inr g
  PushTop→ΠR-base (i , push (f , g , p)  i₁) = push (f , g , p) i₁

  ΠR-extend : Type _
  ΠR-extend = Pushout PushTop→left-push PushTop→ΠR-base


  ΠR-extend→Πₗ : left-push → TotΠ (λ i → joinR-gen J (A i))
  ΠR-extend→Πₗ (i , p , r) = elimI i (inlR p) (inrR r)

  ΠR-base→ : ΠR-base → TotΠ (λ i → joinR-gen J (A i))
  ΠR-base→ (inl x) i = inlR (x i)
  ΠR-base→ (inr x) i = inrR λ j → x i j
  ΠR-base→ (push a i') i = push* (fst a i) (fst (snd a) i) (snd (snd a) i) i'

  pre-eqvl-diag : (i' : fst I) (p : Pushout (fat→ₗ i') (fat→ᵣ i'))
    → ΠR-extend→Πₗ (PushTop→left-push (i' , p)) i'
     ≡ ΠR-base→ (PushTop→ΠR-base (i' , p)) i'
  pre-eqvl-diag i' (inl (f , f2 , p)) =
    elimIβ {B = λ i → joinR-gen J (A i)} i' (inlR (f i' .fst , f i' .snd)) (inrR f2) .fst
  pre-eqvl-diag i' (inr (f , f2 , p)) =
    elimIβ {B = λ i → joinR-gen J (A i)} i' (inlR f) (inrR (f2 (notI i'))) .fst ∙ push* f (f2 i') p 
  pre-eqvl-diag i' (push (f , f2 , p) i) j =
    compPath-filler (elimIβ {B = λ i → joinR-gen J (A i)} i' (inlR (f i')) (inrR (f2 (notI i'))) .fst)
                    (push* (f i') (f2 i') (p i')) i j

  pre-eqvl-not : (i' : fst I) (p : Pushout (fat→ₗ i') (fat→ᵣ i'))
    → ΠR-extend→Πₗ (PushTop→left-push (i' , p)) (notI i') ≡
      ΠR-base→ (PushTop→ΠR-base (i' , p)) (notI i')
  pre-eqvl-not i' (inl (f , f2 , p)) =
      elimIβ {B = λ i → joinR-gen J (A i)} i' (inlR (f i')) (inrR f2) .snd
    ∙ sym (push* (f (notI i')) f2 p)
  pre-eqvl-not i' (inr (f , f2 , p)) =
    elimIβ {B = λ i → joinR-gen J (A i)} i' (inlR f) (inrR (f2 (notI i'))) .snd
  pre-eqvl-not i' (push (f , f2 , p) i) j =
      compPath-filler
        (elimIβ {B = λ i → joinR-gen J (A i)} i' (inlR (f i')) (inrR (f2 (notI i'))) .snd)
        (sym (push* (f (notI i')) (f2 (notI i')) (p (notI i')))) (~ i) j


  eqvl : (a : PushTop) (i : fst I)
    → ΠR-extend→Πₗ (PushTop→left-push a) i
     ≡ ΠR-base→ (PushTop→ΠR-base a) i
  eqvl (i' , p) =
    elimI i' (pre-eqvl-diag i' p)
                 (pre-eqvl-not i' p)

  ΠR-extend→Π : ΠR-extend → TotΠ (λ i → joinR-gen J (A i))
  ΠR-extend→Π (inl t) = ΠR-extend→Πₗ t
  ΠR-extend→Π (inr x) = ΠR-base→ x
  ΠR-extend→Π (push a i) i' = eqvl a i' i

  dable : Type _
  dable = Pushout {A = fst I × ΠR-extend} {B = Σ[ i ∈ fst I ] joinR-gen J (A i)} {C = ΠR-extend}
                  (λ a → fst a , ΠR-extend→Π (snd a) (fst a))
                  snd
                  

  private
    inl123 : (a : _) → dable
    inl123 = inl
  module _ (ise : isEquiv ΠR-extend→Π) where
    
    updater→ : dable → (joinR-gen (fst I) (λ i → joinR-gen J (A i)))
    updater→ (inl x) = inlR x
    updater→ (inr x) = inrR (ΠR-extend→Π x)
    updater→ (push a i) = push* (fst a , ΠR-extend→Π (snd a) (fst a)) (ΠR-extend→Π (snd a)) refl i

    updater← : joinR-gen (fst I) (λ i → joinR-gen J (A i)) → dable
    updater← (inlR x) = inl x
    updater← (inrR x) = inr (invEq (_ , ise) x)
    updater← (push* a b x i) =
      (cong inl123 (ΣPathP (refl , sym x ∙ sym (funExt⁻ (secEq (_ , ise) b) (fst a))))
              ∙ push ((fst a) , invEq (_ , ise) b)) i


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

  
makeRP≃ₗ : (J : RP∞) (j : fst J) → Bool ≃ (fst J)
makeRP≃ₗ J j = isoToEquiv theIs
  where
  F : Bool → fst J
  F = CasesBool true j (not* J j)

  G : fst J → Bool
  G = CasesRP J j true false

  FGF : (x : Bool) → G (F x) ≡ x
  FGF = CasesBool true (CasesRPβ J j true false .fst)
                       (CasesRPβ J j true false .snd)

  GFG : (x : fst J) → F (G x) ≡ x
  GFG = CasesRP J j
    (cong F (CasesRPβ J j true false .fst))
    (cong F (CasesRPβ J j true false .snd))

  theIs : Iso _ _
  Iso.fun theIs = F
  Iso.inv theIs = G
  Iso.rightInv theIs = GFG
  Iso.leftInv theIs = FGF

makeRP≃ᵣ : (J : RP∞) (j : fst J) → Bool ≃ (fst J)
makeRP≃ᵣ J j = compEquiv notEquiv (makeRP≃ₗ J j)

ΠR-extend→Π-alt : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → (fst J) → Type ℓ)
  → 2-elter.ΠR-extend (RP∞'· ℓ) (fst J) A
  → TotΠ (λ i → joinR-gen (fst J) (A i))
ΠR-extend→Π-alt J A (inl (false , f , p)) false = inlR f
ΠR-extend→Π-alt J A (inl (false , f , p)) true = inrR p
ΠR-extend→Π-alt J A (inl (true , f , p)) false = inrR p
ΠR-extend→Π-alt J A (inl (true , f , p)) true = inlR f
ΠR-extend→Π-alt J A (inr (inl x)) a = inlR (x a)
ΠR-extend→Π-alt J A (inr (inr x)) b = inrR (x b)
ΠR-extend→Π-alt J A (inr (push a i)) c =
  push* (fst a c) (fst (snd a) c) (snd (snd a) c) i
ΠR-extend→Π-alt J A (push (false , inl x) i) false = inlR (fst x false)
ΠR-extend→Π-alt J A (push (false , inr x) i) false =
  push* (fst x) (fst (snd x) false) (snd (snd x)) i
ΠR-extend→Π-alt J A (push (false , push (f , p , q) i₁) i) false =
  push* (f false) (p false) (q false) (i ∧ i₁)
ΠR-extend→Π-alt J A (push (false , inl x) i) true =
  push* (fst x true) (fst (snd x)) (snd (snd x)) (~ i)
ΠR-extend→Π-alt J A (push (false , inr x) i) true = inrR (fst (snd x) true)
ΠR-extend→Π-alt J A (push (false , push (f , p , q) i₁) i) true =
  push* (f true) (p true) (q true) (~ i ∨ i₁)
ΠR-extend→Π-alt J A (push (true , inl x) i) false =
  push* (fst x false) (fst (snd x)) (snd (snd x)) (~ i)
ΠR-extend→Π-alt J A (push (true , inr x) i) false = inrR (fst (snd x) false)
ΠR-extend→Π-alt J A (push (true , push (f , p , q) i₁) i) false =
  push* (f false) (p false) (q false) (~ i ∨ i₁)
ΠR-extend→Π-alt J A (push (true , inl x) i) true = inlR (fst x true)
ΠR-extend→Π-alt J A (push (true , inr x) i) true = push* (fst x) (fst (snd x) true) (snd (snd x)) i
ΠR-extend→Π-alt J A (push (true , push (f , p , q) i₁) i) true = push* (f true) (p true) (q true) (i ∧ i₁)

ΠR-extend→Π-alt≡ : ∀ {ℓ} {J : RP∞' ℓ} (A : Bool → fst J → Type ℓ)
  → (x : _) (z : _) → ΠR-extend→Π-alt J A x z ≡ 2-elter.ΠR-extend→Π (RP∞'· ℓ) (fst J) A x z
ΠR-extend→Π-alt≡ A (inl (false , y)) false = refl
ΠR-extend→Π-alt≡ A (inl (false , y)) true = refl
ΠR-extend→Π-alt≡ A (inl (true , y)) false = refl
ΠR-extend→Π-alt≡ A (inl (true , y)) true = refl
ΠR-extend→Π-alt≡ A (inr (inl x)) z = refl
ΠR-extend→Π-alt≡ A (inr (inr x)) z = refl
ΠR-extend→Π-alt≡ A (inr (push a i)) false = refl
ΠR-extend→Π-alt≡ A (inr (push a i)) true = refl
ΠR-extend→Π-alt≡ A (push (false , inl x) i) false = refl
ΠR-extend→Π-alt≡ A (push (false , inr x) i) false j = lUnit (push* (fst x) (fst (snd x) false) (snd (snd x))) j i
ΠR-extend→Π-alt≡ A (push (false , push a i₁) i) false k =
  hcomp (λ r → λ {(i = i0) → inlR (fst a false)
                 ; (i = i1) → push* (fst a false) (fst (snd a) false) (snd (snd a) false) (i₁ ∧ (~ k ∨ r))
                 ; (i₁ = i0) → inlR (fst a false)
                 ; (i₁ = i1) → lUnit-filler (push* (fst a false) (fst (snd a) false) (snd (snd a) false)) r k i
                 ; (k = i0) → push* (fst a false) (fst (snd a) false) (snd (snd a) false) (i ∧ i₁)
                 ; (k = i1) → compPath-filler refl (push* (fst a false) (fst (snd a) false) (snd (snd a) false)) (r ∧ i₁) i})
        (push* (fst a false) (fst (snd a) false) (snd (snd a) false) (i ∧ (i₁ ∧ ~ k)))
ΠR-extend→Π-alt≡ A (push (true , inl x) i) false j = lUnit (sym (push* (fst x false) (fst (snd x)) (snd (snd x)))) j i
ΠR-extend→Π-alt≡ A (push (true , inr x) i) false = refl
ΠR-extend→Π-alt≡ A (push (true , push a i₁) i) false k =
  hcomp (λ r → λ {(i = i0) → inrR (fst (snd a) false)
                 ; (i = i1) → push* (fst a false) (fst (snd a) false) (snd (snd a) false) (i₁ ∨ (k ∧ ~ r))
                 ; (i₁ = i0) → lUnit-filler (sym (push* (fst a false) (fst (snd a) false) (snd (snd a) false))) r k i
                 ; (i₁ = i1) → inrR (fst (snd a) false)
                 ; (k = i0) → push* (fst a false) (fst (snd a) false) (snd (snd a) false) (~ i ∨ i₁)
                 ; (k = i1) → compPath-filler refl
                                (sym (push* (fst a false) (fst (snd a) false) (snd (snd a) false))) (r ∧ ~ i₁) i})
          (push* (fst a false) (fst (snd a) false) (snd (snd a) false) ((k ∨ i₁) ∨ ~ i))
ΠR-extend→Π-alt≡ A (push (false , inl x) i) true j = lUnit (sym (push* (fst x true) (fst (snd x)) (snd (snd x)))) j i
ΠR-extend→Π-alt≡ A (push (false , inr x) i) true = refl
ΠR-extend→Π-alt≡ A (push (false , push a i₁) i) true k =
  hcomp (λ r → λ {(i = i0) → inrR (fst (snd a) true)
                 ; (i = i1) → push* (fst a true) (fst (snd a) true) (snd (snd a) true) (i₁ ∨ (k ∧ ~ r))
                 ; (i₁ = i0) → lUnit-filler (sym (push* (fst a true) (fst (snd a) true) (snd (snd a) true))) r k i
                 ; (i₁ = i1) → inrR (fst (snd a) true)
                 ; (k = i0) → push* (fst a true) (fst (snd a) true) (snd (snd a) true) (~ i ∨ i₁)
                 ; (k = i1) → compPath-filler refl
                                (sym (push* (fst a true) (fst (snd a) true) (snd (snd a) true))) (r ∧ ~ i₁) i})
          (push* (fst a true) (fst (snd a) true) (snd (snd a) true) ((k ∨ i₁) ∨ ~ i))
ΠR-extend→Π-alt≡ A (push (true , inl x) i) true = refl
ΠR-extend→Π-alt≡ A (push (true , inr x) i) true j = lUnit (push* (fst x) (fst (snd x) true) (snd (snd x))) j i
ΠR-extend→Π-alt≡ A (push (true , push a i₁) i) true k =
  hcomp (λ r → λ {(i = i0) → inlR (fst a true)
                 ; (i = i1) → push* (fst a true) (fst (snd a) true) (snd (snd a) true) (i₁ ∧ (~ k ∨ r))
                 ; (i₁ = i0) → inlR (fst a true)
                 ; (i₁ = i1) → lUnit-filler (push* (fst a true) (fst (snd a) true) (snd (snd a) true)) r k i
                 ; (k = i0) → push* (fst a true) (fst (snd a) true) (snd (snd a) true) (i ∧ i₁)
                 ; (k = i1) → compPath-filler refl (push* (fst a true) (fst (snd a) true) (snd (snd a) true)) (r ∧ i₁) i})
        (push* (fst a true) (fst (snd a) true) (snd (snd a) true) (i ∧ (i₁ ∧ ~ k)))


ΠR-extend→× : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
  → 2-elter.ΠR-extend (RP∞'· ℓ) (fst J) A
  → joinR-gen (fst J) (A true) × joinR-gen (fst J) (A false)
ΠR-extend→× J A t = ΠBool→× {A = λ x → joinR-gen (fst J) (A x)} (ΠR-extend→Π-alt J A t)

ΠR-extend→×-old : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
  → 2-elter.ΠR-extend (RP∞'· ℓ) (fst J) A
  → joinR-gen (fst J) (A true) × joinR-gen (fst J) (A false)
ΠR-extend→×-old {ℓ = ℓ} J A t =
  ΠBool→× {A = λ x → joinR-gen (fst J) (A x)}
    (2-elter.ΠR-extend→Π (RP∞'· ℓ) (fst J) A t)

Square-filler : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : z ≡ y)
  → I → I → I → A
Square-filler {y = y} p q i j k =
  hfill (λ k → λ {(i = i0) → p (~ j ∨ ~ k)
                 ; (i = i1) → q (j ∨ ~ k)
                 ; (j = i0) → q (~ k ∨ ~ i)
                 ; (j = i1) → p (i ∨ ~ k)})
         (inS y)
         k

private
  module _ {ℓ : Level} (J : Type) (A : Bool → J → Type ℓ) where

    fill₂-b : (a a' : J) (b : A true a) (b₁ : A false a')
            (c : (i₂ : J) → A true i₂)
            (c₁ : (i₂ : J) → A false i₂)
            (x : c a ≡ b)
            (d : c₁ a' ≡ b₁)
          → I → I → I → 2-elter.ΠR-extend (RP∞'· ℓ) J A
    fill₂-b a a' b b₁ c c₁ x d i i₁ r = Square-filler {A = 2-elter.ΠR-extend (RP∞'· ℓ) J A}
          (push (true , inl (CasesBool true (a , b) (a' , b₁) , c₁ , d)))
          (push (false , inl (CasesBool true (a , b) (a' , b₁) , c , x)))
           i i₁ r

    fill₂ : (a a' : J) (b : A true a) (b₁ : A false a')
            (c : (i₂ : J) → A true i₂)
            (c₁ : (i₂ : J) → A false i₂)
            (x : c a ≡ b)
            (d : c₁ a' ≡ b₁)
          → I → I → I → 2-elter.ΠR-extend (RP∞'· ℓ) J A
    fill₂ a a' b b₁ c c₁ x d i i₁ r =
      hfill (λ r → λ {(i = i0) → push (true , inl (CasesBool true (a , b) (a' , b₁) , c₁ , d)) (~ i₁)
                 ; (i = i1) → push (false , push ((CasesBool true (a , b) (a' , b₁)) , (CasesBool true c c₁ , CasesBool true x d)) r) i₁
                 ; (i₁ = i0) → push (false , inl (CasesBool true (a , b) (a' , b₁) , c , x)) (~ i)
                 ; (i₁ = i1) → push (true , push ((CasesBool true (a , b) (a' , b₁)) , ((CasesBool true c c₁) , CasesBool true x d)) r) i})
        (inS (Square-filler {A = 2-elter.ΠR-extend (RP∞'· ℓ) J A}
          (push (true , inl (CasesBool true (a , b) (a' , b₁) , c₁ , d)))
          (push (false , inl (CasesBool true (a , b) (a' , b₁) , c , x)))
           i i₁ i1)) r

×→ΠR-extend : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
  → joinR-gen (fst J) (A true) × joinR-gen (fst J) (A false)
  → 2-elter.ΠR-extend (RP∞'· ℓ) (fst J) A
×→ΠR-extend J A (inlR x , inlR x₁) = inr (inl (CasesBool true x x₁))
×→ΠR-extend J A (inlR (x , b) , inrR x₁) = inl (true , ((_ , b) , x₁))
×→ΠR-extend J A (inlR (a , b) , push* (a' , d) c x₁ i) =
  push (true , inl ((CasesBool true (a , b) (a' , d)) , c , x₁)) (~ i)
×→ΠR-extend J A (inrR x , inlR x₁) = inl (false , (x₁ , x))
×→ΠR-extend J A (inrR x , inrR x₁) = inr (inr (CasesBool true x x₁))
×→ΠR-extend J A (inrR x , push* (a , b) c x₁ i) =
  push (false , (inr ((a , b) , ((CasesBool true x c) , x₁)))) i
×→ΠR-extend J A (push* (a , b) c x i , inlR (a' , b')) =
  push (false , inl ((CasesBool true (a , b) (a' , b')) , (c , x))) (~ i)
×→ΠR-extend J A (push* (a' , b) c x i , inrR x₁) =
  push (true , inr ((_ , b) , (CasesBool true c x₁ , x))) i
×→ΠR-extend J A (push* (a , b) c x i , push* (a' , b₁) c₁ d i₁) =
  fill₂ (fst J) A a a' b b₁ c c₁ x d i i₁ i1

×→ΠR-extend' : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
  → ((x : Bool) → joinR-gen (fst J) (A x))
  → 2-elter.ΠR-extend (RP∞'· ℓ) (fst J) A
×→ΠR-extend' J A = ×→ΠR-extend J A ∘ Iso.fun ΠBool×Iso

private
  module _ {ℓ : Level} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ) where
    fill-fill : (a a' : fst J) (b : A true a) (b₁ : A false a')
            (c : (i₂ : fst J) → A true i₂)
            (c₁ : (i₂ : fst J) → A false i₂)
            (x : c a ≡ b)
            (d : c₁ a' ≡ b₁)
          → I → I → I → joinR-gen (fst J) (A true) × joinR-gen (fst J) (A false)
    fill-fill a a' b b₁ c c₁ x d i i₁ k =
      hcomp (λ r → λ {(k = i0) → ΠR-extend→× J A (fill₂ (fst J) A a a' b b₁ c c₁ x d i i₁ r)
                 ; (k = i1) → (push* (a , b) c x (i ∧ (~ i₁ ∨ r)))
                               , push* (a' , b₁) c₁ d (((~ i) ∨ r) ∧ i₁)
                 ; (i₁ = i0) → ΠR-extend→× J A (fill₂ (fst J) A a a' b b₁ c c₁ x d i i₁ r)
                 ; (i₁ = i1) → ΠR-extend→× J A (fill₂ (fst J) A a a' b b₁ c c₁ x d i i₁ r)
                 ; (i = i0) → ΠR-extend→× J A (fill₂ (fst J) A a a' b b₁ c c₁ x d i i₁ r)
                 ; (i = i1) → ΠR-extend→× J A (fill₂ (fst J) A a a' b b₁ c c₁ x d i i₁ r)})
                 (hcomp (λ r
                → λ {(k = i0) → ΠR-extend→× J A (Square-filler {A = 2-elter.ΠR-extend (RP∞'· ℓ) (fst J) A}
                                   (push (true , inl ((CasesBool true (a , b) (a' , b₁)) , (c₁ , d))))
                                   (push (false , inl ((CasesBool true (a , b) (a' , b₁)) , (c , x))))
                                    i i₁ r)
                 ; (k = i1) → push* (a , b) c x (i ∧ ~ i₁ ∧ r) , push* (a' , b₁) c₁ d (~ i ∧ i₁ ∧ r)
                 ; (i₁ = i0) → push* (a , b) c x (r ∧ i) , inlR (a' , b₁)
                 ; (i₁ = i1) → inlR (a , b) , push* (a' , b₁) c₁ d (~ i ∧ r)
                 ; (i = i0) → inlR (a , b) , push* (a' , b₁) c₁ d (i₁ ∧ r)
                 ; (i = i1) → push* (a , b) c x (~ i₁ ∧ r) , inlR (a' , b₁) })
                 ((inlR (a , b) , inlR (a' , b₁))))

×→ΠR-extend→× : ∀ {ℓ} {J : RP∞' ℓ} (A : Bool → fst J → Type ℓ)
  (m : joinR-gen (fst J) (A true) × joinR-gen (fst J) (A false))
  → ΠR-extend→× J A (×→ΠR-extend J A m) ≡ m
×→ΠR-extend→× A (inlR (a , b) , inlR (a' , d)) = refl
×→ΠR-extend→× A (inlR (a , snd₁) , inrR x₁) = refl
×→ΠR-extend→× A (inlR (a , b) , push* (a' , d) e x₁ i) = refl
×→ΠR-extend→× A (inrR x , inlR (a , b)) = refl
×→ΠR-extend→× A (inrR x , inrR x₁) = refl
×→ΠR-extend→× A (inrR x , push* (a' , b) c x₁ i) = refl
×→ΠR-extend→× A (push* (a , b) b₁ x i , inlR (a' , b')) = refl
×→ΠR-extend→× A (push* (a , b) b₁ x i , inrR x₁) = refl
×→ΠR-extend→× {J = J} A (push* (a , b) b₁ x i , push* (a' , b') c x₁ i₁) k =
  fill-fill J A a a' b b' b₁ c x x₁ i i₁ k


ΠR-extend→×→ΠR-extend-inl : ∀ {ℓ} (J : RP∞' ℓ)
  (A : Bool → fst J → Type ℓ) (m : _)
  → ×→ΠR-extend J A (ΠR-extend→× J A (inl m)) ≡ (inl m)
ΠR-extend→×→ΠR-extend-inl J A (false , (b , c) , d) = refl
ΠR-extend→×→ΠR-extend-inl J A (true , (b , c) , d) = refl

fill23 : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
  (f : TotΠ (λ i₁ → Σ (fst J) (A i₁)))
  (a : (i₁ : Bool) (j₁ : fst J) → A i₁ j₁)
  (b : (i₁ : Bool) → a i₁ (f i₁ .fst) ≡ f i₁ .snd)
  → I → I → I → 2-elter.ΠR-extend (RP∞'· ℓ) (fst J) A
fill23 J A f a b i j k =
  hfill (λ r → λ {(i = i0) → push (true , (inl (CasesBoolη f j , a false , b false))) r
                 ; (i = i1) → push (true , (inr (f true , CasesBoolη a j , b true))) r
                 ; (j = i0) → fill₂ (fst J) A (fst (f true)) (fst (f false)) (snd (f true))
                                       (snd (f false)) (a true) (a false) (b true) (b false) (i ∧ r) (i ∨ ~ r) i1
                 ; (j = i1) → push (true , (push (f , (a , b)) i)) r})
        (inS (inl (true , f true , a false)))
        k

fill23PP : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
  (f : TotΠ (λ i₁ → Σ (fst J) (A i₁)))
  (a : (i₁ : Bool) (j₁ : fst J) → A i₁ j₁)
  (b : (i₁ : Bool) → a i₁ (f i₁ .fst) ≡ f i₁ .snd)
  → Square (λ j → push (true , (inl (CasesBoolη f j , a false , b false))) i1)
            (λ j → push (true , (inr (f true , CasesBoolη a j , b true))) i1)
                  (λ i → fill₂ (fst J) A (fst (f true)) (fst (f false)) (snd (f true))
                                 (snd (f false)) (a true) (a false) (b true) (b false) i i i1)
            λ i → push (true , (push (f , (a , b)) i)) i1
fill23PP J A f a b i j = fill23 J A f a b i j i1

fill23' : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
  (f : TotΠ (λ i₁ → Σ (fst J) (A i₁)))
  (a : (i₁ : Bool) (j₁ : fst J) → A i₁ j₁)
  (b : (i₁ : Bool) → a i₁ (f i₁ .fst) ≡ f i₁ .snd)
  → I → I → I → 2-elter.ΠR-extend (RP∞'· ℓ) (fst J) A
fill23' J A f a b i j k =
  hfill (λ r → λ {(i = i0) → push (false , inl (CasesBoolη f j , a true , b true)) r
                 ; (i = i1) → push (false , (inr (f false , CasesBoolη a j , b false))) r
                 ; (j = i0) → fill₂ (fst J) A (fst (f true)) (fst (f false)) (snd (f true))
                                       (snd (f false)) (a true) (a false) (b true) (b false) (i ∨ ~ r) (i ∧ r) i1
                 ; (j = i1) → push (false , (push (f , (a , b)) i)) r})
        (inS (inl (false , f false , a true)))
        k

fill23PP≡ : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
  (f : TotΠ (λ i₁ → Σ (fst J) (A i₁)))
  (a : (i₁ : Bool) (j₁ : fst J) → A i₁ j₁)
  (b : (i₁ : Bool) → a i₁ (f i₁ .fst) ≡ f i₁ .snd)
  → fill23PP J A f a b ≡ λ i j → fill23' J A f a b i j i1
fill23PP≡ {ℓ = ℓ} J A f a b k i j =
  hcomp (λ r → λ {(i = i0) → push (true , inl (CasesBoolη f j , a false , b false)) (r ∨ k)
                 ; (i = i1) → push (true , inr (f true , CasesBoolη a j , b true)) (r ∨ k)
                 ; (j = i0) → fill₂ (fst J) A (fst (f true)) (fst (f false)) (snd (f true))
                                       (snd (f false)) (a true) (a false) (b true) (b false) (i ∧ (r ∨ k)) (i ∨ ~ (r ∨ k)) i1
                 ; (j = i1) → push (true , push (f , a , b) i) (r ∨ k)
                 ; (k = i0) → fill23 J A f a b i j r
                 ; (k = i1) → fill23' J A f a b i j i1})
    (hcomp (λ r → λ {(i = i0) → push (true , inl (CasesBoolη f j , a false , b false)) k
                 ; (i = i1) → push (true , push (CasesBoolη f j , CasesBoolη a j , lee j) r) k
                 ; (j = i0) → fill₂ (fst J) A (fst (f true)) (fst (f false)) (snd (f true))
                                       (snd (f false)) (a true) (a false) (b true) (b false) (i ∧ k) (i ∨ ~ k) r
                 ; (j = i1) → push (true , push (f , a , b) (r ∧ i)) k
                 ; (k = i0) → inl (true , f true , a false)
                 ; (k = i1) → tap2 r j i})
      (hcomp (λ r → λ {(i = i0) → push (true , inl (CasesBoolη f j , a false , b false)) (k ∨ ~ r)
                 ; (i = i1) → push (true , inl ((CasesBoolη f j) , ((a false) , (b false)))) (k ∨ ~ r)
                 ; (j = i0) → fill₂-b (fst J) A (fst (f true)) (fst (f false)) (snd (f true))
                                       (snd (f false)) (a true) (a false) (b true) (b false) (i ∧ k) (i ∨ ~ k) r
                 ; (j = i1) → push (true , inl (f , a false , b false)) (k ∨ ~ r)
                 ; (k = i0) → push (true , inl (CasesBoolη f j , a false , b false)) (~ r)
                 ; (k = i1) → tap r j i})
             ((inr (inl (CasesBoolη f j))))))
   where
   H = 2-elter.ΠR-extend (RP∞'· ℓ) (fst J) A

   topSqfiller : I → I → I → H
   topSqfiller i j k =
     hfill (λ r → λ {(i = i0) → fill₂-b (fst J) A (fst (f true)) (fst (f false)) (snd (f true))
                                            (snd (f false)) (a true) (a false) (b true) (b false) j j r
                 ; (i = i1) → inr (push (f , (a , CasesBool true (b true) (b false))) (~ r ∧ ~ j))
                 ; (j = i0) → inr (push ((CasesBoolη f i) , (a , (CasesBool true (b true) (b false)))) (~ r ∧ i))
                 ; (j = i1) → inr (inl (CasesBoolη f i))})
       (inS ((inr
          (push (CasesBoolη f i , a , CasesBool true (b true) (b false)) (i ∧ ~ j)))))
       k

   topSq : Square {A = H}
      (λ i₁ →
         fill₂-b (fst J) A (fst (f true)) (fst (f false)) (snd (f true))
         (snd (f false)) (a true) (a false) (b true) (b false) i₁ i₁ i1)
      (λ _ → inr (inl f)) (λ j₁ → inr (inl (CasesBoolη f j₁)))
      (λ j₁ → inr (inl (CasesBoolη f j₁)))
   topSq i j = topSqfiller i j i1
  
   tap : Cube {A = H}
              (λ j i → inr (inl (CasesBoolη f j)))
              topSq
              (λ r i → fill₂-b (fst J) A (fst (f true)) (fst (f false)) (snd (f true))
                         (snd (f false)) (a true) (a false) (b true) (b false) i i r)
              (λ _ _ → inr (inl f))
              (λ r j → inr (inl (CasesBoolη f j)))
              (λ r j → inr (inl (CasesBoolη f j))) -- r j i
   tap i j k =
     hcomp (λ r → λ {(i = i0) → inr (push (CasesBoolη f j , a , CasesBool true (b true) (b false)) (~ r ∧ ~ k ∧ j))
                 ; (i = i1) → topSqfiller j k r
                 ; (j = i0) → fill₂-b (fst J) A (fst (f true)) (fst (f false)) (snd (f true))
                                (snd (f false)) (a true) (a false) (b true) (b false) k k (i ∧ r)
                 ; (j = i1) → inr (push (f , a , CasesBool true (b true) (b false)) (~ r ∧ ~ k))
                 ; (k = i0) → inr (push (CasesBoolη f j , a , CasesBool true (b true) (b false)) (~ r ∧ j))
                 ; (k = i1) → inr (inl (CasesBoolη f j))})
           ((inr
          (push (CasesBoolη f j , a , CasesBool true (b true) (b false))
           (~ k ∧ j))))


   lee : PathP (λ i₁ → (i₃ : Bool) → CasesBoolη a i₁ i₃ (CasesBoolη f i₁ i₃ .fst) ≡ CasesBoolη f i₁ i₃ .snd) (CasesBool true (b true) (b false)) b
   lee = funTypePP λ { false → refl ; true → refl}


   tap2 : Cube {A = H}
              (λ j i → topSq j i)
              (λ j i → fill23' J A f a b i j i1)
              (λ r i → fill₂ (fst J) A (fst (f true)) (fst (f false)) (snd (f true))
                    (snd (f false)) (a true) (a false) (b true) (b false) i i r)
              (λ r i → inr (push (f , a , b) (r ∧ i)))
              (λ i j → inr (inl (CasesBoolη f j)))
              λ i j → inr (push (CasesBoolη f j , CasesBoolη a j , lee j) i)
   tap2 r i j =
     hcomp (λ k → λ {(i = i0) → fill₂ (fst J) A (fst (f true)) (fst (f false)) (snd (f true))
                                       (snd (f false)) (a true) (a false) (b true) (b false) (j ∨ (~ k ∧ r)) (j ∧ (k ∨ ~ r)) r
                 ; (i = i1) → push (false , push (f , a , b) (r ∧ j)) (k ∨ ~ r)
                 ; (j = i0) → push (false , inl ((CasesBoolη f i) , ((a true) , (b true)))) (k ∨ ~ r)
                 ; (j = i1) → push (false , push ((CasesBoolη f i) , (CasesBoolη a i , lee i)) r) (k ∨ ~ r)
                 ; (r = i0) → topSqfiller i j i1
                 ; (r = i1) → fill23' J A f a b j i k})
           (hcomp (λ k → λ {(i = i0) →
             fill₂ (fst J) A (fst (f true)) (fst (f false)) (snd (f true)) (snd (f false)) (a true) (a false) (b true) (b false) (j ∨ r) (j ∧ (~ r)) (r ∧ k)
                 ; (i = i1) → push (false , push (f , a , CasesBoolη b k) (r ∧ (j ∧ k))) (~ r)
                 ; (j = i0) → push ((false , inl (CasesBoolη f i , a true , b true))) (~ r)
                 ; (j = i1) → push ((false , push (CasesBoolη f i , CasesBoolη a i , helpme k i) (r ∧ k))) (~ r)
                 ; (r = i0) → topSqfiller i j i1 -- topSqfiller i j i1
                 ; (r = i1) → inl (false , f false , a true)})
              (hcomp (λ k → λ {(i = i0) → fill₂-b (fst J) A (fst (f true)) (fst (f false))
                                             (snd (f true)) (snd (f false))
                                             (a true) (a false) (b true) (b false) (j ∨ r) (j ∧ (~ r)) k
                 ; (i = i1) → push (false , push (f , (a , CasesBool true (b true) (b false))) ((~ r ∧ ~ j)  ∧ ~ k)) (~ k ∨ (~ r))
                 ; (j = i0) → push (false , push ((CasesBoolη f i) , (a , CasesBool true (b true) (b false))) (~ r ∧ (~ k ∧ i))) (~ k ∨ (~ r))
                 ; (j = i1) → push (false , inl (CasesBoolη f i , a true , b true)) (~ k ∨ ~ r)
                 ; (r = i0) → topSqfiller i j k
                 ; (r = i1) → push (false , (inl (CasesBoolη f i , a true , b true))) (~ k)})
                (inr (push (CasesBoolη f i , a , CasesBool true (b true) (b false)) (i ∧ (~ j ∧ ~ r))))))
                where
                harp : PathP
                       (λ i₁ →
                          (i₃ : Bool) →
                          CasesBoolη a i₁ i₃ (CasesBoolη f i₁ i₃ .fst) ≡
                          CasesBoolη f i₁ i₃ .snd)
                       (CasesBool true (b true) (b false))
                       (CasesBool true (b true) (b false))
                harp = funTypePP λ { false → refl ; true → refl}
                helpme : SquareP (λ k i → (i₁ : Bool) → CasesBoolη a i i₁ (CasesBoolη f i i₁ .fst) ≡ CasesBoolη f i i₁ .snd)
                              harp (λ i → lee i) (refl {x = CasesBool true (b true) (b false)}) (CasesBoolη b)
                helpme i a false = b false
                helpme i a true = b true

ΠR-extend→×→ΠR-extend : ∀ {ℓ} {J : RP∞' ℓ} (A : Bool → fst J → Type ℓ) (m : _)
  → ×→ΠR-extend J A (ΠR-extend→× J A m) ≡ m
ΠR-extend→×→ΠR-extend {J = J} A (inl m) = ΠR-extend→×→ΠR-extend-inl J A m
ΠR-extend→×→ΠR-extend A (inr (inl x)) j = inr (inl (CasesBoolη x j))
ΠR-extend→×→ΠR-extend A (inr (inr x)) j = inr (inr (CasesBoolη {A = λ i → TotΠ (A i)} x j ))
ΠR-extend→×→ΠR-extend {J = J} A (inr (push (f , a , b) i)) j = fill23 J A f a b i j i1
ΠR-extend→×→ΠR-extend A (push (false , inl (f , q , t)) i) i₁ = push (false , inl (CasesBoolη f i₁ , q , t)) i
ΠR-extend→×→ΠR-extend A (push (true , inl (f , q , t)) i) i₁ = push (true , inl (CasesBoolη f i₁ , q , t)) i
ΠR-extend→×→ΠR-extend A (push (false , inr (f , q , t)) i) j = push (false , inr (f , CasesBoolη q j , t)) i
ΠR-extend→×→ΠR-extend A (push (true , inr (f , q , t)) i) j = push (true , inr (f , CasesBoolη q j , t)) i
ΠR-extend→×→ΠR-extend {J = J} A (push (false , push (f , q , t) i₂) i) i₁ =
  hcomp (λ r → λ {(i = i0) → inl (false , f false , q true)
                  ; (i = i1) → fill23PP≡ J A f q t (~ r) i₂ i₁
                  ; (i₁ = i0) → fill₂ (fst J) A (fst (f true)) (fst (f false))
                                         (snd (f true)) (snd (f false))
                                         (q true) (q false)
                                         (t true) (t false)
                                         ((~ i) ∨ i₂) (i ∧ i₂) i1
                  ; (i₁ = i1) → push (false , push (f , q , t) i₂) i -- push (false , {!!}) i
                  ; (i₂ = i0) → push (false , inl (CasesBoolη f i₁ , q true , t true)) i
                  ; (i₂ = i1) → push (false , inr (f false , CasesBoolη q i₁ , t false)) i})
     (hcomp (λ r → λ {(i = i0) → inl (false , f false , q true)
                  ; (i = i1) → fill23' J A f q t i₂ i₁ r
                  ; (i₁ = i0) → fill₂ (fst J) A (fst (f true)) (fst (f false))
                                         (snd (f true)) (snd (f false))
                                         (q true) (q false)
                                         (t true) (t false)
                                         ((~ i) ∨ (i₂ ∨ ~ r)) (i ∧ (i₂ ∧ r)) i1
                  ; (i₁ = i1) → push (false , push (f , q , t) i₂) (r ∧ i)
                  ; (i₂ = i0) → push (false , (inl ((CasesBoolη f i₁) , ((q true) , (t true))))) (i ∧ r)
                  ; (i₂ = i1) → push (false , inr (f false , CasesBoolη q i₁ , t false)) (i ∧ r)})
                  (inl (false , f false , q true)))
ΠR-extend→×→ΠR-extend {J = J} A (push (true , push (f , q , t) i₂) i) i₁ =
  hcomp (λ r → λ {(i = i0) → inl (true , f true , q false)
                  ; (i = i1) → fill23 J A f q t i₂ i₁ r
                  ; (i₁ = i0) → fill₂ (fst J) A (fst (f true)) (fst (f false))
                                         (snd (f true)) (snd (f false))
                                         (q true) (q false)
                                         (t true) (t false)
                                         (i ∧ (i₂ ∧ r)) ((~ i) ∨ (i₂ ∨ ~ r)) i1
                  ; (i₁ = i1) → push (true , push (f , q , t) i₂) (r ∧ i)
                  ; (i₂ = i0) → push (true , inl (CasesBoolη f i₁ , q false , t false)) (i ∧ r)
                  ; (i₂ = i1) → push (true , inr (f true , CasesBoolη q i₁ , t true)) (i ∧ r)})
          (inl (true , f true , q false))


ΠR-extend→×Iso : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
  → Iso (2-elter.ΠR-extend (RP∞'· ℓ) (fst J) A)
         (joinR-gen (fst J) (A true) × joinR-gen (fst J) (A false))
Iso.fun (ΠR-extend→×Iso J A) = ΠR-extend→× J A
Iso.inv (ΠR-extend→×Iso J A) = ×→ΠR-extend J A
Iso.rightInv (ΠR-extend→×Iso J A) = ×→ΠR-extend→× {J = J} A
Iso.leftInv (ΠR-extend→×Iso J A) = ΠR-extend→×→ΠR-extend {J = J} A

module _ {ℓ : Level} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
  where
  module ΠR-extend→Π-equiv-base-lemmas where
    p : ΠR-extend→Π-alt J A ≡ 2-elter.ΠR-extend→Π (RP∞'· ℓ) (fst J) A
    p = funExt λ x → funExt (ΠR-extend→Π-alt≡ {J = J} A x)

    alt : (2-elter.ΠR-extend (RP∞'· ℓ) (fst J) A) ≃ ((x : Bool) → joinR-gen (fst J) (A x))
    alt = isoToEquiv (compIso (ΠR-extend→×Iso J A) (invIso ΠBool×Iso))

    altid : fst alt ≡ ΠR-extend→Π-alt J A
    altid = funExt λ x → funExt (CasesBool true refl refl)

    isEq : isEquiv (ΠR-extend→Π-alt J A)
    isEq = subst isEquiv altid (snd alt)

  open ΠR-extend→Π-equiv-base-lemmas
  ΠR-extend→Π-equiv-base : isEquiv (2-elter.ΠR-extend→Π (RP∞'· ℓ) (fst J) A)
  ΠR-extend→Π-equiv-base = transport (λ i → isEquiv (p i)) isEq

ΠR-extend→Π-equiv : ∀ {ℓ} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
  → isEquiv (2-elter.ΠR-extend→Π I (fst J) A)
ΠR-extend→Π-equiv {ℓ} =
  RP∞'pt→Prop (λ _ → isPropΠ2 λ _ _ → isPropIsEquiv _) ΠR-extend→Π-equiv-base
