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


module Cubical.Cohomology.EilenbergMacLane.Steenrod5 where
open import Cubical.HITs.Join
open import Cubical.Functions.FunExtEquiv

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
  
  ΠR-base : Type _
  ΠR-base =
    Pushout {A = Σ[ f ∈ (TotΠ λ i → Σ[ j ∈ J ] (A i j)) ]
      (Σ[ g ∈ ((i : fst I) (j : J) → A i j) ] ((i : fst I) → g i (f i .fst) ≡ f i .snd))}
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

  fat : Type _
  fat = (Σ[ f ∈ ((i : fst I) → Σ[ j ∈ J ] A i j) ]
          Σ[ g ∈ ((i : fst I) (j : J) → A i j) ]
            ((i : fst I) → g i (f i .fst) ≡ f i .snd))

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

module 2-elter' {ℓ : Level} (I : RP∞' ℓ) (J : Type) (A : fst I → J → Type ℓ) where
  private
    I2 = snd I
  notI : fst I → fst I
  notI = I2 .fst .fst

  elimI : {B : fst I → Type ℓ} → _
  elimI {B} = I2 .fst .snd .snd B .fst

  elimIβ : {B : fst I → Type ℓ} → _
  elimIβ {B} = I2 .fst .snd .snd B .snd

  elimIη : {B : fst I → Type ℓ} (g : (x : _) → B x) (i : fst I) → elimI i (g i) (g (notI i)) ≡ g
  elimIη g i = funExt (elimI i (elimIβ i (g i) (g _) .fst) (elimIβ i (g i) (g _) .snd))

  elimIη-id : {B : fst I → Type ℓ} (g : (x : _) → B x) (i : fst I)
    → (funExt⁻ (elimIη g i) i  ≡ elimIβ i (g i) (g (notI i)) .fst)
    × (funExt⁻ (elimIη g i) (notI i)  ≡ elimIβ i (g i) (g (notI i)) .snd)
  elimIη-id = λ g i → elimIβ {B = λ i → _ ≡ _} i (elimIβ i (g i) (g _) .fst) (elimIβ i (g i) (g _) .snd)

  ΠR-baseB = Σ[ f ∈ (TotΠ λ i → Σ[ j ∈ J ] (A i j)) ]
        (Σ[ g ∈ ((i : fst I) (j : J) → A i j) ]
          ((i : fst I) → g i (f i .fst) ≡ f i .snd))

  eval : J ⊎ (fst I ≃ J) → fst I → J 
  eval = evalG

  ΠR-baseN1 =
    Σ[ fg ∈ (Σ[ f ∈ J ⊎ (fst I ≃ J) ] ((i : fst I) → A i (eval f i))) ]
        (Σ[ g ∈ ((i : fst I) (j : J) → A i j) ]
          ((i : fst I) → g i (eval (fst fg) i) ≡ snd fg i))

  ΠR-base-back = (J ⊎ (fst I ≃ J)) × ((i : fst I) (j : J) → A i j)

  ΠR-base-back→Σ : ΠR-base-back → Σ[ e ∈ J ⊎ (fst I ≃ J) ] ((i : fst I) → A i (eval e i))
  ΠR-base-back→Σ (f , g) = f , λ i → g i (eval f i)

  ΠR-base-back→Π : ΠR-base-back → TotΠ (λ i → TotΠ (λ j → A i j))
  ΠR-base-back→Π = snd

  ΠR-base : Type _
  ΠR-base = Pushout {A = ΠR-base-back}
                    {B = Σ[ e ∈ J ⊎ (fst I ≃ J) ] ((i : fst I) → A i (eval e i))}
                    {C = TotΠ (λ i → TotΠ (λ j → A i j))}
                    ΠR-base-back→Σ
                    ΠR-base-back→Π

  left-push : Type _
  left-push = Σ[ i ∈ fst I ] (Σ[ j ∈ J ] (A i j)) × ((j : J) → A (notI i) j)

  left-push↑ₗ : fst I → Type _
  left-push↑ₗ i =  Σ[ e ∈ J ⊎ (fst I ≃ J) ] A i (eval e i) × ((j : J) → A (notI i) j)

  left-push↑ᵣ : fst I → Type _
  left-push↑ᵣ i = J × ((i : fst I) (j : J) → A i j)

  fat : Type _
  fat = (J ⊎ (fst I ≃ J)) × (((i : fst I) (j : J) → A i j))

  fat→ₗ : (i : fst I) → fat → left-push↑ₗ i
  fat→ₗ i (f , g) = f , ((g i (eval f i)) , (g (notI i)))

  fat→ᵣ : (i : fst I) → fat → left-push↑ᵣ i
  fat→ᵣ i (f , g) = eval f i , g

  PushTop : Type _
  PushTop = Σ[ i ∈ fst I ] (Pushout (fat→ₗ i) (fat→ᵣ i))

  PushTop→left-push' : (i : fst I)
    → (Pushout (fat→ₗ i) (fat→ᵣ i))
    → (Σ[ j ∈ J ] (A i j)) × ((j : J) → A (notI i) j)
  PushTop→left-push' i (inl (f , g)) = (eval f i , g .fst) , g .snd
  PushTop→left-push' i (inr (f , g)) = (f , g i f) , (g (notI i))
  PushTop→left-push' i (push (f , g) k) = ((eval f i) , (g i (eval f i))) , g (notI i)

  PushTop→left-push : PushTop → left-push
  PushTop→left-push (i , x) = (i , PushTop→left-push' i x)

  inrΠR : _ → ΠR-base
  inrΠR = inr

  elimIηPushTop : (i : fst I) (x : J ⊎ (fst I ≃ J)) (g : (i₂ : fst I) (j₁ : J) → A i₂ j₁)
    → _ ≡ _
  elimIηPushTop i x g = elimIη (λ i' → g i' (eval x i')) i

  PushTop→ΠR-base : PushTop → ΠR-base
  PushTop→ΠR-base (i , inl (f , g)) = inl (f , elimI i (fst g) (snd g _))
  PushTop→ΠR-base (i , inr (f , g)) = inr g -- inr g
  PushTop→ΠR-base (i , push (x , g) i₁) =
      ((λ j → inl (x , elimIηPushTop i x g j))
    ∙ push (x , g)) i₁

  ΠR-extend : Type _
  ΠR-extend = Pushout PushTop→left-push PushTop→ΠR-base


  ΠR-extend→Πₗ : left-push → TotΠ (λ i → joinR-gen J (A i))
  ΠR-extend→Πₗ (i , p , r) = elimI i (inlR p) (inrR r)

  ΠR-base→ : ΠR-base → TotΠ (λ i → joinR-gen J (A i))
  ΠR-base→ (inl (f , p)) i = inlR ((eval f i) , (p i))
  ΠR-base→ (inr x) i = inrR (x i)
  ΠR-base→ (push a i') i = push* (eval (fst a) i , snd a i _) (snd a i) refl i'


  pre-eqvl-diag : (i' : fst I) (p : Pushout (fat→ₗ i') (fat→ᵣ i'))
    → ΠR-extend→Πₗ (PushTop→left-push (i' , p)) i'
     ≡ ΠR-base→ (PushTop→ΠR-base (i' , p)) i'
  pre-eqvl-diag i' (inl (f , g)) = elimIβ i' (inlR (eval f i' , g .fst)) (inrR (g .snd)) .fst
                                 ∙ cong inlR (ΣPathP (refl , sym (elimIβ i' (g .fst) (g .snd _) .fst)))
  pre-eqvl-diag i' (inr (f , g)) =
    elimIβ {B = λ x → joinR-gen J (A x) } i' (inlR (f , g i' f)) (inrR (g (notI i'))) .fst  ∙ push* (f , g i' f) (g i') refl
  pre-eqvl-diag i' (push (f , g) i) j =
    hcomp (λ k → λ {(i = i0) → (elimIβ {B = λ i → joinR-gen J (A i)} i'
                                   (inlR (eval f i' , g i' (eval f i')))
                                   (inrR (g (notI i'))) .fst
                                 ∙ cong inlR (ΣPathP (refl , sym (elimIη-id (λ i' → g i' (eval f i')) i' .fst k)))) j
                   ; (i = i1) → compPath-filler
                                   (elimIβ {B = λ i → joinR-gen J (A i)} i'
                                     (inlR (eval f i' , g i' (eval f i'))) (inrR (g (notI i'))) .fst)
                                   (push*  (eval f i' , g i' (eval f i'))
                                           (g i')
                                           refl) k j
                   ; (j = i0) → ΠR-extend→Πₗ (PushTop→left-push (i' , push (f , g) i)) i'
                   ; (j = i1) → ΠR-base→ ((compPath-filler (λ j → inl (f , elimIη (λ i' → g i' (eval f i')) i' j)) (push (f , g)) k i)) i'})
      (hcomp (λ k → λ {(i = i0) → compPath-filler
                                      (elimIβ {B = λ i → joinR-gen J (A i)} i'
                                       (inlR (eval f i' , g i' (eval f i')))
                                       (inrR (g (notI i'))) .fst)
                                    (cong inlR (ΣPathP (refl , sym (funExt⁻ (elimIη (λ i'' → g i'' (eval f i'')) i') i')))) k j
                   ; (i = i1) → elimIβ {B = λ i → joinR-gen J (A i)} i' (inlR (eval f i' , g i' (eval f i'))) (inrR (g (notI i'))) .fst j
                   ; (j = i0) → ΠR-extend→Πₗ (PushTop→left-push (i' , push (f , g) i)) i'
                   ; (j = i1) → inlR ((eval f i') , elimIη (λ i'' → g i'' (eval f i'')) i' (i ∨ ~ k) i')
                   })
                   (elimIβ {B = λ i → joinR-gen J (A i)} i' (inlR (eval f i' , g i' (eval f i'))) (inrR (g (notI i'))) .fst j))


  pre-eqvl-not : (i' : fst I) (p : Pushout (fat→ₗ i') (fat→ᵣ i'))
    → ΠR-extend→Πₗ (PushTop→left-push (i' , p)) (notI i') ≡
      ΠR-base→ (PushTop→ΠR-base (i' , p)) (notI i')
  pre-eqvl-not i' (inl (f , g)) =
      elimIβ i' (inlR (eval f i' , g .fst)) (inrR (g .snd)) .snd
    ∙ sym (push* (eval f (notI i') , _) (g .snd) (sym (elimIβ i' (fst g)  (snd g (eval f (notI i'))) .snd)))
  pre-eqvl-not i' (inr (f , g)) = elimIβ {B = λ x → joinR-gen J (A x)} i' (inlR (f , g i' f)) (inrR (g (notI i'))) .snd
  pre-eqvl-not i' (push (f , g) i) j =
    hcomp (λ r → λ {(i = i0) → (elimIβ {B = λ x → joinR-gen J (A x)} i' (inlR (eval f i' , g i' (eval f i'))) (inrR (g (notI i'))) .snd
                               ∙ sym (push* (eval f (notI i') , elimI {B = (λ z → A z (eval f z))} i' (g i' (eval f i')) (g (notI i') (eval f (notI i'))) (notI i'))
                                          (g (notI i'))
                                          ((sym ((elimIη-id (λ x → g x (eval f x)) i') .snd r))))) j
                   ; (i = i1) → elimIβ {B = λ x → joinR-gen J (A x)} i'
                                  (inlR (eval f i' , g i' (eval f i'))) (inrR (g (notI i'))) .snd j
                   ; (j = i0) → elimI {B = λ x → joinR-gen J (A x)} i'
                                  (inlR (eval f i' , g i' (eval f i'))) (inrR (g (notI i'))) (notI i')
                   ; (j = i1) → ΠR-base→ (compPath-filler'
                                            (λ i → inl (f , elimIη (λ x → g x (eval f x)) i' i))
                                            (push (f , g)) i1 i) (notI i')
                   })
      (hcomp (λ r → λ {(i = i0) → (elimIβ {B = λ x → joinR-gen J (A x)} i' (inlR (eval f i' , g i' (eval f i'))) (inrR (g (notI i'))) .snd
                                  ∙ sym (push* (eval f (notI i') , elimIη (λ x → g x (eval f x)) i' (~ r) (notI i'))
                                           (g (notI i'))
                                           λ i → elimIη (λ x → g x (eval f x)) i' (~ r ∨ ~ i) (notI i'))) j
                   ; (i = i1) → elimIβ {B = λ x → joinR-gen J (A x)} i'
                                  (inlR (eval f i' , g i' (eval f i'))) (inrR (g (notI i'))) .snd j
                   ; (j = i0) → elimI {B = λ x → joinR-gen J (A x)} i'
                                  (inlR (eval f i' , g i' (eval f i'))) (inrR (g (notI i'))) (notI i')
                   ; (j = i1) → ΠR-base→ (compPath-filler'
                                            (λ i → inl (f , elimIη (λ x → g x (eval f x)) i' i))
                                            (push (f , g)) r i) (notI i') })
                   (compPath-filler (elimIβ {B = λ x → joinR-gen J (A x)} i' (inlR (eval f i' , g i' (eval f i'))) (inrR (g (notI i'))) .snd)
                                    (sym (push* (eval f (notI i') , g (notI i') (eval f _)) (g (notI i')) refl))
                                    (~ i) j))

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

  left-push→double : left-push → joinR-gen J λ j → joinR-gen (fst I) (λ i → A i j)
  left-push→double (i , (c , r)) = inlR ((c .fst) , (inrR (elimI i (c .snd) (r (c .fst)))))


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
  fatcoh x = ΣPathP ((funExt (CasesBool true refl refl)) , refl) -- ΣPathP ((funExt (CasesBool true refl refl)) , refl)

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
    → isoToEquiv (equivToIso (PushTop≃Main I i J A .fst))

  Π-extend→ : Iso (2nd.ΠR-extend) (1st.ΠR-extend)
  Π-extend→ = pushoutIso _ _ _ _
    PushTopIso
    (idEquiv _)
    (ΠR-base≃ I J A)
    (funExt (uncurry λ i y → PushTop≃Main I i J A .snd y .fst))
    (funExt (uncurry λ i y → PushTop≃Main I i J A .snd y .snd))

  

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

module inl-case {ℓ : Level} (I : RP∞' ℓ)  (J : Type) (A : fst I → J → Type ℓ) where
  private
    module M = 2-elter' I J A
    open M

  record ΠR-extendOut-inl : Type ℓ where
    field
      left-pushOut : left-push → joinR-gen J (λ j → joinR-gen (fst I) (λ i → A i j))
      ΠROut-inlₗ : (j : J) (g : (i : fst I) → A i j) → joinR-gen J (λ j → joinR-gen (fst I) (λ i → A i j))
      ΠROut-push : (j : J) (g : ((i : fst I) (j : J) → A i j)) → ΠROut-inlₗ j (λ i → g i j) ≡ inrR λ j → inrR λ i → g i j
      fatₗₗ : (i' : fst I) (x : J) (p : A i' x × ((j : J) → A (notI i') j))
               → left-pushOut (PushTop→left-push (i' , inl (inl x , p))) ≡ ΠROut-inlₗ x (elimI i' (fst p) (snd p x))
      fatᵣ : (i' : fst I) (x : J) (p : (i : fst I) (j : J) → A i j)
               → left-pushOut (i' , PushTop→left-push' i' (inr (x , p)))
                ≡ inrR λ j → inrR λ i → p i j
      fat-pushₗ : (i' : fst I) (x : J) (p : (i : fst I) (j : J) → A i j)
               → Square (λ j → left-pushOut (PushTop→left-push (i' , push (inl x , p) j)))
                         (cong (ΠROut-inlₗ x) (elimIη (λ i → p i x) i') ∙ ΠROut-push x p)
                         (fatₗₗ i' x (p i' x , p (notI i')))
                         (fatᵣ i' x p)


record ΠR-extendOut-inr {ℓ : Level} (I : RP∞' ℓ)
  (J : Type) (e : fst I ≃ J) (A : fst I → J → Type ℓ)
  (left-pushOut : 2-elter'.left-push I J A  → joinR-gen J (λ j → joinR-gen (fst I) (λ i → A i j)))
  (fatᵣ : (i' : fst I) (x : J) (p : (i : fst I) (j : J) → A i j)
               → left-pushOut (i' , 2-elter'.PushTop→left-push' I J A i' (inr (x , p))) ≡ inrR λ j → inrR λ i → p i j) : Type ℓ where
  private
    module M = 2-elter' I J A
    open M

  field
    right-pushOut : ((ℓ₁ : fst I) → A ℓ₁ (fst e ℓ₁)) → joinR-gen J (λ j → joinR-gen (fst I) (λ i → A i j))
    right-pushCoh : (p : (ℓ₁ : fst I) (j : J) → A ℓ₁ j) → right-pushOut (λ i → p i (fst e i)) ≡ inrR λ j → inrR λ i → p i j
    left-right : (i' : fst I) (p : A i' (fst e i') × ((ℓ₁ : J) → A (notI i') ℓ₁))
      → left-pushOut (2-elter'.PushTop→left-push I J A (i' , inl (inr e , p))) ≡ right-pushOut (elimI i' (fst p) (snd p (fst e (notI i'))))
    fat-pushᵣ : (i' : fst I) (p : (ℓ₁ : fst I) (j : J) → A ℓ₁ j)
      → Square (λ i₁ → left-pushOut (PushTop→left-push (i' , push (inr e , p) i₁)))
               ((λ j → right-pushOut (elimIη (λ i'' → p i'' (fst e i'')) i' j)) ∙ right-pushCoh p)
                (left-right i' (p i' (fst e i') , p (notI i')))
                (fatᵣ i' (fst e i') p)

open inl-case

ΠR-extendOut-full : ∀ {ℓ} (I : RP∞' ℓ)
  → (e : (J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) → ΠR-extendOut-inl I (fst J) A)
  → ((J : RP∞' ℓ) (p : fst I ≃ fst J) (A : fst I → fst J → Type ℓ)
    → ΠR-extendOut-inr I (fst J) p A (ΠR-extendOut-inl.left-pushOut (e J A)) (ΠR-extendOut-inl.fatᵣ (e J A)))
  → (J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
  → 2-elter'.ΠR-extend I (fst J) A
  → joinR-gen (fst J) (λ j → joinR-gen (fst I) (λ i → A i j)) 
ΠR-extendOut-full I indl indr J A = F
  where
  open ΠR-extendOut-inl
  open ΠR-extendOut-inr
  r : ΠR-extendOut-inl I (fst J) A
  r = indl _ A

  ΠR-baseM : 2-elter'.ΠR-base I (fst J) A → joinR-gen (fst J) (λ j → joinR-gen (fst I) (λ i → A i j))
  ΠR-baseM (inl (inl x , p)) = ΠROut-inlₗ r x p
  ΠR-baseM (inl (inr x , p)) = right-pushOut {e = x} (indr J x A) p
  ΠR-baseM (inr x) = inrR λ j → inrR λ i → x i j
  ΠR-baseM (push (inl x , p) i) = ΠROut-push r x p i
  ΠR-baseM (push (inr x , p) i) = right-pushCoh (indr _ x A) p i

  F : 2-elter'.ΠR-extend I (fst J) A → joinR-gen (fst J) (λ j → joinR-gen (fst I) (λ i → A i j))
  F (inl x) = left-pushOut r x
  F (inr x) = ΠR-baseM x
  F (push (i' , inl (inl x , p)) i) = fatₗₗ r i' x p i 
  F (push (i' , inl (inr x , p)) i) = left-right (indr J x A) i' p i
  F (push (i' , inr (f , p)) i) = fatᵣ r i' f p i 
  F (push (i' , push (inl x , p) i₁) i) =
    hcomp (λ k → λ {(i = i0) → left-pushOut r (2-elter'.PushTop→left-push I (fst J) A (i' , push (inl x , p) i₁))
                      ; (i = i1) → cong-∙ ΠR-baseM (λ i₁ → inl ((inl x) , (2-elter'.elimIη I (fst J) A (λ i'' → p i'' x) i' i₁)))
                                           (push (inl x , p)) (~ k) i₁
                      ; (i₁ = i0) → fatₗₗ r i' x (p i' x , p _) i
                      ; (i₁ = i1) → fatᵣ r i' x p i
                      })
            (fat-pushₗ r i' x p i i₁)
  F (push (i' , push (inr x , p) i₁) i) =
          hcomp (λ k → λ {(i = i0) → left-pushOut r (2-elter'.PushTop→left-push I (fst J) A (i' , push (inr x , p) i₁))
                      ; (i = i1) → cong-∙ ΠR-baseM (λ i → inl ((inr x) , (2-elter'.elimIη I (fst J) A (λ i'' → p i'' (fst x i'')) i' i))) (push (inr x , p)) (~ k) i₁
                      ; (i₁ = i0) → left-right (indr J x A) i' (p i' (fst x i') , p _) i
                      ; (i₁ = i1) → fatᵣ r i' (fst x i') p i})
            (fat-pushᵣ (indr J x A) i' p i i₁)

ΠR-extendOut-full* : ∀ {ℓ} (I : RP∞' ℓ)
  → (e : (J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) → ΠR-extendOut-inl I (fst J) A)
  → ((A : fst I → fst I → Type ℓ)
    → ΠR-extendOut-inr I (fst I) (idEquiv (fst I)) A
        (ΠR-extendOut-inl.left-pushOut (e I A))
        (ΠR-extendOut-inl.fatᵣ (e I A)))
  → (J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
  → 2-elter'.ΠR-extend I (fst J) A
  → joinR-gen (fst J) (λ j → joinR-gen (fst I) (λ i → A i j))
ΠR-extendOut-full* I e ind  = ΠR-extendOut-full I e (JRP∞'' I ind)

ΠR-extendOut-full-lets : ∀ {ℓ} (I J : RP∞' ℓ)
  (A : fst I → fst J → Type ℓ)
  → 2-elter'.ΠR-extend I (fst J) A → joinR-gen (fst J) (λ j → joinR-gen (fst I) (λ i → A i j))
ΠR-extendOut-full-lets {ℓ} I = ΠR-extendOut-full* I F1 F2
  where
  module _ (J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) where
    open ΠR-extendOut-inl
    module M = 2-elter' I (fst J) A
    open M
    F1 : ΠR-extendOut-inl I (fst J) A
    left-pushOut F1 (i , p) = inlR (fst p .fst , inrR (elimI i (fst p .snd) (snd p (fst p .fst))))
    ΠROut-inlₗ F1 j p = inlR (j , inrR p)
    ΠROut-push F1 j g i = push* (j , inrR (λ i₁ → g i₁ j)) (λ i₁ → inrR (λ i₂ → g i₂ i₁)) refl i
    fatₗₗ F1 i' x (a , p) = refl
    fatᵣ F1 i' x p = push* (x , inrR (elimI i' (p i' x) (p (notI i') x))) (λ j → inrR λ i → p i j) (cong inrR (sym (elimIη (λ i → p i x) i')))
    fat-pushₗ F1 i' x p i j =
      hcomp (λ k → λ {(i = i0) → inlR (x , (inrR (elimIη (λ i₁ → p i₁ x) i' (~ k ∧ j))))
                     ; (i = i1) → (((λ i → inlR (x , inrR (elimIη (λ i → p i x) i' i)))) ∙ (push* (x , inrR (λ i → p i x)) _ refl)) j
                     ; (j = i0) → inlR (x , (inrR (elimI i' (p i' x) (p (notI i') x))))
                     ; (j = i1) → push* (x , inrR (elimIη (λ i → p i x) i' (~ k)))
                                         (λ j → inrR λ i → p i j)
                                         (λ i → inrR (elimIη (λ i₂ → p i₂ x) i' (~ k ∨ ~ i))) i})
            (compPath-filler (λ i → inlR (x , inrR (elimIη (λ i → p i x) i' i))) (push* (x , inrR (λ i → p i x)) _ refl) i j)
  
  module _ (A : fst I → fst I → Type ℓ) where
    open ΠR-extendOut-inr
    open 2-elter' I (fst I) A
    F2 : ΠR-extendOut-inr I (fst I) (idEquiv (fst I)) A (ΠR-extendOut-inl.left-pushOut (F1 I A) ) (ΠR-extendOut-inl.fatᵣ (F1 I A))
    right-pushOut F2 f = inrR λ i → inlR (i , f i)
    right-pushCoh F2 p = cong inrR (funExt λ i → push* (i , p i i) (λ i' → p i' i) refl)
    left-right F2 i' (a , b) = push* (i' , (inrR (elimI i' a (b i'))))
                                     (λ i → inlR (i , elimI {B = λ x → A x x} i' a (b (notI i')) i))
                                     (push* (i' , elimI {B = λ x → A x x} i' a (b (notI i')) i')
                                             (elimI i' a (b i'))
                                             (elimIβ {B = λ x → A x i'} i' a (b i') .fst
                                           ∙ sym (elimIβ {B = λ x → A x x} i' a (b (notI i')) .fst)))
    fat-pushᵣ F2 i' p i j =
     hcomp (λ k → λ {(i = i0) → inlR (i' , (inrR (elimI i' (p i' i') (p (notI i') i'))))
                     ; (i = i1) → ((λ i → inrR λ i* → inlR (i* , elimIη (λ x → p x x) i' i i*))
                                   ∙ λ i → inrR λ i₂ → push* (i₂ , p i₂ i₂) (λ i → p i i₂) refl i) j
                     ; (j = i0) → push* (i' , (inrR (elimI i' (p i' i') (p (notI i') i'))))
                                         (λ i* → inlR (i* , elimI {B = λ x → A x x} i' (p i' i') (p _ _) i*))
                                         (push* (i' , (elimI {B = λ x → A x x} i' (p i' i') (p _ _) i'))
                                                (elimI i' (p i' i') (p _ i'))
                                                (elimIη-id (λ x → p x i') i' .fst k
                                               ∙ sym (elimIη-id (λ x → p x x) i' .fst k))) i
                     ; (j = i1) → push* (i' , inrR (elimI i' (p i' i') (p (notI i') i')))
                                         (λ i → inrR (λ j → p j i))
                                         (cong inrR (sym (elimIη (λ i₂ → p i₂ (idfun (fst I) i')) i'))) i})
        (hcomp (λ k → λ {(i = i0) → inlR (i' , (inrR (elimIη (λ x → p x i') i' (~ k))))
                     ; (i = i1) → compPath-filler'
                                    (λ i → inrR λ i* → inlR (i* , elimIη (λ x → p x x) i' i i*))
                                    (λ i → inrR λ i₂ → push* (i₂ , p i₂ i₂) (λ i → p i i₂) refl i) k j
                     ; (j = i0) → push* (i' , inrR (elimIη (λ x → p x i') i' (~ k)))
                                        (λ i* → inlR (i* , (elimIη (λ x → p x x) i' (~ k) i*)))
                                        (push* (i' , elimIη (λ x → p x x) i' (~ k) i')
                                               (elimIη (λ x → p x i') i' (~ k))
                                               (compPath-filler (λ j → elimIη (λ x → p x i') i' (~ k ∨ j) i')
                                                (λ j → elimIη (λ x → p x x) i' (~ j) i') k)) i
                     ; (j = i1) → push* (i' , inrR (elimIη (λ x → p x i') i' (~ k)))
                                         (λ i → inrR (λ j → p j i))
                                         (cong inrR λ i₁ → elimIη (λ i₂ → p i₂ (idfun (fst I) i')) i' (~ i₁ ∨ ~ k)) i})
               (push* (i' , inrR (λ j → p j i')) (λ i* → push* (i* , p i* i*) (λ j → p j i*) refl j)
                 (λ i → push* (i' , p i' i') (λ j₁ → p j₁ i') refl (i ∨ j) ) i))

{-

module 2-elter* {ℓ : Level} (I : RP∞ ℓ) (J : Type) (A : fst I → J → Type ℓ) (I2 : ∀ {ℓ} → is2Type ℓ (fst I))  where
  private
    module M = 2-elter' I J A I2
    open M

  module _ (left-pushOut* : left-push → joinR-gen J (λ j → joinR I (λ i → A i j)))
             (ΠROut-inlₗ : (j : J) (g : (i : fst I) → A i j) → joinR-gen J (λ j → joinR I (λ i → A i j)))
             (ΠROut-push : (j : J) (g : ((i : fst I) (j : J) → A i j)) → ΠROut-inlₗ j (λ i → g i j) ≡ (inrR λ j → inrR λ i → g i j))
             (fatₗₗ : (i' : fst I) (x : J) (p : A i' x × ((j : J) → A (notI i') j))
               → left-pushOut* (PushTop→left-push (i' , inl (inl x , p))) ≡ ΠROut-inlₗ x (elimI i' (fst p) (snd p x)))
             (fatᵣ : (i' : fst I) (x : J) (p : (i : fst I) (j : J) → A i j)
               → left-pushOut* (i' , PushTop→left-push' i' (inr (x , p))) ≡ (inrR λ j → inrR λ i → p i j))
             (fat-pushₗ : (i' : fst I) (x : J) (p : (i : fst I) (j : J) → A i j)
               → Square (λ j → left-pushOut* (PushTop→left-push (i' , push (inl x , p) j)))
                         (cong (ΠROut-inlₗ x) (elimIη (λ i → p i x) i') ∙ ΠROut-push x p)
                         (fatₗₗ i' x (p i' x , p (notI i')))
                         (fatᵣ i' x p))
             (right-pushOut : (e : fst I ≃ J) → ((ℓ₁ : fst I) → A ℓ₁ (fst e ℓ₁)) → joinR-gen J (λ j → joinR I (λ i → A i j)))
             (right-pushCoh : (e : fst I ≃ J)  (p : (ℓ₁ : fst I) (j : J) → A ℓ₁ j) → right-pushOut e (λ i → p i (fst e i)) ≡ inrR λ j → inrR λ i → p i j)
             (left-right : (i' : fst I) (e : fst I ≃ J) (p : A i' (fst e i') × ((ℓ₁ : J) → A (notI i') ℓ₁))
               → left-pushOut* (PushTop→left-push (i' , inl (inr e , p))) ≡ right-pushOut e (elimI i' (fst p) (snd p (fst e (fst I2 i')))))
             (fat-pushᵣ : (i' : fst I) (e : fst I ≃ J) (p : (ℓ₁ : fst I) (j : J) → A ℓ₁ j)
               → Square (λ i₁ → left-pushOut* (PushTop→left-push (i' , push (inr e , p) i₁)))
                         ((λ j → right-pushOut e (elimIη (λ i'' → p i'' (fst e i'')) i' j)) ∙ right-pushCoh e p)
                         (left-right i' e (p i' (fst e i') , p (notI i')))
                         (fatᵣ i' (fst e i') p))
             where
  

    ΠR-baseM : ΠR-base →  joinR-gen J (λ j → joinR I (λ i → A i j))
    ΠR-baseM (inl (inl x , p)) = ΠROut-inlₗ x p
    ΠR-baseM (inl (inr x , p)) = right-pushOut x p
    ΠR-baseM (inr x) = inrR λ j → inrR λ i → x i j
    ΠR-baseM (push (inl x , p) i) = ΠROut-push x p i
    ΠR-baseM (push (inr x , p) i) = right-pushCoh x p i

    pash : (x : _) → Path ΠR-extend _ _
    pash = push

    ΠR-base→double : ΠR-extend → joinR-gen J λ j → joinR I (λ i → A i j)
    ΠR-base→double (inl x) = left-pushOut* x
    ΠR-base→double (inr x) = ΠR-baseM x
    ΠR-base→double (push (i' , inl (inl x , p)) i) = fatₗₗ i' x p i
    ΠR-base→double (push (i' , inl (inr x , p)) i) = left-right i' x p i
    ΠR-base→double (push (i' , inr (j , p)) i) = fatᵣ i' j p i
    ΠR-base→double (push (i' , push (inl x , p) i₁) i) =
      hcomp (λ k → λ {(i = i0) → left-pushOut* (PushTop→left-push (i' , push (inl x , p) i₁))
                      ; (i = i1) → cong-∙ ΠR-baseM (λ i₁ → inl (inl x , elimIη (λ i'' → p i'' (eval (inl x) i'')) i' i₁)) (push (inl x , p)) (~ k) i₁
                      ; (i₁ = i0) → fatₗₗ i' x (p i' x , p (notI i')) i
                      ; (i₁ = i1) → fatᵣ i' x p i})
            (fat-pushₗ i' x p i i₁)
    ΠR-base→double (push (i' , push (inr x , p) i₁) i) =
      hcomp (λ k → λ {(i = i0) → left-pushOut* (PushTop→left-push (i' , push (inr x , p) i₁))
                      ; (i = i1) → cong-∙ ΠR-baseM (λ i → inl ((inr x) , (elimIη (λ i'' → p i'' (eval (inr x) i'')) i' i))) (push (inr x , p)) (~ k) i₁
                      ; (i₁ = i0) → left-right i' x (p i' (fst x i') , p (notI i')) i
                      ; (i₁ = i1) → fatᵣ i' (fst x i') p i})
            (fat-pushᵣ i' x p i i₁)



{-





  pre-eqvl-not : (i' : I) (p : Pushout (fat→ₗ i') (fat→ᵣ i'))
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


  eqvl : (a : PushTop) (i : I)
    → ΠR-extend→Πₗ (PushTop→left-push a) i
     ≡ ΠR-base→ (PushTop→ΠR-base a) i
  eqvl (i' , p) =
    elimI i' (pre-eqvl-diag i' p)
                 (pre-eqvl-not i' p)

  ΠR-extend→Π : ΠR-extend → TotΠ (λ i → joinR-gen J (A i))
  ΠR-extend→Π (inl t) = ΠR-extend→Πₗ t
  ΠR-extend→Π (inr x) = ΠR-base→ x
  ΠR-extend→Π (push a i) i' = eqvl a i' i

-}



-}

{-
module BoolCase {ℓ : Level} (J : Type) (A : Bool → J → Type ℓ) where
  Iso1 : Iso (Σ[ f ∈ (Σ[ j ∈ J ] (A true j)) × (Σ[ j ∈ J ] (A false j)) ]
               Σ[ g ∈ ((i : Bool) (j : J) → A i j) ] (g true (f .fst .fst) ≡ snd (fst f))
                                                 × (g false (f .snd .fst) ≡ snd (snd f)))
             (Σ[ f ∈ (TotΠ λ i → Σ[ j ∈ J ] (A i j)) ]
      (Σ[ g ∈ ((i : Bool) (j : J) → A i j) ] ((i : Bool) → g i (f i .fst) ≡ f i .snd)))
  Iso.fun Iso1 ((f1 , f2) , g , g1 , g2) = (CasesBool true f1 f2) , (g , (CasesBool true g1 g2))
  Iso.inv Iso1 (f , g , p) = ((f true) , (f false)) , (g , (p true , p false))
  Iso.rightInv Iso1 (f , g , p) =
    ΣPathP (CasesBoolη f
     , ΣPathP (refl , funTypePP (CasesBool true refl refl)))
  Iso.leftInv Iso1 (f , g , p) = refl

  ΠR-baseBool* : Type _
  ΠR-baseBool* =
    Pushout {A = J × J × (((j : J) → A true j × A false j))}
            {B = (Σ[ j ∈ J ] (A true j)) × (Σ[ j ∈ J ] (A false j))}
                    {C = (j : J) → A true j × A false j}
            (λ abc → (fst abc , snd (snd abc) _ .fst)
                     , fst (snd abc) , snd (snd abc) _ .snd)
            λ abc → snd (snd abc)

  ΠR-baseBool : Type _
  ΠR-baseBool =
    Pushout {A = Σ[ f ∈ (Σ[ j ∈ J ] (A true j)) × (Σ[ j ∈ J ] (A false j)) ]
            Σ[ g ∈ ((i : Bool) (j : J) → A i j) ] (g true (f .fst .fst) ≡ snd (fst f))
                                                 × (g false (f .snd .fst) ≡ snd (snd f))}
            {B = (Σ[ j ∈ J ] (A true j)) × (Σ[ j ∈ J ] (A false j))}
                    {C = (j : J) → A true j × A false j}
      fst
      λ x j → (x .snd .fst true j) , (x .snd .fst false j)

  Iso2 : Iso ΠR-baseBool* ΠR-baseBool
  Iso.fun Iso2 (inl (a , b)) = inl (a , b)
  Iso.fun Iso2 (inr x) = inr x
  Iso.fun Iso2 (push (a , b , c) i) =
    push (((a , c a .fst) , (b , c b .snd)) , ((CasesBool true (fst ∘ c) (snd ∘ c )) , (refl , refl))) i
  Iso.inv Iso2 (inl (a , b)) = inl (a , b)
  Iso.inv Iso2 (inr x) = inr x
  Iso.inv Iso2 (push (a , b , c) i) =
    ((λ i → inl (((fst (fst a)) , (c .fst (~ i))) , (fst (snd a) , c .snd (~ i)))) ∙ push (fst (fst a) , (fst (snd a)) , (λ j → b true j , b false j))) i
  Iso.rightInv Iso2 (inl x) = refl
  Iso.rightInv Iso2 (inr x) = refl
  Iso.rightInv Iso2 (push a i) = {!!}
  Iso.leftInv Iso2 = {!!}

  ΠR-baseBoolIso' : Iso ΠR-baseBool (2-elter.ΠR-base ? J A (Bool-2Type _))
  ΠR-baseBoolIso' = pushoutIso _ _ _ _
    (isoToEquiv Iso1)
    (isoToEquiv (invIso ΠBool×Iso))
    (isoToEquiv (compIso →×Iso (invIso ΠBool×Iso)))
    refl
    (funExt λ x → funExt (CasesBool true refl refl))

  highη : (f : TotΠ (λ i₁ → Σ-syntax J (A i₁))) (p : (i₁ : Bool) (j₁ : J) → A i₁ j₁)
    (q : (i₁ : Bool) → p i₁ (f i₁ .fst) ≡ f i₁ .snd)
    → PathP (λ i → (i₁ : Bool) → CasesBoolη p i i₁ (CasesBoolη f i i₁ .fst) ≡ CasesBoolη f i i₁ .snd)
             (CasesBool true (q true) (q false))
             q
  highη f p q i false = q false
  highη f p q i true = q true

  ΠR-baseBoolIso : Iso ΠR-baseBool (2-elter.ΠR-base Bool J A (Bool-2Type _))
  Iso.fun ΠR-baseBoolIso (inl (a , b)) = inl (CasesBool true a b)
  Iso.fun ΠR-baseBoolIso (inr x) = inr (CasesBool true (λ j → x j .fst ) λ j → x j .snd )
  Iso.fun ΠR-baseBoolIso (push a i) =
    push ((CasesBool {A = λ i₁ →  Σ-syntax J (A i₁)} true (fst (fst a)) (snd (fst a)))
       , (CasesBool true (a .snd .fst true) (a .snd .fst false))
       , CasesBool true (snd (snd a) .fst) (snd (snd a) .snd)) i
  Iso.inv ΠR-baseBoolIso (inl x) = inl ((x true) , (x false))
  Iso.inv ΠR-baseBoolIso (inr x) = inr λ j → x true j , x false j
  Iso.inv ΠR-baseBoolIso (push a i) =
    push (((fst a true) , (fst a false)) , ((snd a .fst) , ((snd a .snd true) , (snd a .snd false)))) i
  Iso.rightInv ΠR-baseBoolIso (inl x) i = inl (CasesBoolη x i)
  Iso.rightInv ΠR-baseBoolIso (inr x) i = inr (CasesBoolη x i)
  Iso.rightInv ΠR-baseBoolIso (push (f , p , q) j) i = push (CasesBoolη f i , (CasesBoolη p i) , highη f p q i) j
  Iso.leftInv ΠR-baseBoolIso (inl (a , b)) = refl
  Iso.leftInv ΠR-baseBoolIso (inr x) = refl
  Iso.leftInv ΠR-baseBoolIso (push (f , p , q , r) i) j = push (f , CasesBoolη p j , q , r) i

    {-
      (Σ[ g ∈ ((i : I) (j : J) → A i j) ] ((i : I) → g i (f i .fst) ≡ f i .snd))}
                    {B = TotΠ λ i → Σ[ j ∈ J ] (A i j)}
                    {C = (i : I) (j : J) → A i j}
                    fst
                    (fst ∘ snd)

-}

-}
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


{-
×→ΠR-extend : ∀ {ℓ} (A : Bool → Bool → Type ℓ)
  → joinR Bool* (A true) × joinR Bool* (A false)
  → 2-elter.ΠR-extend Bool Bool A (Bool-2Type _)
×→ΠR-extend A (inlR x , inlR y) = inr (inl (CasesBool true x y))
×→ΠR-extend A (inlR (x , b) , inrR x₁) = inl (true , ((_ , b) , x₁))
×→ΠR-extend A (inlR (a , b) , push* (a' , d) c x₁ i) = push (true , inl ((CasesBool true (a , b) (a' , d)) , c , x₁)) (~ i)
×→ΠR-extend A (inrR x , inlR (a , b)) = inl (false , ((a , b) , x))
×→ΠR-extend A (inrR x , inrR x₁) = inr (inr (CasesBool true x x₁))
×→ΠR-extend A (inrR x , push* (a , b) c x₁ i) =
  push (false , (inr ((a , b) , ((CasesBool true x c) , x₁)))) i
×→ΠR-extend A (push* (a , b) c x i , inlR (a' , b')) =
  push (false , inl ((CasesBool true (a , b) (a' , b')) , (c , x))) (~ i)
×→ΠR-extend A (push* (a' , b) c x i , inrR x₁) =
  push (true , inr ((_ , b) , (CasesBool true c x₁ , x))) i
×→ΠR-extend A (push* (a , b) c x i , push* (a' , b₁) c₁ d i₁) = fill₂ A a a' b b₁ c c₁ x d i i₁ i1
-}

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

ΠR-extend→Π-equiv-base : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
  → isEquiv (2-elter.ΠR-extend→Π (RP∞'· ℓ) (fst J) A)
ΠR-extend→Π-equiv-base {ℓ} J A = transport (λ i → isEquiv (p i)) isEq
  where
  p : ΠR-extend→Π-alt J A ≡ 2-elter.ΠR-extend→Π (RP∞'· ℓ) (fst J) A
  p = funExt λ x → funExt (ΠR-extend→Π-alt≡ {J = J} A x)

  alt : (2-elter.ΠR-extend (RP∞'· ℓ) (fst J) A) ≃ ((x : Bool) → joinR-gen (fst J) (A x))
  alt = isoToEquiv (compIso (ΠR-extend→×Iso J A) (invIso ΠBool×Iso))

  altid : fst alt ≡ ΠR-extend→Π-alt J A
  altid = funExt λ x → funExt (CasesBool true refl refl)

  isEq : isEquiv (ΠR-extend→Π-alt J A)
  isEq = subst isEquiv altid (snd alt)

-- ΠR-extend→Π-equiv : ∀ {ℓ} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
--   → isEquiv (2-elter.ΠR-extend→Π I (fst J) A)
-- ΠR-extend→Π-equiv {ℓ} =
--   RP∞'pt→Prop (λ _ → isPropΠ2 λ _ _ → isPropIsEquiv _)
--     λ J A → transport (λ i → isEquiv (2-elter.ΠR-extend→Π (RP∞'· ℓ) (fst J) A (2Type≡ (~ i))))
--       (ΠR-extend→Π-equiv-base J A)

-- module _ {ℓ : Level} (I J : RP∞) (A : fst I → fst J → Type ℓ) where
--   module M = 2-elter {ℓ} (fst I) (fst J) A (RP∞-2Type _ I)
--   open M
--   GOAL = joinRD J I (λ a b → A b a)
--   asd : Σ[ p ∈ (fst J ⊎ (fst I ≃ fst J)) ] ((i : fst I) → A i (fst (2-eltFun {I = I} {J = J}) p i)) → GOAL
--   asd (inl x , p) = inlR (x , inrR p)
--   asd (inr x , p) = inrR λ j → inlR ((invEq x j) , (subst (A (invEq x j)) (secEq x j) (p (invEq x j))))

--   asd-coh : (d : Σ[ p ∈ (fst J ⊎ (fst I ≃ fst J)) ]
--                   ((i : fst I) → A i (fst (2-eltFun {I = I} {J = J}) p i)))

--             (p : (i₁ : fst I) (j : fst J) → A i₁ j)
--             (q : (i₁ : fst I) → p i₁ (2-eltFun {I = I} {J = J} .fst (d .fst) i₁) ≡ d .snd i₁)
--       → asd d ≡ inrR λ j → inrR λ i → p i j
--   asd-coh d p q = {!!}

--   open import Cubical.HITs.Pushout as PU
--   private
--     2-eltFun* = 2-eltFun {I = I} {J = J}

--   ΠR-base→Goalₗ : (x : fst J ⊎ (fst I ≃ fst J))
--       (g : (a : fst I) → A a (fst 2-eltFun* x a)) →
--       GOAL
--   ΠR-base→Goalₗ (inl x) g = inlR (x , inrR g)
--   ΠR-base→Goalₗ (inr x) g = inrR λ j → inlR ((invEq x j) , {!curry ?!})

--   ΠR-base→J→Goal : ΠR-base → GOAL
--   ΠR-base→J→Goal = elimPushout
--     (uncurryΠ (2-eltFun-elim {I = I} {J = J} (curry asd)))
--     (λ q → inrR λ j → inrR λ i → q i j)
--     (uncurry (uncurryΠ (2-eltFun-elim {I = I} {J = J} λ x g y → {!!} ∙ asd-coh (x , g) (fst y) (snd y))))


--   left-push→J : dable → GOAL
--   left-push→J (inl x) = {!x!}
--   left-push→J (inr x) = {!!}
--   left-push→J (push a i) = {!!}

--   ΠR-base→J : ΠR-base → GOAL
--   ΠR-base→J (inl f) = asd (Iso.fun (TotAIso I J) f)
--   ΠR-base→J (inr x) = inrR λ i → inrR λ j → x j i
--   ΠR-base→J (push (f , p , q) i) = asd-coh (f1 I J f) p (cool (fst ∘ f) (snd ∘ f) (funExt q)) i
--     where
--     cool : (f1* : (a : fst I) → fst J)
--            (sf : (a : fst I) → A a (f1* a))
--          → (q : (λ i → p i (f1* i)) ≡ sf)
--          → (i₁ : fst I) → p i₁ (2-eltFun {I} {J} .fst (f1 I J {A = A} (λ i → f1* i , sf i) .fst) i₁)
--                          ≡ f1 I J {A = A} (λ i → f1* i , sf i) .snd i₁
--     cool f1* = J> λ j → {!!}



--   ΠR-extend-rec : ∀ {ℓ*} {B : Type ℓ*}
--     → (l : ΠR-base → B)
--     → ((i : fst I) → Σ[ g ∈ (Σ[ j ∈ fst J ] (A i j) × ((j : fst J) → A (notI i) j) → B) ]
--                         ((a : Pushout (fat→ₗ i) (fat→ᵣ i))
--                       → l (PushTop→ΠR-base (i , a))
--                        ≡ g ((PushTop→left-push (i , a) .snd) .fst .fst , (PushTop→left-push (i , a) .snd) .fst .snd , (PushTop→left-push (i , a) .snd) .snd)))
--     → (ΠR-extend → B)
--   ΠR-extend-rec l r (inl x) = r (fst x) .fst (snd x .fst .fst , (snd x .fst .snd) , (snd x .snd))
--   ΠR-extend-rec l r (inr x) = l x
--   ΠR-extend-rec l r (push (x , f) i) = r x .snd f (~ i)

--   dable-rec : ∀ {ℓ'} {B : Type ℓ'}
--     → (l : ΠR-base → B)
--     → ((i : fst I) → Σ[ left ∈ (joinR-gen (fst J) (A i) → B) ]
--                         Σ[ pf ∈ (Σ[ g ∈ (Σ[ j ∈ fst J ] (A i j) × ((j : fst J) → A (notI i) j) → B) ]
--                         ((a : Pushout (fat→ₗ i) (fat→ᵣ i))
--                       → l (PushTop→ΠR-base (i , a))
--                        ≡ g ((PushTop→left-push (i , a) .snd) .fst .fst , (PushTop→left-push (i , a) .snd) .fst .snd , (PushTop→left-push (i , a) .snd) .snd))) ]
--                           ((t : ΠR-extend) → {!!} ≡ {!!}))
--     → dable → B
--   dable-rec l f (inl x) = f (fst x) .fst (snd x)
--   dable-rec {B = B} l f (inr x) = ΠR-extend-rec {B = B} l (λ i → f i .snd .fst) x
--   dable-rec l f (push a i) = {!a!}


--   ΠR-extend→J : ΠR-extend → GOAL
--   ΠR-extend→J (inl x) = {!left-push!}
--   ΠR-extend→J (inr x) = ΠR-base→J  x
--   ΠR-extend→J (push (i' , a) i) = {!!}

-- {-
-- dable→ : Type _
-- dable→ = Pushout {A = I × ΠR-extend} {B = Σ[ i ∈ I ] joinR-gen J (A i)} {C = ΠR-extend}
--                 (λ a → fst a , ΠR-extend→Π (snd a) (fst a))
--                 snd
-- -}

