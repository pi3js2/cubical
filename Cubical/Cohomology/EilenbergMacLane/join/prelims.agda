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


module Cubical.Cohomology.EilenbergMacLane.join.prelims where
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

bitch-help2 : ∀ {ℓ} {A : Type ℓ} {x : A} (q : x ≡ x) (r : refl ≡ q)
  → Cube (λ _ _ → x) (λ i j → q i)
          (λ i j → r (~ j) (~ i)) (λ _ _ → x)
          (λ i r → q (~ i ∨ r)) r
bitch-help2 = J> refl

bitch-help : ∀ {ℓ} {A : Type ℓ} {x : A} (y : A) (p : x ≡ y)
    (z : A) (q : y ≡ z)
  → Cube {A = A}
       (λ r j → q (r ∨ ~ j)) (λ i _ → (p ∙ q) i)
       (λ i j → compPath-filler p q (~ j) (~ i)) (λ _ _ → z)
       (λ i r → (p ∙ q) (~ i ∨ r)) (compPath-filler' p q )
bitch-help {x = x} = J> (J> bitch-help2 _ (rUnit (refl {x = x})))

bitch-help' : ∀ {ℓ} {A : Type ℓ} {x : A} (y : A) (p : x ≡ y)
    (z : A) (q : y ≡ z)
  → Cube {A = A}
         (λ i j → q (i ∧ ~ j)) (λ i' j → compPath-filler p q (~ j) i')
         (λ j _ → p (~ j)) (λ i j → q (~ j))
         (compPath-filler' p q)
         λ i j → p (~ i ∨ j)
bitch-help' {x = x} = J> (J> λ i j k → compPath-filler (refl {x = x}) refl (~ k ∧ i) j)

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
CasesBoolη f = funExt (CasesBool true refl refl)

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

join-gen : ∀ {ℓ ℓ'} (I : Type ℓ) (A : I → Type ℓ') → Type _
join-gen I A = Pushout {A = I × TotΠ A} {B = Σ I A} (λ a → fst a , snd a (fst a)) snd

join-gen-ind : ∀ {ℓ ℓ' ℓ''} {I : Type ℓ} {A : I → Type ℓ'} {B : join-gen I A → Type ℓ''}
  → (f : (g : TotΠ A) → B (inr g))
  → ((i : I) → Σ[ g ∈ ((x : A i) → B (inl (i , x))) ]
      ((t : TotΠ A) → PathP (λ j → B (push (i , t) j)) (g (t i)) (f t)))
  → (x : _) → B x
join-gen-ind f g (inl x) = g (fst x) .fst (snd x)
join-gen-ind f g (inr x) = f x
join-gen-ind f g (push a j) = g (fst a) .snd (snd a) j

module _ {ℓ ℓ'} (I : Type ℓ) (A : I → Type ℓ') where
  private
    F : joinR-gen I A → join-gen I A
    F (inlR x) = inl x
    F (inrR x) = inr x
    F (push* a b x i) = ((λ j → inl (fst a , x (~ j))) ∙ push (fst a , b)) i

    G : join-gen I A → joinR-gen I A
    G (inl x) = inlR x
    G (inr x) = inrR x
    G (push a i) = push* (fst a , snd a (fst a)) (snd a) refl i

    FGF : (x : _) → F (G x) ≡ x
    FGF (inl x) = refl
    FGF (inr x) = refl
    FGF (push a i) j = lUnit (push (fst a , snd a)) (~ j) i

    GFG : (x : _) → G (F x) ≡ x
    GFG (inlR x) = refl
    GFG (inrR x) = refl
    GFG (push* a b x i) j = help j i
      where
      help : cong G (((λ j → inl (fst a , x (~ j))) ∙ push (fst a , b)))
           ≡ push* a b x
      help = cong-∙ G (λ j → inl (fst a , x (~ j))) (push (fst a , b))
           ∙ (λ k → (λ j → inlR (fst a , x (~ j ∨ k))) ∙ push* (fst a , x k) b λ i → x (i ∧ k))
           ∙ sym (lUnit _)

  join-gen-Iso : Iso (joinR-gen I A) (join-gen I A)
  Iso.fun join-gen-Iso = F
  Iso.inv join-gen-Iso = G
  Iso.rightInv join-gen-Iso = FGF
  Iso.leftInv join-gen-Iso = GFG

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



module GetProps {ℓ} (X : RP∞' ℓ) where
  2not : fst X → fst X
  2not = snd X .fst .fst

  2elim : ∀ {B : fst X → Type ℓ} (x : fst X) → B x → B (2not x) → (x' : fst X) → B x'
  2elim  {B = B} = snd X .fst .snd .snd B .fst

  2elimβ : ∀ {B : fst X → Type ℓ} (x : fst X) (a : B x) (b : B (2not x))
    → (2elim {B = B} x a b x ≡ a) × (2elim {B = B} x a b (2not x) ≡ b)
  2elimβ {B = B} x a b = snd X .fst .snd .snd B .snd x a b

  PickOne : (A : fst X → Pointed ℓ)
          → Σ[ x ∈ fst X ] A x .fst
          → (x : fst X) → A x .fst
  PickOne A (x , a) = 2elim x a (A (2not x) .snd)

  PickOneConst : (A : fst X → Pointed ℓ) (x : fst X)
    → PickOne A (x , A x .snd) ≡ λ x → A x .snd
  PickOneConst A x =
    funExt (2elim x (2elimβ x (A x .snd) (A (2not x) .snd) .fst) (2elimβ x (A x .snd) (A (2not x) .snd) .snd))

  2Smash : (A : fst X → Pointed ℓ) → Type ℓ
  2Smash A = Pushout fst (PickOne A)

  2Smash∙ : (A : fst X → Pointed ℓ) → Pointed ℓ
  fst (2Smash∙ A) = 2Smash A
  snd (2Smash∙ A) = inr (λ x → A x .snd)

  isBiHom : (A : fst X → Pointed ℓ) (B : Pointed ℓ) → (TotΠ (fst ∘ A) → fst B) → Type ℓ
  isBiHom A B g =
      Σ[ f ∈ ((x : fst X) → fst B) ]
        Σ[ gf ∈ ((x : fst X) (y : fst (A x)) → g (PickOne A (x , y)) ≡ f x) ]
          g (λ x → A x .snd) ≡ snd B

  BiHom : (A : fst X → Pointed ℓ) (B : Pointed ℓ) → Type ℓ
  BiHom A B = Σ[ g ∈ _ ] isBiHom A B g

Ben : ℕ → Σ[ X ∈ (RP∞' ℓ-zero) ] (fst X → ℕ)
Ben n = (RP∞'· ℓ-zero) , (λ _ → n)

isEqBen : Σ[ X ∈ (RP∞' ℓ-zero) ] (fst X → ℕ) → ℕ
isEqBen (X , p) = {!!}
  where
  0RP = RP∞'· ℓ-zero
  isRP : (X Y : RP∞' ℓ-zero) → isRP∞ ℓ-zero (fst X ≃ fst Y)
  isRP = {!!}

  _+RP_ : (X Y : RP∞' ℓ-zero) → RP∞' ℓ-zero
  X +RP Y = (fst X ≃ fst Y) , isRP X Y

  ++RP : (X : RP∞' ℓ-zero) → X +RP X ≡ 0RP
  ++RP = {!!}

  +RP-assoc : (X Y Z : RP∞' ℓ-zero) → X +RP (Y +RP Z) ≡ (X +RP Y) +RP Z 
  +RP-assoc = {!!}

  +RP-rid : (X : RP∞' ℓ-zero) → X +RP 0RP ≡ X 
  +RP-rid = {!!}

  +RP-lid : (X : RP∞' ℓ-zero) → 0RP +RP X ≡ X 
  +RP-lid = {!!}

  +Iso : (X : RP∞' ℓ-zero) → Iso (RP∞' ℓ-zero) (RP∞' ℓ-zero)
  Iso.fun (+Iso X) = X +RP_
  Iso.inv (+Iso X) = X +RP_
  Iso.rightInv (+Iso X) Y = +RP-assoc X X Y ∙ cong (_+RP Y) (++RP X) ∙ +RP-lid Y
  Iso.leftInv (+Iso X) Y = +RP-assoc X X Y ∙ cong (_+RP Y) (++RP X) ∙ +RP-lid Y
  

  ta : Iso (RP∞' ℓ-zero) (RP∞' ℓ-zero)
  ta = +Iso X

  PP : Iso (Σ[ X ∈ (RP∞' ℓ-zero) ] (fst X → ℕ)) (Σ[ X ∈ (RP∞' ℓ-zero) ] (Bool → ℕ))
  PP = compIso (invIso (Σ-cong-iso-fst ta))
         (Σ-cong-iso-snd λ Y → pathToIso ((λ j → {!fst X ≃ fst Y!} → ℕ) ∙ {!!}))


-- QT : (A B D : Pointed₀) (C : Type)
--   → (isHom : isHomogeneous B)
--   → (incl : D →∙ A)
--   → ∥ C ∥₁
--   → isEquiv {A = A →∙ B} {B = C → A →∙ B} (λ f _ → f)
--    → (f g : A →∙ B)
--    → ((d : fst D) (c : C) → fst f (fst incl d) ≡ fst g (fst incl d))
--    → ((d : fst D) → fst f (fst incl d) ≡ fst g (fst incl d))
-- QT A B D C h cpt incl isEq f g ind d = {!ind -- invEq (_ , isEq) !}
--   where
--   help : Iso (D →∙ A) {!!}
--   help = {!!}


-- open import Cubical.ZCohomology.Base
-- open import Cubical.ZCohomology.Properties
-- open import Cubical.ZCohomology.GroupStructure as GS


-- 2Smash∙→Hom+ₗ :
--   (X : RP∞' ℓ-zero) (n : ℕ) (A : fst X → Pointed₀)
--   → ((x : fst X) → A x .fst)
--   → (f :  ((x : fst X) → A x .fst) → coHomK (2 + n))
--   → (fb : GetProps.isBiHom X A (coHomK-ptd (2 + n)) f) 
--   → singl (GS.0ₖ (2 + n)) × singl (GS.0ₖ (2 + n))
-- 2Smash∙→Hom+ₗ =
--   RP∞'pt→Prop (λ _ → isPropΠ4 λ _ _ _ _ → isPropΠ λ _ → isProp× (isContr→isProp (isContrSingl _ )) (isContr→isProp (isContrSingl _ )))
--     λ n A g f fb → ((f (GetProps.2elim (RP∞'· ℓ-zero) true (g true) (A _ .snd)))
--                , sym ((fb .snd .fst true (g true) ∙ sym (fb .snd .fst true (A true .snd)))
--                    ∙∙ cong f (GetProps.PickOneConst (RP∞'· ℓ-zero) A true)
--                    ∙∙ fb .snd .snd))
--                , ((f (GetProps.2elim (RP∞'· ℓ-zero) true (A _ .snd) (g false)))
--                , sym ((fb .snd .fst false (g false) ∙ sym (fb .snd .fst false (A _ .snd)))
--                    ∙∙ cong f (GetProps.PickOneConst (RP∞'· ℓ-zero) A true)
--                    ∙∙ fb .snd .snd))

-- test : (A B : Type) (n : ℕ)
--   → isOfHLevel (suc n) B
--   → (f : (a : A) → B)
--   → ((x y : A) → f x ≡ f y) 
--   → ∥ A ∥₁ → B
-- test A B zero hl f x = PT.rec hl f
-- test A B (suc n) hl f x ∣ x₁ ∣₁ = f x₁
-- test A B (suc n) hl f x (squash₁ a a₁ i) = {!test A B n !}

-- 2Smash∙→Hom : (X : RP∞' ℓ-zero) (n : ℕ) (A : fst X → Pointed₀)
--   (f g : ((x : fst X) → A x .fst) → coHomK (2 + n))
--   (r : f ≡ g)
--   (fb : GetProps.isBiHom X A (coHomK-ptd (2 + n)) f) (gb : GetProps.isBiHom X A (coHomK-ptd (2 + n)) g)
--   → Path (GetProps.BiHom X A _) (f , fb) (g , gb)
-- 2Smash∙→Hom X n =
--   transport (λ i → (A : snd (blyat i) → Pointed₀)
--   → {!!}) {!PT.rec!} {-
--   transport (λ i → (n : ℕ) (A : snd (blyat i) → Pointed₀)
--   (f g : ((x : (snd (blyat i))) → A x .fst) → coHomK (2 + n))
--   (r : f ≡ g) → {!!} → {!!})
--     {!!}-}
--   where
--   blyat : Path (Σ[ T ∈ Type₁ ] T) -- (Pointed (ℓ-suc ℓ-zero))
--            (RP∞' ℓ-zero , RP∞'· ℓ-zero)
--            (RP∞' ℓ-zero , X)
--   blyat = {!!}
-- {- J> help
--   where
--   open GetProps X
--   help : (fb gb : isBiHom A (coHomK-ptd (suc (suc n))) f) →
--       Path (BiHom A (coHomK-ptd (2 + n)))
--       (f , fb)
--       (f , gb)
--   fst (help fb gb i) g = {!thesingl .fst .fst!}
--     where
--     thesingl : singl _ × singl _
--     thesingl = 2Smash∙→Hom+ₗ X n A g f fb

--     lp : {!!}
--     lp = thesingl .fst .snd ∙ {!thesingl .fst!}

--     h : f g ≡ f g
--     h = {!!} -- sym (GS.rUnitₖ (2 + n) {!f g!}) ∙∙ cong (f g +ₖ_) {!!} ∙∙ GS.rUnitₖ _ (f g)
--   fst (snd (help (f₁ , f₁l , fp₁) (f₂ , f₂l , fp₂) i)) x = {!!}
--   fst (snd (snd (help (f₁ , f₁l , fp₁) (f₂ , f₂l , fp₂) i))) = {!!}
--   snd (snd (snd (help (f₁ , f₁l , fp₁) (f₂ , f₂l , fp₂) i))) = {!!}

-- -}

--   -- ΣPathP ((funExt (λ { (inl x) → cong (fst f) (push (x , A x .snd)) ∙∙ {!!} ∙∙ {!!} ; (inr x) → {!!} ∙∙ {!!} ∙∙ {!!} ; (push a i) → {!!}})) , {!!})
--   -- where
--   -- open GetProps X
--   -- _+B_ : {!!}
--   -- _+B_ = {!!}

--   -- t : fst f (inr (λ x → A {!!} .snd)) ≡ {!!}
--   -- t = {!!}

