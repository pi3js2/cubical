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


module Cubical.Cohomology.EilenbergMacLane.Steenrod2 where

open import Cubical.HITs.Join


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
    ((B : X → Type ℓ')
      → Σ[ elim ∈ ((x : X) (a : B x) (a' : B (nope x)) → (x : _) → B x) ]
         ((x : X) (a : B x) (a' : B (nope x)) → (elim x a a' x ≡ a) × (elim x a a' (nope x) ≡ a')))

RP∞-2Type : (ℓ : Level) (X : RP∞) → is2Type ℓ (fst X)
fst (RP∞-2Type ℓ X) = not* X
fst (snd (RP∞-2Type ℓ X) B) = CasesRP X {B}
snd (snd (RP∞-2Type ℓ X) B) = CasesRPβ X {B}

Bool-2Type : (ℓ : Level) → is2Type ℓ Bool
fst (Bool-2Type ℓ) = not
fst (snd (Bool-2Type ℓ) B) = CasesBool
snd (snd (Bool-2Type ℓ) B) = CasesBoolβ

2Type≡ : ∀ {ℓ} → RP∞-2Type ℓ Bool* ≡ Bool-2Type ℓ
fst (2Type≡ i) = not
fst (snd (2Type≡ i) B) x = CasesRP'Bool i B x .fst
snd (snd (2Type≡ i) B) x = CasesRP'Bool i B x .snd

joinR-gen : ∀ {ℓ ℓ'} (I : Type ℓ) (A : I → Type ℓ') → Type _
joinR-gen I A = PushoutR (Σ I A) ((i : I) → A i)  λ x f → f (fst x) ≡ snd x

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

2-eltFun-elim' : ∀ {ℓ ℓ'} {A B : Type ℓ} {C : B → Type ℓ'} (e : A ≃ B)
  → (ind : (a : A) → C (fst e a))
  → (x : _) → subst C (secEq e _) (ind (invEq e (fst e x))) ≡ ind x
2-eltFun-elim' {A = A} {B = B} {C = C} =
  EquivJ (λ A e → (ind : (a : A) → C (fst e a))
    → (x : _) → subst C (secEq e _) (ind (invEq e (fst e x))) ≡ ind x)
    λ ind x → transportRefl (ind x)


module _ {ℓ : Level} {I J : RP∞} {A : (fst I → fst J) → Type ℓ}
  (ind : (x : _) → A (fst (2-eltFun {I} {J}) x)) where
  2-eltFun-elim : (x : _) → A x
  2-eltFun-elim f = subst A (secEq (2-eltFun {I} {J}) f) (ind (invEq (2-eltFun {I} {J}) f))

  2-eltFun-elim-coh : (x : _) → 2-eltFun-elim  (fst (2-eltFun {I} {J}) x) ≡ ind x
  2-eltFun-elim-coh = 2-eltFun-elim' {C = A} (2-eltFun {I} {J}) ind

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


module 2-elter {ℓ : Level} (I : Type) (J : Type) (A : I → J → Type ℓ) (I2 : ∀ {ℓ} → is2Type ℓ I) where
  notI : I → I
  notI = I2 {ℓ} .fst
  elimI : {ℓ : Level} {B : I → Type ℓ} → _
  elimI {ℓ} {B} = I2 {ℓ} .snd B .fst

  elimIβ : {ℓ : Level} {B : I → Type ℓ} → _
  elimIβ {ℓ} {B} = I2 {ℓ} .snd B .snd
  
  ΠR-base : Type _
  ΠR-base =
    Pushout {A = Σ[ f ∈ (TotΠ λ i → Σ[ j ∈ J ] (A i j)) ]
      (Σ[ g ∈ ((i : I) (j : J) → A i j) ] ((i : I) → g i (f i .fst) ≡ f i .snd))}
                    {B = TotΠ λ i → Σ[ j ∈ J ] (A i j)}
                    {C = (i : I) (j : J) → A i j}
                    fst
                    (fst ∘ snd)

  left-push : Type _
  left-push = Σ[ i ∈ I ] (Σ[ j ∈ J ] (A i j)) × ((j : J) → A (notI i) j)

  left-push↑ₗ : I → Type _
  left-push↑ₗ i = Σ[ f ∈ ((i : I) → Σ[ j ∈ J ] A i j) ]
    Σ[ g ∈ ((j : J) → A (notI i) j) ] (g (f (notI i) .fst) ≡ f (notI i) .snd)

  left-push↑ᵣ : I → Type _
  left-push↑ᵣ i = Σ[ f ∈ (Σ[ j ∈ J ] A i j) ]
      Σ[ g ∈ ((i : I) (j : J) → A i j) ] g i (fst f) ≡ snd f

  fat : Type _
  fat = (Σ[ f ∈ ((i : I) → Σ[ j ∈ J ] A i j) ]
          Σ[ g ∈ ((i : I) (j : J) → A i j) ]
            ((i : I) → g i (f i .fst) ≡ f i .snd))

  fat→ₗ : (i : I) → fat → left-push↑ₗ i
  fat→ₗ  i (f , g , r) = (f , (g (notI i)) , (r (notI i)))

  fat→ᵣ : (i : I) → fat → left-push↑ᵣ i
  fat→ᵣ i (f , g , r) =  f i , g , r i

  PushTop : Type _
  PushTop = Σ[ i ∈ I ] (Pushout (fat→ₗ i) (fat→ᵣ i))

  PushTop→left-push' : (i : I)
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

  pre-eqvl-diag : (i' : I) (p : Pushout (fat→ₗ i') (fat→ᵣ i'))
    → ΠR-extend→Πₗ (PushTop→left-push (i' , p)) i'
     ≡ ΠR-base→ (PushTop→ΠR-base (i' , p)) i'
  pre-eqvl-diag i' (inl (f , f2 , p)) =
    elimIβ {B = λ i → joinR-gen J (A i)} i' (inlR (f i' .fst , f i' .snd)) (inrR f2) .fst
  pre-eqvl-diag i' (inr (f , f2 , p)) =
    elimIβ {B = λ i → joinR-gen J (A i)} i' (inlR f) (inrR (f2 (notI i'))) .fst ∙ push* f (f2 i') p 
  pre-eqvl-diag i' (push (f , f2 , p) i) j =
    compPath-filler (elimIβ {B = λ i → joinR-gen J (A i)} i' (inlR (f i')) (inrR (f2 (notI i'))) .fst)
                    (push* (f i') (f2 i') (p i')) i j

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

  dable : Type _
  dable = Pushout {A = I × ΠR-extend} {B = Σ[ i ∈ I ] joinR-gen J (A i)} {C = ΠR-extend}
                  (λ a → fst a , ΠR-extend→Π (snd a) (fst a))
                  snd
                  

  private
    inl123 : (a : _) → dable
    inl123 = inl
  module _ (ise : isEquiv ΠR-extend→Π) where
    
    updater→ : dable → (joinR-gen I (λ i → joinR-gen J (A i)))
    updater→ (inl x) = inlR x
    updater→ (inr x) = inrR (ΠR-extend→Π x)
    updater→ (push a i) = push* (fst a , ΠR-extend→Π (snd a) (fst a)) (ΠR-extend→Π (snd a)) refl i

    updater← : joinR-gen I (λ i → joinR-gen J (A i)) → dable
    updater← (inlR x) = inl x
    updater← (inrR x) = inr (invEq (_ , ise) x)
    updater← (push* a b x i) =
      (cong inl123 (ΣPathP (refl , sym x ∙ sym (funExt⁻ (secEq (_ , ise) b) (fst a))))
              ∙ push ((fst a) , invEq (_ , ise) b)) i

{-
  updater : isEquiv ΠR-extend→Π → Iso dable (joinR-gen I (λ i → joinR-gen J (A i)))
  Iso.fun (updater ise) = updater→ ise
  Iso.inv (updater ise) = updater← ise
  Iso.rightInv (updater ise) (inlR x) = refl
  Iso.rightInv (updater ise) (inrR x) j = inrR (secEq (_ , ise) x j)
  Iso.rightInv (updater ise) (push* a b x i) j = help (fst a) b (snd a) x j i
    where
    help : (i* : I) (b : (ℓ₁ : I) → joinR-gen J (A ℓ₁)) (a : joinR-gen J (A i*)) (x : b i* ≡ a)
      → PathP (λ i → inlR (i* , a) ≡ inrR (secEq (ΠR-extend→Π , ise) b i))
              (cong (updater→ ise) (cong (updater← ise) (push* (i* , a) b x))) (push* (i* , a) b x)
    help i* b = J> ((cong (cong (updater→ ise)) (λ i → cong inl123 (λ j → i* , {!lUnit ? i!}) ∙ push (i* , invEq (_ , ise) b)) ∙ {!!}) ◁ {!!})
  Iso.leftInv (updater ise) = {!!}
  -}

  ΠR-extend→Π-rev : {!ΠR-extend!} -- TotΠ (λ i → joinR-gen J (A i))
  ΠR-extend→Π-rev = {!!}


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

  ΠR-baseBoolIso' : Iso ΠR-baseBool (2-elter.ΠR-base Bool J A (Bool-2Type _))
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

ΠR-extend→Π-alt : ∀ {ℓ} (A : Bool → Bool → Type ℓ)
  → 2-elter.ΠR-extend Bool Bool A (Bool-2Type _)
  → TotΠ (λ i → joinR Bool* (A i))
ΠR-extend→Π-alt A (inl (false , (f , p))) false = inlR f
ΠR-extend→Π-alt A (inl (false , (f , p))) true = inrR p
ΠR-extend→Π-alt A (inl (true , (f , p))) false = inrR p
ΠR-extend→Π-alt A (inl (true , (f , p))) true = inlR f
ΠR-extend→Π-alt A (inr (inl x)) a = inlR (x a)
ΠR-extend→Π-alt A (inr (inr x)) b = inrR (x b)
ΠR-extend→Π-alt A (inr (push a i)) c =
  push* (fst a c) (fst (snd a) c) (snd (snd a) c) i
ΠR-extend→Π-alt A (push (false , inl x) i) false = inlR (fst x false)
ΠR-extend→Π-alt A (push (false , inr x) i) false = push* (fst x) (fst (snd x) false) (snd (snd x)) i
ΠR-extend→Π-alt A (push (false , push (f , p , q) i₁) i) false = push* (f false) (p false) (q false) (i ∧ i₁)
ΠR-extend→Π-alt A (push (false , inl x) i) true = push* (fst x true) (fst (snd x)) (snd (snd x)) (~ i)
ΠR-extend→Π-alt A (push (false , inr x) i) true = inrR (fst (snd x) true)
ΠR-extend→Π-alt A (push (false , push (f , p , q) i₁) i) true = push* (f true) (p true) (q true) (~ i ∨ i₁)
ΠR-extend→Π-alt A (push (true , inl x) i) false = push* (fst x false) (fst (snd x)) (snd (snd x)) (~ i)
ΠR-extend→Π-alt A (push (true , inr x) i) false = inrR (fst (snd x) false)
ΠR-extend→Π-alt A (push (true , push (f , p , q) i₁) i) false = push* (f false) (p false) (q false) (~ i ∨ i₁)
ΠR-extend→Π-alt A (push (true , inl x) i) true = inlR (fst x true)
ΠR-extend→Π-alt A (push (true , inr x) i) true = push* (fst x) (fst (snd x) true) (snd (snd x)) i
ΠR-extend→Π-alt A (push (true , push (f , p , q) i₁) i) true = push* (f true) (p true) (q true) (i ∧ i₁)

ΠR-extend→Π-alt≡ : ∀ {ℓ} (A : Bool → Bool → Type ℓ)
  → (x : _) (z : _) → ΠR-extend→Π-alt A x z ≡ 2-elter.ΠR-extend→Π Bool Bool A (Bool-2Type _) x z
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


ΠR-extend→× : ∀ {ℓ} (A : Bool → Bool → Type ℓ)
  → 2-elter.ΠR-extend Bool Bool A (Bool-2Type _)
  → joinR Bool* (A true) × joinR Bool* (A false)
ΠR-extend→× A t = ΠBool→× {A = λ x → joinR Bool* (A x)} (ΠR-extend→Π-alt A t)

ΠR-extend→×-old : ∀ {ℓ} (A : Bool → Bool → Type ℓ)
  → 2-elter.ΠR-extend Bool Bool A (Bool-2Type _)
  → joinR Bool* (A true) × joinR Bool* (A false)
ΠR-extend→×-old A t = ΠBool→× {A = λ x → joinR Bool* (A x)} (2-elter.ΠR-extend→Π Bool Bool A (Bool-2Type _) t)


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
  module GenF {ℓ : Level} (J : Type) (A : Bool → J → Type ℓ) where

    fill₂-b : (a a' : J) (b : A true a) (b₁ : A false a')
            (c : (i₂ : J) → A true i₂)
            (c₁ : (i₂ : J) → A false i₂)
            (x : c a ≡ b)
            (d : c₁ a' ≡ b₁)
          → I → I → I → 2-elter.ΠR-extend Bool J A (Bool-2Type _)
    fill₂-b a a' b b₁ c c₁ x d i i₁ r = Square-filler {A = 2-elter.ΠR-extend Bool J A (Bool-2Type _)}
          (push (true , inl (CasesBool true (a , b) (a' , b₁) , c₁ , d)))
          (push (false , inl (CasesBool true (a , b) (a' , b₁) , c , x)))
           i i₁ r

    fill₂ : (a a' : J) (b : A true a) (b₁ : A false a')
            (c : (i₂ : J) → A true i₂)
            (c₁ : (i₂ : J) → A false i₂)
            (x : c a ≡ b)
            (d : c₁ a' ≡ b₁)
          → I → I → I → 2-elter.ΠR-extend Bool J A (Bool-2Type _)
    fill₂ a a' b b₁ c c₁ x d i i₁ r =
      hfill (λ r → λ {(i = i0) → push (true , inl (CasesBool true (a , b) (a' , b₁) , c₁ , d)) (~ i₁)
                 ; (i = i1) → push (false , push ((CasesBool true (a , b) (a' , b₁)) , (CasesBool true c c₁ , CasesBool true x d)) r) i₁
                 ; (i₁ = i0) → push (false , inl (CasesBool true (a , b) (a' , b₁) , c , x)) (~ i)
                 ; (i₁ = i1) → push (true , push ((CasesBool true (a , b) (a' , b₁)) , ((CasesBool true c c₁) , CasesBool true x d)) r) i})
        (inS (Square-filler {A = 2-elter.ΠR-extend Bool J A (Bool-2Type _)}
          (push (true , inl (CasesBool true (a , b) (a' , b₁) , c₁ , d)))
          (push (false , inl (CasesBool true (a , b) (a' , b₁) , c , x)))
           i i₁ i1)) r



private
  module _ {ℓ : Level} (A : Bool → Bool → Type ℓ) where

    fill₂-b : (a a' : Bool) (b : A true a) (b₁ : A false a')
            (c : (i₂ : fst Bool*) → A true i₂)
            (c₁ : (i₂ : fst Bool*) → A false i₂)
            (x : c a ≡ b)
            (d : c₁ a' ≡ b₁)
          → I → I → I → 2-elter.ΠR-extend Bool Bool A (Bool-2Type _)
    fill₂-b a a' b b₁ c c₁ x d i i₁ r = Square-filler {A = 2-elter.ΠR-extend Bool Bool A (Bool-2Type _)}
          (push (true , inl (CasesBool true (a , b) (a' , b₁) , c₁ , d)))
          (push (false , inl (CasesBool true (a , b) (a' , b₁) , c , x)))
           i i₁ r

    fill₂ : (a a' : Bool) (b : A true a) (b₁ : A false a')
            (c : (i₂ : fst Bool*) → A true i₂)
            (c₁ : (i₂ : fst Bool*) → A false i₂)
            (x : c a ≡ b)
            (d : c₁ a' ≡ b₁)
          → I → I → I → 2-elter.ΠR-extend Bool Bool A (Bool-2Type _)
    fill₂ a a' b b₁ c c₁ x d i i₁ r =
      hfill (λ r → λ {(i = i0) → push (true , inl (CasesBool true (a , b) (a' , b₁) , c₁ , d)) (~ i₁)
                 ; (i = i1) → push (false , push ((CasesBool true (a , b) (a' , b₁)) , (CasesBool true c c₁ , CasesBool true x d)) r) i₁
                 ; (i₁ = i0) → push (false , inl (CasesBool true (a , b) (a' , b₁) , c , x)) (~ i)
                 ; (i₁ = i1) → push (true , push ((CasesBool true (a , b) (a' , b₁)) , ((CasesBool true c c₁) , CasesBool true x d)) r) i})
        (inS (Square-filler {A = 2-elter.ΠR-extend Bool Bool A (Bool-2Type _)}
          (push (true , inl (CasesBool true (a , b) (a' , b₁) , c₁ , d)))
          (push (false , inl (CasesBool true (a , b) (a' , b₁) , c , x)))
           i i₁ i1)) r


×→ΠR-extend-gen : ∀ {ℓ} (J : RP∞) (A : Bool → fst J → Type ℓ)
  → joinR J (A true) × joinR J (A false)
  → 2-elter.ΠR-extend Bool (fst J) A (Bool-2Type _)
×→ΠR-extend-gen J A (inlR x , inlR x₁) = inr (inl (CasesBool true x x₁))
×→ΠR-extend-gen J A (inlR (x , b) , inrR x₁) = inl (true , ((_ , b) , x₁))
×→ΠR-extend-gen J A (inlR (a , b) , push* (a' , d) c x₁ i) =
  push (true , inl ((CasesBool true (a , b) (a' , d)) , c , x₁)) (~ i)
×→ΠR-extend-gen J A (inrR x , inlR x₁) = inl (false , (x₁ , x))
×→ΠR-extend-gen J A (inrR x , inrR x₁) = inr (inr (CasesBool true x x₁))
×→ΠR-extend-gen J A (inrR x , push* (a , b) c x₁ i) =
  push (false , (inr ((a , b) , ((CasesBool true x c) , x₁)))) i
×→ΠR-extend-gen J A (push* (a , b) c x i , inlR (a' , b')) =
  push (false , inl ((CasesBool true (a , b) (a' , b')) , (c , x))) (~ i)
×→ΠR-extend-gen J A (push* (a' , b) c x i , inrR x₁) =
  push (true , inr ((_ , b) , (CasesBool true c x₁ , x))) i
×→ΠR-extend-gen J A (push* (a , b) c x i , push* (a' , b₁) c₁ d i₁) =
  GenF.fill₂ (fst J) A a a' b b₁ c c₁ x d i i₁ i1

×→ΠR-extend-gen' : ∀ {ℓ} (J : RP∞) (A : Bool → fst J → Type ℓ)
  → ((x : Bool) → joinR J (A x))
  → 2-elter.ΠR-extend Bool (fst J) A (Bool-2Type _)
×→ΠR-extend-gen' J A = ×→ΠR-extend-gen J A ∘ Iso.fun ΠBool×Iso

×→ΠR-extend : ∀ {ℓ} (A : Bool → Bool → Type ℓ)
  → joinR Bool* (A true) × joinR Bool* (A false)
  → 2-elter.ΠR-extend Bool Bool A (Bool-2Type _)
×→ΠR-extend = ×→ΠR-extend-gen Bool*

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
  module _ {ℓ : Level} (A : Bool → Bool → Type ℓ) where
    fill-fill : (a a' : Bool) (b : A true a) (b₁ : A false a')
            (c : (i₂ : fst Bool*) → A true i₂)
            (c₁ : (i₂ : fst Bool*) → A false i₂)
            (x : c a ≡ b)
            (d : c₁ a' ≡ b₁)
          → I → I → I → joinR Bool* (A true) × joinR Bool* (A false)
    fill-fill a a' b b₁ c c₁ x d i i₁ k =
      hcomp (λ r → λ {(k = i0) → ΠR-extend→× A (fill₂ A a a' b b₁ c c₁ x d i i₁ r)
                 ; (k = i1) → (push* (a , b) c x (i ∧ (~ i₁ ∨ r)))
                               , push* (a' , b₁) c₁ d (((~ i) ∨ r) ∧ i₁)
                 ; (i₁ = i0) → ΠR-extend→× A (fill₂ A a a' b b₁ c c₁ x d i i₁ r)
                 ; (i₁ = i1) → ΠR-extend→× A (fill₂ A a a' b b₁ c c₁ x d i i₁ r)
                 ; (i = i0) → ΠR-extend→× A (fill₂ A a a' b b₁ c c₁ x d i i₁ r)
                 ; (i = i1) → ΠR-extend→× A (fill₂ A a a' b b₁ c c₁ x d i i₁ r)})
                 (hcomp (λ r
                → λ {(k = i0) → ΠR-extend→× A (Square-filler {A = 2-elter.ΠR-extend Bool Bool A (Bool-2Type _)}
                                   (push (true , inl ((CasesBool true (a , b) (a' , b₁)) , (c₁ , d))))
                                   (push (false , inl ((CasesBool true (a , b) (a' , b₁)) , (c , x))))
                                    i i₁ r)
                 ; (k = i1) → push* (a , b) c x (i ∧ ~ i₁ ∧ r) , push* (a' , b₁) c₁ d (~ i ∧ i₁ ∧ r)
                 ; (i₁ = i0) → push* (a , b) c x (r ∧ i) , inlR (a' , b₁)
                 ; (i₁ = i1) → inlR (a , b) , push* (a' , b₁) c₁ d (~ i ∧ r)
                 ; (i = i0) → inlR (a , b) , push* (a' , b₁) c₁ d (i₁ ∧ r)
                 ; (i = i1) → push* (a , b) c x (~ i₁ ∧ r) , inlR (a' , b₁) })
                 ((inlR (a , b) , inlR (a' , b₁))))

×→ΠR-extend→× : ∀ {ℓ} (A : Bool → Bool → Type ℓ)
  (m : joinR Bool* (A true) × joinR Bool* (A false))
  → ΠR-extend→× A (×→ΠR-extend A m) ≡ m
×→ΠR-extend→× A (inlR (a , b) , inlR (a' , d)) = refl
×→ΠR-extend→× A (inlR (a , snd₁) , inrR x₁) = refl
×→ΠR-extend→× A (inlR (a , b) , push* (a' , d) e x₁ i) = refl
×→ΠR-extend→× A (inrR x , inlR (a , b)) = refl
×→ΠR-extend→× A (inrR x , inrR x₁) = refl
×→ΠR-extend→× A (inrR x , push* (a' , b) c x₁ i) = refl
×→ΠR-extend→× A (push* (a , b) b₁ x i , inlR (a' , b')) = refl
×→ΠR-extend→× A (push* (a , b) b₁ x i , inrR x₁) = refl
×→ΠR-extend→× A (push* (a , b) b₁ x i , push* (a' , b') c x₁ i₁) k =
  fill-fill A a a' b b' b₁ c x x₁ i i₁ k


ΠR-extend→×→ΠR-extend-inl : ∀ {ℓ} (A : Bool → Bool → Type ℓ) (m : _)
  → ×→ΠR-extend A (ΠR-extend→× A (inl m)) ≡ (inl m)
ΠR-extend→×→ΠR-extend-inl A (false , (b , c) , d) = refl
ΠR-extend→×→ΠR-extend-inl A (true , (b , c) , d) = refl

fill23 : ∀ {ℓ} (A : Bool → Bool → Type ℓ)
  (f : TotΠ (λ i₁ → Σ-syntax Bool (A i₁)))
  (a : (i₁ j₁ : Bool) → A i₁ j₁)
  (b : (i₁ : Bool) → a i₁ (f i₁ .fst) ≡ f i₁ .snd)
  → I → I → I → 2-elter.ΠR-extend Bool Bool A (Bool-2Type _)
fill23 A f a b i j k =
  hfill (λ r → λ {(i = i0) → push (true , (inl (CasesBoolη f j , a false , b false))) r
                 ; (i = i1) → push (true , (inr (f true , CasesBoolη a j , b true))) r
                 ; (j = i0) → fill₂ A (fst (f true)) (fst (f false)) (snd (f true))
                                       (snd (f false)) (a true) (a false) (b true) (b false) (i ∧ r) (i ∨ ~ r) i1
                 ; (j = i1) → push (true , (push (f , (a , b)) i)) r})
        (inS (inl (true , f true , a false)))
        k

fill23PP : ∀ {ℓ} (A : Bool → Bool → Type ℓ)
  (f : TotΠ (λ i₁ → Σ-syntax Bool (A i₁)))
  (a : (i₁ j₁ : Bool) → A i₁ j₁)
  (b : (i₁ : Bool) → a i₁ (f i₁ .fst) ≡ f i₁ .snd)
  → Square (λ j → push (true , (inl (CasesBoolη f j , a false , b false))) i1)
            (λ j → push (true , (inr (f true , CasesBoolη a j , b true))) i1)
                  (λ i → fill₂ A (fst (f true)) (fst (f false)) (snd (f true))
                                 (snd (f false)) (a true) (a false) (b true) (b false) i i i1)
            λ i → push (true , (push (f , (a , b)) i)) i1
fill23PP A f a b i j = fill23 A f a b i j i1

fill23' : ∀ {ℓ} (A : Bool → Bool → Type ℓ)
  (f : TotΠ (λ i₁ → Σ-syntax Bool (A i₁)))
  (a : (i₁ j₁ : Bool) → A i₁ j₁)
  (b : (i₁ : Bool) → a i₁ (f i₁ .fst) ≡ f i₁ .snd)
  → I → I → I → 2-elter.ΠR-extend Bool Bool A (Bool-2Type _)
fill23' A f a b i j k =
  hfill (λ r → λ {(i = i0) → push (false , inl (CasesBoolη f j , a true , b true)) r
                 ; (i = i1) → push (false , (inr (f false , CasesBoolη a j , b false))) r
                 ; (j = i0) → fill₂ A (fst (f true)) (fst (f false)) (snd (f true))
                                       (snd (f false)) (a true) (a false) (b true) (b false) (i ∨ ~ r) (i ∧ r) i1
                 ; (j = i1) → push (false , (push (f , (a , b)) i)) r})
        (inS (inl (false , f false , a true)))
        k

fill23PP≡ : ∀ {ℓ} (A : Bool → Bool → Type ℓ)
  (f : TotΠ (λ i₁ → Σ-syntax Bool (A i₁)))
  (a : (i₁ j₁ : Bool) → A i₁ j₁)
  (b : (i₁ : Bool) → a i₁ (f i₁ .fst) ≡ f i₁ .snd)
  → fill23PP A f a b ≡ λ i j → fill23' A f a b i j i1
fill23PP≡ A f a b k i j =
  hcomp (λ r → λ {(i = i0) → push (true , inl (CasesBoolη f j , a false , b false)) (r ∨ k)
                 ; (i = i1) → push (true , inr (f true , CasesBoolη a j , b true)) (r ∨ k)
                 ; (j = i0) → fill₂ A (fst (f true)) (fst (f false)) (snd (f true))
                                       (snd (f false)) (a true) (a false) (b true) (b false) (i ∧ (r ∨ k)) (i ∨ ~ (r ∨ k)) i1
                 ; (j = i1) → push (true , push (f , a , b) i) (r ∨ k)
                 ; (k = i0) → fill23 A f a b i j r
                 ; (k = i1) → fill23' A f a b i j i1})
    (hcomp (λ r → λ {(i = i0) → push (true , inl (CasesBoolη f j , a false , b false)) k
                 ; (i = i1) → push (true , push (CasesBoolη f j , CasesBoolη a j , lee j) r) k
                 ; (j = i0) → fill₂ A (fst (f true)) (fst (f false)) (snd (f true))
                                       (snd (f false)) (a true) (a false) (b true) (b false) (i ∧ k) (i ∨ ~ k) r
                 ; (j = i1) → push (true , push (f , a , b) (r ∧ i)) k
                 ; (k = i0) → inl (true , f true , a false)
                 ; (k = i1) → tap2 r j i})
      (hcomp (λ r → λ {(i = i0) → push (true , inl (CasesBoolη f j , a false , b false)) (k ∨ ~ r)
                 ; (i = i1) → push (true , inl ((CasesBoolη f j) , ((a false) , (b false)))) (k ∨ ~ r)
                 ; (j = i0) → fill₂-b A (fst (f true)) (fst (f false)) (snd (f true))
                                       (snd (f false)) (a true) (a false) (b true) (b false) (i ∧ k) (i ∨ ~ k) r
                 ; (j = i1) → push (true , inl (f , a false , b false)) (k ∨ ~ r)
                 ; (k = i0) → push (true , inl (CasesBoolη f j , a false , b false)) (~ r)
                 ; (k = i1) → tap r j i})
             ((inr (inl (CasesBoolη f j))))))
   where
   H = 2-elter.ΠR-extend Bool Bool A (Bool-2Type _)

   topSqfiller : I → I → I → H
   topSqfiller i j k =
     hfill (λ r → λ {(i = i0) → fill₂-b A (fst (f true)) (fst (f false)) (snd (f true))
                                            (snd (f false)) (a true) (a false) (b true) (b false) j j r
                 ; (i = i1) → inr (push (f , (a , CasesBool true (b true) (b false))) (~ r ∧ ~ j))
                 ; (j = i0) → inr (push ((CasesBoolη f i) , (a , (CasesBool true (b true) (b false)))) (~ r ∧ i))
                 ; (j = i1) → inr (inl (CasesBoolη f i))})
       (inS ((inr
          (push (CasesBoolη f i , a , CasesBool true (b true) (b false)) (i ∧ ~ j)))))
       k

   topSq : Square {A = H}
      (λ i₁ →
         fill₂-b A (fst (f true)) (fst (f false)) (snd (f true))
         (snd (f false)) (a true) (a false) (b true) (b false) i₁ i₁ i1)
      (λ _ → inr (inl f)) (λ j₁ → inr (inl (CasesBoolη f j₁)))
      (λ j₁ → inr (inl (CasesBoolη f j₁)))
   topSq i j = topSqfiller i j i1
  
   tap : Cube {A = H}
              (λ j i → inr (inl (CasesBoolη f j)))
              topSq
              (λ r i → fill₂-b A (fst (f true)) (fst (f false)) (snd (f true))
                         (snd (f false)) (a true) (a false) (b true) (b false) i i r)
              (λ _ _ → inr (inl f))
              (λ r j → inr (inl (CasesBoolη f j)))
              (λ r j → inr (inl (CasesBoolη f j))) -- r j i
   tap i j k =
     hcomp (λ r → λ {(i = i0) → inr (push (CasesBoolη f j , a , CasesBool true (b true) (b false)) (~ r ∧ ~ k ∧ j))
                 ; (i = i1) → topSqfiller j k r
                 ; (j = i0) → fill₂-b A (fst (f true)) (fst (f false)) (snd (f true))
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
              (λ j i → fill23' A f a b i j i1)
              (λ r i → fill₂ A (fst (f true)) (fst (f false)) (snd (f true))
                    (snd (f false)) (a true) (a false) (b true) (b false) i i r)
              (λ r i → inr (push (f , a , b) (r ∧ i)))
              (λ i j → inr (inl (CasesBoolη f j)))
              λ i j → inr (push (CasesBoolη f j , CasesBoolη a j , lee j) i)
   tap2 r i j =
     hcomp (λ k → λ {(i = i0) → fill₂ A (fst (f true)) (fst (f false)) (snd (f true))
                                       (snd (f false)) (a true) (a false) (b true) (b false) (j ∨ (~ k ∧ r)) (j ∧ (k ∨ ~ r)) r
                 ; (i = i1) → push (false , push (f , a , b) (r ∧ j)) (k ∨ ~ r)
                 ; (j = i0) → push (false , inl ((CasesBoolη f i) , ((a true) , (b true)))) (k ∨ ~ r)
                 ; (j = i1) → push (false , push ((CasesBoolη f i) , (CasesBoolη a i , lee i)) r) (k ∨ ~ r)
                 ; (r = i0) → topSqfiller i j i1
                 ; (r = i1) → fill23' A f a b j i k})
           (hcomp (λ k → λ {(i = i0) →
             fill₂ A (fst (f true)) (fst (f false)) (snd (f true)) (snd (f false)) (a true) (a false) (b true) (b false) (j ∨ r) (j ∧ (~ r)) (r ∧ k)
                 ; (i = i1) → push (false , push (f , a , CasesBoolη b k) (r ∧ (j ∧ k))) (~ r)
                 ; (j = i0) → push ((false , inl (CasesBoolη f i , a true , b true))) (~ r)
                 ; (j = i1) → push ((false , push (CasesBoolη f i , CasesBoolη a i , helpme k i) (r ∧ k))) (~ r)
                 ; (r = i0) → topSqfiller i j i1 -- topSqfiller i j i1
                 ; (r = i1) → inl (false , f false , a true)})
              (hcomp (λ k → λ {(i = i0) → fill₂-b A (fst (f true)) (fst (f false))
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

ΠR-extend→×→ΠR-extend : ∀ {ℓ} (A : Bool → Bool → Type ℓ) (m : _)
  → ×→ΠR-extend A (ΠR-extend→× A m) ≡ m
ΠR-extend→×→ΠR-extend A (inl m) = ΠR-extend→×→ΠR-extend-inl A m
ΠR-extend→×→ΠR-extend A (inr (inl x)) j = inr (inl (CasesBoolη x j))
ΠR-extend→×→ΠR-extend A (inr (inr x)) j = inr (inr (CasesBoolη {A = λ i → TotΠ (A i)} x j ))
ΠR-extend→×→ΠR-extend A (inr (push (f , a , b) i)) j = fill23 A f a b i j i1
ΠR-extend→×→ΠR-extend A (push (false , inl (f , q , t)) i) i₁ = push (false , inl (CasesBoolη f i₁ , q , t)) i
ΠR-extend→×→ΠR-extend A (push (true , inl (f , q , t)) i) i₁ = push (true , inl (CasesBoolη f i₁ , q , t)) i
ΠR-extend→×→ΠR-extend A (push (false , inr (f , q , t)) i) j = push (false , inr (f , CasesBoolη q j , t)) i
ΠR-extend→×→ΠR-extend A (push (true , inr (f , q , t)) i) j = push (true , inr (f , CasesBoolη q j , t)) i
ΠR-extend→×→ΠR-extend A (push (false , push (f , q , t) i₂) i) i₁ =
  hcomp (λ r → λ {(i = i0) → inl (false , f false , q true)
                  ; (i = i1) → fill23PP≡ A f q t (~ r) i₂ i₁
                  ; (i₁ = i0) → fill₂ A (fst (f true)) (fst (f false))
                                         (snd (f true)) (snd (f false))
                                         (q true) (q false)
                                         (t true) (t false)
                                         ((~ i) ∨ i₂) (i ∧ i₂) i1
                  ; (i₁ = i1) → push (false , push (f , q , t) i₂) i -- push (false , {!!}) i
                  ; (i₂ = i0) → push (false , inl (CasesBoolη f i₁ , q true , t true)) i
                  ; (i₂ = i1) → push (false , inr (f false , CasesBoolη q i₁ , t false)) i})
     (hcomp (λ r → λ {(i = i0) → inl (false , f false , q true)
                  ; (i = i1) → fill23' A f q t i₂ i₁ r
                  ; (i₁ = i0) → fill₂ A (fst (f true)) (fst (f false))
                                         (snd (f true)) (snd (f false))
                                         (q true) (q false)
                                         (t true) (t false)
                                         ((~ i) ∨ (i₂ ∨ ~ r)) (i ∧ (i₂ ∧ r)) i1
                  ; (i₁ = i1) → push (false , push (f , q , t) i₂) (r ∧ i)
                  ; (i₂ = i0) → push (false , (inl ((CasesBoolη f i₁) , ((q true) , (t true))))) (i ∧ r)
                  ; (i₂ = i1) → push (false , inr (f false , CasesBoolη q i₁ , t false)) (i ∧ r)})
                  (inl (false , f false , q true)))
ΠR-extend→×→ΠR-extend A (push (true , push (f , q , t) i₂) i) i₁ =
  hcomp (λ r → λ {(i = i0) → inl (true , f true , q false)
                  ; (i = i1) → fill23 A f q t i₂ i₁ r
                  ; (i₁ = i0) → fill₂ A (fst (f true)) (fst (f false))
                                         (snd (f true)) (snd (f false))
                                         (q true) (q false)
                                         (t true) (t false)
                                         (i ∧ (i₂ ∧ r)) ((~ i) ∨ (i₂ ∨ ~ r)) i1
                  ; (i₁ = i1) → push (true , push (f , q , t) i₂) (r ∧ i)
                  ; (i₂ = i0) → push (true , inl (CasesBoolη f i₁ , q false , t false)) (i ∧ r)
                  ; (i₂ = i1) → push (true , inr (f true , CasesBoolη q i₁ , t true)) (i ∧ r)})
          (inl (true , f true , q false))


ΠR-extend→×Iso : ∀ {ℓ} (A : Bool → Bool → Type ℓ)
  → Iso (2-elter.ΠR-extend Bool Bool A (Bool-2Type _))
         (joinR Bool* (A true) × joinR Bool* (A false))
Iso.fun (ΠR-extend→×Iso A) = ΠR-extend→× A
Iso.inv (ΠR-extend→×Iso A) = ×→ΠR-extend A
Iso.rightInv (ΠR-extend→×Iso A) = ×→ΠR-extend→× A
Iso.leftInv (ΠR-extend→×Iso A) = ΠR-extend→×→ΠR-extend A


ΠR-extend→Π-equiv-base : ∀ {ℓ} (A : Bool → Bool → Type ℓ)
  → isEquiv (2-elter.ΠR-extend→Π Bool Bool A (Bool-2Type _))
ΠR-extend→Π-equiv-base A = transport (λ i → isEquiv (p i)) isEq
  where
  p : ΠR-extend→Π-alt A ≡ 2-elter.ΠR-extend→Π Bool Bool A (Bool-2Type _)
  p = funExt λ x → funExt (ΠR-extend→Π-alt≡ A x)

  alt : (2-elter.ΠR-extend Bool Bool A (Bool-2Type _)) ≃ ((x : Bool) → joinR Bool* (A x))
  alt = isoToEquiv (compIso (ΠR-extend→×Iso A) (invIso ΠBool×Iso))

  altid : fst alt ≡ ΠR-extend→Π-alt A
  altid = funExt λ x → funExt (CasesBool true refl refl)

  isEq : isEquiv (ΠR-extend→Π-alt A)
  isEq = subst isEquiv altid (snd alt)

ΠR-extend→Π-equiv : ∀ {ℓ} (I J : RP∞) (A : fst I → fst J → Type ℓ)
  → isEquiv (2-elter.ΠR-extend→Π (fst I) (fst J) A (RP∞-2Type _ I))
ΠR-extend→Π-equiv =
  RP∞pt→Prop (λ _ → isPropΠ2 λ _ _ → isPropIsEquiv _)
    (RP∞pt→Prop (λ _ → isPropΠ λ _ → isPropIsEquiv _)
      λ A → transport (λ i → isEquiv (2-elter.ΠR-extend→Π Bool Bool A (2Type≡ (~ i))))
        (ΠR-extend→Π-equiv-base A))

×→ΠR-extend-gen-Equiv-Bool : ∀ {ℓ} (A : Bool → Bool → Type ℓ) → isEquiv (×→ΠR-extend-gen' Bool* A)
×→ΠR-extend-gen-Equiv-Bool A =
  composesToId→Equiv (Iso.inv ΠBool×Iso ∘ ΠR-extend→× A) _
    (funExt λ p → cong (Iso.inv ΠBool×Iso) (Iso.rightInv (ΠR-extend→×Iso A) (Iso.fun ΠBool×Iso p))
                 ∙ Iso.leftInv ΠBool×Iso p)
    (compEquiv (isoToEquiv (ΠR-extend→×Iso A))
      (isoToEquiv (invIso ΠBool×Iso)) .snd)

×→ΠR-extend-gen-Equiv : ∀ {ℓ} (J : RP∞) (A : Bool → fst J → Type ℓ)
  → isEquiv (×→ΠR-extend-gen' J A)
×→ΠR-extend-gen-Equiv =
  RP∞pt→Prop (λ _ → isPropΠ λ _ → isPropIsEquiv _)
    (×→ΠR-extend-gen-Equiv-Bool)

×→ΠR-extend-gen-Equiv≃ : ∀ {ℓ} (J : RP∞) (A : Bool → fst J → Type ℓ)
  → (((x : Bool) → joinR J (A x))) ≃ 2-elter.ΠR-extend Bool (fst J) A (Bool-2Type _)
×→ΠR-extend-gen-Equiv≃ J A = {!!}

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

  

-- --   ΠR-base→J : ΠR-base → GOAL
-- --   ΠR-base→J (inl f) = asd (Iso.fun (TotAIso I J) f)
-- --   ΠR-base→J (inr x) = inrR λ i → inrR λ j → x j i
-- --   ΠR-base→J (push (f , p , q) i) = asd-coh (f1 I J f) p (cool (fst ∘ f) (snd ∘ f) (funExt q)) i
-- --     where
-- --     cool : (f1* : (a : fst I) → fst J)
-- --            (sf : (a : fst I) → A a (f1* a))
-- --          → (q : (λ i → p i (f1* i)) ≡ sf)
-- --          → (i₁ : fst I) → p i₁ (2-eltFun {I} {J} .fst (f1 I J {A = A} (λ i → f1* i , sf i) .fst) i₁)
-- --                          ≡ f1 I J {A = A} (λ i → f1* i , sf i) .snd i₁
-- --     cool f1* = J> λ j → {!cong (p j) ?!}



-- --   ΠR-extend-rec : ∀ {ℓ*} {B : Type ℓ*}
-- --     → (l : ΠR-base → B)
-- --     → ((i : fst I) → Σ[ g ∈ (Σ[ j ∈ fst J ] (A i j) × ((j : fst J) → A (notI i) j) → B) ]
-- --                         ((a : Pushout (fat→ₗ i) (fat→ᵣ i))
-- --                       → l (PushTop→ΠR-base (i , a))
-- --                        ≡ g ((PushTop→left-push (i , a) .snd) .fst .fst , (PushTop→left-push (i , a) .snd) .fst .snd , (PushTop→left-push (i , a) .snd) .snd)))
-- --     → (ΠR-extend → B)
-- --   ΠR-extend-rec l r (inl x) = r (fst x) .fst (snd x .fst .fst , (snd x .fst .snd) , (snd x .snd))
-- --   ΠR-extend-rec l r (inr x) = l x
-- --   ΠR-extend-rec l r (push (x , f) i) = r x .snd f (~ i)

-- --   dable-rec : ∀ {ℓ'} {B : Type ℓ'}
-- --     → (l : ΠR-base → B)
-- --     → ((i : fst I) → Σ[ left ∈ (joinR-gen (fst J) (A i) → B) ]
-- --                         Σ[ pf ∈ (Σ[ g ∈ (Σ[ j ∈ fst J ] (A i j) × ((j : fst J) → A (notI i) j) → B) ]
-- --                         ((a : Pushout (fat→ₗ i) (fat→ᵣ i))
-- --                       → l (PushTop→ΠR-base (i , a))
-- --                        ≡ g ((PushTop→left-push (i , a) .snd) .fst .fst , (PushTop→left-push (i , a) .snd) .fst .snd , (PushTop→left-push (i , a) .snd) .snd))) ]
-- --                           ((t : ΠR-extend) → {!!} ≡ {!!}))
-- --     → dable → B
-- --   dable-rec l f (inl x) = f (fst x) .fst (snd x)
-- --   dable-rec {B = B} l f (inr x) = ΠR-extend-rec {B = B} l (λ i → f i .snd .fst) x
-- --   dable-rec l f (push a i) = {!a!}


-- --   ΠR-extend→J : ΠR-extend → GOAL
-- --   ΠR-extend→J (inl x) = {!left-push!}
-- --   ΠR-extend→J (inr x) = ΠR-base→J  x
-- --   ΠR-extend→J (push (i' , a) i) = {!!}

-- -- {-
-- -- dable→ : Type _
-- -- dable→ = Pushout {A = I × ΠR-extend} {B = Σ[ i ∈ I ] joinR-gen J (A i)} {C = ΠR-extend}
-- --                 (λ a → fst a , ΠR-extend→Π (snd a) (fst a))
-- --                 snd
-- -- -}
