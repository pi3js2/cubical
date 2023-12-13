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

open import Cubical.Foundations.Univalence


module Cubical.Cohomology.EilenbergMacLane.nov.one-big-file where
open import Cubical.HITs.Join
open import Cubical.Functions.FunExtEquiv

evalG : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → B ⊎ (A ≃ B) → A → B
evalG (inl x) _ = x
evalG (inr x) = fst x

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
    EquivJRP∞' (RP∞'∙ ℓ) {B = λ J eq → invEq LiftEquiv (back J (ΠBool→× (fst eq))) ≡ inr eq}
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

funTypePP : ∀ {ℓ ℓ'} {A : Type ℓ} {B : I → A → Type ℓ'}
  {f : (a : A) → B i0 a} {g : (a : A) → B i1 a}
  → ((a : A) → PathP (λ i → B i a) (f a) (g a))
  → PathP (λ i → (a : A) → B i a) f g
funTypePP p i a = p a i

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

joinR-gen : ∀ {ℓ ℓ'} (I : Type ℓ) (A : I → Type ℓ') → Type _
joinR-gen I A = PushoutR (Σ I A) ((i : I) → A i)  λ x f → f (fst x) ≡ snd x

joinR : ∀ {ℓ} (I : RP∞) (A : fst I → Type ℓ) → Type _
joinR I A = PushoutR (Σ (fst I) A) ((i : fst I) → A i)  λ x f → f (fst x) ≡ snd x

joinRD : ∀ {ℓ} (I J : RP∞) (A : fst I → fst J → Type ℓ) → Type _
joinRD I J A = joinR I λ i → joinR J (A i)

private
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

ΠR-extend→Π-alt : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → (fst J) → Type ℓ)
  → 2-elter.ΠR-extend (RP∞'∙ ℓ) (fst J) A
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
  → (x : _) (z : _) → ΠR-extend→Π-alt J A x z ≡ 2-elter.ΠR-extend→Π (RP∞'∙ ℓ) (fst J) A x z
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
  → 2-elter.ΠR-extend (RP∞'∙ ℓ) (fst J) A
  → joinR-gen (fst J) (A true) × joinR-gen (fst J) (A false)
ΠR-extend→× J A t = ΠBool→× {A = λ x → joinR-gen (fst J) (A x)} (ΠR-extend→Π-alt J A t)

ΠR-extend→×-old : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
  → 2-elter.ΠR-extend (RP∞'∙ ℓ) (fst J) A
  → joinR-gen (fst J) (A true) × joinR-gen (fst J) (A false)
ΠR-extend→×-old {ℓ = ℓ} J A t =
  ΠBool→× {A = λ x → joinR-gen (fst J) (A x)}
    (2-elter.ΠR-extend→Π (RP∞'∙ ℓ) (fst J) A t)

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
          → I → I → I → 2-elter.ΠR-extend (RP∞'∙ ℓ) J A
    fill₂-b a a' b b₁ c c₁ x d i i₁ r = Square-filler {A = 2-elter.ΠR-extend (RP∞'∙ ℓ) J A}
          (push (true , inl (CasesBool true (a , b) (a' , b₁) , c₁ , d)))
          (push (false , inl (CasesBool true (a , b) (a' , b₁) , c , x)))
           i i₁ r

    fill₂ : (a a' : J) (b : A true a) (b₁ : A false a')
            (c : (i₂ : J) → A true i₂)
            (c₁ : (i₂ : J) → A false i₂)
            (x : c a ≡ b)
            (d : c₁ a' ≡ b₁)
          → I → I → I → 2-elter.ΠR-extend (RP∞'∙ ℓ) J A
    fill₂ a a' b b₁ c c₁ x d i i₁ r =
      hfill (λ r → λ {(i = i0) → push (true , inl (CasesBool true (a , b) (a' , b₁) , c₁ , d)) (~ i₁)
                 ; (i = i1) → push (false , push ((CasesBool true (a , b) (a' , b₁)) , (CasesBool true c c₁ , CasesBool true x d)) r) i₁
                 ; (i₁ = i0) → push (false , inl (CasesBool true (a , b) (a' , b₁) , c , x)) (~ i)
                 ; (i₁ = i1) → push (true , push ((CasesBool true (a , b) (a' , b₁)) , ((CasesBool true c c₁) , CasesBool true x d)) r) i})
        (inS (Square-filler {A = 2-elter.ΠR-extend (RP∞'∙ ℓ) J A}
          (push (true , inl (CasesBool true (a , b) (a' , b₁) , c₁ , d)))
          (push (false , inl (CasesBool true (a , b) (a' , b₁) , c , x)))
           i i₁ i1)) r

×→ΠR-extend : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
  → joinR-gen (fst J) (A true) × joinR-gen (fst J) (A false)
  → 2-elter.ΠR-extend (RP∞'∙ ℓ) (fst J) A
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
  → 2-elter.ΠR-extend (RP∞'∙ ℓ) (fst J) A
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
                → λ {(k = i0) → ΠR-extend→× J A (Square-filler {A = 2-elter.ΠR-extend (RP∞'∙ ℓ) (fst J) A}
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
  → I → I → I → 2-elter.ΠR-extend (RP∞'∙ ℓ) (fst J) A
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
  → I → I → I → 2-elter.ΠR-extend (RP∞'∙ ℓ) (fst J) A
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
   H = 2-elter.ΠR-extend (RP∞'∙ ℓ) (fst J) A

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
  → Iso (2-elter.ΠR-extend (RP∞'∙ ℓ) (fst J) A)
         (joinR-gen (fst J) (A true) × joinR-gen (fst J) (A false))
Iso.fun (ΠR-extend→×Iso J A) = ΠR-extend→× J A
Iso.inv (ΠR-extend→×Iso J A) = ×→ΠR-extend J A
Iso.rightInv (ΠR-extend→×Iso J A) = ×→ΠR-extend→× {J = J} A
Iso.leftInv (ΠR-extend→×Iso J A) = ΠR-extend→×→ΠR-extend {J = J} A

module _ {ℓ : Level} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
  where
  module ΠR-extend→Π-equiv-base-lemmas where
    p : ΠR-extend→Π-alt J A ≡ 2-elter.ΠR-extend→Π (RP∞'∙ ℓ) (fst J) A
    p = funExt λ x → funExt (ΠR-extend→Π-alt≡ {J = J} A x)

    alt : (2-elter.ΠR-extend (RP∞'∙ ℓ) (fst J) A) ≃ ((x : Bool) → joinR-gen (fst J) (A x))
    alt = isoToEquiv (compIso (ΠR-extend→×Iso J A) (invIso ΠBool×Iso))

    altid : fst alt ≡ ΠR-extend→Π-alt J A
    altid = funExt λ x → funExt (CasesBool true refl refl)

    isEq : isEquiv (ΠR-extend→Π-alt J A)
    isEq = subst isEquiv altid (snd alt)

  open ΠR-extend→Π-equiv-base-lemmas
  ΠR-extend→Π-equiv-base : isEquiv (2-elter.ΠR-extend→Π (RP∞'∙ ℓ) (fst J) A)
  ΠR-extend→Π-equiv-base = transport (λ i → isEquiv (p i)) isEq

ΠR-extend→Π-equiv : ∀ {ℓ} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
  → isEquiv (2-elter.ΠR-extend→Π I (fst J) A)
ΠR-extend→Π-equiv {ℓ} =
  RP∞'pt→Prop (λ _ → isPropΠ2 λ _ _ → isPropIsEquiv _) ΠR-extend→Π-equiv-base


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

EquivJ' : ∀ {ℓ ℓ'} {B : Type ℓ} {P : (A : Type ℓ) → A ≃ B → Type ℓ'}
         → P B (idEquiv _)
         → (A : _) (e : _) → P A e
EquivJ' {P = P} ind A = EquivJ P ind

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
  leftFun : 2-elter.ΠR-extend (RP∞'∙ ℓ) J A → joinR-gen J (A true)
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
  open 2-elter (RP∞'∙ ℓ) J A
  private
    leftFun'≡-inl : (x : left-push)
      → leftFun' (RP∞'∙ ℓ) J A true (inl x) ≡ leftFun J A (inl x)
    leftFun'≡-inl (false , t , p) = refl
    leftFun'≡-inl (true , t , p) = refl

    leftFun'≡-inr : (x : _)
      → leftFun' (RP∞'∙ ℓ) J A true (inr x) ≡ leftFun J A (inr x)
    leftFun'≡-inr (inl x) = refl
    leftFun'≡-inr (inr x) = refl
    leftFun'≡-inr (push a i) = refl

  leftFun'≡ : (x : _) → leftFun' (RP∞'∙ ℓ) J A true x ≡ leftFun J A x
  leftFun'≡ (inl x) = leftFun'≡-inl x
  leftFun'≡ (inr x) = leftFun'≡-inr x
  leftFun'≡ (push (false , b) i) = help i
    where
    main : (b : _) → PathP (λ i → inrR (PushTop→left-push' false b .snd)
                                  ≡ leftFun'≡-inr (PushTop→ΠR-base (false , b)) i)
                            (leftFun'-pushᵣ (RP∞'∙ ℓ) J A false b)
                            (cong (leftFun J A) (push (false , b)))
    main (inl x) = refl
    main (inr x) = refl
    main (push a i) = refl
    help : PathP (λ i → leftFun'-push (RP∞'∙ ℓ) J A false b true i
                        ≡ leftFun J A (push (false , b) i))
                 refl
                 (leftFun'≡-inr (PushTop→ΠR-base (false , b)))
    help = flipSquare (sym (lUnit _) ◁ main b)
  leftFun'≡ (push (true , b) i) = help i
     where
     main : (b : _) → PathP (λ i → inlR (PushTop→left-push' true b .fst)
                                  ≡ leftFun'≡-inr (PushTop→ΠR-base (true , b)) i)
                            (leftFun'-pushₗ (RP∞'∙ ℓ) J A true b)
                            (cong (leftFun J A) (push (true , b)))
     main (inl x) = refl
     main (inr x) = refl
     main (push a i) = refl

     help : PathP (λ i → leftFun'-push (RP∞'∙ ℓ) J A true b true i
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
  → leftFunExt' (RP∞'∙ ℓ) J A true ≡ leftFun J A
leftFunExtId {ℓ = ℓ} J A i = lem i J A
  where
  lem : leftFunExtCurry (RP∞'∙ ℓ) true ≡ leftFun
  lem = JRP∞'∙ leftFun

joinR-Push' : ∀ {ℓ} (I : RP∞' ℓ) (J : Type) (A : fst I → J → Type ℓ) → Type ℓ
joinR-Push' I J A = Pushout {A = fst I × 2-elter.ΠR-extend I J A} (leftFunExt I J A) snd

module _ {ℓ ℓ' : Level} (J : Type) (B : (I : RP∞' ℓ) (A : fst I → J → Type ℓ) → Type ℓ')
  (lef : (I : RP∞' ℓ) (A : fst I → J → Type ℓ) → 2-elter.ΠR-extend I J A → B I A)
  (ri : (A : Bool → J → Type ℓ) → joinR-gen J (A true) → B (RP∞'∙ ℓ) A)
  (coh : ((A : Bool → J → Type ℓ) (x : _) → lef (RP∞'∙ ℓ) A x ≡ ri A (leftFun J A x)))
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
      help' : invEq (2-elter.ΠR-extend→Π (RP∞'∙ ℓ) (fst J) A , ΠR-extend→Π-equiv (RP∞'∙ ℓ) J A)
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

-- more general
module _ {ℓ : Level} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) where
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
  → ΠR-extend** (RP∞'∙ ℓ) J A → joinR-gen (fst J) (A i)
leftMapBool J A i (inl (i' , a , b)) = leftFun'-inl (RP∞'∙ _) (fst J) A i' a b i
leftMapBool J A i (inr x) = leftFun-inr (RP∞'∙ _) J A i x
leftMapBool J A false (push (false , j , a) k) = leftFun-cohₗ** (RP∞'∙ _) J A false j a k
leftMapBool J A false (push (true , j , a) k) = leftFun-cohᵣ** (RP∞'∙ _) J A true j a k
leftMapBool J A true (push (false , j , a) k) = leftFun-cohᵣ** (RP∞'∙ _) J A false j a k
leftMapBool J A true (push (true , j , a) k) = leftFun-cohₗ** (RP∞'∙ _) J A true j a k

leftMapBool≡ : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
  → (i : Bool) (x : ΠR-extend** (RP∞'∙ ℓ) J A)
  → leftMapBool J A i x ≡ leftMap** (RP∞'∙ _) J A i x
leftMapBool≡ J A i (inl x) = refl
leftMapBool≡ J A i (inr x) = refl
leftMapBool≡ J A false (push (false , j , a) i₁) k = lUnit (leftFun-cohₗ** (RP∞'∙ _) J A false j a) k i₁
leftMapBool≡ J A true (push (false , j , a) i₁) k = lUnit (leftFun-cohᵣ** (RP∞'∙ _) J A false j a) k i₁
leftMapBool≡ J A false (push (true , j , a) i₁) k = lUnit (leftFun-cohᵣ** (RP∞'∙ _) J A true j a) k i₁
leftMapBool≡ J A true (push (true , j , a) i₁) k = lUnit (leftFun-cohₗ** (RP∞'∙ _) J A true j a) k i₁

leftFun*-fullBool : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ) (i : Bool)
  → ΠR-extend* (RP∞'∙ ℓ) J A → joinR-gen (fst J) (A i)
leftFun*-fullBool J A i (inl (i' , a , b)) = leftFun'-inl (RP∞'∙ _) (fst J) A i' a b i
leftFun*-fullBool J A i (inr x) = leftFun-inr (RP∞'∙ _) J A i x
leftFun*-fullBool J A false (push (false , a) k) = leftFun-cohₗ (RP∞'∙ _) J A false a k
leftFun*-fullBool J A false (push (true , y) k) = leftFun-cohᵣ (RP∞'∙ _) J A true y k
leftFun*-fullBool J A true (push (false , a) k) = leftFun-cohᵣ (RP∞'∙ _) J A false a k
leftFun*-fullBool J A true (push (true , y) k) = leftFun-cohₗ (RP∞'∙ _) J A true y k


leftFunBool≡' : ∀ {ℓ} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ)
  → (i : Bool) (x : ΠR-extend* (RP∞'∙ ℓ) J A)
  → leftFun*-full (RP∞'∙ _) J A i x ≡ leftFun*-fullBool J A i x
leftFunBool≡' J A i (inl x) = refl
leftFunBool≡' J A i (inr x) = refl
leftFunBool≡' J A false (push (false , a) k) j = lUnit (leftFun-cohₗ (RP∞'∙ _) J A false a) (~ j) k
leftFunBool≡' J A false (push (true , a) k) j = lUnit (leftFun-cohᵣ (RP∞'∙ _) J A true a) (~ j) k
leftFunBool≡' J A true (push (false , a) k) j = lUnit (leftFun-cohᵣ (RP∞'∙ _) J A false a) (~ j) k
leftFunBool≡' J A true (push (true , a) k) j = lUnit (leftFun-cohₗ (RP∞'∙ _) J A true a) (~ j) k

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
                    (λ i k → leftMapBool J A false (push-case (RP∞'∙ ℓ) J A true (push ((inl x , f) , p , (funExt⁻ q)) i) k))
                    (λ i k → push* (x , f false)  (p false) (funExt⁻ q false) (~ k ∨ i))
                    (λ _ _ → inrR (p false)) λ i j → push* (x , f false) (p false) (funExt⁻ q false) i
    fill-inl x p = J> ((λ i j k → leftMapBool J A false
                        (push-case-filler-inl (RP∞'∙ _) J A true x _ p (λ _ → refl) i k (~ j)))
                     ▷ sym (fill1-refl≡ x p))

    fill-inr : (x : Bool ≃ fst J) (p : (i : Bool) (j : fst J) → A i j)
               (f : (i : Bool) → A i (fst x i)) (q : (λ j → p j (fst x j)) ≡ f)
            → Cube (λ j k → push* (fst x false , f false)  (p false) (funExt⁻ q false) (~ k))
                    (fill1 (fst x true) p (f true) (funExt⁻ q true))
                    (λ i k → leftMapBool J A false (push-case (RP∞'∙ ℓ) J A true (push ((inr x , f) , p , (funExt⁻ q)) i) k))
                    (λ i k → push* (fst x false , f false)  (p false) (funExt⁻ q false) (~ k ∨ i))
                    (λ _ _ → inrR (p false))
                    λ i j → push* (fst x false , f false) (p false) (funExt⁻ q false) i
    fill-inr x p = J> ((λ i j k → leftMapBool J A false (push-case-filler-inr (RP∞'∙ _) J A true x _ p (λ _ → refl) i k (~ j)))
                      ▷ sym (fill1-refl≡ (fst x true) p))

    fill2-inl : (x : fst J) (p : (i : Bool) (j : fst J) → A i j)
               (f : (i : Bool) → A i x) (q : (λ j → p j x) ≡ f)
            → Cube (λ j k → inlR (x , f true))
                    (fill2 x p (f true) (funExt⁻ q true))
                    (λ i k → leftMapBool J A true (push-case (RP∞'∙ ℓ) J A true (push ((inl x , f) , p , (funExt⁻ q)) i) k))
                    (λ i k → push* (x , f true)  (p true) (funExt⁻ q true) (k ∧ i))
                    (λ i j → inlR (x , f true))
                    λ i j → push* (x , f true) (p true) (funExt⁻ q true) i
    fill2-inl x p =
      J> ((λ i j k → leftMapBool J A true
           (push-case-filler-inl (RP∞'∙ _) J A true x
             _ p (λ _ → refl) i k (~ j)))
      ▷ sym (fill2-refl≡ x p))

    fill2-inr : (x : Bool ≃ fst J) (p : (i : Bool) (j : fst J) → A i j)
               (f : (i : Bool) → A i (fst x i)) (q : (λ j → p j (fst x j)) ≡ f)
            → Cube (λ j k → inlR (fst x true , f true))
                    (fill2 (fst x true) p (f true) (funExt⁻ q true))
                    (λ i k → leftMapBool J A true (push-case (RP∞'∙ ℓ) J A true (push ((inr x , f) , p , (funExt⁻ q)) i) k))
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
                                  (push-case-filler-inr (RP∞'∙ ℓ) J A true x
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
      → cong (leftMapBool J A false) (push-case (RP∞'∙ ℓ) J A true x)
      ≡ leftFun-cohᵣ (RP∞'∙ ℓ) J A true x
    mainₗ (inl ((inl x , snd₂) , snd₁)) = refl
    mainₗ  (inl ((inr x , snd₂) , snd₁)) = refl
    mainₗ  (inr ((f , a) , g , q)) = fill1 f g a q
    mainₗ  (push ((inl x , f) , p , q) i) j k = fill-inl x p f (funExt q) i j k
    mainₗ (push ((inr x , f) , p , q) i) j k = fill-inr x p f (funExt q) i j k

    mainᵣ : (x : _)
      → cong (leftMapBool J A true) (push-case (RP∞'∙ ℓ) J A true x)
      ≡ leftFun-cohₗ (RP∞'∙ ℓ) J A true x
    mainᵣ (inl ((inl x , snd₂) , snd₁)) = refl
    mainᵣ  (inl ((inr x , snd₂) , snd₁)) = refl
    mainᵣ  (inr ((f , a) , g , q)) = fill2 f g a q
    mainᵣ  (push ((inl x , f) , p , q) i) j k = fill2-inl x p f (funExt q) i j k
    mainᵣ (push ((inr x , f) , p , q) i) j k = fill2-inr x p f (funExt q) i j k


    main : (k : _) (x : _)
      → cong (leftMapBool J A k) (push-case (RP∞'∙ ℓ) J A true x)
      ≡ cong (leftFun*-full (RP∞'∙ ℓ) J A k) (push (true , x))
    main false x = mainₗ x ∙ lUnit _
    main  true x = mainᵣ x ∙ lUnit _

  h1 : (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ) (k : _) → leftMapBool J A k ≡ leftMap** (RP∞'∙ _) J A k
  h1 J A k = funExt (leftMapBool≡ J A k)
  help : (I : RP∞' ℓ) (i' : fst I) (A : fst I → fst J → Type ℓ) (i : fst I) (a : _)
    → cong (leftMap** I J A i) (cong (ΠR-extend→New I J A) (push (i' , a)))
     ≡ cong (leftFun*-full I J A i) (push (i' , a))
  help = JRP∞' λ A k x → (λ j → cong (h1 J A k (~ j))
      (cong (ΠR-extend→New (RP∞'∙ ℓ) J A) (push (true , x))))
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

-- module MEGA {ℓ : Level} {Targ : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) → ΠR-extend** I J A → Type ℓ}
--          (inler : (A : Bool → Bool → Type ℓ) (a : A true true) (b : TotΠ (A false))
--          → Targ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (inl (true , (true , a) , b)))
--          (inr-inr : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) (t : (i : fst I) (j : fst J) → A i j)
--                   → Targ I J A (inr (inr t)))
--          (inr-inl-inl : (I : RP∞' ℓ) (A : fst I → Bool → Type ℓ)
--                         (f : (x : fst I) → A x true)
--                           → Σ[ k ∈ Targ I (RP∞'∙ ℓ) A (inr (inl (inl true , f))) ]
--                             ((p : (i : fst I) (j : Bool) → A i j) (q : (x : fst I) → p x true ≡ f x)
--                           → PathP (λ r → Targ I (RP∞'∙ ℓ) A (inr (push ((inl true , f) , (p , q)) r)))
--                                    k (inr-inr I (RP∞'∙ ℓ) A p)))
--          (inr-inl-inr : (I : RP∞' ℓ) (A : fst I → fst I → Type ℓ) (f : (i : fst I) → A i i)
--            → Σ[ k ∈ Targ I I A (inr (inl (inr (idEquiv (fst I)) , f))) ]
--                ((p : (i : fst I) (j : fst I) → A i j) (q : (x : fst I) → p x x ≡ f x)
--             → PathP (λ r → Targ I I A (inr (push ((inr (idEquiv (fst I)) , f) , (p , q)) r)))
--                                    k (inr-inr I I A p)))
--          (push-inl : (A : Bool → Bool → Type ℓ) (f : (i : fst (RP∞'∙ ℓ)) → A i true)
--            (g : (j : Bool) → A false j) (p : g true ≡ f false)
--          → PathP (λ k → Targ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A
--                     (push (true , true , inl (inl (f , g , p))) k))
--                   (inler A (f true) g)
--                   (inr-inl-inl (RP∞'∙ ℓ) A f .fst))
--          (coh-inr : (A : Bool → Bool → Type ℓ) (g : (i j : Bool) → A i j)
--            → PathP (λ k → Targ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push (true , true , inr g) k))
--                     (inler A (g true true) (g false)) (inr-inr (RP∞'∙ ℓ) (RP∞'∙ ℓ) A g))
--          (coh-eq1 : (A : Bool → Bool → Type ℓ) (g : (i : Bool) → A i i) (f : TotΠ (A false)) (p : f false ≡ g false)
--                      → PathP (λ k → Targ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push (true , true , inl (inr (idEquiv Bool , refl , g , f , p))) k))
--                              (inler A (g true) f)
--                        (inr-inl-inr (RP∞'∙ ℓ) A g .fst))
--          (coh-eq2 : (A : Bool → Bool → Type ℓ) (g : (i j : Bool) → A i j)
--            → SquareP (λ i j → Targ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A
--                                 (push (true , true , push (inr (idEquiv Bool , refl , g)) i) j))
--                      (coh-eq1 A (λ i → g i i) (g false) refl)
--                      (coh-inr A g)
--                      (λ _ → inler A (g true true) (g false))
--                      (inr-inl-inr (RP∞'∙ ℓ) A (λ i → g i i) .snd g (λ _ → refl)))
--           (coh-eq-l : (A : Bool → Bool → Type ℓ) (g : (i j : Bool) → A i j)
--             → SquareP (λ i j → Targ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A
--                                 (push (true , true , push (inl g) i) j))
--                         (push-inl A (λ i₁ → g i₁ true) (g false) (λ _ → g false true))
--                         (coh-inr A g)
--                         (λ _ → inler A (g true true) (g false))
--                         (inr-inl-inl (RP∞'∙ ℓ) A (λ i → g i true) .snd g (λ _ → refl)))
--          where

--   inr-inl-inl* : (I J : RP∞' ℓ) (j : fst J) (A : fst I → fst J → Type ℓ)
--                         (f : (x : fst I) → A x j)
--                           → Σ[ k ∈ Targ I J A (inr (inl (inl j , f))) ]
--                             ((p : (i : fst I) (j : fst J) → A i j) (q : (x : fst I) → p x j ≡ f x)
--                           → PathP (λ r → Targ I J A (inr (push ((inl j , f) , (p , q)) r)))
--                                    k (inr-inr I J A p))
--   inr-inl-inl* I = JRP∞' (inr-inl-inl I)

--   inr-inl-inl*≡ : (I : RP∞' ℓ) (A : fst I → Bool → Type ℓ)
--                         (f : (x : fst I) → A x true)
--                           → inr-inl-inl* I (RP∞'∙ ℓ) true A f ≡ inr-inl-inl I A f
--   inr-inl-inl*≡ I A f i = help i A f
--     where
--     help : inr-inl-inl* I (RP∞'∙ ℓ) true ≡ inr-inl-inl I
--     help = JRP∞'∙ (inr-inl-inl I)

--   inr-inl-inr* : (I J : RP∞' ℓ) (e : fst I ≃ fst J) (A : fst I → fst J → Type ℓ)
--                (f : (i : fst I) → A i (fst e i))
--            → Σ[ k ∈ Targ I J A (inr (inl (inr e , f))) ]
--                ((p : (i : fst I) (j : fst J) → A i j) (q : (x : fst I) → p x (fst e x) ≡ f x)
--             → PathP (λ r → Targ I J A (inr (push ((inr e , f) , (p , q)) r)))
--                                    k (inr-inr I J A p))
--   inr-inl-inr* I = EquivJRP∞' I (inr-inl-inr I)

--   inr-inl-inr*≡ : (I : RP∞' ℓ) (A : fst I → fst I → Type ℓ)
--                (f : (i : fst I) → A i i)
--            → inr-inl-inr* I I (idEquiv (fst I)) A f ≡ inr-inl-inr I A f
--   inr-inl-inr*≡ I A f i = help i A f
--     where
--     help : inr-inl-inr* I I (idEquiv (fst I)) ≡ inr-inl-inr I
--     help = EquivJRP∞'-idEquiv I (inr-inl-inr I)

--   ΠR-extend→Inl' : (J : RP∞' ℓ) (j : fst J) (A : Bool → fst J → Type ℓ)
--      (a : A true j)
--      (b : TotΠ (A false))
--     → Targ (RP∞'∙ ℓ) J A (inl (true , (j , a) , b))
--   ΠR-extend→Inl' = JRP∞' inler

--   ΠR-extend→Inl : (I : RP∞' ℓ) (i : fst I) (J : RP∞' ℓ) (j : fst J) (A : fst I → fst J → Type ℓ)
--      (a : A i j)
--      (b : TotΠ (A (RP'.notI I i)))
--     → Targ I J A (inl (i , (j , a) , b))
--   ΠR-extend→Inl = JRP∞' ΠR-extend→Inl'

--   ΠR-extend→Inl≡ : (A : Bool → Bool → Type ℓ) (a : A true true) (b : TotΠ (A false))
--     → ΠR-extend→Inl (RP∞'∙ ℓ) true (RP∞'∙ ℓ) true A a b ≡ inler A a b
--   ΠR-extend→Inl≡ A a b =
--      (λ k → h k (RP∞'∙ ℓ) true A a b)
--     ∙ λ k → h' k A a b
--     where
--     h : ΠR-extend→Inl (RP∞'∙ ℓ) true ≡ ΠR-extend→Inl'
--     h = JRP∞'∙ ΠR-extend→Inl'

--     h' : ΠR-extend→Inl' (RP∞'∙ ℓ) true ≡ inler
--     h' = JRP∞'∙ inler


--   ΠR-extend→Inr : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) (x : ΠR-base-ab* I J A)
--     → Targ I J A (inr x)
--   ΠR-extend→Inr I J A (inl (inl j , f)) = inr-inl-inl* I J j A f .fst
--   ΠR-extend→Inr I J A (inl (inr e , f)) = inr-inl-inr* I J e A f .fst
--   ΠR-extend→Inr I J A (inr x) = inr-inr I J A x
--   ΠR-extend→Inr I J A (push ((inl j , f) , p , q) i) = inr-inl-inl* I J j A f .snd p q i
--   ΠR-extend→Inr I J A (push ((inr e , f) , p , q) i) = inr-inl-inr* I J e A f .snd p q i

--   push-inr*-ty : (A : Bool → Bool → Type ℓ) (e : Bool ≃ Bool) (pf : fst e true ≡ true)
--     → Type ℓ
--   push-inr*-ty A e pf =
--     Σ[ t ∈
--          (((g : (i : fst (RP∞'∙ ℓ)) → A i (fst e i))
--          (f : (t : Bool) → A false t)
--          (p : f (fst e false) ≡ g false)
--          → PathP (λ k → Targ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push (true , true , inl (inr (e , pf , g , f , p))) k))
--                   (ΠR-extend→Inl (RP∞'∙ ℓ) true (RP∞'∙ ℓ) (fst e true) A (g true) f)
--                   (inr-inl-inr* (RP∞'∙ ℓ) (RP∞'∙ ℓ) e A g .fst))) ]
--          ((g : (i j : Bool) → A i j)
--          → SquareP (λ i j → Targ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A
--                                (push (true , true , push (inr (e , pf , g)) i) j))
--                     (t (λ i → g i (fst e i)) (g false) refl)
--                     (ΠR-extend→Inl≡ A (g true true) (g false) ◁ coh-inr A g)
--                     (λ i → ΠR-extend→Inl (RP∞'∙ ℓ) true (RP∞'∙ ℓ) (pf i) A (g true (pf i)) (g false))
--                     (inr-inl-inr* (RP∞'∙ ℓ) (RP∞'∙ ℓ) e A (λ i → g i (fst e i)) .snd g λ _ → refl))

--   push-inr*-bool-filler : (A : Bool → Bool → Type ℓ)
--     → (g : (i j : Bool) → A i j)
--     → (i j k : _) → _
--   push-inr*-bool-filler A g i j k =
--     hfill (λ k
--       → λ {(i = i0) → doubleWhiskFiller
--                          (ΠR-extend→Inl≡ A (g true true) (g false))
--                          (coh-eq1 A (λ i → g i i) (g false) refl)
--                          (cong fst (sym (inr-inl-inr*≡ (RP∞'∙ ℓ) A (λ i → g i i)))) k j
--           ; (i = i1) → doubleWhiskFiller
--                          (ΠR-extend→Inl≡ A (g true true) (g false))
--                          (coh-inr A g)
--                          (λ _ → inr-inr (RP∞'∙ ℓ) (RP∞'∙ ℓ) A g) k j
--           ; (j = i0) → ΠR-extend→Inl≡ A (g true true) (g false) (~ k)
--           ; (j = i1) → inr-inl-inr*≡ (RP∞'∙ ℓ) A (λ i → g i i) (~ k) .snd g (λ _ → refl) i})
--           (inS (coh-eq2 A g i j))
--           k

--   push-inr*-bool : (A : Bool → Bool → Type ℓ) → push-inr*-ty A (idEquiv _) refl
--   fst (push-inr*-bool A) g f p =
--       ΠR-extend→Inl≡ A (g true) f
--     ◁ coh-eq1 A g f p
--     ▷ cong fst (sym (inr-inl-inr*≡ (RP∞'∙ ℓ) A g))
--   snd (push-inr*-bool A) g i j = push-inr*-bool-filler A g i j i1

--   push-inl*-bool : (A : Bool → Bool → Type ℓ) (g : (i j : Bool) → A i j)
--     → SquareP
--         (λ i j → Targ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push (true , true , push (inl g) i) j))
--         (ΠR-extend→Inl≡ A (g true true) (g false)
--           ◁ push-inl A (λ i₁ → g i₁ true) (g false) refl
--           ▷ cong fst (sym (inr-inl-inl*≡ (RP∞'∙ ℓ) A (λ i₂ → g i₂ true))))
--         (ΠR-extend→Inl≡ A (g true true) (g false) ◁ coh-inr A g)
--         (λ _ → ΠR-extend→Inl (RP∞'∙ ℓ) true (RP∞'∙ ℓ) true A
--                  (g true true) (g (RP'.notI (RP∞'∙ ℓ) true)))
--          (inr-inl-inl* (RP∞'∙ ℓ) (RP∞'∙ ℓ) true A (λ i₁ → g i₁ true) .snd g λ _ → refl)
--   push-inl*-bool A g i j =
--     hcomp (λ k
--       → λ {(i = i0) → doubleWhiskFiller
--                          (ΠR-extend→Inl≡ A (g true true) (g false))
--                          (push-inl A (λ i₁ → g i₁ true) (g false) refl)
--                          (cong fst (sym (inr-inl-inl*≡ (RP∞'∙ ℓ) A (λ i → g i true)))) k j
--           ; (i = i1) → doubleWhiskFiller
--                          (ΠR-extend→Inl≡ A (g true true) (g false))
--                          (coh-inr A g)
--                          (λ _ → inr-inr (RP∞'∙ ℓ) (RP∞'∙ ℓ) A g) k j
--           ; (j = i0) → ΠR-extend→Inl≡ A (g true true) (g false) (~ k)
--           ; (j = i1) → inr-inl-inl*≡ (RP∞'∙ ℓ) A (λ i → g i true) (~ k) .snd g (λ _ → refl) i})
--           (coh-eq-l A g i j)

--   push-inr* : (A : Bool → Bool → Type ℓ) (e : Bool ≃ Bool) (pf : fst e true ≡ true)
--     → push-inr*-ty A e pf
--   push-inr* A = Bool≃Bool-elim-id _ (push-inr*-bool A)

--   push-inr*≡ : (A : Bool → Bool → Type ℓ)
--     → push-inr* A (idEquiv _) refl ≡ push-inr*-bool A
--   push-inr*≡ A = Bool≃Bool-elim-idβ _ (push-inr*-bool A)

--   cohr-b : (A : Bool → Bool → Type ℓ)
--       (x : TY (RP∞'∙ ℓ) (RP∞'∙ ℓ) A true true)
--         → PathP (λ k → Targ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push (true , true , x) k))
--          (ΠR-extend→Inl (RP∞'∙ ℓ) true (RP∞'∙ ℓ) (fst (fst (TY→Lₗ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A true true x))) A
--            (snd (fst (TY→Lₗ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A true true x))) (snd (TY→Lₗ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A true true x)))
--          (ΠR-extend→Inr (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (TY→R (RP∞'∙ ℓ) (RP∞'∙ ℓ) A true true x))
--   cohr-b A (inl (inl (f , g , p))) =
--       ΠR-extend→Inl≡ A (f true) g
--     ◁ push-inl A f g p
--     ▷ cong fst (sym (inr-inl-inl*≡ (RP∞'∙ ℓ) A f))
--   cohr-b A (inl (inr (e , pf , g , p , q))) = push-inr* A e pf .fst g p q
--   cohr-b A (inr x) = ΠR-extend→Inl≡ A (x true true) (x false) ◁ coh-inr A x
--   cohr-b A (push (inl g) i) j = push-inl*-bool A g i j
--   cohr-b A (push (inr (e , pf , g)) i) j = push-inr* A e pf .snd g i j

--   cohr' : (J : RP∞' ℓ) (j : fst J) (A : Bool → fst J → Type ℓ)
--     → (x : TY (RP∞'∙ ℓ) J A true j) → PathP (λ k → Targ (RP∞'∙ ℓ) J A (push (true , j , x) k))
--          (ΠR-extend→Inl (RP∞'∙ ℓ) true J (fst (fst (TY→Lₗ (RP∞'∙ ℓ)  J A true j x))) A
--            (snd (fst (TY→Lₗ (RP∞'∙ ℓ) J A true j x))) (snd (TY→Lₗ (RP∞'∙ ℓ) J A true j x)))
--          (ΠR-extend→Inr (RP∞'∙ ℓ) J A (TY→R (RP∞'∙ ℓ) J A true j x))
--   cohr' = JRP∞' cohr-b

--   cohr : (I : RP∞' ℓ) (i : fst I) (J : RP∞' ℓ) (j : fst J) (A : fst I → fst J → Type ℓ)
--     → (x : TY I J A i j) → PathP (λ k → Targ I J A (push (i , j , x) k))
--          (ΠR-extend→Inl I i J (fst (fst (TY→Lₗ I J A i j x))) A
--            (snd (fst (TY→Lₗ I J A i j x))) (snd (TY→Lₗ I J A i j x)))
--          (ΠR-extend→Inr I J A (TY→R I J A i j x))
--   cohr = JRP∞' cohr'

--   ΠR-extend→ : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) → (x : ΠR-extend** I J A) → Targ I J A x
--   ΠR-extend→ I J A (inl (f , (j , a) , b)) = ΠR-extend→Inl I f J j A a b
--   ΠR-extend→ I J A (inr x) = ΠR-extend→Inr I J A x
--   ΠR-extend→ I J A (push (i , j , x) k) = cohr I i J j A x k

--   module ID (G : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) → (x : ΠR-extend** I J A) → (i : fst I) → Targ I J A x)
--             (G-inler : (A : Bool → Bool → Type ℓ) (a : A true true) (b : TotΠ (A false)) (i : Bool)
--                     → G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (inl (true , (true , a) , b)) i ≡ inler A a b)
--             (G-inr-inr : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) (t : (i : fst I) (j : fst J) → A i j)
--                        (i : fst I)
--                   → G I J A (inr (inr t)) i ≡ inr-inr I J A t)
--             (G-inr-inl-inl₁ : (I : RP∞' ℓ) (A : fst I → Bool → Type ℓ)
--                         (f : (x : fst I) → A x true) (i : fst I)
--                      → (G I (RP∞'∙ ℓ) A (inr (inl (inl true , f))) i)
--                        ≡ inr-inl-inl I A f .fst)
--             (G-inr-inl-inl₂ : (I : RP∞' ℓ) (A : fst I → Bool → Type ℓ)
--                         (f : (x : fst I) → A x true) (i : fst I)
--                         (p : (i₁ : fst I) (j : Bool) → A i₁ j) (q : (x : fst I) → p x true ≡ f x)
--                      → SquareP (λ i j → Targ I (RP∞'∙ ℓ) A (inr (push ((inl true , f) , p , q) j)))
--                                 (λ k → G I (RP∞'∙ ℓ) A (inr (push ((inl true , f) , p , q) k)) i)
--                                 (inr-inl-inl I A f .snd p q)
--                                 (G-inr-inl-inl₁ I A f i)
--                                 (G-inr-inr I (RP∞'∙ ℓ) A p i))
--             (G-inr-inl-inr₁ : (I : RP∞' ℓ) (A : fst I → fst I → Type ℓ)
--               (f : (i : fst I) → A i i) (i : fst I)
--               → G I I A (inr (inl (inr (idEquiv (fst I)) , f))) i ≡ inr-inl-inr I A f .fst)
--             (G-inr-inl-inr₂ : (I : RP∞' ℓ) (A : fst I → fst I → Type ℓ)
--               (f : (i : fst I) → A i i) (p : (i₁ j : fst I) → A i₁ j)
--                  (q : ((x : fst I) → p x x ≡ f x))
--                  (i : fst I)
--               → SquareP (λ i j → Targ I I A (inr (push ((inr (idEquiv (fst I)) , f) , p , q) j)))
--                          (λ k → G I I A (inr (push ((inr (idEquiv (fst I)) , f) , p , q) k)) i)
--                          (inr-inl-inr I A f .snd p q)
--                          (G-inr-inl-inr₁ I A f i)
--                          (G-inr-inr I I A p i))
--             (G-push-inl : (A : Bool → Bool → Type ℓ) (f : (i : fst (RP∞'∙ ℓ)) → A i true)
--               (g : (j : Bool) → A false j) (p : g true ≡ f false) (i : Bool)
--               → SquareP (λ i j → Targ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A
--                                    (push (true , true , inl (inl (f , g , p))) j))
--                          (λ k → G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push (true , true , inl (inl (f , g , p))) k) i)
--                          (push-inl A f g p)
--                          (G-inler A (f true) g i)
--                          (G-inr-inl-inl₁ (RP∞'∙  ℓ) A f i))
--             (G-coh-inr : (A : Bool → Bool → Type ℓ) (g : (i j : Bool) → A i j) (i : Bool)
--            → SquareP (λ i j → Targ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push (true , true , inr g) j))
--                       (λ k → G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push (true , true , inr g) k) i)
--                       (coh-inr A g)
--                       (G-inler A (g true true) (g false) i)
--                       (G-inr-inr (RP∞'∙ ℓ) (RP∞'∙ ℓ) A g i))
--             (G-coh-eq1 : (A : Bool → Bool → Type ℓ) (g : (i : Bool) → A i i) (f : TotΠ (A false)) (p : f false ≡ g false) (x : Bool)
--                      → SquareP (λ i j → Targ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push (true , true , inl (inr (idEquiv Bool , refl , g , f , p))) j))
--                        (λ i → G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push (true , true , inl (inr (idEquiv Bool , refl , g , f , p))) i) x)
--                        (coh-eq1 A g f p)
--                        (G-inler A (g true) f x)
--                        (G-inr-inl-inr₁ (RP∞'∙ ℓ) A g x))
--             (G-coh-eq2 : (A : Bool → Bool → Type ℓ) (g : (i j : Bool) → A i j) (x : Bool)
--            → CubeP (λ k i j → Targ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A
--                                 (push (true , true , push (inr (idEquiv Bool , refl , g)) i) j))
--                (λ i j → G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push (true , true , push (inr (idEquiv Bool , refl , g)) i) j) x)
--                (coh-eq2 A g)
--                (G-coh-eq1 A (λ i → g i i) (g false) refl x)
--                (G-coh-inr A g x)
--                (λ i _ → G-inler A (g true true) (g false) x i)
--                (G-inr-inl-inr₂ (RP∞'∙ ℓ) A (λ i → g i i) g (λ i → refl) x))
--             (G-coh-eq-l :
--               (A : Bool → Bool → Type ℓ) (g : (i j : Bool) → A i j) (x : Bool)
--            → CubeP (λ k i j → Targ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A
--                                 (push (true , true , push (inl g) i) j))
--                (λ i j → G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push (true , true , push (inl g) i) j) x)
--                (coh-eq-l A g)
--                (G-push-inl A (λ i → g i true) (g false) refl x)
--                (G-coh-inr A g x)
--                (λ i _ → G-inler A (g true true) (g false) x i)
--                (G-inr-inl-inl₂ (RP∞'∙ ℓ) A (λ i → g i true) x g (λ _ → refl)))
--             where
--     GID-inl'' : (A : Bool → Bool → Type ℓ)
--       (a : A true true) (f : (j : Bool) → A false j) (x : Bool)
--       → G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (inl (true , (true , a) , f)) x ≡ ΠR-extend→Inl (RP∞'∙ ℓ) true (RP∞'∙ ℓ) true A a f
--     GID-inl'' A a f x = G-inler A a f x ∙ sym (ΠR-extend→Inl≡ A a f)

--     GID-inl' : (J : RP∞' ℓ) (j : fst J) (A : Bool → fst J → Type ℓ)
--       (a : A true j) (f : (j : fst J) → A false j) (x : Bool)
--       → G (RP∞'∙ ℓ) J A (inl (true , (j , a) , f)) x ≡ ΠR-extend→Inl (RP∞'∙ ℓ) true J j A a f
--     GID-inl' = JRP∞' GID-inl''

--     GID-inl : (I : RP∞' ℓ) (i : fst I) (J : RP∞' ℓ) (j : fst J) (A : fst I → fst J → Type ℓ)
--       (a : A i j) (f : (j : fst J) → A (RP'.notI I i) j) (x : fst I)
--       → G I J A (inl (i , (j , a) , f)) x ≡ ΠR-extend→Inl I i J j A a f
--     GID-inl = JRP∞' GID-inl'

--     GID-inl≡ : (A : Bool → Bool → Type ℓ)
--       (a : A true true) (f : (j : Bool) → A false j) (x : Bool)
--         → GID-inl (RP∞'∙ ℓ) true (RP∞'∙ ℓ) true A a f x
--         ≡ GID-inl'' A a f x
--     GID-inl≡ A a f x =
--         (λ i → h1 i (RP∞'∙ ℓ) true A a f x)
--       ∙ λ i → h2 i A a f x
--       where
--       h1 : GID-inl (RP∞'∙ ℓ) true ≡ GID-inl'
--       h1 = JRP∞'∙ GID-inl'

--       h2 : GID-inl' (RP∞'∙ ℓ) true ≡ GID-inl''
--       h2 = JRP∞'∙ GID-inl''

--     G-inr-inl-inl*-TY : (I : RP∞' ℓ) (J : RP∞' ℓ) (j : fst J)
--       (A : fst I → fst J → Type ℓ)
--       (f : (i : fst I) → A i j) (i : fst I)
--       → Type ℓ
--     G-inr-inl-inl*-TY I J j A f i =
--       Σ[ p1 ∈ G I J A (inr (inl (inl j , f))) i
--             ≡ inr-inl-inl* I J j A f .fst ]
--         ((g : (i : fst I) (j : fst J) → A i j)
--          (p : (i : fst I) → g i j ≡ f i)
--          → SquareP (λ k i → Targ I J A (inr (push ((inl j , f) , g , p) i)))
--                      (λ k → G I J A (inr (push ((inl j , f) , g , p) k)) i)
--                      (inr-inl-inl* I J j A f .snd g p)
--                      p1
--                      (G-inr-inr I J A g i))

--     G-inr-inl-inl*-bool-diag-fill : (I : RP∞' ℓ)
--       (A : fst I → Bool → Type ℓ)
--       (f : (i : fst I) → A i true) (i : fst I)
--       (g : _) (p : _) (j k r : _) → _
--     G-inr-inl-inl*-bool-diag-fill I A f i g p j k r =
--       hfill (λ r → λ {(k = i0) → compPath-filler
--                                       (G-inr-inl-inl₁ I A f i)
--                                       (λ i₁ → fst (inr-inl-inl*≡ I A f (~ i₁))) r j
--                         ; (k = i1) → G-inr-inr I (RP∞'∙ ℓ) A g i j
--                         ; (j = i0) → G I (RP∞'∙ ℓ) A (inr (push (((inl true) , f) , g , p) k)) i
--                         ; (j = i1) → snd (inr-inl-inl*≡ I A f (~ r)) g p k})
--               (inS (G-inr-inl-inl₂ I A f i g p j k))
--               r

--     G-inr-inl-inl*-bool : (I : RP∞' ℓ)
--       (A : fst I → Bool → Type ℓ)
--       (f : (i : fst I) → A i true) (i : fst I)
--       → G-inr-inl-inl*-TY I (RP∞'∙ ℓ) true A f i
--     fst (G-inr-inl-inl*-bool I A f i) =
--       G-inr-inl-inl₁ I A f i ∙ cong fst (sym (inr-inl-inl*≡ I A f))
--     snd (G-inr-inl-inl*-bool I A f i) g p j k =
--       G-inr-inl-inl*-bool-diag-fill I A f i g p j k i1

--     abstract
--       G-inr-inl-inl*-full : (I : RP∞' ℓ) (J : RP∞' ℓ) (j : fst J)
--         (A : fst I → fst J → Type ℓ)
--         (f : (i : fst I) → A i j) (i : fst I)
--         → G-inr-inl-inl*-TY I J j A f i
--       G-inr-inl-inl*-full I = JRP∞' (G-inr-inl-inl*-bool I)

--       G-inr-inl-inl*-full≡ : (I : RP∞' ℓ)
--         (A : fst I → Bool → Type ℓ)
--         (f : (i : fst I) → A i true) (i : fst I)
--         → G-inr-inl-inl*-full I (RP∞'∙ ℓ) true A f i ≡ G-inr-inl-inl*-bool I A f i
--       G-inr-inl-inl*-full≡ I A f i w = cool w A f i
--         where
--         cool : G-inr-inl-inl*-full I (RP∞'∙ ℓ) true ≡ G-inr-inl-inl*-bool I
--         cool = JRP∞'∙ (G-inr-inl-inl*-bool I)

--     G-inr-inl-inl*₁ : (I : RP∞' ℓ) (J : RP∞' ℓ) (j : fst J) (A : fst I → fst J → Type ℓ)
--       → (f : (i : fst I) → A i j)
--       → (i : fst I)
--       → G I J A (inr (inl (inl j , f))) i ≡ inr-inl-inl* I J j A f .fst
--     G-inr-inl-inl*₁ I = JRP∞' λ A f x
--       → G-inr-inl-inl₁ I A f x ∙ cong fst (sym (inr-inl-inl*≡ I A f))

--     G-inr-inl-inr*-TY : (I J : RP∞' ℓ) (e : fst I ≃ fst J)
--       (A : fst I → fst J → Type ℓ)
--       (i : fst I)
--       → Type ℓ
--     G-inr-inl-inr*-TY I J e A i =
--       Σ[ p1 ∈ ((f : (i : fst I) → A i (fst e i))
--               → G I J A (inr (inl (inr e , f))) i
--                ≡ ΠR-extend→ I J A (inr (inl (inr e , f)))) ]
--           ((f : (i₁ : fst I) → A i₁ (fst e i₁))
--                 (g : (i : fst I) (j : fst J) → A i j)
--                 (p : (i : fst I) → g i (fst e i) ≡ f i)
--           → SquareP (λ k j → Targ I J A (inr (push ((inr e , f) , g , p) j)))
--                      (λ j → G I J A (inr (push ((inr e , f) , g , p) j)) i)
--                      (inr-inl-inr* I J e A f .snd g p)
--                      (p1 f)
--                      (G-inr-inr I J A g i))

--     G-inr-inl-inr*-diag-fill : (I : RP∞' ℓ)
--       (A : fst I → fst I → Type ℓ)
--       (f : _) (g : _) (p : _)
--       (i : fst I) (j k r : _)
--       → _
--     G-inr-inl-inr*-diag-fill I A f g p i j k r =
--       hfill (λ r → λ {(k = i0) → compPath-filler
--                                     (G-inr-inl-inr₁ I A f i)
--                                     (λ i₁ → fst (inr-inl-inr*≡ I A f (~ i₁))) r j
--                       ; (k = i1) → G-inr-inr I I A g i j
--                       ; (j = i0) → G I I A (inr (push (((inr (idEquiv (fst I))) , f) , g , p) k)) i
--                       ; (j = i1) → snd (inr-inl-inr*≡ I A f (~ r)) g p k})
--             (inS (G-inr-inl-inr₂ I A f g p i j k))
--             r

--     G-inr-inl-inr*-diag : (I : RP∞' ℓ)
--       (A : fst I → fst I → Type ℓ)
--       (i : fst I)
--       → G-inr-inl-inr*-TY I I (idEquiv (fst I)) A i
--     fst (G-inr-inl-inr*-diag I A i) f =
--         G-inr-inl-inr₁ I A f i
--       ∙ cong fst (sym (inr-inl-inr*≡ I A f))
--     snd (G-inr-inl-inr*-diag I A i) f g p j k =
--       G-inr-inl-inr*-diag-fill I A f g p i j k i1

--     abstract
--       G-inr-inl-inr*-full : (I J : RP∞' ℓ) (e : fst I ≃ fst J)
--         (A : fst I → fst J → Type ℓ)
--         (i : fst I)
--         → G-inr-inl-inr*-TY I J e A i
--       G-inr-inl-inr*-full I =
--         EquivJRP∞' I (G-inr-inl-inr*-diag I)

--       G-inr-inl-inr*≡ : (I : RP∞' ℓ)
--         (A : fst I → fst I → Type ℓ)
--         (i : fst I)
--         → G-inr-inl-inr*-full I I (idEquiv _) A i ≡ G-inr-inl-inr*-diag I A i
--       G-inr-inl-inr*≡ I A i k = help k A i
--         where
--         help : G-inr-inl-inr*-full I I (idEquiv _) ≡ G-inr-inl-inr*-diag I
--         help = EquivJRP∞'-idEquiv I (G-inr-inl-inr*-diag I)

--     GID-inr : (I : RP∞' ℓ) (i : fst I) (J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) (x : _)
--       → G I J A (inr x) i
--       ≡ ΠR-extend→ I J A (inr x)
--     GID-inr I i J A (inl (inl x , f)) = G-inr-inl-inl*-full I J x A f i .fst
--     GID-inr I i J A (inl (inr e , f)) = G-inr-inl-inr*-full I J e A i .fst f
--     GID-inr I i J A (inr x) = G-inr-inr I J A x i
--     GID-inr I i J A (push ((inl x , f) , g , p) j) k = G-inr-inl-inl*-full I J x A f i .snd g p k j
--     GID-inr I i J A (push ((inr x , f) , g , p) j) k = G-inr-inl-inr*-full I J x A i .snd f g p k j

--     module _ (A : Bool → Bool → Type ℓ)
--             (k : Bool)
--             (x : _) where

--       help-inr''-fill : (i j r : _)
--               → _
--       help-inr''-fill i j r =
--         hfill (λ r → λ { (i = i0) → G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push (true , true , inr x) j) k
--                         ; (i = i1) → doubleWhiskFiller (ΠR-extend→Inl≡ A (x true true) (x false)) (coh-inr A x) refl r j
--                         ; (j = i0) → compPath-filler
--                                         (G-inler A (x true true) (x false) k)
--                                         (sym (ΠR-extend→Inl≡ A (x true true) (x false))) r i
--                         ; (j = i1) → G-inr-inr (RP∞'∙ ℓ) (RP∞'∙ ℓ) A x k i})
--               (inS (G-coh-inr A x k i j))
--               r

--       help-inr'' :
--           SquareP (λ t s → Targ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push (true , true , inr x) s))
--              (λ s → G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push (true , true , inr x) s) k)
--              (ΠR-extend→Inl≡ A (x true true) (x false) ◁ coh-inr A x)
--              (G-inler A (x true true) (x false) k ∙ sym (ΠR-extend→Inl≡ A (x true true) (x false)))
--              (G-inr-inr (RP∞'∙ ℓ) (RP∞'∙ ℓ) A x k)
--       help-inr'' i j = help-inr''-fill i j i1

--       help-inr'-fill : (i j r : _)
--               → _
--       help-inr'-fill i j r =
--         hfill (λ r → λ { (i = i0) →  G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push (true , true , inr x) j) k
--                         ; (i = i1) → (ΠR-extend→Inl≡ A (x true true) (x false) ◁ coh-inr A x) j
--                         ; (j = i0) → GID-inl≡ A (x true true) (x false) k (~ r) i
--                         ; (j = i1) → G-inr-inr (RP∞'∙ ℓ) (RP∞'∙ ℓ) A x k i})
--                (inS (help-inr'' i j))
--               r

--       help-inr' :
--          SquareP (λ t s → Targ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push (true , true , inr x) s))
--              (λ s → G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push (true , true , inr x) s) k)
--              (ΠR-extend→Inl≡ A (x true true) (x false) ◁ coh-inr A x)
--              (GID-inl (RP∞'∙ ℓ) true (RP∞'∙ ℓ) true A (x true true)
--               (x false) k)
--              (G-inr-inr (RP∞'∙ ℓ) (RP∞'∙ ℓ) A x k)
--       help-inr' i j = help-inr'-fill i j i1

--     module _ (A : Bool → Bool → Type ℓ)
--             (k : Bool) (f : (i : Bool) → A i true) (g : (j : Bool) → A false j)
--             (p : g true ≡ f false) where

--       help-inl-inl-btm-fill : (i j r : _) → _
--       help-inl-inl-btm-fill i j r =
--         hfill (λ r → λ {(i = i0) → G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A
--                                     (push (true , true , inl (inl (f , g , p))) j) k
--                      ; (i = i1) → doubleWhiskFiller
--                                     (ΠR-extend→Inl≡ A (f true) g)
--                                     (push-inl A f g p)
--                                     (sym (cong fst (inr-inl-inl*≡ (RP∞'∙ ℓ) A f))) r j
--                      ; (j = i0) → compPath-filler
--                                       (G-inler A (f true) g k)
--                                       (sym (ΠR-extend→Inl≡ A (f true) g)) r i
--                      ; (j = i1) → compPath-filler
--                                     (G-inr-inl-inl₁ (RP∞'∙ ℓ) A f k)
--                                     (λ i₁ → fst (inr-inl-inl*≡ (RP∞'∙ ℓ) A f (~ i₁))) r i
--                      })
--               (inS (G-push-inl A f g p k i j))
--               r


--       help-inl-inl :
--              SquareP (λ t s → Targ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A
--                                 (push (true , true , inl (inl (f , g , p))) s))
--                 (λ s → G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A
--                     (push (true , true , inl (inl (f , g , p))) s) k)
--                 (cohr-b A (inl (inl (f , g , p))))
--                 (GID-inl (RP∞'∙ ℓ) true (RP∞'∙ ℓ) true A (f true) g k)
--                 (G-inr-inl-inl*-full (RP∞'∙ ℓ) (RP∞'∙ ℓ) true A f k .fst)
--       help-inl-inl i j =
--         hcomp (λ r → λ {(i = i0) → G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A
--                                     (push (true , true , inl (inl (f , g , p))) j) k
--                      ; (i = i1) → cohr-b A (inl (inl (f , g , p))) j
--                      ; (j = i0) → GID-inl≡ A (f true) g k (~ r) i
--                      ; (j = i1) → G-inr-inl-inl*-full≡ (RP∞'∙ ℓ) A f k (~ r) .fst i})
--          (help-inl-inl-btm-fill i j i1)

--     help-inl-inr-TY : (A : Bool → Bool → Type ℓ) (k : Bool)
--       (e : Bool ≃ Bool) (pf : fst e true ≡ true)
--         → Type ℓ
--     help-inl-inr-TY A k e pf =
--       Σ[ h ∈ (
--         (f : (i : Bool) → A i (fst e i))
--         (g : (j : Bool) → A false j)
--         (p : g (fst e false) ≡ f false)
--         → SquareP (λ i j → Targ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A
--                              (push (true , true , inl (inr (e , pf , f , g , p))) j))
--                   (λ j → G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push (true , true , inl (inr (e , pf , f , g , p))) j) k)
--                   (push-inr* A e pf .fst f g p)
--                   (GID-inl (RP∞'∙ ℓ) true (RP∞'∙ ℓ) (fst e true) A (f true) g k)
--                   (G-inr-inl-inr*-full (RP∞'∙ ℓ) (RP∞'∙ ℓ) e A k .fst f)
--                ) ]
--           ((g : (i j : Bool) → A i j)
--           → (CubeP (λ j i l → Targ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A
--                 (push (true , true , push (inr (e , pf , g)) i) l))
--                 (λ i l → G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push (true , true , push (inr (e , pf , g)) i) l) k)
--                 (push-inr* A e pf .snd g) -- j = i1
--                 (h (λ i₁ → g i₁ (fst e i₁)) (g false) refl)
--                 (help-inr' A k g)
--                 (λ j i → GID-inl (RP∞'∙ ℓ) true (RP∞'∙ ℓ) (pf i) A (g true (pf i)) (g (RP'.notI (RP∞'∙ ℓ) true)) k j)
--                 (G-inr-inl-inr*-full (RP∞'∙ ℓ) (RP∞'∙ ℓ) e A k .snd (λ i₁ → g i₁ (fst e i₁)) g (λ _ → refl))))

--     help-inl-inr-id : (A : Bool → Bool → Type ℓ) (k : Bool)
--       → help-inl-inr-TY A k (idEquiv _) refl
--     fst (help-inl-inr-id A k) f g p i j =
--       hcomp (λ r → λ {(i = i0) → G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push (true , true , inl (inr (idEquiv Bool , refl , f , g , p))) j) k
--                      ; (i = i1) → push-inr*≡ A (~ r) .fst f g p j
--                      ; (j = i0) → GID-inl≡ A (f true) g k (~ r) i
--                      ; (j = i1) → G-inr-inl-inr*≡ (RP∞'∙ ℓ) A k (~ r) .fst f i})
--        (hcomp (λ r → λ {(i = i0) → G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push (true , true , inl (inr (idEquiv Bool , refl , f , g , p))) j) k
--                      ; (i = i1) → doubleWhiskFiller
--                                      (ΠR-extend→Inl≡ A (f true) g)
--                                      (coh-eq1 A f g p)
--                                      (cong fst (sym (inr-inl-inr*≡ (RP∞'∙ ℓ) A f)))
--                                      r j
--                      ; (j = i0) → compPath-filler (G-inler A (f true) g k) (sym (ΠR-extend→Inl≡ A (f true) g)) r i
--                      ; (j = i1) → compPath-filler (G-inr-inl-inr₁ (RP∞'∙ ℓ) A f k)
--                                     (λ i₁ → fst (inr-inl-inr*≡ (RP∞'∙ ℓ) A f (~ i₁)))
--                                     r i})
--               (G-coh-eq1 A f g p k i j))
--     snd (help-inl-inr-id A k) g j i l =
--       hcomp (λ r → λ {(i = i1) → help-inr'-fill A k g j l r
--                      ; (j = i0) → G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push (true , true , push (inr (idEquiv Bool , refl , g)) i) l) k
--                      ; (j = i1) → push-inr*≡ A (~ r) .snd g i l
--                      ; (l = i0) → GID-inl≡ A (g true true) (g false) k (~ r) j
--                      ; (l = i1) → G-inr-inl-inr*≡ (RP∞'∙ ℓ) A k (~ r) .snd (λ i → g i i) g (λ _ → refl) j i
--                      })
--        (hcomp (λ r → λ {(i = i1) → help-inr''-fill A k g j l r
--                      ; (j = i0) → G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push (true , true , push (inr (idEquiv Bool , refl , g)) i) l) k
--                      ; (j = i1) → push-inr*-bool-filler A g i l r
--                      ; (l = i0) → compPath-filler (G-inler A (g true true) (g false) k)
--                                                    (sym (ΠR-extend→Inl≡ A (g true true) (g false))) r j
--                      ; (l = i1) → G-inr-inl-inr*-diag-fill (RP∞'∙ ℓ) A (λ i → g i i) g (λ _ → refl) k j i r
--                      })
--              (G-coh-eq2 A g k j i l))

--     help-inl-inr : (A : Bool → Bool → Type ℓ) (k : Bool)
--       (e : Bool ≃ Bool) (pf : fst e true ≡ true)
--       → help-inl-inr-TY A k e pf
--     help-inl-inr A k = Bool≃Bool-elim-id _ (help-inl-inr-id A k)

--     help' : (A : Bool → Bool → Type ℓ)
--             (k : Bool)
--             (a : TY (RP∞'∙ ℓ) (RP∞'∙ ℓ) A true true)
--          → SquareP (λ t s → Targ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push (true , true , a) s))
--                     (λ s → G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push (true , true , a) s) k)
--                     (cohr-b A a)
--                     (GID-inl (RP∞'∙ ℓ) true (RP∞'∙ ℓ)
--                       (fst (fst (TY→Lₗ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A true true a))) A
--                       (snd (fst (TY→Lₗ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A true true a)))
--                       (snd (TY→Lₗ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A true true a)) k)
--                     (GID-inr (RP∞'∙ ℓ) k (RP∞'∙ ℓ) A
--                       (TY→R (RP∞'∙ ℓ) (RP∞'∙ ℓ) A true true a))
--     help' A k (inl (inl (f , g , p))) = help-inl-inl A k f g p
--     help' A k (inl (inr (e , pf , f , g , p))) = help-inl-inr A k e pf .fst f g p
--     help' A k (inr x) = help-inr' A k x
--     help' A k (push (inl g) i) j l =
--       hcomp (λ r → λ {(i = i1) → help-inr'-fill A k g j l r
--                     ; (j = i0) → G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push (true , true , push (inl g) i) l) k
--                     ; (j = i1) → push-inl*-bool A g i l
--                     ; (l = i0) → GID-inl≡ A (g true true) (g false) k (~ r) j
--                     ; (l = i1) → G-inr-inl-inl*-full≡ (RP∞'∙ ℓ) A (λ i → g i true) k (~ r) .snd g (λ _ → refl) j i
--                     })
--             (hcomp (λ r → λ {
--                     (i = i0) → help-inl-inl-btm-fill A k (λ i → g i true) (g false) refl j l r
--                     ; (i = i1) → help-inr''-fill A k g j l r
--                     ; (j = i0) → G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push (true , true , push (inl g) i) l) k
--                     ; (l = i0) → help-inl-inl-btm-fill A k (λ i₁ → g i₁ true) (g false) (λ _ → g false true) j i0 r
--                     ; (l = i1) → G-inr-inl-inl*-bool-diag-fill (RP∞'∙ ℓ) A (λ i → g i true) k g (λ _ → refl) j i r
--                     })
--               (G-coh-eq-l A g k j i l))
--     help' A k (push (inr (e , pf , g)) i) j l = help-inl-inr A k e pf .snd g j i l

--     GID : (I : RP∞' ℓ) (i : fst I) (J : RP∞' ℓ)
--       (A : fst I → fst J → Type ℓ) (x : _)
--       → G I J A x i ≡ ΠR-extend→ I J A x
--     GID I k J A (inl (i , (j , a) , f)) = GID-inl I i J j A a f k
--     GID I k J A (inr x) = GID-inr I k J A x
--     GID I k J A (push (i , j , a) s) t = help I i J j A k a t s
--       where
--       cohr-id : (A : Bool → Bool → Type ℓ) (k : Bool)
--         (a : TY (RP∞'∙ ℓ) (RP∞'∙ ℓ) A true true)
--         → cohr (RP∞'∙ ℓ) true (RP∞'∙ ℓ) true A a
--         ≡ cohr-b A a
--       cohr-id A k a = (λ i → h i (RP∞'∙ ℓ) true A a)
--                      ∙ λ i → h2 i A a
--         where
--         h : cohr (RP∞'∙ ℓ) true ≡ cohr'
--         h = JRP∞'∙ cohr'

--         h2 : cohr' (RP∞'∙ ℓ) true ≡ cohr-b
--         h2 = JRP∞'∙ cohr-b

--       help : (I : RP∞' ℓ) (i : fst I) (J : RP∞' ℓ) (j : fst J)
--              (A : fst I → fst J → Type ℓ)
--              (k : fst I) (a : TY I J A i j)
--           → SquareP (λ t s → Targ I J A (push (i , j , a) s))
--                      (λ s → G I J A (push (i , j , a) s) k)
--                      (cohr I i J j A a)
--                      (GID-inl I i J (fst (fst (TY→Lₗ I J A i j a))) A
--                        (snd (fst (TY→Lₗ I J A i j a))) (snd (TY→Lₗ I J A i j a)) k)
--                      (GID-inr I k J A (TY→R I J A i j a))
--       help = JRP∞' (JRP∞' λ A k a → help' A k a ▷ sym (cohr-id A k a))


-- EquivJ* : ∀ {ℓ ℓ'} (C : (A : Bool → Bool → Type ℓ) → Type ℓ)
--                  {T1 : (A : Bool → Bool → Type ℓ) → C A → Type ℓ}
--                  {P : (T2 : (A : Bool → Bool → Type ℓ) → C A → Type ℓ)
--                    → ((A : Bool → Bool → Type ℓ) (c : C A) → T1 A c ≃ T2 A c) → Type ℓ'}
--             → P T1 (λ A c → idEquiv _)
--             → (T1 : _) (e : _) → P T1 e
                 
-- EquivJ* {ℓ = ℓ} C {T1 = T1} {P = P} q T2 e =
--   subst (λ x → P (fst x) (snd x)) (isContr→isProp help (T1 , _) (T2 , e)) q
--   where
--   help : isContr (Σ[ T2 ∈ ((A : Bool → Bool → Type ℓ) → C A → Type ℓ) ]
--                     ((A : _) (c : _) → T1 A c ≃ T2 A c))
--   help = isOfHLevelRetractFromIso 0
--           (Σ-cong-iso-snd (λ T1
--             → compIso (codomainIsoDep
--               (λ A → compIso (codomainIsoDep
--                 (λ a → invIso (equivToIso univalence))) funExtIso)) funExtIso))
--           (isContrSingl {A = (A : Bool → Bool → Type ℓ) → C A → Type ℓ} T1)


-- record 𝕄 {ℓ : Level} (Targ : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) → ΠR-extend** I J A → Type ℓ)
--         (Targ' : (A : Bool → Bool → Type ℓ) → ΠR-extend** (RP∞'∙ ℓ) (RP∞'∙ ℓ) A → Type ℓ)
--         (e : (A : Bool → Bool → Type ℓ) (x : ΠR-extend** (RP∞'∙ ℓ) (RP∞'∙ ℓ) A)
--           → Targ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A x ≃ Targ' A x)
--         (G : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) → (x : ΠR-extend** I J A) → (i : fst I) → Targ I J A x)
--         (pushG : (A : Bool → Bool → Type ℓ) (x : newBack (RP∞'∙ ℓ) (RP∞'∙ ℓ) A) (a : Bool)
--           → PathP (λ i → Targ' A (push x i))
--                    (fst (e A _) (G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (inl (newBack→ₗ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A x)) a))
--                    (fst (e A _) (G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (inr (newBack→ᵣ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A x)) a))) : Type (ℓ-suc ℓ)
--         where
--   field
--     inler : (A : Bool → Bool → Type ℓ) (a : A true true) (b : TotΠ (A false))
--       → Targ' A (inl (true , (true , a) , b))
--     inr-inr : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) (t : (i : fst I) (j : fst J) → A i j)
--            → Targ I J A (inr (inr t))
--     inr-inl-inl : (I : RP∞' ℓ) (A : fst I → Bool → Type ℓ)
--                  (f : (x : fst I) → A x true)
--                    → Σ[ k ∈ Targ I (RP∞'∙ ℓ) A (inr (inl (inl true , f))) ]
--                      ((p : (i : fst I) (j : Bool) → A i j) (q : (x : fst I) → p x true ≡ f x)
--                    → PathP (λ r → Targ I (RP∞'∙ ℓ) A (inr (push ((inl true , f) , (p , q)) r)))
--                             k (inr-inr I (RP∞'∙ ℓ) A p))
--     inr-inl-inr : (I : RP∞' ℓ) (A : fst I → fst I → Type ℓ) (f : (i : fst I) → A i i)
--          → Σ[ k ∈ Targ I I A (inr (inl (inr (idEquiv (fst I)) , f))) ]
--              ((p : (i : fst I) (j : fst I) → A i j) (q : (x : fst I) → p x x ≡ f x)
--           → PathP (λ r → Targ I I A (inr (push ((inr (idEquiv (fst I)) , f) , (p , q)) r)))
--                                  k (inr-inr I I A p))
--     push-inl : (A : Bool → Bool → Type ℓ) (f : (i : Bool) → A i true)
--      (g : (j : Bool) → A false j) (p : g true ≡ f false)
--      → PathP (λ k → Targ' A
--               (push (true , true , inl (inl (f , g , p))) k))
--             (inler A (f true) g)
--             (fst (e A _) (inr-inl-inl (RP∞'∙ ℓ) A f .fst))
--     coh-inr : (A : Bool → Bool → Type ℓ) (g : (i j : Bool) → A i j)
--        → PathP (λ k → Targ' A (push (true , true , inr g) k))
--                 (inler A (g true true) (g false))
--                 (fst (e A _) (inr-inr (RP∞'∙ ℓ) (RP∞'∙ ℓ) A g))
--     coh-eq1 : (A : Bool → Bool → Type ℓ) (g : (i : Bool) → A i i) (f : TotΠ (A false)) (p : f false ≡ g false)
--                  → PathP (λ k → Targ' A (push (true , true , inl (inr (idEquiv Bool , refl , g , f , p))) k))
--                          (inler A (g true) f)
--                    (fst (e A _) (inr-inl-inr (RP∞'∙ ℓ) A g .fst))
--     coh-eq2 : (A : Bool → Bool → Type ℓ) (g : (i j : Bool) → A i j)
--        → SquareP (λ i j → Targ' A
--                             (push (true , true , push (inr (idEquiv Bool , refl , g)) i) j))
--                  (coh-eq1 A (λ i → g i i) (g false) refl)
--                  (coh-inr A g)
--                  (λ _ → inler A (g true true) (g false))
--                  λ i → fst (e A _) (inr-inl-inr (RP∞'∙ ℓ) A (λ i₁ → g i₁ i₁) .snd g (λ _ → refl) i)
--     coh-eq-l : (A : Bool → Bool → Type ℓ) (g : (i j : Bool) → A i j)
--        → SquareP (λ i j → Targ' A
--                            (push (true , true , push (inl g) i) j))
--                    (push-inl A (λ i₁ → g i₁ true) (g false) (λ _ → g false true))
--                    (coh-inr A g)
--                    (λ _ → inler A (g true true) (g false))
--                    (λ i → fst (e A _) (inr-inl-inl (RP∞'∙ ℓ) A (λ i → g i true) .snd g (λ _ → refl) i))
--     G-inler : (A : Bool → Bool → Type ℓ) (a : A true true) (b : TotΠ (A false)) (i : Bool)
--                     → fst (e A _) (G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (inl (true , (true , a) , b)) i) ≡ inler A a b
--     G-inr-inr : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) (t : (i : fst I) (j : fst J) → A i j)
--                        (i : fst I)
--                   → G I J A (inr (inr t)) i ≡ inr-inr I J A t
--     G-inr-inl-inl₁ : (I : RP∞' ℓ) (A : fst I → Bool → Type ℓ)
--                         (f : (x : fst I) → A x true) (i : fst I)
--                      → (G I (RP∞'∙ ℓ) A (inr (inl (inl true , f))) i)
--                        ≡ inr-inl-inl I A f .fst
--     G-inr-inl-inl₂ : (I : RP∞' ℓ) (A : fst I → Bool → Type ℓ)
--                         (f : (x : fst I) → A x true) (i : fst I)
--                         (p : (i₁ : fst I) (j : Bool) → A i₁ j) (q : (x : fst I) → p x true ≡ f x)
--                      → SquareP (λ i j → Targ I (RP∞'∙ ℓ) A (inr (push ((inl true , f) , p , q) j)))
--                                 (λ k → G I (RP∞'∙ ℓ) A (inr (push ((inl true , f) , p , q) k)) i)
--                                 (inr-inl-inl I A f .snd p q)
--                                 (G-inr-inl-inl₁ I A f i)
--                                 (G-inr-inr I (RP∞'∙ ℓ) A p i)
--     G-inr-inl-inr₁ : (I : RP∞' ℓ) (A : fst I → fst I → Type ℓ)
--               (f : (i : fst I) → A i i) (i : fst I)
--               → G I I A (inr (inl (inr (idEquiv (fst I)) , f))) i ≡ inr-inl-inr I A f .fst
--     G-inr-inl-inr₂ : (I : RP∞' ℓ) (A : fst I → fst I → Type ℓ)
--               (f : (i : fst I) → A i i) (p : (i₁ j : fst I) → A i₁ j)
--                  (q : ((x : fst I) → p x x ≡ f x))
--                  (i : fst I)
--               → SquareP (λ i j → Targ I I A (inr (push ((inr (idEquiv (fst I)) , f) , p , q) j)))
--                          (λ k → G I I A (inr (push ((inr (idEquiv (fst I)) , f) , p , q) k)) i)
--                          (inr-inl-inr I A f .snd p q)
--                          (G-inr-inl-inr₁ I A f i)
--                          (G-inr-inr I I A p i)

--     G-push-inl : (A : Bool → Bool → Type ℓ) (f : (i : fst (RP∞'∙ ℓ)) → A i true)
--               (g : (j : Bool) → A false j) (p : g true ≡ f false) (i : Bool)
--               → SquareP (λ i j → Targ' A
--                                    (push (true , true , inl (inl (f , g , p))) j))
--                          (λ k → pushG A (true , true , inl (inl (f , g , p))) i k)
--                          (push-inl A f g p)
--                          (G-inler A (f true) g i)
--                          λ k → fst (e A _) (G-inr-inl-inl₁ (RP∞'∙  ℓ) A f i k)
--     G-coh-inr : (A : Bool → Bool → Type ℓ) (g : (i j : Bool) → A i j) (i : Bool)
--            → SquareP (λ i j → Targ' A (push (true , true , inr g) j))
--                       (pushG A (true , true , inr g) i)
--                       (coh-inr A g)
--                       (G-inler A (g true true) (g false) i)
--                       (λ k → fst (e A _) (G-inr-inr (RP∞'∙ ℓ) (RP∞'∙ ℓ) A g i k))
--     G-coh-eq1 : (A : Bool → Bool → Type ℓ) (g : (i : Bool) → A i i) (f : TotΠ (A false)) (p : f false ≡ g false) (x : Bool)
--                      → SquareP (λ i j → Targ' A (push (true , true , inl (inr (idEquiv Bool , refl , g , f , p))) j))
--                        (pushG A (true , true , inl (inr (idEquiv Bool , refl , g , f , p))) x)
--                        (coh-eq1 A g f p)
--                        (G-inler A (g true) f x)
--                        (λ t → fst (e A _) (G-inr-inl-inr₁ (RP∞'∙ ℓ) A g x t))
--     G-coh-eq2 : (A : Bool → Bool → Type ℓ) (g : (i j : Bool) → A i j) (x : Bool)
--            → CubeP (λ k i j → Targ' A
--                                 (push (true , true , push (inr (idEquiv Bool , refl , g)) i) j))
--                (λ i j → pushG A (true , true , push (inr (idEquiv Bool , refl , g)) i) x j)
--                (coh-eq2 A g)
--                (G-coh-eq1 A (λ i → g i i) (g false) refl x)
--                (G-coh-inr A g x)
--                (λ i _ → G-inler A (g true true) (g false) x i)
--                λ s t → fst (e A _) (G-inr-inl-inr₂ (RP∞'∙ ℓ) A (λ i → g i i) g (λ i → refl) x s t)
--     G-coh-eq-l :
--               (A : Bool → Bool → Type ℓ) (g : (i j : Bool) → A i j) (x : Bool)
--            → CubeP (λ k i j → Targ' A
--                                 (push (true , true , push (inl g) i) j))
--                (λ i j → pushG A (true , true , push (inl g) i) x j)
--                (coh-eq-l A g)
--                (G-push-inl A (λ i → g i true) (g false) refl x)
--                (G-coh-inr A g x)
--                (λ i _ → G-inler A (g true true) (g false) x i)
--                λ s t → fst (e A _) (G-inr-inl-inl₂ (RP∞'∙ ℓ) A (λ i → g i true) x g (λ _ → refl) s t)

-- MEGA-inst↓ : ∀ {ℓ} (Targ : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) → ΠR-extend** I J A → Type ℓ)
--         (G : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) → (x : ΠR-extend** I J A) → (i : fst I) → Targ I J A x)
--      → 𝕄 Targ (Targ _ _) (λ _ _ → idEquiv _) G (λ A e a i → G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push e i) a)
--      →  (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
--      → Σ[ f ∈ ((x : _) → Targ I J A x) ] ((i : fst I) (x : _) → G _ _ A x i ≡ f x)
-- MEGA-inst↓ Targ G M I J A = (ΠR-extend→ I J A) , (λ i → G.GID I i J A)
--   where
--   open 𝕄 M
--   module MEG = MEGA {Targ = Targ}
--     inler inr-inr inr-inl-inl inr-inl-inr push-inl coh-inr
--     coh-eq1 coh-eq2 coh-eq-l
--   open MEG
--   module G = ID G G-inler G-inr-inr G-inr-inl-inl₁ G-inr-inl-inl₂ G-inr-inl-inr₁ G-inr-inl-inr₂
--                    G-push-inl G-coh-inr G-coh-eq1 G-coh-eq2 G-coh-eq-l
-- MEGA-inst :
--   ∀ {ℓ} (Targ : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) → ΠR-extend** I J A → Type ℓ)
--         (Targ' : (A : Bool → Bool → Type ℓ) → ΠR-extend** (RP∞'∙ ℓ) (RP∞'∙ ℓ) A → Type ℓ)
--         (e : (A : Bool → Bool → Type ℓ) (x : ΠR-extend** (RP∞'∙ ℓ) (RP∞'∙ ℓ) A)
--           → Targ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A x ≃ Targ' A x)
--         (G : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) → (x : ΠR-extend** I J A) → (i : fst I) → Targ I J A x)
--         (pushG : (A : Bool → Bool → Type ℓ) (x : newBack (RP∞'∙ ℓ) (RP∞'∙ ℓ) A) (a : Bool)
--           → PathP (λ i → Targ' A (push x i))
--                    (fst (e A _) (G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (inl (newBack→ₗ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A x)) a))
--                    (fst (e A _) (G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (inr (newBack→ᵣ (RP∞'∙ ℓ) (RP∞'∙ ℓ) A x)) a)))
--      → ((λ A x a i → fst (e A _) (G (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (push x i) a)) ≡ pushG)
--      → 𝕄 Targ Targ' e G pushG
--      → (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
--      → Σ[ f ∈ ((x : _) → Targ I J A x) ] ((i : fst I) (x : _) → G _ _ A x i ≡ f x)
-- MEGA-inst {ℓ = ℓ} Targ = EquivJ* (λ A → ΠR-extend** (RP∞'∙ ℓ) (RP∞'∙ ℓ) A)
--   λ G → J> MEGA-inst↓ _ _


-- ΣBool→ : ∀ {ℓ} {A : Bool → Type ℓ} → Σ Bool A → A true × A false → Type ℓ
-- ΣBool→ (false , a) (b , c) = c ≡ a
-- ΣBool→ (true , a) (b , c) = b ≡ a


-- joinR-gen' : ∀ {ℓ} (A : Bool → Type ℓ) → Type ℓ
-- joinR-gen' A = PushoutR  (Σ Bool A) (A true × A false) ΣBool→

-- joinR→ : ∀ {ℓ} (A : Bool → Type ℓ) →  joinR-gen Bool A → joinR-gen' A
-- joinR→ A (inlR x) = inlR x
-- joinR→ A (inrR x) = inrR (x true , x false)
-- joinR→ A (push* (false , a) b x i) = push* (false , a) (b true , b false) x i
-- joinR→ A (push* (true , a) b x i) = push* (true , a) (b true , b false) x i

-- joinRIso : ∀ {ℓ} (A : Bool → Type ℓ) → Iso (joinR-gen Bool A) (joinR-gen' A)
-- Iso.fun (joinRIso A) = joinR→ A
-- Iso.inv (joinRIso A) (inlR x) = inlR x
-- Iso.inv (joinRIso A) (inrR (a , b)) = inrR (CasesBool true a b)
-- Iso.inv (joinRIso A) (push* (false , a) (b , c) x i) = push* (false , a) (CasesBool true b c) x i
-- Iso.inv (joinRIso A) (push* (true , a) (b , c) x i) = push* (true , a) (CasesBool true b c) x i
-- Iso.rightInv (joinRIso A) (inlR x) = refl
-- Iso.rightInv (joinRIso A) (inrR x) = refl
-- Iso.rightInv (joinRIso A) (push* (false , a) b x i) = refl
-- Iso.rightInv (joinRIso A) (push* (true , a) b x i) = refl
-- Iso.leftInv (joinRIso A) (inlR x) = refl
-- Iso.leftInv (joinRIso A) (inrR x) = cong inrR (CasesBoolη x)
-- Iso.leftInv (joinRIso A) (push* (false , a) f x i) j = push* (false , a) (CasesBoolη f j) x i
-- Iso.leftInv (joinRIso A) (push* (true , a) f x i) j = push* (true , a) (CasesBoolη f j) x i

-- joinR'Funct : ∀ {ℓ} {A B : Bool → Type ℓ} → ((x : Bool) → A x → B x) → joinR-gen' A → joinR-gen' B
-- joinR'Funct f (inlR (i , x)) = inlR (i , f i x)
-- joinR'Funct f (inrR (a , b)) = inrR (f true a , f false b)
-- joinR'Funct f (push* (false , a) (b , c) x i) = push* (false , f false a) (f true b , f false c) (cong (f false) x) i
-- joinR'Funct f (push* (true , a) (b , c) x i) = push* (true , f true a) (f true b , f false c) (cong (f true) x) i

-- joinR'Funct'isEq : ∀ {ℓ} {A B : Bool → Type ℓ} → (e : (x : Bool) → A x ≃ B x)
--   → section (joinR'Funct (fst ∘ e)) (joinR'Funct (invEq ∘ e))
--   × retract (joinR'Funct (fst ∘ e)) (joinR'Funct (invEq ∘ e))
-- joinR'Funct'isEq {ℓ = ℓ} {A} {B} e = subst TYP (isContr→isProp help _ (B , e)) main
--   where
--   help : isContr (Σ[ B ∈ (Bool → Type ℓ) ] ((x : Bool) → A x ≃ B x))
--   help = isOfHLevelRetractFromIso 0
--            (Σ-cong-iso-snd (λ B → compIso (codomainIsoDep
--              (λ b → equivToIso (invEquiv univalence))) funExtIso))
--            (isContrSingl A)

--   TYP : (Σ[ B ∈ (Bool → Type ℓ) ] ((x : Bool) → A x ≃ B x)) → Type ℓ
--   TYP (B , e) = section (joinR'Funct (fst ∘ e)) (joinR'Funct (invEq ∘ e))
--               × retract (joinR'Funct (fst ∘ e)) (joinR'Funct (invEq ∘ e))

--   main : TYP (A , λ x → idEquiv (A x))
--   fst main (inlR x) = refl
--   fst main (inrR x) = refl
--   fst main (push* (false , a) b x i) = refl
--   fst main (push* (true , a) b x i) = refl
--   snd main (inlR x) = refl
--   snd main (inrR x) = refl
--   snd main (push* (false , a) b x i) = refl
--   snd main (push* (true , a) b x i) = refl

-- joinR'FunctIso : ∀ {ℓ} {A B : Bool → Type ℓ} (e : (x : Bool) → A x ≃ B x)
--   → Iso (joinR-gen' A) (joinR-gen' B)
-- Iso.fun (joinR'FunctIso e) = joinR'Funct (fst ∘ e)
-- Iso.inv (joinR'FunctIso e) = joinR'Funct (invEq ∘ e)
-- Iso.rightInv (joinR'FunctIso e) = joinR'Funct'isEq e .fst
-- Iso.leftInv (joinR'FunctIso e) = joinR'Funct'isEq e .snd

-- joinRIso≃ : ∀ {ℓ} (A : Bool → Type ℓ) → joinR-gen Bool A ≃ joinR-gen' A
-- joinRIso≃ A = isoToEquiv (joinRIso A)

-- GOALTY : ∀ {ℓ} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) → Type ℓ
-- GOALTY I J A = joinR-gen (fst J) λ j → joinR-gen (fst I) λ i → A i j

-- GOALTY' : ∀ {ℓ} (A : Bool → Bool → Type ℓ) → Type ℓ
-- GOALTY' A = joinR-gen' λ a → joinR-gen' λ b → A b a

-- GOALTY≃ : ∀ {ℓ} (A : Bool → Bool → Type ℓ)
--   → Iso (GOALTY (RP∞'∙ ℓ) (RP∞'∙ ℓ) A) (GOALTY' A)
-- GOALTY≃ A = compIso (joinRIso (λ y → joinR-gen Bool λ x → A x y))
--                     (joinR'FunctIso λ y → isoToEquiv (joinRIso (λ x → A x y)))

-- GFUN : ∀ {ℓ} (A : Bool → Bool → Type ℓ)
--   → GOALTY (RP∞'∙ ℓ) (RP∞'∙ ℓ) A → GOALTY' A
-- GFUN A = Iso.fun (GOALTY≃ A)


-- GFUNEq : ∀ {ℓ} (A : Bool → Bool → Type ℓ)
--   → GOALTY (RP∞'∙ ℓ) (RP∞'∙ ℓ) A ≃ GOALTY' A
-- fst (GFUNEq A) = GFUN A
-- snd (GFUNEq A) = isoToIsEquiv (GOALTY≃ A)


-- 𝕄inst : ∀ {ℓ} → Type (ℓ-suc ℓ)
-- 𝕄inst {ℓ = ℓ} =
--   𝕄 (λ I J A _ → GOALTY I J A)
--      (λ A _ → GOALTY' A)
--      (λ A _ → GFUNEq A)
--      (λ I J A x i → btm-map I J A (i , leftMap** I J A i x))
--      λ A x a j → GFUN A (btm-map (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (a , leftMapBool (RP∞'∙ ℓ) A a (push x j)))


-- private
--   variable
--     ℓ : Level

-- inrerr : (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
--          (t : (i : fst I) (j : fst J) → A i j) → GOALTY I J A
-- inrerr I J A t = inrR λ j → inrR λ i → t i j

-- G-inr-inr* : (I₁ J₁ : RP∞' ℓ) (A : fst I₁ → fst J₁ → Type ℓ)
--       (t : (i : fst I₁) (j : fst J₁) → A i j) (i : fst I₁) →
--       inrR (λ j → inlR (i , t i j)) ≡ inrerr I₁ J₁ A t
-- G-inr-inr* I J A t i = cong inrR λ k j → push* (i , t i j) (λ i → t i j) refl k

-- inr-inl-inl* : (I : RP∞' ℓ) (A : fst I → Bool → Type ℓ)
--   (f : (x : fst I) → A x true)
--   → Σ[ x ∈ GOALTY I (RP∞'∙ ℓ) A ]
--       ((p : (i : fst I) (j : Bool) → A i j)
--        (q : (i : fst I) → p i true ≡ f i)
--       → x ≡ inrerr I (RP∞'∙ ℓ) A p)
-- fst (inr-inl-inl* I A f) = inlR (true , inrR f)
-- snd (inr-inl-inl* I A f) p q =
--   push* (true , inrR f) (λ i → inrR λ j → p j i) (cong inrR (funExt q))

-- G-inr-inl-inl*₁ : (I₁ : RP∞' ℓ) (A : fst I₁ → Bool → Type ℓ)
--       (f : (x : fst I₁) → A x true) (i : fst I₁) →
--       Path (GOALTY I₁ (RP∞'∙ ℓ) A) (inlR (true , inlR (i , f i))) (inlR (true , inrR f))
-- G-inr-inl-inl*₁ I A f i k = inlR (true , push* (i , f i) f refl k)

-- G-inr-inl-inl*₂ : (I₁ : RP∞' ℓ) (A : fst I₁ → Bool → Type ℓ)
--       (f : (x : fst I₁) → A x true) (i : fst I₁)
--       (p : (i₁ : fst I₁) (j : Bool) → A i₁ j)
--       (q : (x : fst I₁) → p x true ≡ f x) →
--       Square {A = GOALTY I₁ (RP∞'∙ ℓ) A}
--       (λ k → push* (true , inlR (i , f i)) (λ j → inlR (i , p i j))
--                     (λ t → inlR (i , q i t)) k)
--       (push* (true , inrR f) (λ j → inrR (λ i₁ → p i₁ j))
--       (λ i₁ → inrR (funExt q i₁)))
--       (G-inr-inl-inl*₁ I₁ A f i) (G-inr-inr* I₁ (RP∞'∙ ℓ) A p i)
-- G-inr-inl-inl*₂ I A f i p q k j =
--   push* (true , push* (i , f i) f (λ _ → f i) k)
--         (λ i₁ → push* (i , p i i₁) (λ i₂ → p i₂ i₁) (λ _ → p i i₁) k)
--         (λ t → push* (i , q i t) (λ x → q x t) refl k) j

-- inr-inl-inr* : (I : RP∞' ℓ) (A : fst I → fst I → Type ℓ)
--   (f : (x : fst I) → A x x)
--   → Σ[ x ∈ GOALTY I I A ]
--       ((p : (i j : fst I) → A i j)
--        (q : (i : fst I) → p i i ≡ f i)
--       → x ≡ inrerr I I A p)
-- fst (inr-inl-inr* I A f) = inrR λ i → inlR (i , (f i))
-- snd (inr-inl-inr* I A f) p q k = inrR (λ i → push* (i , f i) (λ j → p j i) (q i) k)


-- G-inr-inl-inr*₁ : (I₁ : RP∞' ℓ) (A : fst I₁ → fst I₁ → Type ℓ)
--       (f : (i : fst I₁) → A i i) (i : fst I₁) →
--       Path (GOALTY I₁ I₁ A) (inlR (idfun (fst I₁) i , inlR (i , f i)))
--                             (inrR (λ i₁ → inlR (i₁ , f i₁)))
-- G-inr-inl-inr*₁ I A f i = push* (i , (inlR (i , f i))) (λ j → inlR (j , f j)) refl

-- module _ (I₁ : RP∞' ℓ) (A : fst I₁ → fst I₁ → Type ℓ)
--       (p : (i₁ j : fst I₁) → A i₁ j) (i : fst I₁) where
--   G-inr-inl-inr*₂-b-fill : (j k r : _) →  GOALTY I₁ I₁ A
--   G-inr-inl-inr*₂-b-fill j k r =
--     hfill (λ r → λ {(j = i0) → push* (i , inlR (i , p i i))
--                                         (λ s → push* (i , p i s) (λ t → p t s) refl (~ r))
--                                         (λ t → push* (i , p i i) (λ t → p t i) refl (~ r ∧ ~ t)) k
--                    ; (j = i1) → inrR (λ v → push* (v , p v v) (λ a → p a v) (λ _ → p v v) (~ r ∨ k))
--                    ; (k = i0) → push* (i , inlR (i , p i i))
--                                        (λ x → push* (x , p x x) (λ a → p a x) refl (~ r))
--                                        (λ j → push* (i , p i i) (λ a → p a i) refl (~ r ∧ ~ j)) j
--                    ; (k = i1) → inrR (λ v → push* (i , p i v) (λ t → p t v) refl (~ r ∨ j))})
--            (inS (push* (i , inlR (i , p i i))
--              (λ v → inrR (λ a → p a v))
--              (sym (push* (i , p i i) (λ a → p a i) refl))
--              (j ∨ k)))
--            r

--   G-inr-inl-inr*₂-b :
--     Square (λ k → push* (i , inlR (i , p i i)) (λ v → inlR (i , p i v)) refl k)
--             (λ k → inrR (λ i₁ → push* (i₁ , p i₁ i₁) (λ j → p j i₁) refl k))
--             (G-inr-inl-inr*₁ I₁ A (λ x → p x x) i)
--             (G-inr-inr* I₁ I₁ A p i)
--   G-inr-inl-inr*₂-b j k = G-inr-inl-inr*₂-b-fill j k i1

--   G-inr-inl-inr*₂ :
--         (f : (i : fst I₁) → A i i) (q : (λ x → p x x) ≡ f) →
--         Square
--         (λ k → push* (i , inlR (i , f i)) (λ j → inlR (i , p i j))
--                       (λ t → inlR (i , q t i)) k)
--         (λ k → inrR (λ i₁ → push* (i₁ , f i₁) (λ j → p j i₁) (funExt⁻ q i₁) k))
--         (G-inr-inl-inr*₁ I₁ A f i)
--         (G-inr-inr* I₁ I₁ A p i)
--   G-inr-inl-inr*₂ = J> G-inr-inl-inr*₂-b

--   G-inr-inl-inr*₂-refl : G-inr-inl-inr*₂ (λ x → p x x) refl ≡ G-inr-inl-inr*₂-b
--   G-inr-inl-inr*₂-refl = transportRefl G-inr-inl-inr*₂-b

-- module Sol {ℓ : Level} (A : Bool → Bool → Type ℓ) where
--   inler : A true true → TotΠ (A false) → GOALTY' A
--   inler a b = inrR ((inrR (a , b true)) , (inlR (false , b false)))

--   push-inl :
--       (f : (i : fst (RP∞'∙ ℓ)) → A i true)
--       (g : (j : Bool) → A false j)
--       (p : g true ≡ f false) →
--       inler (f true) g ≡ GFUN A (inlR (true , inrR f))
--   push-inl f g p =
--     sym (push* (true , inrR (f true , f false))
--                ((inrR (f true , g true)) , (inlR (false , g false)))
--                λ k → inrR (f true , p k))

--   coh-inr : (g : (i j : Bool) → A i j) →
--       inler (g true true) (g false) ≡
--       GFUN A (inrerr (RP∞'∙ ℓ) (RP∞'∙ ℓ) A g)
--   coh-inr g i =
--     inrR (inrR (g true true , g false true)
--         , push* (false , g false false)
--                 (g true false , g false false)
--                 refl i)

--   coh-eq1 : (g : (i : Bool) → A i i)
--       (f : TotΠ (A false)) (p : f false ≡ g false) →
--       inler (g true) f ≡ GFUN A (inrR (λ i → inlR (i , g i)))
--   coh-eq1 g f p i = inrR ((push* (true , g true) (g true , f true) refl (~ i)) , (inlR (false , p i)))

--   coh-eq2 : (g : (i j : Bool) → A i j) →
--       Square
--       (coh-eq1 (λ i → g i i) (g false) refl) (coh-inr g)
--       (λ _ → inler (g true true) (g false))
--       (λ i →
--          GFUN A (inrR (λ i₁ → push* (i₁ , g i₁ i₁) (λ j → g j i₁) refl i)))
--   coh-eq2 g i j = inrR ((push* (true , g true true) (g true true , g false true) refl (i ∨ ~ j))
--                       , (push* (false , g false false) (g true false , g false false) refl (i ∧ j)))

--   coh-eq-l-fill : (g : (i j : Bool) → A i j) (i j k : _) → GOALTY' A
--   coh-eq-l-fill g i j k =
--     hfill (λ k → λ {(i = i0) → push* (true , inrR (g true true , g false true))
--                                         (inrR (g true true , g false true) , inlR (false , g false false))
--                                         (λ _ → inrR (g true true , g false true)) (k ∧ ~ j)
--                    ; (i = i1) → push* (true , inrR (g true true , g false true))
--                                        (inrR (g true true , g false true)
--                                            , push* (false , g false false) (g true false , g false false) refl j)
--                                        refl k
--                    ; (j = i0) → push* (true , inrR (g true true , g false true))
--                                        (inrR (g true true , g false true) , inlR (false , g false false))
--                                        (λ _ → inrR (g true true , g false true)) k
--                    ; (j = i1) → push* (true , inrR (g true true , g false true))
--                                        (inrR (g true true , g false true) ,
--                                         inrR (g true false , g false false)) refl (i ∧ k)})
--           (inS (inlR (true , inrR (g true true , g false true))))
--           k

--   coh-eq-l : (g : (i j : Bool) → A i j) →
--       Square
--       (push-inl (λ i₁ → g i₁ true) (g false) (λ _ → g false true))
--       (coh-inr g)
--       (λ _ → inler (g true true) (g false))
--       (λ i →
--          GFUN A (push* (true , inrR (λ i₁ → g i₁ true))
--           (λ j → inrR (λ i₁ → g i₁ j)) refl
--           i))
--   coh-eq-l g i j = coh-eq-l-fill g i j i1

--   G-inler : (a : A true true)
--       (b : TotΠ (A false)) (i : Bool) →
--       GFUN A
--       (btm-map (RP∞'∙ ℓ) (RP∞'∙ ℓ) A
--        (i , leftFun'-inl (RP∞'∙ ℓ) (fst (RP∞'∙ ℓ)) A true (true , a) b i))
--       ≡ inler a b
--   G-inler a b false i = inrR (push* (false , b true) (a , b true) refl i , inlR (false , b false))
--   G-inler a b true i =
--     push* (true , inlR (true , a))
--           (inrR (a , b true) , inlR (false , b false))
--           (sym (push* (true , a) (a , b true) refl)) i

--   module _ (f : (i : Bool) → A i true) (g : (j : Bool) → A false j) (p : g true ≡ f false) where
--     G-push-inl-filler : (i j k : _) → GOALTY' A
--     G-push-inl-filler i j k =
--       hfill (λ k → λ {(j = i0) → push*
--                                      (true , inlR (true , f true))
--                                      (inrR (f true , p (~ k)) , inlR (false , g false))
--                                      (sym (push* (true , f true) (f true , p (~ k)) refl)) i
--                        ; (j = i1) → inlR (true , push* (true , f true) (f true , f false) refl (i ∧ k))
--                        ; (i = i0) → inlR (true , inlR (true , f true))
--                        ; (i = i1) → push* (true , push* (true , f true) (f true , f false) refl k)
--                                             (inrR (f true , p (~ k)) , inlR (false , g false))
--                                             (λ i → push* (true , f true) (f true , p (~ k ∨ i)) refl
--                                             (k ∨ ~ i)) (~ j)})
--               (inS (push* (true , inlR (true , f true))
--                      (inrR (f true , f false) , inlR (false , g false))
--                      (sym (push* (true , f true) (f true , f false) refl))
--                      (i ∧ ~ j)))
--               k
--     G-push-inl : (i : Bool) →
--         Square (λ k → GFUN A (btm-map (RP∞'∙ ℓ) (RP∞'∙ ℓ) A
--                         (i , leftMapBool (RP∞'∙ ℓ) A i
--                          (push (true , true , inl (inl (f , g , p))) k))))
--         (push-inl f g p)
--         (G-inler (f true) g i)
--         (λ k → GFUN A (G-inr-inl-inl*₁ (RP∞'∙ ℓ) A f i k))
--     G-push-inl false j k =
--       push* (true , push* (false , f false) (f true , f false) refl j)
--            ((push* (false , g true) (f true , g true) refl j) , (inlR (false , g false)))
--            (λ s → push* (false , p s) (f true , p s) refl j) (~ k)
--     G-push-inl true i j = G-push-inl-filler i j i1

--   G-coh-inr-t-fill : (g : (i j : Bool) → A i j) (i j k : _)
--     → GOALTY' A
--   G-coh-inr-t-fill g i j k =
--     hfill (λ k → λ {(j = i0) → push* (true , inlR (true , g true true))
--                                        (inrR (g true true , g false true) , inlR (false , g false false))
--                                        (sym (push* (true , g true true) (g true true , g false true) refl))
--                                        (i ∧ k)
--                    ; (j = i1) → push* (true , inlR (true , g true true))
--                                         ((push* (true , g true true) (g true true , g false true) refl i)
--                                        , (push* (true , g true false) (g true false , g false false) refl i))
--                                        (λ s → push* (true , g true true) (g true true , g false true) refl (~ s ∧ i)) k
--                    ; (i = i0) → push* (true , inlR (true , g true true))
--                                         (inlR (true , g true true) , inlR (true , g true false))
--                                         (λ i₁ → inlR (true , g true true)) (j ∧ k)
--                    ; (i = i1) → push* (true , inlR (true , g true true)) (inrR (g true true , g false true)
--                                            , push* (false , g false false) (g true false , g false false) refl j)
--                                            (sym (push* (true , g true true) (g true true , g false true) refl)) k})
--            (inS (inlR (true , inlR (true , g true true))))
--            k

--   G-coh-inr : (g : (i j : Bool) → A i j)
--       (i : Bool) →
--       Square
--       (λ j → GFUN A (btm-map (RP∞'∙ ℓ) (RP∞'∙ ℓ) A
--                (i , leftMapBool (RP∞'∙ ℓ) A i (push (true , true , inr g) j))))
--       (coh-inr g)
--       (G-inler (g true true) (g false) i)
--       λ k → GFUN A (G-inr-inr* (RP∞'∙ ℓ) (RP∞'∙ ℓ) A g i k)
--   G-coh-inr g false i j =
--     inrR ((push* (false , g false true) (g true true , g false true) refl i)
--         , (push* (false , g false false) (g true false , g false false) refl (i ∧ j)))
--   G-coh-inr g true i j = G-coh-inr-t-fill g i j i1

--   G-coh-eq1-fill : (g : (i : Bool) → A i i)
--         (f : TotΠ (A false)) (p : f false ≡ g false)
--      → (i j k : _) → GOALTY' A
--   G-coh-eq1-fill g f p i j k =
--     hfill (λ k → λ {(i = i0) → push* (false , inlR (false , g false))
--                                        (inlR (false , f true) , inlR (false , f false))
--                                        (λ i₁ → inlR (false , p i₁)) (~ j ∧ k)
--                    ; (i = i1) → push* (false , inlR (false , g false))
--                                        (push* (true , g true) (g true , f true) refl (~ j)
--                                        , inlR (false , p j))
--                                        (λ i → inlR (false , p (i ∨ j))) k
--                    ; (j = i0) → push* (false , inlR (false , g false))
--                                        (push* (false , f true) (g true , f true) refl i , inlR (false , f false))
--                                        (λ i → inlR (false , p i)) k
--                    ; (j = i1) → push* (false , inlR (false , g false))
--                                        (inlR (true , g true) , inlR (false , g false))
--                                        (λ i₁ → inlR (false , g false)) (i ∧ k)})
--           (inS (inlR (false , inlR (false , g false))))
--           k

--   G-coh-eq1 : (g : (i : Bool) → A i i)
--         (f : TotΠ (A false)) (p : f false ≡ g false) (x : Bool) →
--         Square
--         (λ j → GFUN A
--            (btm-map (RP∞'∙ ℓ) (RP∞'∙ ℓ) A
--             (x , leftMapBool (RP∞'∙ ℓ) A x (push (true , true , inl (inr (idEquiv Bool , refl , g , f , p))) j))))
--         (coh-eq1 g f p)
--         (G-inler (g true) f x)
--         (λ t → GFUN A (G-inr-inl-inr*₁ (RP∞'∙ ℓ) A g x t))
--   G-coh-eq1 g f p false i j = G-coh-eq1-fill g f p i j i1
--   G-coh-eq1 g f p true i j =
--     push* (true , inlR (true , g true))
--           (push* (true , g true) (g true , f true) refl (~ j) , inlR (false , p j))
--           (λ k → push* (true , g true) (g true , f true) refl (~ j ∧ ~ k)) i

--   G-coh-eq2-main :  (g : (i j : Bool) → A i j)
--       (x : Bool) →
--       Cube
--       (λ i _ → G-inler (g true true) (g false) x i)
--       (λ s t →
--          GFUN A
--          (G-inr-inl-inr*₂-b (RP∞'∙ ℓ) A g x s t))
--       (λ i j → GFUN A
--          (btm-map (RP∞'∙ ℓ) (RP∞'∙ ℓ) A
--           (x , leftMapBool (RP∞'∙ ℓ) A x
--            (push (true , true , push (inr (idEquiv Bool , refl , g)) j) i)))) -- ()
--       (λ i j → coh-eq2 g j i) -- (G-coh-inr g x)
--       (λ i j → G-coh-eq1 (λ i → g i i) (g false) refl x j i)
--       λ i j → G-coh-inr g x j i
--   G-coh-eq2-main g false k i j =
--     hcomp (λ r → λ {(i = i0) → push* (false , inlR (false , g false false))
--                                         (inlR (false , g false true) , inlR (false , g false false))
--                                         (λ i₁ → inlR (false , g false false)) ((~ k ∨ j) ∧ r)
--                    ; (i = i1) → push* (false , inlR (false , g false false))
--                                        ((push* (true , g true true) (g true true , g false true) refl (j ∨ ~ k))
--                                       , (push* (false , g false false) (g true false , g false false) refl (j ∧ k)))
--                                        (λ s → push* (false , g false false) (g true false , g false false) refl (j ∧ k ∧ ~ s)) r
--                    ; (j = i0) → G-coh-eq1-fill (λ i → g i i) (g false) refl i k r
--                    ; (j = i1) → push* (false , inlR (false , g false false))
--                                        ((push* (false , g false true) (g true true , g false true) refl i)
--                                       , (push* (false , g false false) (g true false , g false false) refl (i ∧ k)))
--                                        (λ s → push* (false , g false false) (g true false , g false false) refl (i ∧ k ∧ ~ s)) r
--                    ; (k = i0) → push* (false , inlR (false , g false false))
--                                        ((push* (false , g false true) (g true true , g false true) refl i)
--                                       , (inlR (false , g false false)))
--                                        refl r
--                    ; (k = i1) → h r i j
--                    })
--             (inlR (false , inlR (false , g false false)))
--     where
--     hah : ∀ {ℓ} {A : Type ℓ} {x : A} (y : A) (p : x ≡ y) -- s k j
--       → Cube (λ k j → p (~ k ∨ j)) (λ _ _ → x)
--               (λ s j → p (~ s)) (λ s j → p (j ∧ ~ s))
--               (λ s k → p (~ s ∧ ~ k)) λ i _ → p (~ i)
--     hah = J> refl 
  
--     h : Cube (λ _ _ → inlR (false , inlR (false , g false false)))
--              (λ i j → GFUN A (G-inr-inl-inr*₂-b-fill (RP∞'∙ ℓ) A g false i j i1))
--              (λ r j → push* (false , inlR (false , g false false))
--                              (inlR (false , g false true) , inlR (false , g false false))
--                              refl (j ∧ r))
--              (λ r j → push* (false , inlR (false , g false false))
--                              (push* (true , g true true) (g true true , g false true) refl j
--                             , push* (false , g false false) (g true false , g false false) refl j)
--                             (λ s →  push* (false , g false false) (g true false , g false false) refl (j ∧ ~ s))
--                             r)
--              (λ r i → G-coh-eq1-fill (λ i₁ → g i₁ i₁) (g false) refl i i1 r)
--              λ r i → push* (false , inlR (false , g false false))
--                             (push* (false , g false true) (g true true , g false true) refl i
--                            , push* (false , g false false) (g true false , g false false) refl i)
--                             (λ s →  push* (false , g false false) (g true false , g false false) refl (i ∧ ~ s))
--                             r
--     h r i j =
--         hcomp (λ k → λ {(i = i0) → push* (false , inlR (false , g false false))
--                                           ((push* (false , g false true) (g true true , g false true) refl (~ k))
--                                          , (push* (false , g false false) (g true false , g false false) refl (~ k)))
--                                           (λ s → push* (false , g false false) (g true false , g false false) refl (~ k ∧ ~ s)) (r ∧ j)
--                    ; (i = i1) → push* (false , inlR (false , g false false))
--                                        ((push* (true , g true true) (g true true , g false true) refl (~ k ∨ j))
--                                       , (push* (false , g false false) (g true false , g false false) refl (~ k ∨ j)))
--                                        (λ s → hah _ (push* (false , g false false) (g true false , g false false) refl) s k j) r
--                    ; (j = i0) → push* (false , inlR (false , g false false))
--                                        ((push* (true , g true true) (g true true , g false true) refl (~ k))
--                                        , (push* (false , g false false) (g true false , g false false) refl (~ k)))
--                                        (λ t → push* (false , g false false) (g true false , g false false) refl (~ k ∧ ~ t)) (i ∧ r)
--                    ; (j = i1) → push* (false , inlR (false , g false false))
--                                        ((push* (false , g false true) (g true true , g false true) refl (~ k ∨ i))
--                                        , (push* (false , g false false) (g true false , g false false) refl (~ k ∨ i)))
--                                        (λ s → hah _ (push* (false , g false false) (g true false , g false false) refl) s k i) r
--                    ; (r = i0) → inlR (false , inlR (false , g false false))
--                    ; (r = i1) → GFUN A (G-inr-inl-inr*₂-b-fill (RP∞'∙ ℓ) A g false i j k)
--                    })
--            (push* (false , inlR (false , g false false))
--           (inrR (g true true , g false true) ,
--            inrR (g true false , g false false))
--           (sym (push* (false , g false false) (g true false , g false false) refl))
--           ((i ∨ j) ∧ r))
--   G-coh-eq2-main g true k i j =
--     hcomp (λ r → λ {(i = i0) → GFUN A (btm-map (RP∞'∙ ℓ) (RP∞'∙ ℓ) A
--                                   (true , leftFun-cohₗ**-fill (RP∞'∙ _) (RP∞'∙ _) A true true (idEquiv Bool) refl g j k r))
--                    ; (i = i1) → inrR ((push* (true , g true true) (g true true , g false true) refl (j ∨ ~ k)
--                                , push* (false , g false false) (g true false , g false false) refl (j ∧ k)))
--                    ; (j = i0) → push* (true , inlR (true , g true true))
--                                         (push* (true , g true true) (g true true , g false true) refl (~ k)
--                                         , inlR (false , g false false))
--                                        (λ s → push* (true , g true true) (g true true , g false true)
--                                           (λ _ → g true true) (~ k ∧ ~ s)) i
--                    ; (j = i1) → cong-GFUN r i k
--                    ; (k = i0) → push* (true , inlR (true , g true true))
--                                        (inrR (g true true , g false true) , inlR (false , g false false))
--                                        (sym (push* (true , g true true) (g true true , g false true) refl)) i
--                    ; (k = i1) → GFUN A (G-inr-inl-inr*₂-b-fill (RP∞'∙ ℓ) A g true i j i1)
--                    })
--        (hcomp (λ r → λ {(i = i0) → push* (true , inlR (true , g true true))
--                                             (inlR (true , g true true) , inlR (true , g true false))
--                                             (λ i₁ → inlR (true , g true true)) (j ∧ (k ∧ r))
--                    ; (i = i1) → push* (true , inlR (true , g true true))
--                                        ((push* (true , g true true) (g true true , g false true)
--                                                refl (j ∨ ~ k))
--                                       , (push* (false , g false false) (g true false , g false false) refl (j ∧ k)))
--                                        (λ s → push* (true , g true true) (g true true , g false true)
--                                                      refl ((~ k ∨ j) ∧ (~ s))) r
--                    ; (j = i0) → push* (true , inlR (true , g true true))
--                                        (push* (true , g true true) (g true true , g false true)
--                                         refl (~ k)
--                                         , inlR (false , g false false))
--                                        (λ s → push* (true , g true true) (g true true , g false true)
--                                                      refl (~ k ∧ ~ s))
--                                        (i ∧ r)
--                    ; (j = i1) → G-coh-inr-t-fill g i k r
--                    ; (k = i0) → push* (true , inlR (true , g true true))
--                                        (inrR (g true true , g false true) , inlR (false , g false false))
--                                        (sym (push* (true , g true true) (g true true , g false true) refl))
--                                        (i ∧ r)
--                    ; (k = i1) → F2 r i j
--                    })
--               (inlR (true , inlR (true , g true true))))
--     where -- r i j
--     F2 : Cube (λ _ _ → inlR (true , inlR (true , g true true)))
--               (λ i j → GFUN A (G-inr-inl-inr*₂-b-fill (RP∞'∙ ℓ) A g true i j i1))
--               (λ r j → push* (true , inlR (true , g true true))
--                               (inlR (true , g true true) , inlR (true , g true false))
--                               refl (j ∧ r))
--               (λ r j → push* (true , inlR (true , g true true))
--                               (push* (true , g true true) (g true true , g false true) refl j
--                              , push* (false , g false false) (g true false , g false false) refl j)
--                               (λ s → push* (true , g true true) (g true true , g false true) refl (j ∧ ~ s)) r)
--               (λ r i → push* (true , inlR (true , g true true))
--                               (inlR (true , g true true) , inlR (false , g false false))
--                               refl (i ∧ r))
--               λ r i → G-coh-inr-t-fill g i i1 r
--     F2 r i j =
--       hcomp (λ k → λ {(i = i0) → push* (true , inlR (true , g true true))
--                                           (push* (true , g true true) (g true true , g false true) refl (~ k)
--                                         , push* (true , g true false) (g true false , g false false) refl (~ k))
--                                           (λ i₂ → push* (true , g true true)
--                                                          (g true true , g false true) refl (~ k ∧ ~ i₂)) (r ∧ j)
--                    ; (i = i1) →  push* (true , inlR (true , g true true))
--                                         ((push* (true , g true true) (g true true , g false true) refl (~ k ∨ j))
--                                        , (push* (false , g false false) (g true false , g false false) refl (~ k ∨ j)))
--                                         (λ t → push* (true , g true true) (g true true , g false true) refl ((j ∨ ~ k) ∧ (~ t))) r
--                    ; (j = i0) → push* (true , inlR (true , g true true))
--                                        ((push* (true , g true true) (g true true , g false true) refl (~ k))
--                                        , (push* (false , g false false) (g true false , g false false) refl (~ k)))
--                                        (λ i → push* (true , g true true) (g true true , g false true) refl (~ i ∧ ~ k))
--                                        (r ∧ i)
--                    ; (j = i1) → push* (true , inlR (true , g true true))
--                                        ((push* (true , g true true) (g true true , g false true) refl (~ k ∨ i))
--                                      , (push* (true , g true false) (g true false , g false false) refl (~ k ∨ i)))
--                                        (λ t → push* (true , g true true) (g true true , g false true) refl (~ t ∧ (i ∨ ~ k))) r
--                    ; (r = i0) → inlR (true , inlR (true , g true true))
--                    ; (r = i1) → GFUN A (G-inr-inl-inr*₂-b-fill (RP∞'∙ ℓ) A g true i j k)
--                    })
--                   (push* (true , inlR (true , g true true))
--                          (inrR (g true true , g false true)
--                         , inrR (g true false , g false false))
--                          (sym (push* (true , g true true) (g true true , g false true) refl))
--                          (r ∧ (i ∨ j)))

--     cong-GFUN : Cube (λ i k → G-coh-inr-t-fill g i k i1)
--                      (λ i k → G-coh-inr-t-fill g i k i1)
--                      (λ r k → push* (true , inlR (true , g true true))
--                                       (inlR (true , g true true) , inlR (true , g true false))
--                                       refl k)
--                      (λ r k → inrR (inrR (g true true , g false true)
--                              , push* (false , g false false) (g true false , g false false) refl k))
--                      (λ r i → push* (true , inlR (true , g true true))
--                                        (inrR (g true true , g false true) , inlR (false , g false false))
--                                        (sym (push* (true , g true true) (g true true , g false true) refl)) i)
--                      λ r i → inrR (push* (true , g true true) (g true true , g false true) refl i
--                             , push* (true , g true false) (g true false , g false false) refl i)
--     cong-GFUN r i k =
--       hcomp (λ j → λ {(r = i0) → G-coh-inr-t-fill g i k j
--                    ; (r = i1) → G-coh-inr-t-fill g i k j
--                    ; (i = i0) → G-coh-inr-t-fill g i k j
--                    ; (i = i1) → G-coh-inr-t-fill g i k j
--                    ; (k = i0) → G-coh-inr-t-fill g i k j
--                    ; (k = i1) → G-coh-inr-t-fill g i k j
--                    })
--               (inlR (true , inlR (true , g true true)))

--   G-coh-eq2 : (g : (i j : Bool) → A i j)
--       (x : Bool) →
--       Cube
--       (λ i _ → G-inler (g true true) (g false) x i)
--       (λ s t →
--          GFUN A
--          (G-inr-inl-inr*₂ (RP∞'∙ ℓ) A g x (λ i → g i i) refl s t))
--       (λ i j → GFUN A
--          (btm-map (RP∞'∙ ℓ) (RP∞'∙ ℓ) A
--           (x , leftMapBool (RP∞'∙ ℓ) A x
--            (push (true , true , push (inr (idEquiv Bool , refl , g)) j) i)))) -- ()
--       (λ i j → coh-eq2 g j i) -- (G-coh-inr g x)
--       (λ i j → G-coh-eq1 (λ i → g i i) (g false) refl x j i)
--       λ i j → G-coh-inr g x j i
--   G-coh-eq2 g x =
--     G-coh-eq2-main g x
--     ▷ λ a s t → GFUN A (G-inr-inl-inr*₂-refl (RP∞'∙ ℓ) A g x (~ a) s t)

--   G-coh-eq-l : (g : (i j : Bool) → A i j) (x : Bool) →
--       Cube
--       (λ i j → GFUN A
--          (btm-map (RP∞'∙ ℓ) (RP∞'∙ ℓ) A
--            (x , leftMapBool (RP∞'∙ ℓ) A x (push (true , true , push (inl g) i) j))))
--       (coh-eq-l g)
--       (G-push-inl (λ i → g i true) (g false) refl x)
--       (G-coh-inr g x)
--       (λ i _ → G-inler (g true true) (g false) x i)
--       (λ s t → GFUN A (G-inr-inl-inl*₂ (RP∞'∙ ℓ) A (λ i → g i true) x g (λ z → refl) s t))
--   G-coh-eq-l g false i j k =
--     hcomp (λ r → λ {(i = i0) → f _ (push*
--                                       (true , inlR (false , g (RP'.notI (RP∞'∙ ℓ) true) true))
--                                       (inlR (false , g (RP'.notI (RP∞'∙ ℓ) true) true) ,
--                                        inlR (false , g (RP'.notI (RP∞'∙ ℓ) true) false)) refl) r j k
--                    ; (j = i0) → push* (true , push* (false , g false true) (g true true , g false true) refl i)
--                                        ((push* (false , g false true) (g true true , g false true) refl i)
--                                       , (inlR (false , g false false)))
--                                        refl (r ∧ ~ k)
--                    ; (j = i1) → push* (true , push* (false , g false true) (g true true , g false true) refl i)
--                                        ((push* (false , g false true) (g true true , g false true) refl i)
--                                       , (push* (false , g false false) (g true false , g false false) refl(i ∧ k)))
--                                        refl r
--                    ; (k = i0) → push* (true , (push* (false , g false true) (g true true , g false true) refl i))
--                                       ((push* (false , g false true) (g true true , g false true) refl i)
--                                      , (inlR (false , g false false)))
--                                       refl r
--                    ; (k = i1) → push* (true , push* (false , g false true) (g true true , g false true) refl i)
--                                        ((push* (false , g false true) (g true true , g false true) refl i)
--                                       , (push* (false , g false false) (g true false , g false false) refl i))
--                                        refl (j ∧ r)})
--           (inlR (true , push* (false , g false true) (g true true , g false true) refl i))
--     where
--     f : ∀ {ℓ} {A : Type ℓ} {x : A} (y : A) (p : x ≡ y) -- r j k
--       → Cube refl (λ j k → p (j ∨ ~ k))
--              (λ r k → p (r ∧ ~ k)) (λ r k → p r)
--              (λ r j → p r) (λ r j → p (j ∧ r))
--     f = J> refl
--   G-coh-eq-l g true i j k =
--     hcomp (λ r → λ {(i = i0) → push* (true , inlR (true , g true true))
--                                        (inlR (true , g true true) , inlR (true , g true false))
--                                        refl (j ∧ k)
--                    ; (i = i1) → s1 r j k
--                    ; (j = i0) → G-push-inl-filler (λ k → g k true) (g false) refl i k r
--                    ; (j = i1) → G-coh-inr-t-fill g i k i1
--                    ; (k = i0) → push* (true , inlR (true , g true true))
--                                        (inrR (g true true , g false true) , inlR (false , g false false))
--                                        (sym (push* (true , g true true) (g true true , g false true) refl)) i
--                    ; (k = i1) → push* (true , push* (true , g true true) (g true true , g false true) refl (i ∧ r))
--                                        ((push* (true , g true true) (g true true , g false true) refl i)
--                                       , (push* (true , g true false) (g true false , g false false) refl i))
--                                       (λ k →  push* (true , g true true) (g true true , g false true) refl (i ∧ (r ∨ ~ k))) j
--                    })
--      (hcomp (λ r → λ {(i = i0) → push* (true , inlR (true , g true true))
--                                          (inlR (true , g true true) , inlR (true , g true false))
--                                           refl (j ∧ k ∧ r)
--                    ; (i = i1) → SQ-f j k r
--                    ; (j = i0) → push* (true , inlR (true , g true true))
--                                         (inrR (g true true , g false true) , inlR (false , g false false))
--                                         (sym (push* (true , g true true) (g true true , g false true) refl))
--                                         (i ∧ ~ k ∧ r)
--                    ; (j = i1) → G-coh-inr-t-fill g i k r
--                    ; (k = i0) → push* (true , inlR (true , g true true))
--                                        ((inrR (g true true , g false true))
--                                       , (inlR (false , g false false)))
--                                        (sym (push* (true , g true true)
--                                                    (g true true , g false true)
--                                                    refl)) (i ∧ r)
--                    ; (k = i1) → push* (true , inlR (true , g true true))
--                                        ((push* (true , g true true) (g true true , g false true) refl i)
--                                        , (push* (true , g true false) (g true false , g false false) refl i))
--                                        (λ s → push* (true , g true true) (g true true , g false true) refl (i ∧ ~ s)) (r ∧ j)
--                    })
--             (inlR (true , inlR (true , g true true))))
--     where
--     SQ-f : (j k r : _) → GOALTY' A
--     SQ-f j k r =
--       hfill (λ r → λ {(j = i0) → push* (true , inlR (true , g true true))
--                                                  (inrR (g true true , g false true) , inlR (false , g false false))
--                                                  (sym (push* (true , g true true) (g true true , g false true) refl))
--                                                  (~ k ∧ r)
--                      ; (j = i1) → push* (true , (inlR (true , g true true)))
--                                          (inrR (g true true , g false true)
--                                         , push* (false , g false false) (g true false , g false false) refl k)
--                                         (sym (push* (true , g true true) (g true true , g false true) refl)) r
--                      ; (k = i0) → push* (true , inlR (true , g true true))
--                                           (inrR (g true true , g false true) , inlR (false , g false false))
--                                           (sym (push* (true , g true true) (g true true , g false true) refl))
--                                           r
--                      ; (k = i1) → push* (true , inlR (true , g true true))
--                                          (inrR (g true true , g false true) , inrR (g true false , g false false))
--                                          (sym (push* (true , g true true) (g true true , g false true) refl)) (j ∧ r)})
--             (inS (inlR (true , inlR (true , g true true))))
--             r

--     SQ : Square _ _ _ _
--     SQ j k = SQ-f j k i1

--     s1 : Cube SQ
--               (λ j k → coh-eq-l-fill g j k i1)
--               (λ r k → G-push-inl-filler (λ k → g k true) (g false) refl i1 k r)
--               (λ r k → G-coh-inr-t-fill g i1 k i1)
--               (λ r j → inrR (inrR (g true true , g false true) , inlR (false , g false false)))
--               (λ r j → push* (true , push* (true , g true true) (g true true , g false true) refl r)
--                               (inrR (g true true , g false true) , inrR (g true false , g false false))
--                               (λ k → push* (true , g true true) (g true true , g false true) refl (r ∨ ~ k)) j)
--     s1 r j k =
--       hcomp (λ i →
--         λ {(j = i0) → push* (true , push* (true , g true true) (g true true , g false true) refl r)
--                             (inrR (g true true , g false true) , inlR (false , g false false))
--                             (λ s → push* (true , g true true) (g true true , g false true) refl (~ s ∨ r))
--                             (~ k ∧ i)
--          ; (j = i1) → push* (true , push* (true , g true true) (g true true , g false true) refl r)
--                              ((inrR (g true true , g false true))
--                              , (push* (false , g false false) (g true false , g false false) refl k))
--                              (λ j → push* (true , g true true) (g true true , g false true) refl (r ∨ ~ j)) i
--          ; (k = i0) → push* (true , push* (true , g true true) (g true true , g false true) refl r)
--                              ((inrR (g true true , g false true))
--                              , (inlR (false , g false false)))
--                              (λ s → push* (true , g true true) (g true true , g false true) refl (r ∨ ~ s)) i
--          ; (k = i1) → push* (true , push* (true , g true true) (g true true , g false true) refl r)
--                              ((inrR (g true true , g false true)) , (inrR (g true false , g false false)))
--                              (λ k → push* (true , g true true) (g true true , g false true) refl (r ∨ ~ k)) (j ∧ i)})
--         (inlR (true , push* (true , g true true) (g true true , g false true) refl r))

-- open 𝕄
-- 𝕄inst· : ∀ {ℓ} → 𝕄inst {ℓ = ℓ}
-- inler 𝕄inst· = Sol.inler
-- inr-inr 𝕄inst· = inrerr
-- inr-inl-inl 𝕄inst· = inr-inl-inl*
-- inr-inl-inr 𝕄inst· = inr-inl-inr*
-- push-inl 𝕄inst· = Sol.push-inl
-- coh-inr 𝕄inst· = Sol.coh-inr
-- coh-eq1 𝕄inst· = Sol.coh-eq1
-- coh-eq2 𝕄inst· = Sol.coh-eq2
-- coh-eq-l 𝕄inst· = Sol.coh-eq-l
-- G-inler 𝕄inst· = Sol.G-inler
-- G-inr-inr 𝕄inst· = G-inr-inr*
-- G-inr-inl-inl₁ 𝕄inst· = G-inr-inl-inl*₁
-- G-inr-inl-inl₂ 𝕄inst· = G-inr-inl-inl*₂
-- G-inr-inl-inr₁ 𝕄inst· = G-inr-inl-inr*₁
-- G-inr-inl-inr₂ 𝕄inst· I A f p q i = G-inr-inl-inr*₂ I A p i f (funExt q)
-- G-push-inl 𝕄inst· = Sol.G-push-inl
-- G-coh-inr 𝕄inst· = Sol.G-coh-inr
-- G-coh-eq1 𝕄inst· = Sol.G-coh-eq1
-- G-coh-eq2 𝕄inst· A g x i j k = Sol.G-coh-eq2 A g x k i j
-- G-coh-eq-l 𝕄inst· = Sol.G-coh-eq-l

-- TheId : ∀ {ℓ} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
--   → Better! I J A → GOALTY I J A
-- TheId {ℓ = ℓ} I J A = elimPushout (btm-map I J A) (FF I J A .fst) λ {(i , x) → FF I J A .snd i x}
--   where
--   FF = MEGA-inst (λ I J A _ → GOALTY I J A) (λ A _ → GOALTY' A) (λ A _ → GFUNEq A)
--                  (λ I J A x i → btm-map I J A (i , leftMap** I J A i x))
--                  (λ A x a j → GFUN A (btm-map (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (a , leftMapBool (RP∞'∙ ℓ) A a (push x j))))
--                  (λ t A x y i → GFUN A (btm-map (RP∞'∙ ℓ) (RP∞'∙ ℓ) A (y , leftMapBool≡ (RP∞'∙ ℓ) A y (push x i) (~ t))))
--                  𝕄inst·

-- module EZ {ℓ : Level} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) where
--   DOMTY : Type ℓ
--   DOMTY = joinR-gen (fst I) λ i → joinR-gen (fst J) (A i)

--   equivElim-lem : ∀ {ℓ} {A B : Type ℓ}
--                (C : B → Type ℓ)
--                (e : A ≃ B)
--                → ((a : A) → C (fst e a))
--                → ((b : B) → C b)
--   equivElim-lem C e ind b = subst C (secEq e b) (ind (invEq e b))

--   equivElim-lem-id : ∀ {ℓ} {A B : Type ℓ} (C : B → Type ℓ)
--                → (e : A ≃ B)
--                → (ind : (a : A) → C (fst e a))
--                → (a : A)
--                → equivElim-lem C e ind (fst e a) ≡ ind a
--   equivElim-lem-id {A = A} {B = B} C =
--     EquivJ (λ A e →
--                 (ind : (a : A) → C (fst e a))
--                → (a : A)
--                → equivElim-lem C e ind (fst e a) ≡ ind a)
--            λ ind a → transportRefl (ind a)

--   megaty : (f : TotΠ (λ i → Σ-syntax (fst J) (A i))) → Type ℓ
--   megaty f =
--     Σ[ h ∈ ΠR-extend* I J A ]
--       Σ[ h2 ∈ (((g : (i₁ : fst I) (j : fst J) → A i₁ j)
--               (p : (i₁ : fst I) → g i₁ (f i₁ .fst) ≡ f i₁ .snd)
--             → h ≡ inr (inr g))) ]
--        ((t : fst I)
--          → Σ[ one ∈ (((q : (j : fst J) → A (RP'.notI I t) j) (p : q (f (RP'.notI I t) .fst) ≡ f (RP'.notI I t) .snd)
--                    → inl (t , f t , q) ≡ h)) ]
--          (((g : (i₂ : fst I) (j : fst J) → A i₂ j)
--               (p : (i₂ : fst I) → g i₂ (f i₂ .fst) ≡ f i₂ .snd)
--            → Square (λ j → inl (t , f t , g (I .snd .fst .fst t)))
--                     (h2 g p)
--                     (one (g (RP'.notI I t)) (p _))
--                     (push (t , inr (f t , g , p t))))))

--   megaty-b : (f : _) → megaty (Iso.inv (TotAIso I J {A}) f)
--   fst (megaty-b f) = inr (inl f)
--   fst (snd (megaty-b f)) g p k = inr (push (f , (g , p)) k)
--   fst (snd (snd (megaty-b f)) t) g q = push (t , (inl (f , g , q)))
--   snd (snd (snd (megaty-b f)) t) g q i j = push (t , push (f , g , q) j) i

--   abstract
--     megaty-ba : (f : _) → megaty f
--     megaty-ba =
--       equivElim-lem megaty (invEquiv (isoToEquiv (TotAIso I J {A})))
--        megaty-b

--     megaty-ba≡ : (f : _) → megaty-ba (Iso.inv (TotAIso I J {A}) f) ≡ megaty-b f
--     megaty-ba≡ =
--       equivElim-lem-id megaty (invEquiv (isoToEquiv (TotAIso I J {A})))
--         megaty-b

--   L2-side : 2-elter.ΠR-extend I (fst J) A
--           → ΠR-extend* I J A
--   L2-side (inl x) = inl x
--   L2-side (inr (inl f)) = megaty-ba f .fst
--   L2-side (inr (inr x)) = inr (inr x)
--   L2-side (inr (push (f , g , p) i)) = megaty-ba f .snd .fst g p i
--   L2-side (push (t , inl (f , q , p)) i) = megaty-ba f .snd .snd t .fst q p i
--   L2-side (push (t , inr x) i) = push (t , inr x) i
--   L2-side (push (t , push (f , g , p) j) i) = megaty-ba f .snd .snd t .snd g p i j


-- module _ {ℓ : Level} (J : RP∞' ℓ) (A : Bool → fst J → Type ℓ) where
--   open EZ (RP∞'∙ ℓ) J A

--   T = TotAIso (RP∞'∙ ℓ) J {A}

--   L2-side-Bool-inl : (a : _)
--     → leftFun (fst J) A (inl a) ≡ leftFun*-fullBool J A true (EZ.L2-side (RP∞'∙ ℓ) J A (inl a))
--   L2-side-Bool-inl (false , snd₁) = refl
--   L2-side-Bool-inl (true , snd₁) = refl

--   L2-side-Bool-push-inr : (t : Bool) (x : 2-elter.left-push↑ᵣ (RP∞'∙ ℓ) (fst J) A t)
--     → Square (λ i → leftFun (fst J) A (push (t , inr x) i))
--               (λ i → leftFun*-fullBool J A true (push (t , inr x) i))
--               (L2-side-Bool-inl (t , fst x , fst (snd x) (not t)))
--               refl
--   L2-side-Bool-push-inr false x = refl
--   L2-side-Bool-push-inr true x = refl

--   TYVM : (f : TotΠ (λ i → Σ-syntax (fst J) (A i))) (q : megaty f)
--     → Type ℓ
--   TYVM f q =
--     Σ[ p1 ∈ inlR (f true) ≡ leftFun*-fullBool J A true (q .fst) ]
--       Σ[ p2 ∈ (((g : (i₁ : Bool) (j : fst J) → A i₁ j)
--                 (p : (i₁ : fst (RP∞'∙ ℓ)) → g i₁ (f i₁ .fst) ≡ f i₁ .snd)
--              → Square p1 refl
--                       (push* (f true) (g true) (p true))
--                       (λ i → leftFun*-fullBool J A true (q .snd .fst g p i)))) ]
--         ((t : Bool)
--         → Σ[ p3 ∈ ((g : (j : fst J) → A (2-elter.notI (RP∞'∙ ℓ) (fst J) A t) j)
--                      (p : g (f (not t) .fst) ≡ f (not t) .snd)
--                 → Square
--                     (L2-side-Bool-inl (t , 2-elter.PushTop→left-push (RP∞'∙ ℓ) (fst J) A (t , inl (f , g , p)) .snd))
--                     p1
--                     (cong (leftFun (fst J) A) (push (t , inl (f , g , p))))
--                     λ i → leftFun*-fullBool J A true (q .snd .snd t .fst g p i)) ]
--              ((g : (i₁ : Bool) (j₁ : fst J) → A i₁ j₁)
--                (p : (i₁ : Bool) → g i₁ (f i₁ .fst) ≡ f i₁ .snd)
--                 → Cube (λ i j → leftFun (fst J) A (push (t , push (f , g , p) j) i))
--                         (λ i j → leftFun*-fullBool J A true (q .snd .snd t .snd g p i j))
--                         (λ k j → L2-side-Bool-inl (t , f t , g (2-elter.notI (RP∞'∙ ℓ) (fst J) A t)) k)
--                         (λ j i → p2 g p i j)
--                         (λ i j → p3 (g (not t)) (p (not t)) j i)
--                         (L2-side-Bool-push-inr t ((f t) , (g , p t)))))

--   abstract
--     TYVM-b : (f : _) → TYVM (Iso.inv T f) (megaty-b f)
--     fst (TYVM-b (inl x , p)) = refl
--     fst (TYVM-b (inr x , p)) = refl
--     fst (snd (TYVM-b (inl x , p))) g q i j =
--       push* (x , p true) (g true) (q true) i
--     fst (snd (snd (TYVM-b (inl x , p))) false) g q i j =
--       push* (x , p true) g q (~ i)
--     fst (snd (snd (TYVM-b (inl x , p))) true) g q i j =
--       inlR (x , p true)
--     snd (snd (snd (TYVM-b (inl x , p))) false) g q i j k =
--       push* (x , p true) (g true) (q true) (~ j ∨ k)
--     snd (snd (snd (TYVM-b (inl x , p))) true) g q i j k =
--       push* (x , p true) (g true) (q true) (k ∧ j)
--     fst (snd (TYVM-b (inr x , p))) g q i j =
--       push* (fst x true , p true) (g true) (q true) i
--     fst (snd (snd (TYVM-b (inr x , p))) false) g q i j =
--       push* (fst x true , p true) g q (~ i)
--     fst (snd (snd (TYVM-b (inr x , p))) true) g q i j =
--       inlR (fst x true , p true)
--     snd (snd (snd (TYVM-b (inr x , p))) false) g q = refl
--     snd (snd (snd (TYVM-b (inr x , p))) true) g q = refl

--     TYVM∙ : (f : _) → TYVM f (megaty-ba f)
--     TYVM∙ = equivElim-lem
--       (λ f → TYVM f (megaty-ba f))
--       (invEquiv (isoToEquiv T))
--       λ f → subst (TYVM (fst (invEquiv (isoToEquiv T)) f))
--                    (sym (megaty-ba≡ f))
--                    (TYVM-b f)


--   L2-side-Bool : (a : _)
--     → leftFun (fst J) A a ≡ leftFun*-fullBool J A true (EZ.L2-side (RP∞'∙ ℓ) J A a)
--   L2-side-Bool (inl (t , a)) = L2-side-Bool-inl (t , a)
--   L2-side-Bool (inr (inl f)) = TYVM∙ f .fst
--   L2-side-Bool (inr (inr x)) = refl
--   L2-side-Bool (inr (push (f , g , p) i)) = TYVM∙ f .snd .fst g p i
--   L2-side-Bool (push (t , inl (f , g , p)) i) = TYVM∙ f .snd .snd t .fst g p i
--   L2-side-Bool (push (t , inr x) i) j = L2-side-Bool-push-inr t x j i
--   L2-side-Bool (push (t , push (f , g , p) j) i) k = TYVM∙ f .snd .snd t .snd g p k i j

-- mainCoh : {ℓ : Level} (I : RP∞' ℓ) (t : fst I) (J : RP∞' ℓ) (A : fst I → fst J → Type ℓ)
--   → (a : _)
--   → snd (leftFunExt I (fst J) A (t , a))
--   ≡ leftFun*-full I J A t (EZ.L2-side I J A a)
-- mainCoh {ℓ = ℓ} = JRP∞' λ J A a →
--     (λ k → help k (fst J) A a)
--   ∙ L2-side-Bool J A a
--   ∙ sym (leftFunBool≡' J A true (EZ.L2-side (RP∞'∙ ℓ) J A a))
--   where
--   help :  leftFunExtCurry (RP∞'∙ ℓ) true ≡ leftFun
--   help = JRP∞'∙ leftFun



-- module _ {ℓ : Level} (I J : RP∞' ℓ) (A : fst I → fst J → Type ℓ) where
--   open EZ I J A
--   L2 : joinR-Push' I (fst J) A → Pushout (λ i → fst i , leftFun*-full I J A (fst i) (snd i)) snd
--   L2 (inl x) = inl x
--   L2 (inr x) = inr (L2-side x)
--   L2 (push (t , a) i) = ((λ k → inl (t , mainCoh I t J A a k)) ∙ push (t , L2-side a)) i

--   mainComm : DOMTY → GOALTY I J A
--   mainComm x = TheId I J A (ΠR-pushout→Better! I J A (L2 x'))
--     where
--     x' : joinR-Push' I (fst J) A
--     x' = Iso.fun (FullIso₁ I J A) (Iso.fun (joinR-Equiv) x)

-- joinR→join : ∀ {ℓ} {A : Bool → Type ℓ}
--   → joinR-gen Bool A → join (A true) (A false)
-- joinR→join (inlR (false , a)) = inr a
-- joinR→join (inlR (true , a)) = inl a
-- joinR→join (inrR x) = inl (x true)
-- joinR→join (push* (false , a) b x i) = push (b true) a (~ i)
-- joinR→join (push* (true , a) b x i) = inl (x (~ i))

-- join→joinR : ∀ {ℓ} {A : Bool → Type ℓ}
--   → join (A true) (A false)
--   → joinR-gen Bool A
-- join→joinR (inl x) = inlR (true , x)
-- join→joinR (inr x) = inlR (false , x)
-- join→joinR (push a b i) =
--    (push* (true , a) (CasesBool true a b) refl
--   ∙ sym (push* (false , b) (CasesBool true a b) refl)) i

-- join-joinR-iso : ∀ {ℓ} {A : Bool → Type ℓ}
--   → Iso (joinR-gen Bool A) (join (A true) (A false))
-- Iso.fun join-joinR-iso = joinR→join
-- Iso.inv join-joinR-iso = join→joinR
-- Iso.rightInv join-joinR-iso (inl x) = refl
-- Iso.rightInv join-joinR-iso (inr x) = refl
-- Iso.rightInv (join-joinR-iso {A = A}) (push a b i) j = help j i
--   where
--   help : cong (joinR→join {A = A})
--                (push* (true , a) (CasesBool true a b) refl
--               ∙ sym (push* (false , b) (CasesBool true a b) refl))
--       ≡ push a b
--   help = cong-∙ joinR→join
--             (push* (true , a) (CasesBool true a b) refl)
--             (sym (push* (false , b) (CasesBool true a b) refl))
--        ∙ sym (lUnit (push a b))
-- Iso.leftInv join-joinR-iso (inlR (false , y)) = refl
-- Iso.leftInv join-joinR-iso (inlR (true , y)) = refl
-- Iso.leftInv join-joinR-iso (inrR x) = push* (true , x true) x refl
-- Iso.leftInv (join-joinR-iso {A = A}) (push* (false , x) b p i) j =  h x p j i
--   where
--   h : (x : A false) (p : b false ≡ x)
--     → Square {A = joinR-gen Bool A}
--              (sym (push* (true , b true) (CasesBool true (b true) x) refl
--                ∙ sym (push* (false , x) (CasesBool true (b true) x) refl)))
--              (push* (false , x) b p)
--              refl
--              (push* (true , b true) b refl)
--   h = J> ((λ s → sym (push* (true , b true) (CasesBoolη b s) refl
--                 ∙ sym (push* (false , b false) (CasesBoolη b s) refl)))
--         ◁ λ i j → compPath-filler'
--                     (push* (true , b true) b refl)
--                     (sym (push* (false , b false) b refl)) (~ i) (~ j))
-- Iso.leftInv (join-joinR-iso {A = A}) (push* (true , x) b p i) j = h x p j i
--   where
--   h : (x : _) (p : b true ≡ x)
--     → Square {A = joinR-gen Bool A}
--               (λ i → inlR (true , p (~ i))) (push* (true , x) b p )
--               refl (push* (true , b true) b (λ _ → b true))
--   h = J> λ i j → push* (true , b true) b refl (i ∧ j)
