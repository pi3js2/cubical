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


module Cubical.Cohomology.EilenbergMacLane.GenSmash where


RP∞ = 2-EltType₀

2-Elt≃ : (X Y : RP∞) → fst X ≃ fst Y → X ≡ Y
2-Elt≃ X Y p = Σ≡Prop (λ _ → squash₁) (ua p)

2-Elt≃-idEquiv : (X : RP∞) → 2-Elt≃ X X (idEquiv (fst X)) ≡ refl
2-Elt≃-idEquiv X =
  ΣSquareSet (λ _ → isProp→isSet squash₁) uaIdEquiv

RP∞pt→Prop : ∀ {ℓ} {B : RP∞ → Type ℓ}
  → ((x : _) → isProp (B x))
  → B Bool*
  → (x : _) → B x
RP∞pt→Prop {B = B} p b =
  uncurry λ X → PT.elim (λ _ → p _)
    λ x → subst B (2-Elt≃ Bool* (X , ∣ x ∣₁) (invEquiv x)) b

RP∞pt→Prop-β : ∀ {ℓ} {B : RP∞ → Type ℓ}
  → (pr : (x : _) → isProp (B x))
  → (b : B Bool*)
  → RP∞pt→Prop {B = B} pr b Bool* ≡ b
RP∞pt→Prop-β {B = B} p q =
    (λ i → subst B (2-Elt≃ Bool* Bool* (invEquivIdEquiv Bool i)) q)
  ∙ (λ i → subst B (2-Elt≃-idEquiv Bool* i) q)
  ∙ transportRefl q

DiscreteBool : Discrete Bool
DiscreteBool false false = yes refl
DiscreteBool false true = no (true≢false ∘ sym)
DiscreteBool true false = no true≢false
DiscreteBool true true = yes refl


decPt : (X : RP∞) → Discrete (fst X)
decPt = RP∞pt→Prop (λ _ → isPropDiscrete) DiscreteBool

Bool≃Charac : Iso (Bool ≃ Bool) Bool
Bool≃Charac = iso F G (λ { false → refl ; true → refl}) λ e → Σ≡Prop isPropIsEquiv (funExt (F→G→F e))
  where
  F : Bool ≃ Bool → Bool
  F e = fst e true

  G : Bool → Bool ≃ Bool
  G false = notEquiv
  G true = idEquiv Bool

  F→G→F : (e : Bool ≃ Bool) (x : Bool) → G (F e) .fst x ≡ e .fst x
  F→G→F e with (dichotomyBool (fst e true)) | (dichotomyBool (fst e false))
  ... | inl p | inl q = ⊥.rec
    (true≢false (sym (retEq e true) ∙∙ cong (invEq e) (p ∙ sym q) ∙∙ retEq e false))
  ... | inl p | inr q = λ { false → (λ i → G (p i) .fst false) ∙ sym q
                          ; true → (λ i → G (p i) .fst true) ∙ sym p}
  ... | inr p | inl q = λ { false → (λ i → G (p i) .fst false) ∙ sym q
                          ; true → (λ i → G (p i) .fst true) ∙ sym p}
  ... | inr p | inr q =
    ⊥.rec (true≢false  (sym (retEq e true) ∙∙ cong (invEq e) (p ∙ sym q) ∙∙ retEq e false))

BoolAutoElim : ∀ {ℓ} {A : Bool ≃ Bool → Type ℓ}
  → A (idEquiv Bool)
  → A notEquiv
  → (x : _) → A x
BoolAutoElim {A = A} p q e with (dichotomyBool (fst e true))
... | inl z = subst A (cong (Iso.inv Bool≃Charac) (sym z)
                     ∙ Iso.leftInv Bool≃Charac e ) p
... | inr z = subst A (cong (Iso.inv Bool≃Charac) (sym z)
                     ∙ Iso.leftInv Bool≃Charac e) q

pst : {x y : Bool} → isProp (Bool , x ≃∙ Bool , y)
pst {x} {y} =
  subst2 (λ x y → isProp (x ≃∙ y)) (help x) (help y)
    (isContr→isProp lem)
  where
  lem : isContr (Bool , true ≃∙ Bool , true)
  fst lem = idEquiv Bool , refl
  snd lem e = Σ≡Prop (λ _ → isSetBool _ _)
    (cong (Iso.inv Bool≃Charac) (sym (snd e)) ∙ Iso.leftInv Bool≃Charac (fst e))

  help : isHomogeneous (Bool , true)
  help false = ΣPathP ((ua notEquiv) , toPathP refl)
  help true = refl

isPropNegBool : isProp (Σ[ e ∈ (Bool ≃ Bool) ] ¬ e ≡ idEquiv Bool)
isPropNegBool = isContr→isProp help
  where
  help : isContr (Σ[ e ∈ (Bool ≃ Bool) ] ¬ e ≡ idEquiv Bool)
  fst help = notEquiv , (λ p → true≢false (funExt⁻ (cong fst p) false))
  snd help (e , g) =
    Σ≡Prop (λ _ → isProp¬ _)
      (⊎.rec (λ p → ⊥.rec (g (sym (Iso.leftInv Bool≃Charac e)
                    ∙ cong (Iso.inv Bool≃Charac) p)))
              (λ p → sym (cong (Iso.inv Bool≃Charac) p)
                        ∙ (Iso.leftInv Bool≃Charac e))
              (dichotomyBool (fst e true)))

isPropNegRP∞ : (X : RP∞) → isProp (Σ[ e ∈ (fst X ≃ fst X) ] ¬ e ≡ idEquiv (fst X))
isPropNegRP∞ = RP∞pt→Prop (λ _ → isPropIsProp) isPropNegBool

notEquiv* : (X : RP∞) → Σ[ e ∈ (fst X ≃ fst X) ] ¬ e ≡ idEquiv (fst X)
notEquiv* =
  RP∞pt→Prop isPropNegRP∞
    (notEquiv , (λ p → true≢false (funExt⁻ (cong fst p) false)))

isSetRPpt : (X : RP∞) → isSet (fst X)
isSetRPpt = RP∞pt→Prop (λ _ → isPropIsSet) isSetBool

not* : (X : RP∞) → fst X → fst X
not* X = fst (fst (notEquiv* X))

not¬ : (a : Bool) → ¬ (a ≡ not a)
not¬ false p = false≢true p
not¬ true p = false≢true (sym p)

isPropPath⊎RP∞ : (I : RP∞) (i j : fst I) → isProp ((i ≡ j) ⊎ (i ≡ not* I j))
isPropPath⊎RP∞ = RP∞pt→Prop (λ _ → isPropΠ2 λ _ _ → isPropIsProp)
  λ { a b (inl x) (inl x₁) i → inl (isSetBool _ _ x x₁ i)
    ; a b (inl x) (inr x₁) → ⊥.rec (not¬ b (sym x ∙ x₁))
    ; a b (inr x) (inl x₁) → ⊥.rec (not¬ b (sym x₁ ∙ x))
    ; a b (inr x) (inr x₁) i → inr (isSetBool _ _ x x₁ i)}

RP∞DecPath : (I : RP∞) (i j : fst I) → (i ≡ j) ⊎ (i ≡ not* I j)
RP∞DecPath = RP∞pt→Prop (λ _ → isPropΠ2 (isPropPath⊎RP∞ _))
  λ { false false → inl refl
  ; false true → inr refl
  ; true false → inr refl
  ; true true → inl refl}

RP∞DecPath→ : ∀ {ℓ} (I : RP∞) (A : fst I → fst I → Type ℓ) (i j : fst I)
  → ((i ≡ j) ⊎ (i ≡ not* I j) → A i j) → A i j
RP∞DecPath→ I A i j p = p (RP∞DecPath I i j)

not*not* : (X : RP∞) (x : fst X) → not* X (not* X x) ≡ x
not*not* = RP∞pt→Prop (λ X → isPropΠ λ _ → isSetRPpt X _ _) F
  where
  F : (x : fst Bool*) → not* Bool* (not* Bool* x) ≡ x
  F false = refl
  F true = refl
not-charac : (X : RP∞) (x y : fst X) → ¬ x ≡ y → x ≡ not* X y
not-charac = RP∞pt→Prop (λ X → isPropΠ3 λ _ _ _ → isSetRPpt X _ _) F
  where
  F : (x y : fst Bool*) → ¬ x ≡ y → x ≡ not* Bool* y
  F false false q = ⊥.rec (q refl)
  F false true q = refl
  F true false q = refl
  F true true q = ⊥.rec (q refl)

¬not≡id : (X : RP∞) (x : fst X) → ¬ x ≡ not* X x
¬not≡id =
  RP∞pt→Prop (λ _ → isPropΠ λ _ → isProp¬ _) F
  where
  F : (x : fst Bool*) → ¬ x ≡ not* Bool* x
  F true = true≢false
  F false = true≢false ∘ sym 


preCasesRP : ∀ {ℓ} (X : RP∞) {A : fst X → Type ℓ} (x₀ : fst X)
  → A x₀
  → A (not* X x₀)
  → (x : _) → Dec (x₀ ≡ x)
  → A x
preCasesRP X {A = A} x₀ l r x (yes p) = subst A p l
preCasesRP X {A = A} x₀ l r x (no ¬p) = subst A (sym (not-charac X x x₀ (¬p ∘ sym))) r

CasesBool* : ∀ {ℓ} {A : Bool → Type ℓ}
  → isContr (Σ[ f ∈ (A true → A false → (x : _) → A x) ]
      ((a : A true) (b : A false) → (f a b true ≡ a) × (f a b false ≡ b)))
fst (fst CasesBool*) a b false = b
fst (fst CasesBool*) a b true = a
snd (fst CasesBool*) a b = refl , refl
fst (snd CasesBool* (f , p) i) a b false = p a b .snd (~ i)
fst (snd CasesBool* (f , p) i) a b true = p a b .fst (~ i)
fst (snd (snd CasesBool* (f , p) i) a b) j = p a b .fst (~ i ∨ j)
snd (snd (snd CasesBool* (f , p) i) a b) j = p a b .snd (~ i ∨ j)

T2' : ∀ {ℓ} (X : RP∞) (x : fst X) (A : fst X → Type ℓ) → Type ℓ 
T2' X x A = Σ[ f ∈ ((a : A x) (b : A (not* X x)) → (x : _) → A x) ]
             ((a : _) (b : _) → (f a b x ≡ a) × (f a b (not* X x) ≡ b))

fstP-RP∞ : (X Y : RP∞) → Iso (fst X ≡ fst Y) (X ≡ Y)
Iso.fun (fstP-RP∞ X Y) p = Σ≡Prop (λ _ → squash₁) p
Iso.inv (fstP-RP∞ X Y) = cong fst
Iso.rightInv (fstP-RP∞ X Y) p =
  ΣSquareSet (λ _ → isProp→isSet squash₁) λ _ i → p i .fst
Iso.leftInv (fstP-RP∞ X Y) p = refl

isGroupoidRP∞ : isGroupoid RP∞
isGroupoidRP∞ =
 uncurry λ X → PT.elim (λ _ → isPropΠ λ _ → isPropIsSet)
  (EquivJ (λ X x → (b : RP∞) → isSet (Path RP∞ (X , ∣ x ∣₁) b))
    (uncurry λ Y → PT.elim (λ _ → isPropIsSet)
      (EquivJ (λ Y x → isSet (Path RP∞ (Bool , ∣ idEquiv Bool ∣₁) (Y , ∣ x ∣₁)))
        (isOfHLevelRetractFromIso 2
          (compIso (invIso (fstP-RP∞ Bool* Bool*))
            (compIso (equivToIso univalence) Bool≃Charac)) isSetBool))))

isCTot : isContr (Σ[ X ∈ RP∞ ] fst X)
fst isCTot = Bool* , true
snd isCTot = uncurry (uncurry λ X
  → PT.elim→Set (λ _ → isSetΠ λ _ → t _ _)
      (λ x y → psts X x y _ refl)
      λ e q → PathPFlip λ x → ΣSquareSet isSetRPpt
        (ΣSquareSet (λ _ → isProp→isSet squash₁)
          (maincoh X e q x _ _ refl refl)))
  where
  PathPFlip : ∀ {ℓ ℓ'} {A : Type ℓ} {B : I → A → Type ℓ'} {f0 : (x : _) → B i0 x} {f1 : (x : _) → B i1 x}
    → ((x : _) → PathP (λ i → B i x) (f0 x) (f1 x))
    → PathP (λ i → (x : _) → B i x) f0 f1
  PathPFlip p i x = p x i
  

  t : isGroupoid (Σ[ X ∈ RP∞ ] fst X)
  t = isOfHLevelΣ 3 isGroupoidRP∞ λ X → isOfHLevelSuc 2 (isSetRPpt X)

  psts :  (X : Type) (x : X ≃ Bool) (y : X) (b : Bool) (t : fst x y ≡ b)
    → Path (Σ[ X ∈ RP∞ ] fst X) (Bool* , true) ((X , ∣ x ∣₁) , y)
  psts X x y false t =
    ΣPathP ((Σ≡Prop (λ _ → squash₁) (ua (compEquiv notEquiv (invEquiv x))))
      , symP (toPathP (cong not (cong (fst x) (transportRefl y)) ∙ cong not t)))
  psts X x y true t = ΣPathP ((Σ≡Prop (λ _ → squash₁) (ua (invEquiv x)))
      , symP (toPathP (cong (fst x) (transportRefl y) ∙ t)))

  booleq-lem : ∀ {X : Type} (e e2 : X ≃ Bool)
    → (x : X) → (fst e x ≡ fst e2 x)
    → e ≡ e2 
  booleq-lem {X = X} =
    EquivJ (λ X e → (e2 : X ≃ Bool)
    → (x : X) → (fst e x ≡ fst e2 x)
    → e ≡ e2 )
    λ e2 x id → te (Iso.fun Bool≃Charac e2) x
      (id ∙ sym (funExt⁻ (cong fst (Iso.leftInv Bool≃Charac e2)) x))
      ∙ Iso.leftInv Bool≃Charac e2
    where
    te : (e2 : Bool) (x : Bool)
      → x ≡ fst (Iso.inv Bool≃Charac e2) x
      → idEquiv Bool ≡ Iso.inv Bool≃Charac e2
    te false false p = ⊥.rec (true≢false (sym p))
    te false true p = ⊥.rec (true≢false p)
    te true x p =
      Σ≡Prop isPropIsEquiv (funExt λ { false → refl ; true → refl})

  invEq≡→≡ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
    → (e q : A ≃ B)
    → invEquiv e ≡ invEquiv q → e ≡ q
  invEq≡→≡ e q p = Σ≡Prop (λ _ → isPropIsEquiv _)
    (funExt λ a → sym (secEq q (e .fst a))
                 ∙ cong (fst q) (sym (funExt⁻ (cong fst p) (e .fst a))
                              ∙ retEq e a))

  maincoh : (X : Type) (e q : X ≃ Bool) (x : X)
    (b1 b2 : Bool) (t1 : fst e x ≡ b1) (t2 : fst q x ≡ b2)
    → cong fst (cong fst (psts X e x b1 t1))
    ≡ cong fst (cong fst (psts X q x b2 t2))
  maincoh X e q x false false t1 t2 =
    cong ua (invEq≡→≡ _ _ (booleq-lem _ _ x (cong not (t1 ∙ sym t2))))
  maincoh X e q x false true t1 t2 =
    cong ua (invEq≡→≡ _ _ (booleq-lem _ _ x (cong not t1 ∙ sym t2)))
  maincoh X e q x true false t1 t2 =
    cong ua (invEq≡→≡ _ _ (booleq-lem _ _ x (t1 ∙ cong not (sym t2))))
  maincoh X e q x true true t1 t2 =
    cong ua (invEq≡→≡ _ _ (booleq-lem _ _ x (t1 ∙ sym t2)))


JRP∞ : ∀ {ℓ} (A : (X : RP∞) (x : fst X) → Type ℓ)
  → A Bool* true
  → {X : _} {x : _} → A X x
JRP∞ A t {X = X} {x = x} = A'Sec (X , x)
  where
  A' : Σ[ X ∈ RP∞ ] (fst X) → Type _
  A' (X , x) = A X x

  A'Sec : (m : Σ[ X ∈ RP∞ ] (fst X)) → A' m
  A'Sec m = subst A' (isCTot .snd m) t


T2 : ∀ {ℓ} (X : RP∞) (A : fst X → Type ℓ) → Type ℓ 
T2 X A = (x : fst X) → T2' X x A
  
isC : ∀ {ℓ} (X : RP∞) (A : fst X → Type ℓ) → isProp (T2 X A)
isC {ℓ} X A = isPropΠ λ x
  → JRP∞ (λ X x → (A : fst X → Type ℓ) → isProp (T2' X x A))
         (λ A → isContr→isProp CasesBool*) {X = X} {x} A
{-
CasesRP-full : ∀ {ℓ} (X : RP∞) (A : fst X → Type ℓ) → T2 X A
CasesRP-full = uncurry λ X
  → PT.elim (λ _ → isPropΠ (isC _))
       λ e A x → (λ t1 t2 r → {!!}) , {!!}
-}


CasesBool-true : ∀ {ℓ} {A : Bool → Type ℓ} (x₀ : Bool)
  → A true → A false → A x₀
CasesBool-true false p q = q
CasesBool-true true p q = p

CasesBool : ∀ {ℓ} {A : Bool → Type ℓ} (x₀ : Bool)
  → A x₀ → A (not* Bool* x₀) → (x : _) → A x
CasesBool {A = A} false p q y = CasesBool-true {A = A} y q p
CasesBool {A = A} true p q y = CasesBool-true {A = A} y p q

CasesBoolβ : ∀ {ℓ} {A : Bool → Type ℓ} (x₀ : Bool)
  → (l : A x₀) (r : A (not* Bool* x₀))
  → (CasesBool {A = A} x₀ l r x₀ ≡ l)
   × (CasesBool {A = A} x₀ l r (not* Bool* x₀) ≡ r)
CasesBoolβ {A = A} false l r = refl , refl
CasesBoolβ {A = A} true l r = refl , refl


CasesRP-base : ∀ {ℓ} (X : Type) (x : X ≃ Bool) (A : X → Type ℓ) → T2 (X , ∣ x ∣₁) A
CasesRP-base {ℓ = ℓ} X =
  EquivJ (λ X x → (A : X → Type ℓ) → T2 (X , ∣ x ∣₁) A)
    λ A → λ g → CasesBool {A = A} g , CasesBoolβ {A = A} g

CasesRP' : (∀ {ℓ} (X : RP∞) (A : fst X → Type ℓ) → T2 X A)
CasesRP' = uncurry λ X
  → PT.elim (λ _ → isPropΠ (isC _))
      (CasesRP-base X)

CasesRP'Bool : ∀ {ℓ}
  → CasesRP' {ℓ} Bool* ≡ ((λ A x → (CasesBool x) , (CasesBoolβ x)))
CasesRP'Bool {ℓ = ℓ} = EquivJ-idEquiv {A = Bool}
      (λ X x → (A : X → Type ℓ) → T2 (X , ∣ x ∣₁) A)
        λ A → λ g → CasesBool {A = A} g , CasesBoolβ {A = A} g

CasesRP : ∀ {ℓ} (X : RP∞) {A : fst X → Type ℓ} (x₀ : fst X)
  → A x₀ → A (not* X x₀) → (x : _) → A x
CasesRP X {A = A} x₀ = CasesRP' X A x₀ .fst

CasesRPβ : ∀ {ℓ} (X : RP∞) {A : fst X → Type ℓ} (x₀ : fst X)
  → (l : A x₀) (r : A (not* X x₀))
  → (CasesRP X {A = A} x₀ l r x₀ ≡ l)
   × (CasesRP X {A = A} x₀ l r (not* X x₀) ≡ r)
CasesRPβ X x₀ = CasesRP' X _ x₀ .snd

CasesRP≡ : ∀ {ℓ} (X : RP∞) {A : fst X → Type ℓ} (x₀ : fst X)
  {x x' : A x₀} {y y' : A (not* X x₀)} (a : _)
  → x ≡ x' → y ≡ y' → CasesRP X {A = A} x₀ x y a ≡ CasesRP X {A = A} x₀ x' y' a
CasesRP≡ X {A = A} x₀ a p q i = CasesRP X {A = A} x₀ (p i) (q i) a

CasesRPβ' : ∀ {ℓ} (X : RP∞) {A : fst X → Type ℓ} (x₀ : fst X)
  → (f : (x : fst X) → A x)
  → CasesRP X x₀ (f x₀) (f (not* X x₀)) ≡ f
CasesRPβ' X x₀ f =
  funExt (CasesRP X x₀
          (CasesRPβ X x₀ (f x₀) (f (not* X x₀)) .fst)
          (CasesRPβ X x₀ (f x₀) (f (not* X x₀)) .snd))

∑RP : (X : RP∞) (n : fst X → ℕ) → ℕ
∑RP = uncurry λ X → rec→Set (isSetΠ (λ _ → isSetℕ))
  (λ e n → n (invEq e true) + n (invEq e false))
  (EquivJ (λ X e → (y : X ≃ Bool) →
      (λ (n : X → ℕ) → n (invEq e true) + n (invEq e false)) ≡
      (λ n → n (invEq y true) + n (invEq y false)))
    (BoolAutoElim refl
      (funExt λ n → +-comm _ _)))

SM : {ℓ : Level} (X : RP∞) (A : fst X → Pointed ℓ) → Type ℓ
SM X A = Pushout {A = Σ (fst X) (fst ∘ A)} {B = fst X} {C = (x : fst X) → A x .fst} fst λ x → CasesRP X {A = fst ∘ A} (fst x) (snd x) (snd (A (not* X (fst x))))


SM∙ : {ℓ : Level} (X : RP∞) (A : fst X → Pointed ℓ) → Pointed ℓ
SM∙ X A = SM X A , inr λ x → A x .snd

J2-elem : ∀ {ℓ} (A : (X : RP∞) (x : fst X) → Type ℓ)
  → Σ[ F ∈ ((e : A Bool* true)
  → (X : _) (y : _) → A X y) ] ((e : A Bool* true) → F e Bool* true ≡ e)
J2-elem A = (λ e X x → transport (λ i → A (toP X x i) (ua-gluePt (_ , isEq X x) i true)) e)
  , λ e → transp-lem {C = A} (toP Bool* true) refl (λ i → ua-gluePt (_ , isEq Bool* true) i true) refl e
             toP-refl
             (toPathP refl)
           ∙ transportRefl e
  where
  h : (X : RP∞) (x : fst X) → Bool → fst X
  h X x true = x
  h X x false = not* X x

  isEq-h : Iso Bool Bool
  Iso.fun isEq-h = h Bool* true
  Iso.inv isEq-h = h Bool* true
  Iso.rightInv isEq-h = λ { false → refl ; true → refl}
  Iso.leftInv isEq-h = λ { false → refl ; true → refl}

  isEq : (X : _) (x : _) → isEquiv (h X x)
  isEq = uncurry λ X → PT.elim (λ _ → isPropΠ λ _ → isPropIsEquiv _)
    (EquivJ (λ X x₁ → (x₂ : X) → isEquiv (h (X , ∣ x₁ ∣₁) x₂))
      λ { false → subst isEquiv (funExt λ { false → refl ; true → refl})
                    (notEquiv .snd)
        ; true → subst isEquiv (funExt λ { false → refl ; true → refl})
                    (idEquiv Bool .snd)})

  transp-lem : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : A → Type ℓ'} {C : (a : A) (b : B a) → Type ℓ''}
    → {x y : A} {b₀ : B x} {b₁ : B y}
    → (p q : x ≡ y)
    → (r : PathP (λ i → B (p i)) b₀ b₁)
    → (s : PathP (λ i → B (q i)) b₀ b₁)
    → (t : C x b₀)
    → (P : p ≡ q)
    → SquareP (λ i j → B (P i j)) r s (λ _ → b₀) (λ _ → b₁)
    → transport (λ i → C (p i) (r i)) t ≡ transport (λ i → C (q i) (s i)) t
  transp-lem {C = C} p q r s t P sq k = transport (λ i → C (P k i) (sq k i)) t

  toP : (X : _) (x : fst X) → Bool* ≡ X
  toP X x = Σ≡Prop (λ _ → squash₁) (ua (_ , isEq X x))

  toP-refl : toP Bool* true ≡ refl
  toP-refl = ΣSquareSet (λ _ → isProp→isSet squash₁) (cong ua (Σ≡Prop (λ _ → isPropIsEquiv _) (funExt λ { false → refl ; true → refl})) ∙ uaIdEquiv)


-- CasesRPΔ : ∀ {ℓ} (X : RP∞) (x : fst X) {A : fst X → Type ℓ} (f : (x : fst X) → A x)
--   → CasesRP X {A = A} x (f x) (f (not* X x)) ≡ f 
-- CasesRPΔ = J2-elem _ .fst λ f → funExt λ { false → transportRefl (f false) ; true → transportRefl (f true)}

-- _×'_ : ∀ {ℓ} (A B : Type ℓ) → Bool → Type ℓ
-- (A ×' B) false = A
-- (A ×' B) true = B

-- _×'∙_ : ∀ {ℓ} (A B : Pointed ℓ) → Bool → Pointed ℓ
-- (A ×'∙ B) false = A
-- (A ×'∙ B) true = B


-- SmashPushoutF : ∀ {ℓ} (A : Bool → Pointed ℓ) → Σ Bool (fst ∘ A) → (x : Bool) → A x .fst
-- SmashPushoutF A (false , a) false = a
-- SmashPushoutF A (false , a) true = A true .snd
-- SmashPushoutF A (true , a) false = A false. snd
-- SmashPushoutF A (true , a) true = a

-- SmashPushout : ∀ {ℓ} (A : Bool → Pointed ℓ) → Type ℓ
-- SmashPushout A = Pushout {A = Σ Bool (fst ∘ A)} {C = (x : Bool) → A x .fst} fst (SmashPushoutF A)

-- module _ {ℓ : Level} {A B : Pointed ℓ} where
--   private
--     boolf : (x : fst A) (y : fst B) → (x : Bool) → (A ×'∙ B) x .fst
--     boolf x y false = x
--     boolf x y true = y

--     bool-fₗ : (a : fst A) (x : Bool) → boolf a (pt B) x ≡ SmashPushoutF (A ×'∙ B) (false , a) x
--     bool-fₗ a false = refl
--     bool-fₗ a true = refl

--     bool-fᵣ : (b : fst B) (x : Bool) → boolf (pt A) b x ≡ SmashPushoutF (A ×'∙ B) (true , b) x
--     bool-fᵣ a false = refl
--     bool-fᵣ a true = refl

--     bool-fΔ : (f : (x : Bool) → _) (x : _) → boolf (f false) (f true) x ≡ f x
--     bool-fΔ f false = refl
--     bool-fΔ f true = refl

--     F : Smash A B → SmashPushout (A ×'∙ B)
--     F basel = inl false
--     F baser = inl true
--     F (proj x y) = inr (boolf x y)
--     F (gluel a i) = (push (false , a) ∙ λ j → inr (funExt (bool-fₗ a) (~ j))) (~ i)
--     F (gluer b i) = (push (true , b) ∙ λ j → inr (funExt (bool-fᵣ b) (~ j))) (~ i)

--     G : SmashPushout (A ×'∙ B) → Smash A B
--     G (inl false) = basel
--     G (inl true) = baser
--     G (inr x) = proj (x false) (x true)
--     G (push (false , y) i) = gluel y (~ i)
--     G (push (true , y) i) = gluer y (~ i)

--   Smash-pushout : Iso (Smash A B) (SmashPushout (A ×'∙ B))
--   Iso.fun Smash-pushout = F
--   Iso.inv Smash-pushout = G
--   Iso.rightInv Smash-pushout (inl false) = refl
--   Iso.rightInv Smash-pushout (inl true) = refl
--   Iso.rightInv Smash-pushout (inr x) i = inr (funExt (bool-fΔ x) i)
--   Iso.rightInv Smash-pushout (push (false , y) i) j =
--     hcomp (λ k → λ {(i = i0) → push (false , y) (~ k)
--                    ; (i = i1) → inr (funExt (help (~ k)) j)
--                    ; (j = i0) → compPath-filler' (push (false , y))
--                                                   (λ j → inr λ x → bool-fₗ y x (~ j)) k i
--                    ; (j = i1) → push (false , y) (i ∨ ~ k)})
--           (inr (funExt (help i1) (~ i ∨ j)))
--     where
--     help : bool-fΔ (SmashPushoutF (A ×'∙ B) (false , y)) ≡ bool-fₗ y
--     help = funExt λ { false → refl ; true → refl}
--   Iso.rightInv Smash-pushout (push (true , y) i) j =
--     hcomp (λ k → λ {(i = i0) → push (true , y) (~ k)
--                    ; (i = i1) → inr (funExt (help (~ k)) j)
--                    ; (j = i0) → compPath-filler' (push (true , y))
--                                                   (λ j → inr λ x → bool-fᵣ y x (~ j)) k i
--                    ; (j = i1) → push (true , y) (i ∨ ~ k)})
--           (inr (funExt (help i1) (~ i ∨ j)))
--     where
--     help : bool-fΔ (SmashPushoutF (A ×'∙ B) (true , y)) ≡ bool-fᵣ y
--     help = funExt λ { false → refl ; true → refl}
--   Iso.leftInv Smash-pushout basel = refl
--   Iso.leftInv Smash-pushout baser = refl
--   Iso.leftInv Smash-pushout (proj x y) = refl
--   Iso.leftInv Smash-pushout (gluel a i) j = cc j i
--     where
--     cc : cong G (sym ((push (false , a)
--        ∙ λ j → inr (funExt (bool-fₗ a) (~ j))))) ≡ gluel a
--     cc = cong sym (cong-∙ G (push (false , a)) (λ j → inr (funExt (bool-fₗ a) (~ j)))
--                 ∙ sym (rUnit (sym (gluel a))))
--   Iso.leftInv Smash-pushout (gluer b i) j = cc j i
--     where
--     cc : cong G (sym ((push (true , b)
--        ∙ λ j → inr (funExt (bool-fᵣ b) (~ j))))) ≡ gluer b
--     cc = cong sym (cong-∙ G (push (true , b)) (λ j → inr (funExt (bool-fᵣ b) (~ j)))
--                 ∙ sym (rUnit (sym (gluer b))))

--   Iso-SmashPushout-SM : Iso (SmashPushout (A ×'∙ B)) (SM Bool* (A ×'∙ B))
--   Iso-SmashPushout-SM =
--     pushoutIso fst _ _ _ (idEquiv _) (idEquiv _) (idEquiv _) refl
--       (funExt λ { (false , t) → funExt
--                   λ { false → sym (transportRefl t)
--                     ; true → sym (transportRefl _)}
--                 ; (true , t) → funExt
--                   λ { false → sym (transportRefl _)
--                     ; true → sym (transportRefl _)}})

--   Iso-Smash-SM : Iso (Smash A B) (SM Bool* (A ×'∙ B))
--   Iso-Smash-SM = compIso Smash-pushout Iso-SmashPushout-SM




-- SM×'-Iso : ∀ {ℓ} (A : Bool → Pointed ℓ) → Iso (SM Bool* (A false ×'∙ A true)) (SM Bool* A)
-- SM×'-Iso A = pathToIso (cong (SM Bool*) (funExt λ { false → refl ; true → refl}))

-- Iso-Smash-SM' : ∀ {ℓ} {A : Bool → Pointed ℓ} → Iso (Smash (A false) (A true)) (SM Bool* A)
-- Iso-Smash-SM' {A = A} = compIso Iso-Smash-SM (SM×'-Iso A)

-- Iso-Smash-SM'∙ : ∀ {ℓ} {A : Bool → Pointed ℓ} → (Smash∙ (A false) (A true)) ≃∙ (SM∙ Bool* A)
-- Iso-Smash-SM'∙ {A = A} =
--   isoToEquiv (Iso-Smash-SM' {A = A})
--   , push (false , snd (A false))
--    ∙ cong inr' (CasesRPΔ Bool* false λ x → A x .snd)
--   where
--   inr' : _ → SM Bool* A
--   inr' = inr

-- Iso-Smash-SM'-proj : ∀ {ℓ} {A : Bool → Pointed ℓ} (h : (x : Bool) → A x .fst)
--   → Iso.inv (Iso-Smash-SM' {A = A}) (inr h) ≡ proj (h false) (h true)
-- Iso-Smash-SM'-proj h = transportRefl _

-- Iso-Smash-SM'-proj' : ∀ {ℓ} {A : Bool → Pointed ℓ} (h : (x : Bool) → A x .fst)
--   → Iso.fun (Iso-Smash-SM' {A = A}) (proj (h false) (h true)) ≡ inr h
-- Iso-Smash-SM'-proj' {A = A} h =
--     sym (cong (Iso.fun (Iso-Smash-SM' {A = A})) (Iso-Smash-SM'-proj h))
--   ∙ Iso.rightInv (Iso-Smash-SM') (inr h)



-- -------

-- _+∞_ : RP∞ → RP∞ → RP∞
-- fst ((X , e) +∞ (Y , e')) = X ≃ Y
-- snd ((X , e) +∞ (Y , e')) =
--   PT.rec squash₁ (λ e → PT.rec squash₁
--     (λ y → ∣ isoToEquiv (compIso (help e y) Bool≃Charac) ∣₁) e') e
--   where
--   help : (x : X ≃ Bool) (y : Y ≃ Bool) → Iso (X ≃ Y) (Bool ≃ Bool)
--   Iso.fun (help x y) p = compEquiv (compEquiv (invEquiv x) p) y
--   Iso.inv (help x y) e = compEquiv x (compEquiv e (invEquiv y))
--   Iso.rightInv (help x y) e =
--     Σ≡Prop isPropIsEquiv (funExt λ f
--       → secEq y _ ∙ cong (e .fst) (secEq x f))
--   Iso.leftInv (help x y) e =
--     Σ≡Prop isPropIsEquiv
--       (funExt λ f
--         → retEq y _ ∙ cong (e .fst) (retEq x f))

-- +∞-comm : (X Y : RP∞) → (X +∞ Y) ≡ (Y +∞ X)
-- +∞-comm X Y = Σ≡Prop (λ _ → squash₁)
--   (isoToPath (iso invEquiv invEquiv (λ e → Σ≡Prop isPropIsEquiv refl)
--     λ e → Σ≡Prop isPropIsEquiv refl))

-- elimBool≃ : ∀ {ℓ} {B : Bool ≃ Bool → Type ℓ}
--   → B (idEquiv Bool) → B notEquiv  → (x : _) → B x
-- elimBool≃ {B = B} b1 b2 x = subst B (Iso.leftInv Bool≃Charac x)
--   (t (Iso.fun Bool≃Charac x))
--   where
--   t : (x : Bool) → B (Iso.inv Bool≃Charac x)
--   t false = b2
--   t true = b1



-- +∞-comm0 : +∞-comm Bool* Bool* ≡ refl
-- +∞-comm0 = ΣSquareSet (λ _ → isProp→isSet squash₁)
--   (cong ua (Σ≡Prop (λ _ → isPropIsEquiv _)
--     (funExt (elimBool≃ (Σ≡Prop (λ _ → isPropIsEquiv _) refl)
--                        (Σ≡Prop (λ _ → isPropIsEquiv _) refl))))
--    ∙ uaIdEquiv)


-- +∞rId : (X : RP∞) → (X +∞ Bool*) ≡ X
-- +∞rId X = Σ≡Prop (λ _ → squash₁)
--   (ua (c (fst X) (snd X) , isEq-c _ _))
--   where
--   c : (X : Type) → ∥ X ≃ Bool ∥₁ → (X ≃ fst Bool*) → X
--   c X p e = invEq e true

--   c* : c Bool ∣ idEquiv _ ∣₁ ≡ Iso.fun Bool≃Charac
--   c* = funExt λ s → cong (c Bool ∣ idEquiv Bool ∣₁)
--          (sym (Iso.leftInv Bool≃Charac s))
--          ∙ t _
--     where
--     t : (b : Bool) → c Bool ∣ idEquiv _ ∣₁ (Iso.inv Bool≃Charac b) ≡ b
--     t false = refl
--     t true = refl

--   isEq-c : (X : Type) (e : ∥ X ≃ Bool ∥₁) → isEquiv (c X e)
--   isEq-c X = PT.rec (isPropIsEquiv _)
--     (EquivJ (λ X e → isEquiv (c X ∣ e ∣₁))
--       (subst isEquiv (sym c*) (isoToIsEquiv Bool≃Charac)))

-- rCancel∞ : (X : RP∞) → X +∞ X ≡ Bool*
-- rCancel∞ X = Σ≡Prop (λ _ → squash₁)
--   (sym (ua (h X , isEq-h X)))
--   where
--   h : (X : RP∞) → Bool → fst X ≃ fst X
--   h x false = notEquiv* x .fst
--   h x true = idEquiv (fst x)

--   h⋆ : (t : Bool) → Iso.fun Bool≃Charac (h Bool* t) ≡ t
--   h⋆ false = refl
--   h⋆ true = refl

--   isEq-h : (X : RP∞) → isEquiv (h X)
--   isEq-h = uncurry λ X → PT.elim (λ _ → isPropIsEquiv _)
--     (EquivJ (λ X x → isEquiv (h (X , ∣ x ∣₁)))
--       (subst isEquiv
--         (funExt (λ x → sym (cong (Iso.inv Bool≃Charac) (h⋆ x))
--                       ∙ Iso.leftInv Bool≃Charac (h Bool* x) ) )
--         (isoToIsEquiv (invIso Bool≃Charac))))

-- lId∞ : (X : RP∞) → (Bool* +∞ X) ≡ X
-- lId∞ X = +∞-comm Bool* X ∙ +∞rId X

-- lId≡rId : lId∞ Bool* ≡ +∞rId Bool*
-- lId≡rId = cong (_∙ +∞rId Bool*) +∞-comm0 ∙ sym (lUnit _)

-- bst : Ω (RP∞ , Bool*) .fst ≃ Bool
-- bst = compEquiv (isoToEquiv (invIso (fstP-RP∞ Bool* Bool*)))
--                 (compEquiv univalence
--                 (isoToEquiv Bool≃Charac))

-- liftBool : ∀ {ℓ} → Iso Bool (Lift {j = ℓ} Bool)
-- Iso.fun liftBool = lift
-- Iso.inv liftBool = lower
-- Iso.rightInv liftBool x = refl
-- Iso.leftInv liftBool x = refl

-- bst' : Ω (RP∞ , Bool*) ≡ (Lift Bool , lift true)
-- bst' = ua∙ (compEquiv bst (isoToEquiv liftBool)) refl

-- isAssocHSp : ∀ {ℓ} → (A : Pointed ℓ) (_+A_ : fst A → fst A → fst A) → Type ℓ
-- isAssocHSp A _+A_ = (Σ[ rid ∈ ((x : _) → x +A pt A ≡ x) ]
--                     Σ[ lid ∈ ((x : _) → (pt A) +A x ≡ x) ]
--                     (lid (pt A) ≡ rid (pt A)))
--                   × ((x y z : fst A) → (x +A (y +A z)) ≡ ((x +A y) +A z))

-- open import Cubical.HITs.EilenbergMacLane1 as EM1
-- open import Cubical.Algebra.Group.Instances.IntMod
-- open import Cubical.Functions.Embedding
-- open import Cubical.Data.Fin.Base
-- open import Cubical.Data.Fin.Arithmetic

-- isAssocHSpEM1 : isAssocHSp (EM∙ ℤ/2 1) _+ₖ_
-- fst isAssocHSpEM1 = rUnitₖ 1 , lUnitₖ 1 , refl
-- snd isAssocHSpEM1 = assocₖ 1

-- Bool→ℤ/2 : Bool → ℤ/2 .fst
-- Bool→ℤ/2 true = fzero
-- Bool→ℤ/2 false = fone


-- map-one : RP∞ → EM ℤ/2 1
-- map-one = uncurry λ X → PT.elim→Gpd _ (λ _ → hLevelEM ℤ/2 1)
--   (λ _ → embase)
--   (hel X)
--   (helcoh X)
--   where
--   hel : (X : Type) (x y : X ≃ Bool) → embase ≡ embase
--   hel X x y = emloop (Bool→ℤ/2 (Iso.fun Bool≃Charac (compEquiv (invEquiv x) y)))

--   helcoh : (X : Type) (x y z : X ≃ Bool) → Square (hel X x y) (hel X x z) refl (hel X y z)
--   helcoh X =
--     EquivJ (λ X x → (y z : X ≃ Bool)
--       → Square (hel X x y) (hel X x z) refl (hel X y z))
--       λ t z → (l t)
--             ◁ (flipSquare (flipSquare (mylem (Iso.fun Bool≃Charac t) (Iso.fun Bool≃Charac z))
--             ▷ λ i → hel Bool (Iso.leftInv Bool≃Charac t i) (Iso.leftInv Bool≃Charac z i))
--             ▷ sym (l z))
--       where
--       ps : (x : Bool)
--         → Iso.fun Bool≃Charac (compEquiv (invEquiv (idEquiv Bool))
--                                (Iso.inv Bool≃Charac x))
--         ≡ x
--       ps false = refl
--       ps true = refl

--       l : (t : Bool ≃ Bool) → hel Bool (idEquiv _) t
--         ≡ emloop (Bool→ℤ/2 (Iso.fun Bool≃Charac t))
--       l t = cong emloop (cong (Bool→ℤ/2) (cong (Iso.fun Bool≃Charac)
--                   (Σ≡Prop (λ _ → isPropIsEquiv _)
--                     refl)))

--       mylem : (t z : Bool)
--         → PathP (λ i → Path (EM ℤ/2 1) embase
--                  (emloop (Bool→ℤ/2 (Iso.fun Bool≃Charac
--                  (compEquiv (invEquiv (Iso.inv Bool≃Charac t)) (Iso.inv Bool≃Charac z)))) i))
--                  (emloop (Bool→ℤ/2 t)) (emloop (Bool→ℤ/2 z))
--       mylem false false = emcomp {Group = AbGroup→Group ℤ/2} fone fzero
--       mylem false true = emcomp {Group = AbGroup→Group ℤ/2} fone fone
--       mylem true false = emcomp {Group = AbGroup→Group ℤ/2} fzero fone
--       mylem true true = emcomp {Group = AbGroup→Group ℤ/2} fzero fzero

-- map-one-eq : isEquiv map-one
-- equiv-proof map-one-eq =
--   EM1.elimProp _ (λ _ → isPropIsContr)
--     ((Bool* , refl)
--     , isEmbedding→hasPropFibers t _ _)
--   where
--   t : isEmbedding map-one
--   t = RP∞pt→Prop (λ _ → isPropΠ λ _ → isPropIsEquiv _)
--     (RP∞pt→Prop (λ _ → isPropIsEquiv _)
--       (transport (λ j → isEquiv (t2 (~ j)))
--         (isoToIsEquiv BIso)))
--     where
--     BIso : Iso (Lift Bool) (fst ℤ/2)
--     BIso = compIso (invIso (equivToIso LiftEquiv)) (fst Bool≅ℤGroup/2)

--     t2 : PathP (λ i → bst' i .fst → isoToPath (Iso-EM-ΩEM+1 {G = ℤ/2} 0) (~ i))
--                (cong {x = Bool*} {y = Bool*} map-one)
--                (Iso.fun BIso)
--     t2 = toPathP (funExt λ { (lift false) → Σ≡Prop (λ _ → Cubical.Data.Nat.Order.isProp≤) refl
--                            ; (lift true) → Σ≡Prop (λ _ → Cubical.Data.Nat.Order.isProp≤) refl})

-- ∞wedgeconn : ∀ {ℓ} {A : RP∞ → RP∞ → Type ℓ}
--   → ((x y : _) → isSet (A x y))
--   → (f : (x : _) → A x Bool*)
--   → (g : (x : _) → A Bool* x)
--   → f Bool* ≡ g Bool*
--   → (x y : _) → A x y
-- ∞wedgeconn {A = A} is-set f g p =
--   uncurry λ X → PT.elim→Set (λ _ → isSetΠ λ x → is-set _ _)
--     (f1 X)
--     (EquivJ (λ X x → (y : X ≃ Bool) →
--       PathP (λ i → (y₁ : RP∞) → A (X , squash₁ ∣ x ∣₁ ∣ y ∣₁ i) y₁)
--       (f1 X x) (f1 X y))
--       λ y → f1-idEquiv
--       ◁ λ i y' → main' y' y i)
--   where
--   p1 : Bool* ≡ Bool*
--   p1 = Σ≡Prop (λ _ → squash₁) refl
--   lem : p1 ≡ refl
--   lem = ΣSquareSet (λ _ → isProp→isSet squash₁) λ _ i → Bool


--   f1 : (X : Type) → (x : X ≃ Bool) (y : RP∞) → A (X , ∣ x ∣₁) y
--   f1 X e y = subst (λ x → A x y) (Σ≡Prop (λ _ → squash₁) (sym (ua e))) (g y)

--   f1-idEquiv : f1 Bool (idEquiv Bool) ≡ g
--   f1-idEquiv = funExt λ y
--     → (λ j → subst (λ x → A x y) (Σ≡Prop (λ _ → squash₁) (sym (uaIdEquiv {A = Bool} j))) (g y)) ∙ (λ j → subst (λ x → A x y) (lem j) (g y))
--     ∙ transportRefl (g y)

--   main' : (y' : RP∞) (y : Bool ≃ Bool)
--     → PathP (λ i → A (Bool , squash₁ ∣ idEquiv Bool ∣₁ ∣ y ∣₁ i) y')
--              (g y') (f1 Bool y y')
--   main' =
--     RP∞pt→Prop (λ _ → isPropΠ λ _ → isOfHLevelPathP' 1 (is-set _ _) _ _)
--       (elimBool≃
--         (toPathP ((λ j → transport (λ i → A (Bool , l j i) Bool*) (g Bool*))
--           ∙ sym l2))
--         (sym p ◁ (((λ j → f (Bool , squash₁ ∣ idEquiv Bool ∣₁ ∣ notEquiv ∣₁ j ))
--                ▷ λ i → transp (λ j → A (l3 (~ i ∨ j)) Bool*) (~ i) (f (l3 (~ i))))
--                ▷ cong (transp (λ j → A (l3 j) Bool*) i0) p)))
--                       -- p))))
--        where
--        l : Path (Path ∥ Bool ≃ Bool ∥₁ ∣ idEquiv _ ∣₁ ∣ idEquiv _ ∣₁) (squash₁ _ _) refl
--        l = isProp→isSet squash₁ _ _ _ _

--        l3 : Bool* ≡ (Bool , ∣ notEquiv ∣₁)
--        l3 = Σ≡Prop (λ _ → squash₁) (λ i₁ → ua notEquiv (~ i₁)) 

       

--        l2 : f1 Bool (idEquiv Bool) Bool* ≡ transport refl (g Bool*)
--        l2 = (λ j → transport (λ i → A (pp2 j i) Bool*) (g Bool*))
--         where
--         pp2 : Path (Bool* ≡ Bool*) (Σ≡Prop (λ _ → squash₁) (λ i₁ → ua (idEquiv Bool) (~ i₁))) refl
--         pp2 = ΣSquareSet (λ _ → isProp→isSet squash₁)
--             ((λ j i → uaIdEquiv {A = Bool} j (~ i)))

-- map-one-pres+ : (x y : RP∞) → map-one (x +∞ y) ≡ map-one x +[ 1 ]ₖ map-one y
-- map-one-pres+ = ∞wedgeconn (λ _ _ → emsquash _ _) F G p
--   where
--   F : (x : _) → map-one (x +∞ Bool*) ≡ +ₖ-syntax 1 (map-one x) (map-one Bool*)
--   G : (x : RP∞) →  map-one (Bool* +∞ x) ≡ +ₖ-syntax 1 (map-one Bool*) (map-one x)
--   p : F Bool* ≡ G Bool*
--   F X = cong map-one (+∞rId X)
--         ∙ sym (rUnitₖ 1 (map-one X))
--   G X = cong map-one (lId∞ X)
--         ∙ sym (lUnitₖ 1 (map-one X))
--   p i = cong map-one (lId≡rId (~ i)) ∙ refl

-- isAssocHSpRP∞ : isAssocHSp (RP∞ , Bool*) _+∞_
-- isAssocHSpRP∞ = transport (λ i → isAssocHSp (p1 (~ i)) (p2 (~ i))) tr
--   where
--   LL : Pointed (ℓ-suc ℓ-zero)
--   LL = ((Lift (EM ℤ/2 1)) , (lift embase))

--   _L+_ : LL .fst → LL .fst → LL .fst 
--   (lift x) L+ (lift y) = lift (x +ₖ y)

--   tr : isAssocHSp LL _L+_
--   fst (fst tr) (lift x) = cong lift (rUnitₖ 1 x)
--   fst (snd (fst tr)) (lift y) = cong lift (lUnitₖ 1 y)
--   snd (snd (fst tr)) = refl
--   snd tr (lift x) (lift y) (lift z) = cong lift (assocₖ 1 x y z)

--   p1 : Path (Pointed (ℓ-suc ℓ-zero)) ((RP∞ , Bool*)) LL
--   p1 = ua∙ (compEquiv (map-one , map-one-eq) LiftEquiv) refl

--   p2 : PathP (λ i → p1 i .fst → p1 i .fst → p1 i .fst) _+∞_ _L+_
--   p2 = toPathP (funExt λ { (lift a) → funExt λ { (lift b)
--     → transportRefl _
--     ∙ cong lift (
--       (cong map-one (cong₂
--       _+∞_ (λ i → invEq (_ , map-one-eq) (transportRefl a i))
--             λ i → invEq (_ , map-one-eq) (transportRefl b i)))
--     ∙ map-one-pres+ _ _
--     ∙ cong₂ _+ₖ_ (secEq (_ , map-one-eq) a) (secEq (_ , map-one-eq) b))}})

-- +∞-assoc : (X Y Z : RP∞) → (X +∞ (Y +∞ Z)) ≡ ((X +∞ Y) +∞ Z)
-- +∞-assoc = isAssocHSpRP∞ .snd

-- +∞-iso : (X : RP∞) → Iso RP∞ RP∞
-- Iso.fun (+∞-iso X) = X +∞_
-- Iso.inv (+∞-iso X) = X +∞_
-- Iso.rightInv (+∞-iso X) t = +∞-assoc X X t ∙ cong (_+∞ t) (rCancel∞ X) ∙ lId∞ t
-- Iso.leftInv (+∞-iso X) t = +∞-assoc X X t ∙ cong (_+∞ t) (rCancel∞ X) ∙ lId∞ t

-- -- isEmbedding→hasPropFibers

-- -- isEq : {!!}
-- -- isEq = {!!}

-- -- +∞-assoc : (Y X Z : RP∞) → (X +∞ (Y +∞ Z)) ≡ ((X +∞ Y) +∞ Z)
-- -- +∞-assoc Y =
-- --   ∞wedgeconn (λ _ _ → isGroupoidRP∞ _ _)
-- --     (λ X → cong (X +∞_) (+∞rId Y) ∙ sym (+∞rId (X +∞ Y)))
-- --     (λ Z → lId∞ (Y +∞ Z) ∙ cong (_+∞ Z) (sym (lId∞ Y)))
-- --     {!!}
-- --   where
-- --   h : {!!}
-- --   h = {!!}

-- -- →P : (X Y : RP∞) → fst X → fst Y → fst (X +∞ Y)
-- -- →P X Y x y = isoToEquiv
-- --   (iso (tom X x Y y)
-- --        (tom Y y X x)
-- --        (bs Y y X x)
-- --        (bs X x Y y))
-- --   where
-- --   tom : (X : RP∞) (x : fst X) (Y : RP∞) (y : fst Y)
-- --     → fst X → fst Y
-- --   tom X x Y y = CasesRP X x y (not* Y y)

-- --   bs : (X : RP∞) (x : fst X) (Y : RP∞) (y : fst Y)
-- --     → (t : fst X)
-- --     → tom Y y X x (tom X x Y y t) ≡ t
-- --   bs = J2-elem _ .fst (J2-elem _ .fst
-- --     λ { false → refl
-- --       ; true → refl})

-- -- -- (X : RP∞) → ⋀_x K n x → K_(S x)

-- -- -- _⌣_ : ⋀_x K_(S_(n x)) -> ⋀_x K_(S_(n x)) -> K_(S_n)
-- -- -- _⌣_ : ⋀_(x+y) K_(S_(n x)) -> ⋀_x K_(S_(n x)) -> K_(S_n)

-- -- -- S(X,a) , a : ⋀_x (S_(n x)) + ⋀_y (S_(n y)) 
-- -- -- S(Y,b) , b : ⋀_y (S_(n y))


-- -- -- S(X+Y, a + b)

-- -- ts : (X Y : RP∞)
-- --   → fst X ≃ fst Y
-- --   → (n : fst X → fst Y → ℕ)
-- --   → ℕ
-- -- ts X Y eq n = ∑RP X λ e → n e (fst eq e)

-- -- sss : (X Y : RP∞) (n : fst X → fst Y → ℕ)
-- --   → (fst X ≃ fst Y  → ℕ)
-- -- sss X Y n e = ts X Y e n

-- -- nt : Bool → Bool → ℕ
-- -- nt false false = 10
-- -- nt false true = 1
-- -- nt true false = 5
-- -- nt true true = 17


-- -- SM∙→∙ : {ℓ : Level} (X : RP∞) (A A' : fst X → Pointed ℓ)
-- --   → ((x : _) → A x →∙ A' x)
-- --   → SM X A → SM X A'
-- -- SM∙→∙ X A A' f (inl x) = inl x
-- -- SM∙→∙ X A A' f (inr g) = inr λ x → f x .fst (g x)
-- -- SM∙→∙ X A A' f (push a i) =
-- --     (push (fst a , f (fst a) .fst (snd a))
-- --   ∙ λ i → inr (λ x → help x i)) i
-- --   where
-- --   help : (x : fst X)
-- --     → (CasesRP X {A = λ x → A' x .fst} (fst a) (f (fst a) .fst (snd a))
-- --                 (snd (A' (not* X (fst a))))) x
-- --        ≡ f x .fst (CasesRP X {A = λ x → A x .fst}
-- --            (fst a) (a .snd) (A (not* X (fst a)) .snd) x)
-- --   help = CasesRP X (fst a)
-- --     (CasesRPβ X {A = λ x → A' x .fst} (fst a) (f (fst a) .fst (snd a))
-- --                 (snd (A' (not* X (fst a)))) .fst
-- --     ∙ cong (f (fst a) .fst)
-- --       (sym (CasesRPβ X {A = λ x → A x .fst}
-- --              (fst a) (a .snd) (A (not* X (fst a)) .snd) .fst)))
-- --        (CasesRPβ X {A = λ x → A' x .fst} (fst a) (f (fst a) .fst (snd a))
-- --                 (snd (A' (not* X (fst a)))) .snd
-- --     ∙ sym (f _ .snd)
-- --     ∙ cong (f (not* X (fst a)) .fst)
-- --         (sym (CasesRPβ X {A = λ x → A x .fst}
-- --            (fst a) (a .snd) (A (not* X (fst a)) .snd) .snd)))

