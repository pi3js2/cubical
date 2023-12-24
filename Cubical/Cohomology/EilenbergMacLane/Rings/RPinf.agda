{-# OPTIONS --safe --lossy-unification #-}

{-
This file contains
1. The Thom isomorphism (various related forms of it)
2. The Gysin sequence
-}

module Cubical.Cohomology.EilenbergMacLane.Rings.RPinf where

open import Cubical.Cohomology.EilenbergMacLane.Base
open import Cubical.Cohomology.EilenbergMacLane.Groups.Sn
open import Cubical.Cohomology.EilenbergMacLane.CupProduct
open import Cubical.Cohomology.EilenbergMacLane.Gysin

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
open import Cubical.Homotopy.EilenbergMacLane.Order2

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
open import Cubical.HITs.RPn
open import Cubical.HITs.RPn.Unordered
open import Cubical.HITs.RPn.JoinFubini




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
open import Cubical.Algebra.CommRing.Instances.IntMod
open import Cubical.Algebra.Group.Instances.IntMod

open import Cubical.Data.Fin.Arithmetic
open import Cubical.Data.Fin.Base


open RingStr renaming (_+_ to _+r_)
open PlusBis

→∙HomogeneousPathP : ∀ {ℓ ℓ'} {A∙ A∙' : Pointed ℓ} {B∙ B∙' : Pointed ℓ'}
  {f∙ : A∙ →∙ B∙} {g∙ : A∙' →∙ B∙'} (p : A∙ ≡ A∙') (q : B∙ ≡ B∙')
  (h : isHomogeneous B∙')
  → PathP (λ i → fst (p i) → fst (q i)) (f∙ .fst) (g∙ .fst)
  → PathP (λ i → p i →∙ q i) f∙ g∙
→∙HomogeneousPathP p q h r = toPathP (→∙Homogeneous≡ h (fromPathP r))

+'-suc' : (n : ℕ) → 1 +' n ≡ suc n
+'-suc' zero = refl
+'-suc' (suc n) = refl

EM→-charac : ∀ {ℓ ℓ'} {A : Pointed ℓ} {G : AbGroup ℓ'} (n : ℕ)
  → Iso (fst A → EM G n) ((A →∙ EM∙ G n) × EM G n)
Iso.fun (EM→-charac {A = A} n) f =
  ((λ x → f x -ₖ f (pt A)) , rCancelₖ n (f (pt A))) , f (pt A)
Iso.inv (EM→-charac n) (f , a) x = fst f x +ₖ a
Iso.rightInv (EM→-charac {A = A} n) ((f , p) , a) =
  ΣPathP (→∙Homogeneous≡ (isHomogeneousEM _)
    (funExt (λ x → (λ i → (f x +ₖ a) -ₖ (cong (_+ₖ a) p ∙ lUnitₖ n a) i)
                  ∙ sym (assocₖ n (f x) a (-ₖ a))
                  ∙ cong (f x +ₖ_) (rCancelₖ n a)
                  ∙ rUnitₖ n (f x)))
  , cong (_+ₖ a) p ∙ lUnitₖ n a)
Iso.leftInv (EM→-charac {A = A} n) f =
  funExt λ x → sym (assocₖ n (f x) (-ₖ f (pt A)) (f (pt A)))
    ∙∙ cong (f x +ₖ_) (lCancelₖ n (f (pt A)))
    ∙∙ rUnitₖ n (f x)

EquivPresId : ∀ {ℓ} {A B : Type ℓ} (e : A ≃ B) {x y : A} → fst e x ≡ fst e y → x ≡ y
EquivPresId e p = sym (retEq e _) ∙∙ cong (invEq e) p ∙∙ retEq e _

private
  hlev : (b : EM (Ring→AbGroup ℤ/2Ring) 1)
    → isOfHLevel 2 (Susp∙ (embase ≡ b) →∙ EM∙ (CommRing→AbGroup ℤ/2CommRing) 1)
  hlev = EM→Prop _ 0 (λ _ → isPropIsOfHLevel 2)
    (subst isSet (cong ((ℤ/2Ring .fst , fzero) →∙_)
              (EM≃ΩEM+1∙ 0)
      ∙ isoToPath (ΩSuspAdjointIso {A = ℤ/2Ring .fst , fzero})
      ∙ cong (_→∙ EM∙ (CommRing→AbGroup ℤ/2CommRing) 1)
      (cong Susp∙ (isoToPath  (Iso-EM-ΩEM+1 0))))
      (subst isSet
        (cong (λ x → x →∙ x)
          (ua∙ {A = _ , true} (isoToEquiv (Bool≅ℤGroup/2 .fst)) refl))
        (isOfHLevel→∙ 2 isSetBool)))


  open import Cubical.Data.Empty as ⊥
  open import Cubical.Relation.Nullary

  myType : (b : EM (Ring→AbGroup ℤ/2Ring) 1) → Type _
  myType b =  (Σ[ F ∈ Susp∙ (embase ≡ b) →∙ EM∙ (CommRing→AbGroup ℤ/2CommRing) 1 ]
             ¬ F ≡ const∙ _ _)

  Iso1 : Iso (Susp∙ (Ω (EM∙ (CommRing→AbGroup ℤ/2CommRing) 1) .fst) →∙ EM∙ (CommRing→AbGroup ℤ/2CommRing) 1)
             ((Bool , true) →∙ (Bool , true))
  Iso1 =
    compIso (invIso (ΩSuspAdjointIso {A = Ω (EM∙ (CommRing→AbGroup ℤ/2CommRing) 1)}) )
            (compIso
              (post∘∙equiv (help , refl))
              (pre∘∙equiv (help , refl)))
    where
    help = (isoToEquiv (compIso (invIso (Iso-EM-ΩEM+1 {G = CommRing→AbGroup ℤ/2CommRing} 0))
            (invIso (Bool≅ℤGroup/2 .fst))))

  open import Cubical.Foundations.Univalence
  ΣIs : ∀ {ℓ} {B A : Type ℓ}
    → (e : A ≃ B)
    → {x : A}
    → Iso (Σ[ y ∈ A ] ¬ y ≡ x)
           (Σ[ y ∈ B ] ¬ y ≡ fst e x)
  ΣIs {B = B} = EquivJ (λ A e → {x : A}
    → Iso (Σ[ y ∈ A ] ¬ y ≡ x)
           (Σ[ y ∈ B ] ¬ y ≡ fst e x)) idIso

  iso2Inv : Bool → (Bool , true) →∙ (Bool , true)
  iso2Inv false = idfun∙ _
  iso2Inv true = const∙ _ _
  iso2 : Iso ((Bool , true) →∙ (Bool , true)) Bool
  Iso.fun iso2 f = fst f false
  Iso.inv iso2 = iso2Inv
  Iso.rightInv iso2 false = refl
  Iso.rightInv iso2 true = refl
  Iso.leftInv iso2 f = Σ≡Prop (λ _ → isSetBool _ _) (help _ refl)
    where
    help : (x : Bool) → fst f false ≡ x → iso2Inv (fst f false) .fst ≡ f .fst
    help false p = funExt λ { false → (λ j → iso2Inv (p j) .fst false) ∙ sym p
                             ; true → (λ j → iso2Inv (p j) .fst true) ∙ sym (snd f)}
    help true p = (λ j → iso2Inv (p j) .fst) ∙ funExt λ { false → sym p ; true → sym (snd f)}

  myTYIso : Iso (myType embase) (Σ[ F ∈ Bool ] ¬ F ≡ true)
  myTYIso = ΣIs (isoToEquiv (compIso Iso1 iso2))

  isProp-T : (b : EM (Ring→AbGroup ℤ/2Ring) 1) → isProp (myType b)
  isProp-T = EM→Prop _ 0 (λ _ → isPropIsProp)
           (isOfHLevelRetractFromIso 1 myTYIso
             (isContr→isProp ((false , true≢false ∘ sym)
                            , λ { (false , p) → Σ≡Prop (λ _ → isProp¬ _) refl  
                                ; (true , p) → ⊥.rec (p refl)})))

  euler-f : Susp∙ (Ω (EM∙ (CommRing→AbGroup ℤ/2CommRing) 1) .fst) →∙ EM∙ (CommRing→AbGroup ℤ/2CommRing) 1
  fst euler-f north = embase
  fst euler-f south = embase
  fst euler-f (merid a i) = a i
  snd euler-f = refl

  euler : myType embase
  fst euler = euler-f
  snd euler p = true≢false true≡false
    where
    true≡false : true ≡ false
    true≡false i = Iso.fun (compIso Iso1 iso2) (p (~ i))

  euler-full : (b : EM (Ring→AbGroup ℤ/2Ring) 1) → myType b
  euler-full = EM→Prop _ 0 isProp-T euler

  module ThomRP∞ = Thom (EM∙ (Ring→AbGroup ℤ/2Ring) 1) (0ₖ 1 ≡_) refl -- (isConnectedEM 1)
                   (isConnectedEM 1) -- ℤ/2CommRing
                   ℤ/2CommRing


  open ThomRP∞
  isContrE : isContr E
  isContrE = isContrSingl _

  module conRP∞ =
    con 0 (((compEquiv (isoToEquiv (invIso (Iso-EM-ΩEM+1 0)))
                     (isoToEquiv (invIso (fst Bool≅ℤGroup/2))))) , refl)
          (λ b → euler-full b .fst)
          (EquivPresId (isoToEquiv (compIso Iso1 iso2)) λ i → false)
  open conRP∞
  test : (n : ℕ) → ((fst (EM∙ (Ring→AbGroup ℤ/2Ring) 1) → EM (Ring→AbGroup ℤ/2Ring) n))
                   ≃ (EM∙ (Ring→AbGroup ℤ/2Ring) 1 →∙ EM∙ (Ring→AbGroup ℤ/2Ring) (n +' 1))
  test n = ϕ-raw-contr n isContrE

  open import Cubical.Algebra.AbGroup.TensorProduct
  ⌣RP∞ : (n : ℕ) → (fst (EM∙ (Ring→AbGroup ℤ/2Ring) 1) → EM (Ring→AbGroup ℤ/2Ring) n)
                  → EM∙ (Ring→AbGroup ℤ/2Ring) 1 →∙ EM∙ (Ring→AbGroup ℤ/2Ring) (n +' 1)
  fst (⌣RP∞ n f) x = (f x) ⌣ₖ x
  snd (⌣RP∞ n f) = ⌣ₖ-0ₖ _ _ (f (0ₖ 1))

  ⌣RP∞' : (n : ℕ) → (fst (EM∙ (Ring→AbGroup ℤ/2Ring) 1) → EM (Ring→AbGroup ℤ/2Ring) n)
                    → EM∙ (Ring→AbGroup ℤ/2Ring) 1 →∙ EM∙ (Ring→AbGroup ℤ/2Ring) (1 +' n)
  fst (⌣RP∞' n f) x = x ⌣ₖ (f x)
  snd (⌣RP∞' n f) = 0ₖ-⌣ₖ _ _ (f (0ₖ 1))

  ⌣RP∞≡⌣RP∞' : (n : ℕ)
    → PathP (λ i → (fst (EM∙ (Ring→AbGroup ℤ/2Ring) 1) → EM (Ring→AbGroup ℤ/2Ring) n)
                  → EM∙ (Ring→AbGroup ℤ/2Ring) 1 →∙ EM∙ (Ring→AbGroup ℤ/2Ring) (+'-comm n 1 i))
             (⌣RP∞ n)
             (⌣RP∞' n)
  ⌣RP∞≡⌣RP∞' n = funExt λ f →
    →∙HomogeneousPathP refl (cong (EM∙ (Ring→AbGroup ℤ/2Ring)) (+'-comm n 1))
      (isHomogeneousEM _)
      (funExt λ x → lem f x)
    where
    lem : (f : EM (Ring→AbGroup ℤ/2Ring) 1 → EM (Ring→AbGroup ℤ/2Ring) n)
          (x : EM (Ring→AbGroup ℤ/2Ring) 1)
      → PathP (λ i → EM (Ring→AbGroup ℤ/2Ring) (+'-comm n 1 i))
               (f x ⌣ₖ x) (x ⌣ₖ f x)
    lem f x = toPathP (sym (⌣ₖ-commℤ/2 1 n x (f x)))

  ⌣RP∞IsEq : (n : ℕ) → isEquiv (⌣RP∞ n)
  ⌣RP∞IsEq n =
    subst isEquiv
      (funExt (λ f → →∙Homogeneous≡ (isHomogeneousEM _)
        (λ i x → f x ⌣ₖ (euler-full-lem x i))))
        (test n .snd)
    where
    help : (g : _) → (λ i → euler-full (emloop g i) .fst .fst south) ≡ emloop g
    help g j i = hcomp (λ k → λ {(i = i0) → embase
                                ; (i = i1) → emloop g k
                                ; (j = i0) → euler-full (emloop g i) .fst .fst (merid (λ w → emloop g (i ∧ w)) k)
                                ; (j = i1) → emloop g (i ∧ k)})
                       (euler-full (emloop g i) .fst .snd j)

    euler-full-lem : (x : _) → euler-full x .fst .fst south ≡ x
    euler-full-lem = EM-raw'-elim _ 1 (λ _ → hLevelEM _ 1 _ _)
      λ { embase-raw → refl ; (emloop-raw g i) j → help g j i }

  abstract
    ⌣RP∞'IsEq : (n : ℕ) → isEquiv (⌣RP∞' n)
    ⌣RP∞'IsEq n = transport (λ i → isEquiv (⌣RP∞≡⌣RP∞' n i)) (⌣RP∞IsEq n)

  ⌣RP∞Equiv : (n : ℕ) → (fst (EM∙ (Ring→AbGroup ℤ/2Ring) 1) → EM (Ring→AbGroup ℤ/2Ring) n)
                        ≃ (EM∙ (Ring→AbGroup ℤ/2Ring) 1 →∙ EM∙ (Ring→AbGroup ℤ/2Ring) (n +' 1))
  fst (⌣RP∞Equiv n) = ⌣RP∞ n
  snd (⌣RP∞Equiv n) = ⌣RP∞IsEq n

  ⌣RP∞'Equiv : (n : ℕ) → ((EM (Ring→AbGroup ℤ/2Ring) 1) → EM (Ring→AbGroup ℤ/2Ring) n)
                         ≃ (EM∙ (Ring→AbGroup ℤ/2Ring) 1 →∙ EM∙ (Ring→AbGroup ℤ/2Ring) (1 +' n))
  fst (⌣RP∞'Equiv n) = ⌣RP∞' n
  snd (⌣RP∞'Equiv n) = ⌣RP∞'IsEq n

  ⌣RP∞''Equiv : (n : ℕ) → ((EM (Ring→AbGroup ℤ/2Ring) 1) → EM (Ring→AbGroup ℤ/2Ring) n)
                         ≃ (EM∙ (Ring→AbGroup ℤ/2Ring) 1 →∙ EM∙ (Ring→AbGroup ℤ/2Ring) (suc n))
  ⌣RP∞''Equiv n =
    compEquiv (⌣RP∞'Equiv n)
      (isoToEquiv (pre∘∙equiv
        ((pathToEquiv (cong (EM (Ring→AbGroup ℤ/2Ring)) (+'-suc' n)))
        , (subst-EM-0ₖ (+'-suc' n)))))

 -- pre∘∙equiv

  RP→Charac₀ : Iso (EM (Ring→AbGroup ℤ/2Ring) 1 → ℤ/2Ring .fst)
                    (ℤ/2Ring .fst)
  Iso.fun RP→Charac₀ f = f embase
  Iso.inv RP→Charac₀ a = λ _ → a
  Iso.rightInv RP→Charac₀ a = refl
  Iso.leftInv RP→Charac₀ f = funExt (EM→Prop _ 0 (λ _ → is-set (snd ℤ/2Ring) _ _) refl)

  _ˣ_ : ∀ {ℓ} (A : ℕ → Type ℓ) (n : ℕ) → Type ℓ
  A ˣ zero = A zero
  A ˣ suc n = (A ˣ n) × A (suc n)

  triv : (n : ℕ) (x : EM _ n) → ⌣RP∞Equiv n .fst (λ _ → x) ≡ ((λ y → x ⌣ₖ y) , ⌣ₖ-0ₖ _ 1 _)
  triv n x = →∙Homogeneous≡ (isHomogeneousEM _) refl

  RP→CharacIso : (n : ℕ)
    → Iso (fst (EM∙ (Ring→AbGroup ℤ/2Ring) 1) → EM (Ring→AbGroup ℤ/2Ring) n)
           ((EM (Ring→AbGroup ℤ/2Ring)) ˣ n)
  RP→CharacIso zero = RP→Charac₀
  RP→CharacIso (suc n) =
    compIso (EM→-charac (suc n))
      (Σ-cong-iso-fst
        (compIso help (RP→CharacIso n)))
    where
    help : Iso (EM∙ (Ring→AbGroup ℤ/2Ring) 1
               →∙ EM∙ (Ring→AbGroup ℤ/2Ring) (suc n))
               (EM (Ring→AbGroup ℤ/2Ring) 1
               → EM (Ring→AbGroup ℤ/2Ring) n)
    help = equivToIso (invEquiv (⌣RP∞''Equiv n))


makeSquare : (n : ℕ)
    →  (EM (Ring→AbGroup ℤ/2Ring) 1
    → EM (Ring→AbGroup ℤ/2Ring) n
    → EM (Ring→AbGroup ℤ/2Ring) (n +' n))
    → (EM (Ring→AbGroup ℤ/2Ring) n → (EM (Ring→AbGroup ℤ/2Ring)) ˣ (n +' n))
makeSquare n f y = Iso.fun (RP→CharacIso _) λ x → f x y

UnordSmash∙ : ∀ {ℓ} (X : RP∞' ℓ) (A : fst X → Pointed ℓ) → Pointed ℓ
UnordSmash∙ X A = UnordSmash X A , inr (snd ∘ A)

module _ {ℓ} (X Y : RP∞' ℓ) (A : fst X → fst Y → Pointed ℓ) where
  UnordSmash∙² : Pointed ℓ
  UnordSmash∙² = UnordSmash∙ X (λ x → UnordSmash∙ Y (A x))

  UnordSmash∙²-fun : ((x : fst X) (y : fst Y) → A x y .fst)
    → UnordSmash∙² .fst
  UnordSmash∙²-fun f = inr (λ x → inr (f x))

open import Cubical.HITs.Join
×⁴ : ∀ {ℓ} (A : Bool → Bool → Pointed ℓ) → Type ℓ
×⁴ A = A true true .fst × A true false .fst
     × A false true .fst × A false false .fst

JoinStructureBoolDom : {!(A : Bool → Bool → Pointed ℓ) → ?!}
JoinStructureBoolDom = {!!}

module _ {ℓ} {A : Type ℓ} {B C : A → Type ℓ} (contr : isContr (Σ A B)) where
  private
    push-c : (a : A) (p : contr .fst .fst ≡ a)
          → (c : C a)
          → Path (cofib {A = C (contr .fst .fst)} {B = Σ A C} λ x → _ , x) (inl tt) (inr (a , c))
    push-c = J> push

    cofib→join : (ptA : A) (ptB : B ptA) → (cofib {A = C ptA} {B = Σ A C} λ x → _ , x) → Σ[ a ∈ A ] join (B a) (C a)
    cofib→join ptA ptB (inl x) = ptA , (inl ptB) -- contr .fst .fst , inl (contr .fst .snd)
    cofib→join ptA ptB (inr (a , c)) = a , inr c
    cofib→join ptA ptB (push a i) = ptA , push ptB a i

    push-c-coh : (a : A) (p : contr .fst .fst ≡ a) (d : B a) (pp : PathP (λ i → B (p i)) (contr .fst .snd) d) (c : C a)
              → PathP (λ i → cofib→join (contr .fst .fst) (contr .fst .snd) (push-c a p c i) ≡ (a , push d c i))
                       (ΣPathP (p , (λ j → inl (pp j))))
                       refl -- refl
    push-c-coh =
      J> (J> λ c → flipSquare ((λ j i → cofib→join (contr .fst .fst) (contr .fst .snd) (help c j i))
        ◁ λ i j → (contr .fst .fst) , (push (contr .fst .snd) c j)))
      where
      help : (c : _) → push-c (contr .fst .fst) refl c ≡ push c
      help = funExt⁻ (transportRefl push)

  joinC : Iso (Σ[ a ∈ A ] join (B a) (C a))
              (cofib {A = C (contr .fst .fst)} {B = Σ A C} λ x → _ , x)
  Iso.fun joinC (a , inl x) = inl tt
  Iso.fun joinC (a , inr x) = inr (a , x)
  Iso.fun joinC (a , push b c i) = push-c a (cong fst (contr .snd (a , b))) c i
  Iso.inv joinC = cofib→join (contr .fst .fst) (contr .fst .snd)
  Iso.rightInv joinC (inl x) = refl
  Iso.rightInv joinC (inr x) = refl
  Iso.rightInv joinC (push a i) j =
    ((λ j → push-c (contr .fst .fst)
             (cong fst (isProp→isSet (isContr→isProp contr) _ _ (contr .snd (contr .fst)) refl j)) a)
     ∙ lem a) j i
    where
    lem : (a : _) → Path (Path (cofib (λ x → contr .fst .fst , x)) _ _) (push-c (contr .fst .fst) refl a) (push a)
    lem = funExt⁻ (transportRefl push)
  Iso.leftInv joinC (a , inl x) = ΣPathP ((cong fst (contr .snd (a , x))) , (λ j → inl (contr .snd (a , x) j .snd)))
  Iso.leftInv joinC (a , inr x) = refl
  Iso.leftInv joinC (a , push c d i) j =
    push-c-coh a (cong fst (contr .snd (a , c))) c (cong snd (contr .snd (a , c))) d i j

ΠContr : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
  → (c : isContr A) → Iso ((x : A) → B x) (B (c .fst))
Iso.fun (ΠContr c) f = f (fst c)
Iso.inv (ΠContr {B = B} c) pt x = subst B (snd c x) pt
Iso.rightInv (ΠContr {B = B} c) pt =
    (λ j → subst B (isProp→isSet (isContr→isProp c) _ _ (snd c (fst c)) refl j) pt)
  ∙ transportRefl pt
Iso.leftInv (ΠContr {B = B} c) f =
  funExt λ x → subst (λ x → subst B (snd c x) (f (fst c)) ≡ f x) (snd c x)
    ((λ j → subst B (isProp→isSet (isContr→isProp c) _ _ (snd c (fst c)) refl j) (f (fst c)))
    ∙ transportRefl _)

ΣΠContr : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {C : (a : A) → B a → Type ℓ'}
  → (c : isContr A)
  → Iso (Σ[ f ∈ ((a : A) → B a) ] (C (fst c) (f (fst c))))
         (Σ[ f ∈ B (fst c) ] C (fst c) f)
ΣΠContr {B = B} {C} c = Σ-cong-iso (ΠContr c) λ f → idIso

-- JoinStructureBool : (A : Bool → Bool → Pointed ℓ-zero) (B : Pointed ℓ-zero)
--   (f : A true true .fst × A true false .fst
--      × A false true .fst × A false false .fst
--     → fst B)
--   → Type
-- JoinStructureBool A B f =
--   (g : A true true .fst × A true false .fst
--      × A false true .fst × A false false .fst)
--   → join (join (fst g ≡ A true true .snd)
--                 (snd g .fst ≡ A true false .snd))
--           (join (snd (snd g) .fst ≡ A false true .snd)
--                 (snd (snd g) .snd ≡ A false false .snd))
--   → f g ≡ B .snd

-- module DEP (A B :  Pointed ℓ-zero) (T : fst A → fst B → Pointed ℓ-zero)
--          (f : (a : fst A) (b : fst B) → fst (T a b)) where
--   JS₁ : Type
--   JS₁ = (a : A .fst) (b : B .fst)
--       → join (a ≡ A .snd) (b ≡ B .snd)
--       → f a b ≡ T a b .snd

--   JS'l : singl (pt A) → Type
--   JS'l (a , p) = (b : fst B) → f a b ≡ T a b .snd

--   JS'r : singl (pt B) → Type
--   JS'r (b , p) = (a : fst A) → f a b ≡ T a b .snd

--   JS₁' : Type
--   JS₁' = Σ[ l ∈ ((a : _) → JS'l a) ]
--          Σ[ r ∈ ((a : _) → JS'r a) ]
--          ((a : _) (b : _) → l a (fst b) ≡ r b (fst a))


--   JS₁'' : Type
--   JS₁'' = Σ[ l ∈ JS'l (pt A , refl) ]
--           Σ[ r ∈ JS'r (pt B , refl) ]
--           l (pt B) ≡ r (pt A)

--   IS1 : Iso JS₁ JS₁'
--   fst (Iso.fun IS1 F) (a , p) b = F a b (inl (sym p))
--   fst (snd (Iso.fun IS1 F)) (b , p) a = F a b (inr (sym p))
--   snd (snd (Iso.fun IS1 F)) (a , p) (b , q) = cong (F a b) (push (sym p) (sym q))
--   Iso.inv IS1 (l , r , lr) a b (inl x) = l (a , sym x) b
--   Iso.inv IS1 (l , r , lr) a b (inr x) = r (b , sym x) a
--   Iso.inv IS1 (l , r , lr) a b (push p q i) = lr (a , sym p) (b , sym q) i
--   Iso.rightInv IS1 _ = refl
--   Iso.leftInv IS1 F = funExt λ a → funExt λ b → funExt
--     λ { (inl x) → refl ; (inr x) → refl ; (push a b i) → refl}

--   IS2 : Iso JS₁' JS₁''
--   IS2 = compIso
--     (Σ-cong-iso
--       {B = λ l → Σ[ r ∈ ((a : _) → JS'r a) ]
--                    ((a : _) (b : _) → l a (fst b) ≡ r b (fst a))}
--       {B' = λ l → Σ[ r ∈ ((a : _) → JS'r a) ]
--                    ((b : _) → l (fst b) ≡ r b (pt A))}
--       (ΠContr (isContrSingl (pt A)))
--         λ x → Σ-cong-iso-snd λ r → ΠContr (isContrSingl (pt A)))
--       (Σ-cong-iso-snd
--         λ l → Σ-cong-iso {B = λ r → ((b : _) → l (fst b) ≡ r b (pt A))}
--                           {B' = λ r → (l (pt B) ≡ r (pt A))}
--       (ΠContr (isContrSingl (pt B)))
--       λ _ → ΠContr (isContrSingl (pt B)))

--   FullIso : Iso JS₁ JS₁''
--   FullIso = compIso IS1 IS2

RP∞'→SetRec : ∀ {ℓ} {A : Type ℓ} (s : isSet A) (X : RP∞' ℓ)
         → (f : fst X → A)
         → ((x : _) → f x ≡ f (RP∞'-fields.notRP∞' X x))
         → A
RP∞'→SetRec s = uncurry λ X
  → uncurry λ 2tx
  → elim→Set (λ _ → isSetΠ2 λ _ _ → s)
               (λ x f coh → f x)
               λ x → RP∞'-fields.elimRP∞' (X , 2tx , ∣ x ∣₁) x
                 (λ i f coh → f x)
                 λ i f coh → coh x i

notNotRP∞' : ∀ {ℓ} (X : RP∞' ℓ) (x : fst X)
  → RP∞'-fields.notRP∞' X (RP∞'-fields.notRP∞' X x) ≡ x
notNotRP∞' = JRP∞' refl

∑RP∞' : (X : RP∞' ℓ-zero) (n : fst X → ℕ) → ℕ
∑RP∞' X n =
  RP∞'→SetRec isSetℕ X
   (λ x → n x + n (RP∞'-fields.notRP∞' X x))
   λ x → +-comm (n x) _ ∙ cong (n (RP∞'-fields.notRP∞' X x) +_)
                           (cong n (sym (notNotRP∞' X x)))

∑RP∞'≡ : (X : RP∞' ℓ-zero) (x : fst X) (n : fst X → ℕ)
  → ∑RP∞' X n ≡ n x +' n (RP∞'-fields.notRP∞' X x)
∑RP∞'≡ = JRP∞' (λ n → sym (+'≡+ _ _))

module _ {ℓ} (X : RP∞' ℓ) (A : fst X → Pointed ℓ) (B : Pointed ℓ) where
  BipointedUnordJoin : (f : ((x : fst X) → A x .fst) → fst B) → Type ℓ
  BipointedUnordJoin f =
      (g : (x : fst X) → A x .fst)
    → UnordJoinR X (λ x → g x ≡ A x .snd)
    → f g ≡ B .snd

module _ {ℓ} (A B T :  Pointed ℓ)
         (f : fst A → fst B → fst T) where
  BipointedJoinBool : Type ℓ
  BipointedJoinBool = (a : A .fst) (b : B .fst)
      → join (a ≡ A .snd) (b ≡ B .snd)
      → f a b ≡ T .snd

  JS'l : singl (pt A) → Type ℓ
  JS'l (a , p) = (b : fst B) → f a b ≡ T .snd

  JS'r : singl (pt B) → Type ℓ
  JS'r (b , p) = (a : fst A) → f a b ≡ T .snd

  BipointedJoinBool' : Type ℓ
  BipointedJoinBool' = Σ[ l ∈ ((a : _) → JS'l a) ]
         Σ[ r ∈ ((a : _) → JS'r a) ]
         ((a : _) (b : _) → l a (fst b) ≡ r b (fst a))


  BipointedJoinBool'' : Type ℓ
  BipointedJoinBool'' = Σ[ l ∈ JS'l (pt A , refl) ]
          Σ[ r ∈ JS'r (pt B , refl) ]
          l (pt B) ≡ r (pt A)

  IS1 : Iso BipointedJoinBool BipointedJoinBool'
  fst (Iso.fun IS1 F) (a , p) b = F a b (inl (sym p))
  fst (snd (Iso.fun IS1 F)) (b , p) a = F a b (inr (sym p))
  snd (snd (Iso.fun IS1 F)) (a , p) (b , q) = cong (F a b) (push (sym p) (sym q))
  Iso.inv IS1 (l , r , lr) a b (inl x) = l (a , sym x) b
  Iso.inv IS1 (l , r , lr) a b (inr x) = r (b , sym x) a
  Iso.inv IS1 (l , r , lr) a b (push p q i) = lr (a , sym p) (b , sym q) i
  Iso.rightInv IS1 _ = refl
  Iso.leftInv IS1 F = funExt λ a → funExt λ b → funExt
    λ { (inl x) → refl ; (inr x) → refl ; (push a b i) → refl}

  IS2 : Iso BipointedJoinBool' BipointedJoinBool''
  IS2 = compIso
    (Σ-cong-iso
      {B = λ l → Σ[ r ∈ ((a : _) → JS'r a) ]
                   ((a : _) (b : _) → l a (fst b) ≡ r b (fst a))}
      {B' = λ l → Σ[ r ∈ ((a : _) → JS'r a) ]
                   ((b : _) → l (fst b) ≡ r b (pt A))}
      (ΠContr (isContrSingl (pt A)))
        λ x → Σ-cong-iso-snd λ r → ΠContr (isContrSingl (pt A)))
      (Σ-cong-iso-snd
        λ l → Σ-cong-iso {B = λ r → ((b : _) → l (fst b) ≡ r b (pt A))}
                          {B' = λ r → (l (pt B) ≡ r (pt A))}
      (ΠContr (isContrSingl (pt B)))
      λ _ → ΠContr (isContrSingl (pt B)))

  FullIso : Iso BipointedJoinBool BipointedJoinBool''
  FullIso = compIso IS1 IS2

module _ (A B C D T :  Pointed ℓ-zero)
         (f : fst A → fst B → fst C → fst D → fst T) where
  JS4 : Type
  JS4 = (a : fst A) (b : fst B) (c : fst C) (d : fst D)
      → join (join (a ≡ snd A) (b ≡ snd B)) (join (c ≡ snd C) (d ≡ snd D))
      → f a b c d ≡ pt T

  -- JS4ₗ : (c : fst C) (d : fst D) → Type
  -- JS4ₗ c d = BipointedJoinBool A B T λ a b → f a b c d

  -- JS4ᵣ : (a : fst A) (b : fst B) → Type
  -- JS4ᵣ a b = BipointedJoinBool C D T (f a b)

  -- JS4' : Type
  -- JS4' = Σ[ l ∈ ((c : fst C) (d : fst D) → JS4ₗ c d) ]
  --        Σ[ r ∈ ((a : fst A) (b : fst B) → JS4ᵣ a b) ]
  --        ((a : fst A) (b : fst B) (t : join (a ≡ snd A) (b ≡ snd B))
  --         (c : fst C) (d : fst D) (t' : join (c ≡ snd C) (d ≡ snd D))
  --      → l c d a b t ≡ r a b c d t')

open import Cubical.HITs.SmashProduct

isOfHLevelEM→ : ∀ {ℓ} {G H : AbGroup ℓ} (n : ℕ)
  → isOfHLevel 3 (EM∙ G n →∙ EM∙ H (suc n))
isOfHLevelEM→ {G = G} {H = H} n =
  isConnected→∙ (suc n) 2 (isConnectedEM n)
    (subst (λ m → isOfHLevel m (EM H (suc n))) (+-comm 2 (suc n))
      (hLevelEM _ (suc n)))

-- SmashAdjIso∙ : {A B T : Pointed ℓ-zero}
--   → Iso.fun (SmashAdjIso {A = A} {B = B} {C = T}) (((A ⋀∙ B) →∙ T ∙) .snd)
--    ≡ (A →∙ (B →∙ T ∙) ∙) .snd
-- SmashAdjIso∙ {A = A} {B} {T} = {!!}

mainLem' : (A B T : Pointed ℓ-zero)
  → Iso (Σ[ f ∈ (fst A → fst B → fst T) ] BipointedJoinBool A B T f)
          (A ⋀∙ B →∙ T)
mainLem' A B T = compIso (Σ-cong-iso-snd (λ f → FullIso A B T f)) is2
  where
  F→ : (T : Type) (t : T) → Σ[ f ∈ (fst A → fst B → T) ] BipointedJoinBool'' A B (T , t) f → (A ⋀∙ B →∙ (T , t))
  fst (F→ T t (f , fl , fr , flr)) (inl x) = t
  fst (F→ T t (f , fl , fr , flr)) (inr x) = f (fst x) (snd x)
  fst (F→ T t (f , fl , fr , flr)) (push (inl x) i) = fr x (~ i)
  fst (F→ T t (f , fl , fr , flr)) (push (inr x) i) = fl x (~ i)
  fst (F→ T t (f , fl , fr , flr)) (push (push a i₁) i) = flr (~ i₁) (~ i)
  snd (F→ T t (f , fl , fr , flr)) = refl

  mmB : (T : Type) (f : A ⋀ B → T)
    → Σ[ g ∈ (fst A → fst B → T) ] BipointedJoinBool'' A B (T , f (inl tt)) g
  fst (mmB T f) a b = f (inr (a , b))
  fst (snd (mmB T f)) b = cong f (sym (push (inr b)))
  fst (snd (snd (mmB T f))) c = cong f (sym (push (inl c)))
  snd (snd (snd (mmB T f))) j i = f (push (push tt (~ j)) (~ i))

  mm : (T : Type) (f : A ⋀ B → T) (t : T)
    → (f (inl tt) ≡ t)
    → Σ[ f ∈ (fst A → fst B → T) ] BipointedJoinBool'' A B (T , t) f
  mm T f = J> (mmB T f)

  c1 : (T : Type) (f : A ⋀ B → T) (t : T) (p : f (inl tt) ≡ t)
    → F→ T t (mm T f t p) ≡ (f , p)
  c1 T f = J> cong (F→ T (f (inl tt))) (transportRefl (mmB T f))
            ∙ ΣPathP ((funExt (
            λ { (inl x) → refl
              ; (inr x) → refl
              ; (push (inl x) i) → refl
              ; (push (inr x) i) → refl
              ; (push (push a i₁) i) → refl})) , refl)

  is2 : Iso (Σ[ f ∈ (fst A → fst B → fst T) ] BipointedJoinBool'' A B T f)
            (A ⋀∙ B →∙ T)
  Iso.fun is2 f = F→ (fst T) (snd T) f
  Iso.inv is2 f = mm (fst T) (fst f) (snd T) (snd f)
  Iso.rightInv is2 f = c1 (fst T) (fst f) _ (snd f)
  Iso.leftInv is2 f = transportRefl f

mainLem : (A B T : Pointed ℓ-zero)
  → Iso (Σ[ f ∈ (fst A → fst B → fst T) ] BipointedJoinBool A B T f)
         (A →∙ (B →∙ T ∙))
mainLem A B T = compIso (mainLem' A B T) SmashAdjIso

open Iso
open import Cubical.Foundations.Equiv.HalfAdjoint

module _ {ℓ ℓ' ℓ'' ℓ'''} {A : Type ℓ} {A' : Type ℓ'}
     {B : A → Type ℓ''} {B' : A' → Type ℓ'''}
     (e : Iso A A') (f : (x : A) → Iso (B x) (B' (fun e x))) where
  e' = iso→HAEquiv e

  ΠIso : Iso ((x : A) → B x) ((x : A') → B' x)
  fun ΠIso g x = subst B' (isHAEquiv.rinv (snd e') x) (fun (f _) (g (inv e x)))
  inv ΠIso g x = inv (f _) (g (fun e x))
  rightInv ΠIso g =
    funExt λ x
    → cong (subst B' (isHAEquiv.rinv (snd e') x))
              (rightInv (f (inv e x)) _)
     ∙ (λ j → transp (λ k → B' (isHAEquiv.rinv (snd e') x (k ∨ j))) j
                 (g (isHAEquiv.rinv (snd e') x j)))
  leftInv ΠIso g =
    funExt λ x
      → cong (inv (f x))
          ((λ j → subst B' (isHAEquiv.com (snd e') x (~ j))
                    (fun (f (inv e (fun e x))) (g (inv e (fun e x)))))
          ∙ λ j → transp (λ k → B' (fst e' (isHAEquiv.linv (snd e') x (j ∨ k)))) j
                          (fun (f (isHAEquiv.linv (snd e') x j))
                            (g (isHAEquiv.linv (snd e') x j))))
      ∙ leftInv (f x) (g x)

Iso-BipointedUnordJoin-BipointedJoinBool :
  ∀ {ℓ} (A : Bool → Pointed ℓ) (B : Pointed ℓ)
  → (f : ((x : Bool) → A x .fst) → fst B)
  → Iso (BipointedUnordJoin (RP∞'∙ ℓ) A B f)
         (BipointedJoinBool (A true) (A false) B
           λ a b → f (CasesBool true a b))
Iso-BipointedUnordJoin-BipointedJoinBool A B f =
  compIso (codomainIsoDep (λ g → domIso join-UnordJoinR-iso))
    (compIso (ΠIso ΠBool×Iso λ g
      → codomainIso (pathToIso (cong (_≡ B .snd) (cong f (sym (CasesBoolη g)))))) curryIso)

SteenrodFunType : (X : RP∞' ℓ-zero) (n : fst X → ℕ) → Type
SteenrodFunType X n =
  Σ[ f ∈ (((x : fst X) → EM ℤ/2 (n x)) → EM ℤ/2 (∑RP∞' X n)) ]
    BipointedUnordJoin X (λ x → EM∙ ℤ/2 (n x)) (EM∙ ℤ/2 (∑RP∞' X n)) f

isOfHLevelEM→∙∙-full : {!!}
isOfHLevelEM→∙∙-full = {!!}

isSetSteenrodFunType : (X : RP∞' ℓ-zero) (n : fst X → ℕ) → isSet (SteenrodFunType X n)
isSetSteenrodFunType = RP∞'pt→Prop (λ _ → isPropΠ λ _ → isPropIsOfHLevel 2)
  λ n → isOfHLevelRetractFromIso 2
    (compIso (Σ-cong-iso-snd (λ f → Iso-BipointedUnordJoin-BipointedJoinBool _ _ _))
             (compIso (invIso (Σ-cong-iso (compIso (invIso curryIso) (invIso (ΠIso ΠBool×Iso λ f → idIso)))
                      λ g → idIso))
             (mainLem (EM∙ ℤ/2 (n true)) (EM∙ ℤ/2 (n false))
                      (EM∙ ℤ/2 (n true + n false)))))
          (isConnected→∙ (suc (n true)) 1
            (isConnectedEM (n true))
              (subst (λ m → isOfHLevel m (EM∙ ℤ/2 (n false) →∙ EM∙ ℤ/2 (n true + n false)))
                (cong suc (+-comm 1 (n true)) )
                (isConnected→∙ (suc (n false)) (suc (n true))
                  (isConnectedEM (n false))
                  (subst (λ m → isOfHLevel (suc m) (EM ℤ/2 (n true + n false)))
                     (+-comm (suc (n true)) (n false))
                     (hLevelEM ℤ/2 (n true + n false))))))

cp : {n m : ℕ} → EM ℤ/2 n → EM ℤ/2 m → EM ℤ/2 (n +' m)
cp = _⌣ₖ_ {G'' = ℤ/2Ring}

SQ : (X : RP∞' ℓ-zero) (n : fst X → ℕ) → SteenrodFunType X n
SQ X n = RP∞'→SetRec (isSetSteenrodFunType X n) X
  (λ x → (λ f → subst (EM ℤ/2) (sym (∑RP∞'≡ X x n)) (cp (f x) (f (RP∞'-fields.notRP∞' X x))))
        , λ g → {!!})
  {!!}



-- mainA : (A B C D T : Pointed ℓ-zero)
--   → Iso (Σ[ f ∈ (fst A → fst B → fst C → fst D → fst T) ]
--             JS4 A B C D T f)
--          (A →∙ (B →∙ C →∙ D →∙ T ∙ ∙ ∙))
-- mainA A B C D T =
--   compIso
--    (compIso IsMain
--      (pathToIso (λ i → Σ (fst A → fst B → mainIs i .fst)
--                            (BipointedJoinBool A B (mainIs i)))))
--                             (mainLem A B (C →∙ D →∙ T ∙ ∙))
--   where
--   T1 = (Σ[ f ∈ (fst A → fst B → fst C → fst D → fst T) ] JS4 A B C D T f)
--   T2 = (Σ (fst A → fst B → Σ (fst C → fst D → fst T) (BipointedJoinBool C D T))
--                  (BipointedJoinBool A B (Σ (fst C → fst D → fst T) (BipointedJoinBool C D T)
--                    , (λ _ _ → snd T) , (λ _ _ _ → refl) )))

--   module _ (a : fst A) (b : fst B) (c : fst C) (d : fst D)
--            (p : join (a ≡ snd A) (b ≡ snd B))
--            (q : join (c ≡ snd C) (d ≡ snd D)) (i j k : I) where
--     fill₁ : T1 → fst T
--     fill₁ (f , g) =
--       hfill (λ k → λ {(i = i0) → g a b c d (push p q k) j
--                      ; (i = i1) → snd T
--                      ; (j = i0) → g a b c d (inl p) i
--                      ; (j = i1) → snd T})
--             (inS (g a b c d (inl p) (i ∨ j))) k

--     fill₂ : T2 → fst T
--     fill₂ (f , g) =
--       hfill (λ k → λ {(i = i0) → g a b p j .snd c d q (~ k)
--                    ; (i = i1) → f a b .snd c d q (~ k ∨ j)
--                    ; (j = i0) → f a b .snd c d q (~ k)
--                    ; (j = i1) → snd T})
--           (inS (snd T)) k

--   T1→T2 : T1 → T2
--   fst (fst (T1→T2 (f , p)) a b) c d = f a b c d
--   snd (fst (T1→T2 (f , p)) a b) c d t = p a b c d (inr t)
--   fst (snd (T1→T2 (f , p)) a b t i) c d = p a b c d (inl t) i
--   snd (snd (T1→T2 (f , p)) a b t i) c d q j = fill₁ a b c d t q i j i1 (f , p)

--   T2→T1 : T2 → T1
--   fst (T2→T1 (f , p)) a b c d = f a b .fst c d
--   snd (T2→T1 (f , p)) a b c d (inl x) i = p a b x i .fst c d
--   snd (T2→T1 (f , p)) a b c d (inr x) = f a b .snd c d x
--   snd (T2→T1 (f , g)) a b c d (push p q i) j = fill₂ a b c d p q i j i1 (f , g)

--   IsMain : Iso T1 T2
--   Iso.fun IsMain = T1→T2
--   Iso.inv IsMain = T2→T1
--   fst (Iso.rightInv IsMain (f , p) i) = fst (T1→T2 (T2→T1 (f , p)))
--   fst (snd (Iso.rightInv IsMain (f , p) i) a b t j) = p a b t j .fst
--   snd (snd (Iso.rightInv IsMain (f , g) i) a b p j) c d q k =
--     hcomp (λ r → λ {(i = i0) → fill₁ a b c d p q j k r ((λ a b c d → f a b .fst c d) , (snd (T2→T1 (f , g))))
--                    ; (i = i1) → snd (g a b p j) c d q k
--                    ; (j = i0) → sd r i k
--                    ; (j = i1) → snd T
--                    ; (k = i0) → g a b p j .fst c d
--                    ; (k = i1) → snd T})
--            (cb k j i)
--     where
--     sq : (k i r : I) → fst T
--     sq k i r =
--       hfill (λ r → λ {(i = i0) → g a b p k .snd c d q (~ r)
--                      ; (i = i1) → f a b .snd c d q (~ r ∨ k)
--                      ; (k = i0) → f a b .snd c d q (~ r)
--                      ; (k = i1) → snd T})
--             (inS (snd T))
--             r

--     sd : Cube (λ i j → sq j i i1)
--                (λ i k → f a b .snd c d q k)
--                (λ r k → fill₂ a b c d p q r k i1
--                           (f , λ a b p → g a b p))
--                (λ r k → snd (f a b) c d q k)
--                (λ r i → f a b .fst c d) (λ _ _ → pt T)
--     sd r i k =
--       hcomp (λ w → λ {(r = i0) → sq k i w
--                      ; (r = i1) → f a b .snd c d q (~ w ∨ k)
--                      ; (i = i0) → fill₂ a b c d p q r k w (f , λ a b p → g a b p)
--                      ; (i = i1) → f a b .snd c d q (~ w ∨ k)
--                      ; (k = i0) → f a b .snd c d q (~ w)
--                      ; (k = i1) → snd T})
--                 (snd T)

--     cb : Cube (λ j i → g a b p j .fst c d) (λ _ _ → pt T)
--               (λ i j → sq i j i1) (λ _ _ → pt T)
--               (λ k j → g a b p (j ∨ k) .fst c d)
--               λ k j → snd (g a b p j) c d q k
--     cb k j i =
--       hcomp (λ r → λ {(i = i0) → g a b p (k ∨ j) .snd c d q (~ r)
--                      ; (i = i1) → snd (g a b p j) c d q (~ r ∨ k)
--                      ; (j = i1) → snd T
--                      ; (k = i0) → g a b p j .snd c d q (~ r)
--                      ; (k = i1) → snd T})
--             (snd T)
--   fst (Iso.leftInv IsMain (f , g) i) = f
--   snd (Iso.leftInv IsMain (f , g) i) a b c d (inl p) = g a b c d (inl p)
--   snd (Iso.leftInv IsMain (f , g) i) a b c d (inr p) = g a b c d (inr p)
--   snd (Iso.leftInv IsMain (f , g) i) a b c d (push p q j) k =
--     hcomp (λ r → λ {(i = i0) → fill₂ a b c d p q j k r
--                                    (fst (T1→T2 (f , g)) , snd (T1→T2 (f , g)))
--                    ; (i = i1) → ss r j k
--                    ; (j = i0) → s2 r k i
--                    ; (j = i1) → g a b c d (inr q) (~ r ∨ k)
--                    ; (k = i0) → g a b c d (inr q) (~ r)
--                    ; (k = i1) → pt T})
--            (snd T)
--     where
--     PP : (i j k : I) → fst T
--     PP i j k = doubleWhiskFiller {A = λ i → g a b c d (inr q) (~ i) ≡ pt T} refl
--           (λ i j → g a b c d (inr q) (~ i ∨ j))
--           (λ j k → g a b c d (push p q (~ j)) k)
--           k i j

--     s2 : Cube (λ _ _ → pt T) (λ k i → g a b c d (inl p) k)
--               (λ r i → g a b c d (inr q) (~ r)) (λ _ _ → pt T)
--               (λ r k → fill₁ a b c d p q k (~ r) i1 (f , g))
--               λ r k → PP r k i1
--     s2 r k i =
--       hcomp (λ j → λ {(r = i0) → pt T
--                      ; (r = i1) → g a b c d (push p q (~ j ∧ i)) k
--                      ; (k = i0) → g a b c d (push p q (j ∨ i)) (~ r)
--                      ; (k = i1) → pt T
--                      ; (i = i0) → fill₁ a b c d p q k (~ r) j (f , g)
--                      ; (i = i1) → PP r k j})
--             (g a b c d (push p q i) (k ∨ ~ r))

--     ss : Cube (λ _ _ → pt T) (λ j k → g a b c d (push p q j) k)
--                (λ i j → PP i j i1)
--                (λ r k → g a b c d (inr q) (~ r ∨ k))
--                (λ r j → g a b c d (inr q) (~ r))
--                (λ r j → pt T)
--     ss r j k =
--       hcomp (λ w → λ {(r = i0) → pt T
--                    ; (r = i1) → g a b c d (push p q (~ w ∨ j)) k
--                    ; (j = i1) → g a b c d (inr q) (~ r ∨ k)
--                    ; (k = i0) → g a b c d (inr q) (~ r)
--                    ; (k = i1) → pt T})
--            (g a b c d (inr q) (~ r ∨ k))

--   mainIs : (isoToPath (mainLem C D T) i0 , (λ c d → pt T) , λ _ _ _ → refl)
--          ≡ (C →∙ (D →∙ T ∙) ∙)
--   mainIs =
--     ua∙ ((isoToEquiv (mainLem C D T)))
--      (cong (Iso.fun SmashAdjIso)
--        (ΣPathP ((funExt (
--          λ { (inl x) → refl
--             ; (inr x) → refl
--             ; (push (inl x) i) → refl
--             ; (push (inr x) i) → refl
--             ; (push (push a i₁) i) → refl})) , refl))
--             ∙ SmashAdj≃∙ .snd)

-- -- module _ (A B C D :  Pointed ℓ-zero) (T : Pointed ℓ-zero)
-- --          (f : A .fst × B .fst × C .fst × D .fst
-- --            → fst T) where
-- --   BipointedJoinBool : Type
-- --   BipointedJoinBool = (a : A .fst) (b : B .fst) (c : C .fst) (d : D .fst)
-- --          → join (a ≡ A .snd)
-- --              (join (b ≡ B .snd)
-- --                (join (c ≡ C .snd)
-- --                      (d ≡ D .snd)))
-- --          → f (a , b , c , d) ≡ T .snd

-- --   BipointedJoinBool* : Type
-- --   BipointedJoinBool* = (b : B .fst) (c : C .fst) (d : D .fst)
-- --     → Σ[ fr ∈ ((a : A .fst) → join (b ≡ B .snd) (join (c ≡ C .snd) (d ≡ D .snd))
-- --                              → f (a , b , c , d) ≡ T .snd) ]
-- --           ((x : singl (A .snd)) → 
-- --               (Σ[ fl ∈ (f (x .fst , b , c , d) ≡ T .snd) ]
-- --                ((t : join (b ≡ B .snd) (join (c ≡ C .snd) (d ≡ D .snd)))
-- --              → fl ≡ fr (x .fst) t)))

-- --   BipointedJoinBool** : Type
-- --   BipointedJoinBool** = (b : B .fst) (c : C .fst) (d : D .fst)
-- --     → Σ[ fr ∈ ((a : A .fst) → join (b ≡ B .snd) (join (c ≡ C .snd) (d ≡ D .snd))
-- --                              → f (a , b , c , d) ≡ T .snd) ]
-- --            Σ[ fl ∈ (f (pt A , b , c , d) ≡ T .snd) ]
-- --                ((t : join (b ≡ B .snd) (join (c ≡ C .snd) (d ≡ D .snd)))
-- --              → fl ≡ fr (pt A) t)

-- --   JS₂ : Type
-- --   JS₂ = (c : C .fst) (d : D .fst)
-- --     → Σ[ fr ∈ ((a : A .fst) (b : fst B)
-- --               → join (c ≡ C .snd) (d ≡ D .snd)
-- --               → f (a , b , c , d) ≡ T .snd) ]
-- --        Σ[ fl ∈ ((b : fst B) → f (pt A , b , c , d) ≡ T .snd) ]
-- --          Σ[ flp ∈ ((b : fst B) → (t : join (c ≡ C .snd) (d ≡ D .snd))
-- --                  → fl b ≡ fr (pt A) b t) ]
-- --           ((x : singl (B .snd))
-- --        → Σ[ frl ∈ ((a : fst A) → f (a , fst x , c , d) ≡ T .snd) ]
-- --            Σ[ frp ∈ ((a : fst A) (t : join (c ≡ C .snd) (d ≡ D .snd)) → frl a ≡ fr a (fst x) t) ]
-- --              Σ[ r ∈ fl (fst x) ≡ frl (pt A) ]
-- --                ((t : join (c ≡ C .snd) (d ≡ D .snd))
-- --              → Square r (flp (fst x) t) refl (frp (pt A) t)))

-- --   JS₂* : Type
-- --   JS₂* = (c : C .fst) (d : D .fst)
-- --     → Σ[ fr ∈ ((a : A .fst) (b : fst B)
-- --               → join (c ≡ C .snd) (d ≡ D .snd)
-- --               → f (a , b , c , d) ≡ T .snd) ]
-- --        Σ[ fl ∈ ((b : fst B) → f (pt A , b , c , d) ≡ T .snd) ]
-- --          Σ[ flp ∈ ((b : fst B) → (t : join (c ≡ C .snd) (d ≡ D .snd))
-- --                  → fl b ≡ fr (pt A) b t) ]
-- --           (Σ[ frl ∈ ((a : fst A) → f (a , pt B , c , d) ≡ T .snd) ]
-- --            Σ[ frp ∈ ((a : fst A) (t : join (c ≡ C .snd) (d ≡ D .snd)) → frl a ≡ fr a (pt B) t) ]
-- --              Σ[ r ∈ fl (pt B) ≡ frl (pt A) ]
-- --                ((t : join (c ≡ C .snd) (d ≡ D .snd))
-- --              → Square r (flp (pt B) t) refl (frp (pt A) t)))

-- --   module _ (fl₁ : ((b : fst B) (c : C .fst) (d : D .fst) → f (pt A , b , c , d) ≡ T .snd))
-- --                 (fl₂ : ((a : fst A) (c : C .fst) (d : D .fst) → f (a , pt B , c , d) ≡ T .snd))
-- --                 (fl₁₂ : (c : fst C) (d : fst D) → fl₁ (pt B) c d ≡ fl₂ (pt A) c d)
-- --                 where
-- --     TL : singl (snd C) → Type
-- --     TL (c , p) =
-- --       Σ[ fr ∈ ((a : fst A) (b : fst B) (d : fst D) → f (a , b , c , d) ≡ T .snd) ]
-- --         Σ[ flp ∈ ((b : fst B) (d : fst D)  → fl₁ b c d ≡ fr (pt A) b d) ]
-- --           Σ[ frp ∈ ((a : fst A) (d : fst D) → fl₂ a c d ≡ fr a (pt B) d) ]
-- --             ((d : fst D) → Square (fl₁₂ c d) (flp (pt B) d) refl (frp (pt A) d))
-- --     TR : singl (snd D) → Type
-- --     TR (d , p) =
-- --       Σ[ fr ∈ ((a : fst A) (b : fst B) (c : fst C) → f (a , b , c , d) ≡ T .snd) ]
-- --         Σ[ flp ∈ ((b : fst B) (c : fst C)  → fl₁ b c d ≡ fr (pt A) b c) ]
-- --           Σ[ frp ∈ ((a : fst A) (c : fst C) → fl₂ a c d ≡ fr a (pt B) c) ]
-- --             ((c : fst C) → Square (fl₁₂ c d) (flp (pt B) c) refl (frp (pt A) c))

-- --     TLR : (c : singl (snd C)) (d : singl (snd D)) → TL c → TR d → Type
-- --     TLR (c , p) (d , q) (frₗ , flpₗ , frpₗ , sqₗ) (frᵣ , flpᵣ , frpᵣ , sqᵣ) =
-- --       Σ[ frₗᵣ ∈ (((a : fst A) (b : fst B) → frₗ a b d ≡ frᵣ a b c)) ]
-- --       Σ[ flpₗᵣ ∈ ((b : fst B) → PathP (λ i → fl₁ b c d ≡ frₗᵣ (pt A) b i) (flpₗ b d) (flpᵣ b c)) ]
-- --       Σ[ frpₗᵣ ∈ ((a : fst A) → PathP (λ i → fl₂ a c d ≡ frₗᵣ a (pt B) i) (frpₗ a d) (frpᵣ a c)) ]
-- --         Cube (sqₗ d) (sqᵣ c)
-- --              (λ i j → fl₁₂ c d j) (flpₗᵣ (pt B))
-- --              (λ j i → fl₁ (pt B) c d) (frpₗᵣ (pt A)) 


-- --   JS₃* : Type
-- --   JS₃* = Σ[ fl₁ ∈ ((b : fst B) (c : C .fst) (d : D .fst) → f (pt A , b , c , d) ≡ T .snd) ]
-- --            Σ[ fl₂ ∈ ((a : fst A) (c : C .fst) (d : D .fst) → f (a , pt B , c , d) ≡ T .snd) ]
-- --             Σ[ fl₁₂ ∈ ((c : fst C) (d : fst D) → fl₁ (pt B) c d ≡ fl₂ (pt A) c d) ]
-- --              Σ[ l ∈ ((c : _) → TL fl₁ fl₂ fl₁₂ c) ]
-- --               Σ[ r ∈ ((c : _) → TR fl₁ fl₂ fl₁₂ c) ]
-- --                 ((c : singl (snd C)) (d : singl (snd D)) → TLR fl₁ fl₂ fl₁₂ c d (l c) (r d))

-- --   JS₃** : Type
-- --   JS₃** = Σ[ fl₁ ∈ ((b : fst B) (c : C .fst) (d : D .fst) → f (pt A , b , c , d) ≡ T .snd) ]
-- --            Σ[ fl₂ ∈ ((a : fst A) (c : C .fst) (d : D .fst) → f (a , pt B , c , d) ≡ T .snd) ]
-- --             Σ[ fl₁₂ ∈ ((c : fst C) (d : fst D) → fl₁ (pt B) c d ≡ fl₂ (pt A) c d) ]
-- --              Σ[ l ∈ (TL fl₁ fl₂ fl₁₂ (pt C , refl)) ]
-- --               Σ[ r ∈ (TR fl₁ fl₂ fl₁₂ (pt D , refl)) ]
-- --                 (TLR fl₁ fl₂ fl₁₂ (pt C , refl) (pt D , refl) l r)

-- --   module _ (js : JS₃**) where
-- --     open import Cubical.HITs.SmashProduct
-- --     JS₃**→' : (A ⋀∙ (B ⋀∙ (C ⋀∙ D))) →∙ T
-- --     fst JS₃**→' (inl x) = pt T
-- --     fst JS₃**→' (inr (a , inl x)) = {!f (a , ?)!} -- pt T
-- --     fst JS₃**→' (inr (a , inr (b , inl x))) = {!!} -- pt T
-- --     fst JS₃**→' (inr (a , inr (b , inr (c , d)))) = f (a , b , c , d)
-- --     fst JS₃**→' (inr (a , inr (b , push (inl x) i))) = snd js .snd .snd .snd .fst .fst a b x (~ i)
-- --     fst JS₃**→' (inr (a , inr (b , push (inr x) i))) = snd js .snd .snd .fst .fst a b x (~ i)
-- --     fst JS₃**→' (inr (a , inr (b , push (push tt i₁) i))) = snd js .snd .snd .snd .snd .fst a b (~ i₁) (~ i)
-- --     fst JS₃**→' (inr (a , push (inl x) i)) = {!f (a , pt B , pt C , ?)!} -- pt T
-- --     fst JS₃**→' (inr (a , push (inr (inl x)) i)) = {!f (a , pt B , pt C , x)!} -- snd T
-- --     fst JS₃**→' (inr (a , push (inr (inr (c , d))) i)) = snd js .fst a c d (~ i)
-- --     fst JS₃**→' (inr (a , push (inr (push (inl x) i₁)) i)) = {!!}
-- --     fst JS₃**→' (inr (a , push (inr (push (inr x) i₁)) i)) = {!snd js .snd .snd .fst .snd .snd .fst a x (~ i₁) (~ i)!}
-- --     fst JS₃**→' (inr (a , push (inr (push (push a₁ i₂) i₁)) i)) = {!!}
-- --     fst JS₃**→' (inr (a , push (push a₁ i₁) i)) = {!!}
-- --     fst JS₃**→' (push a i) = {!!}
-- --     snd JS₃**→' = {!!}

-- --     JS₃**→ : A →∙ (B →∙ (C →∙ (D →∙ T ∙) ∙) ∙)
-- --     fst (fst (fst (fst JS₃**→ a) b) c) d = f (a , b , c , d)
-- --     snd (fst (fst (fst JS₃**→ a) b) c) = snd js .snd .snd .snd .fst .fst a b c
-- --     fst (snd (fst (fst JS₃**→ a) b) i) d = snd js .snd .snd .fst .fst a b d i
-- --     snd (snd (fst (fst JS₃**→ a) b) i) = {!snd js .snd .snd .snd .snd .fst a b  i!}
-- --     fst (fst (snd (fst JS₃**→ a) i) c) d = snd js .fst a c d i
-- --     snd (fst (snd (fst JS₃**→ a) i) c) j = {!!}
-- --     fst (snd (snd (fst JS₃**→ a) i) j) d = {!!}
-- --     snd (snd (snd (fst JS₃**→ a) i) j) k = {!!}
-- --     fst (fst (fst (snd JS₃**→ i) b) c) d = fst js b c d i
-- --     snd (fst (fst (snd JS₃**→ i) b) c) j = {!!}
-- --     fst (snd (fst (snd JS₃**→ i) b) j) d = {!!}
-- --     snd (snd (fst (snd JS₃**→ i) b) j) k = {!!}
-- --     fst (fst (snd (snd JS₃**→ i) j) c) d = {!!}
-- --     snd (fst (snd (snd JS₃**→ i) j) c) k = {!!}
-- --     snd (snd (snd JS₃**→ i) j) = {!!}

-- --   Iso-JS₃*-JS₃** : Iso JS₃* JS₃**
-- --   Iso-JS₃*-JS₃** =
-- --     Σ-cong-iso-snd λ f' → Σ-cong-iso-snd λ g → Σ-cong-iso-snd λ fg
-- --       → compIso (Σ-cong-iso-snd (λ r → Σ-cong-iso-snd λ s
-- --         → compIso (ΠContr (isContrSingl (snd C)))
-- --                    (ΠContr (isContrSingl (snd D)))))
-- --            (compIso (ΣΠContr {C = λ c l → Σ ((d : _) → TR f' g fg d)
-- --                      λ r → TLR f' g fg c (pt D , refl) l (r (pt D , refl))} (isContrSingl (snd C)))
-- --              (Σ-cong-iso-snd λ l →
-- --                ΣΠContr {C = λ d r → TLR f' g fg (pt C , refl) d l r} (isContrSingl (snd D))))

-- --   Iso₂ : Iso BipointedJoinBool** JS₂
-- --   fst (Iso.fun Iso₂ F c d) a b t = F b c d .fst a (inr t)
-- --   fst (snd (Iso.fun Iso₂ F c d)) b = F b c d .snd .fst
-- --   fst (snd (snd (Iso.fun Iso₂ F c d))) b t = F b c d .snd .snd (inr t)
-- --   fst (snd (snd (snd (Iso.fun Iso₂ F c d))) (b , p)) a =
-- --     F b c d .fst a (inl (sym p))
-- --   fst (snd (snd (snd (snd (Iso.fun Iso₂ F c d))) (b , p))) a t =
-- --     cong (F b c d .fst a) (push (sym p) t)
-- --   fst (snd (snd (snd (snd (snd (Iso.fun Iso₂ F c d))) (b , p)))) =
-- --     F b c d .snd .snd (inl (sym p))
-- --   snd (snd (snd (snd (snd (snd (Iso.fun Iso₂ F c d))) (b , p)))) t =
-- --     cong (F b c d .snd .snd) (push (sym p) t)
-- --   fst (Iso.inv Iso₂ F b c d) a (inl x) = F c d .snd .snd .snd (b , sym x) .fst a
-- --   fst (Iso.inv Iso₂ F b c d) a (inr t) = F c d .fst a b t
-- --   fst (Iso.inv Iso₂ F b c d) a (push x t i) =
-- --     F c d .snd .snd .snd (b , sym x) .snd .fst a t i
-- --   fst (snd (Iso.inv Iso₂ F b c d)) = F c d .snd .fst b
-- --   snd (snd (Iso.inv Iso₂ F b c d)) (inl x) =
-- --     F c d .snd .snd .snd (b , sym x) .snd .snd .fst
-- --   snd (snd (Iso.inv Iso₂ F b c d)) (inr t) = F c d .snd .snd .fst b t
-- --   snd (snd (Iso.inv Iso₂ F b c d)) (push a t i) =
-- --     F c d .snd .snd .snd (b , sym a) .snd .snd .snd t i
-- --   Iso.rightInv Iso₂ = λ _ → refl
-- --   Iso.leftInv Iso₂ F = funExt λ b → funExt λ c → funExt λ x →
-- --     ΣPathP (funExt (λ a → funExt λ { (inl x) → refl
-- --                                     ; (inr x) → refl
-- --                                     ; (push a x i) → refl})
-- --            , ΣPathP (refl , (funExt (λ { (inl x) → refl
-- --                            ; (inr x) → refl
-- --                            ; (push a x i) → refl}))))

-- --   Iso₂* : Iso BipointedJoinBool** JS₂*
-- --   Iso₂* =
-- --     compIso Iso₂
-- --       (codomainIsoDep λ c → codomainIsoDep λ d →
-- --         Σ-cong-iso-snd λ f → Σ-cong-iso-snd λ g → Σ-cong-iso-snd
-- --         λ h → ΠContr (isContrSingl (B .snd)))

-- --   Iso₃ : Iso JS₂* JS₃*
-- --   fst (Iso.fun Iso₃ F) b c d = F c d .snd .fst b
-- --   fst (snd (Iso.fun Iso₃ F)) a c d = F c d .snd .snd .snd .fst a
-- --   fst (snd (snd (Iso.fun Iso₃ F))) c d = F c d .snd .snd .snd .snd .snd .fst
-- --   fst (fst (snd (snd (snd (Iso.fun Iso₃ F)))) (c , p)) a b d =
-- --     F c d .fst a b (inl (sym p))
-- --   fst (snd (fst (snd (snd (snd (Iso.fun Iso₃ F)))) (c , p))) b d =
-- --     F c d .snd .snd .fst b (inl (sym p))
-- --   fst (snd (snd (fst (snd (snd (snd (Iso.fun Iso₃ F)))) (c , p)))) a d =
-- --     F c d .snd .snd .snd .snd .fst a (inl (sym p))
-- --   snd (snd (snd (fst (snd (snd (snd (Iso.fun Iso₃ F)))) (c , p)))) d =
-- --     F c d .snd .snd .snd .snd .snd .snd (inl (sym p))
-- --   fst (fst (snd (snd (snd (snd (Iso.fun Iso₃ F))))) (d , p)) a b c =
-- --     F c d .fst a b (inr (sym p))
-- --   fst (snd (fst (snd (snd (snd (snd (Iso.fun Iso₃ F))))) (d , p))) b c =
-- --     F c d .snd .snd .fst b (inr (sym p))
-- --   fst (snd (snd (fst (snd (snd (snd (snd (Iso.fun Iso₃ F))))) (d , p)))) a c =
-- --     F c d .snd .snd .snd .snd .fst a (inr (sym p))
-- --   snd (snd (snd (fst (snd (snd (snd (snd (Iso.fun Iso₃ F))))) (d , p)))) c =
-- --     F c d .snd .snd .snd .snd .snd .snd (inr (sym p))
-- --   fst (snd (snd (snd (snd (snd (Iso.fun Iso₃ F))))) (c , p) (d , q)) a b =
-- --     cong (F c d .fst a b) (push (sym p) (sym q))
-- --   fst (snd (snd (snd (snd (snd (snd (Iso.fun Iso₃ F))))) (c , p) (d , q))) b i =
-- --     F c d .snd .snd .fst b (push (sym p) (sym q) i)
-- --   fst (snd (snd (snd (snd (snd (snd (snd (Iso.fun Iso₃ F))))) (c , p) (d , q)))) a i =
-- --     F c d .snd .snd .snd .snd .fst a (push (sym p) (sym q) i)
-- --   snd (snd (snd (snd (snd (snd (snd (snd (Iso.fun Iso₃ F))))) (c , p) (d , q)))) i =
-- --     F c d .snd .snd .snd .snd .snd .snd (push (sym p) (sym q) i)
-- --   fst (Iso.inv Iso₃ F c d) a b (inl x) =
-- --     F .snd .snd .snd .fst (c , sym x) .fst a b d
-- --   fst (Iso.inv Iso₃ F c d) a b (inr x) =
-- --     F .snd .snd .snd .snd .fst (d , sym x) .fst a b c
-- --   fst (Iso.inv Iso₃ F c d) a b (push p q i) =
-- --     F .snd .snd .snd .snd .snd (c , sym p) (d , sym q) .fst a b i
-- --   fst (snd (Iso.inv Iso₃ F c d)) b = F .fst b c d
-- --   fst (snd (snd (Iso.inv Iso₃ F c d))) b (inl x) = F .snd .snd .snd .fst (c , sym x) .snd .fst b d 
-- --   fst (snd (snd (Iso.inv Iso₃ F c d))) b (inr x) = F .snd .snd .snd .snd .fst (d , sym x) .snd .fst b c 
-- --   fst (snd (snd (Iso.inv Iso₃ F c d))) b (push p q i) =
-- --     F .snd .snd .snd .snd .snd (c , sym p) (d , sym q) .snd .fst b i
-- --   fst (snd (snd (snd (Iso.inv Iso₃ F c d)))) a = F .snd .fst a c d
-- --   fst (snd (snd (snd (snd (Iso.inv Iso₃ F c d))))) a (inl x) =
-- --     F .snd .snd .snd .fst (c , sym x) .snd .snd .fst a d
-- --   fst (snd (snd (snd (snd (Iso.inv Iso₃ F c d))))) a (inr x) =
-- --     F .snd .snd .snd .snd .fst (d , sym x) .snd .snd .fst a c
-- --   fst (snd (snd (snd (snd (Iso.inv Iso₃ F c d))))) a (push p q i) =
-- --     F .snd .snd .snd .snd .snd (c , sym p) (d , sym q) .snd .snd .fst a i
-- --   fst (snd (snd (snd (snd (snd (Iso.inv Iso₃ F c d)))))) = F .snd .snd .fst c d
-- --   snd (snd (snd (snd (snd (snd (Iso.inv Iso₃ F c d)))))) (inl x) =
-- --     F .snd .snd .snd .fst (c , sym x) .snd .snd .snd d
-- --   snd (snd (snd (snd (snd (snd (Iso.inv Iso₃ F c d)))))) (inr x) =
-- --     F .snd .snd .snd .snd .fst (d , sym x) .snd .snd .snd c
-- --   snd (snd (snd (snd (snd (snd (Iso.inv Iso₃ F c d)))))) (push p q i) =
-- --     F .snd .snd .snd .snd .snd (c , sym p) (d , sym q) .snd .snd .snd i
-- --   Iso.rightInv Iso₃ _ = refl
-- --   Iso.leftInv Iso₃ F = funExt λ c → funExt λ d →
-- --     ΣPathP ((funExt (λ a → funExt λ b → funExt
-- --            λ { (inl x) → refl ; (inr x) → refl ; (push a b i) → refl}))
-- --     , ΣPathP (refl , (ΣPathP ((funExt (λ b
-- --       → funExt λ { (inl x) → refl ; (inr x) → refl ; (push a b i) → refl}))
-- --      , (ΣPathP (refl , (ΣPathP ((funExt (λ a →
-- --         funExt λ { (inl x) → refl ; (inr x) → refl ; (push a b i) → refl}))
-- --      , (ΣPathP (refl , (funExt (λ { (inl x) → refl ; (inr x) → refl ; (push a b i) → refl}))))))))))))


-- --            Σ[ fl ∈ (f (pt A , b , c , d) ≡ T .snd) ]
-- --                ((t : join (b ≡ B .snd) (join (c ≡ C .snd) (d ≡ D .snd)))
-- --              → fl ≡ fr (pt A) t)

-- --   Iso₁ : Iso BipointedJoinBool BipointedJoinBool*
-- --   fst (Iso.fun Iso₁ F b c d) a x = F a b c d (inr x)
-- --   fst (snd (Iso.fun Iso₁ F b c d) (a , p)) = F a b c d (inl (sym p))
-- --   snd (snd (Iso.fun Iso₁ F b c d) (a , p)) t = cong (F a b c d) (push (sym p) t)
-- --   Iso.inv Iso₁ F a b c d (inl x) = F b c d .snd (a , sym x) .fst
-- --   Iso.inv Iso₁ F a b c d (inr t) = F b c d .fst a t
-- --   Iso.inv Iso₁ F a b c d (push p t i) = F b c d .snd (a , sym p) .snd t i
-- --   Iso.rightInv Iso₁ = λ _ → refl
-- --   Iso.leftInv Iso₁ F = funExt λ a → funExt λ b → funExt λ c → funExt λ d
-- --     → funExt λ { (inl x) → refl ; (inr x) → refl ; (push a x i) → refl}

-- --   Iso₁' : Iso BipointedJoinBool BipointedJoinBool**
-- --   Iso₁' = compIso Iso₁ (codomainIsoDep λ b → codomainIsoDep λ c → codomainIsoDep λ d
-- --     → Σ-cong-iso-snd λ f → ΠContr (isContrSingl (A .snd)))

-- -- JoinStructureBool* : (A : Bool → Bool → Pointed ℓ-zero) (B : Pointed ℓ-zero)
-- --   (f : A true true .fst × A true false .fst
-- --      × A false true .fst × A false false .fst
-- --     → fst B)
-- --   → Type
-- -- JoinStructureBool* A B f =
-- --   (g : A true true .fst × A true false .fst
-- --      × A false true .fst × A false false .fst)
-- --   → join (fst g ≡ A true true .snd)
-- --       (join (snd g .fst ≡ A true false .snd)
-- --         (join (snd (snd g) .fst ≡ A false true .snd)
-- --               (snd (snd g) .snd ≡ A false false .snd)))
-- --   → f g ≡ B .snd

-- -- 4→∙ : (A : Bool → Bool → Pointed ℓ-zero) (B : Pointed ℓ-zero) → Type ℓ-zero
-- -- 4→∙ A B = A true true →∙ (A true false →∙ (A false true →∙ (A false false →∙ B ∙) ∙) ∙)

-- -- 4→∙' : (A : Bool → Bool → Pointed ℓ-zero) (B : Pointed ℓ-zero)
-- --       → Type ℓ-zero
-- -- 4→∙' A B =
-- --   Σ[ f ∈ (A true true .fst → A true false .fst
-- --        → A false true .fst → A false false .fst → fst B) ]
-- --    Σ[ f-inl-inl ∈ ((a : singl (A true true .snd)) (b : _) (c : _) (d : _) → f (fst a) b c d ≡ pt B) ]
-- --     Σ[ f-inl-inr ∈ ((b : singl (A true false .snd)) (a : _) (c : _) (d : _) → f a (fst b) c d ≡ pt B) ]
-- --      Σ[ f-inl-push ∈ (((a : singl (A true true .snd)) (b : singl (A true false .snd)) (c : _) (d : _)
-- --                      → f-inl-inl a (fst b) c d ≡ f-inl-inr b (fst a) c d)) ]
-- --     Σ[ f-inr-inl ∈ ((c : singl (A false true .snd)) (a : _) (b : _)  (d : _) → f a b (fst c) d ≡ pt B) ]
-- --      Σ[ f-inr-inr ∈ ((d : singl (A false false .snd)) (a : _) (b : _) (c : _) → f a b c (fst d) ≡ pt B) ]
-- --        Σ[ f-inl-push ∈ ((c : singl (A false true .snd)) (d : singl (A false false .snd)) (a : _) (b : _)
-- --          → f-inr-inl c a b (fst d) ≡ f-inr-inr d a b (fst c)) ]
-- --        {!Σ[ f-inl-push ∈ ((c : singl (A false true .snd)) (d : singl (A false false .snd)) (a : _) (b : _)
-- --          → f-inr-inl c a b (fst d) ≡ f-inr-inr d a b (fst c)) ]!}

-- -- pss : (A : Bool → Bool → Pointed ℓ-zero) (B : Pointed ℓ-zero) (f : _) → JoinStructureBool A B f
-- -- pss A B f (x , y , z , w) (inl (inl p)) = {!p!}
-- -- pss A B f (x , y , z , w) (inl (inr q)) = {!q!}
-- -- pss A B f (x , y , z , w) (inl (push p q i)) = {!!}
-- -- pss A B f (x , y , z , w) (inr (inl p)) = {!!}
-- -- pss A B f (x , y , z , w) (inr (inr q)) = {!!}
-- -- pss A B f (x , y , z , w) (inr (push p q i)) = {!!}
-- -- pss A B f (x , y , z , w) (push (inl p) (inl q) i) = {!!}
-- -- pss A B f (x , y , z , w) (push (inr p) (inl q) i) = {!!}
-- -- pss A B f (x , y , z , w) (push (push p q i₁) (inl r) i) = {!!}
-- -- pss A B f (x , y , z , w) (push p (inr q) i) = {!!}
-- -- pss A B f (x , y , z , w) (push p (push q r i₁) i) = {!!}


-- -- JoinStructureBoolD : (A : Bool → Bool → Pointed ℓ-zero) (B : Pointed ℓ-zero)
-- --   → Σ _ (JoinStructureBool A B)
-- --   → A true true →∙ (A true false →∙ (A false true →∙ (A false false →∙ B ∙) ∙) ∙)
-- -- fst (fst (fst (fst (JoinStructureBoolD A B (f , p)) x) y) z) w =
-- --   f (x , y , z , w)
-- -- snd (fst (fst (fst (JoinStructureBoolD A B (f , p)) x) y) z) =
-- --   p (x , y , z , snd (A false false)) (inr (inr refl))
-- -- fst (snd (fst (fst (JoinStructureBoolD A B (f , p)) x) y) i) w =
-- --   p (x , y , snd (A false true) , w) (inr (inl refl)) i 
-- -- snd (snd (fst (fst (JoinStructureBoolD A B (f , p)) x) y) i) = {!!}
-- -- fst (fst (snd (fst (JoinStructureBoolD A B (f , p)) x) i) z) w =
-- --   p (x , snd (A true false) , z , w) (inl (inr refl)) i
-- -- snd (fst (snd (fst (JoinStructureBoolD A B (f , p)) x) i) z) = {!!}
-- -- fst (snd (snd (fst (JoinStructureBoolD A B (f , p)) x) i) j) w = {!!}
-- -- snd (snd (snd (fst (JoinStructureBoolD A B (f , p)) x) i) j) = {!!}
-- -- fst (fst (fst (snd (JoinStructureBoolD A B (f , p)) i) y) z) w =
-- --   p (snd (A true true) , y , z , w) (inl (inl refl)) i
-- -- snd (fst (fst (snd (JoinStructureBoolD A B (f , p)) i) y) z) j = {!!}
-- -- snd (fst (snd (JoinStructureBoolD A B (f , p)) i) y) = {!!}
-- -- snd (snd (JoinStructureBoolD A B (f , p)) i) = {!!}

-- module _ {ℓ} (X Y : RP∞' ℓ) (A : fst X → fst Y → Pointed ℓ) (B : Type ℓ) where

--   JoinStructure : ((f : (x : fst X) (y : fst Y) → A x y .fst) → B) → Type ℓ
--   JoinStructure f =
--        (g : (x : fst X) (y : fst Y) → A x y .fst)
--     → UnordJoinR² X Y (λ x y → g x y ≡ pt (A x y))
--     → f g ≡ f (λ x y → pt (A x y))

-- module _ {ℓ} (X Y : RP∞' ℓ) (A : fst X → fst Y → Pointed ℓ) (B : Type ℓ) where

--   JoinStructure→ : (t : (f : (x : fst X) (y : fst Y) → A x y .fst) → B)
--     → JoinStructure X Y A B t
--     → JoinStructure Y X (λ y x → A x y) B
--                     λ f → t λ x y → f y x
--   JoinStructure→ f st g pr =
--     st (λ x y → g y x)
--        (UnordJoinFubiniFun Y X (λ x y → g x y ≡ pt (A y x)) pr)


--   inr* : _ → UnordSmash∙² X Y A .fst
--   inr* = inr

--   inr-case : (g : (x₁ : fst X) (y : fst Y) → A x₁ y .fst) (x : fst X)
--     → UnordJoinR Y (λ y → g x y ≡ pt (A x y))
--     → Path (UnordSmash Y (A x)) (inr (g x)) (inr (λ y → pt (A x y)))
--   inr-case g x (inlR (y , z)) = {!z!}
--   inr-case g x (inrR z) = {!!}
--   inr-case g x (pushR a b x₁ i) = {!!}

--   m2 : Σ _ (JoinStructure X Y A B) → UnordSmash∙² X Y A .fst → B
--   m2 (f , p) (inl x) = {!!}
--   m2 (f , p) (inr t) = {!!}
--   m2 (f , p) (push a i) = {!!}
  
--   m1 : (f : UnordSmash∙² X Y A .fst → B)
--      → Σ _ (JoinStructure X Y A B)
--   fst (m1 f) g = f (inr λ x → inr (g x))
--   snd (m1 f) g (inlR (x , inlR r)) = {!cong !}
--   snd (m1 f) g (inlR (x , inrR r)) = {!!}
--   snd (m1 f) g (inlR (x , pushR a b x₁ i)) = {!!}
--   snd (m1 f) g (inrR h) = cong f (cong inr* (funExt λ x → inr-case g x (h x)))
--   snd (m1 f) g (pushR a b x i) = {!!}

--   -- Smash→ : (Σ[ h ∈ (UnordΠ X (fst ∘ A) → fst B) ]
--   --              ((f : UnordΠ X ((λ r → fst r) ∘ A))
--   --              → UnordJoinR X (λ x → f x ≡ pt (A x))
--   --              → h f ≡ pt B))
--   --   → (UnordSmash X A → fst B)
--   -- Smash→ (h , f) (inl x) = pt B
--   -- Smash→ (h , f) (inr x) = h x
--   -- Smash→ (h , f) (push (x , a) i) =
--   --   f (UnordΣ→UnordΠ X A (x , a))
--   --     (inlR (RP∞'-fields.notRP∞' X x
--   --     , RP∞'-fields.elimRP∞'β X x a
--   --       (pt (A (RP∞'-fields.notRP∞' X x))) .snd)) (~ i)
