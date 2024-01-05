{-# OPTIONS --safe --lossy-unification #-}

{-
This file contiains.
-}

module Cubical.Cohomology.EilenbergMacLane.Steenrod.Base where

open import Cubical.Cohomology.EilenbergMacLane.Base
open import Cubical.Cohomology.EilenbergMacLane.Groups.Sn
open import Cubical.Cohomology.EilenbergMacLane.CupProduct
open import Cubical.Cohomology.EilenbergMacLane.Gysin
open import Cubical.Cohomology.EilenbergMacLane.Rings.RPinf
open import Cubical.Cohomology.EilenbergMacLane.Steenrod.sum-temp


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
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Univalence

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.Sn hiding (S)
open import Cubical.HITs.Pushout
open import Cubical.HITs.EilenbergMacLane1
open import Cubical.HITs.Susp
open import Cubical.HITs.S1
open import Cubical.HITs.RPn
open import Cubical.HITs.RPn.Unordered
open import Cubical.HITs.RPn.JoinFubini
open import Cubical.HITs.Join
open import Cubical.HITs.SmashProduct

open import Cubical.Data.Empty as ⊥
open import Cubical.Relation.Nullary


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

open Iso


-- 1. Construction of the steenrod squares
{-
Idea : We know that
  (RP∞ → EM ℤ/2 n → EM ℤ/2 (n + n)) ≃
  (EM ℤ/2 n → EM ℤ/2 0 × ... × EM ℤ/2 (n + n))

The RHS of this equivalence is the type of the total Steendrod square
(with the invidivual squares Sqⁱ given by taken i:th projection). To
define it, we work on the LHS of the equivalence.

We can generalise the LHS: Given a point (X : RP∞) and a function n :
X → ℕ, we may consider the sum of n, defined as follows:
-}

∑RP∞' : (X : RP∞' ℓ-zero) (n : fst X → ℕ) → ℕ
∑RP∞' X n =
  RP∞'→SetRec isSetℕ X
   (λ x → n x +' n (RP∞'-fields.notRP∞' X x))
   λ x → +'-comm (n x) _ ∙ cong (n (RP∞'-fields.notRP∞' X x) +'_)
                           (cong n (sym (notNotRP∞' X x)))

∑RP∞'≡ : (X : RP∞' ℓ-zero) (x : fst X) (n : fst X → ℕ)
  → ∑RP∞' X n ≡ n x +' n (RP∞'-fields.notRP∞' X x)
∑RP∞'≡ = RP∞'pt→Prop (λ _ → isPropΠ2 λ _ _ → isSetℕ _ _)
  λ { false n → +'-comm (n true) (n false)
     ; true n → refl}

{-
We may now ask: is there a function S_X taking undordered pairs
  (p : Π[ x : X ] (EM ℤ/2 (n x))) to EM ℤ/2 (∑ n).

In the special case when n is constant, we may define the total
Steenrod square S : (RP∞ → EM ℤ/2 n → EM ℤ/2 (n + n)) by taking the
diagonal of the above construction S(X,x) := S_X (λ _ → x)

So, the challenge: define, for each X : RP∞ and n : X → ℕ a function
of type Π[ x : X ] (EM ℤ/2 (n x)) → EM ℤ/2 (∑ n).

It's easy to do this when X is Bool (just take the cup product).

Problem: Woud like (Π[ x : X ] (EM ℤ/2 (n x)) → EM ℤ/2 (∑ n)) to be at
least an hSet for this argument to work.

Solution: beef up
  (Π[ x : X ] (EM ℤ/2 (n x)) → EM ℤ/2 (∑ n))
with a structure turning it into an
hSet -}

-- The relation
module _ {ℓ} (X : RP∞' ℓ) (A : fst X → Pointed ℓ) (B : Pointed ℓ) where
  BipointedUnordJoin : (f : ((x : fst X) → A x .fst) → fst B) → Type ℓ
  BipointedUnordJoin f =
      (g : (x : fst X) → A x .fst)
    → UnordJoinR X (λ x → g x ≡ A x .snd)
    → f g ≡ B .snd

-- The 'full' type of steenrod squares.
SteenrodFunType : (X : RP∞' ℓ-zero) (n : fst X → ℕ) → Type
SteenrodFunType X n =
  Σ[ f ∈ (((x : fst X) → EM ℤ/2 (n x)) → EM ℤ/2 (∑RP∞' X n)) ]
    BipointedUnordJoin X (λ x → EM∙ ℤ/2 (n x)) (EM∙ ℤ/2 (∑RP∞' X n)) f

-- Goal: Show that SteenrodFunType is simply the type of bipointed
-- functions when X is Bool. This allows us, in particular, to
-- conclude that it is an hSet.

-- We characterise the structure BipointedJoinBool in this case
module _ {ℓ} (A B T :  Pointed ℓ)
         (f : fst A → fst B → fst T) where
  BipointedJoinBool : Type ℓ
  BipointedJoinBool = (a : A .fst) (b : B .fst)
      → join (a ≡ A .snd) (b ≡ B .snd)
      → f a b ≡ T .snd

  JS'r : singl (pt B) → Type ℓ
  JS'r (b , p) = (a : fst A) → f a b ≡ T .snd

  BipointedJoinBool' : Type ℓ
  BipointedJoinBool' =
    Σ[ l ∈ ((a : singl (pt A)) (b : fst B) → f (fst a) b ≡ T .snd) ]
    Σ[ r ∈ ((b : singl (pt B)) (a : fst A) → f a (fst b) ≡ T .snd) ]
      ((a : _) (b : _) → l a (fst b) ≡ r b (fst a))

  BipointedJoinBool'' : Type ℓ
  BipointedJoinBool'' =
    Σ[ l ∈ ((b : fst B) → f (pt A) b ≡ T .snd) ]
    Σ[ r ∈ ((a : fst A) → f a (pt B) ≡ T .snd) ]
      l (pt B) ≡ r (pt A)

  IsoBipointedJoinBool₁ : Iso BipointedJoinBool BipointedJoinBool'
  fst (Iso.fun IsoBipointedJoinBool₁ F) (a , p) b = F a b (inl (sym p))
  fst (snd (Iso.fun IsoBipointedJoinBool₁ F)) (b , p) a = F a b (inr (sym p))
  snd (snd (Iso.fun IsoBipointedJoinBool₁ F)) (a , p) (b , q) =
    cong (F a b) (push (sym p) (sym q))
  Iso.inv IsoBipointedJoinBool₁ (l , r , lr) a b (inl x) = l (a , sym x) b
  Iso.inv IsoBipointedJoinBool₁ (l , r , lr) a b (inr x) = r (b , sym x) a
  Iso.inv IsoBipointedJoinBool₁ (l , r , lr) a b (push p q i) = lr (a , sym p) (b , sym q) i
  Iso.rightInv IsoBipointedJoinBool₁ _ = refl
  Iso.leftInv IsoBipointedJoinBool₁ F = funExt λ a → funExt λ b → funExt
    λ { (inl x) → refl ; (inr x) → refl ; (push a b i) → refl}

  IsoBipointedJoinBool₂ : Iso BipointedJoinBool' BipointedJoinBool''
  IsoBipointedJoinBool₂ = compIso
    (Σ-cong-iso
      {B = λ l → Σ[ r ∈ ((b : singl (pt B)) (a : fst A) → f a (fst b) ≡ T .snd) ]
                   ((a : _) (b : _) → l a (fst b) ≡ r b (fst a))}
      {B' = λ l → Σ[ r ∈ ((b : singl (pt B)) (a : fst A) → f a (fst b) ≡ T .snd) ]
                   ((b : _) → l (fst b) ≡ r b (pt A))}
      (DomainContrIso (isContrSingl (pt A)))
        λ x → Σ-cong-iso-snd λ r → DomainContrIso (isContrSingl (pt A)))
      (Σ-cong-iso-snd
        λ l → Σ-cong-iso {B = λ r → ((b : _) → l (fst b) ≡ r b (pt A))}
                          {B' = λ r → (l (pt B) ≡ r (pt A))}
      (DomainContrIso (isContrSingl (pt B)))
      λ _ → DomainContrIso (isContrSingl (pt B)))

  IsoBipointedJoinBool₃ : Iso BipointedJoinBool BipointedJoinBool''
  IsoBipointedJoinBool₃ = compIso IsoBipointedJoinBool₁ IsoBipointedJoinBool₂

-- Characterisation of the type of functions with a BipointedJoinBool
-- structure
module _ (A B T : Pointed ℓ-zero) where
  Iso-ΣBipointedJoinBool-⋀→∙ :
    Iso (Σ[ f ∈ (fst A → fst B → fst T) ] BipointedJoinBool A B T f)
        (A ⋀∙ B →∙ T)
  Iso-ΣBipointedJoinBool-⋀→∙ =
    compIso (Σ-cong-iso-snd (λ f → IsoBipointedJoinBool₃ A B T f)) main
    where
    F : (T : Type) (t : T)
      → Σ[ f ∈ (fst A → fst B → T) ]
          BipointedJoinBool'' A B (T , t) f → (A ⋀∙ B →∙ (T , t))
    fst (F T t (f , fl , fr , flr)) (inl x) = t
    fst (F T t (f , fl , fr , flr)) (inr x) = f (fst x) (snd x)
    fst (F T t (f , fl , fr , flr)) (push (inl x) i) = fr x (~ i)
    fst (F T t (f , fl , fr , flr)) (push (inr x) i) = fl x (~ i)
    fst (F T t (f , fl , fr , flr)) (push (push a i₁) i) = flr (~ i₁) (~ i)
    snd (F T t (f , fl , fr , flr)) = refl

    G-pre : (T : Type) (f : A ⋀ B → T)
      → Σ[ g ∈ (fst A → fst B → T) ] BipointedJoinBool'' A B (T , f (inl tt)) g
    fst (G-pre T f) a b = f (inr (a , b))
    fst (snd (G-pre T f)) b = cong f (sym (push (inr b)))
    fst (snd (snd (G-pre T f))) c = cong f (sym (push (inl c)))
    snd (snd (snd (G-pre T f))) j i = f (push (push tt (~ j)) (~ i))

    G-snd : (T : Type) (f : A ⋀ B → T) (t : T)
      → (f (inl tt) ≡ t)
      → BipointedJoinBool'' A B (T , t) (λ a b → f (inr (a , b)))
    G-snd T f = J> G-pre T f .snd

    G : (T : Type) (f : A ⋀ B → T) (t : T)
      → (f (inl tt) ≡ t)
      → Σ[ f ∈ (fst A → fst B → T) ] BipointedJoinBool'' A B (T , t) f
    fst (G T f t x) a b = f (inr (a , b))
    snd (G T f t x) = G-snd T f t x

    F∘G≡ : (T : Type) (f : A ⋀ B → T) (t : T) (p : f (inl tt) ≡ t)
      → F T t (G T f t p) ≡ (f , p)
    F∘G≡ T f =
      J> cong (F T (f (inl tt)))
          (ΣPathP (refl , (transportRefl (G-pre T f .snd))))
       ∙ ΣPathP ((funExt (
               λ { (inl x) → refl
                 ; (inr x) → refl
                 ; (push (inl x) i) → refl
                 ; (push (inr x) i) → refl
                 ; (push (push a i₁) i) → refl})) , refl)

    main : Iso (Σ[ f ∈ (fst A → fst B → fst T) ] BipointedJoinBool'' A B T f)
              (A ⋀∙ B →∙ T)
    Iso.fun main f = F (fst T) (snd T) f
    Iso.inv main f = G (fst T) (fst f) (snd T) (snd f)
    Iso.rightInv main f = F∘G≡ (fst T) (fst f) _ (snd f)
    Iso.leftInv main f = ΣPathP (refl , transportRefl (snd f))

  Iso-ΣBipointedJoinBool-Bipointed :
     Iso (Σ[ f ∈ (fst A → fst B → fst T) ] BipointedJoinBool A B T f)
          (A →∙ (B →∙ T ∙))
  Iso-ΣBipointedJoinBool-Bipointed =
    compIso (Iso-ΣBipointedJoinBool-⋀→∙) SmashAdjIso

Iso-BipointedUnordJoin-BipointedJoinBool :
  ∀ {ℓ} (A : Bool → Pointed ℓ) (B : Pointed ℓ)
  → (f : ((x : Bool) → A x .fst) → fst B)
  → Iso (BipointedUnordJoin (RP∞'∙ ℓ) A B f)
         (BipointedJoinBool (A true) (A false) B
           λ a b → f (CasesBool true a b))
Iso-BipointedUnordJoin-BipointedJoinBool A B f =
  compIso (codomainIsoDep (λ g → domIso join-UnordJoinR-iso))
    (compIso (ΠIso ΠBool×Iso λ g
      → codomainIso (pathToIso
        (cong (_≡ B .snd) (cong f (sym (CasesBoolη g)))))) curryIso)

-- SteenrodFunType at Bool is Bipointed maps
isSetSteenrodFunTypeBoolIso : (n : Bool → ℕ)
  → Iso (SteenrodFunType (RP∞'∙ ℓ-zero) n)
         (EM∙ ℤ/2 (n true) →∙ (EM∙ ℤ/2 (n false) →∙ EM∙ ℤ/2 (n true +' n false) ∙))
isSetSteenrodFunTypeBoolIso n =
  (compIso (Σ-cong-iso-snd (λ f → Iso-BipointedUnordJoin-BipointedJoinBool _ _ _))
    (compIso (invIso (Σ-cong-iso (compIso (invIso curryIso)
                                  (invIso (ΠIso ΠBool×Iso λ f → idIso)))
                      λ g → idIso))
    (Iso-ΣBipointedJoinBool-Bipointed (EM∙ ℤ/2 (n true)) (EM∙ ℤ/2 (n false))
             (EM∙ ℤ/2 (n true +' n false)))))

-- Corollary 1: SteenrodFunType is always a set
isSetSteenrodFunType : (X : RP∞' ℓ-zero) (n : fst X → ℕ)
  → isSet (SteenrodFunType X n)
isSetSteenrodFunType = RP∞'pt→Prop (λ _ → isPropΠ λ _ → isPropIsOfHLevel 2)
  λ n → isOfHLevelRetractFromIso 2
  (isSetSteenrodFunTypeBoolIso n)
  (isConnected→∙ (suc (n true)) 1
  (isConnectedEM (n true))
  (subst (λ m → isOfHLevel m (EM∙ ℤ/2 (n false) →∙ EM∙ ℤ/2 (n true +' n false)))
         (cong suc (+-comm 1 (n true)) )
         (isConnected→∙ (suc (n false)) (suc (n true))
           (isConnectedEM (n false))
           (subst (λ m → isOfHLevel (suc m) (EM ℤ/2 (n true +' n false)))
              (cong suc (+'≡+ (n true) (n false))
              ∙ (+-comm (suc (n true)) (n false)))
              (hLevelEM ℤ/2 (n true +' n false))))))

-- Corollay 2: To show that two elements (f , p) and (g , q) of type
-- SteenrodFunType are equal, it suffices to show that f ≡ g
SteenrodFunType≡ : (X : RP∞' ℓ-zero) (n : fst X → ℕ)
  (f g : SteenrodFunType X n)
  → fst f ≡ fst g
  → f ≡ g
SteenrodFunType≡ =
  RP∞'pt→Prop (λ X → isPropΠ4 λ n _ _ _ → isSetSteenrodFunType X n _ _)
   λ n f g p
    → sym (Iso.leftInv (isSetSteenrodFunTypeBoolIso n) f)
    ∙∙ cong (inv (isSetSteenrodFunTypeBoolIso n))
         (→∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneousEM _))
           (funExt (λ x → →∙Homogeneous≡ (isHomogeneousEM _)
             (funExt λ y → transportRefl _
                          ∙ funExt⁻ p (×→ΠBool (x , y))
                          ∙ sym (transportRefl _)))))
    ∙∙ Iso.leftInv (isSetSteenrodFunTypeBoolIso n) g

-- We can now construct the Steenrod squares
-- ⌣ₖ₂ : {n m : ℕ} → EM ℤ/2 n → EM ℤ/2 m → EM ℤ/2 (n +' m)
-- ⌣ₖ₂ = _⌣ₖ_ {G'' = ℤ/2Ring}

-- To construct the steenrod squares, we need to:
-- a) construct the underlying function
--  Π[ x ∈ X ] (EM ℤ/2 (n x)) → EM ℤ/2 (∑ n) given
-- some (x : X)

preSq : (X : RP∞' ℓ-zero) (x : fst X) (n : fst X → ℕ)
     (f : ((x₁ : fst X) → EM ℤ/2 (n x₁))) → EM ℤ/2 (∑RP∞' X n)
preSq X x n f =
  subst (EM ℤ/2) (sym (∑RP∞'≡ X x n))
        (⌣ₖ₂ (f x) (f (RP∞'-fields.notRP∞' X x)))

-- This is the cup product when X is Bool
preSqBool : (n : Bool → ℕ) (f : ((x₁ : Bool) → EM ℤ/2 (n x₁)))
  → EM ℤ/2 (∑RP∞' (RP∞'∙ ℓ-zero) n)
preSqBool n f = ⌣ₖ₂ (f true) (f false)

preSqBool≡ : (n : Bool → ℕ) (f : ((x₁ : Bool) → EM ℤ/2 (n x₁)))
  → preSq (RP∞'∙ ℓ-zero) true n f ≡ preSqBool n f
preSqBool≡ n f = (λ j → subst (EM ℤ/2)
                     (isSetℕ _ _ (sym (∑RP∞'≡ (RP∞'∙ ℓ-zero) true n)) refl j)
                     (preSqBool n f))
           ∙ transportRefl _

-- We then need to b) show that this has a BipointedUnordJoin structure
preSqCoh : (X : RP∞' ℓ-zero) (x : fst X) (n : fst X → ℕ)
  → BipointedUnordJoin X (λ x₁ → EM∙ ℤ/2 (n x₁))
                          (EM∙ ℤ/2 (∑RP∞' X n)) (preSq X x n)
preSqCoh = JRP∞' λ n → Iso-BipointedUnordJoin-BipointedJoinBool
                        (λ x₁ → EM∙ ℤ/2 (n x₁))
                        (EM∙ ℤ/2 (∑RP∞' (RP∞'∙ ℓ-zero) n))
                        (preSq (RP∞'∙ ℓ-zero) true n) .Iso.inv
                        λ g x r → preSqBool≡ n _ ∙ preSqCohBool n g x r
  where
  preSqCohBool : (n : Bool → ℕ)
    → BipointedJoinBool (EM∙ ℤ/2 (n true)) (EM∙ ℤ/2 (n false))
                         (EM∙ ℤ/2 (∑RP∞' (RP∞'∙ ℓ-zero) n))
           (λ a b → preSqBool n (CasesBool true a b))
  preSqCohBool n =
    Iso-ΣBipointedJoinBool-⋀→∙ (EM∙ ℤ/2 (n true)) (EM∙ ℤ/2 (n false))
             (EM∙ ℤ/2 (∑RP∞' (RP∞'∙ ℓ-zero) n)) .Iso.inv
      (preSq' n ∘∙ (⋀→Smash , refl)) .snd
    where
    preSq' : (n : Bool → ℕ)
      → SmashPt (EM∙ ℤ/2 (n true)) (EM∙ ℤ/2 (n false))
      →∙ EM∙ ℤ/2 (n true +' n false)
    fst (preSq' n) basel = 0ₖ (n true +' n false)
    fst (preSq' n) baser = 0ₖ (n true +' n false)
    fst (preSq' n) (proj x y) = ⌣ₖ₂ x y
    fst (preSq' n) (gluel a i) = ⌣ₖ-0ₖ {G'' = ℤ/2Ring} (n true) (n false) a i
    fst (preSq' n) (gluer b i) = 0ₖ-⌣ₖ {G'' = ℤ/2Ring} (n true) (n false) b i
    snd (preSq' n) = refl

-- and finally, because the codomain is an hSet and not an hProp,
-- c) verify that this construction is invariant under negation on X.

preSqCohComm : (X : RP∞' ℓ-zero) (x : fst X) (n : fst X → ℕ)
  → Path (SteenrodFunType X n)
          (preSq X x n , preSqCoh X x n)
          (preSq X (RP∞'-fields.notRP∞' X x) n
            , preSqCoh X (RP∞'-fields.notRP∞' X x) n)
preSqCohComm =
  JRP∞' λ n → SteenrodFunType≡ (RP∞'∙ ℓ-zero) n _ _
    (funExt λ f
    → cong (subst (EM ℤ/2) (sym (∑RP∞'≡ (RP∞'∙ ℓ-zero) true n)))
            (⌣ₖ-commℤ/2 (n true) (n false) (f true) (f false))
     ∙ help _ (+'-comm (n false) (n true)) _
              (sym (∑RP∞'≡ (RP∞'∙ ℓ-zero) true n))
              (sym (∑RP∞'≡ (RP∞'∙ ℓ-zero) false n))
        (⌣ₖ₂ (f false) (f true)))
  where
  help : {n : ℕ} (m : ℕ) (p : n ≡ m) (l : ℕ) (q : m ≡ l) (r : n ≡ l)
    → (x : EM ℤ/2 n)
    → subst (EM ℤ/2) q (subst (EM ℤ/2) p x) ≡ subst (EM ℤ/2) r x
  help = J> (J> λ r x
    → transportRefl _
     ∙ λ j → subst (EM ℤ/2) (isSetℕ _ _ refl r j) x)

-- This gives the total Steenrod squares (as an element of SteenrodFunType)
SteenrodFun : (X : RP∞' ℓ-zero) (n : fst X → ℕ) → SteenrodFunType X n
SteenrodFun X n =
  RP∞'→SetRec
    (isSetSteenrodFunType X n) X
    (λ x → preSq X x n , preSqCoh X x n)
    (λ x → preSqCohComm X x n)

-- The total square without the additional structure
S : (X : RP∞' ℓ-zero) (n : fst X → ℕ)
       (f : ((x₁ : fst X) → EM ℤ/2 (n x₁))) → EM ℤ/2 (∑RP∞' X n)
S X n f = SteenrodFun X n .fst f

SteenrodFunId : (X : RP∞' ℓ-zero) (n : fst X → ℕ)
  (x : fst X) (g : (x₁ : fst X) → EM ℤ/2 (n x₁))
  → S X n g ≡ preSq X x n g
SteenrodFunId X n x g i =
  RP∞'→SetRecβ
    (isSetSteenrodFunType X n) X
    (λ x → preSq X x n , preSqCoh X x n)
    (λ x → preSqCohComm X x n) x i .fst g

SteenrodFunBool : (n : Bool → ℕ) (g : _)
  → S (RP∞'∙ ℓ-zero) n g ≡ ⌣ₖ₂ (g true) (g false)
SteenrodFunBool n g = SteenrodFunId (RP∞'∙ ℓ-zero) n true g ∙ preSqBool≡ n g

-- The total squares (with the expected type)
private
  makeSquare : (n : ℕ)
      → (EM ℤ/2 1 → EM ℤ/2 n → EM ℤ/2 (n +' n))
      → (EM ℤ/2 n → (EM ℤ/2) ˣ (n +' n))
  makeSquare n f y = Iso.fun (RP→EM-ℤ/2-CharacIso _) λ x → f x y

  makeSquare' : (n : ℕ)
      → (RP∞' ℓ-zero → EM ℤ/2 n → EM ℤ/2 (n +' n))
      → (EM ℤ/2 n → (EM ℤ/2) ˣ (n +' n))
  makeSquare' n f y = makeSquare n (λ x y → f (EM₁-ℤ/2→RP∞' x) y) y

∑RP∞'const : (X : RP∞' ℓ-zero) (n : ℕ) → ∑RP∞' X (λ _ → n) ≡ (n +' n)
∑RP∞'const = RP∞'pt→Prop (λ _ → isPropΠ λ _ → isSetℕ _ _) λ  _ → refl

SqTot : (n : ℕ) → EM ℤ/2 n → (EM ℤ/2) ˣ (n +' n)
SqTot n = makeSquare' n λ X y → subst (EM ℤ/2) (∑RP∞'const X n) (S X (λ _ → n) (λ _ → y))

SqIneq : (n i : ℕ) (p : i ≤ n) → (i +' n) ≤ (n +' n)
SqIneq n i p =
  subst2 _≤_ (sym (+'≡+ i n)) (sym (+'≡+ n n))
    (≤-+-≤ p (0 , refl))

Sq : (n i : ℕ) → (i ≤ n) → EM ℤ/2 n → EM ℤ/2 (i +' n)
Sq n i p x = projˣ (EM ℤ/2) (n +' n) (i +' n) (SqIneq n i p) (SqTot n x)

open import Cubical.Data.FinData.DepFinVec

RP→EM-ℤ/2-CharacIso'-expl' : (n : ℕ) (f : _) (x : _)
  → Iso.inv (RP→EM-ℤ/2-CharacIso' n) f x
    ≡ sum {A = EM ℤ/2} _+ₖ_ ⌣ₖ₂' (expEM₁ x) (fst f) n
RP→EM-ℤ/2-CharacIso'-expl' zero f x = sym (1ₖ-⌣ₖ {G'' = ℤ/2Ring} zero (fst f zero))
  ∙ sym (transportRefl _)
  ∙ sym (transportRefl _)
RP→EM-ℤ/2-CharacIso'-expl' (suc n) f x =
  (cong₂ _+ₖ_ ((λ j → subst (EM ℤ/2) (isSetℕ _ _ (+'-suc₁ n) (+'≡+ 1 n) j)
               (⌣[]ₖ-syntax ℤ/2Ring x (RP→EM-ℤ/2-CharacIso'-expl' n (ΠDepFinVec↓ n (EM∙ ℤ/2) f) x j)))
    ∙ cong₂ (⌣ₖ₂' 1 n) refl (cong (λ s → sum-helper≤ n s _+ₖ_ n (0 , (λ _ → n)))
        (funExt λ p → funExt λ r →
          cong (subst (EM ℤ/2) (snd r))
            (cong (⌣ₖ₂' (fst r) p (expEM₁ x (fst r)))
              (ΠDepFinVec↓₁≡ n (EM∙ ℤ/2) f p r))))
    ∙ sym (distrL-sum-helper≤ n
        (λ p r → subst (EM ℤ/2) (snd r)
                   (⌣ₖ₂' (fst r) p (expEM₁ x (fst r)) (fst f p)))
        (0ₖ n) _+ₖ_ _+ₖ_ (⌣ₖ₂' 1 n)
          (λ b a1 a2 → sym (distrL⌣ₖ₂' 1 n b a1 a2))
          x n (0 , refl)))
    
    (λ _ → fst f (suc n)))
    ∙ cong₂ _+ₖ_
      (sum-helper<-eq (suc n) _ _ _+ₖ_
          help' n
        (0 , refl)
        (≤-trans (0 , (λ _ → n)) (1 , refl))
        (≤-trans (1 , (λ _ → suc n)) (0 , (λ _ → suc n))))
      (refl {x = (fst f (suc n))} 
        ∙ (sym (1ₖ-⌣ₖ {G'' = ℤ/2Ring} (suc n) (fst f (suc n)))
        ∙ sym (transportRefl _))
        ∙ sym (transportRefl _))
  where
  help' : (t : ℕ) (q : t < suc n) →
      ⌣ₖ₂' 1 n x
      (subst (EM ℤ/2) (λ i → predℕ (snd (<-weaken q) i))
       (⌣ₖ₂' (fst q) t (expEM₁ x (fst q)) (fst f t)))
      ≡
      subst (EM ℤ/2) (snd (<-weaken q))
      (⌣ₖ₂' (fst (<-weaken q)) t (⌣ₖ₂' 1 (fst q) x (expEM₁ x (fst q)))
       (fst f t))
  help' t r =
      (sym (substCommSlice (EM ℤ/2) (EM ℤ/2 ∘ suc)
            (λ n p → ⌣ₖ₂' 1 n x p) (cong predℕ (snd (<-weaken r))) s)
    ∙ cong (λ p → subst (EM ℤ/2) p (⌣ₖ₂' 1 (fst r + t) x s))
           (isSetℕ _ _ (cong suc (cong predℕ (snd (<-weaken r))))
                        (snd (<-weaken r))))
    ∙ cong (subst (EM ℤ/2) (snd (<-weaken r)))
           (assoc⌣ₖ₂' 1 (fst r) t x (expEM₁ x (fst r)) (fst f t))
    where
    s = (⌣ₖ₂' (fst r) t (expEM₁ x (fst r)) (fst f t))

RP→EM-ℤ/2-CharacIso'inv-hom⌣ : (n m : ℕ) (f : _) (g : _) (x : _)
  → ⌣ₖ₂' n m (Iso.inv (RP→EM-ℤ/2-CharacIso' n) f x)
              (Iso.inv (RP→EM-ℤ/2-CharacIso' m) g x)
    ≡ Iso.inv (RP→EM-ℤ/2-CharacIso' (n + m))
              (⌣ΠDepFinVec n m f g) x
RP→EM-ℤ/2-CharacIso'inv-hom⌣ n m f g x =
  cong₂ (⌣ₖ₂' n m) (RP→EM-ℤ/2-CharacIso'-expl' n f x) (RP→EM-ℤ/2-CharacIso'-expl' m g x)
  ∙∙ {!!}
  ∙∙ {!sym (RP→EM-ℤ/2-CharacIso'-expl' (n + m) (⌣ΠDepFinVec n m f g) x)!}

-- RP→EM-ℤ/2-CharacIso'-expl : (n : ℕ) (f : _) (x : _)
--   → Iso.inv (RP→EM-ℤ/2-CharacIso' n) f x
--     ≡ sum' {A = EM ℤ/2} {B = EM ℤ/2} _+ₖ_ ⌣ₖ₂' (expEM₁ x)  (f .fst) n
-- RP→EM-ℤ/2-CharacIso'-expl zero f x =
--    sym (1ₖ-⌣ₖ {G'' = ℤ/2Ring} zero (fst f zero))
--     ∙ sym (transportRefl _)
-- RP→EM-ℤ/2-CharacIso'-expl (suc n) f x =
--     cong₂ _+ₖ_ (cong (λ z → ⌣RP∞''Equiv n .fst z .fst x)
--                  (funExt (RP→EM-ℤ/2-CharacIso'-expl n (ΠDepFinVec↓ n (EM∙ ℤ/2) f)))
--               ∙ (λ i → subst (EM ℤ/2) (+'-suc₁ n)
--                           (⌣ₖ₂ {n = 1} {m = n} x
--                                (sum' _+ₖ_ ⌣ₖ₂' (expEM₁ x) (ΠDepFinVec↓₁ n (EM∙ ℤ/2) f) n)))
--               ∙ {!!})
--                  (refl {x = fst f (suc n)}
--                  ∙ sym (1ₖ-⌣ₖ {G'' = ℤ/2Ring} (suc n) (fst f (suc n)))
--                  ∙ sym (transportRefl _))
--   ∙ refl

-- -- RP→EM-ℤ/2-CharacIso-hom' : (n m : ℕ) (x : _) (y : _)
-- --   → Iso.inv (RP→EM-ℤ/2-CharacIso' (n + m)) (mult⌣ n m x y)
-- --    ≡ λ a → ⌣ₖ₂' n m (Iso.inv (RP→EM-ℤ/2-CharacIso' n) x a)
-- --                      (Iso.inv (RP→EM-ℤ/2-CharacIso' m) y a)
-- -- RP→EM-ℤ/2-CharacIso-hom' zero m f g =
-- --     cong (inv (RP→EM-ℤ/2-CharacIso' m)) (mult⌣₀ₗ m f g)
-- --   ∙ funExt (help _ refl)
-- --   where
-- --   help : (t : ℤ/2 .fst) (r : fst f zero ≡ t) (x : EM ℤ/2 1)
-- --     → inv (RP→EM-ℤ/2-CharacIso' m) (mult⌣₀ₗ m f g i1) x
-- --     ≡ ⌣ₖ₂' zero m (fst f zero) (inv (RP→EM-ℤ/2-CharacIso' m) g x)
-- --   help = ℤ/2-elim
-- --     (λ r x → (funExt⁻ (cong (inv (RP→EM-ℤ/2-CharacIso' m))
-- --          (toPathΠDepFinVec (EM∙ ℤ/2) _ λ k p
-- --            → cong (λ t → ⌣ₖ₂ {n = zero} {m = k} t (fst g k)) r
-- --             ∙ 0ₖ-⌣ₖ {G'' = ℤ/2Ring} zero k (fst g k))) x
-- --       ∙ funExt⁻ (RP→EM-ℤ/2-CharacIso'inv∙ m) x)
-- --       ∙ sym (subst-EM-0ₖ (+'≡+ zero m))
-- --       ∙ cong (subst (EM ℤ/2) (+'≡+ zero m))
-- --         (sym (0ₖ-⌣ₖ {G'' = ℤ/2Ring} zero m (inv (RP→EM-ℤ/2-CharacIso' m) g x))
-- --        ∙ cong (λ t → ⌣ₖ₂ {n = zero} {m = m} t (inv (RP→EM-ℤ/2-CharacIso' m) g x))
-- --               (sym r)))
-- --     λ r x → funExt⁻ (cong (inv (RP→EM-ℤ/2-CharacIso' m))
-- --               (toPathΠDepFinVec (EM∙ ℤ/2) _ λ k _
-- --                 → cong (λ t → ⌣ₖ₂ {n = zero} {m = k} t (fst g k)) r
-- --                 ∙ 1ₖ-⌣ₖ {G'' = ℤ/2Ring} k (fst g k))) x
-- --       ∙ sym (transportRefl _) -- sym (subst-EM-0ₖ (+'≡+ zero m))
-- --       ∙ cong (subst (EM ℤ/2) (+'≡+ zero m))
-- --         (sym (1ₖ-⌣ₖ {G'' = ℤ/2Ring} m (inv (RP→EM-ℤ/2-CharacIso' m) g x))
-- --        ∙ cong (λ t → ⌣ₖ₂ {n = zero} {m = m} t (inv (RP→EM-ℤ/2-CharacIso' m) g x))
-- --               (sym r))
-- -- RP→EM-ℤ/2-CharacIso-hom' (suc n) m f g =
-- --   funExt λ x → (λ i
-- --   → subst (EM ℤ/2)(+'-suc₁ (n + m))
-- --          (fst
-- --           (⌣RP∞'Equiv (n + m) .fst
-- --            (inv (RP→EM-ℤ/2-CharacIso' (n + m))
-- --             (tsa i))) x)
-- --     +ₖ (sum' _+ₖ_ ⌣ₖ₂' (fst f) (fst g) ((suc n) + m)))
-- --    ∙ (λ i → subst (EM ℤ/2)(+'-suc₁ (n + m))
-- --          (fst (⌣RP∞'Equiv (n + m) .fst
-- --            (RP→EM-ℤ/2-CharacIso-hom' n m (ΠDepFinVec↓ n (EM∙ ℤ/2) f) g i)) x)
-- --     +ₖ (lem1 i))
-- --    ∙ {!inv (RP→EM-ℤ/2-CharacIso' m) g x!}
-- --    ∙ sym (⌣ₖ₂'-distrₗ (suc n) m
-- --       (fst (⌣RP∞''Equiv n .fst  (inv (RP→EM-ℤ/2-CharacIso' n) (ΠDepFinVec↓ n (EM∙ ℤ/2) f))) x)
-- --       (idfun (EM ℤ/2 (suc n)) (fst f (suc n)))
-- --       (inv (RP→EM-ℤ/2-CharacIso' m) g x))
-- --   where
-- --   ⌣ₖ₂'-distrₗ : (n m : ℕ) (x y : EM ℤ/2 n) (z : EM ℤ/2 m)
-- --     → ⌣ₖ₂' n m (x +ₖ y) z ≡ ⌣ₖ₂' n m x z +ₖ ⌣ₖ₂' n m y z
-- --   ⌣ₖ₂'-distrₗ n m x y z = {!(inv (RP→EM-ℤ/2-CharacIso' m) (suc m) g x)!}
-- --   lem1 : sum' _+ₖ_ ⌣ₖ₂' (fst f) (fst g) ((suc n) + m)
-- --        ≡ ⌣ₖ₂' (suc n) m (fst f (suc n)) (fst g m)
-- --   lem1 = {!⌣ₖ₂' (suc n) m
-- --       (fst
-- --        (⌣RP∞''Equiv n .fst
-- --         (inv (RP→EM-ℤ/2-CharacIso' n) (ΠDepFinVec↓ n (EM∙ ℤ/2) (fst f , snd f))))
-- --        x
-- --        +ₖ idfun (EM ℤ/2 (suc n)) (fst f (suc n)))
-- --       (inv (RP→EM-ℤ/2-CharacIso' m) g x)!}

-- --   prs : (k : ℕ) → fst (fun (ΠDepFinVec-ind (n + m) (EM∙ ℤ/2)) (mult⌣ (suc n) m f g) .snd) k
-- --                   ≡ fst (mult⌣ n m (ΠDepFinVec↓ n (EM∙ ℤ/2) f) g) k
-- --   prs k = {! -- (Iso.inv (RP→EM-ℤ/2-CharacIso' m) g ?)!} -- Π↓-mult n m (EM∙ ℤ/2) (EM∙ ℤ/2) k _+ₖ_ ⌣ₖ₂' f (fst g)
-- --         ∙ {!!}

-- --   tsa : Iso.fun (ΠDepFinVec-ind (n + m) (EM∙ ℤ/2)) (mult⌣ (suc n) m f g) .snd
-- --       ≡ mult⌣ n m (ΠDepFinVec↓ n (EM∙ ℤ/2) f) g
-- --   tsa = toPathΠDepFinVec (EM∙ ℤ/2) _
-- --     λ k p → {!!}

-- -- -- RP→EM-ℤ/2-CharacIso-hom' : (n m : ℕ) (x : _) (y : _)
-- -- --   → Iso.inv (RP→EM-ℤ/2-CharacIso (n + m)) (multˣ ⌣ₖ₂' n m x y)
-- -- --    ≡ λ a → ⌣ₖ₂' n m (Iso.inv (RP→EM-ℤ/2-CharacIso n) x a) (Iso.inv (RP→EM-ℤ/2-CharacIso m) y a)
-- -- -- RP→EM-ℤ/2-CharacIso-hom' zero m =
-- -- --   ℤ/2-elim
-- -- --     (λ y → cong (inv (RP→EM-ℤ/2-CharacIso m))
-- -- --               (multˣAnnₗ ⌣ₖ₂' 0ₖ (λ n m a → cong (subst (EM ℤ/2) (+'≡+ n m)) (0ₖ-⌣ₖ n m a)
-- -- --                               ∙ subst-EM∙ (+'≡+ n m)  .snd) zero m y)
-- -- --          ∙ cong (inv (RP→EM-ℤ/2-CharacIso m)) (sym (RP→EM-ℤ/2-CharacIso∙ m))
-- -- --          ∙ Iso.leftInv (RP→EM-ℤ/2-CharacIso m) (λ _ → 0ₖ m)
-- -- --          ∙ funExt λ a → sym (0ₖ-⌣ₖ₂' zero m (inv (RP→EM-ℤ/2-CharacIso m) y a)))
-- -- --     λ y → cong (inv (RP→EM-ℤ/2-CharacIso m))
-- -- --             (multˣIdL ⌣ₖ₂' fone (λ m a → transportRefl _ ∙ 1ₖ-⌣ₖ m a) m y)
-- -- --         ∙ funExt λ a → sym (1ₖ-⌣ₖ m (inv (RP→EM-ℤ/2-CharacIso m) y a))
-- -- --                       ∙ sym (transportRefl _)
-- -- -- RP→EM-ℤ/2-CharacIso-hom' (suc n) m (f , y) g =
-- -- --   funExt λ x → (λ i → fst (⌣RP∞''Equiv (n + m))
-- -- --                             (RP→EM-ℤ/2-CharacIso-hom' n m f g i) .fst x
-- -- --                          +ₖ ⌣ₖ₂' (suc n) m y (lastˣ (EM ℤ/2) m g))
-- -- --              ∙∙ (λ i → subst (EM ℤ/2) (+'-suc₁ (n + m))
-- -- --                           (⌣ₖ₂ {n = 1} {n + m} x
-- -- --                             (⌣ₖ₂' n m (inv (RP→EM-ℤ/2-CharacIso n) f x)
-- -- --                               (inv (RP→EM-ℤ/2-CharacIso m) g x)))
-- -- --                +ₖ ⌣ₖ₂' (suc n) m y (lastˣ (EM ℤ/2) m g))
-- -- --              ∙∙ {!subst (EM ℤ/2) (+'≡+ (suc n) m)
-- -- --       (⌣ₖ₂
-- -- --        (subst (EM ℤ/2) (+'-suc₁ n)
-- -- --         (⌣ₖ₂ x (inv (RP→EM-ℤ/2-CharacIso n) f x)))
-- -- --        (inv (RP→EM-ℤ/2-CharacIso m) g x)
-- -- --        +ₖ ⌣ₖ₂ y (inv (RP→EM-ℤ/2-CharacIso m) g x))!}
-- -- --                ∙ cong (subst (EM ℤ/2) (+'≡+ (suc n) m))
-- -- --                    ( (sym (help' n x (inv (RP→EM-ℤ/2-CharacIso n) f x) (inv (RP→EM-ℤ/2-CharacIso m) g x) y))) -- (sym (help' n x (inv (RP→EM-ℤ/2-CharacIso n) f x) (inv (RP→EM-ℤ/2-CharacIso m) g x) y .fst))
-- -- --              ∙∙ (λ i → subst (EM ℤ/2) (+'≡+ (suc n) m)
-- -- --                   (⌣ₖ₂ {n = suc n} {m = m} (subst (EM ℤ/2) (+'-suc₁ n)
-- -- --                      (⌣ₖ₂ {n = 1} {n} x (inv (RP→EM-ℤ/2-CharacIso n) f x)) +ₖ y)
-- -- --                      (inv (RP→EM-ℤ/2-CharacIso m) g x)))
-- -- --              ∙∙ λ i → ⌣ₖ₂' (suc n) m (fst (⌣RP∞''Equiv n) (inv (RP→EM-ℤ/2-CharacIso n) f) .fst x
-- -- --                 +ₖ y) (inv (RP→EM-ℤ/2-CharacIso m) g x)
-- -- --   where
-- -- --   help' : (n : ℕ) (x : EM ℤ/2 1) (f : EM ℤ/2 n) (g : EM ℤ/2 m) (y : EM ℤ/2 (suc n))
-- -- --     → (⌣ₖ₂ {n = suc n} {m = m}
-- -- --         (subst (EM ℤ/2) (+'-suc₁ n)
-- -- --           (⌣ₖ₂ {n = 1} {m = n} x f) +ₖ y) g
-- -- --       ≡ ⌣ₖ₂ {n = suc n} {m = m} (subst (EM ℤ/2) (+'-suc₁ n) (⌣ₖ₂ {n = 1} {m = n} x f)) g
-- -- --       +ₖ ⌣ₖ₂ {n = suc n} {m = m} y g)
-- -- --      -- × ((g' : EM ℤ/2 m)
-- -- --      --   → (subst (EM ℤ/2) (+'-suc₁ (n + m))
-- -- --      --      (⌣ₖ₂ x (⌣ₖ₂' n m f g))
-- -- --      --   +ₖ ⌣ₖ₂' (suc n) m y g'
-- -- --      -- ≡ {!!} +ₖ {!⌣ₖ₂' (suc n) m y g'!}))
-- -- --   help' n x = {!!}
-- -- --     where
-- -- --     c : {!!}
-- -- --     c = {!!}
-- -- --   main : (n m k l : ℕ) (x : EM ℤ/2 n) (y : EM ℤ/2 m) (z : EM ℤ/2 k) (w : EM ℤ/2 l)
-- -- --     → subst (EM ℤ/2) {!!} (⌣ₖ₂ x {!!}) +ₖ subst (EM ℤ/2) {!lastˣ (EM ℤ/2) m !} (⌣ₖ₂ y w) ≡ {!⌣ₖ₂' (suc n) m y (lastˣ (EM ℤ/2) m g)!}
-- -- --   main = {!!}
-- -- -- {-
-- -- -- Goal: fst
-- -- --       (inv (Cubical.Cohomology.EilenbergMacLane.Rings.RPinf.help (n + m))
-- -- --        (inv (RP→EM-ℤ/2-CharacIso (n + m)) (multˣ ⌣ₖ₂' n m (fst f) g)))
-- -- --       x
-- -- --       +ₖ
-- -- --       idfun (EM ℤ/2 (suc (n + m)))
-- -- --       (⌣ₖ₂' (suc n) m (snd f) (lastˣ (EM ℤ/2) m g))
-- -- --       ≡
-- -- --       ⌣ₖ₂' (suc n) m
-- -- --       (fst
-- -- --        (inv (Cubical.Cohomology.EilenbergMacLane.Rings.RPinf.help n)
-- -- --         (inv (RP→EM-ℤ/2-CharacIso n) (fst f)))
-- -- --        x
-- -- --        +ₖ idfun (EM ℤ/2 (suc n)) (snd f))
-- -- --       (inv (RP→EM-ℤ/2-CharacIso m) g x)
-- -- -- -}




-- -- -- RP→EM-ℤ/2-CharacIso-hom : (n m : ℕ)
-- -- --   (f : EM ℤ/2 1 → EM ℤ/2 n) (g : EM ℤ/2 1 → EM ℤ/2 m)
-- -- --   → Iso.fun (RP→EM-ℤ/2-CharacIso (n + m)) (λ x → ⌣ₖ₂' n m (f x) (g x))
-- -- --    ≡ multˣ ⌣ₖ₂' n m (Iso.fun (RP→EM-ℤ/2-CharacIso n) f)
-- -- --                 (Iso.fun (RP→EM-ℤ/2-CharacIso m) g)
-- -- -- RP→EM-ℤ/2-CharacIso-hom zero m f g = {!!}
-- -- -- RP→EM-ℤ/2-CharacIso-hom (suc n) m f g = {!!}
