{-# OPTIONS --safe --lossy-unification #-}

{-
This file contiains.
-}

module Cubical.Cohomology.EilenbergMacLane.Steenrod where

open import Cubical.Cohomology.EilenbergMacLane.Base
open import Cubical.Cohomology.EilenbergMacLane.Groups.Sn
open import Cubical.Cohomology.EilenbergMacLane.CupProduct
open import Cubical.Cohomology.EilenbergMacLane.Gysin
open import Cubical.Cohomology.EilenbergMacLane.Rings.RPinf

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
⌣ₖ₂ : {n m : ℕ} → EM ℤ/2 n → EM ℤ/2 m → EM ℤ/2 (n +' m)
⌣ₖ₂ = _⌣ₖ_ {G'' = ℤ/2Ring}

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

-- module _ {ℓ} (X Y : RP∞' ℓ) (A : fst X → fst Y → Pointed ℓ) (B : Pointed ℓ) where
--   QuadpointedUnordJoin : (f : ((x : fst X) (y : fst Y) → A x y .fst) → fst B) → Type ℓ
--   QuadpointedUnordJoin f = (g : (x : fst X) (y : fst Y) → A x y .fst)
--     → UnordJoinR X (λ x → UnordJoinR Y λ y → g x y ≡ A x y .snd)
--     → f g ≡ B .snd

-- ΣQuadpointTy : (X Y : RP∞' ℓ-zero) (n : fst X → fst Y → ℕ)
--   → Type
-- ΣQuadpointTy X Y n =
--   Σ[ f ∈ (((x : fst X) (y : fst Y) → EM ℤ/2 (n x y))
--          → EM ℤ/2 (∑RP∞' X λ x → ∑RP∞' Y λ y → n x y)) ]
--       QuadpointedUnordJoin X Y
--         (λ x y → EM∙ ℤ/2 (n x y))
--         (EM∙ ℤ/2 (∑RP∞' X λ x → ∑RP∞' Y λ y → n x y)) f

-- SteenrodFun4 : (X Y : RP∞' ℓ-zero) (n : fst X → fst Y → ℕ)
--   → ΣQuadpointTy X Y n
-- fst (SteenrodFun4 X Y n) f = SteenrodFun X (λ x → ∑RP∞' Y (n x)) .fst λ x → SteenrodFun Y (n x) .fst (f x)
-- snd (SteenrodFun4 X Y n) g (inlR p) = SteenrodFun X (λ x → ∑RP∞' Y (n x)) .snd _ (inlR (fst p , SteenrodFun Y (n (fst p)) .snd _ (snd p)))
-- snd (SteenrodFun4 X Y n) g (inrR f) = SteenrodFun X (λ x → ∑RP∞' Y (n x)) .snd _ (inrR λ x → SteenrodFun Y (n x) .snd _ (f x))
-- snd (SteenrodFun4 X Y n) g (pushR p f r i) =
--   SteenrodFun X (λ x → ∑RP∞' Y (n x)) .snd _
--     (pushR (fst p , SteenrodFun Y (n (fst p)) .snd _ (snd p))
--            (λ x → SteenrodFun Y (n x) .snd _ (f x))
--            (cong (SteenrodFun Y (n (fst p)) .snd (λ x₂ → g (fst p) x₂)) r) i)

-- SteenrodFun4comm' : (X Y : RP∞' ℓ-zero) (n : fst X → fst Y → ℕ)
--   → Σ[ f ∈ (((x : fst X) (y : fst Y) → EM ℤ/2 (n x y))
--          → EM ℤ/2 (∑RP∞' Y λ y → ∑RP∞' X λ x → n x y)) ]
--       QuadpointedUnordJoin Y X
--         (λ y x → EM∙ ℤ/2 (n x y))
--         (EM∙ ℤ/2 (∑RP∞' Y λ y → ∑RP∞' X λ x → n x y))
--         (λ g → f (λ x y → g y x))
-- fst (SteenrodFun4comm' X Y n) f =
--   SteenrodFun Y (λ z → ∑RP∞' X (λ x → n x z)) .fst
--     λ y → SteenrodFun X (λ x → n x y) .fst λ x → f x y
-- snd (SteenrodFun4comm' X Y n) g (inlR x) =
--   SteenrodFun Y (λ z → ∑RP∞' X (λ x₁ → n x₁ z)) .snd
--     (λ y → SteenrodFun X (λ x₁ → n x₁ y) .fst (λ x₁ → g y x₁))
--       (inlR (fst x , SteenrodFun X (λ x₁ → n x₁ (fst x)) .snd (g (fst x)) (snd x)))
-- snd (SteenrodFun4comm' X Y n) g (inrR f) =
--   SteenrodFun Y (λ y → ∑RP∞' X (λ x → n x y)) .snd
--     (λ y → SteenrodFun X (λ x → n x y) .fst (g y))
--     (inrR λ y → SteenrodFun X (λ x → n x y) .snd (g y) (f y))
-- snd (SteenrodFun4comm' X Y n) g (pushR a b x i) =
--   SteenrodFun Y (λ y → ∑RP∞' X (λ x → n x y)) .snd
--     (λ y → SteenrodFun X (λ x₁ → n x₁ y) .fst (g y))
--       (pushR (fst a , SteenrodFun X (λ x → n x (fst a)) .snd (g (fst a)) (snd a))
--              (λ y → SteenrodFun X (λ x → n x y) .snd (g y) (b y))
--              (cong (SteenrodFun X (λ x₁ → n x₁ (fst a)) .snd (g (fst a))) x) i)

-- ∑RP∞'Fubini : (X Y : RP∞' ℓ-zero) (n : fst X → fst Y → ℕ)
--   → (∑RP∞' Y (λ y → ∑RP∞' X (λ x → n x y)))
--    ≡ (∑RP∞' X (λ x → ∑RP∞' Y (n x)))
-- ∑RP∞'Fubini =
--   RP∞'pt→Prop (λ X → isPropΠ2 λ _ _ → isSetℕ _ _)
--     (RP∞'pt→Prop ((λ _ → isPropΠ λ _ → isSetℕ _ _))
--       λ n → move4 (n true true) (n false true) (n true false) (n false false) _+'_
--         +'-assoc
--         +'-comm)

-- SteenrodFun4comm : (X Y : RP∞' ℓ-zero) (n : fst X → fst Y → ℕ)
--   → ΣQuadpointTy X Y n
-- fst (SteenrodFun4comm X Y n) f =
--   subst (EM ℤ/2) (∑RP∞'Fubini X Y n)
--     (SteenrodFun Y (λ z → ∑RP∞' X (λ x → n x z)) .fst
--       λ y → SteenrodFun X (λ x → n x y) .fst λ x → f x y)
-- snd (SteenrodFun4comm X Y n) f p =
--     cong (subst (EM ℤ/2) (∑RP∞'Fubini X Y n))
--       (SteenrodFun4comm' X Y n .snd (λ y x → f x y)
--         (UnordJoinFubiniFun X Y _ p))
--   ∙ subst-EM∙ (∑RP∞'Fubini X Y n) .snd

-- module _ (A B C D T :  Pointed ℓ-zero)
--          (f : fst A → fst B → fst C → fst D → fst T) where
--   JS4 : Type
--   JS4 = (a : fst A) (b : fst B) (c : fst C) (d : fst D)
--       → join (join (a ≡ snd A) (b ≡ snd B)) (join (c ≡ snd C) (d ≡ snd D))
--       → f a b c d ≡ pt T

-- mainA : (A B C D T : Pointed ℓ-zero)
--   → Iso (Σ[ f ∈ (fst A → fst B → fst C → fst D → fst T) ]
--             JS4 A B C D T f)
--          (A →∙ (B →∙ C →∙ D →∙ T ∙ ∙ ∙))
-- mainA A B C D T =
--   compIso
--    (compIso IsMain
--      (Σ-cong-iso
--        (codomainIso (codomainIso (Iso-ΣBipointedJoinBool-Bipointed C D T)))
--        λ f → codomainIsoDep λ a
--            → codomainIsoDep λ b
--            → codomainIso
--              (compIso (congIso {x = f a b} (Iso-ΣBipointedJoinBool-Bipointed C D T))
--                (pathToIso (cong (fun (Iso-ΣBipointedJoinBool-Bipointed C D T) (f a b) ≡_)
--                  (mainIs .snd)) ))))
--     (Iso-ΣBipointedJoinBool-Bipointed A B (C →∙ D →∙ T ∙ ∙))
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

--   mainIs :  (isoToPath (Iso-ΣBipointedJoinBool-Bipointed C D T) i0 , (λ c d → pt T) , λ _ _ _ → refl)
--           ≃∙ (C →∙ (D →∙ T ∙) ∙)
--   fst mainIs = isoToEquiv (Iso-ΣBipointedJoinBool-Bipointed C D T)
--   snd mainIs = cong (Iso.fun SmashAdjIso)
--        (ΣPathP ((funExt (
--          λ { (inl x) → refl
--             ; (inr x) → refl
--             ; (push (inl x) i) → refl
--             ; (push (inr x) i) → refl
--             ; (push (push a i₁) i) → refl})) , refl))
--             ∙ SmashAdj≃∙ .snd

-- ΣQuadpointTyBool : (n : Bool → Bool → ℕ)
--   → Iso (ΣQuadpointTy (RP∞'∙ ℓ-zero) (RP∞'∙ ℓ-zero) n)
--         (EM∙ ℤ/2 (n true true)
--      →∙ (EM∙ ℤ/2 (n true false)
--      →∙ EM∙ ℤ/2 (n false true)
--      →∙ EM∙ ℤ/2 (n false false)
--      →∙ EM∙ ℤ/2 ((n true true +' n true false)
--                +' (n false true +' n false false)) ∙ ∙ ∙))
-- ΣQuadpointTyBool n =
--    (compIso
--     (Σ-cong-iso
--      (invIso (compIso (invIso curryIso)
--      (compIso (invIso curryIso)
--      (compIso (invIso curryIso)
--      (domIso (invIso help))))))
--       λ f → invIso (compIso
--         (compIso (invIso curryIso)
--           (compIso (invIso curryIso)
--             (compIso (invIso curryIso)
--               (invIso
--                 (ΠIso idIso
--                   λ {(((x , y) , z) , w)
--                → domIso (compIso join-UnordJoinR-iso
--                    (Iso→joinIso
--                      join-UnordJoinR-iso
--                      join-UnordJoinR-iso))})))))
--           (ΠIso (invIso help) λ _ → idIso)))
--     (mainA (EM∙ ℤ/2 (n true true))
--            (EM∙ ℤ/2 (n true false))
--            (EM∙ ℤ/2 (n false true))
--            (EM∙ ℤ/2 (n false false))
--      (EM∙ ℤ/2 ((n true true +' n true false)
--            +' (n false true +' n false false)))))
--   where
--   help : Iso ((x y : fst (RP∞'∙ ℓ-zero)) → EM∙ ℤ/2 (n x y) .fst)
--              (((EM ℤ/2 (n true true)
--               × EM ℤ/2 (n true false))
--               × EM ℤ/2 (n false true))
--               × EM ℤ/2 (n false false))
--   help = compIso (compIso ΠBool×Iso
--                   (prodIso ΠBool×Iso ΠBool×Iso))
--                   (invIso Σ-assoc-Iso)

-- {-
-- ΣQuadpointTyPres : (n : Bool → Bool → ℕ)
--   (f : ΣQuadpointTy (RP∞'∙ ℓ-zero) (RP∞'∙ ℓ-zero) n)
--   → Path (EM ℤ/2 (n true true) →
--       (EM ℤ/2 (n true false) →
--        EM ℤ/2 (n false true) →
--        EM ℤ/2 (n false false) →
--        EM ℤ/2
--          ((n true true +' n true false)
--        +' (n false true +' n false false))))
--         (λ x y z w → Iso.fun (ΣQuadpointTyBool n) f .fst x .fst y .fst z .fst w)
--         λ x y z w → f .fst (CasesBool true
--                              (CasesBool true x y)
--                              (CasesBool true z w))
-- ΣQuadpointTyPres n f = refl
-- -}

-- isSetΣQuadPoint : (X Y : RP∞' ℓ-zero) (n : fst X → fst Y → ℕ)
--   → isSet (ΣQuadpointTy X Y n)
-- isSetΣQuadPoint =
--   RP∞'pt→Prop (λ Y → isPropΠ2 (λ _ _ → isPropIsSet))
--     (RP∞'pt→Prop (λ Y → isPropΠ (λ _ → isPropIsSet))
--       λ n → isOfHLevelRetractFromIso 2
--               (ΣQuadpointTyBool n)
--               (isConnected→∙ (suc (n true true)) 1
--                 (isConnectedEM (n true true))
--                 (isConnected→∙ (suc (n true false)) (n true true + 1)
--                   (isConnectedEM (n true false))
--                   (isConnected→∙ (suc (n false true))
--                     ((n true false) + (n true true + 1))
--                     (isConnectedEM (n false true))
--                     (isConnected→∙
--                       (suc (n false false))
--                       (n false true + (n true false + (n true true + 1)))
--                       (isConnectedEM (n false false))
--                       (subst (λ k → isOfHLevel (suc k) (EM ℤ/2 (N' n)))
--                         (lem n)
--                         (hLevelEM ℤ/2 (N' n))))))))
--   where
--   N' : (n : Bool → Bool → ℕ) → ℕ
--   N' n = ((n true true +' n true false) +' (n false true +' n false false))

--   lem : (n : _) → suc (N' n)
--                  ≡ (n false false + (n false true + (n true false + (n true true + 1))))
--   lem n =  cong suc ((cong₂ _+'_ (+'≡+ (n true true) (n true false))
--                                 (+'≡+ (n false true) (n false false))
--                  ∙ +'≡+ _ _)
--                  ∙ +-assoc (n true true + n true false ) (n false true) (n false false))
--          ∙ cong (_+ n false false)
--               (cong (_+ n false true)
--                 ((λ i → +-comm (+-comm 1 (n true true) i) (n true false) i))
--               ∙ +-comm _ (n false true))
--          ∙ +-comm _ (n false false)

-- ΣQuadPoint≡ : (X Y : RP∞' ℓ-zero) (n : fst X → fst Y → ℕ)
--   (f g : ΣQuadpointTy X Y n)
--   → ((t : _) → f .fst t ≡ g .fst t)
--   → f ≡ g
-- ΣQuadPoint≡ =
--   RP∞'pt→Prop (λ X → isPropΠ5 λ Y n _ _ _ → isSetΣQuadPoint X Y n _ _)
--     (RP∞'pt→Prop (λ Y → isPropΠ4 λ n _ _ _
--                        → isSetΣQuadPoint (RP∞'∙ ℓ-zero) Y n _ _)
--      λ n f g p
--    → sym (Iso.leftInv (ΣQuadpointTyBool n) f)
--    ∙∙ cong (inv (ΣQuadpointTyBool n))
--        (main n f g p)
--    ∙∙ Iso.leftInv (ΣQuadpointTyBool n) g)
--   where
--   module _ (n : Bool → Bool → ℕ)
--            (f g : ΣQuadpointTy (RP∞'∙ ℓ-zero) (RP∞'∙ ℓ-zero) n)
--          (p : (t : (x y : fst (RP∞'∙ ℓ-zero)) → EM ℤ/2 (n x y))
--         →  f .fst t ≡ g .fst t) where
--     p' : (x : _) (y : _) (z : _) (w : _)
--       → fun (ΣQuadpointTyBool n) f .fst x .fst y .fst z .fst w
--       ≡ fun (ΣQuadpointTyBool n) g .fst x .fst y .fst z .fst w
--     p' x y z w = p (CasesBool true
--                        (CasesBool true x y)
--                        (CasesBool true z w))

--     module _ {ℓ ℓ' ℓT} {C : Pointed ℓ} {D : Pointed ℓ'} {T : Pointed ℓT}
--               (hom : isHomogeneous T) where
--       isHomogeneous→∙₂ : isHomogeneous (C →∙ (D →∙ T ∙) ∙) 
--       isHomogeneous→∙₂ = isHomogeneous→∙ (isHomogeneous→∙ hom)

--       module _ {ℓ'' : Level} {B : Pointed ℓ''} where
--         isHomogeneous→∙₃ : isHomogeneous (B →∙ (C →∙ (D →∙ T ∙) ∙) ∙) 
--         isHomogeneous→∙₃ = isHomogeneous→∙ isHomogeneous→∙₂

--         isHomogeneous→∙₄ : ∀ {ℓ'''} {A : Pointed ℓ'''}
--           → isHomogeneous (A →∙ (B →∙ (C →∙ (D →∙ T ∙) ∙) ∙) ∙)
--         isHomogeneous→∙₄ = isHomogeneous→∙ isHomogeneous→∙₃

      

--     T = (n true true +' n true false) +' (n false true +' n false false)

--     m4 : (x : EM ℤ/2 (n true true)) (y : EM ℤ/2 (n true false))
--          (z : EM ℤ/2 (n false true))
--        → fun (ΣQuadpointTyBool n) f .fst x .fst y .fst z
--        ≡ fun (ΣQuadpointTyBool n) g .fst x .fst y .fst z
--     m4 x y z = →∙Homogeneous≡ (isHomogeneousEM T) (funExt (p' x y z))

--     m3 : (x : EM ℤ/2 (n true true)) (y : EM ℤ/2 (n true false))
--        → fun (ΣQuadpointTyBool n) f .fst x .fst y
--        ≡ fun (ΣQuadpointTyBool n) g .fst x .fst y
--     m3 x y = →∙Homogeneous≡ (isHomogeneous→∙ (isHomogeneousEM T))
--                (funExt (m4 x y))

--     m2 : (x : EM ℤ/2 (n true true))
--       → fun (ΣQuadpointTyBool n) f .fst x
--        ≡ fun (ΣQuadpointTyBool n) g .fst x
--     m2 x = →∙Homogeneous≡ (isHomogeneous→∙₂ (isHomogeneousEM T))
--              (funExt (m3 x))

--     main : fun (ΣQuadpointTyBool n) f ≡ fun (ΣQuadpointTyBool n) g
--     main = →∙Homogeneous≡ (isHomogeneous→∙₃ (isHomogeneousEM T))
--              (funExt m2)

-- SteenrodFun4≡SteenrodFun4comm : (X Y : RP∞' ℓ-zero) (n : fst X → fst Y → ℕ)
--   → SteenrodFun4 X Y n ≡ SteenrodFun4comm X Y n
-- SteenrodFun4≡SteenrodFun4comm =
--   RP∞'pt→Prop (λ _ → isPropΠ2 λ Y n → isSetΣQuadPoint _ Y n _ _)
--   (RP∞'pt→Prop (λ Y → isPropΠ λ n → isSetΣQuadPoint _ Y n _ _)
--     λ n → ΣQuadPoint≡ _ _ _ _ _
--       λ f → SteenrodFunBool (λ x → ∑RP∞' (RP∞'∙ ℓ-zero) (n x))
--                     (λ x → SteenrodFun (RP∞'∙ ℓ-zero) (n x) .fst (f x))
--            ∙ cong₂ ⌣ₖ₂ (SteenrodFunBool (n true) (f true))
--                       (SteenrodFunBool (n false) (f false))
--            ∙ help (EM ℤ/2) (λ n m x y → ⌣ₖ₂ {n = n} {m = m} x y)
--                ⌣ₖ-commℤ/2 assoc⌣ₖ
--                (n true true) (n true false)
--                (n false true) (n false false)
--                (f true true) (f true false)
--                (f false true) (f false false)
--                (∑RP∞'Fubini (RP∞'∙ ℓ-zero) (RP∞'∙ ℓ-zero) n)
--            ∙ cong (subst (EM ℤ/2) (∑RP∞'Fubini (RP∞'∙ ℓ-zero) (RP∞'∙ ℓ-zero) n))
--                (sym (SteenrodFunBool (λ z → ∑RP∞' (RP∞'∙ ℓ-zero) (λ x → n x z))
--                          (λ y → SteenrodFun (RP∞'∙ ℓ-zero) (λ x → n x y) .fst (λ x → f x y))
--                ∙ cong₂ ⌣ₖ₂ (SteenrodFunBool (λ x → n x true) (λ x → f x true))
--                                (SteenrodFunBool (λ x → n x false) (λ x → f x false)))))
--   where
--   help : ∀ {ℓ} (A : ℕ → Type ℓ) (compA : (n m : ℕ) (x : A n) (y : A m) → A (n +' m))
--     → (⌣comm : (n m : ℕ) (x : A n) (y : A m)
--       → compA n m x y
--        ≡ subst A (+'-comm m n) (compA m n y x))
--     → (⌣assoc : (n m l : ℕ) (x : A n) (y : A m) (z : A l)
--       → compA (n +' m) l (compA n m x y) z
--        ≡ subst A (+'-assoc n m l)
--            (compA n (m +' l) x (compA m l y z)))
--     → (n m k l : ℕ) (x : A n) (y : A m) (z : A k) (w : A l)
--     → (p : ((n +' k) +' (m +' l)) ≡ ((n +' m) +' (k +' l)))
--     → compA (n +' m) (k +' l) (compA n m x y) (compA k l z w)
--      ≡ subst A p (compA (n +' k) (m +' l) (compA n k x z) (compA m l y w))
--   help A compA ⌣comm ⌣assoc n m k l x y z w p =
--       (sym (transportRefl _)
--     ∙ (λ i → subst A (isSetℕ _ _ refl (((sym (+'-assoc n m (k +' l))) ∙ p5 ∙ p4) ∙ p) i)
--                (compA (n +' m) (k +' l) (compA n m x y) (compA k l z w))))
--     ∙ substComposite A ((sym (+'-assoc n m (k +' l)) ∙ p5 ∙ p4)) p _
--     ∙ cong (subst A p)
--         ((substComposite A (sym (+'-assoc n m (k +' l))) (p5 ∙ p4) _
--         ∙ cong (subst A (p5 ∙ p4))
--            (cong (subst A (sym (+'-assoc n m (k +' l))))
--                  (⌣assoc _ _ _ x y (compA k l z w))
--          ∙ subst⁻Subst A (+'-assoc n m (k +' l)) _))
--         ∙ substComposite A (cong (_+'_ n) ((p1 ∙ p2) ∙ p3)) p4
--            (compA n (m +' (k +' l)) x (compA m (k +' l) y (compA k l z w)))
--         ∙ cong (subst A (+'-assoc n k (m +' l)))
--           (sym (substLems _ _ ((p1 ∙ p2) ∙ p3) _ .snd
--                  x (compA m (k +' l) y (compA k l z w)))
--          ∙ cong (compA n (k +' (m +' l)) x)
--             (substComposite A (p1 ∙ p2) p3 (compA m (k +' l) y (compA k l z w))
--            ∙ cong (subst A p3)
--               ((substComposite A p1 p2 (compA m (k +' l) y (compA k l z w))
--               ∙ cong (subst A (cong (_+' l) (+'-comm m k)))
--                   (sym (⌣assoc m k l y z w)))
--               ∙ sym (substLems _ _ (+'-comm m k) _ .fst (compA m k y z) w)
--               ∙ cong (λ z → compA (k +' m) l z w)
--                  (sym (⌣comm k m z y)))
--             ∙ cong (subst A p3)
--               (⌣assoc _ _ _ z y w)
--            ∙ subst⁻Subst A (+'-assoc k m l) _))
--         ∙ sym (⌣assoc _ _ _ x z (compA m l y w)))
--     where
--     p1 = +'-assoc m k l
--     p2 = cong (_+' l) (+'-comm m k)
--     p3 = sym (+'-assoc k m l)
--     p4 = +'-assoc n k (m +' l)
--     p5 = cong (n +'_) ((p1 ∙ p2) ∙ p3)

--     substLems : (n n' : ℕ) (p : n ≡ n') (m : ℕ)
--       → ((x : A n) (y : A m)
--         → compA n' m (subst A p x) y ≡ subst A (cong (_+' m) p) (compA n m x y))
--        × ((x : A m) (y : A n)
--         → compA m n' x (subst A p y) ≡ subst A (cong (m +'_) p) (compA m n x y))
--     substLems n = J> λ m
--       → (λ x y → cong (λ x → compA n m x y) (transportRefl x)
--                  ∙ sym (transportRefl _))
--        , ((λ x y → cong (λ y → compA m n x y) (transportRefl y)
--                  ∙ sym (transportRefl _)))

-- SMasterLemma : (X Y : RP∞' ℓ-zero) (n : fst X → fst Y → ℕ)
--   → (f : (x : fst X) (y : fst Y) → EM ℤ/2 (n x y))
--   → S X (λ x → ∑RP∞' Y (n x)) (λ x → S Y (n x) (f x))
--    ≡ subst (EM ℤ/2) (∑RP∞'Fubini X Y n)
--        (S Y (λ y → ∑RP∞' X (λ x → n x y))
--          (λ y → S X (λ x → n x y) (λ x → f x y)))
-- SMasterLemma X Y n f i = SteenrodFun4≡SteenrodFun4comm X Y n i .fst f
