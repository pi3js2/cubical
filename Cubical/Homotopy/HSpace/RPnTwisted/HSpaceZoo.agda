{-# OPTIONS --safe #-}

-- Here we define a collection types of H-space structures twisted
-- over a 2-element type, and prove their equivalence.

-- Then we define an incoherent notion of "M-space" structure, and
-- prove that the type of H-space structures is a retract of it.

-- In the end this allows us to prove that two H-space structures are
-- equal as soon as their multiplications are equal as pointed
-- functions.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Equiv
open import Cubical.HITs.RPn.Base hiding ( RP∞ )

module Cubical.Homotopy.HSpace.RPnTwisted.HSpaceZoo ℓ
  -- -- TODO hmm, working around slow typechecking due to excessive
  -- -- unfolding (?)... opaque/unfolding can help but seems to introduce
  -- -- other problems
  -- (negEquiv : (X : 2-EltType₀) → typ X ≃ typ X)
  -- (negNeg : (X : 2-EltType₀) (x : typ X) → equivFun (negEquiv X) (equivFun (negEquiv X) x) ≡ x)
  -- (if＝ : ∀ {ℓ} (X : 2-EltType₀) (A : typ X → Type ℓ) (x x' : typ X)
  --   → A x
  --   → A (equivFun (negEquiv X) x)
  --   → A x')
  -- (if＝-eta : ∀ {ℓ} (X : 2-EltType₀) (A : typ X → Type ℓ) (x : typ X)
  --   (f : (x' : typ X) → A x')
  --   → (λ x' → if＝ X A x x' (f x) (f (equivFun (negEquiv X) x))) ≡ f)
  where

open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Functions.FunExtEquiv
open import Cubical.Reflection.StrictEquiv

open import Cubical.Data.Sigma

open import Cubical.Foundations.Pointed.Homogeneous

open import Cubical.Homotopy.HSpace.RPnTwisted.TwoElementTypes ℓ

-- private
--   neg : (X : 2-EltType₀) → typ X → typ X
--   neg X = fst (negEquiv X)

--   negIsEquiv : (X : 2-EltType₀) → isEquiv (neg X)
--   negIsEquiv X = snd (negEquiv X)



-- Some general lemmas

module _ where
  private
    variable
      ℓ' ℓ'' ℓ''' : Level
      A : Type ℓ'
      B : Type ℓ''
      -- B : A → Type ℓ
      x y z w : A

  -- backwards singletons

  singl' : (a : A) → Type _
  singl' {A = A} a = Σ A (λ x → x ≡ a)

  isContrSingl' : (a : A) → isContr (singl' a)
  fst (isContrSingl' a) = (a , refl)
  snd (isContrSingl' a) (x , p) i = (p (~ i) , λ j → p (~ i ∨ j))

  recenter : isContr A → A → isContr A
  recenter c a = (a , isContr→isProp c a)

  -- hmm, this seems silly
  silly-lemma' :
    {f g : A → B} {h : A → A}
    (c : idfun A ≡ h)
    (a : ∀ x → f x ≡ g x)
    (b : ∀ x → f (h x) ≡ g (h x))
    → (∀ x → b x ≡ a (h x))
      ≃ (∀ x → transport (λ i → f (c (~ i) x) ≡ g (c (~ i) x)) (b x) ≡ a x)
  silly-lemma' {f = f} {g = g} {h = h} =
    J (λ h c → (a : ∀ x → f x ≡ g x)
               (b : ∀ x → f (h x) ≡ g (h x))
               → (∀ x → b x ≡ a (h x))
                 ≃ (∀ x → transport (λ i → f (c (~ i) x) ≡ g (c (~ i) x)) (b x) ≡ a x))
      (λ a b → equivΠCod (λ x → compPathlEquiv (transportRefl (b x))))

  silly-lemma :
    {f g : A → B} {h : A → A}
    (a : (x : A) → f x ≡ g x)
    (b : (x : A) → f (h x) ≡ g (h x))
    (c : (x : A) → h x ≡ x)
    → ((x : A) → b x ≡ a (h x))
      ≃ ((x : A) → transport (λ i → f (c x i) ≡ g (c x i)) (b x) ≡ a x)
  silly-lemma = λ a b c → silly-lemma' (sym (funExt c)) a b

  isPropEquiv : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂}
    → A ≃ B
    → isProp A → isProp B
  isPropEquiv f = isPropRetract (invEq f) (equivFun f) (secEq f)

  isContrEquiv : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂}
    → A ≃ B
    → isContr A → isContr B
  isContrEquiv f = isContrRetract (invEq f) (equivFun f) (secEq f)

  silly-lemma2 : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂}
    {g : A → B} {h : A → A}
    → isEquiv h
    → isContr (Σ (A → B) (λ f → ((x : A) → f (h x) ≡ g x)))
  silly-lemma2 {g = g} {h = h} e =
    isContrEquiv
      (Σ-cong-equiv-snd λ f → compEquiv
                                (invEquiv funExtEquiv)
                                (equivΠ {B' = λ a → f (h a) ≡ g a} (invEquiv (h , e))
                                   (λ a → compPathlEquiv (cong f (secEq (h , e) a)))))
      (isContrSingl' (λ x → g (invEq (h , e) x)))

  silly-lemma3 : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁}
    {g : A → Type ℓ₂} {h : A → A}
    → isEquiv h
    → isContr (Σ (A → Type ℓ₂) (λ f → ((x : A) → f (h x) ≃ g x)))
  silly-lemma3 {g = g} {h = h} e =
    isContrEquiv
      (Σ-cong-equiv-snd λ f → equivΠCod λ x → univalence)
      (silly-lemma2 e)

  composeHasRetract : ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
    {f : B → C} {g : A → B}
    → hasRetract f → hasRetract g → hasRetract (f ∘ g)
  composeHasRetract {g = g} (f' , h) (g' , k) = (g' ∘ f' , λ a → congS g' (h (g a)) ∙ k a)

  isEquivHasRetract : ∀ {ℓ₁ ℓ₂}
    {A : Type ℓ₁} {B : Type ℓ₂}
    {f : A → B}
    → isEquiv f → hasRetract f
  isEquivHasRetract {f = f} e = (invIsEq e , retIsEq e)

  equivHasRetract : ∀ {ℓ₁ ℓ₂}
    {A : Type ℓ₁} {B : Type ℓ₂}
    (f : A ≃ B) → hasRetract (equivFun f)
  equivHasRetract f = isEquivHasRetract (snd f)

  retractInj : ∀ {ℓ₁ ℓ₂}
    {A : Type ℓ₁} {B : Type ℓ₂}
    {f : A → B}
    → hasRetract f
    → {x y : A} → f x ≡ f y → x ≡ y
  retractInj (g , h) {x = x} {y = y} p =
    sym (h x) ∙∙ congS g p ∙∙ h y



-- H-space zoo...

module _ {-{ℓ}-} where
  -- Bool cases for clarity, not used here
  {-
  record HSpace1 (B : Pointed ℓ) : Type ℓ where
    constructor HSp
    field
      μ : typ B → typ B → typ B
      μ∙ : μ (pt B) (pt B) ≡ pt B
      μunit₀ : (y : typ B) → μ (pt B) y ≡ y
      μunit₁ : (x : typ B) → μ x (pt B) ≡ x
      μcoh₀ : μunit₀ (pt B) ≡ μ∙
      μcoh₁ : μunit₁ (pt B) ≡ μ∙

  record HSpace2 (B : Pointed ℓ) : Type ℓ where
    constructor HSp
    field
      μ : typ B → typ B → typ B
      ∙₀ ∙₁ : typ B
      μ∙ : μ ∙₀ ∙₁ ≡ pt B
      μunit₀ : (y : typ B) → μ ∙₀ y ≡ y
      μunit₁ : (x : typ B) → μ x ∙₁ ≡ x

  record HSpace3 (B : Pointed ℓ) : Type (ℓ-suc ℓ) where
    constructor HSp
    field
      A₀ A₁ : Pointed ℓ
      μ : typ A₀ → typ A₁ → typ B
      μ∙ : μ (pt A₀) (pt A₁) ≡ pt B
      μunit₀ : isEquiv (λ (y : typ A₁) → μ (pt A₀) y)
      μunit₁ : isEquiv (λ (x : typ A₀) → μ x (pt A₁))

  record MSpace1 (B : Pointed ℓ) : Type (ℓ-suc ℓ) where
    constructor MSp
    field
      μ : typ B → typ B → typ B
      μ∙ : μ (pt B) (pt B) ≡ pt B
      μunit₀ : isEquiv (λ (y : typ B) → μ (pt B) y)
      μunit₁ : isEquiv (λ (x : typ B) → μ x (pt B))

  record MSpace2 (B : Pointed ℓ) : Type (ℓ-suc ℓ) where
    constructor MSp
    field
      A₀ A₁ : Pointed ℓ
      μ : typ A₀ → typ A₁ → typ B
      μ∙ : μ (pt A₀) (pt A₁) ≡ pt B
      μunit₀ : isEquiv (λ (y : typ A₁) → μ (pt A₀) y)
      μunit₁ : isEquiv (λ (x : typ A₀) → μ x (pt A₁))
      triv₀ : B ≡ A₀
      triv₁ : B ≡ A₁
  -}

  record HSpace1 (X : RP∞) (B : Pointed ℓ) : Type ℓ where
    constructor HSp
    field
      μ : (typ X → typ B) → typ B
      μ∙ : μ (λ _ → pt B) ≡ pt B
      μunit : (x : typ X) (a : typ B)
        → μ (λ x' → if＝ X (λ _ → typ B) x x' (pt B) a) ≡ a
      μcoh : (x : typ X)
        → PathP (λ i → μ (λ x' → if＝-eta X (λ _ → typ B) x (λ _ → pt B) i x') ≡ pt B)
                (μunit x (pt B))
                μ∙

  record HSpace2 (X : RP∞) (B : Pointed ℓ) : Type ℓ where
    constructor HSp
    field
      μ : (typ X → typ B) → typ B
      ∙ : typ X → typ B
      μ∙ : μ ∙ ≡ pt B
      μunit : (x : typ X) (a : typ B)
        → μ (λ x' → if＝ X (λ _ → typ B) x x' (∙ x) a) ≡ a

  record HSpace3 (X : RP∞) (B : Pointed ℓ) : Type (ℓ-suc ℓ) where
    constructor HSp
    field
      A : typ X → Pointed ℓ
      μ : ((x : typ X) → typ (A x)) → typ B
      μ∙ : μ (λ x → pt (A x)) ≡ pt B
      μunit : (x : typ X)
        → isEquiv (λ (y : typ (A (neg X x))) → μ (λ x' → if＝ X (λ x' → typ (A x')) x x' (pt (A x)) y))

  record MSpace1 (X : RP∞) (B : Pointed ℓ) : Type (ℓ-suc ℓ) where
    constructor MSp
    field
      μ : (typ X → typ B) → typ B
      μ∙ : μ (λ _ → pt B) ≡ pt B
      μunit : (x : typ X)
        → isEquiv (λ (a : typ B) → μ (λ x' → if＝ X (λ _ → typ B) x x' (pt B) a))

  record MSpace2 (X : RP∞) (B : Pointed ℓ) : Type (ℓ-suc ℓ) where
    constructor MSp
    field
      A : typ X → Pointed ℓ
      μ : ((x : typ X) → typ (A x)) → typ B
      μ∙ : μ (λ x → pt (A x)) ≡ pt B
      μunit : (x : typ X)
        → isEquiv (λ (y : typ (A (neg X x))) → μ (λ x' → if＝ X (λ x' → typ (A x')) x x' (pt (A x)) y))
      triv : (x : typ X) → B ≡ A x

  variable
    X : RP∞
    B : Pointed ℓ

  hEquiv12 : HSpace1 X B ≃ HSpace2 X B
  hEquiv12 {X = X} {B = B} =
    HSpace1 X B
      ≃⟨ strictEquiv (λ { (HSp μ μ∙ μunit μcoh) → (μ , μ∙ , μunit , μcoh) } )
                     (λ { (μ , μ∙ , μunit , μcoh) → (HSp μ μ∙ μunit μcoh) } ) ⟩
    (Σ ((typ X → typ B) → typ B) λ μ →
     Σ (μ (λ _ → pt B) ≡ pt B) λ μ∙ →
     Σ ((x : typ X) (a : typ B) → μ (λ x' → if＝ X (λ _ → typ B) x x' (pt B) a) ≡ a) λ μunit →
     (x : typ X) → PathP (λ i → μ (λ x' → if＝-eta X (λ _ → typ B) x (λ _ → pt B) i x') ≡ pt B)
                         (μunit x (pt B))
                         μ∙)
      ≃⟨ invEquiv (Σ-cong-equiv-snd (λ μ → compEquiv (invEquiv Σ-assoc-≃)
                                                     (Σ-contractFst (isContrSingl (λ _ → pt B))))) ⟩
    (Σ ((typ X → typ B) → typ B) λ μ →
     Σ (typ X → typ B) λ ∙ →
     Σ (Path (typ X → typ B) (λ _ → pt B) ∙) λ ∙triv →
     Σ (μ ∙ ≡ pt B) λ μ∙ →
     Σ ((x : typ X) (a : typ B) → μ (λ x' → if＝ X (λ _ → typ B) x x' (∙ x) a) ≡ a) λ μunit →
     (x : typ X) → PathP (λ i → μ (λ x' → if＝-eta X (λ _ → typ B) x (∙) i x') ≡ ∙triv (~ i) (neg X x))
                         (μunit x (∙ (neg X x)))
                         μ∙)
      ≃⟨ (Σ-cong-equiv-snd λ μ →
          Σ-cong-equiv-snd λ ∙ →
          Σ-cong-equiv-snd λ ∙triv →
          Σ-cong-equiv-snd λ μ∙ →
          Σ-cong-equiv-snd λ μunit →
          equivΠCod λ x → compEquiv (strictEquiv flipSquare flipSquare)
                                    (compEquiv (Square≃doubleComp _ _ _ _)
                                               (strictEquiv (congS sym) (congS sym)))) ⟩
    (Σ ((typ X → typ B) → typ B) λ μ →
     Σ (typ X → typ B) λ ∙ →
     Σ (Path (typ X → typ B) (λ _ → pt B) ∙) λ ∙triv →
     Σ (μ ∙ ≡ pt B) λ μ∙ →
     Σ ((x : typ X) (a : typ B) → μ (λ x' → if＝ X (λ _ → typ B) x x' (∙ x) a) ≡ a) λ μunit →
     (x : typ X) → (sym μ∙ ∙∙ sym (cong μ (if＝-eta X (λ _ → typ B) x (∙))) ∙∙ μunit x (∙ (neg X x))) ≡ funExt⁻ ∙triv (neg X x))
      ≃⟨ (Σ-cong-equiv-snd λ μ →
          Σ-cong-equiv-snd λ ∙ →
          Σ-cong-equiv-snd λ ∙triv →
          Σ-cong-equiv-snd λ μ∙ →
          Σ-cong-equiv-snd λ μunit →
          invEquiv (equivΠ (negEquiv X) λ _ → idEquiv _)) ⟩
    (Σ ((typ X → typ B) → typ B) λ μ →
     Σ (typ X → typ B) λ ∙ →
     Σ (Path (typ X → typ B) (λ _ → pt B) ∙) λ ∙triv →
     Σ (μ ∙ ≡ pt B) λ μ∙ →
     Σ ((x : typ X) (a : typ B) → μ (λ x' → if＝ X (λ _ → typ B) x x' (∙ x) a) ≡ a) λ μunit →
     (x : typ X) → (sym μ∙ ∙∙ sym (cong μ (if＝-eta X (λ _ → typ B) (neg X x) (∙))) ∙∙ μunit (neg X x) (∙ (neg X (neg X x))))
                   ≡ funExt⁻ ∙triv (neg X (neg X x)))
      ≃⟨ (Σ-cong-equiv-snd λ μ →
          Σ-cong-equiv-snd λ ∙ →
          Σ-cong-equiv-snd λ ∙triv →
          Σ-cong-equiv-snd λ μ∙ →
          Σ-cong-equiv-snd λ μunit →
          silly-lemma (funExt⁻ ∙triv) _ (negNeg X)) ⟩
    (Σ ((typ X → typ B) → typ B) λ μ →
     Σ (typ X → typ B) λ ∙ →
     Σ (Path (typ X → typ B) (λ _ → pt B) ∙) λ ∙triv →
     Σ (μ ∙ ≡ pt B) λ μ∙ →
     Σ ((x : typ X) (a : typ B) → μ (λ x' → if＝ X (λ _ → typ B) x x' (∙ x) a) ≡ a) λ μunit →
     (x : typ X) → transport (λ i → pt B ≡ ∙ (negNeg X x i)) (sym μ∙ ∙∙ sym (cong μ (if＝-eta X (λ _ → typ B) (neg X x) (∙))) ∙∙ μunit (neg X x) (∙ (neg X (neg X x))))
                   ≡ funExt⁻ ∙triv x)
      ≃⟨ (Σ-cong-equiv-snd λ μ →
          Σ-cong-equiv-snd λ ∙ →
          Σ-cong-equiv-snd λ ∙triv →
          Σ-cong-equiv-snd λ μ∙ →
          Σ-cong-equiv-snd λ μunit →
          strictEquiv (λ h i j x → h x i j) (λ h x i j → h i j x)) ⟩
    (Σ ((typ X → typ B) → typ B) λ μ →
     Σ (typ X → typ B) λ ∙ →
     Σ (Path (typ X → typ B) (λ _ → pt B) ∙) λ ∙triv →
     Σ (μ ∙ ≡ pt B) λ μ∙ →
     Σ ((x : typ X) (a : typ B) → μ (λ x' → if＝ X (λ _ → typ B) x x' (∙ x) a) ≡ a) λ μunit →
     funExt (λ x → transport (λ i → pt B ≡ ∙ (negNeg X x i)) (sym μ∙ ∙∙ sym (cong μ (if＝-eta X (λ _ → typ B) (neg X x) (∙))) ∙∙ μunit (neg X x) (∙ (neg X (neg X x)))))
       ≡ ∙triv)
      ≃⟨ strictEquiv (λ { (μ , (∙) , ∙triv , μ∙ , μunit , μcoh) → (μ , (∙) , μ∙ , μunit , ∙triv , μcoh) })
                     (λ { (μ , (∙) , μ∙ , μunit , ∙triv , μcoh) → (μ , (∙) , ∙triv , μ∙ , μunit , μcoh) }) ⟩
    (Σ ((typ X → typ B) → typ B) λ μ →
     Σ (typ X → typ B) λ ∙ →
     Σ (μ ∙ ≡ pt B) λ μ∙ →
     Σ ((x : typ X) (a : typ B) → μ (λ x' → if＝ X (λ _ → typ B) x x' (∙ x) a) ≡ a) λ μunit →
     Σ (Path (typ X → typ B) (λ _ → pt B) ∙) λ ∙triv →
     funExt (λ x → transport (λ i → pt B ≡ ∙ (negNeg X x i)) (sym μ∙ ∙∙ sym (cong μ (if＝-eta X (λ _ → typ B) (neg X x) (∙))) ∙∙ μunit (neg X x) (∙ (neg X (neg X x)))))
       ≡ ∙triv)
      ≃⟨ (Σ-cong-equiv-snd λ μ →
          Σ-cong-equiv-snd λ ∙ →
          Σ-cong-equiv-snd λ μ∙ →
          Σ-contractSnd λ μunit →
          isContrSingl _) ⟩
    (Σ ((typ X → typ B) → typ B) λ μ →
     Σ (typ X → typ B) λ ∙ →
     Σ (μ ∙ ≡ pt B) λ μ∙ →
     (x : typ X) (a : typ B) → μ (λ x' → if＝ X (λ _ → typ B) x x' (∙ x) a) ≡ a)
      ≃⟨ strictEquiv (λ { (μ , (∙) , μ∙ , μunit) → (HSp μ (∙) μ∙ μunit) } )
                     (λ { (HSp μ (∙) μ∙ μunit) → (μ , (∙) , μ∙ , μunit) } ) ⟩
    HSpace2 X B ■

  hEquiv23 : HSpace2 X B ≃ HSpace3 X B
  hEquiv23 {X = X} {B = B} =
    HSpace2 X B
      ≃⟨ strictEquiv (λ { (HSp μ (∙) μ∙ μunit) → (μ , (∙) , μ∙ , μunit) } )
                     (λ { (μ , (∙) , μ∙ , μunit) → (HSp μ (∙) μ∙ μunit) } ) ⟩
    (Σ ((typ X → typ B) → typ B) λ μ →
     Σ (typ X → typ B) λ ∙ →
     Σ (μ ∙ ≡ pt B) λ μ∙ →
     (x : typ X) (a : typ B) → μ (λ x' → if＝ X (λ _ → typ B) x x' (∙ x) a) ≡ a)
      ≃⟨ (Σ-cong-equiv-snd λ μ →
          Σ-cong-equiv-snd λ ∙ →
          Σ-cong-equiv-snd λ μ∙ →
          equivΠCod (λ x → strictEquiv (λ h i y → h y (~ i)) (λ h y i → h (~ i) y))) ⟩
    (Σ ((typ X → typ B) → typ B) λ μ →
     Σ (typ X → typ B) λ ∙ →
     Σ (μ ∙ ≡ pt B) λ μ∙ →
     (x : typ X) → idfun (typ B) ≡ (λ (y : typ B) → μ (λ x' → if＝ X (λ _ → fst B) x x' (∙ x) y)))
      ≃⟨ invEquiv (Σ-contractFst (recenter (silly-lemma3 (negIsEquiv X))
                                           ((λ _ → typ B) , (λ _ → idEquiv (typ B))))) ⟩
    (Σ (Σ (typ X → Type ℓ) λ A → ((x : typ X) → A (neg X x) ≃ typ B)) λ (A , μunit) →
     Σ (((x : typ X) → A x) → typ B) λ μ →
     Σ ((x : typ X) → A x) λ ∙ →
     Σ (μ ∙ ≡ pt B) λ μ∙ →
     (x : typ X) → fst (μunit x) ≡ (λ (y : A (neg X x)) → μ (λ x' → if＝ X A x x' (∙ x) y)))
      ≃⟨ strictEquiv (λ { ((A , μunit) , μ , (∙) , μ∙ , h) → ((λ x → A x , ∙ x) , μ , μ∙ , μunit , h) })
                     (λ { (A , μ , μ∙ , μunit , h) → ((typ ∘ A , μunit) , μ , pt ∘ A , μ∙ , h) })⟩
    (Σ (typ X → Pointed ℓ) λ A →
     Σ (((x : typ X) → typ (A x)) → typ B) λ μ →
     Σ (μ (λ x → pt (A x)) ≡ pt B) λ μ∙ →
     Σ ((x : typ X) → typ (A (neg X x)) ≃ typ B) λ μunit →
     (x : typ X) → fst (μunit x) ≡ (λ (y : typ (A (neg X x))) → μ (λ x' → if＝ X (λ x' → typ (A x')) x x' (pt (A x)) y)))
      ≃⟨ (Σ-cong-equiv-snd λ A →
          Σ-cong-equiv-snd λ μ →
          Σ-cong-equiv-snd λ μ∙ →
          compEquiv (invEquiv Σ-Π-≃)
                    (equivΠCod λ x → compEquiv Σ-assoc-swap-≃ (Σ-contractFst (isContrSingl' _)))) ⟩
    (Σ (typ X → Pointed ℓ) λ A →
     Σ (((x : typ X) → typ (A x)) → typ B) λ μ →
     Σ (μ (λ x → pt (A x)) ≡ pt B) λ μ∙ →
     (x : typ X) → isEquiv (λ (y : typ (A (neg X x))) → μ (λ x' → if＝ X (λ x' → typ (A x')) x x' (pt (A x)) y)))
      ≃⟨ strictEquiv (λ { (A , μ , μ∙ , μunit) → (HSp A μ μ∙ μunit) })
                     (λ { (HSp A μ μ∙ μunit) → (A , μ , μ∙ , μunit) }) ⟩
    HSpace3 X B ■

  mEquiv12 : MSpace1 X B ≃ MSpace2 X B
  mEquiv12 {X = X} {B = B} =
    MSpace1 X B
      ≃⟨ strictEquiv (λ { (MSp μ μ∙ μunit) → (μ , μ∙ , μunit) })
                     (λ { (μ , μ∙ , μunit) → (MSp μ μ∙ μunit) }) ⟩
    (Σ ((typ X → typ B) → typ B) λ μ →
     Σ (μ (λ _ → pt B) ≡ pt B) λ μ∙ →
     (x : typ X) → isEquiv (λ (a : typ B) → μ (λ x' → if＝ X (λ _ → typ B) x x' (pt B) a)))
      ≃⟨ invEquiv (Σ-contractFst (isContrSingl (λ _ → B))) ⟩
    (Σ (Σ (typ X → Pointed ℓ) (λ A → (λ _ → B) ≡ A)) λ (A , _) →
     Σ (((x : typ X) → typ (A x)) → typ B) λ μ →
     Σ (μ (λ x → pt (A x)) ≡ pt B) λ μ∙ →
     (x : typ X) → isEquiv (λ (y : typ (A (neg X x))) → μ (λ x' → if＝ X (λ x' → typ (A x')) x x' (pt (A x)) y)))
      ≃⟨ strictEquiv (λ { ((A , triv) , μ , μ∙ , μunit) → (A , μ , μ∙ , μunit , funExt⁻ triv) })
                     (λ { (A , μ , μ∙ , μunit , triv) → ((A , funExt triv) , μ , μ∙ , μunit) }) ⟩
    (Σ (typ X → Pointed ℓ) λ A →
     Σ (((x : typ X) → typ (A x)) → typ B) λ μ →
     Σ (μ (λ x → pt (A x)) ≡ pt B) λ μ∙ →
     Σ ((x : typ X) → isEquiv (λ (y : typ (A (neg X x))) → μ (λ x' → if＝ X (λ x' → typ (A x')) x x' (pt (A x)) y))) λ μunit →
     (x : typ X) → B ≡ A x)
      ≃⟨ strictEquiv (λ { (A , μ , μ∙ , μunit , triv) → (MSp A μ μ∙ μunit triv) })
                     (λ { (MSp A μ μ∙ μunit triv) → (A , μ , μ∙ , μunit , triv) }) ⟩
    MSpace2 X B ■

  r1 : MSpace2 X B → HSpace3 X B
  r1 (MSp A μ μ∙ μunit _) = HSp A μ μ∙ μunit

  module _ {X : RP∞} (h : HSpace3 X B) where
    open HSpace3 h
    triv1' : (x : typ X) → B ≡ A (neg X x)
    triv1' x =
      ua∙ (invEquiv (_ , μunit x))
          (sym (invEq (equivAdjointEquiv (_ , μunit x))
                      (cong μ (if＝-eta X (λ x → typ (A x)) x (λ x → pt (A x)))
                       ∙ μ∙)))

    triv1 : (x : typ X) → B ≡ A x
    triv1 x = triv1' (neg X x) ∙ cong (λ x → A x) (negNeg X x) 

  s1 : HSpace3 X B → MSpace2 X B
  s1 h@(HSp A μ μ∙ μunit) = MSp A μ μ∙ μunit (triv1 h)

  rs1 : (h : HSpace3 X B) → r1 (s1 h) ≡ h
  rs1 h = refl

  hmRetract : {X : RP∞} {B : Pointed ℓ} → hasRetract (s1 {X = X} {B = B})
  fst hmRetract = r1
  snd hmRetract = rs1

  lemma1 : Σ (HSpace1 X B → MSpace1 X B) hasRetract
  lemma1 = _ , composeHasRetract
                 (equivHasRetract (invEquiv mEquiv12))
                 (composeHasRetract
                    hmRetract
                    (equivHasRetract (compEquiv hEquiv12 hEquiv23)))

  -- TODO this is not as simple as we'd hope
  danger : HSpace1 X B → MSpace1 X B
  danger = fst lemma1

  module _ (h : HSpace1 X B) where
    module H = HSpace1 h
    module M = MSpace1 (danger h)

    lol : (f : typ X → typ B) (x : typ X)
      → transport refl (transport refl (transport refl (transport refl (transport refl (f (transport refl x))))))
        ≡ f x
    lol f x i = transp (λ _ → typ B) i (transp (λ _ → typ B) i (transp (λ _ → typ B) i (transp (λ _ → typ B) i (transp (λ _ → typ B) i (f (transp (λ _ → typ X) i x))))))

    show-μ : M.μ ≡ H.μ
    show-μ = funExt (λ f → transportRefl _ ∙ congS H.μ (funExt (lol f)))

    -- we won't need this for now because we will just apply Cavallo's
    -- trick
    {-
    show-μ∙ : PathP (λ i → show-μ i (λ _ → pt B) ≡ pt B) M.μ∙ H.μ∙
    show-μ∙ = {!!}
    -}

  module _ (m1 m2 : MSpace1 X B)
    where
    module M1 = MSpace1 m1
    module M2 = MSpace1 m2

    lemmaM :
      Path (Πᵘ∙ (typ X) (λ _ → B) →∙ B) (M1.μ , M1.μ∙) (M2.μ , M2.μ∙)
      → Path (MSpace1 X B) m1 m2
    MSpace1.μ (lemmaM h i) = fst (h i)
    MSpace1.μ∙ (lemmaM h i) = snd (h i)
    MSpace1.μunit (lemmaM h i) x =
      isProp→PathP
        (λ i → isPropIsEquiv (λ a → MSpace1.μ (lemmaM h i) (λ x' → if＝ X (λ _ → typ B) x x' (pt B) a)))
        (M1.μunit x) (M2.μunit x)
        i

  module _ (h1 h2 : HSpace1 X B)
    (homogB : isHomogeneous B)
    where

    module H1 = HSpace1 h1
    module H2 = HSpace1 h2

    lemma2 :
      Path ((typ X → typ B) → typ B) H1.μ H2.μ
      → Path (HSpace1 X B) h1 h2
    lemma2 p =
      retractInj
        (snd lemma1)
        (lemmaM _ _ (→∙Homogeneous≡ homogB (show-μ h1 ∙∙ p ∙∙ sym (show-μ h2))))
