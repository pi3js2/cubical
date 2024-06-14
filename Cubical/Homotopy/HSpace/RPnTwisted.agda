-- David Wärn's RPn-twisted H-space structure on n+1-loop spaces

-- WIP! :(

{-# OPTIONS --safe #-}
module Cubical.Homotopy.HSpace.RPnTwisted ℓ where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Reflection.StrictEquiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.HITs.Wedge
open import Cubical.HITs.Pushout
open import Cubical.Data.Unit.Base
open import Cubical.Data.Sigma
open import Cubical.Data.NatMinusOne.Base
open import Cubical.Homotopy.Loopspace

open import Cubical.HITs.RPn hiding ( RP∞ ; Bool* )
open import Cubical.Data.Bool as Bool hiding ( Bool* )
open import Cubical.Homotopy.HSpace.RPnTwisted.TwoElementTypes ℓ
open import Cubical.Homotopy.HSpace.RPnTwisted.HSpaceZoo ℓ
  -- negEquiv negNeg if＝ if＝-eta
  as HSpaceZoo
  hiding ( lemma1 ; lemma2 ; module H ) -- TODO

cancel : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) → sym p ∙∙ refl ∙∙ p ≡ refl
cancel {x = x} {y = y} p i j =
  hcomp (λ k → λ { (i = i1) → y
                 ; (j = i0) → p (i ∨ k)
                 ; (j = i1) → p (i ∨ k)
                 })
        (p i)

-- TODO this was backported from the future :(
⋁gen : ∀ {ℓ ℓ'} (A : Type ℓ) (B : A → Pointed ℓ') → Type (ℓ-max ℓ ℓ')
⋁gen A B = cofib {A = A} {B = Σ A λ a → fst (B a)}
                  (λ a → a , snd (B a))

⋁gen∙ : ∀ {ℓ ℓ'} (A : Type ℓ) (B : A → Pointed ℓ') → Pointed (ℓ-max ℓ ℓ')
⋁gen∙ A B = ⋁gen A B , inl tt

module _ (X : RP∞) {B : Pointed ℓ} where
  wedge-to-product : ⋁gen (typ X) (λ _ → B) → (typ X → typ B)
  wedge-to-product (inl tt) a = pt B
  wedge-to-product (inr (x , b)) x' = if＝ X (λ _ → typ B) x x' (pt B) b
  wedge-to-product (push x i) x' = funExt⁻ (if＝-eta X (λ _ → typ B) x (λ _ → pt B)) x' (~ i)

  wedge-to-product∙ : ⋁gen∙ (typ X) (λ _ → B) →∙ Πᵘ∙ (typ X) (λ _ → B)
  fst wedge-to-product∙ = wedge-to-product
  snd wedge-to-product∙ = refl

  wedge-codiag : ⋁gen (typ X) (λ _ → B) → typ B
  wedge-codiag (inl tt) = pt B
  wedge-codiag (inr (a , b)) = b
  wedge-codiag (push a i) = pt B

  wedge-codiag∙ : ⋁gen∙ (typ X) (λ _ → B) →∙ B
  fst wedge-codiag∙ = wedge-codiag
  snd wedge-codiag∙ = refl

record TwistedHSpace (X : RP∞) (B : Pointed ℓ) : Type ℓ where
  Wedge : Type ℓ
  Wedge = ⋁gen (typ X) (λ _ → B)

  Product : Type ℓ
  Product = typ X → typ B

  incl : Wedge → Product
  incl = wedge-to-product X

  codiag : Wedge → typ B
  codiag = wedge-codiag X

  field
    μ : Product → typ B
    μ-comm : μ ∘ incl ≡ codiag

record TwistedHSpace∙ (X : RP∞) (B : Pointed ℓ) : Type ℓ where
  Wedge : Type ℓ
  Wedge = ⋁gen (typ X) (λ _ → B)

  Wedge∙ : Pointed ℓ
  Wedge∙ = ⋁gen∙ (typ X) (λ _ → B)

  Product : Type ℓ
  Product = typ X → typ B

  Product∙ : Pointed ℓ
  Product∙ = Πᵘ∙ (typ X) (λ _ → B)

  incl∙ : Wedge∙ →∙ Product∙
  incl∙ = wedge-to-product∙ X

  codiag∙ : Wedge∙ →∙ B
  codiag∙ = wedge-codiag∙ X

  field
    μ : Product∙ →∙ B
    μ-comm : μ ∘∙ incl∙ ≡ codiag∙

module Step1 {X : RP∞} {B : Pointed ℓ} where
  Φ : TwistedHSpace X B → HSpace1 X B
  HSpace1.μ (Φ h) = TwistedHSpace.μ h
  HSpace1.μ∙ (Φ h) = funExt⁻ (TwistedHSpace.μ-comm h) (inl tt)
  HSpace1.μunit (Φ h) x b = funExt⁻ (TwistedHSpace.μ-comm h) (inr (x , b))
  HSpace1.μcoh (Φ h) x i = funExt⁻ (TwistedHSpace.μ-comm h) (push x (~ i))

  Ψ : HSpace1 X B → TwistedHSpace X B
  TwistedHSpace.μ (Ψ h) = HSpace1.μ h
  TwistedHSpace.μ-comm (Ψ h) j (inl tt) = HSpace1.μ∙ h j
  TwistedHSpace.μ-comm (Ψ h) j (inr (x , b)) = HSpace1.μunit h x b j
  TwistedHSpace.μ-comm (Ψ h) j (push x i) = HSpace1.μcoh h x (~ i) j

  ΦΨ : (h : HSpace1 X B) → Φ (Ψ h) ≡ h
  ΦΨ h = refl

  ΨΦ : (h : TwistedHSpace X B) → Ψ (Φ h) ≡ h
  TwistedHSpace.μ (ΨΦ h t) = TwistedHSpace.μ h
  TwistedHSpace.μ-comm (ΨΦ h t) j (inl tt) = TwistedHSpace.μ-comm h j (inl tt)
  TwistedHSpace.μ-comm (ΨΦ h t) j (inr (x , b)) = TwistedHSpace.μ-comm h j (inr (x , b))
  TwistedHSpace.μ-comm (ΨΦ h t) j (push x i) = TwistedHSpace.μ-comm h j (push x i)

  ΦEquiv : TwistedHSpace X B ≃ HSpace1 X B
  ΦEquiv = isoToEquiv (iso Φ Ψ ΦΨ ΨΦ)

-- this is like the remark about wedge extensions in banded types paper
module Step0 {X : RP∞} {B : Pointed ℓ} where
  unpoint : TwistedHSpace∙ X B → TwistedHSpace X B
  TwistedHSpace.μ (unpoint h) = fst (TwistedHSpace∙.μ h)
  TwistedHSpace.μ-comm (unpoint h) = congS fst (TwistedHSpace∙.μ-comm h)

  lemma1 : ∀ {ℓ} {A : Type ℓ} {x y : A}
    (p q : x ≡ y)
    → Square p refl q refl ≡ (p ≡ q)
  lemma1 {A = A} {y = y} p q =
    λ t → PathP (λ i → PathP (λ j → A) (q (~ t ∧ i)) y) (λ j → p j) (λ j → q (j ∨ ~ t))

  lemma2 : ∀ {ℓ} {A : Type ℓ} {x y : A}
    (p q : x ≡ y)
    → Square (refl ∙ p) refl q refl ≡ (p ≡ q)
  lemma2 {A = A} {y = y} p q =
    cong (λ p → Square p refl q refl) (sym (lUnit p)) ∙ lemma1 p q

  unpointEquiv =
    TwistedHSpace∙ X B
      ≃⟨ strictEquiv (λ { h → (TwistedHSpace∙.μ h , TwistedHSpace∙.μ-comm h) })
                     (λ { (μ , μ-comm) → record { μ = μ ; μ-comm = μ-comm } }) ⟩
    Σ (Πᵘ∙ (typ X) (λ _ → B) →∙ B) (λ μ → μ ∘∙ wedge-to-product∙ X ≡ wedge-codiag∙ X {B = B}) 
      ≃⟨ strictEquiv (λ { (μ , μ-comm) → (fst μ , congS fst μ-comm , snd μ , cong snd μ-comm) })
                     (λ { (μ , μ-comm , μ∙ , μ-comm∙) → ((μ , μ∙) , ΣPathP (μ-comm , μ-comm∙)) }) ⟩
    (Σ ((typ X → typ B) → typ B) λ μ →
     Σ (μ ∘ wedge-to-product X ≡ wedge-codiag X {B = B}) λ μ-comm →
     Σ (μ (λ _ → pt B) ≡ pt B) λ μ∙ →
     Square (refl ∙ μ∙) refl (λ i → μ-comm i (inl tt)) refl)
      ≃⟨ (Σ-cong-equiv-snd λ μ →
          Σ-cong-equiv-snd λ μ-comm →
          Σ-cong-equiv-snd λ μ∙ →
          compEquiv (pathToEquiv (lemma2 μ∙ (λ i → μ-comm i (inl tt))))
                    (strictEquiv sym sym)) ⟩
    (Σ ((typ X → typ B) → typ B) λ μ →
     Σ (μ ∘ wedge-to-product X ≡ wedge-codiag X {B = B}) λ μ-comm →
     Σ (μ (λ _ → pt B) ≡ pt B) λ μ∙ →
     (λ i → μ-comm i (inl tt)) ≡ μ∙)
      ≃⟨ (Σ-cong-equiv-snd λ μ →
          Σ-contractSnd λ μ-comm →
          isContrSingl (λ i → μ-comm i (inl tt))) ⟩
    (Σ ((typ X → typ B) → typ B) λ μ →
     μ ∘ wedge-to-product X ≡ wedge-codiag X {B = B})
      ≃⟨ strictEquiv (λ { (μ , μ-comm) → record { μ = μ ; μ-comm = μ-comm } })
                     (λ { h → (TwistedHSpace.μ h , TwistedHSpace.μ-comm h) }) ⟩
    TwistedHSpace X B
      ■

  isEquivUnpoint : isEquiv unpoint
  isEquivUnpoint = snd unpointEquiv

module Looping∙ {X : RP∞} {B : Pointed ℓ}
  (h : TwistedHSpace∙ X B)
  where

  Wedge ΩWedge WedgeΩ : Pointed _
  Wedge = ⋁gen∙ (typ X) (λ _ → B)
  ΩWedge = Ω (⋁gen∙ (typ X) (λ _ → B))
  WedgeΩ = ⋁gen∙ (typ X) (λ _ → Ω B)

  Product ΩProduct ProductΩ : Pointed _
  Product = Πᵘ∙ (typ X) (λ _ → B)
  ΩProduct = Ω (Πᵘ∙ (typ X) (λ _ → B))
  ProductΩ = Πᵘ∙ (typ X) (λ _ → Ω B)

  extra : WedgeΩ →∙ ΩWedge
  fst extra (inl tt) = refl
  fst extra (inr (x , p)) = push x ∙∙ cong (λ b → inr (x , b)) p ∙∙ sym (push x)
  fst extra (push x i) = cancel (sym (push x)) (~ i)
  snd extra = refl

  coextra : ProductΩ →∙ ΩProduct
  fst coextra = funExt
  snd coextra = refl

  coextra⁻ : ΩProduct →∙ ProductΩ
  fst coextra⁻ = funExt⁻
  snd coextra⁻ = refl

  ι : Wedge →∙ Product
  ι = wedge-to-product∙ X {B}

  ∇ : Wedge →∙ B
  ∇ = wedge-codiag∙ X {B}

  μ : Product →∙ B
  μ = TwistedHSpace∙.μ h

  μ-comm : μ ∘∙ ι ≡ ∇
  μ-comm = TwistedHSpace∙.μ-comm h

  Ωι : ΩWedge →∙ ΩProduct
  Ωι = Ω→ ι

  Ω∇ : ΩWedge →∙ Ω B
  Ω∇ = Ω→ ∇

  Ωμ : ΩProduct →∙ Ω B
  Ωμ = Ω→ μ

  Ωμ-comm : Ωμ ∘∙ Ωι ≡ Ω∇
  Ωμ-comm = Ωμ ∘∙ Ωι ≡⟨ sym (Ω→∘∙ μ ι) ⟩
            Ω→ (μ ∘∙ ι) ≡⟨ cong Ω→ μ-comm ⟩
            Ω∇ ∎

  Ωι' : WedgeΩ →∙ ProductΩ
  Ωι' = wedge-to-product∙ X {Ω B}

  Ω∇' : WedgeΩ →∙ Ω B
  Ω∇' = wedge-codiag∙ X {Ω B}

  lem₁ : coextra ∘∙ Ωι' ≡ Ωι ∘∙ extra
  lem₁ = {!!}

  lem₂ : Ω∇' ≡ Ω∇ ∘∙ extra
  lem₂ = {!!}

  Ωμ' : ProductΩ →∙ Ω B
  Ωμ' = Ωμ ∘∙ coextra

  Ωμ'-comm : Ωμ' ∘∙ Ωι' ≡ Ω∇'
  Ωμ'-comm =
    Ωμ' ∘∙ Ωι'             ≡⟨⟩
    (Ωμ ∘∙ coextra) ∘∙ Ωι' ≡⟨ ∘∙-assoc Ωμ coextra Ωι'    ⟩
    Ωμ ∘∙ (coextra ∘∙ Ωι') ≡⟨ cong (Ωμ ∘∙_) lem₁         ⟩
    Ωμ ∘∙ (Ωι ∘∙ extra)    ≡⟨ sym (∘∙-assoc Ωμ Ωι extra) ⟩
    (Ωμ ∘∙ Ωι) ∘∙ extra    ≡⟨ cong (_∘∙ extra) Ωμ-comm   ⟩
    Ω∇ ∘∙ extra            ≡⟨ sym lem₂                   ⟩
    Ω∇' ∎

  looping : TwistedHSpace∙ X (Ω B)
  TwistedHSpace∙.μ looping = Ωμ'
  TwistedHSpace∙.μ-comm looping = Ωμ'-comm

  _ : Path ((typ X → typ (Ω B)) → typ (Ω B))
           (HSpace1.μ (Step1.Φ (Step0.unpoint looping)))
           (fst (Ω→ (TwistedHSpace∙.μ h)) ∘ funExt)
  _ = refl

open Looping∙ using ( looping )

module _ {B : Pointed ℓ} where
  pathComp₁ : HSpace1 Bool* (Ω B)
  HSpace1.μ pathComp₁ = λ f → f false ∙ f true
  HSpace1.μ∙ pathComp₁ = cancel refl
  HSpace1.μunit pathComp₁ = Bool.elim (sym ∘ rUnit) (sym ∘ lUnit)
  HSpace1.μcoh pathComp₁ = Bool.elim refl refl

  pathComp₀ : TwistedHSpace Bool* (Ω B)
  pathComp₀ = Step1.Ψ pathComp₁

  pathComp∙ : TwistedHSpace∙ Bool* (Ω B)
  pathComp∙ = invEq Step0.unpointEquiv pathComp₀

-- TODO I can never find this in cubical...
equivInj : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂}
  (f : A ≃ B)
  → {x y : A} → equivFun f x ≡ equivFun f y → x ≡ y
equivInj f {x} {y} p = sym (retEq f x) ∙∙ cong (invEq f) p ∙∙ retEq f y

TODO : ∀ {B : Pointed ℓ}
  → isHomogeneous B
  → {h₁ h₂ : TwistedHSpace∙ Bool* B}
  → fst (TwistedHSpace∙.μ h₁) ≡ fst (TwistedHSpace∙.μ h₂)
  → h₁ ≡ h₂
TODO homogB p = equivInj Step0.unpointEquiv (equivInj Step1.ΦEquiv (HSpaceZoo.lemma2 _ _ homogB p))

-- Bool.elim is in the wrong order ;)
elimBool : ∀ {A : Bool → Type ℓ}
  → A false → A true
  → ∀ b → A b
elimBool f t false = f
elimBool f t true = t

recBool : ∀ {A : Type ℓ}
  → A → A → Bool → A
recBool {A = A} = elimBool

module KeyLemma {B : Pointed ℓ}
  (h : TwistedHSpace∙ Bool* B)
  where
  module H = TwistedHSpace∙ h
  module ΩH = TwistedHSpace∙ (looping h)

  magic : (p q : typ (Ω B))
    → Path (Path (Bool → typ B) (λ _ → pt B) (λ _ → pt B))
           (funExt (recBool p q))
           (funExt (recBool p refl) ∙ funExt (recBool refl q))
  magic p q i j false = rUnit p i j
  magic p q i j true = lUnit q i j

  lem₀ : (p : typ (Ω B)) → fst (Ω→ H.μ) (funExt (recBool p refl)) ≡ p
  lem₀ p = cong (fst (Ω→ H.μ) ∘ funExt) (funExt (elimBool refl refl)) ∙ funExt⁻ (congS fst ΩH.μ-comm) (inr (true , p))

  lem₁ : (q : typ (Ω B)) → fst (Ω→ H.μ) (funExt (recBool refl q)) ≡ q
  lem₁ q = cong (fst (Ω→ H.μ) ∘ funExt) (funExt (elimBool refl refl)) ∙ funExt⁻ (congS fst ΩH.μ-comm) (inr (false , q))

  enough : (p q : typ (Ω B)) → fst (Ω→ H.μ) (funExt (recBool p q)) ≡ (p ∙ q)
  enough p q =
    fst (Ω→ H.μ) (funExt (recBool p q)) ≡⟨ cong (fst (Ω→ H.μ)) (magic p q) ⟩
    fst (Ω→ H.μ) (funExt (recBool p refl) ∙ funExt (recBool refl q)) ≡⟨ Ω→pres∙ H.μ (funExt (recBool p refl)) (funExt (recBool refl q)) ⟩
    fst (Ω→ H.μ) (funExt (recBool p refl)) ∙ fst (Ω→ H.μ) (funExt (recBool refl q)) ≡⟨ cong₂ _∙_ (lem₀ p) (lem₁ q) ⟩
    p ∙ q ∎

  lemma : (f : Bool → typ (Ω B)) → fst (Ω→ H.μ) (funExt f) ≡ (f false ∙ f true)
  lemma f = need
    where
    p = f false
    q = f true

    f' = recBool p q

    f≡f' : f ≡ f'
    f≡f' = funExt (elimBool refl refl)

    have : fst (Ω→ H.μ) (funExt f') ≡ (p ∙ q)
    have = enough p q

    need : fst (Ω→ H.μ) (funExt f) ≡ (p ∙ q)
    need = cong (fst (Ω→ H.μ) ∘ funExt) f≡f' ∙ have

lemma : ∀ {B : Pointed ℓ}
  (h : TwistedHSpace∙ Bool* B)
  → looping h ≡ pathComp∙
lemma h = TODO (isHomogeneousPath _ _) (funExt (KeyLemma.lemma h))

-- d'oh, we are not compatible with RP and cov⁻¹ anymore, hmm

twisted : {B : Pointed ℓ} (n : ℕ₋₁) (x : RP n)
  → TwistedHSpace∙ {-(cov⁻¹ n x)-} {!!} ((Ω^ (1+ n)) B)
twisted n x = {!!}
