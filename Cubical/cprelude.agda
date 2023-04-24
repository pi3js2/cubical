module Cubical.cprelude where

open import Cubical.Core.Primitives public
{-
infixr 30 _∙_
infixr 30 _∙₂_
infix  3 _∎
infixr 2 _≡⟨_⟩_ _≡⟨⟩_
infixr 2.5 _≡⟨_⟩≡⟨_⟩_
infixl 4 _≡$_ _≡$S_
-}

-- Basic theory about paths. These proofs should typically be
-- inlined. This module also makes equational reasoning work with
-- (non-dependent) paths.

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
    B : A → Type ℓ
    x y z w : A


isContr : Type ℓ → Type ℓ
isContr A = Σ[ x ∈ A ] (∀ y → x ≡ y)

isProp : Type ℓ → Type ℓ
isProp A = (x y : A) → x ≡ y

isSet : Type ℓ → Type ℓ
isSet A = (x y : A) → isProp (x ≡ y)

isGroupoid : Type ℓ → Type ℓ
isGroupoid A = ∀ a b → isSet (Path A a b)

isProp→isSet : isProp A → isSet A
isProp→isSet h a b p q j i =
  hcomp (λ k → λ { (i = i0) → h a a k
                 ; (i = i1) → h a b k
                 ; (j = i0) → h a (p i) k
                 ; (j = i1) → h a (q i) k }) a


open import Cubical.Foundations.Prelude using (_∙_ ; isSet' ; isSet→isSet' ; isProp→PathP) public
