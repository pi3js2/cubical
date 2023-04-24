module Cubical.ctalk where

open import Cubical.cprelude public
open import Cubical.Data.Nat renaming (_+_ to _+N_ ; _·_ to _·ℕ_)
open import Cubical.Data.Sigma
open import Cubical.Foundations.HLevels



infixl 10 _⁻

private
  variable
    ℓ ℓ' ℓ'' : Level
    A B : Type ℓ
    C : A → Type ℓ
    x y z w : A

-- Cubical Agda
-- Libraries: agda/cubical, 1lab

-- Part 1 (Paths)

-- No inductive identity type. Instead _≡_ is described using functions out of an interval I

-- Two endpoints points, i0 i1 : I.

-- (f : I → A) ~ (f i0 ≡ f i1)

refl : (x : A) → x ≡ x 
refl x = λ i → x

ap : {x y : A} (f : A → B) (p : x ≡ y) → f x ≡ f y
ap f p i = f (p i)
-- cong

funExt : {f g : (x : A) → C x} → ((x : A) → f x ≡ g x) → f ≡ g
-- have : A → (I → B),
-- want : I → (A → B)
funExt h i x = h x i

-- Interval manipulation
-- Minimum _∧_ : I → I → I
-- Maximum _∨_ : I → I → I
-- Symmetry/reversal ~_ : I → I

_⁻ : {x y : A} → x ≡ y → y ≡ x
(p ⁻) i = p (~ i)

isContr-singl : {A : Type} {x : A}
  → (p : Σ[ y ∈ A ] x ≡ y) → (x , refl x) ≡ p
fst (isContr-singl {x = x} (y , p) i) = p i
snd (isContr-singl {x = x} (y , p) i) j = p (i ∧ j)

-- Dependent paths
-- _≡_ is a special case of a dependent path type
-- Given A : I → Type and points (x₀ : A i0), (x₁ : A i1)
-- in

apd : {x y : A} (f : (x : A) → C x) (p : x ≡ y)
  → PathP (λ i → C (p i)) (f x) (f y)
apd f p i = f (p i)

-- Transport
-- Defined in terms of a primitive function transp taking:
-- A line of type (B : I → Type), a point in the interval (i : I) and a point in (B i0)
-- when i0, it's what we know as transport
transport : {A₀ A₁ : Type} (B : A₀ ≡ A₁) → A₀ → A₁
transport B b = transp (λ i → B i) i0 b

-- the interval variable 'specifies when transp is constant'
-- transp B i1 b := b whenever well-typed

transportRefl : {B : Type} (b : B) → transport (refl B) b ≡ b
transportRefl {B = B} b i = transp (λ i → B) i b

-- Higher inductive types

-- data ℤ' : Type where
--   pos : ℕ → ℤ'
--   neg : ℕ → ℤ'
--   0≡-0 : pos 0 ≡ neg 0

-- -_ : ℤ' → ℤ'
-- - pos x = neg x
-- - neg x = pos x
-- - 0≡-0 i = 0≡-0 (~ i)

-- comment out after


open import Cubical.Data.Int
open import Cubical.Data.Empty
open import Cubical.Data.Unit





-- Set quotients
data _/_ (A : Type) (R : A → A → Type) : Type where
  [_] : A → A / R
  eq/ : (x y : A) → R x y → [ x ] ≡ [ y ]
  trunc : isSet (A / R)

/elimSet : {A : Type} {R : A → A → Type}
  → {B : A / R → Type}
  → ((x : A / R) → isSet (B x))
  → ([_]' : (a : A) → B [ a ])
  → (eq/' : (x y : A) (r : R x y) → PathP (λ i → B (eq/ x y r i)) [ x ]' [ y ]')
  → (x : A / R) → B x
/elimSet is-set [_]' eq/' [ x ] = [ x ]'
/elimSet is-set [_]' eq/' (eq/ x y r i) = eq/' x y r i
/elimSet {B = B} is-set [_]' eq/' (trunc x y p q i j) =
  isSet→SquareP {A = λ i j → B (trunc x y p q i j)}
    (λ _ _ → is-set _)
    (λ j → /elimSet is-set [_]' eq/' (p j))
    (λ j → /elimSet is-set [_]' eq/' (q j))
    (λ _ → /elimSet is-set [_]' eq/' x)
    (λ _ → /elimSet is-set [_]' eq/' y) i j

/elimProp : {A : Type} {R : A → A → Type}
  → {B : A / R → Type}
  → ((x : A / R) → isProp (B x))
  → ([_]' : (a : A) → B [ a ])
  → (x : A / R) → B x
/elimProp {B = B} is-prop [_]' =
  /elimSet
    (λ x → isProp→isSet (is-prop x))
    [_]'
    λ _ _ _ → isProp→PathP (λ _ → is-prop _) _ _

-- Example ℚ

non-zero : ℕ → Type
non-zero zero = ⊥
non-zero (suc n) = Unit

ℕ₊ : Type
ℕ₊ = Σ ℕ non-zero

ℚ-rel : ℤ × ℕ₊ → ℤ × ℕ₊ → Type
ℚ-rel (a , b) (c , d) = a · pos (fst d) ≡ c · pos (fst b)

ℚ : Type
ℚ = (ℤ × ℕ₊) / ℚ-rel

-ℚ_ : ℚ → ℚ
-ℚ [ (a , n) ] = [ - a , n ]
-ℚ eq/ (a , n) (b , m) r i =
  eq/ (- a , n) ( - b , m)
    ((-DistL· a (pos (fst m)) ⁻) ∙ ap (-_) r ∙ -DistL· b (pos (fst n))) i
-ℚ trunc a b p q i j =
  trunc
    (-ℚ a) (-ℚ b)
    (λ i → -ℚ (p i)) (λ i → -ℚ (q i)) i j

_∙ℚ_ : ℚ → ℚ → ℚ
_∙ℚ_ = /elimSet (λ _ → isSetΠ λ _ → trunc)
  l
  λ { (x , suc n , p) (y , suc m , q) r
    → funExt (/elimProp (λ _ → trunc _ _)
        λ { (z , suc k , s)
          → eq/ _ _ (pf₂ x y z n m k r)})}
  where
  pf₁ : (x y t : ℤ) (k n m : ℕ) → x · pos (suc m) ≡ y · pos (suc n)
    → t · x · pos (suc (m +N k ·ℕ suc m))
    ≡ t · y · pos (suc (n +N k ·ℕ suc n))
  pf₁ x y t k n m r =
    ( (·Assoc t x _ ⁻)
               ∙ ap (t ·_)
                  (ap (x ·_) (ap pos (·-comm (suc k) (suc m))
                            ∙ pos·pos (suc m) (suc k))
                  ∙ ·Assoc x (pos (suc m)) (pos (suc k))
                  ∙ ap (_· pos (suc k)) r
                  ∙ (·Assoc y (pos (suc n)) (pos (suc k))⁻)
                  ∙ ap (y ·_) ((pos·pos (suc n) (suc k) ⁻)
                             ∙ ap pos (·-comm  (suc n) (suc k))))
               ∙ ·Assoc t y _)

  pf₂ : (x y z : ℤ) (n m k : ℕ)
    → x · pos (suc m) ≡ y · pos (suc n)
    → x · z · pos (suc (k +N m ·ℕ suc k))
     ≡ y · z · pos (suc (k +N n ·ℕ suc k))
  pf₂ x y z n m k r =
    ((ap (_· _) (·Comm x z) ∙ ap (z · x ·_)
                     (ap pos (·-comm (suc m) (suc k))))
                   ∙ pf₁ x y z k n m r
                   ∙ ap (z · y ·_) (ap pos (·-comm (suc k) (suc n)))
                   ∙ ap (_· _) (·Comm z y))
 
  main : ℤ × ℕ₊ → ℤ × ℕ₊ → ℤ × ℕ₊
  main (X , suc n , p) (Y , suc m , q) = X · Y , suc n ·ℕ suc m , tt

  l : ℤ × ℕ₊ → ℚ → ℚ
  l (t , suc k , s) =
    /elimSet (λ _ → trunc)
      (λ b → [ main (t , suc k , s) b ] )
      λ {(x , suc n , p) (y , suc m , q) r
      → eq/ _ _ (pf₁ x y t k n m r)}
