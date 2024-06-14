{-# OPTIONS --safe #-}

module Cubical.Homotopy.HSpace.RPnTwisted.TwoElementTypes ℓ where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.HITs.RPn
  using (
        -- Axel's stuff from silly_steen
        -- ; notRP∞ ; notRP∞Equiv ; CasesRP ; CasesRPβ ; JRP∞
        RP∞' ; RP∞'∙ ; module RP∞'-fields ; notNotRP∞'
        )

open RP∞'-fields

RP∞ = RP∞' ℓ

Bool* : RP∞
Bool* = RP∞'∙ ℓ

neg : (X : RP∞) → typ X → typ X
neg X = notRP∞' X

negNeg : (X : RP∞) (x : typ X) → neg X (neg X x) ≡ x
negNeg = notNotRP∞'

negIsEquiv : (X : RP∞) → isEquiv (neg X)
negIsEquiv X = isoToIsEquiv (iso (neg X) (neg X) (negNeg X) (negNeg X))

negEquiv : (X : RP∞) → typ X ≃ typ X
negEquiv X = (neg X , negIsEquiv X)

if＝ : (X : RP∞) (A : typ X → Type ℓ) (x x' : typ X)
  → A x
  → A (neg X x)
  → A x'
if＝ X A x x' y n = elimRP∞' X {B = A} x y n x'

if＝-beta-yes : (X : RP∞) (A : typ X → Type ℓ) (x : typ X)
  (y : A x) (n : A (neg X x))
  → if＝ X A x x y n ≡ y
if＝-beta-yes X A x y n = fst (elimRP∞'β X {B = A} x y n)

if＝-beta-no : (X : RP∞) (A : typ X → Type ℓ) (x : typ X)
  (y : A x) (n : A (neg X x))
  → if＝ X A x (neg X x) y n ≡ n
if＝-beta-no X A x y n = snd (elimRP∞'β X {B = A} x y n)

if＝-eta' : (X : RP∞) (A : typ X → Type ℓ)
  (f : (x' : typ X) → A x')
  (x x' : typ X)
  → if＝ X A x x' (f x) (f (neg X x)) ≡ f x'
if＝-eta' X A f x x' =
  if＝ X (λ x' → if＝ X A x x' (f x) (f (neg X x)) ≡ f x') x x'
    (if＝-beta-yes X A x (f x) (f (neg X x)))
    (if＝-beta-no X A x (f x) (f (neg X x)))

if＝-eta : (X : RP∞) (A : typ X → Type ℓ) (x : typ X)
  (f : (x' : typ X) → A x')
  → (λ x' → if＝ X A x x' (f x) (f (neg X x))) ≡ f
if＝-eta X A x f = funExt (if＝-eta' X A f x)
