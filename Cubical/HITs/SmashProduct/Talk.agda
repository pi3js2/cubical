{-# OPTIONS --safe #-}
module Cubical.HITs.SmashProduct.Talk where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.HITs.Pushout.Base
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.HITs.Wedge
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.Path
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport

private
  variable
    ℓ ℓ' : Level

data _⋀_ (A : Pointed ℓ) (B : Pointed ℓ') : Type (ℓ-max ℓ ℓ') where
  ⋆∧ : A ⋀ B
  ⟨_,_⟩ : typ A → typ B → A ⋀ B
  pushl : (a : typ A) → ⟨ a , pt B ⟩ ≡ ⋆∧
  pushr : (b : typ B) → ⟨ pt A , b ⟩ ≡ ⋆∧
  pushlr : pushl (pt A) ≡ pushr (pt B)

_⋀∙_ : Pointed ℓ → Pointed ℓ' → Pointed (ℓ-max ℓ ℓ')
A ⋀∙ B = (A ⋀ B) , ⋆∧


module _ {A B C D : Pointed₀} {E : Type}
  (f g : ((A ⋀∙ B) ⋀∙ C) ⋀ D → E)
  where
  pf : (x : _) → f x ≡ g x
  pf ⋆∧ = {!!}
  pf ⟨ x , x₁ ⟩ = {!!}
  pf (pushl ⋆∧ i) = {!!}
  pf (pushl ⟨ x , x₁ ⟩ i) = {!!}
  pf (pushl (pushl ⋆∧ i₁) i) = {!!}
  pf (pushl (pushl ⟨ x , x₁ ⟩ i₁) i) = {!!}
  pf (pushl (pushl (pushl a i) j) k) = {!!}
  pf (pushl (pushl (pushr b i₂) i₁) i) = {!!}
  pf (pushl (pushl (pushlr i₂ i₃) i₁) i) = {!!}
  pf (pushl (pushr b i₁) i) = {!!}
  pf (pushl (pushlr i₁ i₂) i) = {!!}
  pf (pushr b i) = {!!}
  pf (pushlr i i₁) = {!!}


















    -- proof : (x : (A ⋀∙ B) ⋀ C) → f x ≡ g x
    -- proof ⋆∧ = base-path
    -- proof ⟨ ⋆∧ , c ⟩ = easy-path c
    -- proof ⟨ ⟨ a , b ⟩ , c ⟩ = h a b c
    -- proof ⟨ pushl a i , c ⟩ j = complicated-proof₁ a c i j
    -- proof ⟨ pushr b i , c ⟩ j = complicated-proof₂ b c i j
    -- proof ⟨ pushlr i j , c ⟩ k = horrible-proof₁₂ c i j k --
    -- proof (pushl ⋆∧ j) i = easyish-proof i j
    -- proof (pushl ⟨ a , b ⟩ i) j = complicated-proof₃ a b i j
    -- proof (pushl (pushl a i) j) k = impossible₁ a i j k --
    -- proof (pushl (pushr b i) j) k = impossible₂ b i j k --
    -- proof (pushl (pushlr l i) j) k = {!!} --
    -- proof (pushr b i) = {!!}
    -- proof (pushlr i j) k = {!!}
