{-# OPTIONS --safe #-}
module Cubical.HITs.SmashProduct.SmashTalk where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed hiding (⋆)
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



data _⋀_ {ℓ ℓ' : Level} (A : Pointed ℓ) (B : Pointed ℓ') : Type (ℓ-max ℓ ℓ') where
  ⋆ : A ⋀ B
  ⟨_,_⟩ : fst A → fst B → A ⋀ B
  pushₗ : (a : fst A) → ⟨ a , pt B ⟩ ≡ ⋆
  pushᵣ : (b : fst B)→ ⟨ pt A , b ⟩ ≡ ⋆
  pushₗᵣ : pushₗ (pt A) ≡ pushᵣ (pt B) 

_⋀∙_ : {ℓ ℓ' : Level} (A : Pointed ℓ) (B : Pointed ℓ') → Pointed (ℓ-max ℓ ℓ')
fst (A ⋀∙ B) = A ⋀ B
snd (A ⋀∙ B) = ⋆

private
  variable
    ℓ : Level
    A B C D : Pointed ℓ
    E : Type ℓ


module _ (f g : ((A ⋀∙ B) ⋀∙ C) ⋀ D  → E) where
  pf : (x : ((A ⋀∙ B) ⋀∙ C) ⋀ D)  → f x ≡ g x
  pf ⋆ = {!!}
  pf ⟨ ⋆ , d ⟩ = {!!}
  pf ⟨ ⟨ ⋆ , c ⟩ , d ⟩ = {!!}
  pf ⟨ ⟨ ⟨ a , b ⟩ , c ⟩ , d ⟩ = {!!}
  pf ⟨ ⟨ pushₗ a i , c ⟩ , d ⟩ = {!!}
  pf ⟨ ⟨ pushᵣ b i , c ⟩ , d ⟩ = {!!}
  pf ⟨ ⟨ pushₗᵣ i j , c ⟩ , d ⟩ = {!!}
  pf ⟨ pushₗ ⋆ i , d ⟩ = {!!}
  pf ⟨ pushₗ ⟨ a , b ⟩ i , d ⟩ = {!!}
  pf ⟨ pushₗ (pushₗ a j) i , d ⟩ = {!!}
  pf ⟨ pushₗ (pushᵣ b j) i , d ⟩ = {!!}
  pf ⟨ pushₗ (pushₗᵣ i j) k , d ⟩ = {!!}
  pf ⟨ pushᵣ c i , d ⟩ = {!!}
  pf ⟨ pushₗᵣ i j , d ⟩ = {!!}
  pf (pushₗ ⋆ i) = {!!}
  pf (pushₗ ⟨ ⋆ , c ⟩ i) = {!!}
  pf (pushₗ ⟨ ⟨ a , b ⟩ , c ⟩ i) = {!!}
  pf (pushₗ ⟨ pushₗ a j , c ⟩ i) = {!!}
  pf (pushₗ ⟨ pushᵣ b j , c ⟩ i) = {!!}
  pf (pushₗ ⟨ pushₗᵣ j k , c ⟩ i) = {!!}
  pf (pushₗ (pushₗ ⋆ i₁) i) = {!!}
  pf (pushₗ (pushₗ ⟨ a , b ⟩ j) i) = {!b!}
  pf (pushₗ (pushₗ (pushₗ a k) j) i) = {!!}
  pf (pushₗ (pushₗ (pushᵣ b k) j) i) = {!!}
  pf (pushₗ (pushₗ (pushₗᵣ l k) j) i) = {!!}
  pf (pushₗ (pushᵣ b j) i) = {!!}
  pf (pushₗ (pushₗᵣ k j) i) = {!!}
  pf (pushᵣ b i) = {!!}
  pf (pushₗᵣ i j) = {!!}
