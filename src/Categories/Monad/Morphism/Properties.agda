{-# OPTIONS --without-K --safe #-}

open import Level
open import Categories.Category
open import Categories.Monad
import Categories.Morphism.Reasoning as MR

module Categories.Monad.Morphism.Properties {o ℓ e} {C D : Category o ℓ e} where

open import Categories.Monad.Morphism {C = C} {D = D}

open import Categories.NaturalTransformation
open import Categories.Functor

open NaturalTransformation

module id {S R T : Monad C} where
  private
    module S = Monad S
    module T = Monad T
    module R = Monad R
  open Monad⇒-id hiding (module C)
  module C = Category C
  open C using(_∘_; _≈_)
  open MR C
  open C.HomReasoning
  open Monad
  Monad⇒-id-∘ : (Monad⇒-id S T) → (Monad⇒-id T R) → (Monad⇒-id S R)
  Monad⇒-id-∘ τ σ .α = τ .α ∘ᵥ σ .α
  Monad⇒-id-∘ τ σ .unit-comp {x} = begin
      (τ .α .η x ∘  σ .α .η x) ∘ R .η .η x
      ≈⟨ C.assoc ⟩
      τ .α .η x ∘  (σ .α .η x ∘ R .η .η x)
      ≈⟨ refl⟩∘⟨ σ .unit-comp ⟩
      τ .α .η x ∘ T .η .η x
      ≈⟨ τ .unit-comp ⟩
      S .η .η x
      ∎
  Monad⇒-id-∘ τ σ .mult-comp {x} = begin
      (τ .α .η x ∘ σ .α .η x) ∘ R.μ.η x
      ≈⟨ C.assoc ⟩
      τ .α .η x ∘ (σ .α .η x ∘ R.μ.η x)
      ≈⟨ refl⟩∘⟨ σ .mult-comp ⟩
      τ .α .η x ∘ (T.μ.η x ∘ σ .α .η (T.F.₀ x) ∘ R.F.₁ (σ .α .η x))
      ≈⟨ ? ⟩
      (τ .α .η x ∘ T.μ.η x) ∘ σ .α .η (T.F.₀ x) ∘ R.F.₁ (σ .α .η x)
      ≈⟨ ? ⟩
      (S.μ.η x ∘ τ .α .η (S.F.₀ x) ∘ T.F.₁ (τ .α .η x)) ∘ σ .α .η (T.F.₀ x) ∘ R.F.₁ (σ .α .η x)
      ≈⟨ ? ⟩
      (S.μ.η x ∘ τ .α .η (S.F.₀ x)) ∘ σ .α .η (S.F.₀ x) ∘ R.F.₁ (τ .α .η x) ∘ R.F.₁ (σ .α .η x)
      ≈⟨ ? ⟩
      S.μ.η x ∘ (τ .α .η (S.F.₀ x) ∘ σ .α .η (S.F.₀ x)) ∘ R.F.₁ (τ .α .η x ∘ σ .α .η x)
      ∎
