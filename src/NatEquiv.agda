{-# OPTIONS --without-K #-}
open import Categories.Category using (Category)
open import Categories.Category.Product using (_⁂_; _⁂ⁿ_)
open import Categories.Functor using (Functor) renaming (id to idF)
import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation using (NaturalTransformation; _∘ʳ_; _∘ˡ_; _∘ᵥ_; _∘ₕ_) renaming (id to idN)
open import Categories.NaturalTransformation.Equivalence using (_≃_; ≃-isEquivalence)
open import Categories.Functor using (Endofunctor) renaming (id to idF)
open import Relation.Binary using (Rel; IsEquivalence; Setoid)

module NatEquiv {o ℓ e} {C D E : Category o ℓ e} {F G H : Functor C D} {K J M : Functor D E} where
private
  variable
    α β : NaturalTransformation F G
    δ γ : NaturalTransformation G H
    ε κ : NaturalTransformation K J
    τ : NaturalTransformation J M
  module D = Category D

≃-vert : δ ≃ γ → α ≃ β → δ ∘ᵥ α ≃ γ ∘ᵥ β
≃-vert e₁ e₂ = D.∘-resp-≈ e₁ e₂

≃-vertˡ : δ ≃ γ → δ ∘ᵥ α ≃ γ ∘ᵥ α
≃-vertˡ {δ = δ} {γ = γ} {α = α} e = ≃-vert {δ = δ} {γ = γ} {α = α} {β = α} e (refl {x = α})
  where open IsEquivalence ≃-isEquivalence


≃-vertʳ : α ≃ β → δ ∘ᵥ α ≃ δ ∘ᵥ β
≃-vertʳ {α = α} {β = β} {δ = δ} e = ≃-vert {δ = δ} {γ = δ} {α = α} {β = β} (refl {x = δ}) e
  where open IsEquivalence ≃-isEquivalence

≃-whiskerˡ : α ≃ β → K ∘ˡ α ≃ K ∘ˡ β
≃-whiskerˡ e = {! !}

≃-whiskerʳ : ε ≃ κ → ε ∘ʳ F ≃ κ ∘ʳ F
≃-whiskerʳ e = {! !}

-- ------
-- |    |
-- ε    β
-- |    |
-- κ    α
-- |    |
-- ------
≃-interchange : (τ ∘ᵥ κ) ∘ₕ (δ ∘ᵥ α) ≃ (τ ∘ₕ δ) ∘ᵥ (κ ∘ₕ α)
≃-interchange = {! !}

⁂ⁿ∘⁂ⁿ : ∀ {C₁ D₁ : Category o ℓ e} {F G H : Functor C C₁} {K J L : Functor D D₁}
          (α : NaturalTransformation G H) (β : NaturalTransformation J L)
          (δ : NaturalTransformation F G) (γ : NaturalTransformation K J) →
    (α ⁂ⁿ β) ∘ᵥ (δ ⁂ⁿ γ) ≃ (α ∘ᵥ δ) ⁂ⁿ (β ∘ᵥ γ)
⁂ⁿ∘⁂ⁿ  = {! !}

⁂ⁿid∘id⁂ⁿ : ∀ {C₁ D₁ : Category o ℓ e} {F G : Functor C C₁} {K J : Functor D D₁}
          (α : NaturalTransformation F G) (β : NaturalTransformation K J) →
    (α ⁂ⁿ idN) ∘ᵥ (idN ⁂ⁿ β) ≃ α ⁂ⁿ β
⁂ⁿid∘id⁂ⁿ  = {!⁂ⁿ∘⁂ⁿ α idN idN β  !}

id⁂ⁿ∘⁂ⁿid : ∀ {C₁ D₁ : Category o ℓ e} {F G H : Functor C C₁} {K J L : Functor D D₁}
          {α : NaturalTransformation F G} {β : NaturalTransformation K J} →
    (idN ⁂ⁿ α) ∘ᵥ (β ⁂ⁿ idN) ≃ β ⁂ⁿ α
id⁂ⁿ∘⁂ⁿid  = {! !}

⁂ⁿswap : ∀ {C₁ D₁ : Category o ℓ e} {F G H : Functor C C₁} {K J L : Functor D D₁}
          {α : NaturalTransformation F G} {β : NaturalTransformation K J} →
    (α ⁂ⁿ idN) ∘ᵥ (idN ⁂ⁿ β) ≃ (idN ⁂ⁿ β) ∘ᵥ (α ⁂ⁿ idN)
⁂ⁿswap  = {! !}
