{-# OPTIONS --without-K --hidden-argument-puns --allow-unsolved-metas --lossy-unification #-}
open import Categories.Category using (Category)
open import Categories.Functor using (Functor) renaming (id to idF)
import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation using (NaturalTransformation; _∘ʳ_; _∘ˡ_; _∘ᵥ_; _∘ₕ_) renaming (id to idN)
open import Categories.NaturalTransformation.Equivalence using (_≃_; ≃-isEquivalence)
open import Categories.Functor using (Endofunctor) renaming (id to idF)
open import Relation.Binary using (Rel; IsEquivalence; Setoid)

open import Level using (_⊔_) renaming (suc to lsuc)

module test {o ℓ e}  where

{-
infix 4 _≃_
-- We use a one-constructor data type, instead of a type alias or record to avoid eta equality.
-- This avoids Agda eagerly expanding the definition of _≃_ as a function, and improves unification.
data _≃_ {C D : Category o ℓ e} {F G : Functor C D} : Rel (NaturalTransformation F G) (o ⊔ ℓ ⊔ e) where
  ≃-ext : (let open Category D) {α β : NaturalTransformation F G} →
          (∀ {x} → (NaturalTransformation.η α x) ≈ (NaturalTransformation.η β x)) →
          α ≃ β
-}

private
  variable
    C D : Category o ℓ e
    F G : Functor C D
    α β : NaturalTransformation F G
    δ γ : NaturalTransformation F G

{-
≃-isEquivalence : ∀ {F G : Functor C D} → IsEquivalence (_≃_ {F = F} {G = G})
≃-isEquivalence {D} = record
  { refl = ≃-ext refl
  ; sym   = λ { (≃-ext f) → ≃-ext (sym f) }
  ; trans = λ { (≃-ext f) (≃-ext g) → ≃-ext (trans f g) }
  }
  where open Category.Equiv D

∘ᵥ-resp-≃ : δ ≃ γ → α ≃ β → δ ∘ᵥ α ≃ γ ∘ᵥ β
∘ᵥ-resp-≃ {_} {(D)} (≃-ext f) (≃-ext g) = ≃-ext (∘-resp-≈ f g)
  where open Category D

∘ᵥ-resp-≃ˡ : δ ≃ γ → δ ∘ᵥ α ≃ γ ∘ᵥ α
∘ᵥ-resp-≃ˡ {α} e = ∘ᵥ-resp-≃ e (refl {x = α})
  where open IsEquivalence ≃-isEquivalence

∘ᵥ-resp-≃ʳ : α ≃ β → δ ∘ᵥ α ≃ δ ∘ᵥ β
∘ᵥ-resp-≃ʳ {δ} e = ∘ᵥ-resp-≃ (refl {x = δ}) e
  where open IsEquivalence ≃-isEquivalence
-}
∘ᵥ-resp-≃ : δ ≃ γ → α ≃ β → δ ∘ᵥ α ≃ γ ∘ᵥ β
∘ᵥ-resp-≃ {_} {(D)} e₁ e₂ = ∘-resp-≈ e₁ e₂
  where open Category D

∘ᵥ-resp-≃ˡ : ∀  {F G H : Functor C D} 
          {α : NaturalTransformation F G} {δ γ : NaturalTransformation G H} →
          δ ≃ γ → δ ∘ᵥ α ≃ γ ∘ᵥ α
∘ᵥ-resp-≃ˡ {C = C} {α} e = ∘ᵥ-resp-≃  e (refl {x = α})
  where open IsEquivalence ≃-isEquivalence
{-
∘ᵥ-resp-≃ʳ : α ≃ β → δ ∘ᵥ α ≃ δ ∘ᵥ β
∘ᵥ-resp-≃ʳ {δ} e = ∘ᵥ-resp-≃ (refl {x = δ}) e
  where open IsEquivalence ≃-isEquivalence
  -}
