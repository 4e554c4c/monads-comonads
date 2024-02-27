{-# OPTIONS --without-K --safe #-}

open import Level
open import Categories.Category
open import Categories.Comonad

module Categories.Comonad.Morphism {o ℓ e} {C D : Category o ℓ e} where

open import Categories.NaturalTransformation
open import Categories.Functor

open NaturalTransformation

-- comonad morphism in the sense of the nLab
-- between generic comonads s : a -> a & t : b -> b
record Comonad⇒ (S : Comonad C) (T : Comonad D) : Set (o ⊔ ℓ ⊔ e) where

  private
    module S = Comonad S
    module T = Comonad T

  open module D = Category D using (_∘_; _≈_)

  field
    X : Functor C D
    α : NaturalTransformation (T.F ∘F X) (X ∘F S.F)

  module X = Functor X
  module α = NaturalTransformation α

  field
    -- we want this but no definitional functionality means sadness
    -- counit-comp : (X ∘ˡ S.ε) ∘ᵥ α ≃ T.ε ∘ʳ X
    -- instead we cope
    counit-comp : ∀ {U} → X.₁ (S.ε.η U) ∘ α.η U ≈ T.ε.η (X.₀ U)
    -- likewise here we want
    -- comult-comp : (X ∘ˡ S.δ) ∘ α ≃ (α ∘ʳ S) ∘ (T ∘ˡ α) ∘ T.δ
    comult-comp : ∀ {U} → X.₁ (S.δ.η U) ∘ α.η U ≈ α.η (S.F.₀ U) ∘ T.F.₁ (α.η U) ∘ T.δ.η (X.₀ U)

-- comonad morphism in a different sense:
-- comonads are on the same category, X is the identity
record Comonad⇒-id (T S : Comonad C) : Set (o ⊔ ℓ ⊔ e) where

  private
    module T = Comonad T
    module S = Comonad S

  field
    α : NaturalTransformation T.F S.F

  module α = NaturalTransformation α

  open module C = Category C using (_∘_; _≈_)

  field
    counit-comp : ∀ {U} → S.ε.η U ∘ α.η U ≈ T.ε.η U
    comult-comp : ∀ {U} → S.δ.η U ∘ α.η U ≈ α.η (S.F.₀ U) ∘ T.F.₁ (α.η U) ∘ T.δ.η U


-- not sure if this definition makes sense?
record Comonad²⇒ {S : Comonad C} {T : Comonad D} (Γ Δ : Comonad⇒ S T) : Set (o ⊔ ℓ ⊔ e) where

  private
    module S = Comonad S
    module T = Comonad T
    module Γ = Comonad⇒ Γ
    module Δ = Comonad⇒ Δ

  field
    m : NaturalTransformation Γ.X Δ.X

  module m = NaturalTransformation m

  open module D = Category D using (_∘_; _≈_)

  field
    comm : ∀ {U} → Δ.α.η U ∘ T.F.₁ (m.η U) ≈ m.η (S.F.₀ U) ∘ Γ.α.η U
