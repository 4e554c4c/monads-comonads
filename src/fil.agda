{-# OPTIONS --without-K --safe #-}
open import Prelude
module fil  {o ℓ e} {C : Category o ℓ e} (MC : Monoidal C) where

open Monoidal MC using (⊗)

isFIL : Endofunctor C → Endofunctor C → Set (o ⊔ ℓ ⊔ e)
isFIL F G = NaturalTransformation (⊗ ∘F (F ⁂ G)) ⊗

record FIL : Set (o ⊔ ℓ ⊔ e) where
  constructor FIL[_,_,_]
  field
    F : Endofunctor C
    G : Endofunctor C
    ϕ : isFIL F G

  module F = Functor F
  module G = Functor G

  source = F
  dest = G

open Monoidal MC using (⊗; _⊗₁_; _⊗₀_)
open Category C

record isFIL' (F G : Endofunctor C) : Set (o ⊔ ℓ ⊔ e) where
  private
    module F = Functor F
    module G = Functor G
  field
    ϕ : ∀ X Y → (F.₀ X ⊗₀ G.₀ Y) ⇒ X ⊗₀ Y
    natural₁ : ∀ {X X' Y} → (f : X ⇒ X') →
              (f ⊗₁ id) ∘ ϕ X Y ≈ ϕ X' Y ∘ (F.₁ f ⊗₁ id)
    natural₂ : ∀ {X Y Y'} → (g : Y ⇒ Y') → 
              (id ⊗₁ g) ∘ ϕ X Y ≈ ϕ X Y' ∘ (id ⊗₁ G.₁ g)
