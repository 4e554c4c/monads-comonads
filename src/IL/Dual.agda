{-# OPTIONS --without-K --lossy-unification #-}

open import Prelude

open import Categories.Diagram.End using () renaming (End to infixl 10 ∫_)
open import Categories.Diagram.End.Properties
open import Categories.Diagram.End.Parameterized renaming (EndF to ⨏)
open import Categories.Functor.Bifunctor

module IL.Dual  {ℓ} {C : Category ℓ ℓ ℓ} {MC : Monoidal C} (CC : Closed MC)  where

private
  module C = Category C

--open Monoidal MC using (⊗; _⊗₀_; _⊗₁_; _⊗-; -⊗_)
open Closed CC renaming (adjoint to ⊗⊢[-,-])
module _ (G : Endofunctor C) where
  private
    module G = Functor G
  integrand : Functor (C ×ᶜ (C.op ×ᶜ C)) C
  integrand = [-,-] ∘F ((G.op ∘F (πˡ ∘F πʳ)) ※ (⊗ ∘F (πˡ ※ (πʳ ∘F πʳ))))

  module integrand = Functor integrand

-- TODO determine end existence with typeclass search instead?
_° : (G : Endofunctor C) → {ω : ∀ X → ∫ (appˡ (integrand G) X)} → Endofunctor C
(G °) {ω} = ⨏ (integrand G) {ω}

module _ {F G : Endofunctor C}
    {ωF : ∀ X → ∫ (appˡ (integrand F) X)}
    {ωG : ∀ X → ∫ (appˡ (integrand G) X)}
    (η : NaturalTransformation F G) where

  private
    module F = Functor F
    module G = Functor G
    F° = (F °) {ωF}
    G° = (G °) {ωG}
    module F° = Functor F°
    module G° = Functor G°
    module η = NaturalTransformation η

  η° : NaturalTransformation G° F°
  η° = end-η♯ ([-,-] ∘ˡ ((η.op ∘ʳ (πˡ ∘F πʳ)) ※ⁿ idN)) ⦃ EndF-is-End (integrand G) {ωG} ⦄ ⦃ EndF-is-End (integrand F) {ωF} ⦄
