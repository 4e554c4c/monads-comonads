{-# OPTIONS --without-K --lossy-unification #-}

open import Prelude

--open import Categories.Diagram.End using (End)
open import Categories.Diagram.End using () renaming (End to infixl 10 ∫_)
open import Categories.Diagram.End.Properties renaming (EndF to ⨏)
open import Categories.Functor.Bifunctor
open import Categories.Category.Instance.Setoids
open import Categories.Diagram.End.Instances.NaturalTransformation
--open import Categories.Diagram.End.Fubini
open import Categories.NaturalTransformation.Equivalence renaming (≃-setoid to NT-setoid)

open import Categories.Category.Construction.Presheaves

open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)

import Categories.Morphism as M
import Categories.Morphism.Reasoning as MR

open import Categories.Yoneda using (module Yoneda)

open import Categories.Category.Construction.Functors using () renaming (product to functor-product)

module IL.Dual  {ℓ} {C : Category ℓ ℓ ℓ} {MC : Monoidal C} (CC : Closed MC)  where

open import IL (MC) renaming (id to idIL) --using (IL; FILM⟨_,_,_⟩; _⇒ᶠⁱˡ_; IL-monoidal; isFILM; _≃ᶠⁱˡ_)
open import fil (MC) using (FIL; isFIL; FIL[_,_,_])
open ∫_ renaming (E to end; factor to ∫factor)

open Yoneda C renaming (embed to ょ)

private
  module C = Category C
  module C² = Category (C ×ᶜ C)
  module IL = Category IL
  module ょ = Functor ょ

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
