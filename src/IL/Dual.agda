{-# OPTIONS --without-K --allow-unsolved-metas #-}

open import Prelude

open import Categories.Diagram.End using (End)
open import Categories.Diagram.End.Properties using (EndF)

module IL.Dual  {o ℓ e} {C : Category o ℓ e} {MC : Monoidal C} (CC : Closed MC) (G : Endofunctor C) where

open import IL (MC) renaming (id to idIL) --using (IL; FILM⟨_,_,_⟩; _⇒ᶠⁱˡ_; IL-monoidal; isFILM; _≃ᶠⁱˡ_)
open import fil (MC) using (FIL; isFIL; FIL[_,_,_])

private
  module C = Category C
  module C² = Category (C ×ᶜ C)
  module IL = Category IL
  module G = Functor G
  open G using () renaming (F₀ to G₀; F₁ to G₁)

open Monoidal MC using (⊗; _⊗₀_; _⊗₁_; _⊗-)
open Closed CC using ([-,-])

private
  --                                  this one gets applied
  --                                           ↓
  step1 : Functor (C.op ×ᶜ (C ×ᶜ C)) C
  step1 = [-,-] ∘F (idF ⁂ ⊗)


  -- first lets reassoc
  step2 : Functor ((C.op ×ᶜ C) ×ᶜ C) C
  step2 = step1 ∘F assocˡ C.op C C

  -- then swap
  step3 : Functor ((C ×ᶜ C.op) ×ᶜ C) C
  step3 = step2 ∘F (Swap ⁂ idF)

  -- then go back
  step4 : Functor (C ×ᶜ (C.op ×ᶜ C)) C
  step4 = step3 ∘F assocʳ C C.op C

  -- then we can curry
  motive : Functor C (Functors (C.op ×ᶜ C) C)
  motive = curry₀ step4

-- now we assume our end exists

module motive = Functor motive

module _ (end : ∀ X → End (motive.₀ X)) where
  G˚ : Endofunctor C
  G˚ = EndF motive end
