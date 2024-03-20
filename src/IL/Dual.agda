{-# OPTIONS --without-K --allow-unsolved-metas #-}

open import Prelude

--open import Categories.Diagram.End using (End)
open import Categories.Diagram.End using () renaming (End to infixl 10 ∫_)
open import Categories.Diagram.End.Properties using (EndF; end-η)

module IL.Dual  {o ℓ e} {C : Category o ℓ e} {MC : Monoidal C} (CC : Closed MC)  where

open import IL (MC) renaming (id to idIL) --using (IL; FILM⟨_,_,_⟩; _⇒ᶠⁱˡ_; IL-monoidal; isFILM; _≃ᶠⁱˡ_)
open import fil (MC) using (FIL; isFIL; FIL[_,_,_])
open ∫_ renaming (E to end; factor to ∫factor)


-- a better way to state paramaterized ends (MacLane §V.7)
module _ where
  private 
    module C = Category C
    variable
      D E : Category o ℓ e
  _♯ : Functor ((C.op ×ᶜ C) ×ᶜ D) E → Functor (C.op ×ᶜ C) (Functors D E)
  _♯ = curry.₀

  infix 30 _♯

  end-η♯ : (F G : Functor ((C.op ×ᶜ C) ×ᶜ D) E)
           (η : NaturalTransformation F G)
           {ef : ∫ F ♯} {eg : ∫ G ♯} → NaturalTransformation (ef .end) (eg .end)
  end-η♯ _ _ η {ef} {eg} = end-η (curry.₁ η) {ef} {eg}

private
  module C = Category C
  module C² = Category (C ×ᶜ C)
  module IL = Category IL

--open Monoidal MC using (⊗; _⊗₀_; _⊗₁_; _⊗-; -⊗_)
open Closed CC renaming (adjoint to ⊗⊢[-,-])
module _ (G : Endofunctor C) where
  private
    module G = Functor G
    --               this one gets applied
    --                        ↓
    step1 : Functor (C.op ×ᶜ (C ×ᶜ C)) C
    step1 = [-,-] ∘F (G.op ⁂ ⊗)
    -- then swap
    step2 : Functor (C.op ×ᶜ (C ×ᶜ C)) C
    step2 = step1 ∘F (idF ⁂ Swap)

  -- and reassoc
  integrand : Functor ((C.op ×ᶜ C) ×ᶜ C) C
  integrand = step2 ∘F assocˡ C.op C C

  module integrand = Functor integrand

-- TODO determine end existance with typeclass search instead?
_˚ : (G : Endofunctor C) → {∫ integrand G ♯} → Endofunctor C
(G ˚) {e} = e .end

module _ (G : Endofunctor C) {e : ∫ integrand G ♯} where
  private
    G˚ : Endofunctor C
    G˚ = (G ˚) {e}

    module G = Functor G
    module G˚ = Functor G˚
    module e = ∫_ e
  open G using () renaming (F₀ to G₀; F₁ to G₁)
  --open FIL
  open NaturalTransformation using (app; commute; sym-commute)
  open Commutation C
  open import Categories.Category.Monoidal.Reasoning (MC)
  open Category C using (_∘_)

  dual-fil : FIL
  dual-fil .FIL.F = G˚
  dual-fil .FIL.G = G
  --dual-fil .FIL.Φ = {! !}
  dual-fil .FIL.Φ .app (X , Y) = -- ⟨ (e .end)₀ X ⊗₀ G₀ Y ⟩
    e.dinatural.α Y .app X ⊗₁ C.id ⇒⟨ integrand.₀ G ((Y , Y) , X) ⊗₀ G₀ Y ⟩
    ⊗⊢[-,-].counit .app (X ⊗₀ Y) --⇒⟨ X ⊗₀ Y ⟩
  dual-fil .FIL.Φ .commute {X , Y} {X' , Y'} (f , g) = begin
    (⊗⊢[-,-].counit .app (X' ⊗₀ Y') ∘ (e.dinatural.α Y' .app X' ⊗₁ C.id)) ∘ ( G˚.₁ f ⊗₁ G₁ g)
    --≈⟨ C.assoc ⟩
    --⊗⊢[-,-].counit .app (X' ⊗₀ Y') ∘ (e.dinatural.α Y' .app X' ⊗₁ C.id) ∘ ( G˚.₁ f ⊗₁ G₁ g)
    --≈⟨ ? ⟩ -- functorality
    --⊗⊢[-,-].counit .app (X' ⊗₀ Y') ∘ (Functor.F₁ (Functor.F₀ (integrand G ♯) ( Y'  , Y' )) f ⊗₁ G₁ g) ∘ (e.dinatural.α Y' .app X ⊗₁ C.id)
    ---- some sort of dinaturality?
    --⊗⊢[-,-].counit .app (X' ⊗₀ Y') ∘ (G₁ (( g  , C.id )) f ⊗₁ G₁ g) ∘ (e.dinatural.α Y' .app X ⊗₁ C.id)
    ≈⟨ ? ⟩
    (f ⊗₁ g) ∘ (⊗⊢[-,-].counit .app (X ⊗₀ Y) ∘ (e.dinatural.α Y .app X ⊗₁ C.id))
    ∎
  dual-fil .FIL.Φ .sym-commute f = C.Equiv.sym $ dual-fil .FIL.Φ .commute f
