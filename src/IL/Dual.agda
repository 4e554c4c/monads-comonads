{-# OPTIONS --without-K --allow-unsolved-metas --lossy-unification #-}

open import Prelude

--open import Categories.Diagram.End using (End)
open import Categories.Diagram.End using () renaming (End to infixl 10 ∫_)
open import Categories.Diagram.End.Properties renaming (EndF to ⨏)
open import Categories.Functor.Bifunctor
open import Categories.Category.Instance.Setoids
open import Categories.Diagram.End.Instances.NaturalTransformation
open import Categories.Diagram.End.Fubini
open import Categories.NaturalTransformation.Equivalence renaming (≃-setoid to NT-setoid)

open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)

import Categories.Morphism as M
import Categories.Morphism.Reasoning as MR

module IL.Dual  {ℓ} {C : Category ℓ ℓ ℓ} {MC : Monoidal C} (CC : Closed MC)  where

open import IL (MC) renaming (id to idIL) --using (IL; FILM⟨_,_,_⟩; _⇒ᶠⁱˡ_; IL-monoidal; isFILM; _≃ᶠⁱˡ_)
open import fil (MC) using (FIL; isFIL; FIL[_,_,_])
open ∫_ renaming (E to end; factor to ∫factor)


{-
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
-}

private
  module C = Category C
  module C² = Category (C ×ᶜ C)
  module IL = Category IL

--open Monoidal MC using (⊗; _⊗₀_; _⊗₁_; _⊗-; -⊗_)
open Closed CC renaming (adjoint to ⊗⊢[-,-])
module _ (G : Endofunctor C) where
  private
    module G = Functor G
  integrand : Functor (C ×ᶜ (C.op ×ᶜ C)) C
  -- integrand.₀ (X , (Y⁻ , Y)) = [ G₀ Y⁻ , X ⊗₀ Y ]₀
  integrand = [-,-] ∘F (G.op ∘F (πˡ ∘F πʳ) ※ ⊗ ∘F (πˡ ※ (πʳ ∘F πʳ)))

  module integrand = Functor integrand

-- TODO determine end existence with typeclass search instead?
_˚ : (G : Endofunctor C) → {ω : ∀ X → ∫ (appˡ (integrand G) X)} → Endofunctor C
(G ˚) {ω} = ⨏ (integrand G) {ω}

module _ (F G : Endofunctor C) {ω : ∀ X → ∫ (appˡ (integrand G) X)} where
  private
    G˚ : Endofunctor C
    G˚ = (G ˚) {ω}

    module F = Functor F
    module G = Functor G
    module G˚ = Functor G˚
    module ω (X : C.Obj) = ∫_ (ω X)
  open G using () renaming (F₀ to G₀; F₁ to G₁)

  open Category (Setoids ℓ ℓ)
  open M (Setoids ℓ ℓ)

  open import Relation.Binary.Bundles using (Setoid)

  fils : Setoid ℓ ℓ
  fils = NT-setoid (⊗ ∘F (F ⁂ G)) ⊗
  module fils = Setoid fils

  _ : fils.Carrier ≡ isFIL F G
  _ = ≡.refl
  open import Categories.Functor.Hom
  --postulate 
    --ω : ∀ ((c- , c) : Category.Obj C × Category.Obj C) → ∫ (appʳ (integrand G) (c- , c))
    --
  -- the existence of the dual is, unsurprisingly, stronger than the
  -- existcnce of our end of NTs, which is guaranteed. So we have to
  -- start there and work backward

  to-dual-end : ∫ (Hom[ C ][-,-] ∘F (F.op ⁂ G˚))
  to-dual-end = NTs-are-End F G˚

  -- by definition
  dual-end' : ∫ (Hom[ C ][-,-] ∘F (F.op ⁂  ⨏ (integrand G) {ω}))
  dual-end' = to-dual-end
  -- but since Hom[ C ][_,-] is continuous

  open Functor-Swaps
  iterated : ∫ ⨏ (Hom[ C ][-,-] ∘F (F.op ∘F πˡ ∘F πʳ ※ integrand G ∘F (πʳ ∘F πʳ ※ πˡ))) { ? }
  iterated = ?

  -- elaborating and simplifying projections yields
  iterated' : ∫ (⨏ (Hom[ C ][-,-] ∘F (F.op ∘F πˡ ∘F πʳ
                                   ※ ([-,-] ∘F (G.op ∘F πˡ ∘F πˡ
                                              ※ ⊗ ∘F (πʳ ⁂  πʳ))))) { ? })
  iterated' = ?

  -- by adjoint equivalence this is the same as
  iterated-adj : ∫ ⨏ (Hom[ C ][-,-] ∘F (⊗.op ∘F (F.op ∘F πˡ ∘F πʳ ※ G.op ∘F πˡ ∘F πˡ)
                                       ※ ⊗ ∘F (πʳ ⁂  πʳ))) { ? }
  iterated-adj = ?
  -- or
  iterated-adj' : ∫ ⨏ ((Hom[ C ][-,-] ∘F (Functor.op (⊗ ∘F (F ⁂ G)) ⁂ ⊗)) ′) { ? }
  iterated-adj' = ?

  -- which by fubini is exactly the product end

  fils-end : ∫ (Hom[ C ][-,-] ∘F (Functor.op (⊗ ∘F (F ⁂ G)) ⁂ ⊗))
  fils-end = NTs-are-End (⊗ ∘F (F ⁂ G)) ⊗


  --dual-end' : ∫ (Hom[ C ][-,-] ∘F (F.op ⁂ ⨏ ([-,-] ∘F (G.op ∘F (πˡ ∘F πʳ) ※ ⊗ ∘F (πˡ ※ (πʳ ∘F πʳ)))) {ω}))
  --dual-end' = to-dual-end

  --_ : ∫ (Hom[ C ][-,-] ∘F (F.op ⁂ ⨏ ([-,-] ∘F (G.op ∘F (πˡ ∘F πʳ) ※ ⊗ ∘F (πˡ ※ (πʳ ∘F πʳ)))) {ω}))
  --dual-end' = to-dual-end

  goal : fils ≅ NT-setoid F G˚
  goal = {! !}
