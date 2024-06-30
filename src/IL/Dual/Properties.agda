{-# OPTIONS --without-K --allow-unsolved-metas #-}


open import Prelude

open import Categories.Diagram.End using () renaming (End to infixl 10 ∫_)
open import Categories.Diagram.End.Properties
open import Categories.Diagram.End.Parameterized renaming (EndF to ⨏)
open import Categories.Functor.Bifunctor
open import Categories.Category.Instance.Setoids
open import Categories.Diagram.End.Instances.NaturalTransformation
open import Categories.Diagram.End.Fubini
open import Categories.NaturalTransformation.Equivalence renaming (≃-setoid to NT-setoid)

open import Categories.Category.Construction.Presheaves

open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)

import Categories.Morphism as M
import Categories.Morphism.Reasoning as MR

open import Categories.Yoneda using (module Yoneda)

open import Categories.Category.Construction.Functors using (uncurry) renaming (product to functor-product)

module IL.Dual.Properties  {ℓ} {C : Category ℓ ℓ ℓ} {MC : Monoidal C} (CC : Closed MC)  where

{- Here we have a skeleton of a proof that [C][F,G°] ≅ [C²][F⊗G,⊗]
   Unfortunately, unification issues makes this really hard since typechecking is incredibly slow
   lossy unification does not work due to its inability to unify levels
   and some theorems (like preservation of limits in the presheaf category) are needed

   really this proof needs to be performed syntactically, using a logic for end calculus. See §6.3.2 in thesis.

open import IL (MC) renaming (id to idIL)
open import fil (MC) using (FIL; isFIL; FIL[_,_,_])
open ∫_ renaming (E to end; factor to ∫factor)

open Yoneda C renaming (embed to ょ)

open Closed CC renaming (adjoint to ⊗⊢[-,-])

open import IL.Dual CC

private
  module C = Category C
  module C² = Category (C ×ᶜ C)
  module IL = Category IL
  module ょ = Functor ょ

module _ (F G : Endofunctor C) {ω : ∀ X → ∫ (appˡ (integrand G) X)} where
  private
    G° : Endofunctor C
    G° = (G °) {ω}

    module F = Functor F
    module G = Functor G
    module G° = Functor G°
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
  -- the existence of the dual is, unsurprisingly, stronger than the
  -- existence of our end of NTs---which is guaranteed. So we have to
  -- start there and work backward

{- slow
  to-dual-end : ∫ (Hom[ C ][-,-] ∘F (F.op ⁂ G°))
  to-dual-end = NTs-are-End F G°

  -- by definition. takes forever to check for some reason
  dual-end' : ∫ (Hom[ C ][-,-] ∘F (F.op ⁂  ⨏ (integrand G) {ω}))
  dual-end' = to-dual-end

-}

  -- but to make things easier (so that we compose with *one* function) compose with `uncurry ∘ curry`

  -- first, lets define the direct image functor (on presheaves)
  --
  module _ where
    private
      variable
        o' ℓ' e' : Level
        A B E : Category o' ℓ' e'

    _* : Functor A B -> Functor (Presheaves′ o' ℓ' A) (Presheaves′ o' ℓ' B)
    _* = idF ∘F_

  _ : Functor C (Presheaves′ ℓ ℓ C)
  _ = (F.op *) ∘F ょ

  dual-end''-premotive : Functor C (Functors (Category.op C) (Setoids ℓ ℓ))
  dual-end''-premotive = (F.op * ∘F ょ ∘F ⨏ (integrand G) {ω})
  {-

  --dual-end' : ∫ (uncurry.₀ (curry₀ (Hom[ C ][-,-] ∘F (F.op ⁂  ⨏ (integrand G) {ω})))
  --dual-end' = ?

  -- but since Hom[ C ][_,-] is continuous
  ω' : ∀ X → ∫ appˡ (Hom[ C ][-,-] ∘F (F.op ∘F πˡ ∘F πʳ ※ integrand G ∘F (πʳ ∘F πʳ ※ πˡ))) X
  --ω' = Continuous-preserve-endf-motive {! !} {! Hom[ C ][-,-] !} {ω} {{! !}}

  open Functor-Swaps
  --iterated : ∫ ⨏ (Hom[ C ][-,-] ∘F (F.op ∘F πˡ ∘F πʳ ※ integrand G ∘F (πʳ ∘F πʳ ※ πˡ))) { ω' }
  --iterated = {! !}

  -- elaborating and simplifying projections yields
  iterated'-motive =(⨏ (Hom[ C ][-,-] ∘F (F.op ∘F πˡ ∘F πʳ
                                   ※ ([-,-] ∘F (G.op ∘F πˡ ∘F πˡ
                                              ※ ⊗ ∘F (πʳ ⁂  πʳ))))) { {! !} })

  -- by adjoint equivalence this is the same as
  iterated-adj-motive = ⨏ (Hom[ C ][-,-] ∘F (⊗.op ∘F (F.op ∘F πˡ ∘F πʳ ※ G.op ∘F πˡ ∘F πˡ)
                                       ※ ⊗ ∘F (πʳ ⁂  πʳ))) { {! !} }
  -- or
  iterated-adj'-motive = ∫ ⨏ ((Hom[ C ][-,-] ∘F (Functor.op (⊗ ∘F (F ⁂ G)) ⁂ ⊗)) ′) { {! !} }

  -- which by fubini is exactly the product end

  fils-end : ∫ (Hom[ C ][-,-] ∘F (Functor.op (⊗ ∘F (F ⁂ G)) ⁂ ⊗))
  fils-end = NTs-are-End (⊗ ∘F (F ⁂ G)) ⊗


  --dual-end' : ∫ (Hom[ C ][-,-] ∘F (F.op ⁂ ⨏ ([-,-] ∘F (G.op ∘F (πˡ ∘F πʳ) ※ ⊗ ∘F (πˡ ※ (πʳ ∘F πʳ)))) {ω}))
  --dual-end' = to-dual-end

  --_ : ∫ (Hom[ C ][-,-] ∘F (F.op ⁂ ⨏ ([-,-] ∘F (G.op ∘F (πˡ ∘F πʳ) ※ ⊗ ∘F (πˡ ※ (πʳ ∘F πʳ)))) {ω}))
  --dual-end' = to-dual-end

  goal : fils ≅ NT-setoid F G°
  goal = {! !}
  -}
  -}
