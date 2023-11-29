{-# OPTIONS --without-K --lossy-unification #-}
open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)

module IL.Monoidal  {o ℓ e} {C : Category o ℓ e} (MC : Monoidal C) where

import Categories.Morphism.Reasoning as MR
open Monoidal MC using (⊗)
open import Categories.Functor using (Endofunctor; _∘F_) renaming (id to idF)
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Categories.NaturalTransformation using (NaturalTransformation; _∘ʳ_; _∘ˡ_; _∘ᵥ_; _∘ₕ_; ntHelper) renaming (id to idN)
open import Categories.NaturalTransformation.Properties using (replaceˡ)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_ⓘᵥ_; _ⓘₕ_; _ⓘˡ_; _ⓘʳ_; associator; sym-associator) 
                                                                renaming (_≃_ to _≃ⁿ_; refl to reflⁿⁱ)
open import IL.Core (MC)
open import fil (MC) using (functor-functor-interaction-law; FIL)
open import Data.Product using (uncurry; uncurry′; Σ; _,_; _×_)
open import Categories.Category.Product using (_⁂_; _⁂ⁿ_) renaming (Product to ProductCat)

unit : functor-functor-interaction-law
unit = record
  { F = idF
  ; G = idF
  -- agda doesn't like `idN` here, so we eta-expand it
  ; ϕ = ntHelper record
    { η = λ { _ → C.id }
    ; commute = λ { _ → id-comm-sym } }}
  where open MR C

private
  module C² = Category (ProductCat C C)

-- unfortunately we don't have a definitional equality here, so we need to transport along a natural isomorphism
⊗₀-IL : functor-functor-interaction-law → functor-functor-interaction-law → functor-functor-interaction-law
⊗₀-IL L L' = FIL (F ∘F J) (G ∘F K) map
  where open functor-functor-interaction-law L
        open functor-functor-interaction-law L' renaming (ϕ to Ψ; F to J; G to K)
        map : NaturalTransformation (⊗ ∘F (F ∘F J ⁂ G ∘F K)) ⊗
        map = replaceˡ (Ψ ∘ᵥ ϕ ∘ʳ (J ⁂ K)) {! (reflⁿⁱ ⓘᵥ associator (J ⁂ K) (F ⁂ G) ⊗) !}
⊗-IL : Bifunctor IL IL IL
⊗-IL = record
  { F₀           = uncurry ⊗₀-IL
  ; F₁           = λ { (f , g) → {! !} }
  ; identity     = {! !}
  ; homomorphism = {! !}
  ; F-resp-≈     = {! !}
  }

monoidal : Monoidal IL
monoidal = record
  { ⊗                    = {! !}
  ; unit                 = unit
  ; unitorˡ              = {! !}
  ; unitorʳ              = {! !}
  ; associator           = {! !}
  ; unitorˡ-commute-from = {! !}
  ; unitorˡ-commute-to   = {! !}
  ; unitorʳ-commute-from = {! !}
  ; unitorʳ-commute-to   = {! !}
  ; assoc-commute-from   = {! !}
  ; assoc-commute-to     = {! !}
  ; triangle             = {! !}
  ; pentagon             = {! !}
  }
