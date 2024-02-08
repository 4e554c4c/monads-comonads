{-# OPTIONS --without-K --safe #-}
open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Product using (_⁂_)
open import Categories.Functor using (Endofunctor) renaming (_∘F_ to _∘_)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Level using (_⊔_)

module fil  {o ℓ e} {C : Category o ℓ e} (MC : Monoidal C) where

open Monoidal MC using (⊗)

record functor-functor-interaction-law : Set (o ⊔ ℓ ⊔ e) where
  no-eta-equality
  pattern
  constructor FIL
  field
    F : Endofunctor C
    G : Endofunctor C
    ϕ : NaturalTransformation (⊗ ∘ (F ⁂ G)) ⊗
