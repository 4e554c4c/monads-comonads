{-# OPTIONS --without-K --safe #-}
open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Product using (_⁂_)
open import Categories.Functor using (Endofunctor) renaming (_∘F_ to _∘_)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Level using (_⊔_)

module fil  {o ℓ e} {C : Category o ℓ e} (MC : Monoidal C) where

open Monoidal MC using (⊗)

record FIL : Set (o ⊔ ℓ ⊔ e) where
  --no-eta-equality
  constructor FIL[_,_,_]
  field
    F : Endofunctor C
    G : Endofunctor C
    Φ : NaturalTransformation (⊗ ∘ (F ⁂ G)) ⊗

  source = F
  dest = G
