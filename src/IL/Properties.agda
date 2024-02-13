{-# OPTIONS --without-K --lossy-unification --hidden-argument-puns --allow-unsolved-metas #-}
open import Categories.Category
open import Categories.Category.Monoidal using (Monoidal; monoidalHelper)
open import Categories.Category.Monoidal.Braided using (Braided)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Category.Product using (_⁂_; _⁂ⁿ_) renaming (Product to ProductCat)
open import Categories.NaturalTransformation using (NaturalTransformation; _∘ʳ_; _∘ˡ_; _∘ᵥ_; _∘ₕ_) renaming (id to idN)

module IL.Properties  {o ℓ e} {C : Category o ℓ e} (MC : Monoidal C) where

import Categories.Morphism.Reasoning as MR

open import IL.Core (MC) renaming (id to idIL) using (IL; F⟨_,_,_⟩; _⇒ᶠⁱˡ_)

open import fil (MC)

open Monoidal MC using (⊗)

stretch : ∀ {F' G'} → (L : FIL) → (let open FIL L using (F; G; Φ)) →
          (NaturalTransformation F' F) → (NaturalTransformation G' G) → FIL
stretch {F'} _ _ _ .FIL.F = F'
stretch {G'} _ _ _ .FIL.G = G'
stretch FIL[ _ , _ , Φ ] f g .FIL.Φ = Φ ∘ᵥ ⊗ ∘ˡ (f ⁂ⁿ g)


module Dual (BM : Braided MC) where


  open Braided BM using (module braiding)

  _ʳᵉᵛ : (L : FIL) → FIL
  (FIL[ _ , G , _ ] ʳᵉᵛ) .FIL.F = G
  (FIL[ F , _ , _ ] ʳᵉᵛ) .FIL.G = F
  (FIL[ F , G , Φ ] ʳᵉᵛ) .FIL.Φ = {!braiding.⇒  !} ∘ᵥ Φ ∘ᵥ {! !}
