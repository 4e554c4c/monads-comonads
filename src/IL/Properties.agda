{-# OPTIONS --without-K --hidden-argument-puns --allow-unsolved-metas #-}
open import Categories.Category
open import Categories.Category.Monoidal using (Monoidal; monoidalHelper)
open import Categories.Category.Monoidal.Braided using (Braided)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Category.Product using (_⁂_; _⁂ⁿ_; Swap) renaming (Product to ProductCat)
open import Categories.NaturalTransformation using (NaturalTransformation; _∘ʳ_; _∘ˡ_; _∘ᵥ_; _∘ₕ_) renaming (id to idN)

open import Prelude

module IL.Properties  {o ℓ e} {C : Category o ℓ e} (MC : Monoidal C) where

import Categories.Morphism.Reasoning as MR

open import IL.Core (MC) renaming (id to idIL) using (IL; F⟨_,_,_⟩; _⇒ᶠⁱˡ_)

open import fil (MC)

private
  module C = Category C
  module IL = Category IL

open Monoidal MC using (⊗)

stretch : ∀ {F' G'} → (L : FIL) → (let open FIL L using (F; G; Φ)) →
          (NaturalTransformation F' F) → (NaturalTransformation G' G) → FIL
stretch {F'} _ _ _ .FIL.F = F'
stretch {G'} _ _ _ .FIL.G = G'
stretch FIL[ _ , _ , Φ ] f g .FIL.Φ = Φ ∘ᵥ ⊗ ∘ˡ (f ⁂ⁿ g)


module Symmetry (BM : Braided MC) where
  open import Categories.Functor.Bifunctor using (flip-bifunctor)

  module _ (H : Bifunctor C C C) (F : Functor C C) (G : Functor C C)  where
    open Functor H public

    open NaturalIsomorphism
    swap-prod : (flip-bifunctor H ∘F (F ⁂ G)) ≃ⁿ flip-bifunctor (H ∘F (G ⁂ F))
    -- not sure why this has to be eta expanded? probably bc of the '-sym' again...
    swap-prod = niHelper record
      { η = λ _ → C.id
      ; η⁻¹ = λ _ → C.id
      ; commute = λ f → id-comm-sym {f = _}
      ; iso = λ X → record
        { isoˡ = C.identity²
        ; isoʳ = C.identity² } }
      where open MR C

  flip-trans : {H G : Bifunctor C C C} → NaturalTransformation H G → NaturalTransformation (flip-bifunctor H) (flip-bifunctor G)
  flip-trans = _∘ʳ Swap

  open Braided BM using (module braiding)

  _ʳᵉᵛ : (L : FIL) → FIL
  (FIL[ _ , G , _ ] ʳᵉᵛ) .FIL.F = G
  (FIL[ F , _ , _ ] ʳᵉᵛ) .FIL.G = F
  (FIL[ F , G , Φ ] ʳᵉᵛ) .FIL.Φ = braiding.F⇐G
                                ∘ᵥ flip-trans Φ
                                ∘ᵥ NaturalIsomorphism.F⇒G (swap-prod ⊗ _ _)
                                ∘ᵥ braiding.F⇒G ∘ʳ (G ⁂ F)

  module _ where
    open _⇒ᶠⁱˡ_
    unit : ∀ {L} → L ⇒ᶠⁱˡ  L ʳᵉᵛ ʳᵉᵛ
    unit .f = idN
    unit .g = idN
    unit .isMap = {! !}

    counit : ∀ {L} → L ʳᵉᵛ ʳᵉᵛ ⇒ᶠⁱˡ  L
    counit .f = idN
    counit .g = idN
    counit .isMap = {! !}


  rev-map : ∀{L M} → (f : L ⇒ᶠⁱˡ M) → M ʳᵉᵛ ⇒ᶠⁱˡ  L ʳᵉᵛ
  rev-map F⟨ _ , g , _     ⟩ ._⇒ᶠⁱˡ_.f  = g
  rev-map F⟨ f , _ , _     ⟩ ._⇒ᶠⁱˡ_.g  = f
  rev-map F⟨ f , g , isMap ⟩ ._⇒ᶠⁱˡ_.isMap  = {! !}

  module _ where
    open Functor
    REV : Functor IL.op IL
    REV .F₀ = _ʳᵉᵛ
    REV .F₁ = rev-map
    REV .identity = C.Equiv.refl , C.Equiv.refl
    REV .homomorphism = C.Equiv.refl , C.Equiv.refl
    REV .F-resp-≈ (e₁ , e₂) = e₂ , e₁

  module _ where
    --open import Categories.Adjoint.Equivalence
    --open import Categories.Adjoint.TwoSided

    module REV = Functor REV

    --open ⊣Equivalence

    open import Categories.Category.Equivalence
    open StrongEquivalence
    open WeakInverse
    selfDual : StrongEquivalence IL IL.op
    selfDual .F = REV.op
    selfDual .G = REV
    selfDual .weak-inverse .F∘G≈id = niHelper record 
      { η = λ _ → unit
      ; η⁻¹ = λ _ → counit
      ; commute = {! !}
      ; iso = {! !}
      }
    selfDual .weak-inverse .G∘F≈id = {! !}
    --  { unit = {! !}
    --  ; counit = {! !}
    --  ; zig = {! !}
    --  }



