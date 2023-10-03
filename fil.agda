open import Categories.Category using (Category)
open import Categories.Category.Product using (_⁂_)
open import Categories.Functor using (Functor; Endofunctor; _∘F_) renaming (id to idF)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Level using (_⊔_)
open import Categories.Category.Monoidal using (Monoidal)

module fil  {o ℓ e} (C : Category o ℓ e) {MC : Monoidal C} where
open Monoidal MC

record functor-functor-interaction-law : Set (o ⊔ ℓ ⊔ e) where
  constructor FIL
  field
    F : Endofunctor C
    G : Endofunctor C
    ϕ : NaturalTransformation (⊗ ∘F (F ⁂ G)) ⊗
