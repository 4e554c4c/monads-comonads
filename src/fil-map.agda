open import Categories.Category using (Category)
open import Categories.Category.Product using (_⁂_)
open import Categories.Functor using (Functor; Endofunctor; _∘F_) renaming (id to idF)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Level using (_⊔_)
open import Categories.Category.Monoidal using (Monoidal; MonoidalCategory)

module fil-map  {o ℓ e} (C : Category o ℓ e) (MC : Monoidal C) where
