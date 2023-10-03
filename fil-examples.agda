open import Categories.Category using (Category)
open import Categories.Category.Product using (_⁂_)
open import Categories.Functor using (Functor; Endofunctor; _∘F_) renaming (id to idF)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Level using (_⊔_)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.CartesianClosed using (CartesianClosed)
open import Categories.Category.BinaryProducts using (BinaryProducts; module BinaryProducts)

open import Data.Product using (Σ; _,_)


open import fil using (functor-functor-interaction-law)


module fil-examples  {o ℓ e} (C : Category o ℓ e) (CC : CartesianClosed C) where


open Category C
open CartesianClosed CC

module cartesian = Cartesian cartesian

open BinaryProducts (cartesian.products) using (-×_; _×-)

-- f : (a x b) -> (c x d) 

example-1 : ∀ {A : Obj} → functor-functor-interaction-law C
example-1 {A} = record
  { F = A ⇨-
  ; G = -× A
  ; ϕ = ntHelper record
    { η = λ { (X , Y) → {! !} }
      ; commute = {! !}
    }
  }
