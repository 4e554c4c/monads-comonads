{-# OPTIONS --without-K --hidden-argument-puns --allow-unsolved-metas #-}
open import Level

open import Prelude
open import Categories.Diagram.End using (End)
open import Categories.Diagram.End.Properties -- using (EndF)

module test where

private
  variable
    o ℓ e : Level

module _ {C D E : Category o ℓ e}
    (F G : Functor E (Functors ((Category.op C) ×ᶜ C) D))
    (hF : ∀ X → End (Functor.F₀ F X))
    (hG : ∀ X → End (Functor.F₀ G X))
    (η : ∀ X → NaturalTransformation (Functor.F₀ F X) (Functor.F₀ G X))
    where
  private
    module C = Category C
    module D = Category D
    module E = Category E
    module NT = NaturalTransformation
  open D
  open HomReasoning

  open MR D
  open module F = Functor F using (F₀; F₁)
  open module G = Functor G using () renaming (F₀ to G₀; F₁ to G₁)
  open End hiding (E)
  open NT using (app; commute; sym-commute)

  foo : NaturalTransformation (EndF F hF) (EndF G hG)
  foo .app X = end-η (η X) {hF X} {hG X}
  foo .commute f = {! !}
  foo .sym-commute f = D.Equiv.sym $ foo .commute f

  


