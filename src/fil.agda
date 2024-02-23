{-# OPTIONS --without-K --safe #-}
open import Prelude renaming (_∘F_ to _∘_)
module fil  {o ℓ e} {C : Category o ℓ e} (MC : Monoidal C) where

open Monoidal MC using (⊗)

isFIL : Endofunctor C → Endofunctor C → Set _
isFIL F G = NaturalTransformation (⊗ ∘ (F ⁂ G)) ⊗

record FIL : Set (o ⊔ ℓ ⊔ e) where
  --no-eta-equality
  constructor FIL[_,_,_]
  field
    F : Endofunctor C
    G : Endofunctor C
    Φ : isFIL F G

  source = F
  dest = G
