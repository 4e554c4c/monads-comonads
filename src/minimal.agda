{-# OPTIONS --without-K --allow-unsolved-metas #-}

open import Categories.Category
open import Categories.Category.Monoidal using (Monoidal)

import Categories.Morphism.Reasoning as MR
open import Categories.Category.Product using (_⁂_; _⁂ⁿ_)
open import Categories.Functor using (Functor) renaming (id to idF)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper) renaming (id to idN)

open import Data.Product using (Σ; _,_; _×_)

module minimal {o ℓ e} {C : Category o ℓ e} (MC : Monoidal C) where

open import fil (MC) using (functor-functor-interaction-law; FIL)

open Category C
open Monoidal MC using (⊗; _⊗₁_)

-- original version that works
unit₁ : functor-functor-interaction-law
unit₁ = record
  { F = idF
  ; G = idF
  -- agda doesn't like `idN` here, so we eta-expand it
  ; ϕ = ntHelper record
      { η = λ _ → id
      ; commute = λ f → id-comm-sym {f = _}
      }
  }
  where open MR C


-- 'solve' on the metavariable above'
unit₂ : functor-functor-interaction-law
unit₂ = record
  { F = idF
  ; G = idF
  ; ϕ = ntHelper record
      { η = λ _ → id
      ; commute = λ f → id-comm-sym {f = ⊗.F₁ (Functor.₁ (idF ⁂ idF) f)}
      }
  }
  where open MR C

-- here's a version i wrote myself that's fine
unit₃ : functor-functor-interaction-law
unit₃ = record
  { F = idF
  ; G = idF
  ; ϕ = ntHelper record
      { η = λ _ → id
      ; commute = λ (f , g) → id-comm-sym {f = f ⊗₁ g}
      }
  }
  where open MR C
