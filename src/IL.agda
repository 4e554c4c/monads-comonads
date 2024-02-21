{-# OPTIONS --without-K --safe #-}

open import Prelude

-- Definition of the category of functor-functor-interraction-laws
module IL {o ℓ e} {C : Category o ℓ e} (MC : Monoidal C) where

open import IL.Core MC public
open import IL.Monoidal MC using (IL-monoidal) public
