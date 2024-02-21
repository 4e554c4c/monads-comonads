{-# OPTIONS --without-K --allow-unsolved-metas --lossy-unification #-}
open import Prelude
open import Categories.Category.Product renaming (Product to ProductCat)
open import Relation.Binary using (Rel; IsEquivalence; Setoid)
open import Categories.Category.Construction.Monoids using (Monoids)

module MCIL.Core  {o ℓ e} {C : Category o ℓ e} (MC : Monoidal C) where

open import IL MC

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

test : (o ⊔ ℓ ⊔ e ⊔ (o ⊔ ℓ ⊔ e)) ≡ (o ⊔ ℓ ⊔ e)
test = refl

MCIL : Category (o ⊔ ℓ ⊔ e ⊔ (o ⊔ ℓ ⊔ e) ⊔ (o ⊔ e)) (o ⊔ ℓ ⊔ e ⊔ (o ⊔ e)) (o ⊔ e)
MCIL = Monoids IL-monoidal
