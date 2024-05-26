{-# OPTIONS --without-K #-}
open import Prelude hiding (_×_)

open import Categories.Category.Monoidal.BiClosed using (BiClosed)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

--open import Data.Product using (uncurry; uncurry′; Σ; _,_; _×_)
open import Level using (_⊔_)

open import Categories.Category.CartesianClosed
open import Categories.Category.Cartesian
open import Categories.Category.Cocartesian
open import Categories.Category.Cartesian.Monoidal

open import Categories.Object.Terminal
open import Categories.Object.Initial
open import Categories.Object.StrictInitial

open import Categories.Functor.Construction.Constant

open import Categories.Diagram.End using () renaming (End to infixl 10 ∫_)
open import Categories.Diagram.End.Properties renaming (EndF to ⨏)
open import Categories.Functor.Bifunctor
open import Categories.Diagram.End.Instances.NaturalTransformation

import Categories.NaturalTransformation.NaturalIsomorphism as NI
open NI renaming (_≃_ to _≃ⁱ_)


import Categories.Morphism as M
import Categories.Morphism.Reasoning as MR

open import Categories.Yoneda using (module Yoneda)

--open import IL (MC) renaming (id to idIL) --using (IL; FILM⟨_,_,_⟩; _⇒ᶠⁱˡ_; IL-monoidal; isFILM; _≃ᶠⁱˡ_)
--open import fil (MC) using (FIL; isFIL; FIL[_,_,_])
open ∫_ renaming (E to end; factor to ∫factor)

-- since we are assuming all coproducts (with the terminal object) and initiality, assume cocartesian
module IL.Dual.Examples  {ℓ} {C : Category ℓ ℓ ℓ} (CCC : CartesianClosed C) (cC : Cocartesian C) where

open M C --using (_≅_)

open import Categories.Category.CartesianClosed.Properties CCC

private
  module CCC = CartesianClosed CCC

open Category C
open CartesianClosed CCC --using (_^_; eval′; cartesian; -⇨-)
open Cartesian cartesian using (products; terminal)
open BinaryProducts products
open Terminal terminal using (⊤; !)

open Cocartesian cC

open CartesianMonoidal cartesian using (monoidal)
open CartesianMonoidalClosed C CCC using (closedMonoidal)

open import Categories.Object.Coproduct C

open Closed closedMonoidal using ([-,-])

open import IL.Dual closedMonoidal

-- First, we consider the constant functor
Δ⊤ : Endofunctor C
Δ⊤ = const ⊤
module Δ⊤ = Functor Δ⊤

private module _ {ω : ∀ X → ∫ (appˡ (integrand Δ⊤) X)} where
  private
    module ω (X : Obj) = ∫_ (ω X)
  Δ⊤° : Endofunctor C
  Δ⊤° = (Δ⊤ °) {ω}
  private
    module Δ⊤° = Functor Δ⊤°

  open Commutation C
  dual→any : ∀ {X} C → Δ⊤°.₀ X ⇒ C
  dual→any {X} C = ω.dinatural.α X C ⇒⟨ ⊤ ⇨ (X × C) ⟩
                   ⟨ id , ! ⟩        ⇒⟨ (⊤ ⇨ (X × C)) × ⊤ ⟩
                   eval′             ⇒⟨ X × C ⟩
                   π₂                --⇒ C

  -- in particular, since we have an initial object
  private
    module isStrictInitial = IsStrictInitial (initial→strict-initial ⊥-is-initial)
  Δ⊥ : Endofunctor C
  Δ⊥ = const ⊥

  open NaturalIsomorphism
  is-const-terminal : Δ⊥ ≃ⁱ Δ⊤°
  is-const-terminal = niHelper record
    { η = λ X → ¡
    ; η⁻¹ = λ X → dual→any ⊥
    ; commute = λ f → ¡-unique₂ _ _
    ; iso = λ X → ≅.sym (isStrictInitial.is-strict (dual→any ⊥)) ._≅_.iso
    }
  -- now, for any object A, we have our functor G_A
  private module _ {A : Obj} {ω' : ∀ X → ∫ (appˡ (integrand (-+ A)) X)} where
    G = -+ A
    G° = (G  °) {ω'}
    private
      module G = Functor G
      module G° = Functor G°
