{-# OPTIONS --without-K --safe #-}
open import Prelude hiding (_×_)

open import Level using (_⊔_)

open import Categories.Category.Cartesian
open import Categories.Category.Cartesian.Monoidal
open import Categories.Category.CartesianClosed
open import Categories.Category.Cocartesian
open import Categories.Category.Monoidal.BiClosed using (BiClosed)
open import Categories.Diagram.End using () renaming (End to infixl 10 ∫_)
open import Categories.Diagram.End.Parameterized renaming (EndF to ⨏)
open import Categories.Diagram.End.Properties
open import Categories.Functor.Bifunctor
open import Categories.Functor.Construction.Constant
open import Categories.Object.Initial
open import Categories.Object.StrictInitial
open import Categories.Object.Terminal

import Categories.NaturalTransformation.NaturalIsomorphism as NI
import Categories.Morphism as M

open NI renaming (_≃_ to _≃ⁱ_)

-- since we are assuming all coproducts (with the terminal object) and initiality, assume cocartesian
module IL.Dual.Examples  {ℓ} {C : Category ℓ ℓ ℓ} (CCC : CartesianClosed C) (cC : Cocartesian C) where

open M C

open import Categories.Category.CartesianClosed.Properties CCC

private
  module CCC = CartesianClosed CCC

open module C = Category C
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

  G : Endofunctor C
  G = -+ ⊤
  -- now, for any object A, we have our functor G_A
  private module _ {ω' : ∀ X → ∫ (appˡ (integrand G) X)} where
    G° : Endofunctor C
    G° = (G  °) {ω'}
    private
      module G = Functor G
      module G° = Functor G°
    -- first, lets define the inr NT
    open HomReasoning
    open MR C

    inr : NaturalTransformation Δ⊤ G
    inr = ntHelper record
      { η = λ X → i₂
      ; commute = λ f → begin
        i₂ ∘ id                   ≈⟨ identityʳ ⟩
        i₂                       ≈˘⟨ inject₂ ⟩
        [ i₁ ∘ f , i₂ ] ∘ i₂     ≈˘⟨ []-cong₂ Equiv.refl identityʳ ⟩∘⟨refl ⟩
        [ i₁ ∘ f , i₂ ∘ id ] ∘ i₂ ∎
      }

    inr° : NaturalTransformation G° Δ⊤°
    inr° = η° {Δ⊤} {G} {ω} {ω'} inr

    is-const-terminal-G : Δ⊥ ≃ⁱ G°
    is-const-terminal-G = niHelper record
      { η = λ X → ¡
      ; η⁻¹ = λ X → G°→initial X
      ; commute = λ f → ¡-unique₂ _ _
      ; iso = λ X → ≅.sym (isStrictInitial.is-strict (G°→initial X)) ._≅_.iso
      }
      where module inr° = NaturalTransformation inr°
            G°→initial : ∀ X → G°.₀ X ⇒ ⊥
            G°→initial X = dual→any ⊥ ∘ inr°.η X
