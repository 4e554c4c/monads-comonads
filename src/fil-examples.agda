{-# OPTIONS --without-K --safe #-}
open import Prelude

open import Categories.Category.Monoidal.BiClosed using (BiClosed)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Categories.Functor.Bifunctor using (module Bifunctor)
open import Categories.Functor.Bifunctor using (module Bifunctor)

open import Data.Product using (uncurry; uncurry′; Σ; _,_; _×_)
open import Level using (_⊔_)
import fil

module fil-examples  {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} where

open import Categories.Category.Monoidal.Reasoning M

open import IL.Monoidal M using (_⊗L₀_; _⊗L₁_)
open import fil (M) using (FIL)

open Category C
open MR C


module example-1  (CC : Closed M) {A : Obj} where
  open Closed CC

  Reader : Endofunctor C
  Reader = [ A ,-]

  CoReader : Endofunctor C
  CoReader = A ⊗-

  open Functor Reader using () renaming (F₀ to Reader₀; F₁ to Reader₁) public
  open Functor CoReader using () renaming (F₀ to CoReader₀; F₁ to CoReader₁) public

  ϕ : (X Y : Obj) → (Reader₀ X) ⊗₀ (CoReader₀ Y) ⇒ (X ⊗₀ Y)
  ϕ X Y = (adjoint.counit.η X ⊗₁ id) ∘ associator.to

  natural : {X Y Z W : Obj} (f : X ⇒ Z) (g : Y ⇒ W) →  ϕ Z W ∘ (Reader₁ f ⊗₁ CoReader₁ g) ≈ (f ⊗₁ g) ∘ ϕ X Y
  natural {X} {Y} {Z} {W} f g = begin
    (ϕ Z W) ∘ ((Reader₁ f) ⊗₁ (CoReader₁ g))
      ≈⟨ assoc ⟩
    (adjoint.counit.η Z ⊗₁ id) ∘ associator.to ∘ ((Reader₁ f) ⊗₁ (CoReader₁ g)) 
      ≈⟨ refl⟩∘⟨ assoc-commute-to ⟩
    (adjoint.counit.η Z ⊗₁ id) ∘ ((Reader₁ f ⊗₁ id) ⊗₁ g) ∘ _
      ≈˘⟨ pushˡ ⊗-distrib-over-∘ ⟩
    ((adjoint.counit.η Z ∘ (Reader₁ f ⊗₁ id)) ⊗₁ (id ∘ g)) ∘ _
      ≈⟨ adjoint.counit.commute f ⟩⊗⟨ id-comm-sym ⟩∘⟨refl ⟩
    ((f ∘ adjoint.counit.η X) ⊗₁ (g ∘ id)) ∘ associator.to
      ≈⟨ ⊗-distrib-over-∘ ⟩∘⟨refl ○ assoc ⟩
    (f ⊗₁ g) ∘ (ϕ X Y)
      ∎

  fil : FIL
  fil = record
    { F = Reader
    ; G = CoReader
    ; ϕ = ntHelper record
      { η = uncurry ϕ
      ; commute = uncurry natural }}

module example-2 (BC : BiClosed M) {A : Obj} where
  open BiClosed BC

  Reader Writer CoReader CoWriter : Endofunctor C
  Reader   = [ A ,-]
  CoReader = A ⊗-
  Writer   =  -⊗ A
  CoWriter = ⟦ A ,-⟧

  open Functor Reader renaming (F₀ to Reader₀; F₁ to Reader₁)
  open Functor CoReader renaming (F₀ to CoReader₀; F₁ to CoReader₁)

  open Functor Writer renaming (F₀ to Writer₀; F₁ to Writer₁)
  open Functor CoWriter renaming (F₀ to CoWriter₀; F₁ to CoWriter₁)

  open adjointˡ.counit using () renaming (η to εˡ)
  open adjointˡ.unit   using () renaming (η to ηˡ)

  open adjointʳ.counit using () renaming (η to εʳ)
  open adjointʳ.unit   using () renaming (η to ηʳ)

  ϕ : (X Y : Obj) → (Reader₀ X) ⊗₀ (CoReader₀ Y) ⇒ (X ⊗₀ Y)
  ϕ X Y = (εˡ X ⊗₁ id) ∘ associator.to

  ψ : (X Y : Obj) → (Writer₀ X) ⊗₀ (CoWriter₀ Y) ⇒ (X ⊗₀ Y)
  ψ X Y = (id ⊗₁ εʳ Y) ∘ associator.from

  ϕ-natural : ∀ {X Y Z W} (f : X ⇒ Z) (g : Y ⇒ W) →
              ϕ Z W ∘ Reader₁ f ⊗₁ CoReader₁ g ≈ f ⊗₁ g ∘ ϕ X Y
  ϕ-natural {X} {Y} {Z} {W} f g = begin
    ϕ Z W ∘ (Reader₁ f) ⊗₁ (CoReader₁ g)
      ≈⟨ pullʳ assoc-commute-to ⟩
    (εˡ Z ⊗₁ id) ∘ (Reader₁ f ⊗₁ id) ⊗₁ g ∘ associator.to
      ≈˘⟨ pushˡ ⊗-distrib-over-∘ ⟩
    (εˡ Z ∘ Reader₁ f ⊗₁ id) ⊗₁ (id ∘ g) ∘ associator.to
      ≈⟨ adjointˡ.counit.commute f ⟩⊗⟨ id-comm-sym ⟩∘⟨refl ⟩
    (f ∘ εˡ X) ⊗₁ (g ∘ id) ∘ associator.to
      ≈⟨ pushˡ ⊗-distrib-over-∘ ⟩
    f ⊗₁ g ∘ ϕ X Y
      ∎

  fil-reader : FIL
  fil-reader = record
    { F = Reader
    ; G = CoReader
    ; ϕ = ntHelper record
      { η = uncurry ϕ
      ; commute = uncurry ϕ-natural }}

  ψ-natural : {X Y Z W : Obj} (f : X ⇒ Z) (g : Y ⇒ W) → ψ Z W ∘ (Writer₁ f ⊗₁ CoWriter₁ g) ≈ (f ⊗₁ g) ∘ ψ X Y
  ψ-natural {X} {Y} {Z} {W} f g = begin
    (ψ Z W) ∘ ((Writer₁ f) ⊗₁ (CoWriter₁ g))      ≈⟨ assoc ⟩
    (id ⊗₁ εʳ W) ∘ associator.from ∘ ((Writer₁ f) ⊗₁ (CoWriter₁ g))
                                                  ≈⟨ refl⟩∘⟨ assoc-commute-from ⟩
    (id ⊗₁ εʳ W) ∘ (f ⊗₁ id ⊗₁ CoWriter₁ g) ∘ _  ≈˘⟨ pushˡ ⊗-distrib-over-∘ ⟩
    ((id ∘ f) ⊗₁ (εʳ W ∘ (id ⊗₁ CoWriter₁ g)))∘ _ ≈⟨ id-comm-sym ⟩⊗⟨ adjointʳ.counit.commute g ⟩∘⟨refl  ⟩
    ((f ∘ id) ⊗₁ (g ∘ εʳ Y)) ∘ associator.from    ≈⟨ ⊗-distrib-over-∘ ⟩∘⟨refl ○ assoc ⟩
    (f ⊗₁ g) ∘ (ψ X Y)                            ∎

  fil-writer : FIL
  fil-writer = record
    { F = Writer
    ; G = CoWriter
    ; ϕ = ntHelper record
      { η = uncurry ψ
      ; commute = uncurry ψ-natural }}

  State CoState : Endofunctor C
  State   = Reader ∘F Writer
  CoState = CoReader ∘F CoWriter

  fil-state : FIL
  fil-state = fil-reader ⊗L₀ fil-writer

  module fil-state = FIL fil-state

  _ : fil-state.F ≡ State
  _ = refl
  _ : fil-state.G ≡ CoState
  _ = refl
