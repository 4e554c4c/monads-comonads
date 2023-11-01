{-# OPTIONS --without-K #-}
open import Categories.Category using (Category)
open import Categories.Category.BinaryProducts using (BinaryProducts; module BinaryProducts)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Category.Monoidal.BiClosed using (BiClosed)
open import Categories.Category.Product using (_⁂_)
open import Categories.Functor using (Functor; Endofunctor; _∘F_) renaming (id to idF)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Data.Product using (uncurry; uncurry′; Σ; _,_; _×_)
open import Level using (_⊔_)

module fil-examples  {o ℓ e} (C : Category o ℓ e)  where

open Category C

module example-1 (M : Monoidal C) (CC : Closed M) {A : Obj} where
  open import fil (M) using (functor-functor-interaction-law)

  open HomReasoning

  open Closed CC

  open import Categories.Functor.Bifunctor using (module Bifunctor)

  private module ⊗-Bifunctor = Bifunctor ⊗

  F : Endofunctor C
  F = [ A ,-]

  G : Endofunctor C
  G = A ⊗-

  open Functor F using (F₀; F₁)
  open Functor G renaming (F₀ to G₀; F₁ to G₁)

  φ : (X Y : Obj) → (F₀ X) ⊗₀ (G₀ Y) ⇒ (X ⊗₀ Y)
  φ X Y = (adjoint.counit.η X ⊗₁ id) ∘ associator.to

  open import Categories.Morphism.Reasoning C using ( pullˡ; pushˡ; id-comm-sym)
  open import Categories.Category.Monoidal.Reasoning (M) using (⊗-resp-≈ˡ; ⊗-distrib-over-∘; _⟩⊗⟨_)

  natural : {X Y Z W : Obj} (f : X ⇒ Z) (g : Y ⇒ W) →  φ Z W ∘ (F₁ f ⊗₁ G₁ g) ≈ (f ⊗₁ g) ∘ φ X Y
  natural {X} {Y} {Z} {W} f g = begin
    (φ Z W) ∘ ((F₁ f) ⊗₁ (G₁ g))                                     ≈⟨ assoc ⟩
    (adjoint.counit.η Z ⊗₁ id) ∘ associator.to ∘ ((F₁ f) ⊗₁ (G₁ g))  ≈⟨ refl⟩∘⟨ assoc-commute-to ⟩
    (adjoint.counit.η Z ⊗₁ id) ∘ ((F₁ f ⊗₁ id) ⊗₁ g) ∘ _            ≈˘⟨ pushˡ ⊗-distrib-over-∘ ⟩
    ((adjoint.counit.η Z ∘ (F₁ f ⊗₁ id)) ⊗₁ (id ∘ g)) ∘ _            ≈⟨ adjoint.counit.commute f ⟩⊗⟨ id-comm-sym ⟩∘⟨refl ⟩
    ((f ∘ adjoint.counit.η X) ⊗₁ (g ∘ id)) ∘ associator.to           ≈⟨ ⊗-distrib-over-∘ ⟩∘⟨refl ○ assoc ⟩
    (f ⊗₁ g) ∘ (φ X Y)                                               ∎

  fil : functor-functor-interaction-law
  fil = record
    { F = F
    ; G = G
    ; ϕ = ntHelper record
      { η = uncurry φ
      ; commute = uncurry natural }}

module example-2 (M : Monoidal C) (BC : BiClosed M) {A : Obj} where
  open import fil (M) using (functor-functor-interaction-law)

  open BiClosed BC

  Reader Writer CoReader CoWriter : Endofunctor C
  Reader   = [-⇦ A ]
  CoReader = A ⊗-
  Writer   =  -⊗ A
  CoWriter = [ A ⇨-]

  open Functor Reader renaming (F₀ to Reader₀; F₁ to Reader₁)
  open Functor CoReader renaming (F₀ to CoReader₀; F₁ to CoReader₁)

  open Functor Writer renaming (F₀ to Writer₀; F₁ to Writer₁)
  open Functor CoWriter renaming (F₀ to CoWriter₀; F₁ to CoWriter₁)

  open adjointˡ.counit using () renaming (η to εˡ)
  open adjointˡ.unit   using () renaming (η to ηˡ)

  open adjointʳ.counit using () renaming (η to εʳ)
  open adjointʳ.unit   using () renaming (η to ηʳ)

  φ : (X Y : Obj) → (Reader₀ X) ⊗₀ (CoReader₀ Y) ⇒ (X ⊗₀ Y)
  φ X Y = (εˡ X ⊗₁ id) ∘ associator.to

  ψ : (X Y : Obj) → (Writer₀ X) ⊗₀ (CoWriter₀ Y) ⇒ (X ⊗₀ Y)
  ψ X Y = (id ⊗₁ εʳ Y) ∘ associator.from

  open import Categories.Morphism.Reasoning C using ( pullˡ; pushˡ; id-comm-sym)
  open import Categories.Category.Monoidal.Reasoning (M) using (⊗-resp-≈ˡ; ⊗-distrib-over-∘; _⟩⊗⟨_)
  open HomReasoning

  open import Categories.Functor.Bifunctor using (module Bifunctor)

  private module ⊗-Bifunctor = Bifunctor ⊗

  φ-natural : {X Y Z W : Obj} (f : X ⇒ Z) (g : Y ⇒ W) →  φ Z W ∘ (Reader₁ f ⊗₁ CoReader₁ g) ≈ (f ⊗₁ g) ∘ φ X Y
  φ-natural {X} {Y} {Z} {W} f g = begin
    (φ Z W) ∘ ((Reader₁ f) ⊗₁ (CoReader₁ g))     ≈⟨ assoc ⟩
    (εˡ Z ⊗₁ id) ∘ associator.to ∘ ((Reader₁ f) ⊗₁ (CoReader₁ g))
                                                 ≈⟨ refl⟩∘⟨ assoc-commute-to ⟩
    (εˡ Z ⊗₁ id) ∘ ((Reader₁ f ⊗₁ id) ⊗₁ g) ∘ _ ≈˘⟨ pushˡ ⊗-distrib-over-∘ ⟩
    ((εˡ Z ∘ (Reader₁ f ⊗₁ id)) ⊗₁ (id ∘ g)) ∘ _ ≈⟨ adjointˡ.counit.commute f ⟩⊗⟨ id-comm-sym ⟩∘⟨refl ⟩
    ((f ∘ εˡ X) ⊗₁ (g ∘ id)) ∘ associator.to     ≈⟨ ⊗-distrib-over-∘ ⟩∘⟨refl ○ assoc ⟩
    (f ⊗₁ g) ∘ (φ X Y)                           ∎

  fil-reader : functor-functor-interaction-law
  fil-reader = record
    { F = Reader
    ; G = CoReader
    ; ϕ = ntHelper record
      { η = uncurry φ
      ; commute = uncurry φ-natural }}

  ψ-natural : {X Y Z W : Obj} (f : X ⇒ Z) (g : Y ⇒ W) → ψ Z W ∘ (Writer₁ f ⊗₁ CoWriter₁ g) ≈ (f ⊗₁ g) ∘ ψ X Y
  ψ-natural {X} {Y} {Z} {W} f g = begin
    (ψ Z W) ∘ ((Writer₁ f) ⊗₁ (CoWriter₁ g))      ≈⟨ assoc ⟩
    (id ⊗₁ εʳ W) ∘ associator.from ∘ ((Writer₁ f) ⊗₁ (CoWriter₁ g))
                                                  ≈⟨ refl⟩∘⟨ assoc-commute-from ⟩
    (id ⊗₁ εʳ W) ∘ (f ⊗₁ id ⊗₁ CoWriter₁ g) ∘ _  ≈˘⟨ pushˡ ⊗-distrib-over-∘ ⟩
    ((id ∘ f) ⊗₁ (εʳ W ∘ (id ⊗₁ CoWriter₁ g)))∘ _ ≈⟨ id-comm-sym ⟩⊗⟨ adjointʳ.counit.commute g ⟩∘⟨refl  ⟩
    ((f ∘ id) ⊗₁ (g ∘ εʳ Y)) ∘ associator.from    ≈⟨ ⊗-distrib-over-∘ ⟩∘⟨refl ○ assoc ⟩
    (f ⊗₁ g) ∘ (ψ X Y)                            ∎

  fil-writer : functor-functor-interaction-law
  fil-writer = record
    { F = Writer
    ; G = CoWriter
    ; ϕ = ntHelper record
      { η = uncurry ψ
      ; commute = uncurry ψ-natural }}

  {- This should follow by the monoidal product in IL
  fil-state : functor-functor-interaction-law
  fil-state = record
    { F = Reader ∘F Writer
    ; G = CoReader ∘F CoWriter
    ; ϕ = ntHelper record
      { η = ?
      ; commute = ? }}
  -}

