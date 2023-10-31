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

module example-2-1 (M : Monoidal C) (BC : BiClosed M) {A : Obj} where
  open import fil (M) using (functor-functor-interaction-law)

  open BiClosed BC

  Reader : Endofunctor C
  Reader = [-⇦ A ]

  CoReader : Endofunctor C
  CoReader = A ⊗-

  open Functor Reader renaming (F₀ to Reader₀; F₁ to Reader₁)
  open Functor CoReader renaming (F₀ to CoReader₀; F₁ to CoReader₁)

  φ : (X Y : Obj) → (Reader₀ X) ⊗₀ (CoReader₀ Y) ⇒ (X ⊗₀ Y)
  φ X Y = (adjointˡ.counit.η X ⊗₁ id) ∘ associator.to

  open import Categories.Morphism.Reasoning C using ( pullˡ; pushˡ; id-comm-sym)
  open import Categories.Category.Monoidal.Reasoning (M) using (⊗-resp-≈ˡ; ⊗-distrib-over-∘; _⟩⊗⟨_)
  open HomReasoning

  open import Categories.Functor.Bifunctor using (module Bifunctor)

  private module ⊗-Bifunctor = Bifunctor ⊗

  natural : {X Y Z W : Obj} (f : X ⇒ Z) (g : Y ⇒ W) →  φ Z W ∘ (Reader₁ f ⊗₁ CoReader₁ g) ≈ (f ⊗₁ g) ∘ φ X Y
  natural {X} {Y} {Z} {W} f g = begin
    (φ Z W) ∘ ((Reader₁ f) ⊗₁ (CoReader₁ g))                    ≈⟨ assoc ⟩
    (adjointˡ.counit.η Z ⊗₁ id) ∘ associator.to ∘ ((Reader₁ f) ⊗₁ (CoReader₁ g))
                                                                ≈⟨ refl⟩∘⟨ assoc-commute-to ⟩
    (adjointˡ.counit.η Z ⊗₁ id) ∘ ((Reader₁ f ⊗₁ id) ⊗₁ g) ∘ _ ≈˘⟨ pushˡ ⊗-distrib-over-∘ ⟩
    ((adjointˡ.counit.η Z ∘ (Reader₁ f ⊗₁ id)) ⊗₁ (id ∘ g)) ∘ _ ≈⟨ adjointˡ.counit.commute f ⟩⊗⟨ id-comm-sym ⟩∘⟨refl ⟩
    ((f ∘ adjointˡ.counit.η X) ⊗₁ (g ∘ id)) ∘ associator.to     ≈⟨ ⊗-distrib-over-∘ ⟩∘⟨refl ○ assoc ⟩
    (f ⊗₁ g) ∘ (φ X Y)                                          ∎

  fil : functor-functor-interaction-law
  fil = record
    { F = Reader
    ; G = CoReader
    ; ϕ = ntHelper record
      { η = uncurry φ
      ; commute = uncurry natural }}

  -- for the rest of the file, we assume that A is a monoid object

module example-2-2 (M : Monoidal C) (BC : BiClosed M) {A : Obj} {IsMonoid A} where
  open import fil (M) using (functor-functor-interaction-law)
  open BiClosed BC

  Writer : Endofunctor C
  Writer = -⊗ A

  CoWriter : Endofunctor C
  CoWriter =  [ A ⇨-]

  open Functor Writer renaming (F₀ to Writer₀; F₁ to Writer₁)
  open Functor CoWriter renaming (F₀ to CoWriter₀; F₁ to CoWriter₁)

  φ : (X Y : Obj) → (Writer₀ X) ⊗₀ (CoWriter₀ Y) ⇒ (X ⊗₀ Y)
  φ X Y = (id ⊗₁ adjointʳ.counit.η Y) ∘ associator.from

  open import Categories.Morphism.Reasoning C using ( pullˡ; pushˡ; id-comm-sym)
  open import Categories.Category.Monoidal.Reasoning (M) using (⊗-resp-≈ˡ; ⊗-distrib-over-∘; _⟩⊗⟨_)
  open HomReasoning

  open import Categories.Functor.Bifunctor using (module Bifunctor)

  private module ⊗-Bifunctor = Bifunctor ⊗

  natural : {X Y Z W : Obj} (f : X ⇒ Z) (g : Y ⇒ W) →  φ Z W ∘ (Writer₁ f ⊗₁ CoWriter₁ g) ≈ (f ⊗₁ g) ∘ φ X Y
  natural {X} {Y} {Z} {W} f g = begin
    (φ Z W) ∘ ((Writer₁ f) ⊗₁ (CoWriter₁ g))                     ≈⟨ assoc ⟩
    (id ⊗₁ adjointʳ.counit.η W) ∘ associator.from ∘ ((Writer₁ f) ⊗₁ (CoWriter₁ g))
                                                                 ≈⟨ refl⟩∘⟨ assoc-commute-from ⟩
    (id ⊗₁ adjointʳ.counit.η W) ∘ (f ⊗₁ id ⊗₁ CoWriter₁ g) ∘ _  ≈˘⟨ pushˡ ⊗-distrib-over-∘ ⟩
    ((id ∘ f) ⊗₁ (adjointʳ.counit.η W ∘ (id ⊗₁ CoWriter₁ g)))∘ _ ≈⟨ id-comm-sym ⟩⊗⟨ adjointʳ.counit.commute g ⟩∘⟨refl  ⟩
    ((f ∘ id) ⊗₁ (g ∘ adjointʳ.counit.η Y)) ∘ associator.from    ≈⟨ ⊗-distrib-over-∘ ⟩∘⟨refl ○ assoc ⟩
    (f ⊗₁ g) ∘ (φ X Y)                                           ∎

  fil : functor-functor-interaction-law
  fil = record
    { F = Writer
    ; G = CoWriter
    ; ϕ = ntHelper record
      { η = uncurry φ
      ; commute = uncurry natural }}

module example-2-3 (M : Monoidal C) (BC : BiClosed M) {A : Obj} {IsMonoid A} where
  open import fil (M) using (functor-functor-interaction-law)
  module BC =  BiClosed BC
  open example-2-1 (M) (BC) renaming (fil to fil₁)
  open example-2-2 (M) (BC) renaming (fil to fil₂)

  {- This should follow by the monoidal product in IL
  fil : functor-functor-interaction-law
  fil = record
    { F = Reader ∘F Writer
    ; G = CoReader ∘F CoWriter
    ; ϕ = ntHelper record
      { η = ?
      ; commute = ? }}
  -}

