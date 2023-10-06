{-# OPTIONS --without-K #-}
open import Categories.Category using (Category)
open import Categories.Category.BinaryProducts using (BinaryProducts; module BinaryProducts)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
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
