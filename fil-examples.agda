{-# OPTIONS --without-K #-}
open import Categories.Category using (Category)
open import Categories.Category.BinaryProducts using (BinaryProducts; module BinaryProducts)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.Cartesian.Monoidal using (module CartesianMonoidal)
open import Categories.Category.CartesianClosed using (CartesianClosed; module CartesianMonoidalClosed)
open import Categories.Category.Product using (_⁂_)
open import Categories.Functor using (Functor; Endofunctor; _∘F_) renaming (id to idF)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Data.Product using (uncurry; uncurry′; Σ; _,_; _×_)
open import Level using (_⊔_)

module fil-examples  {o ℓ e} (C : Category o ℓ e) (CC : CartesianClosed C) where

open Category C
open CartesianClosed CC

module cartesian = Cartesian cartesian

open import fil (CartesianMonoidal.monoidal cartesian) using (functor-functor-interaction-law)

open CartesianMonoidalClosed C CC using (module adjoint; _⊗₀_; _⊗₁_; ⊗)

module example-1 {A : Obj} where
  open BinaryProducts (cartesian.products) using (-×_; _×-; ⟨_,_⟩; π₁; π₂; assocʳ; ⟨⟩∘; ⟨⟩-cong₂; ⟨⟩-congʳ;⟨⟩-congˡ; π₁∘⁂; π₂∘⁂; assocʳ∘⁂; ⁂∘⟨⟩)
  open HomReasoning

  open import Categories.Category.Monoidal.Reasoning (CartesianMonoidal.monoidal cartesian) using (⊗-resp-≈ˡ)
  open import Categories.Functor.Bifunctor using (module Bifunctor)
  open import Categories.Morphism.Reasoning C using (assoc²'; pullˡ; assoc²'' )
  open import Categories.Tactic.Category using (solve)

  private module ⊗-Bifunctor = Bifunctor ⊗

  F : Endofunctor C
  F = A ⇨-

  G : Endofunctor C
  G = A ×-

  open Functor F using (F₀; F₁)
  open Functor G renaming (F₀ to G₀; F₁ to G₁)

  φ : (X Y : Obj) → (F₀ X) ⊗₀ (G₀ Y) ⇒ (X ⊗₀ Y)
  φ X Y = ⟨ eval′ ∘ π₁ ∘ assocʳ , π₂ ∘ π₂ ⟩

  natural : {X Y Z W : Obj} (f : X ⇒ Z) (g : Y ⇒ W) →  φ Z W ∘ (F₁ f ⊗₁ G₁ g) ≈ (f ⊗₁ g) ∘ φ X Y
  natural {X} {Y} {Z} {W} f g = begin
    (φ Z W) ∘ ((F₁ f) ⊗₁ (G₁ g))                      ≈⟨ ⟨⟩∘ ○ ⟨⟩-cong₂ assoc²' assoc ⟩
    ⟨ _ , π₂ ∘ π₂   ∘ _  ⟩                            ≈⟨ ⟨⟩-congˡ (∘-resp-≈ʳ π₂∘⁂) ⟩
    ⟨ _ , π₂ ∘ G₁ g ∘ π₂ ⟩                            ≈⟨ ⟨⟩-congˡ (pullˡ π₂∘⁂ ○ assoc)  ⟩
    ⟨ _ , g  ∘ π₂   ∘ π₂ ⟩                            ≈⟨ Equiv.refl ⟩
    ⟨ eval′ ∘ π₁ ∘ assocʳ ∘ (F₁ f ⊗₁ (id ⊗₁ g)) , _ ⟩ ≈⟨ ⟨⟩-congʳ (∘-resp-≈ʳ (∘-resp-≈ʳ assocʳ∘⁂)) ⟩
    ⟨ eval′ ∘ π₁ ∘ ((F₁ f ⊗₁ id) ⊗₁ g) ∘ assocʳ , _ ⟩ ≈⟨ ⟨⟩-congʳ (∘-resp-≈ʳ (pullˡ π₁∘⁂ ○ assoc)) ⟩
    -- here we simplify (F₁ f) after pulling it out of the lambda,
    -- as it is easier to do before re-associating
    ⟨ eval′ ∘ (F₁ f ⊗₁ id) ∘ π₁ ∘ assocʳ , _ ⟩        ≈⟨ ⟨⟩-congʳ (pullˡ (β′ ○ ∘-resp-≈ʳ (∘-resp-≈ʳ ⊗-Bifunctor.identity ○ identityʳ)))⟩
    ⟨ (f ∘ eval′) ∘ π₁ ∘ assocʳ , _ ⟩                 ≈⟨ ⟨⟩-congʳ (Equiv.sym assoc²'' ○ ∘-resp-≈ʳ assoc) ⟩
    ⟨ f ∘ eval′ ∘ π₁ ∘ assocʳ , g ∘ π₂ ∘ π₂ ⟩         ≈⟨ Equiv.sym ⁂∘⟨⟩ ⟩
    (f ⊗₁ g) ∘ (φ X Y)                                ∎

  fil : functor-functor-interaction-law
  fil = record
    { F = F
    ; G = G
    ; ϕ = ntHelper record
      { η = uncurry φ
      ; commute = uncurry natural }}
