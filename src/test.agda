{-# OPTIONS --without-K --hidden-argument-puns #-}
open import Categories.Category using (Category)
open import Categories.Functor using (Functor; Endofunctor)

module test {o ℓ e} {C : Category o ℓ e} {F : Endofunctor C} where

open Functor F
open Category C
open HomReasoning

f-eq : {A : Obj} → F₁ {A} id ∘ id ≈ id
f-eq = begin F₁ id ∘ id ≈⟨ identity ⟩∘⟨refl ⟩
             id    ∘ id ≈⟨ identity² ⟩
             id         ∎
