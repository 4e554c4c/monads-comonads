{-# OPTIONS --without-K --safe --lossy-unification #-}

module Prelude where

open import Categories.Category public
open import Categories.Category.BinaryProducts using (BinaryProducts; module BinaryProducts) public
open import Categories.Category.Monoidal using (Monoidal; monoidalHelper) public
open import Categories.Category.Monoidal.Closed using (Closed) public
open import Categories.Category.Product using (_⁂_; _⁂ⁿ_) public renaming (Product to ProductCat) public
open import Categories.Functor using (Functor; Endofunctor; _∘F_) renaming (id to idF) public
open import Categories.Functor.Bifunctor using (Bifunctor) public
open import Categories.NaturalTransformation using (NaturalTransformation; _∘ʳ_; _∘ˡ_; _∘ᵥ_; _∘ₕ_; ntHelper)
                                             renaming (id to idN)
                                             hiding (module NaturalTransformation) public
open import Categories.NaturalTransformation.Properties using (replaceˡ; replaceʳ) public
open import Categories.NaturalTransformation.NaturalIsomorphism using (_ⓘᵥ_; _ⓘₕ_; _ⓘˡ_; _ⓘʳ_; associator; sym-associator)
                                                                renaming (_≃_ to _≃ⁿ_; refl to reflⁿⁱ) public
open import Categories.NaturalTransformation.Equivalence using (_≃_; ≃-isEquivalence) public

open import Data.Product using (uncurry; uncurry′; Σ; _,_; _×_) renaming (proj₁ to fst; proj₂ to snd) public
open import Level using (_⊔_) renaming (suc to lsuc) public

import Categories.Morphism.Reasoning

open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism; niHelper)
                                                                renaming (_≃_ to _≃ⁿ_; sym to symⁿⁱ) public
                                                                --hiding (module NaturalIsomorphism) public
--module NaturalIsomorphism = Categories.NaturalTransformation.NaturalIsomorphism.NaturalIsomorphism renaming (F⇒G to to; F⇐G to from)

module NaturalTransformation = Categories.NaturalTransformation.NaturalTransformation renaming (η to app)

module MR {o ℓ e} (C : Category o ℓ e) where
  open Categories.Morphism.Reasoning C public

  open Category C
  open Definitions C
  open HomReasoning

  private
    variable
      X Y : Obj
      a b c d : X ⇒ Y
      f g h i : X ⇒ Y
  module Pull-assocs (ab≡cd : a ∘ b ≈ c ∘ d) where

    pullˡ-assoc : a ∘ (b ∘ f) ≈ c ∘ (d ∘ f)
    pullˡ-assoc {f = f} = pullˡ ab≡cd ○ assoc

  open Pull-assocs public

infixr -1 _$_
_$_ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂} →
      ((x : A) → B x) → ((x : A) → B x)
f $ x = f x
{-# INLINE _$_ #-}
