{-# OPTIONS --without-K --safe --lossy-unification #-}

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
open import Categories.NaturalTransformation.Properties using (replaceˡ) public
open import Categories.NaturalTransformation.NaturalIsomorphism using (_ⓘᵥ_; _ⓘₕ_; _ⓘˡ_; _ⓘʳ_; associator; sym-associator)
                                                                renaming (_≃_ to _≃ⁿ_; refl to reflⁿⁱ) public
open import Categories.NaturalTransformation.Equivalence using (_≃_; ≃-isEquivalence) public

open import Data.Product using (uncurry; uncurry′; Σ; _,_; _×_) renaming (proj₁ to fst; proj₂ to snd) public
open import Level using (_⊔_) renaming (suc to lsuc) public

--import Categories.Morphism.Reasoning
--module MR = Categories.Morphism.Reasoning
module NaturalTransformation = Categories.NaturalTransformation.NaturalTransformation renaming (η to app)

open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism; niHelper)
                                                                renaming (_≃_ to _≃ⁿ_) public
                                                                --hiding (module NaturalIsomorphism) public
--module NaturalIsomorphism = Categories.NaturalTransformation.NaturalIsomorphism.NaturalIsomorphism renaming (F⇒G to to; F⇐G to from)
