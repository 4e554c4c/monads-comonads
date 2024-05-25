{-# OPTIONS --without-K --safe --lossy-unification #-}

module Prelude where


import Categories.Morphism.Reasoning

open import Categories.Category                                  public
open import Categories.Category.BinaryProducts                   using (BinaryProducts; module BinaryProducts) public
open import Categories.Category.Construction.Functors            using (Functors; curry) -- ; curry₀; curry₁)
                                                                 renaming () public
open import Categories.Category.Construction.Monoids             using (Monoids) public
open import Categories.Category.Monoidal                         using (Monoidal; monoidalHelper) public
open import Categories.Category.Monoidal.Braided                 using (Braided) public
open import Categories.Category.Monoidal.Symmetric               using (Symmetric) public
open import Categories.Category.Monoidal.Closed                  using (Closed) public
open import Categories.Category.Product                          using (_⁂_; _⁂ⁿ_;_※_; _※ⁿ_; Swap; assocˡ; assocʳ; πˡ; πʳ)
                                                                 renaming (Product to _×ᶜ_) public
open import Categories.Comonad                                   using (Comonad)
                                                                 renaming (id to idCM) 
                                                                 hiding (module Comonad) public
open import Categories.Comonad.Morphism                          using (module Comonad⇒-id)
                                                                 renaming (Comonad⇒-id to _CM⇒_; Comonad⇒-id-id to CM⇒-id; Comonad⇒-id-∘ to _∘CM_) public
open import Categories.Functor                                   using (Functor; Endofunctor; _∘F_)
                                                                 renaming (id to idF) public
open import Categories.Functor.Bifunctor                         using (Bifunctor) public
open import Categories.Functor.Construction.Constant             using (const) public
open import Categories.Monad                                     using (Monad)
                                                                 renaming (id to idM)
                                                                 hiding (module Monad) public
open import Categories.Monad.Morphism                            using (module Monad⇒-id)
                                                                 renaming (Monad⇒-id to _M⇒_; Monad⇒-id-id to M⇒-id; Monad⇒-id-∘ to _∘M_) public
open import Categories.NaturalTransformation                     using (NaturalTransformation; _∘ʳ_; _∘ˡ_; _∘ᵥ_; _∘ₕ_; ntHelper)
                                                                 renaming (id to idN) public --hiding (module NaturalTransformation) public
open import Categories.NaturalTransformation.Equivalence         using (_≃_; ≃-isEquivalence) public
open import Categories.NaturalTransformation.NaturalIsomorphism  using (NaturalIsomorphism; niHelper)
                                                                 renaming (_≃_ to _≃ⁿ_; sym to symⁿⁱ) public
open import Categories.NaturalTransformation.NaturalIsomorphism  using (_ⓘᵥ_; _ⓘₕ_; _ⓘˡ_; _ⓘʳ_; associator; sym-associator)
                                                                 renaming (_≃_ to _≃ⁿ_; refl to reflⁿⁱ) public
open import Categories.NaturalTransformation.Properties          using (replaceˡ; replaceʳ) public
open import Categories.NaturalTransformation.Properties          using (replaceˡ; replaceʳ) public

open import Data.Product                                         using (Σ; _,_; _×_)
                                                                 renaming (proj₁ to fst; proj₂ to snd) public
open import Level                                                using (_⊔_; Level)
                                                                 renaming (suc to lsuc) public

--module NaturalTransformation = Categories.NaturalTransformation.NaturalTransformation renaming (η to app)

module Monad {o ℓ e} {C : Category o ℓ e} (M : Monad C) where
  open Categories.Monad.Monad M public
  open Functor F public

module Comonad {o ℓ e} {C : Category o ℓ e} (W : Comonad C) where
  open Categories.Comonad.Comonad W public
  open Functor F public

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
