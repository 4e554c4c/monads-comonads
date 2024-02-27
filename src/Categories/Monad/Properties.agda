{-# OPTIONS --without-K --safe #-}
open import Level
open import Categories.Category using (Category)
open import Categories.Functor using (Functor; Endofunctor; _∘F_) renaming (id to idF)
open import Categories.Monad
open import Categories.NaturalTransformation renaming (id to idN)
open import Categories.NaturalTransformation.NaturalIsomorphism hiding (_≃_)
open import Categories.NaturalTransformation.Equivalence
open NaturalIsomorphism

module Categories.Monad.Properties {o ℓ e} {C : Category o ℓ e} where

module _ where
  open Monad
  open Category C
  idM : Monad C
  idM .F = idF
  idM .η = idN
  idM .μ = unitor² .F⇒G
  idM .assoc = Equiv.refl
  idM .sym-assoc = Equiv.refl
  idM .identityˡ = identity²
  idM .identityʳ = identity²
