{-# OPTIONS --without-K --safe #-}
open import Level
open import Categories.Category using (Category)
open import Categories.Functor using (Functor; Endofunctor; _∘F_) renaming (id to idF)
open import Categories.Comonad
open import Categories.NaturalTransformation renaming (id to idN)
open import Categories.NaturalTransformation.NaturalIsomorphism hiding (_≃_)
open import Categories.NaturalTransformation.Equivalence
open NaturalIsomorphism

module Categories.Comonad.Properties {o ℓ e} {C : Category o ℓ e} where

module _ where
  open Comonad
  open Category C
  idCM : Comonad C
  idCM .F = idF
  idCM .ε = idN
  idCM .δ = unitor² .F⇐G
  idCM .assoc = Equiv.refl
  idCM .sym-assoc = Equiv.refl
  idCM .identityˡ = identity²
  idCM .identityʳ = identity²
