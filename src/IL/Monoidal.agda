{-# OPTIONS --without-K --lossy-unification --allow-unsolved-metas #-}
open import Categories.Category
open import Categories.Category.Monoidal using (Monoidal)

module IL.Monoidal  {o ℓ e} {C : Category o ℓ e} (MC : Monoidal C) where

import Categories.Morphism.Reasoning as MR
open Monoidal MC using (⊗)
open import Categories.Functor using (Functor; Endofunctor; _∘F_) renaming (id to idF)
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Categories.NaturalTransformation using (NaturalTransformation; _∘ʳ_; _∘ˡ_; _∘ᵥ_; _∘ₕ_; ntHelper) renaming (id to idN)
open import Categories.NaturalTransformation.Properties using (replaceˡ)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_ⓘᵥ_; _ⓘₕ_; _ⓘˡ_; _ⓘʳ_; associator; sym-associator) 
                                                                renaming (_≃_ to _≃ⁿ_; refl to reflⁿⁱ)
open import IL.Core (MC) renaming (id to idIL)
open import fil (MC) using (functor-functor-interaction-law; FIL)
open import Data.Product using (uncurry; uncurry′; Σ; _,_; _×_)
open import Categories.Category.Product using (_⁂_; _⁂ⁿ_) renaming (Product to ProductCat)

private
  module C = Category C
  module C² = Category (ProductCat C C)

unit : functor-functor-interaction-law
unit = record
  { F = idF
  ; G = idF
  -- agda doesn't like `idN` here, so we eta-expand it
  ; ϕ = ntHelper record
    { η = λ { _ → C.id }
    ; commute = λ { _ → id-comm-sym } }}
  where open MR C

-- unfortunately we don't have a definitional equality here, so we need to transport along a natural isomorphism
⊗₀-IL : functor-functor-interaction-law → functor-functor-interaction-law → functor-functor-interaction-law
⊗₀-IL L L' = FIL (F ∘F J) (G ∘F K) map
  where open functor-functor-interaction-law L
        open functor-functor-interaction-law L' renaming (ϕ to Ψ; F to J; G to K)
        map : NaturalTransformation (⊗ ∘F (F ∘F J ⁂ G ∘F K)) ⊗
        map = replaceˡ (Ψ ∘ᵥ ϕ ∘ʳ (J ⁂ K)) (associator (J ⁂ K) (F ⁂ G) ⊗)

open import Categories.Category.Monoidal.Reasoning (MC)

⊗₁-IL : {L L' M M' : functor-functor-interaction-law} →
        (L ⇒ᶠⁱˡ L') → (M ⇒ᶠⁱˡ M') →
        IL [ ⊗₀-IL L M , ⊗₀-IL L' M' ]
⊗₁-IL {L} {L'} {M} {M'} F⟨ f , g , eq ⟩ F⟨ j , k , eq' ⟩ = F⟨ f ∘ₕ j , g ∘ₕ k , (λ {x} → begin
    appN (_ ∘ᵥ ⊗ ∘ˡ (idN ⁂ⁿ g ∘ₕ k)) x    ≈⟨ {! !} ⟩
    appN (_ ∘ᵥ ⊗ ∘ˡ (f ∘ₕ j ⁂ⁿ idN)) x    ∎
  )⟩
  where open functor-functor-interaction-law L  using (ϕ; F; G)
        open functor-functor-interaction-law L' renaming (ϕ to ϕ'; F to F'; G to G')
        open functor-functor-interaction-law M  renaming (ϕ to Ψ; F to J; G to K)
        open functor-functor-interaction-law M' renaming (ϕ to Ψ'; F to J'; G to K')
        open NaturalTransformation using () renaming (η to appN)

homomorphism-IL : {L L' L'' M M' M'' : functor-functor-interaction-law }
                  {f : L ⇒ᶠⁱˡ L'} → {g : M ⇒ᶠⁱˡ M'} →
                  {f' : L' ⇒ᶠⁱˡ L''} → {g' : M' ⇒ᶠⁱˡ M''} → (let open Category IL) →
                  ⊗₁-IL (f' ∘ f) (g' ∘ g) ≈ ⊗₁-IL f' g' ∘ ⊗₁-IL f g
homomorphism-IL {L} {L'} {L''} {M} {M'} {M''} {F⟨ f , g , _ ⟩} 
  {F⟨ j , k , _ ⟩} {F⟨ f' , g' , _ ⟩}  {F⟨ j' , k' , _ ⟩} = {!C.assoc !} , {! !}
  where open Category C
        open functor-functor-interaction-law L   using (ϕ; F; G)
        open functor-functor-interaction-law L'  renaming (ϕ to ϕ';  F to F';  G to G')
        open functor-functor-interaction-law L'' renaming (ϕ to ϕ''; F to F''; G to G'')
        open functor-functor-interaction-law M   renaming (ϕ to Ψ;   F to J;   G to K)
        open functor-functor-interaction-law M'  renaming (ϕ to Ψ';  F to J';  G to K')
        open functor-functor-interaction-law M'' renaming (ϕ to Ψ''; F to J''; G to K'')
        open Functor F'' renaming (F₁ to F''₁)
        open Functor F' renaming (F₁ to F'₁)
        open Functor F using (F₀)
        open Functor J renaming (F₀ to J₀)
        open Functor J' renaming (F₀ to J'₀)
        open NaturalTransformation j' renaming (η to j'⟨_⟩)
        open NaturalTransformation j renaming (η to j⟨_⟩)
        open NaturalTransformation f renaming (η to f⟨_⟩)
        open NaturalTransformation f' renaming (η to f'⟨_⟩)

⊗-IL : Bifunctor IL IL IL
⊗-IL = record
  { F₀           = uncurry ⊗₀-IL
  ; F₁           = uncurry ⊗₁-IL
  ; identity     = f-eq , f-eq
  ; homomorphism = homomorphism-IL
  ; F-resp-≈     = {! !}
  }
  where open Category C
        f-eq : {F : Endofunctor C} → (let open Functor F) →
               F₁ id ∘ id ≈  id
        f-eq = {! !}
        open import Function.Base using () renaming (_∘_ to _●_)

monoidal : Monoidal IL
monoidal = record
  { ⊗                    = ⊗-IL
  ; unit                 = unit
  ; unitorˡ              = {! !}
  ; unitorʳ              = {! !}
  ; associator           = {! !}
  ; unitorˡ-commute-from = {! !}
  ; unitorˡ-commute-to   = {! !}
  ; unitorʳ-commute-from = {! !}
  ; unitorʳ-commute-to   = {! !}
  ; assoc-commute-from   = {! !}
  ; assoc-commute-to     = {! !}
  ; triangle             = {! !}
  ; pentagon             = {! !}
  }
