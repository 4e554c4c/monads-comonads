{-# OPTIONS --without-K --allow-unsolved-metas --lossy-unification #-}
open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Product using (_⁂_; _⁂ⁿ_)
open import Categories.Functor using (Functor)
import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation using (NaturalTransformation; _∘ʳ_; _∘ˡ_; _∘ᵥ_; _∘ₕ_) renaming (id to idN)
open import NatEquiv using (_≃_; ≃-isEquivalence; module NatReasoning)
open import Categories.Functor using (Endofunctor) renaming (id to idF)
open import Relation.Binary using (Rel; IsEquivalence; Setoid)


open import Data.Product using (uncurry; uncurry′; Σ; _,_; _×_)
open import Level using (_⊔_) renaming (suc to lsuc)

module IL  {o ℓ e} {C : Category o ℓ e} (MC : Monoidal C) where

open import fil (MC) using (functor-functor-interaction-law)

open Monoidal MC using (⊗)

infix  4 _≃ᶠⁱˡ_ _⇒ᶠⁱˡ_
infixr 9 _∘ᶠⁱˡ_

record _⇒ᶠⁱˡ_ (f₁ f₂ : functor-functor-interaction-law) : Set (o ⊔ ℓ ⊔ e) where
  constructor F⟨_,_,_⟩
  open functor-functor-interaction-law f₁
  open functor-functor-interaction-law f₂ renaming (ϕ to Ψ; F to F'; G to G')
  field
    f : NaturalTransformation F F'
    g : NaturalTransformation G' G
    isMap : ϕ ∘ᵥ (⊗ ∘ˡ (idN ⁂ⁿ g)) ≃ Ψ ∘ᵥ (⊗ ∘ˡ (f ⁂ⁿ idN))

module C = Category C

id : ∀ {L : functor-functor-interaction-law} → L ⇒ᶠⁱˡ L
id = F⟨ idN , idN , refl ⟩
  where open IsEquivalence ≃-isEquivalence 


_∘ᶠⁱˡ_ : ∀ {f₁ f₂ f₃ : functor-functor-interaction-law} → f₂ ⇒ᶠⁱˡ  f₃ → f₁ ⇒ᶠⁱˡ  f₂ → f₁ ⇒ᶠⁱˡ  f₃
_∘ᶠⁱˡ_ {f₁} {f₂} {f₃} F⟨ f , g , eq ⟩ F⟨ f' , g' , eq' ⟩  = F⟨ f ∘ᵥ f' , g' ∘ᵥ g , begin
    ϕ ∘ᵥ ⊗ ∘ˡ (idN ⁂ⁿ g' ∘ᵥ g)                        ≈⟨ refl⟩∘ᵥ[ ⊗ ⇛ ⊗ ]⟨ refl⟩∘ˡ⟨ {! !} ⟩
    ϕ ∘ᵥ ⊗ ∘ˡ ((idN ⁂ⁿ g') ∘ᵥ (idN ⁂ⁿ g))             ≈⟨ refl⟩∘ᵥ[ ⊗ ⇛ ⊗ ]⟨ ∘ˡ-distr-∘ᵥ ⟩
    ϕ ∘ᵥ (⊗ ∘ˡ (idN ⁂ⁿ  g')) ∘ᵥ (⊗ ∘ˡ  (idN ⁂ⁿ  g))   ≈⟨ pullˡ eq' ○[ ⊗ ⇛ ⊗ ] ∘ᵥ-assoc ⟩
    Ψ ∘ᵥ (⊗ ∘ˡ (f'  ⁂ⁿ idN)) ∘ᵥ (⊗ ∘ˡ  (idN ⁂ⁿ  g))   ≈⟨ refl⟩∘ᵥ[ ⊗ ⇛ ⊗ ]⟨ {!⁂ⁿ-swap-∘ᵥ  !} ⟩
    Ψ ∘ᵥ (⊗ ∘ˡ (idN ⁂ⁿ   g)) ∘ᵥ (⊗ ∘ˡ  (f'  ⁂ⁿ  idN)) ≈⟨ pullˡ eq ○[ ⊗  ⇛ ⊗ ] ∘ᵥ-assoc ⟩
    Χ ∘ᵥ (⊗ ∘ˡ (f   ⁂ⁿ idN)) ∘ᵥ (⊗ ∘ˡ  (f'  ⁂ⁿ  idN))≈˘⟨ refl⟩∘ᵥ[ ⊗ ⇛ ⊗ ]⟨ {! !} ⟩
    Χ ∘ᵥ ⊗ ∘ˡ (f ∘ᵥ f' ⁂ⁿ idN)                     ∎
  ⟩
  where open functor-functor-interaction-law f₁ using (ϕ; F; G)
        open functor-functor-interaction-law f₂ renaming (ϕ to Ψ; F to F'; G to G')
        open functor-functor-interaction-law f₃ renaming (ϕ to Χ; F to F''; G to G'')
        open NatReasoning
        open import NatEquiv

_≃ᶠⁱˡ_ : ∀ {f₁ f₂ : functor-functor-interaction-law} → Rel (f₁ ⇒ᶠⁱˡ f₂) (o ⊔ ℓ ⊔ e)
F⟨ f , g , _ ⟩ ≃ᶠⁱˡ F⟨ f' , g' , _ ⟩ = (f ≃ f') × (g ≃ g')

--≃ᶠⁱˡ-isEquivalence : ∀ {f₁ f₂ : functor-functor-interaction-law} → IsEquivalence (_≃ᶠⁱˡ_  {f₁ = f₁} {f₂ = f₂})
--≃ᶠⁱˡ-isEquivalence {f₁} {f₂} = record
--  { refl  = refl , refl
--  ; sym   = λ { (e₁ , e₂) → sym e₁ , sym e₂ }
--  ; trans = λ { (e₁ , e₂) (e'₁ , e'₂) → trans e₁ e'₁ , trans e₂ e'₂ }
--  }
--  where open IsEquivalence ≃-isEquivalence

--module ≃ᶠⁱˡ-isEquivalence = IsEquivalence ≃ᶠⁱˡ-isEquivalence

--≃ᶠⁱˡ-setoid : ∀ (f₁ f₂ : functor-functor-interaction-law) → Setoid _ _
--≃ᶠⁱˡ-setoid f₁ f₂ = record
--  { Carrier       = f₁ ⇒ᶠⁱˡ  f₂
--  ; _≈_           = _≃ᶠⁱˡ_
--  ; isEquivalence = ≃ᶠⁱˡ-isEquivalence
--  }


assoc : ∀ {A B C D} {f : A ⇒ᶠⁱˡ B} {g : B ⇒ᶠⁱˡ C} {h : C ⇒ᶠⁱˡ D} → (h ∘ᶠⁱˡ g) ∘ᶠⁱˡ f ≃ᶠⁱˡ h ∘ᶠⁱˡ (g ∘ᶠⁱˡ f)
assoc = {! !} , {! !}


IL : Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e)
IL = record
  { Obj       = functor-functor-interaction-law
  ; _⇒_       = _⇒ᶠⁱˡ_
  ; _≈_       = _≃ᶠⁱˡ_
  ; id        = id
  ; _∘_       = _∘ᶠⁱˡ_
  ; assoc     = {! !} -- assoc
  ; sym-assoc = {! !} -- IsEquivalence.sym ≃ᶠⁱˡ-isEquivalence assoc
  ; identityˡ = {! !}
  ; identityʳ = {! !}
  ; identity² = {! !}
  ; equiv     = {! !} -- ≃ᶠⁱˡ-isEquivalence
  ; ∘-resp-≈  = {! !}
  }
