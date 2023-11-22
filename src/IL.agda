{-# OPTIONS --without-K --allow-unsolved-metas --lossy-unification #-}
open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Product using (_⁂_; _⁂ⁿ_) renaming (Product to ProductCat)
open import Categories.Functor using (Functor)
import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation using (NaturalTransformation; _∘ʳ_; _∘ˡ_; _∘ᵥ_; _∘ₕ_) renaming (id to idN)
open import Categories.NaturalTransformation.Equivalence using (_≃_; ≃-isEquivalence)
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
id {L} = F⟨ idN , idN , C.Equiv.refl  ⟩

_∘ᶠⁱˡ_ : ∀ {f₁ f₂ f₃ : functor-functor-interaction-law} → f₂ ⇒ᶠⁱˡ  f₃ → f₁ ⇒ᶠⁱˡ  f₂ → f₁ ⇒ᶠⁱˡ  f₃
_∘ᶠⁱˡ_ {f₁} {f₂} {f₃} F⟨ f , g , eq ⟩ F⟨ f' , g' , eq' ⟩  = F⟨ f ∘ᵥ f' , g' ∘ᵥ g , (λ {x} → begin
    appN (ϕ ∘ᵥ ⊗ ∘ˡ (idN ⁂ⁿ g' ∘ᵥ g)) x    ≈⟨ Equiv.refl ⟩
    appN ϕ x ∘ (idC ⊗₁ (appN g' (π₂ x) ∘
                        appN g (π₂ x)))    ≈⟨ refl⟩∘⟨ split₂ˡ ⟩
    appN ϕ x ∘ (idC ⊗₁ (appN g' (π₂ x)))
             ∘ (idC ⊗₁ (appN g  (π₂ x)))   ≈⟨ pullˡ eq' ○ assoc ⟩
    appN Ψ x ∘ ((appN f' (π₁ x)) ⊗₁ idC)
             ∘ (idC ⊗₁ (appN g  (π₂ x)))   ≈⟨ refl⟩∘⟨ (Equiv.sym serialize₁₂ ○ serialize₂₁) ⟩
    appN Ψ x ∘ (idC ⊗₁ (appN g  (π₂ x)))
             ∘ ((appN f' (π₁ x)) ⊗₁ idC)   ≈⟨ (pullˡ eq ○ assoc) ⟩
    appN Χ x ∘ ((appN f  (π₁ x)) ⊗₁ idC)
             ∘ ((appN f' (π₁ x)) ⊗₁ idC)  ≈˘⟨ refl⟩∘⟨ split₁ˡ ⟩
    appN Χ x ∘ ((appN f  (π₁ x) ∘
                 appN f' (π₁ x)) ⊗₁ idC)   ≈⟨ Equiv.refl ⟩
    appN (Χ ∘ᵥ ⊗ ∘ˡ (f ∘ᵥ f' ⁂ⁿ idN)) x       ∎
  )⟩
  where open functor-functor-interaction-law f₁ using (ϕ; F; G)
        open functor-functor-interaction-law f₂ renaming (ϕ to Ψ; F to F'; G to G')
        open functor-functor-interaction-law f₃ renaming (ϕ to Χ; F to F''; G to G'')
        open NaturalTransformation using () renaming (η to appN)
        open C renaming (id to idC)
        open MR C
        open Data.Product renaming (proj₁ to π₁; proj₂ to π₂)
        open Monoidal MC using (_⊗₁_)
        open import Categories.Category.Monoidal.Reasoning (MC) 

_≃ᶠⁱˡ_ : ∀ {f₁ f₂ : functor-functor-interaction-law} → Rel (f₁ ⇒ᶠⁱˡ f₂) (o ⊔ e)
F⟨ f , g , _ ⟩ ≃ᶠⁱˡ F⟨ f' , g' , _ ⟩ = (f ≃ f') × (g ≃ g')

≃ᶠⁱˡ-isEquivalence : ∀ {f₁ f₂ : functor-functor-interaction-law} → IsEquivalence (_≃ᶠⁱˡ_  {f₁ = f₁} {f₂ = f₂})
≃ᶠⁱˡ-isEquivalence {f₁} {f₂} = record
  { refl  = refl , refl
  ; sym   = λ { (e₁ , e₂) → sym e₁ , sym e₂ }
  ; trans = λ { (e₁ , e₂) (e'₁ , e'₂) → trans e₁ e'₁ , trans e₂ e'₂ }
  }
  where open C.Equiv

≃ᶠⁱˡ-setoid : ∀ (f₁ f₂ : functor-functor-interaction-law) → Setoid _ _
≃ᶠⁱˡ-setoid f₁ f₂ = record
  { Carrier       = f₁ ⇒ᶠⁱˡ  f₂
  ; _≈_           = _≃ᶠⁱˡ_
  ; isEquivalence = ≃ᶠⁱˡ-isEquivalence
  }

assoc : ∀ {A B C D} {f : A ⇒ᶠⁱˡ B} {g : B ⇒ᶠⁱˡ C} {h : C ⇒ᶠⁱˡ D} → (h ∘ᶠⁱˡ g) ∘ᶠⁱˡ f ≃ᶠⁱˡ h ∘ᶠⁱˡ (g ∘ᶠⁱˡ f)
assoc = C.assoc , C.sym-assoc

sym-assoc : ∀ {A B C D} {f : A ⇒ᶠⁱˡ B} {g : B ⇒ᶠⁱˡ C} {h : C ⇒ᶠⁱˡ D} → h ∘ᶠⁱˡ (g ∘ᶠⁱˡ f) ≃ᶠⁱˡ (h ∘ᶠⁱˡ g) ∘ᶠⁱˡ f
sym-assoc = C.sym-assoc , C.assoc

identityˡ : ∀{A B} {f : A ⇒ᶠⁱˡ B} → id ∘ᶠⁱˡ f ≃ᶠⁱˡ f
identityˡ = C.identityˡ , C.identityʳ

identityʳ : ∀{A B} {f : A ⇒ᶠⁱˡ B} → f ∘ᶠⁱˡ id ≃ᶠⁱˡ f
identityʳ = C.identityʳ , C.identityˡ

∘-resp-≈ : {A B C : functor-functor-interaction-law}
           {f h : B ⇒ᶠⁱˡ C} {g i : A ⇒ᶠⁱˡ B} →
           f ≃ᶠⁱˡ h → g ≃ᶠⁱˡ i → f ∘ᶠⁱˡ g ≃ᶠⁱˡ h ∘ᶠⁱˡ i
∘-resp-≈ (e₁ , e₂) (e'₁ , e'₂) = (e₁ ⟩∘⟨ e'₁) ,  (e'₂ ⟩∘⟨ e₂)
  where open C.Equiv
        open MR C
        open C.HomReasoning

IL : Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) (o ⊔ e)
IL = record
  { Obj       = functor-functor-interaction-law
  ; _⇒_       = _⇒ᶠⁱˡ_
  ; _≈_       = _≃ᶠⁱˡ_
  ; id        = id
  ; _∘_       = _∘ᶠⁱˡ_
  ; assoc     = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identityˡ
  ; equiv     = ≃ᶠⁱˡ-isEquivalence
  ; ∘-resp-≈  = ∘-resp-≈
  }
