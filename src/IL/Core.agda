{-# OPTIONS --without-K --safe --lossy-unification #-}
open import Prelude
open import Categories.Category.Product renaming (Product to ProductCat)
open import Relation.Binary using (Rel; IsEquivalence; Setoid)

module IL.Core  {o ℓ e} {C : Category o ℓ e} (MC : Monoidal C) where

open import fil (MC) using (FIL; FIL[_,_,_])

open Monoidal MC using (⊗)

infix  4 _≃ᶠⁱˡ_ _⇒ᶠⁱˡ_

isFILM : (f₁ f₂ : FIL) → (let open FIL f₁) →
         (let open FIL f₂ renaming (ϕ to ψ; F to F'; G to G')) →
         (NaturalTransformation F F') → (NaturalTransformation G' G) → Set _
isFILM FIL[ _ , _ , ϕ ] FIL[ _ , _ , ψ ] f g =
  ϕ ∘ᵥ (⊗ ∘ˡ (idN ⁂ⁿ g)) ≃ ψ ∘ᵥ (⊗ ∘ˡ (f ⁂ⁿ idN))

record _⇒ᶠⁱˡ_ (f₁ f₂ : FIL) : Set (o ⊔ ℓ ⊔ e) where
  constructor FILM⟨_,_,_⟩
  open FIL f₁
  open FIL f₂ renaming (ϕ to ψ; F to F'; G to G')
  field
    f : NaturalTransformation F F'
    g : NaturalTransformation G' G
    isMap : isFILM f₁ f₂ f g

-- helps a lot with performance
{-# INLINE FILM⟨_,_,_⟩ #-}

private
  module C = Category C

module _ where
  infixr 9 _∘ᶠⁱˡ_
  open _⇒ᶠⁱˡ_

  id : ∀ {L : FIL} → L ⇒ᶠⁱˡ L
  id .f = idN
  id .g = idN
  id .isMap = C.Equiv.refl

  --syntax _∘ᶠⁱˡ_ {A} {B}{C} f g = [ A -> B ][ f ][ g ]
  _∘ᶠⁱˡ_ : ∀ {f₁ f₂ f₃ : FIL} → f₂ ⇒ᶠⁱˡ  f₃ → f₁ ⇒ᶠⁱˡ  f₂ → f₁ ⇒ᶠⁱˡ  f₃
  (FILM⟨ f , g , _ ⟩ ∘ᶠⁱˡ  FILM⟨ f' , g' , _ ⟩) .f = f ∘ᵥ f'
  (FILM⟨ f , g , _ ⟩ ∘ᶠⁱˡ  FILM⟨ f' , g' , _ ⟩) .g = g' ∘ᵥ g
  _∘ᶠⁱˡ_ {f₁} {f₂} {f₃} FILM⟨ f , g , eq ⟩ FILM⟨ f' , g' , eq' ⟩ .isMap {x} = begin
      (ϕ ∘ᵥ ⊗ ∘ˡ (idN ⁂ⁿ g' ∘ᵥ g)) .η x    ≈⟨ Equiv.refl ⟩
      ϕ.η x ∘ (idC ⊗₁ (g' .η (π₂ x) ∘
                         g .η (π₂ x)))    ≈⟨ refl⟩∘⟨ split₂ˡ ⟩
      ϕ .η x ∘ (idC ⊗₁ (g' .η (π₂ x)))
               ∘ (idC ⊗₁ (g .η  (π₂ x)))   ≈⟨ extendʳ eq' ⟩
      ψ .η x ∘ ((f' .η (π₁ x)) ⊗₁ idC)
               ∘ (idC ⊗₁ (g .η  (π₂ x)))   ≈⟨ refl⟩∘⟨ (Equiv.sym serialize₁₂ ○ serialize₂₁) ⟩
      ψ .η x ∘ (idC ⊗₁ (g .η  (π₂ x)))
               ∘ ((f' .η (π₁ x)) ⊗₁ idC)   ≈⟨ extendʳ eq ⟩
      Χ .η x ∘ ((f .η  (π₁ x)) ⊗₁ idC)
               ∘ ((f' .η (π₁ x)) ⊗₁ idC)  ≈˘⟨ refl⟩∘⟨ split₁ˡ ⟩
      Χ .η x ∘ ((f .η  (π₁ x) ∘
                   f' .η (π₁ x)) ⊗₁ idC)   ≈⟨ Equiv.refl ⟩
      (Χ ∘ᵥ ⊗ ∘ˡ (f ∘ᵥ f' ⁂ⁿ idN)) .η x       ∎
    where open FIL f₁ using (ϕ; F; G)
          open FIL f₂ renaming (ϕ to ψ; F to F'; G to G')
          open FIL f₃ renaming (ϕ to Χ; F to F''; G to G'')
          open NaturalTransformation using (η)
          module ϕ = NaturalTransformation ϕ
          open C renaming (id to idC)
          open MR C
          open import Data.Product renaming (proj₁ to π₁; proj₂ to π₂)
          open Monoidal MC using (_⊗₁_)
          open import Categories.Category.Monoidal.Reasoning (MC) 

_≃ᶠⁱˡ_ : ∀ {f₁ f₂ : FIL} → Rel (f₁ ⇒ᶠⁱˡ f₂) (o ⊔ e)
FILM⟨ f , g , _ ⟩ ≃ᶠⁱˡ FILM⟨ f' , g' , _ ⟩ = (f ≃ f') × (g ≃ g')

≃ᶠⁱˡ-isEquivalence : ∀ {f₁ f₂ : FIL} → IsEquivalence (_≃ᶠⁱˡ_  {f₁ = f₁} {f₂ = f₂})
≃ᶠⁱˡ-isEquivalence {f₁} {f₂} = record
  { refl  = refl , refl
  ; sym   = λ { (e₁ , e₂) → sym e₁ , sym e₂ }
  ; trans = λ { (e₁ , e₂) (e'₁ , e'₂) → trans e₁ e'₁ , trans e₂ e'₂ }
  }
  where open C.Equiv

≃ᶠⁱˡ-setoid : ∀ (f₁ f₂ : FIL) → Setoid _ _
≃ᶠⁱˡ-setoid f₁ f₂ = record
  { Carrier       = f₁ ⇒ᶠⁱˡ  f₂
  ; _≈_           = _≃ᶠⁱˡ_
  ; isEquivalence = ≃ᶠⁱˡ-isEquivalence
  }

private module isCategory where
  assoc : ∀ {A B C D} {f : A ⇒ᶠⁱˡ B} {g : B ⇒ᶠⁱˡ C} {h : C ⇒ᶠⁱˡ D} → (h ∘ᶠⁱˡ g) ∘ᶠⁱˡ f ≃ᶠⁱˡ h ∘ᶠⁱˡ (g ∘ᶠⁱˡ f)
  assoc = C.assoc , C.sym-assoc

  sym-assoc : ∀ {A B C D} {f : A ⇒ᶠⁱˡ B} {g : B ⇒ᶠⁱˡ C} {h : C ⇒ᶠⁱˡ D} → h ∘ᶠⁱˡ (g ∘ᶠⁱˡ f) ≃ᶠⁱˡ (h ∘ᶠⁱˡ g) ∘ᶠⁱˡ f
  sym-assoc = C.sym-assoc , C.assoc

  identityˡ : ∀{A B} {f : A ⇒ᶠⁱˡ B} → id ∘ᶠⁱˡ f ≃ᶠⁱˡ f
  identityˡ = C.identityˡ , C.identityʳ

  identityʳ : ∀{A B} {f : A ⇒ᶠⁱˡ B} → f ∘ᶠⁱˡ id ≃ᶠⁱˡ f
  identityʳ = C.identityʳ , C.identityˡ

  identity² : ∀{A} → id ∘ᶠⁱˡ id {A} ≃ᶠⁱˡ id
  identity² = identityˡ

  ∘-resp-≈ : {A B C : FIL}
             {f h : B ⇒ᶠⁱˡ C} {g i : A ⇒ᶠⁱˡ B} →
             f ≃ᶠⁱˡ h → g ≃ᶠⁱˡ i → f ∘ᶠⁱˡ g ≃ᶠⁱˡ h ∘ᶠⁱˡ i
  ∘-resp-≈ (e₁ , e₂) (e'₁ , e'₂) = (e₁ ⟩∘⟨ e'₁) ,  (e'₂ ⟩∘⟨ e₂)
    where open C.Equiv
          open MR C
          open C.HomReasoning

IL : Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) (o ⊔ e)
IL = record
  { Obj       = FIL
  ; _⇒_       = _⇒ᶠⁱˡ_
  ; _≈_       = _≃ᶠⁱˡ_
  ; id        = id
  ; _∘_       = _∘ᶠⁱˡ_
  ; equiv     = ≃ᶠⁱˡ-isEquivalence
  ; isCategory
  }
