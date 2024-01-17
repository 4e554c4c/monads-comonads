{-# OPTIONS --without-K --allow-unsolved-metas --lossy-unification #-}
open import Categories.Category
open import Categories.Category.Monoidal using (Monoidal; monoidalHelper)

module IL.Monoidal  {o ℓ e} {C : Category o ℓ e} (MC : Monoidal C) where

import Categories.Morphism.Reasoning as MR
open Monoidal MC using (⊗)
open import Categories.Functor using (Functor; Endofunctor; _∘F_) renaming (id to idF)
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Categories.NaturalTransformation using (NaturalTransformation; _∘ʳ_; _∘ˡ_; _∘ᵥ_; _∘ₕ_; ntHelper) renaming (id to idN)
open import Categories.NaturalTransformation.Properties using (replaceˡ)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_ⓘᵥ_; _ⓘₕ_; _ⓘˡ_; _ⓘʳ_; associator; sym-associator) 
                                                                renaming (_≃_ to _≃ⁿ_; refl to reflⁿⁱ)
open import Categories.NaturalTransformation.Equivalence using (_≃_)
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
      { η = λ _ → C.id
      ; commute = λ f → id-comm-sym {f = _}
      }
  }
  where open MR C

-- unfortunately we don't have a definitional equality here, so we need to transport along a natural isomorphism
⊗₀-IL : functor-functor-interaction-law → functor-functor-interaction-law → functor-functor-interaction-law
⊗₀-IL L L' = FIL (F ∘F J) (G ∘F K) map
  where open functor-functor-interaction-law L
        open functor-functor-interaction-law L' renaming (ϕ to Ψ; F to J; G to K)
        map : NaturalTransformation (⊗ ∘F (F ∘F J ⁂ G ∘F K)) ⊗
        map = replaceˡ (Ψ ∘ᵥ ϕ ∘ʳ (J ⁂ K)) (associator (J ⁂ K) (F ⁂ G) ⊗)

module _ {A B D : Category o ℓ e} {F G H : Functor A B} {I J K : Functor B D}
    {α : NaturalTransformation F G} {β : NaturalTransformation G H}
    {δ : NaturalTransformation I J} {γ : NaturalTransformation J K} where
  private
    module α = NaturalTransformation α
    module β = NaturalTransformation β
    module δ = NaturalTransformation δ
    module γ = NaturalTransformation γ
    module D = Category D
    module K = Functor K
  --open MR D
  open Category.HomReasoning D
  open Functor F using (F₀)
  open Functor G using () renaming (F₀ to G₀)
  open Functor H using () renaming (F₀ to H₀)
  open Functor J using () renaming (F₁ to J₁)
  open Functor K using () renaming (F₁ to K₁)
  ≃-interchange : (γ ∘ᵥ δ) ∘ₕ (β ∘ᵥ α) ≃ (γ ∘ₕ β) ∘ᵥ (δ ∘ₕ α)
  ≃-interchange {x} = begin
      NaturalTransformation.η ((γ ∘ᵥ δ) ∘ₕ β ∘ᵥ α) x
      ≈⟨ D.Equiv.refl ⟩
      D [ K₁ (B [ β.η x ∘ α.η x ]) ∘ D [ γ.η (F₀ x) ∘ δ.η (F₀ x)] ]
      ≈⟨ K.homomorphism ⟩∘⟨refl ⟩
      D [ D [ K₁ (β.η     x) ∘ K₁ (α.η x) ]  ∘ D [ γ.η (F₀ x) ∘ δ.η (F₀ x)] ]
      ≈⟨ D.assoc ○ refl⟩∘⟨ D.sym-assoc ⟩
      D [ K₁ (β.η x)         ∘ D [ D [ K₁ (α.η x) ∘ γ.η (F₀ x) ] ∘ δ.η (F₀ x)] ]
      ≈⟨ refl⟩∘⟨ γ.sym-commute (α.η x) ⟩∘⟨refl ⟩
      D [ K₁ (β.η x)         ∘ D [ D [ γ.η (G₀ x) ∘ J₁ (α.η x) ] ∘ δ.η (F₀ x)] ]
      ≈˘⟨ D.assoc ○ refl⟩∘⟨ D.sym-assoc ⟩
      D [     D [ K₁ (β.η x) ∘ γ.η (G₀ x) ]  ∘ D [ J₁ (α.η x) ∘ δ.η (F₀ x)] ]
      ≈⟨ D.Equiv.refl ⟩
      NaturalTransformation.η ((γ ∘ₕ β) ∘ᵥ δ ∘ₕ α) x ∎

module _ where
  open import Categories.Category.Monoidal.Reasoning (MC)

  ⊗₁-IL : {L L' M M' : functor-functor-interaction-law} →
          (L ⇒ᶠⁱˡ L') → (M ⇒ᶠⁱˡ M') →
          IL [ ⊗₀-IL L M , ⊗₀-IL L' M' ]
  ⊗₁-IL {L} {L'} {M} {M'} F⟨ f , g , isMap₁ ⟩ F⟨ j , k , isMap₂ ⟩ = F⟨ f ∘ₕ j , g ∘ₕ k , (λ {(x , y)} → begin
      appN (_ ∘ᵥ ⊗ ∘ˡ (idN ⁂ⁿ g ∘ₕ k)) (x , y)
      ≈⟨ Equiv.refl ⟩
      ((appN Ψ (x , y) ∘ appN ϕ (J₀ x ,  K₀ y)) ∘ idC) ∘ (idC ⊗₁ (G₁ (appN k y) ∘ appN g (K'₀ y)))
      ≈⟨ pushˡ C.identityʳ ⟩
      appN Ψ  (x , y) ∘ appN ϕ (J₀ x  , K₀  y)         ∘ (idC ⊗₁ (G₁ (appN k y) ∘ appN g (K'₀ y)))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ split₂ʳ ⟩ -- slide down g
      appN Ψ  (x , y) ∘ appN ϕ (J₀ x  , K₀  y)         ∘ (idC ⊗₁ G₁ (appN k y))
                                                       ∘ (idC ⊗₁ appN g (K'₀ y))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ (Functor.identity F) ⟩⊗⟨refl ⟩∘⟨refl
       ○ refl⟩∘⟨ pullˡ (NaturalTransformation.commute ϕ _)
       ○ refl⟩∘⟨ C.assoc
       ⟩ -- slide up k
      appN Ψ  (x , y) ∘ (idC ⊗₁ (appN k y))  ∘ appN ϕ (J₀ x  , K'₀  y)
                                             ∘ (idC ⊗₁ appN g (K'₀ y))
      ≈⟨ pullˡ isMap₂ ○ C.assoc ⟩
      appN Ψ' (x , y) ∘ (appN j x ⊗₁ idC)  ∘ appN ϕ (J₀ x  , K'₀  y)
                                           ∘ (idC ⊗₁ appN g (K'₀ y))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ isMap₁ ⟩
      appN Ψ' (x , y) ∘ (appN j x ⊗₁ idC)  ∘ appN ϕ' (J₀ x  , K'₀  y)
                                           ∘ (appN f (J₀ x) ⊗₁ idC)
      ≈⟨ refl⟩∘⟨ pullˡ (NaturalTransformation.sym-commute ϕ' _) 
       ○ refl⟩∘⟨ C.assoc
       ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩⊗⟨ G'.identity ⟩∘⟨refl ⟩ -- slide down j
      appN Ψ' (x , y) ∘ appN ϕ' (J'₀ x , K'₀ y) ∘ (F'₁ (appN j x) ⊗₁ idC)
                                                ∘ (appN f (J₀ x)  ⊗₁ idC)
      ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ split₁ʳ ⟩ -- slide up f
      appN Ψ' (x , y) ∘ appN ϕ' (J'₀ x , K'₀ y) ∘ (F'₁ (appN j x) ∘ appN f (J₀ x)) ⊗₁ idC
      ≈˘⟨ pushˡ C.identityʳ ⟩
      ((appN Ψ' (x , y) ∘ appN ϕ' (J'₀ x , K'₀ y)) ∘ idC) ∘ (F'₁ (appN j x) ∘ appN f (J₀ x)) ⊗₁ idC
      ≈⟨ Equiv.refl ⟩
      appN (_ ∘ᵥ ⊗ ∘ˡ (f ∘ₕ j ⁂ⁿ idN)) (x , y)
      ∎
    )⟩
    where open functor-functor-interaction-law L  using (ϕ; F; G)
          open NaturalTransformation using () renaming (η to appN)
          open C renaming (id to idC)
          open Monoidal MC using (_⊗₁_)
          open MR C
          open functor-functor-interaction-law L' renaming (ϕ to ϕ'; F to F'; G to G')
          open functor-functor-interaction-law M  renaming (ϕ to Ψ; F to J; G to K)
          open functor-functor-interaction-law M' renaming (ϕ to Ψ'; F to J'; G to K')
          open Functor F' using () renaming (F₀ to F'₀; F₁ to F'₁)
          open Functor G  using () renaming (F₀ to G₀; F₁ to G₁)
          module G' = Functor G'
          open G' using () renaming (F₀ to G'₀; F₁ to G'₁)
          open Functor J  using () renaming (F₀ to J₀; F₁ to J₁)
          open Functor J' using () renaming (F₀ to J'₀; F₁ to J'₁)
          open Functor K  using () renaming (F₀ to K₀; F₁ to K₁)
          open Functor K' using () renaming (F₀ to K'₀; F₁ to K'₁)
  homomorphism-IL : (L L' L'' M M' M'' : functor-functor-interaction-law) →
                    (f : L ⇒ᶠⁱˡ L') → (j : M ⇒ᶠⁱˡ M') →
                    (f' : L' ⇒ᶠⁱˡ L'') → (j' : M' ⇒ᶠⁱˡ M'') → (let open Category IL) →
                    ⊗₁-IL (f' ∘ f) (j' ∘ j) ≈ ⊗₁-IL f' j' ∘ ⊗₁-IL f j
  homomorphism-IL L L' L'' M M' M'' F⟨ f , g , _ ⟩ F⟨ j , k , _ ⟩ F⟨ f' , g' , _ ⟩  F⟨ j' , k' , _ ⟩ =
      ≃-interchange {α = j} {β = j'} {δ = f} {γ = f'}  , ≃-interchange {α = k'} {β = k} {δ = g'} {γ = g}

module _ {F : Endofunctor C} where
  open Functor F
  open Category C
  open MR C
  open HomReasoning
  f-eq : {A : Obj} → F₁ {A} id ∘ id ≈ id
  f-eq = begin F₁ id ∘ id ≈⟨ identity ⟩∘⟨refl ⟩
               id    ∘ id ≈⟨ C.identity² ⟩
               id         ∎

⊗-IL : Bifunctor IL IL IL
⊗-IL = record
  { F₀           = uncurry ⊗₀-IL
  ; F₁           = uncurry ⊗₁-IL
  ; identity     = λ {(FIL F G _ , FIL J K _)} → (λ {x} → f-eq {F = F} {A = Functor.F₀ J x}) , λ {x} → f-eq {F = G} {A = Functor.F₀ K x}
  ; homomorphism = λ {(L , M)} {(L' , M')} {(L'' , M'')} {(F⟨ f , g , _ ⟩ , F⟨ j , k , _ ⟩)} {(F⟨ f' , g' , _ ⟩  , F⟨ j' , k' , _ ⟩)}
                    -- i guess it's cleaner to copy-paste homomorphism-IL above here
                     → ≃-interchange {α = j} {β = j'} {δ = f} {γ = f'}  , ≃-interchange {α = k'} {β = k} {δ = g'} {γ = g}
  ; F-resp-≈     = λ { {A = (FIL F G _ , FIL F' G' _)} {B = (FIL M N _ , FIL M' N' _)} {f = (f₁ , f₂)} {g = (g₁ , g₂)} ((e₁₁ , e₁₂) , (e₂₁ , e₂₂)) 
                     → (Functor.F-resp-≈ M e₂₁ ⟩∘⟨ e₁₁) , (Functor.F-resp-≈ G e₂₂ ⟩∘⟨ e₁₂) }
  }
  where open Category C
        open HomReasoning

monoidal : Monoidal IL
monoidal = monoidalHelper IL record
  { ⊗               = ⊗-IL
  ; unit            = unit
  ; unitorˡ         = {! !}
  ; unitorʳ         = {! !}
  ; associator      = {! !}
  ; unitorˡ-commute = {! !}
  ; unitorʳ-commute = {! !}
  ; assoc-commute   = {! !}
  ; triangle        = {! !}
  ; pentagon        = {! !}
  }
