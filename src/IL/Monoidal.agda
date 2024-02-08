{-# OPTIONS --without-K --lossy-unification --hidden-argument-puns #-}
open import Categories.Category
open import Categories.Category.Monoidal using (Monoidal; monoidalHelper)

module IL.Monoidal  {o ℓ e} {C : Category o ℓ e} (MC : Monoidal C) where

import Categories.Morphism.Reasoning as MR
open Monoidal MC using (⊗; _⊗₀_; _⊗₁_)
open import Categories.Functor using (Functor; Endofunctor; _∘F_) renaming (id to idF)
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Categories.NaturalTransformation using (NaturalTransformation; _∘ʳ_; _∘ˡ_; _∘ᵥ_; _∘ₕ_; ntHelper) renaming (id to idN)
open import Categories.NaturalTransformation.Properties using (replaceˡ)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_ⓘᵥ_; _ⓘₕ_; _ⓘˡ_; _ⓘʳ_; associator; sym-associator) 
                                                                renaming (_≃_ to _≃ⁿ_; refl to reflⁿⁱ)
open import Categories.NaturalTransformation.Equivalence using (_≃_)
open import IL.Core (MC) renaming (id to idIL) using (IL; F⟨_,_,_⟩; _⇒ᶠⁱˡ_)
open import fil (MC) using (functor-functor-interaction-law; FIL)
open import Data.Product using (uncurry; uncurry′; Σ; _,_; _×_)
open import Categories.Category.Product using (_⁂_; _⁂ⁿ_) renaming (Product to ProductCat)

private
  module C = Category C
  module C² = Category (ProductCat C C)

module MC = Monoidal MC

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

infixr 10 _⊗L₀_

-- unfortunately we don't have a definitional equality here, so we need to transport along a natural isomorphism
_⊗L₀_ : functor-functor-interaction-law → functor-functor-interaction-law → functor-functor-interaction-law
L ⊗L₀ L' = FIL (F ∘F J) (G ∘F K) map
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
  infixr 10 _⊗L₁_

  _⊗L₁_ : {L L' M M' : functor-functor-interaction-law} →
          (L ⇒ᶠⁱˡ L') → (M ⇒ᶠⁱˡ M') →
          IL [ L ⊗L₀ M , L' ⊗L₀ M' ]
  _⊗L₁_ {L} {L'} {M} {M'} F⟨ f , g , isMap₁ ⟩ F⟨ j , k , isMap₂ ⟩ = F⟨ f ∘ₕ j , g ∘ₕ k , (λ {(x , y)} → begin
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
  homomorphism-IL : (L L' L'' M M' M'' : functor-functor-interaction-law)
                  → (f : L ⇒ᶠⁱˡ L') → (j : M ⇒ᶠⁱˡ M')
                  → (f' : L' ⇒ᶠⁱˡ L'') → (j' : M' ⇒ᶠⁱˡ M'')
                  → (let open Category IL) 
                  → (f' ∘ f) ⊗L₁ (j' ∘ j) ≈ f' ⊗L₁ j' ∘ f ⊗L₁ j
  homomorphism-IL L L' L'' M M' M'' F⟨ f , g , _ ⟩ F⟨ j , k , _ ⟩ F⟨ f' , g' , _ ⟩  F⟨ j' , k' , _ ⟩ =
      ≃-interchange {α = j} {β = j'} {δ = f} {γ = f'}  , ≃-interchange {α = k'} {β = k} {δ = g'} {γ = g}

module _ {F : Endofunctor C} where
  open Functor F
  open Category C
  open MR C
  open import Categories.Category.Monoidal.Reasoning (MC)
  f-eq : {A : Obj} → F₁ {A} id ∘ id ≈ id
  f-eq = begin F₁ id ∘ id ≈⟨ identity ⟩∘⟨refl ⟩
               id    ∘ id ≈⟨ C.identity² ⟩
               id         ∎

⊗-IL : Bifunctor IL IL IL
⊗-IL = record
  { F₀           = uncurry _⊗L₀_
  ; F₁           = uncurry _⊗L₁_
  ; identity     = λ {(FIL F G _ , FIL J K _)} → (λ {x} → f-eq {F = F} {A = Functor.F₀ J x}) , λ {x} → f-eq {F = G} {A = Functor.F₀ K x}
  ; homomorphism = λ {_} {_} {_} {(F⟨ f , g , _ ⟩ , F⟨ j , k , _ ⟩)} {(F⟨ f' , g' , _ ⟩  , F⟨ j' , k' , _ ⟩)}
                    -- i guess it's cleaner to copy-paste homomorphism-IL above here
                     → ≃-interchange {α = j} {β = j'} {δ = f} {γ = f'}  , ≃-interchange {α = k'} {β = k} {δ = g'} {γ = g}
  ; F-resp-≈     = λ { {A = (FIL F G _ , FIL F' G' _)} {B = (FIL M N _ , FIL M' N' _)} {f = (f₁ , f₂)} {g = (g₁ , g₂)} ((e₁₁ , e₁₂) , (e₂₁ , e₂₂))
                     → (Functor.F-resp-≈ M e₂₁ ⟩∘⟨ e₁₁) , (Functor.F-resp-≈ G e₂₂ ⟩∘⟨ e₁₂) }
  }
  where open Category C
        open HomReasoning

module _ where

  open import Categories.Morphism IL using (_≅_; Iso)

  open import Categories.NaturalTransformation.NaturalIsomorphism renaming (_≃_ to _≃ⁿ_)

  open Category C
  open MR C
  open import Categories.Category.Monoidal.Reasoning (MC)
  open NaturalTransformation using () renaming (η to appN)
  NatIso⇒ILIso : ∀ {L M : functor-functor-interaction-law}
            (let open functor-functor-interaction-law L)
            (let open functor-functor-interaction-law M renaming (ϕ to Ψ; F to F'; G to G'))
            (F≃F' : F ≃ⁿ F')
            (G≃G' : G' ≃ⁿ G)
            (let open NaturalIsomorphism F≃F'  renaming (F⇒G to F⇒F';F⇐G to F⇐F'; module iso to iso₁))
            (let open NaturalIsomorphism G≃G'  renaming (F⇒G to G'⇒G;F⇐G to G'⇐G; module iso to iso₂))
            (isMap₁ : (ϕ ∘ᵥ ⊗ ∘ˡ (idN ⁂ⁿ G'⇒G)) ≃ (Ψ ∘ᵥ ⊗ ∘ˡ (F⇒F' ⁂ⁿ idN)))
            --(isMap₂ : (Ψ  ∘ᵥ ⊗ ∘ˡ (idN ⁂ⁿ G'⇐G)) ≃ (ϕ ∘ᵥ ⊗ ∘ˡ (F⇐F' ⁂ⁿ idN)))
          → L ≅  M
  NatIso⇒ILIso {L} {M} F≃F' G≃G' isMap₁ = record
    { from = record
      { f     = F⇒F'
      ; g     = G'⇒G
      ; isMap = isMap₁
      }
    ; to = record
      { f     = F⇐F'
      ; g     = G'⇐G
      ; isMap = isMap₂
      }
    ; iso = record
      { isoˡ = F≃F'.iso.isoˡ _ , G≃G'.iso.isoʳ _
      ; isoʳ = F≃F'.iso.isoʳ _ , G≃G'.iso.isoˡ _
      }
    }
    where open functor-functor-interaction-law L
          open functor-functor-interaction-law M renaming (ϕ to Ψ; F to F'; G to G')
          open NaturalIsomorphism F≃F' renaming (F⇒G to F⇒F';F⇐G to F⇐F'; module iso to iso₁)
          open NaturalIsomorphism G≃G' renaming (F⇒G to G'⇒G;F⇐G to G'⇐G; module iso to iso₂)
          module F≃F' = NaturalIsomorphism F≃F'
          module G≃G' = NaturalIsomorphism G≃G'
          isMap₂ : (Ψ  ∘ᵥ ⊗ ∘ˡ (idN ⁂ⁿ G'⇐G)) ≃ (ϕ ∘ᵥ ⊗ ∘ˡ (F⇐F' ⁂ⁿ idN))
          isMap₂ {(x , y)} = begin
            appN (Ψ ∘ᵥ ⊗ ∘ˡ (idN ⁂ⁿ G'⇐G)) (x , y)
            ≈⟨ refl⟩∘⟨ Equiv.sym (F≃F'.iso.isoʳ _) ⟩⊗⟨refl ⟩
            appN (Ψ ∘ᵥ ⊗ ∘ˡ ((F⇒F' ∘ᵥ F⇐F') ⁂ⁿ G'⇐G) ) (x , y)
            ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ ⟺ identityˡ ⟩
            appN (Ψ ∘ᵥ ⊗ ∘ˡ (F⇒F' ⁂ⁿ idN)  ∘ᵥ (F⇐F' ⁂ⁿ G'⇐G)) (x , y)
            ≈⟨ refl⟩∘⟨ ⊗-distrib-over-∘
             ○ pullˡ (⟺ isMap₁) ○ assoc
             ○ refl⟩∘⟨ ⟺ ⊗-distrib-over-∘ ⟩ -- isMap₁
            appN (ϕ ∘ᵥ ⊗ ∘ˡ (idN ⁂ⁿ G'⇒G) ∘ᵥ (F⇐F' ⁂ⁿ G'⇐G)) (x , y)
            ≈⟨ refl⟩∘⟨ identityˡ ⟩⊗⟨refl ⟩
            appN (ϕ  ∘ᵥ ⊗ ∘ˡ (F⇐F'  ⁂ⁿ (G'⇒G ∘ᵥ G'⇐G))) (x , y)
            ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ G≃G'.iso.isoʳ _ ⟩
            appN (ϕ  ∘ᵥ ⊗ ∘ˡ (F⇐F'  ⁂ⁿ idN)) (x , y)
            ∎

  unitorˡ-IL : {X : functor-functor-interaction-law} → unit ⊗L₀ X ≅ X
  unitorˡ-IL {X} = NatIso⇒ILIso unitorˡ (sym unitorˡ) λ {x} → begin
      ((appN ϕ x ∘ id) ∘ id) ∘ (id ⊗₁ id)
      ≈⟨ (identityʳ ○ identityʳ) ⟩∘⟨refl ⟩
      appN ϕ x ∘ (id ⊗₁ id)
      ∎
    where open functor-functor-interaction-law X

  unitorʳ-IL : {X : functor-functor-interaction-law} → X ⊗L₀ unit ≅ X
  unitorʳ-IL {X} = NatIso⇒ILIso unitorʳ (sym unitorʳ) λ {x} → begin
      (((id ∘ appN ϕ x)) ∘ id) ∘ (id ⊗₁ id)
      ≈⟨ (identityʳ ○ identityˡ) ⟩∘⟨refl ⟩
      appN ϕ x ∘ (id ⊗₁ id)
      ∎
    where open functor-functor-interaction-law X

  associator-IL : {X Y Z : functor-functor-interaction-law} → (X ⊗L₀ Y) ⊗L₀ Z ≅ X ⊗L₀ (Y ⊗L₀ Z)
  associator-IL {X} {Y} {Z} = NatIso⇒ILIso (associator _ _ _) (sym-associator _ _ _) λ {(x , y)} → begin
      ((appN Χ (x , y) ∘ (appN Ψ (F''₀ x , G''₀ y) ∘ appN ϕ (F'₀ (F''₀ x) , G'₀ (G''₀ y))) ∘ id) ∘ id) ∘ (id ⊗₁ id)
      ≈⟨ (identityʳ ○ refl⟩∘⟨ identityʳ) ⟩∘⟨refl ⟩
      (appN Χ (x , y) ∘ appN Ψ (F''₀ x , G''₀ y) ∘ appN ϕ (F'₀ (F''₀ x) , G'₀ (G''₀ y))) ∘ (id ⊗₁ id)
      ≈⟨ Equiv.sym identityʳ ⟩∘⟨refl
       ○ sym-assoc ⟩∘⟨refl ⟩∘⟨refl
       ○ (refl⟩∘⟨ ⟺ identityˡ) ⟩∘⟨refl ⟩∘⟨refl
       ○ sym-assoc ⟩∘⟨refl ⟩∘⟨refl ⟩
      ((((appN Χ (x , y) ∘ appN Ψ (F''₀ x , G''₀ y)) ∘ id) ∘ appN ϕ (F'₀ (F''₀ x) , G'₀ (G''₀ y))) ∘ id) ∘ (id ⊗₁ id)
      ∎
    where open functor-functor-interaction-law X
          open functor-functor-interaction-law Y renaming (ϕ to Ψ; F to F'; G to G')
          open functor-functor-interaction-law Z renaming (ϕ to Χ; F to F''; G to G'')
          open Functor F using (F₀; F₁)
          open Functor F' using () renaming (F₀ to F'₀; F₁ to F'₁)
          open Functor G' using () renaming (F₀ to G'₀; F₁ to G'₁)
          open Functor F'' using () renaming (F₀ to F''₀; F₁ to F''₁)
          open Functor G'' using () renaming (F₀ to G''₀; F₁ to G''₁)

  open Definitions IL
  module unitorˡ-IL {X} = _≅_ (unitorˡ-IL {X = X})
  module unitorʳ-IL {X} = _≅_ (unitorʳ-IL {X = X})
  module associator-IL {X} {Y} {Z} = _≅_ (associator-IL {X} {Y} {Z})

  unitorʳ-commute : ∀{L M} {f : L ⇒ᶠⁱˡ M} →
                    CommutativeSquare (f ⊗L₁ idIL) unitorʳ-IL.from unitorʳ-IL.from f
  unitorʳ-commute {L} {M} {f = 𝒻} = (λ {x} → begin
      id ∘ J.₁ id ∘ appN f x
      ≈⟨ identityˡ ⟩
      J.₁ id ∘ appN f x
      ≈⟨ J.identity ⟩∘⟨refl ○ identityˡ ○ ⟺ identityʳ ⟩
      appN f x ∘ id
      ∎)  , λ {x} → begin
      (G.₁ id ∘ appN g x) ∘ id
      ≈⟨ identityʳ ○ G.identity ⟩∘⟨refl ⟩
      id ∘ appN g x
      ∎
    where open _⇒ᶠⁱˡ_ 𝒻
          open functor-functor-interaction-law L using (F; G)
          open functor-functor-interaction-law M using () renaming (F to J; G to K)
          module F = Functor F
          module G = Functor G
          module J = Functor J

  assoc-commute : ∀{L M}  {f : L ⇒ᶠⁱˡ M} {L' M'} {g : L' ⇒ᶠⁱˡ M'} {L'' M''}  {h : L'' ⇒ᶠⁱˡ M''} →
                  CommutativeSquare ((f ⊗L₁ g) ⊗L₁ h) associator-IL.from associator-IL.from (f ⊗L₁ (g ⊗L₁ h))
  assoc-commute {L} {M} {f = f1} {L'} {M'} {g = f2} {L''} {M''} {h = f3} = (λ {x} → begin
      id ∘ J.₁ (J'.₁ (appN f'' x)) ∘ J.₁ (appN f' (F''.₀ x)) ∘ appN f (F'.₀ (F''.₀ x))
      ≈⟨ identityˡ ⟩
      J.₁ (J'.₁ (appN f'' x)) ∘ J.₁ (appN f' (F''.₀ x)) ∘ appN f (F'.₀ (F''.₀ x))
      ≈⟨ pullˡ (⟺ J.homomorphism) ⟩
      J.₁ (J'.₁ (appN f'' x) ∘ (appN f' (F''.₀ x))) ∘ appN f (F'.₀ (F''.₀ x))
      ≈⟨ ⟺ identityʳ ⟩
      (J.₁ (J'.₁ (appN f'' x) ∘ appN f' (F''.₀ x)) ∘ appN f (F'.₀ (F''.₀ x))) ∘ id
      ∎)  , λ {x} → begin
      (G.₁ (G'.₁ (appN g'' x)) ∘ G.₁ (appN g' (K''.₀ x)) ∘ appN g (K'.₀ (K''.₀ x))) ∘ id
      ≈⟨ identityʳ ⟩
      G.₁ (G'.₁ (appN g'' x)) ∘ G.₁ (appN g' (K''.₀ x)) ∘ appN g (K'.₀ (K''.₀ x))
      ≈⟨ pullˡ (⟺ G.homomorphism) ⟩
      G.₁ (G'.₁ (appN g'' x) ∘ (appN g' (K''.₀ x))) ∘ appN g (K'.₀ (K''.₀ x))
      ≈⟨ ⟺ identityˡ ⟩
      id ∘ G.₁ (G'.₁ (appN g'' x) ∘ appN g' (K''.₀ x)) ∘ appN g (K'.₀ (K''.₀ x))
      ∎
    where open _⇒ᶠⁱˡ_ f1 using (f; g)
          open _⇒ᶠⁱˡ_ f2 using () renaming (f to f'; g to g')
          open _⇒ᶠⁱˡ_ f3 using () renaming (f to f''; g to g'')
          open functor-functor-interaction-law L using (F; G)
          open functor-functor-interaction-law M using () renaming (F to J; G to K)
          open functor-functor-interaction-law L' using () renaming (F to F'; G to G')
          open functor-functor-interaction-law M' using () renaming (F to J'; G to K')
          open functor-functor-interaction-law L'' using () renaming (F to F''; G to G'')
          open functor-functor-interaction-law M'' using () renaming (F to J''; G to K'')
          module F = Functor F
          module G = Functor G
          module J = Functor J
          module K = Functor K
          module F' = Functor F'
          module G' = Functor G'
          module J' = Functor J'
          module K' = Functor K'
          module F'' = Functor F''
          module G'' = Functor G''
          module J'' = Functor J''
          module K'' = Functor K''

  open Commutation IL

  triangle : ∀ {X Y} → 
             [ (X ⊗L₀ unit) ⊗L₀ Y ⇒ X ⊗L₀ Y ]⟨
               associator-IL.from ⇒⟨ X ⊗L₀ (unit ⊗L₀ Y) ⟩
             idIL ⊗L₁ unitorˡ-IL.from
           ≈ unitorʳ-IL.from ⊗L₁ idIL
           ⟩
  triangle {X} {Y} = identityʳ , identityˡ
    where open functor-functor-interaction-law X using (F; G)
          open functor-functor-interaction-law Y using () renaming (F to J; G to K)
          module F = Functor F
          module G = Functor G
          module J = Functor J
          module K = Functor K

  pentagon : ∀ {X Y Z W} →
             [ ((X ⊗L₀ Y) ⊗L₀ Z) ⊗L₀ W ⇒ X ⊗L₀ Y ⊗L₀ Z ⊗L₀ W ]⟨
               associator-IL.from ⊗L₁ idIL ⇒⟨ (X ⊗L₀ Y ⊗L₀ Z) ⊗L₀ W ⟩
               associator-IL.from         ⇒⟨ X ⊗L₀ (Y ⊗L₀ Z) ⊗L₀ W ⟩
               idIL ⊗L₁ associator-IL.from
             ≈ associator-IL.from         ⇒⟨ (X ⊗L₀ Y) ⊗L₀ Z ⊗L₀ W ⟩
               associator-IL.from
             ⟩
  pentagon {X} {Y} {Z} = (λ {x} → begin
        (F.₁ id ∘ id) ∘ id ∘ F.₁ (J.₁ (H.₁ id)) ∘ id
        ≈⟨ (identityʳ ○ F.identity) ⟩∘⟨ Equiv.refl ⟩∘⟨ (F.F-resp-≈ (J.F-resp-≈ H.identity ○ J.identity) ○ F.identity) ⟩∘⟨refl ⟩
        id ∘ id ∘ id ∘ id
        ≈⟨ identityˡ ○ identityˡ ⟩
        id ∘ id
        ∎)  , λ {x} → begin
        ((G.₁ (K.₁ (I.₁ id)) ∘ id) ∘ id) ∘ G.₁ id ∘ id
        ≈⟨ (identityʳ ○ identityʳ ○ G.F-resp-≈ (K.F-resp-≈ I.identity ○ K.identity) ○ G.identity) ⟩∘⟨refl ⟩
        id ∘ G.₁ id ∘ id
        ≈⟨ identityˡ
         ○ G.identity ⟩∘⟨refl ⟩
        id ∘ id
        ∎
    where open functor-functor-interaction-law X using (F; G)
          open functor-functor-interaction-law Y using () renaming (F to J; G to K)
          open functor-functor-interaction-law Z using () renaming (F to H; G to I)
          module F = Functor F
          module G = Functor G
          module J = Functor J
          module K = Functor K
          module H = Functor H
          module I = Functor I

  monoidal : Monoidal IL
  monoidal = monoidalHelper IL record
    { ⊗               = ⊗-IL
    ; unit            = unit
    ; unitorˡ         = unitorˡ-IL
    ; unitorʳ         = unitorʳ-IL
    ; associator      = associator-IL
    ; unitorˡ-commute = identityˡ , (identityʳ ○ identityʳ ○ ⟺ identityˡ)
    ; unitorʳ-commute = unitorʳ-commute
    {-
      We want this: `assoc-commute` but it takes too long (100,000ms+). We tried eta-expanding to
      ```
      λ {L} {M} {f} {L'} {M'} {g} {L''} {M''} {h} → assoc-commute  {L} {M} {f} {L'} {M'} {g} {L''} {M''} {h} 
      ```
      and it takes around half the time, but it is still too long (50,000ms).

      We tried giving `assoc-commute` several different types, e.g.
      assoc-commute-type = ∀{L M}  {f : L ⇒ᶠⁱˡ M} {L' M'} {g : L' ⇒ᶠⁱˡ M'} {L'' M''}  {h : L'' ⇒ᶠⁱˡ M''} →
                       CommutativeSquare ((f ⊗L₁ g) ⊗L₁ h) associator-IL.from associator-IL.from (f ⊗L₁ (g ⊗L₁ h))
      and
      assoc-commute-type2 = ∀{L M}  {f : L ⇒ᶠⁱˡ M} {L' M'} {g : L' ⇒ᶠⁱˡ M'} {L'' M''}  {h : L'' ⇒ᶠⁱˡ M''} →
                            CommutativeSquare
                            (Functor.F₁ ⊗-IL (Functor.F₁ ⊗-IL (f , g) , h))
                            associator-IL.from
                            associator-IL.from
                            (Functor.F₁ ⊗-IL (f , Functor.F₁ ⊗-IL (g , h)))
      but neither worked. Instead, what follows is a nasty copy-paste of the proof term.
      -}
    ; assoc-commute   = λ {L} {M} {f1} {L'} {M'} {f2} {L''} {M''} {f3} → 
          let open _⇒ᶠⁱˡ_ f1 using (f; g)
              open _⇒ᶠⁱˡ_ f2 using () renaming (f to f'; g to g')
              open _⇒ᶠⁱˡ_ f3 using () renaming (f to f''; g to g'')
              open functor-functor-interaction-law L using (F; G)
              open functor-functor-interaction-law M using () renaming (F to J; G to K)
              open functor-functor-interaction-law L' using () renaming (F to F'; G to G')
              open functor-functor-interaction-law M' using () renaming (F to J'; G to K')
              open functor-functor-interaction-law L'' using () renaming (F to F''; G to G'')
              open functor-functor-interaction-law M'' using () renaming (F to J''; G to K'')
              module F = Functor F
              module G = Functor G
              module J = Functor J
              module K = Functor K
              module F' = Functor F'
              module G' = Functor G'
              module J' = Functor J'
              module K' = Functor K'
              module F'' = Functor F''
              module G'' = Functor G''
              module J'' = Functor J''
              module K'' = Functor K'' in
            (λ {x} → begin
            id ∘ J.₁ (J'.₁ (appN f'' x)) ∘ J.₁ (appN f' (F''.₀ x)) ∘ appN f (F'.₀ (F''.₀ x))
            ≈⟨ identityˡ ⟩
            J.₁ (J'.₁ (appN f'' x)) ∘ J.₁ (appN f' (F''.₀ x)) ∘ appN f (F'.₀ (F''.₀ x))
            ≈⟨ pullˡ (⟺ J.homomorphism) ⟩
            J.₁ (J'.₁ (appN f'' x) ∘ (appN f' (F''.₀ x))) ∘ appN f (F'.₀ (F''.₀ x))
            ≈⟨ ⟺ identityʳ ⟩
            (J.₁ (J'.₁ (appN f'' x) ∘ appN f' (F''.₀ x)) ∘ appN f (F'.₀ (F''.₀ x))) ∘ id
            ∎)  , λ {x} → begin
            (G.₁ (G'.₁ (appN g'' x)) ∘ G.₁ (appN g' (K''.₀ x)) ∘ appN g (K'.₀ (K''.₀ x))) ∘ id
            ≈⟨ identityʳ ⟩
            G.₁ (G'.₁ (appN g'' x)) ∘ G.₁ (appN g' (K''.₀ x)) ∘ appN g (K'.₀ (K''.₀ x))
            ≈⟨ pullˡ (⟺ G.homomorphism) ⟩
            G.₁ (G'.₁ (appN g'' x) ∘ (appN g' (K''.₀ x))) ∘ appN g (K'.₀ (K''.₀ x))
            ≈⟨ ⟺ identityˡ ⟩
            id ∘ G.₁ (G'.₁ (appN g'' x) ∘ appN g' (K''.₀ x)) ∘ appN g (K'.₀ (K''.₀ x))
            ∎
    ; triangle        = λ {X} {Y} → triangle {X} {Y}
    ; pentagon        = λ {X} {Y} {Z} {W} → pentagon {X} {Y} {Z} {W}
    }
