{-# OPTIONS --without-K --lossy-unification --hidden-argument-puns #-}
open import Prelude

module IL.Monoidal  {o ℓ e} {C : Category o ℓ e} (MC : Monoidal C) where


open Monoidal MC using (⊗; _⊗₀_; _⊗₁_)

open import IL.Core (MC) renaming (id to idIL) using (IL; F⟨_,_,_⟩; _⇒ᶠⁱˡ_)
open import fil (MC) using (FIL; FIL[_,_,_])

private
  module C = Category C
  module C² = Category (ProductCat C C)

module MC = Monoidal MC

open FIL using (source; dest)
unit : FIL
unit .FIL.F = idF
unit .FIL.G = idF
  -- agda doesn't like `idN` here, so we eta-expand it
unit .FIL.Φ  = ntHelper record
  { η = λ _ → C.id
  ; commute = λ f → id-comm-sym {f = _}
  }
  where open MR C

infixr 10 _⊗L₀_

-- unfortunately we don't have a definitional equality here, so we need to transport along a natural isomorphism
_⊗L₀_ : FIL → FIL → FIL
(L ⊗L₀ L') .FIL.F = source L ∘F source L'
(L ⊗L₀ L') .FIL.G = dest L   ∘F dest L'
(L ⊗L₀ L') .FIL.Φ  = replaceˡ (Ψ ∘ᵥ Φ ∘ʳ (J ⁂ K)) (associator (J ⁂ K) (F ⁂ G) ⊗)
  where open FIL L
        open FIL L' renaming (Φ to Ψ; F to J; G to K)

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
      NaturalTransformation.app ((γ ∘ᵥ δ) ∘ₕ β ∘ᵥ α) x
      ≈⟨ D.Equiv.refl ⟩
      D [ K₁ (B [ β.app x ∘ α.app x ]) ∘ D [ γ.app (F₀ x) ∘ δ.app (F₀ x)] ]
      ≈⟨ K.homomorphism ⟩∘⟨refl ⟩
      D [ D [ K₁ (β.app     x) ∘ K₁ (α.app x) ]  ∘ D [ γ.app (F₀ x) ∘ δ.app (F₀ x)] ]
      ≈⟨ D.assoc ○ refl⟩∘⟨ D.sym-assoc ⟩
      D [ K₁ (β.app x)         ∘ D [ D [ K₁ (α.app x) ∘ γ.app (F₀ x) ] ∘ δ.app (F₀ x)] ]
      ≈⟨ refl⟩∘⟨ γ.sym-commute (α.app x) ⟩∘⟨refl ⟩
      D [ K₁ (β.app x)         ∘ D [ D [ γ.app (G₀ x) ∘ J₁ (α.app x) ] ∘ δ.app (F₀ x)] ]
      ≈˘⟨ D.assoc ○ refl⟩∘⟨ D.sym-assoc ⟩
      D [     D [ K₁ (β.app x) ∘ γ.app (G₀ x) ]  ∘ D [ J₁ (α.app x) ∘ δ.app (F₀ x)] ]
      ≈⟨ D.Equiv.refl ⟩
      NaturalTransformation.app ((γ ∘ₕ β) ∘ᵥ δ ∘ₕ α) x ∎

module _ where
  open import Categories.Category.Monoidal.Reasoning (MC)
  infixr 10 _⊗L₁_

  _⊗L₁_ : {L L' M M' : FIL} →
          (L ⇒ᶠⁱˡ L') → (M ⇒ᶠⁱˡ M') →
          IL [ L ⊗L₀ M , L' ⊗L₀ M' ]
  (F⟨ f , _ , _ ⟩ ⊗L₁ F⟨ j , _ , _ ⟩) ._⇒ᶠⁱˡ_.f = f ∘ₕ j
  (F⟨ _ , g , _ ⟩ ⊗L₁ F⟨ _ , k , _ ⟩) ._⇒ᶠⁱˡ_.g = g ∘ₕ k
  _⊗L₁_ {L} {L'} {M} {M'} F⟨ f , g , isMap₁ ⟩ F⟨ j , k , isMap₂ ⟩ ._⇒ᶠⁱˡ_.isMap {(x , y)} = begin
      (_ ∘ᵥ ⊗ ∘ˡ (idN ⁂ⁿ g ∘ₕ k)) .app (x , y)
      ≈⟨ Equiv.refl ⟩
      ((Ψ .app (x , y) ∘ Φ .app (J₀ x ,  K₀ y)) ∘ idC) ∘ (idC ⊗₁ (G₁ (k .app y) ∘ g .app (K'₀ y)))
      ≈⟨ pushˡ C.identityʳ ⟩
      Ψ .app  (x , y) ∘ Φ .app (J₀ x  , K₀  y)         ∘ (idC ⊗₁ (G₁ (k .app y) ∘ g .app (K'₀ y)))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ split₂ʳ ⟩ -- slide down g
      Ψ .app (x , y) ∘ Φ .app (J₀ x  , K₀  y)         ∘ (idC ⊗₁ G₁ (k .app y))
                                                       ∘ (idC ⊗₁ g .app (K'₀ y))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ (Functor.identity F) ⟩⊗⟨refl ⟩∘⟨refl
       ○ refl⟩∘⟨ pullˡ-assoc (NaturalTransformation.commute Φ _)
       ⟩ -- slide up k
      Ψ .app (x , y) ∘ (idC ⊗₁ (k .app y))  ∘ Φ .app (J₀ x  , K'₀  y)
                                             ∘ (idC ⊗₁ g .app (K'₀ y))
      ≈⟨ pullˡ-assoc isMap₂ ⟩
      Ψ' .app (x , y) ∘ (j .app x ⊗₁ idC)  ∘ Φ .app (J₀ x  , K'₀  y)
                                           ∘ (idC ⊗₁ g .app (K'₀ y))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ isMap₁ ⟩
      Ψ' .app (x , y) ∘ (j .app x ⊗₁ idC)  ∘ Φ' .app (J₀ x  , K'₀  y)
                                           ∘ (f .app (J₀ x) ⊗₁ idC)
      ≈⟨ refl⟩∘⟨ pullˡ-assoc (NaturalTransformation.sym-commute Φ' _) 
       ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩⊗⟨ G'.identity ⟩∘⟨refl ⟩ -- slide down j
      Ψ' .app (x , y) ∘ Φ' .app (J'₀ x , K'₀ y) ∘ (F'₁ (j .app x) ⊗₁ idC)
                                                ∘ (f .app (J₀ x)  ⊗₁ idC)
      ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ split₁ʳ ⟩ -- slide up f
      Ψ' .app (x , y) ∘ Φ' .app (J'₀ x , K'₀ y) ∘ (F'₁ (j .app x) ∘ f .app (J₀ x)) ⊗₁ idC
      ≈˘⟨ pushˡ C.identityʳ ⟩
      ((Ψ' .app (x , y) ∘ Φ' .app (J'₀ x , K'₀ y)) ∘ idC) ∘ (F'₁ (j .app x) ∘ f .app (J₀ x)) ⊗₁ idC
      ≈⟨ Equiv.refl ⟩
      (_ ∘ᵥ ⊗ ∘ˡ (f ∘ₕ j ⁂ⁿ idN)) .app (x , y)
      ∎
    where open FIL L  using (Φ; F; G)
          open NaturalTransformation using (app)
          open C renaming (id to idC)
          open MR C
          open FIL L' renaming (Φ to Φ'; F to F'; G to G')
          open FIL M  renaming (Φ to Ψ; F to J; G to K)
          open FIL M' renaming (Φ to Ψ'; F to J'; G to K')
          open Functor F' using () renaming (F₀ to F'₀; F₁ to F'₁)
          open Functor G  using () renaming (F₀ to G₀; F₁ to G₁)
          module G' = Functor G'
          open G' using () renaming (F₀ to G'₀; F₁ to G'₁)
          open Functor J  using () renaming (F₀ to J₀; F₁ to J₁)
          open Functor J' using () renaming (F₀ to J'₀; F₁ to J'₁)
          open Functor K  using () renaming (F₀ to K₀; F₁ to K₁)
          open Functor K' using () renaming (F₀ to K'₀; F₁ to K'₁)
  homomorphism-IL : {L L' L'' M M' M'' : FIL}
                  → {f : L ⇒ᶠⁱˡ L'} → {j : M ⇒ᶠⁱˡ M'}
                  → {f' : L' ⇒ᶠⁱˡ L''} → {j' : M' ⇒ᶠⁱˡ M''}
                  → (let open Category IL)
                  → (f' ∘ f) ⊗L₁ (j' ∘ j) ≈ f' ⊗L₁ j' ∘ f ⊗L₁ j
  homomorphism-IL {f = F⟨ f , g , _ ⟩} {j = F⟨ j , k , _ ⟩} {f' = F⟨ f' , g' , _ ⟩}  {j' = F⟨ j' , k' , _ ⟩} =
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
  ; identity     = λ {(FIL[ F , G , _ ] , FIL[ J , K , _ ])} → (λ {x} → f-eq {F = F} {A = Functor.F₀ J x}) , λ {x} → f-eq {F = G} {A = Functor.F₀ K x}
  ; homomorphism = λ {_} {_} {_} {(F⟨ f , g , _ ⟩ , F⟨ j , k , _ ⟩)} {(F⟨ f' , g' , _ ⟩  , F⟨ j' , k' , _ ⟩)}
                    -- i guess it's cleaner to copy-paste homomorphism-IL above here
                     → ≃-interchange {α = j} {β = j'} {δ = f} {γ = f'}  , ≃-interchange {α = k'} {β = k} {δ = g'} {γ = g}
  ; F-resp-≈     = λ { {A = (FIL[ F , G , _ ] , FIL[ F' , G' , _ ])} {B = (FIL[ M , N , _ ] , FIL[ M' , N' , _ ] )} {f = (f₁ , f₂)} {g = (g₁ , g₂)} ((e₁₁ , e₁₂) , (e₂₁ , e₂₂))
                     → (Functor.F-resp-≈ M e₂₁ ⟩∘⟨ e₁₁) , (Functor.F-resp-≈ G e₂₂ ⟩∘⟨ e₁₂) }
  }
  where open Category C
        open HomReasoning

module _ where

  open import Categories.Morphism IL using (_≅_; Iso)
  open Category C
  open MR C
  open import Categories.Category.Monoidal.Reasoning (MC)
  open NaturalTransformation using (app)
  NatIso⇒ILIso : ∀ {L M : FIL}
            (let open FIL L)
            (let open FIL M renaming (Φ to Ψ; F to F'; G to G'))
            (F≃F' : F ≃ⁿ F')
            (G≃G' : G' ≃ⁿ G)
            (let open NaturalIsomorphism F≃F'  renaming (F⇒G to F⇒F';F⇐G to F⇐F'; module iso to iso₁))
            (let open NaturalIsomorphism G≃G'  renaming (F⇒G to G'⇒G;F⇐G to G'⇐G; module iso to iso₂))
            (isMap₁ : (Φ ∘ᵥ ⊗ ∘ˡ (idN ⁂ⁿ G'⇒G)) ≃ (Ψ ∘ᵥ ⊗ ∘ˡ (F⇒F' ⁂ⁿ idN)))
            --(isMap₂ : (Ψ  ∘ᵥ ⊗ ∘ˡ (idN ⁂ⁿ G'⇐G)) ≃ (Φ ∘ᵥ ⊗ ∘ˡ (F⇐F' ⁂ⁿ idN)))
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
    where open FIL L
          open FIL M renaming (Φ to Ψ; F to F'; G to G')
          open NaturalIsomorphism F≃F' renaming (F⇒G to F⇒F';F⇐G to F⇐F'; module iso to iso₁)
          open NaturalIsomorphism G≃G' renaming (F⇒G to G'⇒G;F⇐G to G'⇐G; module iso to iso₂)
          module F≃F' = NaturalIsomorphism F≃F'
          module G≃G' = NaturalIsomorphism G≃G'
          isMap₂ : (Ψ  ∘ᵥ ⊗ ∘ˡ (idN ⁂ⁿ G'⇐G)) ≃ (Φ ∘ᵥ ⊗ ∘ˡ (F⇐F' ⁂ⁿ idN))
          isMap₂ {(x , y)} = begin
            (Ψ ∘ᵥ ⊗ ∘ˡ (idN ⁂ⁿ G'⇐G)) .app (x , y)
            ≈⟨ refl⟩∘⟨ Equiv.sym (F≃F'.iso.isoʳ _) ⟩⊗⟨refl ⟩
            (Ψ ∘ᵥ ⊗ ∘ˡ ((F⇒F' ∘ᵥ F⇐F') ⁂ⁿ G'⇐G) ) .app (x , y)
            ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ ⟺ identityˡ ⟩
            (Ψ ∘ᵥ ⊗ ∘ˡ (F⇒F' ⁂ⁿ idN)  ∘ᵥ (F⇐F' ⁂ⁿ G'⇐G)) .app (x , y)
            ≈⟨ refl⟩∘⟨ ⊗-distrib-over-∘
             ○ pullˡ-assoc (⟺ isMap₁)
             ○ refl⟩∘⟨ ⟺ ⊗-distrib-over-∘ ⟩ -- isMap₁
            (Φ ∘ᵥ ⊗ ∘ˡ (idN ⁂ⁿ G'⇒G) ∘ᵥ (F⇐F' ⁂ⁿ G'⇐G)) .app (x , y)
            ≈⟨ refl⟩∘⟨ identityˡ ⟩⊗⟨refl ⟩
            (Φ  ∘ᵥ ⊗ ∘ˡ (F⇐F'  ⁂ⁿ (G'⇒G ∘ᵥ G'⇐G))) .app (x , y)
            ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ G≃G'.iso.isoʳ _ ⟩
            (Φ  ∘ᵥ ⊗ ∘ˡ (F⇐F'  ⁂ⁿ idN)) .app (x , y)
            ∎
  open import Categories.NaturalTransformation.NaturalIsomorphism

  unitorˡ-IL : {X : FIL} → unit ⊗L₀ X ≅ X
  unitorˡ-IL {X} = NatIso⇒ILIso unitorˡ (sym unitorˡ) λ {x} → begin
      ((Φ .app x ∘ id) ∘ id) ∘ (id ⊗₁ id)
      ≈⟨ (identityʳ ○ identityʳ) ⟩∘⟨refl ⟩
      Φ .app x ∘ (id ⊗₁ id)
      ∎
    where open FIL X

  unitorʳ-IL : {X : FIL} → X ⊗L₀ unit ≅ X
  unitorʳ-IL {X} = NatIso⇒ILIso unitorʳ (sym unitorʳ) λ {x} → begin
      (((id ∘ Φ .app x)) ∘ id) ∘ (id ⊗₁ id)
      ≈⟨ (identityʳ ○ identityˡ) ⟩∘⟨refl ⟩
      Φ .app x ∘ (id ⊗₁ id)
      ∎
    where open FIL X

  associator-IL : {X Y Z : FIL} → (X ⊗L₀ Y) ⊗L₀ Z ≅ X ⊗L₀ (Y ⊗L₀ Z)
  associator-IL {X} {Y} {Z} = NatIso⇒ILIso (associator _ _ _) (sym-associator _ _ _) λ {(x , y)} → begin
      ((Χ .app (x , y) ∘ (Ψ .app (F''₀ x , G''₀ y) ∘ Φ .app (F'₀ (F''₀ x) , G'₀ (G''₀ y))) ∘ id) ∘ id) ∘ (id ⊗₁ id)
      ≈⟨ (identityʳ ○ refl⟩∘⟨ identityʳ) ⟩∘⟨refl ⟩
      (Χ .app (x , y) ∘ Ψ .app (F''₀ x , G''₀ y) ∘ Φ .app (F'₀ (F''₀ x) , G'₀ (G''₀ y))) ∘ (id ⊗₁ id)
      ≈⟨ Equiv.sym identityʳ ⟩∘⟨refl
       ○ sym-assoc ⟩∘⟨refl ⟩∘⟨refl
       ○ (refl⟩∘⟨ ⟺ identityˡ) ⟩∘⟨refl ⟩∘⟨refl
       ○ sym-assoc ⟩∘⟨refl ⟩∘⟨refl ⟩
      ((((Χ .app (x , y) ∘ Ψ .app (F''₀ x , G''₀ y)) ∘ id) ∘ Φ .app (F'₀ (F''₀ x) , G'₀ (G''₀ y))) ∘ id) ∘ (id ⊗₁ id)
      ∎
    where open FIL X
          open FIL Y renaming (Φ to Ψ; F to F'; G to G')
          open FIL Z renaming (Φ to Χ; F to F''; G to G'')
          open Functor F using (F₀; F₁)
          open Functor F' using () renaming (F₀ to F'₀; F₁ to F'₁)
          open Functor G' using () renaming (F₀ to G'₀; F₁ to G'₁)
          open Functor F'' using () renaming (F₀ to F''₀; F₁ to F''₁)
          open Functor G'' using () renaming (F₀ to G''₀; F₁ to G''₁)

  open Definitions IL
  module unitorˡ-IL {X} = _≅_ (unitorˡ-IL {X = X})
  module unitorʳ-IL {X} = _≅_ (unitorʳ-IL {X = X})
  module associator-IL {X} {Y} {Z} = _≅_ (associator-IL {X} {Y} {Z})

  unitorˡ-commute : ∀{L M} {f : L ⇒ᶠⁱˡ M} →
                    CommutativeSquare (idIL ⊗L₁ f) unitorˡ-IL.from unitorˡ-IL.from f
  unitorˡ-commute = identityˡ , (identityʳ ○ identityʳ ○ ⟺ identityˡ)

  unitorʳ-commute : ∀{L M} {f : L ⇒ᶠⁱˡ M} →
                    CommutativeSquare (f ⊗L₁ idIL) unitorʳ-IL.from unitorʳ-IL.from f
  unitorʳ-commute {L} {M} {f = fil-morphism} = (λ {x} → begin
      id ∘ J.₁ id ∘ f .app x
      ≈⟨ identityˡ ⟩
      J.₁ id ∘ f .app x
      ≈⟨ J.identity ⟩∘⟨refl ○ identityˡ ○ ⟺ identityʳ ⟩
      f .app x ∘ id
      ∎)  , λ {x} → begin
      (G.₁ id ∘ g .app x) ∘ id
      ≈⟨ identityʳ ○ G.identity ⟩∘⟨refl ⟩
      id ∘ g .app x
      ∎
    where open _⇒ᶠⁱˡ_ fil-morphism
          open FIL L using (F; G)
          open FIL M using () renaming (F to J; G to K)
          module F = Functor F
          module G = Functor G
          module J = Functor J
  assoc-commute : ∀{L M : Category.Obj IL}      {f : IL [ L   , M   ]}
                   {L' M' : Category.Obj IL}    {g : IL [ L'  , M'  ]}
                   {L'' M'' : Category.Obj IL}  {h : IL [ L'' , M'' ]} →
                 CommutativeSquare
                 ((f ⊗L₁ g) ⊗L₁ h) associator-IL.from
                 associator-IL.from (f ⊗L₁ (g ⊗L₁ h))
  assoc-commute {L} {M} {f = f1} {L'} {M'} {g = f2} {L''} {M''} {h = f3} = (λ {x} → begin
      id ∘ J.₁ (J'.₁ (f'' .app x)) ∘ J.₁ (f' .app (F''.₀ x)) ∘ f .app (F'.₀ (F''.₀ x))
      ≈⟨ identityˡ ⟩
      J.₁ (J'.₁ (f'' .app x)) ∘ J.₁ (f' .app (F''.₀ x)) ∘ f .app (F'.₀ (F''.₀ x))
      ≈⟨ pullˡ (⟺ J.homomorphism) ⟩
      J.₁ (J'.₁ (f'' .app x) ∘ (f' .app (F''.₀ x))) ∘ f .app (F'.₀ (F''.₀ x))
      ≈⟨ ⟺ identityʳ ⟩
      (J.₁ (J'.₁ (f'' .app x) ∘ f' .app (F''.₀ x)) ∘ f .app (F'.₀ (F''.₀ x))) ∘ id
      ∎)  , λ {x} → begin
      (G.₁ (G'.₁ (g'' .app x)) ∘ G.₁ (g' .app (K''.₀ x)) ∘ g .app (K'.₀ (K''.₀ x))) ∘ id
      ≈⟨ identityʳ ⟩
      G.₁ (G'.₁ (g'' .app x)) ∘ G.₁ (g' .app (K''.₀ x)) ∘ g .app (K'.₀ (K''.₀ x))
      ≈⟨ pullˡ (⟺ G.homomorphism) ⟩
      G.₁ (G'.₁ (g'' .app x) ∘ (g' .app (K''.₀ x))) ∘ g .app (K'.₀ (K''.₀ x))
      ≈⟨ ⟺ identityˡ ⟩
      id ∘ G.₁ (G'.₁ (g'' .app x) ∘ g' .app (K''.₀ x)) ∘ g .app (K'.₀ (K''.₀ x))
      ∎
    where open _⇒ᶠⁱˡ_ f1 using (f; g)
          open _⇒ᶠⁱˡ_ f2 using () renaming (f to f'; g to g')
          open _⇒ᶠⁱˡ_ f3 using () renaming (f to f''; g to g'')
          open FIL L using (F; G)
          open FIL M using () renaming (F to J; G to K)
          open FIL L' using () renaming (F to F'; G to G')
          open FIL M' using () renaming (F to J'; G to K')
          open FIL L'' using () renaming (F to F''; G to G'')
          open FIL M'' using () renaming (F to J''; G to K'')
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
    where open FIL X using (F; G)
          open FIL Y using () renaming (F to J; G to K)
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
    where open FIL X using (F; G)
          open FIL Y using () renaming (F to J; G to K)
          open FIL Z using () renaming (F to H; G to I)
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
    ; unitorˡ-commute = unitorˡ-commute
    ; unitorʳ-commute = unitorʳ-commute
    ; assoc-commute   = assoc-commute
    ; triangle        = λ {X} {Y} → triangle {X} {Y}
    ; pentagon        = λ {X} {Y} {Z} {W} → pentagon {X} {Y} {Z} {W}
    }
