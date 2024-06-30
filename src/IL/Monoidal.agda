{-# OPTIONS --without-K --hidden-argument-puns --safe --lossy-unification #-}
open import Prelude

module IL.Monoidal  {o ℓ e} {C : Category o ℓ e} (MC : Monoidal C) where


open Monoidal MC using (⊗; _⊗₀_; _⊗₁_)
open import Categories.NaturalTransformation.NaturalIsomorphism hiding (_≃_)

open import IL.Core (MC) renaming (id to idIL) using (IL; FILM⟨_,_,_⟩; _⇒ᶠⁱˡ_)
open import fil (MC) using (FIL; FIL[_,_,_])
open import Data.Product using (uncurry; uncurry′)

private
  module C = Category C
  module C² = Category (C ×ᶜ C)

module MC = Monoidal MC

module _ where
  open FIL
  unit : FIL
  unit .F = idF
  unit .G = idF
  -- agda doesn't like `idN` here, instead we need the unitor
  unit .ϕ  = unitorʳ.F⇒G
    where module unitorʳ = NaturalIsomorphism unitorʳ


infixr 10 _⊗L₀_
_⊗L₀_ : FIL → FIL → FIL
(FIL[ F , _ , _ ] ⊗L₀ FIL[ J , _ , _ ]) .FIL.F = F ∘F J
(FIL[ _ , G , _ ] ⊗L₀ FIL[ _ , K , _ ]) .FIL.G = G ∘F K
(FIL[ F , G , ϕ ] ⊗L₀ FIL[ J , K , ψ ]) .FIL.ϕ  = replaceˡ (ψ ∘ᵥ ϕ ∘ʳ (J ⁂ K)) (associator (J ⁂ K) (F ⁂ G) ⊗)

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

  _⊗L₁_ : {L L' M M' : FIL} →
          (L ⇒ᶠⁱˡ L') → (M ⇒ᶠⁱˡ M') →
          IL [ L ⊗L₀ M , L' ⊗L₀ M' ]
  (FILM⟨ f , _ , _ ⟩ ⊗L₁ FILM⟨ j , _ , _ ⟩) ._⇒ᶠⁱˡ_.f = f ∘ₕ j
  (FILM⟨ _ , g , _ ⟩ ⊗L₁ FILM⟨ _ , k , _ ⟩) ._⇒ᶠⁱˡ_.g = g ∘ₕ k
  _⊗L₁_ {L} {L'} {M} {M'} FILM⟨ f , g , isMap₁ ⟩ FILM⟨ j , k , isMap₂ ⟩ ._⇒ᶠⁱˡ_.isMap {(x , y)} = begin
      (_ ∘ᵥ ⊗ ∘ˡ (idN ⁂ⁿ g ∘ₕ k)) .η (x , y)
      ≈⟨ Equiv.refl ⟩
      ((ψ .η (x , y) ∘ ϕ .η (J₀ x ,  K₀ y)) ∘ idC) ∘ (idC ⊗₁ (G₁ (k .η y) ∘ g .η (K'₀ y)))
      ≈⟨ pushˡ C.identityʳ ⟩
      ψ .η  (x , y) ∘ ϕ .η (J₀ x  , K₀  y)         ∘ (idC ⊗₁ (G₁ (k .η y) ∘ g .η (K'₀ y)))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ split₂ʳ ⟩ -- slide down g
      ψ .η (x , y) ∘ ϕ .η (J₀ x  , K₀  y)         ∘ (idC ⊗₁ G₁ (k .η y))
                                                       ∘ (idC ⊗₁ g .η (K'₀ y))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ (Functor.identity F) ⟩⊗⟨refl ⟩∘⟨refl
       ○ refl⟩∘⟨ extendʳ (NaturalTransformation.commute ϕ _)
       ⟩ -- slide up k
      ψ .η (x , y) ∘ (idC ⊗₁ (k .η y))  ∘ ϕ .η (J₀ x  , K'₀  y)
                                             ∘ (idC ⊗₁ g .η (K'₀ y))
      ≈⟨ extendʳ isMap₂ ⟩
      ψ' .η (x , y) ∘ (j .η x ⊗₁ idC)  ∘ ϕ .η (J₀ x  , K'₀  y)
                                           ∘ (idC ⊗₁ g .η (K'₀ y))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ isMap₁ ⟩
      ψ' .η (x , y) ∘ (j .η x ⊗₁ idC)  ∘ ϕ' .η (J₀ x  , K'₀  y)
                                           ∘ (f .η (J₀ x) ⊗₁ idC)
      ≈⟨ refl⟩∘⟨ extendʳ (NaturalTransformation.sym-commute ϕ' _) 
       ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩⊗⟨ G'.identity ⟩∘⟨refl ⟩ -- slide down j
      ψ' .η (x , y) ∘ ϕ' .η (J'₀ x , K'₀ y) ∘ (F'₁ (j .η x) ⊗₁ idC)
                                                ∘ (f .η (J₀ x)  ⊗₁ idC)
      ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ split₁ʳ ⟩ -- slide up f
      ψ' .η (x , y) ∘ ϕ' .η (J'₀ x , K'₀ y) ∘ (F'₁ (j .η x) ∘ f .η (J₀ x)) ⊗₁ idC
      ≈˘⟨ pushˡ C.identityʳ ⟩
      ((ψ' .η (x , y) ∘ ϕ' .η (J'₀ x , K'₀ y)) ∘ idC) ∘ (F'₁ (j .η x) ∘ f .η (J₀ x)) ⊗₁ idC
      ≈⟨ Equiv.refl ⟩
      (_ ∘ᵥ ⊗ ∘ˡ (f ∘ₕ j ⁂ⁿ idN)) .η (x , y)
      ∎
    where open FIL L  using (ϕ; F; G)
          open NaturalTransformation using (η)
          open C renaming (id to idC)
          open MR C
          open FIL L' renaming (ϕ to ϕ'; F to F'; G to G')
          open FIL M  renaming (ϕ to ψ; F to J; G to K)
          open FIL M' renaming (ϕ to ψ'; F to J'; G to K')
          open Functor F' using () renaming (F₀ to F'₀; F₁ to F'₁)
          open Functor G  using () renaming (F₀ to G₀; F₁ to G₁)
          open G' using () renaming (F₀ to G'₀; F₁ to G'₁)
          open Functor J  using () renaming (F₀ to J₀; F₁ to J₁)
          open Functor J' using () renaming (F₀ to J'₀; F₁ to J'₁)
          open Functor K  using () renaming (F₀ to K₀; F₁ to K₁)
          open Functor K' using () renaming (F₀ to K'₀; F₁ to K'₁)

private module _ {F : Endofunctor C} where
  open Functor F
  open Category C
  open MR C
  open import Categories.Category.Monoidal.Reasoning (MC)
  f-eq : {A : Obj} → F₁ {A} id ∘ id ≈ id
  f-eq = elimˡ identity

⊗-IL : Bifunctor IL IL IL
⊗-IL = record
  { F₀           = uncurry _⊗L₀_
  ; F₁           = uncurry _⊗L₁_
  ; identity     = λ {(FIL[ F , G , _ ] , FIL[ J , K , _ ])} → (λ {x} → f-eq {F = F} {A = Functor.F₀ J x}) , λ {x} → f-eq {F = G} {A = Functor.F₀ K x}
  ; homomorphism = λ {_} {_} {_} {(FILM⟨ f , g , _ ⟩ , FILM⟨ j , k , _ ⟩)} {(FILM⟨ f' , g' , _ ⟩  , FILM⟨ j' , k' , _ ⟩)}
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
  open NaturalTransformation using (η)
  NatIso⇒ILIso : ∀ {L M : FIL}
            (let open FIL L)
            (let open FIL M renaming (ϕ to ψ; F to F'; G to G'))
            (F≃F' : F ≃ⁿ F')
            (G≃G' : G' ≃ⁿ G)
            (let open NaturalIsomorphism F≃F'  renaming (F⇒G to F⇒F';F⇐G to F⇐F'; module iso to iso₁))
            (let open NaturalIsomorphism G≃G'  renaming (F⇒G to G'⇒G;F⇐G to G'⇐G; module iso to iso₂))
            (isMap₁ : (ϕ ∘ᵥ ⊗ ∘ˡ (idN ⁂ⁿ G'⇒G)) ≃ (ψ ∘ᵥ ⊗ ∘ˡ (F⇒F' ⁂ⁿ idN)))
            --(isMap₂ : (ψ  ∘ᵥ ⊗ ∘ˡ (idN ⁂ⁿ G'⇐G)) ≃ (ϕ ∘ᵥ ⊗ ∘ˡ (F⇐F' ⁂ⁿ idN)))
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
          open FIL M renaming (ϕ to ψ; F to F'; G to G')
          open NaturalIsomorphism F≃F' renaming (F⇒G to F⇒F';F⇐G to F⇐F'; module iso to iso₁)
          open NaturalIsomorphism G≃G' renaming (F⇒G to G'⇒G;F⇐G to G'⇐G; module iso to iso₂)
          module F≃F' = NaturalIsomorphism F≃F'
          module G≃G' = NaturalIsomorphism G≃G'
          isMap₂ : (ψ  ∘ᵥ ⊗ ∘ˡ (idN ⁂ⁿ G'⇐G)) ≃ (ϕ ∘ᵥ ⊗ ∘ˡ (F⇐F' ⁂ⁿ idN))
          isMap₂ {(x , y)} = begin
            (ψ ∘ᵥ ⊗ ∘ˡ (idN ⁂ⁿ G'⇐G)) .η (x , y)
            ≈⟨ refl⟩∘⟨ Equiv.sym (F≃F'.iso.isoʳ _) ⟩⊗⟨refl ⟩
            (ψ ∘ᵥ ⊗ ∘ˡ ((F⇒F' ∘ᵥ F⇐F') ⁂ⁿ G'⇐G) ) .η (x , y)
            ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ ⟺ identityˡ ⟩
            (ψ ∘ᵥ ⊗ ∘ˡ (F⇒F' ⁂ⁿ idN)  ∘ᵥ (F⇐F' ⁂ⁿ G'⇐G)) .η (x , y)
            ≈⟨ refl⟩∘⟨ ⊗-distrib-over-∘
             ○ extendʳ (⟺ isMap₁)
             ○ refl⟩∘⟨ ⟺ ⊗-distrib-over-∘ ⟩ -- isMap₁
            (ϕ ∘ᵥ ⊗ ∘ˡ (idN ⁂ⁿ G'⇒G) ∘ᵥ (F⇐F' ⁂ⁿ G'⇐G)) .η (x , y)
            ≈⟨ refl⟩∘⟨ identityˡ ⟩⊗⟨refl ⟩
            (ϕ  ∘ᵥ ⊗ ∘ˡ (F⇐F'  ⁂ⁿ (G'⇒G ∘ᵥ G'⇐G))) .η (x , y)
            ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ G≃G'.iso.isoʳ _ ⟩
            (ϕ  ∘ᵥ ⊗ ∘ˡ (F⇐F'  ⁂ⁿ idN)) .η (x , y)
            ∎

  unitorˡ-IL : {X : FIL} → unit ⊗L₀ X ≅ X
  unitorˡ-IL {X} = NatIso⇒ILIso unitorˡ (sym unitorˡ) λ {x} → begin
      ((ϕ .η x ∘ id) ∘ id) ∘ (id ⊗₁ id)
      ≈⟨ (identityʳ ○ identityʳ) ⟩∘⟨refl ⟩
      ϕ .η x ∘ (id ⊗₁ id)
      ∎
    where open FIL X

  unitorʳ-IL : {X : FIL} → X ⊗L₀ unit ≅ X
  unitorʳ-IL {X} = NatIso⇒ILIso unitorʳ (sym unitorʳ) λ {x} → begin
      (((id ∘ ϕ .η x)) ∘ id) ∘ (id ⊗₁ id)
      ≈⟨ (identityʳ ○ identityˡ) ⟩∘⟨refl ⟩
      ϕ .η x ∘ (id ⊗₁ id)
      ∎
    where open FIL X

  associator-IL : {X Y Z : FIL} → (X ⊗L₀ Y) ⊗L₀ Z ≅ X ⊗L₀ (Y ⊗L₀ Z)
  associator-IL {X} {Y} {Z} = NatIso⇒ILIso (associator _ _ _) (sym-associator _ _ _) λ {(x , y)} → begin
      ((Χ .η (x , y) ∘ (ψ .η (F''₀ x , G''₀ y) ∘ ϕ .η (F'₀ (F''₀ x) , G'₀ (G''₀ y))) ∘ id) ∘ id) ∘ (id ⊗₁ id)
      ≈⟨ (identityʳ ○ refl⟩∘⟨ identityʳ) ⟩∘⟨refl ⟩
      (Χ .η (x , y) ∘ ψ .η (F''₀ x , G''₀ y) ∘ ϕ .η (F'₀ (F''₀ x) , G'₀ (G''₀ y))) ∘ (id ⊗₁ id)
      ≈⟨ Equiv.sym identityʳ ⟩∘⟨refl
       ○ sym-assoc ⟩∘⟨refl ⟩∘⟨refl
       ○ (refl⟩∘⟨ ⟺ identityˡ) ⟩∘⟨refl ⟩∘⟨refl
       ○ sym-assoc ⟩∘⟨refl ⟩∘⟨refl ⟩
      ((((Χ .η (x , y) ∘ ψ .η (F''₀ x , G''₀ y)) ∘ id) ∘ ϕ .η (F'₀ (F''₀ x) , G'₀ (G''₀ y))) ∘ id) ∘ (id ⊗₁ id)
      ∎
    where open FIL X
          open FIL Y renaming (ϕ to ψ; F to F'; G to G')
          open FIL Z renaming (ϕ to Χ; F to F''; G to G'')
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
      id ∘ J.₁ id ∘ f .η x
      ≈⟨ identityˡ ⟩
      J.₁ id ∘ f .η x
      ≈⟨ J.identity ⟩∘⟨refl ○ identityˡ ○ ⟺ identityʳ ⟩
      f .η x ∘ id
      ∎)  , λ {x} → begin
      (G.₁ id ∘ g .η x) ∘ id
      ≈⟨ identityʳ ○ G.identity ⟩∘⟨refl ⟩
      id ∘ g .η x
      ∎
    where open _⇒ᶠⁱˡ_ fil-morphism
          open FIL L using (F; G)
          open FIL M using () renaming (F to J; G to K)
  assoc-commute : ∀{L M : Category.Obj IL}      {f : IL [ L   , M   ]}
                   {L' M' : Category.Obj IL}    {g : IL [ L'  , M'  ]}
                   {L'' M'' : Category.Obj IL}  {h : IL [ L'' , M'' ]} →
                 CommutativeSquare
                 ((f ⊗L₁ g) ⊗L₁ h) associator-IL.from
                 associator-IL.from (f ⊗L₁ (g ⊗L₁ h))
  assoc-commute {L} {M} {f = f1} {L'} {M'} {g = f2} {L''} {M''} {h = f3} = (λ {x} → begin
      id ∘ J.₁ (J'.₁ (f'' .η x)) ∘ J.₁ (f' .η (F''.₀ x)) ∘ f .η (F'.₀ (F''.₀ x))
      ≈⟨ identityˡ ⟩
      J.₁ (J'.₁ (f'' .η x)) ∘ J.₁ (f' .η (F''.₀ x)) ∘ f .η (F'.₀ (F''.₀ x))
      ≈⟨ pullˡ (⟺ J.homomorphism) ⟩
      J.₁ (J'.₁ (f'' .η x) ∘ (f' .η (F''.₀ x))) ∘ f .η (F'.₀ (F''.₀ x))
      ≈⟨ ⟺ identityʳ ⟩
      (J.₁ (J'.₁ (f'' .η x) ∘ f' .η (F''.₀ x)) ∘ f .η (F'.₀ (F''.₀ x))) ∘ id
      ∎)  , λ {x} → begin
      (G.₁ (G'.₁ (g'' .η x)) ∘ G.₁ (g' .η (K''.₀ x)) ∘ g .η (K'.₀ (K''.₀ x))) ∘ id
      ≈⟨ identityʳ ⟩
      G.₁ (G'.₁ (g'' .η x)) ∘ G.₁ (g' .η (K''.₀ x)) ∘ g .η (K'.₀ (K''.₀ x))
      ≈⟨ pullˡ (⟺ G.homomorphism) ⟩
      G.₁ (G'.₁ (g'' .η x) ∘ (g' .η (K''.₀ x))) ∘ g .η (K'.₀ (K''.₀ x))
      ≈⟨ ⟺ identityˡ ⟩
      id ∘ G.₁ (G'.₁ (g'' .η x) ∘ g' .η (K''.₀ x)) ∘ g .η (K'.₀ (K''.₀ x))
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

  IL-monoidal : Monoidal IL
  IL-monoidal = monoidalHelper IL record
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
