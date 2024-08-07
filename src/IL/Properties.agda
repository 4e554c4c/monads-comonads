{-# OPTIONS --without-K --hidden-argument-puns --safe #-}
open import Prelude
open import Categories.Object.Terminal using (Terminal; IsTerminal)
open import Categories.Object.Initial using (Initial)

open import Prelude

module IL.Properties  {o ℓ e} {C : Category o ℓ e} (MC : Monoidal C) where

open import IL.Core (MC) renaming (id to idIL) using (IL; FILM⟨_,_,_⟩; _⇒ᶠⁱˡ_)
open import fil (MC)

private
  module C = Category C
  module C² = Category (C ×ᶜ C)
  module IL = Category IL

open Monoidal MC using (⊗; _⊗₀_; _⊗₁_)

module _ where
  open FIL
  stretch : ∀ {F' G'} (L : FIL) → (NaturalTransformation F' (L .F)) →
            (NaturalTransformation G' (L .G)) → FIL
  stretch {F'} {G'} FIL[ F , G , ϕ ] f g = FIL[ F' , G' , ϕ ∘ᵥ ⊗ ∘ˡ (f ⁂ⁿ g) ]

module Symmetry (SM : Symmetric MC) where
  open import Categories.Functor.Bifunctor using (flip-bifunctor)

  module _ (H : Bifunctor C C C) (F : Functor C C) (G : Functor C C)  where
    open Functor H

    open NaturalIsomorphism
    swap-prod : ((flip-bifunctor H) ∘F (F ⁂ G)) ≃ⁿ flip-bifunctor (H ∘F (G ⁂ F))
    -- not sure why this has to be eta expanded? probably bc of the '-sym' again...
    swap-prod = niHelper record
      { η = λ _ → C.id
      ; η⁻¹ = λ _ → C.id
      ; commute = λ f → id-comm-sym {f = _}
      ; iso = λ X → record
        { isoˡ = C.identity²
        ; isoʳ = C.identity² } }
      where open MR C

    module swap-prod = NaturalIsomorphism swap-prod

  flip-trans : {H G : Bifunctor C C C} → NaturalTransformation H G → NaturalTransformation (flip-bifunctor H) (flip-bifunctor G)
  flip-trans = _∘ʳ Swap

  open Symmetric SM using (module braiding; commutative)
  open import Categories.Category.Monoidal.Symmetric.Properties SM using (inv-commutative)

  _ʳᵉᵛ : (L : FIL) → FIL
  (FIL[ _ , G , _ ] ʳᵉᵛ) .FIL.F = G
  (FIL[ F , _ , _ ] ʳᵉᵛ) .FIL.G = F
  (FIL[ F , G , ϕ ] ʳᵉᵛ) .FIL.ϕ = braiding.F⇐G
                                ∘ᵥ (ϕ ∘ʳ Swap)
                                ∘ᵥ swap-prod.F⇒G ⊗ G F
                                ∘ᵥ (braiding.F⇒G ∘ʳ (G ⁂ F))


  module symmetric = Symmetric SM

  open import Categories.Category.Monoidal.Reasoning (MC)
  open NaturalTransformation using (η)
  open Category C
  open MR C
  module _ where
    private
      pf : ∀ {L : FIL} {x y : C.Obj} →
         (let open FIL L) →
         (let open Functor F using (F₀; F₁)) →
         (let open Functor G using () renaming (F₀ to G₀; F₁ to G₁)) →
         (braiding.⇐.η (x , y) ∘ (braiding.⇐.η (y , x)
                                ∘ ϕ .η (x , y) ∘ id
                                ∘ symmetric.braiding.⇒.η (G₀ y , F₀ x))
                              ∘ id
                              ∘ symmetric.braiding.⇒.η (F₀ x , G₀ y))
                              ∘ (id ⊗₁ id)
         ≈ ϕ .η (x , y) ∘ (id ⊗₁ id)
      pf {L} {x} {y} = _⟩∘⟨refl $ begin
        braiding.⇐.η (x , y) ∘ (braiding.⇐.η (y , x) ∘ ϕ .η (x , y) ∘ id ∘ braiding.⇒.η (G₀ y , F₀ x))
          ∘ id ∘ braiding.⇒.η (F₀ x , G₀ y) 
        -- reassociate, of course
        ≈⟨ refl⟩∘⟨ assoc
         ○ refl⟩∘⟨ refl⟩∘⟨ assoc
         ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ assoc²δγ
         ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ identityˡ
         ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ identityʳ ⟩∘⟨refl
         ⟩
        braiding.⇐.η (x , y) ∘ braiding.⇐.η (y , x) ∘ ϕ .η (x , y) ∘ braiding.⇒.η (G₀ y , F₀ x) ∘ braiding.⇒.η (F₀ x , G₀ y)
        ≈⟨ pullˡ inv-commutative
         ○ identityˡ
         ⟩
        ϕ .η (x , y) ∘ braiding.⇒.η (G₀ y , F₀ x) ∘ braiding.⇒.η (F₀ x , G₀ y)
        ≈⟨ refl⟩∘⟨ commutative
         ○ identityʳ
         ⟩
        ϕ .η (x , y) ∎
        where open FIL L
              open Functor F using (F₀; F₁)
              open Functor G using () renaming (F₀ to G₀; F₁ to G₁)

    open _⇒ᶠⁱˡ_
    unit : ∀ {L} → L ⇒ᶠⁱˡ  L ʳᵉᵛ ʳᵉᵛ
    unit .f = idN
    unit .g = idN
    unit {L} .isMap {(x , y)} = ⟺ (pf {L} {x} {y})

    counit : ∀ {L} → L ʳᵉᵛ ʳᵉᵛ ⇒ᶠⁱˡ  L
    counit .f = idN
    counit .g = idN
    counit {L} .isMap {(x , y)} = pf {L} {x} {y}


  rev-map : ∀{L M} → (f : L ⇒ᶠⁱˡ M) → M ʳᵉᵛ ⇒ᶠⁱˡ  L ʳᵉᵛ
  rev-map FILM⟨ _ , g , _     ⟩ ._⇒ᶠⁱˡ_.f  = g
  rev-map FILM⟨ f , _ , _     ⟩ ._⇒ᶠⁱˡ_.g  = f
  rev-map {L} {M} FILM⟨ f , g , isMap ⟩ ._⇒ᶠⁱˡ_.isMap {(x , y)} = begin
    (braiding.⇐.η (x , y) ∘ Ψ .η (y , x) ∘ id ∘ braiding.⇒.η (K₀ x , J₀ y)) ∘ (id ⊗₁ f .η y)
    ≈⟨ assoc
     ○ refl⟩∘⟨ assoc
     ○ refl⟩∘⟨ refl⟩∘⟨ assoc
     ○ refl⟩∘⟨ refl⟩∘⟨ identityˡ
     ⟩
    braiding.⇐.η (x , y) ∘ Ψ .η (y , x) ∘ braiding.⇒.η (K₀ x , J₀ y) ∘ (id ⊗₁ f .η y)
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ braiding.⇒.commute (id , f .η y) ⟩
    braiding.⇐.η (x , y) ∘ Ψ .η (y , x) ∘ (f .η y ⊗₁ id) ∘ braiding.⇒.η (K₀ x , F₀ y)
    ≈⟨ refl⟩∘⟨ extendʳ (⟺ isMap) ⟩
    braiding.⇐.η (x , y) ∘ ϕ .η (y , x) ∘ (id ⊗₁ g .η x) ∘ braiding.⇒.η (K₀ x , F₀ y)
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ braiding.⇒.sym-commute (g .η x , id) ⟩
    braiding.⇐.η (x , y) ∘ ϕ .η (y , x) ∘ braiding.⇒.η (G₀ x , F₀ y) ∘ (g .η x ⊗₁  id)
    ≈˘⟨
     assoc
     ○ refl⟩∘⟨ assoc
     ○ refl⟩∘⟨ refl⟩∘⟨ assoc
     ○ refl⟩∘⟨ refl⟩∘⟨ identityˡ
     ⟩
    (braiding.⇐.η (x , y) ∘ ϕ .η (y , x) ∘ id ∘ braiding.⇒.η (G₀ x , F₀ y)) ∘ (g .η x ⊗₁  id) ∎
    where open FIL L
          open FIL M renaming (ϕ to Ψ; F to J; G to K)
          open Functor F using (F₀; F₁)
          open Functor G using () renaming (F₀ to G₀; F₁ to G₁)
          open Functor J using () renaming (F₀ to J₀; F₁ to J₁)
          open Functor K using () renaming (F₀ to K₀; F₁ to K₁)

  module _ where
    open Functor
    REV : Functor IL.op IL
    REV .F₀ = _ʳᵉᵛ
    REV .F₁ = rev-map
    REV .identity = C.Equiv.refl , C.Equiv.refl
    REV .homomorphism = C.Equiv.refl , C.Equiv.refl
    REV .F-resp-≈ (e₁ , e₂) = e₂ , e₁
    module REV = Functor REV

    _ : Functor IL IL.op
    _ = REV.op

  module _ where

    private
      REV-self-inv : NaturalIsomorphism (REV.op ∘F REV) idF
      REV-self-inv = niHelper record
        { η = λ _ → unit
        ; η⁻¹ = λ _ → counit
        ; commute = λ _ → (C.identityʳ ○ ⟺ C.identityˡ) , (C.identityˡ ○ ⟺ C.identityʳ)
        ; iso = λ X → record
          { isoˡ = C.identity² , C.identity²
          ; isoʳ = C.identity² , C.identity²
          }
        }
      module REV-self-inv = NaturalIsomorphism REV-self-inv

      _ : NaturalIsomorphism (REV ∘F REV.op) idF
      _ = REV-self-inv.op′

    open import Categories.Category.Equivalence
    open StrongEquivalence
    open WeakInverse
    selfDual : StrongEquivalence IL IL.op
    selfDual .F = REV.op
    selfDual .G = REV
    selfDual .weak-inverse .F∘G≈id = REV-self-inv
    selfDual .weak-inverse .G∘F≈id = REV-self-inv.op′
