{-# OPTIONS --without-K --hidden-argument-puns --allow-unsolved-metas #-}
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

stretch : ∀ {F' G'} → (L : FIL) → (let open FIL L using (F; G; Φ)) →
          (NaturalTransformation F' F) → (NaturalTransformation G' G) → FIL
stretch {F'} _ _ _ .FIL.F = F'
stretch {G'} _ _ _ .FIL.G = G'
stretch FIL[ _ , _ , Φ ] f g .FIL.Φ = Φ ∘ᵥ ⊗ ∘ˡ (f ⁂ⁿ g)

module _ (τ : Terminal C) (ι : Initial C) where
  open Terminal τ
  open Initial ι
  --open Terminal
  open IsTerminal
  -- really this should only hold if C has products, and isn't just monoidal
  -- because either F is idF, and you need a universal idF ⇒ F
  -- or it is `const ⊤` and you need some (const ⊤) ⇒ idF for the law
  --open _⇒ᶠⁱˡ_
  --terminal : Terminal IL
  --terminal .Terminal.⊤ = FIL[ idF , const ⊤ , {! !} ]
  --terminal .Terminal.⊤-is-terminal .! {FIL[ F , G , Φ ]} .f = {! !}
  --terminal .Terminal.⊤-is-terminal .! {FIL[ F , G , Φ ]} .g = {! !}
  --terminal .Terminal.⊤-is-terminal .! {FIL[ F , G , Φ ]} .isMap = {! !}
  --terminal .Terminal.⊤-is-terminal .!-unique = {! !}


module Symmetry (SM : Symmetric MC) where
  open import Categories.Functor.Bifunctor using (flip-bifunctor)

  module _ (H : Bifunctor C C C) (F : Functor C C) (G : Functor C C)  where
    open Functor H

    open NaturalIsomorphism
    swap-prod : (flip-bifunctor H ∘F (F ⁂ G)) ≃ⁿ flip-bifunctor (H ∘F (G ⁂ F))
    -- not sure why this has to be eta expanded? probably bc of the '-sym' again...
    swap-prod = niHelper record
      { η = λ _ → C.id
      ; η⁻¹ = λ _ → C.id
      ; commute = λ f → id-comm-sym {f = _}
      ; iso = λ X → record
        { isoˡ = C.identity²
        ; isoʳ = C.identity² } }
      where open MR C

  flip-trans : {H G : Bifunctor C C C} → NaturalTransformation H G → NaturalTransformation (flip-bifunctor H) (flip-bifunctor G)
  flip-trans = _∘ʳ Swap

  open Symmetric SM using (module braiding; commutative)
  open import Categories.Category.Monoidal.Symmetric.Properties SM using (inv-commutative)

  _ʳᵉᵛ : (L : FIL) → FIL
  (FIL[ _ , G , _ ] ʳᵉᵛ) .FIL.F = G
  (FIL[ F , _ , _ ] ʳᵉᵛ) .FIL.G = F
  (FIL[ F , G , Φ ] ʳᵉᵛ) .FIL.Φ = braiding.F⇐G
                                ∘ᵥ flip-trans Φ
                                ∘ᵥ NaturalIsomorphism.F⇒G (swap-prod ⊗ _ _)
                                ∘ᵥ braiding.F⇒G ∘ʳ (G ⁂ F)


  module symmetric = Symmetric SM

  open import Categories.Category.Monoidal.Reasoning (MC)
  open NaturalTransformation using (app)
  open Category C
  open MR C
  module _ where
    private
      pf : ∀ {L : FIL} {x y : C.Obj} →
         (let open FIL L) →
         (let open Functor F using (F₀; F₁)) →
         (let open Functor G using () renaming (F₀ to G₀; F₁ to G₁)) →
         (braiding.⇐.η (x , y) ∘ (braiding.⇐.η (y , x)
                                ∘ Φ .app (x , y) ∘ id
                                ∘ symmetric.braiding.⇒.η (G₀ y , F₀ x))
                              ∘ id
                              ∘ symmetric.braiding.⇒.η (F₀ x , G₀ y))
                              ∘ (id ⊗₁ id)
         ≈ Φ .app (x , y) ∘ (id ⊗₁ id)
      pf {L} {x} {y} = _⟩∘⟨refl $ begin
        braiding.⇐.η (x , y) ∘ (braiding.⇐.η (y , x) ∘ Φ .app (x , y) ∘ id ∘ braiding.⇒.η (G₀ y , F₀ x))
          ∘ id ∘ braiding.⇒.η (F₀ x , G₀ y) 
        -- reassociate, of course
        ≈⟨ refl⟩∘⟨ assoc
         ○ refl⟩∘⟨ refl⟩∘⟨ assoc
         ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ assoc²''
         ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ identityˡ
         ○ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ identityʳ ⟩∘⟨refl
         ⟩
        braiding.⇐.η (x , y) ∘ braiding.⇐.η (y , x) ∘ Φ .app (x , y) ∘ braiding.⇒.η (G₀ y , F₀ x) ∘ braiding.⇒.η (F₀ x , G₀ y)
        ≈⟨ pullˡ inv-commutative
         ○ identityˡ
         ⟩
        Φ .app (x , y) ∘ braiding.⇒.η (G₀ y , F₀ x) ∘ braiding.⇒.η (F₀ x , G₀ y)
        ≈⟨ refl⟩∘⟨ commutative
         ○ identityʳ
         ⟩
        Φ .app (x , y) ∎
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
    (braiding.⇐.η (x , y) ∘ Ψ .app (y , x) ∘ id ∘ braiding.⇒.η (K₀ x , J₀ y)) ∘ (id ⊗₁ f .app y)
    ≈⟨ assoc
     ○ refl⟩∘⟨ assoc
     ○ refl⟩∘⟨ refl⟩∘⟨ assoc
     ○ refl⟩∘⟨ refl⟩∘⟨ identityˡ
     ⟩
    braiding.⇐.η (x , y) ∘ Ψ .app (y , x) ∘ braiding.⇒.η (K₀ x , J₀ y) ∘ (id ⊗₁ f .app y)
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ braiding.⇒.commute (id , f .app y) ⟩
    braiding.⇐.η (x , y) ∘ Ψ .app (y , x) ∘ (f .app y ⊗₁ id) ∘ braiding.⇒.η (K₀ x , F₀ y)
    ≈⟨ refl⟩∘⟨ pullˡ-assoc (⟺ isMap) ⟩
    braiding.⇐.η (x , y) ∘ Φ .app (y , x) ∘ (id ⊗₁ g .app x) ∘ braiding.⇒.η (K₀ x , F₀ y)
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ braiding.⇒.sym-commute (g .app x , id) ⟩
    braiding.⇐.η (x , y) ∘ Φ .app (y , x) ∘ braiding.⇒.η (G₀ x , F₀ y) ∘ (g .app x ⊗₁  id)
    ≈˘⟨
     assoc
     ○ refl⟩∘⟨ assoc
     ○ refl⟩∘⟨ refl⟩∘⟨ assoc
     ○ refl⟩∘⟨ refl⟩∘⟨ identityˡ
     ⟩
    (braiding.⇐.η (x , y) ∘ Φ .app (y , x) ∘ id ∘ braiding.⇒.η (G₀ x , F₀ y)) ∘ (g .app x ⊗₁  id) ∎
    where open FIL L
          open FIL M renaming (Φ to Ψ; F to J; G to K)
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

  module _ where
    module REV = Functor REV

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

    open import Categories.Category.Equivalence
    open StrongEquivalence
    open WeakInverse
    selfDual : StrongEquivalence IL IL.op
    selfDual .F = REV.op
    selfDual .G = REV
    selfDual .weak-inverse .F∘G≈id = REV-self-inv
    selfDual .weak-inverse .G∘F≈id = REV-self-inv.op′
