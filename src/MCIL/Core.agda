{-# OPTIONS --without-K --safe --lossy-unification #-}
open import Prelude

open import Categories.NaturalTransformation.NaturalIsomorphism using (unitorˡ; unitorʳ)
open import Relation.Binary using (Rel; IsEquivalence; Setoid)

open NaturalTransformation using (app)

module MCIL.Core  {o ℓ e} {C : Category o ℓ e} (MC : Monoidal C) where

open import IL (MC) renaming (id to idIL) --using (IL; FILM⟨_,_,_⟩; _⇒ᶠⁱˡ_; IL-monoidal; isFILM; _≃ᶠⁱˡ_)

open import fil (MC) using (FIL; isFIL;FIL[_,_,_])

private
  module C = Category C
  module C² = Category (C ×ᶜ C)
  module IL = Category IL

open C using (_≈_; _∘_) renaming (id to idC)
open Monoidal MC using (⊗; _⊗₀_; _⊗₁_)

record mcIL : Set (o ⊔ ℓ ⊔ e) where
  constructor MCIL[_,_,_]
  field
    T : Monad C
    D : Comonad C

  module T = Monad T
  module D = Comonad D renaming (F to G)

  --module F = Functor F
  --module G = Functor G

  field
    ψ : isFIL T.F D.G
  module ψ = NaturalTransformation ψ

  as-fil : FIL
  as-fil = FIL[ T.F , D.G , ψ ]

  --  open Category C using (_∘_; _≈_)
  field
    triangle : ∀{X Y : C.Obj} → idC ⊗₁ D.ε .app Y ≈ ψ.app (X , Y) ∘ T.η .app X ⊗₁ idC
    pentagon : ∀{X Y : C.Obj} → ψ.app (X , Y) ∘ ψ.app (T.₀ X , D.₀ Y) ∘ (idC ⊗₁ D.δ .app Y) ≈ ψ.app (X , Y) ∘ (T.μ .app X ⊗₁ idC)
    -- Really we would like to state this in terms of equality of natural
    -- transformations, but this presents multiple challenges (see other files).
    --
    -- In particular, things like the `unitor` below adds additional unnecessary
    -- identities in the natural transformation. Furthermore, there is no easy
    -- way to state the pentagon identity, as stating it depends on the
    -- associativity of functors on different projections in the product category.
    --
    --triangle' : replaceʳ (⊗ ∘ˡ (idN ⁂ⁿ D.ε)) unitorʳ ≃ ψ ∘ᵥ (⊗ ∘ˡ (T.η ⁂ⁿ idN))
    --pentagon' : ψ ∘ᵥ (ψ ∘ʳ (T.F ⁂ D.G)) ∘ᵥ (⊗ ∘ˡ (idN {F = T.F ∘F T.F} ⁂ⁿ D.δ)) ≃ ψ ∘ᵥ (T.μ ⁂ⁿ idN)

record _⇒ᵐᶜⁱˡ_ (f₁ f₂ : mcIL) : Set (o ⊔ ℓ ⊔ e) where
  --constructor MCILM
  --no-eta-equality
  --pattern
  module f₁ = mcIL f₁
  open f₁ using (T; D; ψ)
  module f₂ = mcIL f₂
  open f₂ using () renaming (ψ to φ; T to T'; D to D')
  field
    -- as defined in agda-categories, S M⇒ T contravariantly induces a natural transformation T ⇒ S.
    f : T' M⇒ T
    -- However, this should means comonad morphisms are covariant. (change this?)
    g : D' CM⇒ D

  module f = Monad⇒-id f
  module g = Comonad⇒-id g
  field
    isMap : isFILM f₁.as-fil f₂.as-fil f.α g.α

  as-film : f₁.as-fil ⇒ᶠⁱˡ f₂.as-fil
  as-film = FILM⟨ f.α , g.α , isMap ⟩

_≃ᵐᶜⁱˡ_ : ∀ {f₁ f₂ : mcIL} → Rel (f₁ ⇒ᵐᶜⁱˡ f₂) (o ⊔ e)
a ≃ᵐᶜⁱˡ b = a.as-film ≃ᶠⁱˡ  b.as-film
  where module a = _⇒ᵐᶜⁱˡ_ a
        module b = _⇒ᵐᶜⁱˡ_ b

module _ {L : mcIL} where
  open _⇒ᵐᶜⁱˡ_
  open _⇒ᶠⁱˡ_
  idMCIL : L ⇒ᵐᶜⁱˡ L
  idMCIL .f = M⇒-id
  idMCIL .g = CM⇒-id
  idMCIL .isMap = IL.id .isMap

module _ {L₁ L₂ L₃ : mcIL} where
  open _⇒ᶠⁱˡ_
  open _⇒ᵐᶜⁱˡ_
  _∘ᵐᶜⁱˡ_ : L₂ ⇒ᵐᶜⁱˡ L₃ → L₁  ⇒ᵐᶜⁱˡ L₂ → L₁ ⇒ᵐᶜⁱˡ L₃
  (α ∘ᵐᶜⁱˡ β) .f = β .f ∘M α .f
  (α ∘ᵐᶜⁱˡ β) .g = β .g ∘CM α .g
  (α ∘ᵐᶜⁱˡ β) .isMap = (α.as-film ∘ᶠⁱˡ β.as-film) .isMap
    where module α = _⇒ᵐᶜⁱˡ_ α
          module β = _⇒ᵐᶜⁱˡ_ β

MCIL : Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) (o ⊔ e)
MCIL = record
  { Obj       = mcIL
  ; _⇒_       = _⇒ᵐᶜⁱˡ_
  ; _≈_       = _≃ᵐᶜⁱˡ_
  ; id        = idMCIL
  ; _∘_       = _∘ᵐᶜⁱˡ_
  -- this is all `; Category IL` but heavily eta expanded lol
  ; ∘-resp-≈  = λ {_} {_} {_} {f} {h} {g} {i} → IL.∘-resp-≈ {f = ↓ f} {↓ h} {↓ g} {↓ i}
  ; assoc     = λ {_} {_} {_} {_} {f} {g} {h} → IL.assoc {f = ↓ f} {↓ g} {↓ h}
  ; sym-assoc = λ {_} {_} {_} {_} {f} {g} {h} → IL.sym-assoc {f = ↓ f} {↓ g} {↓ h}
  ; identityˡ = λ {_} {_} {f = f₁} → IL.identityˡ {f = ↓ f₁}
  ; identityʳ = λ {_} {_} {f = f₁} → IL.identityʳ {f = ↓ f₁}
  ; identity² = λ {A} → IL.identity² {mcIL.as-fil A}
  ; equiv     = λ {f₁ f₂ : mcIL} → record
                  { refl = λ {f} → IL.Equiv.refl {x = ↓ f}
                  ; sym = λ {f} {g} → IL.Equiv.sym {x = ↓ f}
                  ; trans = λ {f} {g} {h} → IL.Equiv.trans {i = ↓ f}
                  }
  }
  where open _⇒ᵐᶜⁱˡ_ renaming (as-film to ↓)
