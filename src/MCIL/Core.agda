{-# OPTIONS --without-K --allow-unsolved-metas --lossy-unification #-}
open import Prelude
open import Categories.Category.Product renaming (Product to ProductCat)
open import Relation.Binary using (Rel; IsEquivalence; Setoid)
open import Categories.Category.Construction.Monoids using (Monoids)

module MCIL.Core  {o ℓ e} {C : Category o ℓ e} (MC : Monoidal C) where

open import IL (MC) renaming (id to idIL) using (IL; FILM⟨_,_,_⟩; _⇒ᶠⁱˡ_; IL-monoidal; isFILM; _≃ᶠⁱˡ_)

open import fil (MC) using (FIL; isFIL;FIL[_,_,_])

private
  module C = Category C
  module C² = Category (ProductCat C C)
  module IL = Category IL
open Monoidal MC using (⊗; _⊗₀_; _⊗₁_)

open C renaming (id to idC)


--open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

-- doesn't work with sloppy unification
--MCIL : Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) (o ⊔ e)
--MCIL = Monoids IL-monoidal

open import Categories.Monad
open import Categories.Comonad
open import Categories.NaturalTransformation.NaturalIsomorphism using (unitorˡ; unitorʳ)

record MC-FIL : Set (o ⊔ ℓ ⊔ e) where
  constructor MCIL[_,_,_]
  field
    T : Monad C
    D : Comonad C

  module T = Monad T
  module D = Comonad D renaming (F to G)

  --module F = Functor F
  --module G = Functor G

  field
    Φ : isFIL T.F D.G
  module Φ = NaturalTransformation Φ

  as-fil : FIL
  as-fil = FIL[ T.F , D.G , Φ ]

  open NaturalTransformation using (app)

  --  open Category C using (_∘_; _≈_)
  field
    triangle : ∀{X Y : C.Obj} → idC ⊗₁ D.ε .app Y ≈ Φ.app (X , Y) ∘ T.η .app X ⊗₁ idC
    pentagon : ∀{X Y : C.Obj} → Φ.app (X , Y) ∘ Φ.app (T.F.₀ X , D.G.₀ Y) ∘ (idC ⊗₁ D.δ .app Y) ≈ Φ.app (X , Y) ∘ (T.μ .app X ⊗₁ idC)
    -- Really we would like to state this in terms of equality of natural
    -- transformations, but this presents multiple challenges (see other files).
    --
    -- In particular, things like the `unitor` below adds additional unnecessary
    -- identities in the natural transformation. Furthermore, there is no easy
    -- way to state the pentagon identity, as stating it depends on the
    -- associativity of functors on different projections in the product category.
    --
    --triangle' : replaceʳ (⊗ ∘ˡ (idN ⁂ⁿ D.ε)) unitorʳ ≃ Φ ∘ᵥ (⊗ ∘ˡ (T.η ⁂ⁿ idN))
    --pentagon' : Φ ∘ᵥ (Φ ∘ʳ (T.F ⁂ D.G)) ∘ᵥ (⊗ ∘ˡ (idN {F = T.F ∘F T.F} ⁂ⁿ D.δ)) ≃ Φ ∘ᵥ (T.μ ⁂ⁿ idN)

open import Categories.Monad.Morphism using (module Monad⇒-id) renaming (Monad⇒-id to _M⇒_)
open import Categories.Comonad.Morphism using (module Comonad⇒-id) renaming (Comonad⇒-id to _CM⇒_)
record _⇒ᵐᶜⁱˡ_ (f₁ f₂ : MC-FIL) : Set (o ⊔ ℓ ⊔ e) where
  constructor MCILM⟨_,_,_⟩
  --no-eta-equality
  --pattern
  module f₁ = MC-FIL f₁
  open f₁ using (T; D; Φ)
  module f₂ = MC-FIL f₂
  open f₂ using () renaming (Φ to Ψ; T to T'; D to D')
  field
    -- as defined in agda-categories, S M⇒ T contravariantly induces a natural transformation T ⇒ S.
    f : T' M⇒ T
    -- However, this should mean that comonad morphisms are covariant. (change this?)
    g : D' CM⇒ D

  module f = Monad⇒-id f
  module g = Comonad⇒-id g
  field
    isMap : isFILM f₁.as-fil f₂.as-fil f.α g.α

  as-film : f₁.as-fil ⇒ᶠⁱˡ f₂.as-fil
  as-film = FILM⟨ f.α , g.α , isMap ⟩

_≃ᵐᶜⁱˡ_ : ∀ {f₁ f₂ : MC-FIL} → Rel (f₁ ⇒ᵐᶜⁱˡ f₂) (o ⊔ e)
a ≃ᵐᶜⁱˡ b = a.as-film ≃ᶠⁱˡ  b.as-film
  where module a = _⇒ᵐᶜⁱˡ_ a
        module b = _⇒ᵐᶜⁱˡ_ b

private module _ {L : MC-FIL} where
  open _⇒ᵐᶜⁱˡ_
  id : L ⇒ᵐᶜⁱˡ L
  id .f = ?
  id .g = ?
  id .isMap = ?

MCIL : Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) (o ⊔ e)
MCIL = record
  { Obj       = MC-FIL
  ; _⇒_       = _⇒ᵐᶜⁱˡ_
  -- the forgetful functor from MCIL to IL is full, so we can use all of our
  -- proofs from there.
  ; _≈_       = _≃ᵐᶜⁱˡ_
  ; id        = {! !}
  ; _∘_       = {! !}
  ; assoc     = {! !}
  ; sym-assoc = {! !}
  ; identityˡ = {! !}
  ; identityʳ = {! !}
  ; identity² = {! !}
  ; equiv     = {! !}
  ; ∘-resp-≈  = {! !}
  }
{-

module MonoidObj where
  open import Categories.Object.Monoid IL-monoidal using (Monoid; IsMonoid)
  open Monad hiding (F)
  open Comonad hiding (F)

  private module foo (L : FIL) (ML : IsMonoid L) where
    open FIL L
    open _⇒ᶠⁱˡ_ using (f; g)
    module L = FIL L
    module ML = IsMonoid ML

    T : Monad C
    T .Monad.F = F
    T .μ = ML.μ .f
    T .η = ML.η .f
    T .assoc     {X} = {!(ML.sym-assoc .fst) !}
    T .sym-assoc = {! !}
    T .identityˡ = {! !}
    T .identityʳ = {! !}
      where open MR IL

    D : Comonad C
    D .Comonad.F = G
    D .δ = ML.μ .g
    D .ε = ML.η .g
    D .assoc     = {! !}
    D .sym-assoc = {! !}
    D .identityˡ = {! !}
    D .identityʳ = {! !}

    module T = Monad T
    module D = Comonad D renaming (F to G)

    module Φ = NaturalTransformation Φ

    as-fil : FIL
    as-fil = FIL[ T.F , D.G , Φ ]

    open NaturalTransformation using (app)

    triangle : ∀{X Y : C.Obj} → idC ⊗₁ D.ε .app Y ≈ Φ.app (X , Y) ∘ T.η .app X ⊗₁ idC
    pentagon : ∀{X Y : C.Obj} → Φ.app (X , Y) ∘ Φ.app (T.F.₀ X , D.G.₀ Y) ∘ (idC ⊗₁ D.δ .app Y) ≈ Φ.app (X , Y) ∘ (T.μ .app X ⊗₁ idC)

  module _ where
    open Functor
    iso : Functor (Monoids IL-monoidal) MCIL
    iso .F₀ o = {! !}
      where open Monoid 
    iso .F₁ = {! !}
    iso .identity = {! !}
    iso .homomorphism = {! !}
    iso .F-resp-≈ _ = {! !}
-}
