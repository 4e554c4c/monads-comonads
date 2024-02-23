{-# OPTIONS --without-K --allow-unsolved-metas --lossy-unification #-}
open import Prelude
open import Categories.Category.Product renaming (Product to ProductCat)
open import Relation.Binary using (Rel; IsEquivalence; Setoid)
open import Categories.Category.Construction.Monoids using (Monoids)

module MCIL.Core  {o ℓ e} {C : Category o ℓ e} (MC : Monoidal C) where

open import IL (MC) renaming (id to idIL) using (IL; FILM⟨_,_,_⟩; _⇒ᶠⁱˡ_; IL-monoidal)

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

record MCIL : Set (o ⊔ ℓ ⊔ e) where
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

_⇒ᵐᶜⁱˡ_ :(f₁ f₂ : MCIL) → Set (o ⊔ ℓ ⊔ e)
f₁ ⇒ᵐᶜⁱˡ f₂ = f₁.as-fil ⇒ᶠⁱˡ f₂.as-fil
  where module f₁ = MCIL f₁
        module f₂ = MCIL f₂

MIL : Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) (o ⊔ e)
MIL = record
  { Obj       = MCIL
  ; _⇒_       = _⇒ᵐᶜⁱˡ_
  -- the forgetful functor from MCIL to IL is full, so we can use all of our
  -- proofs from there.
  ; Category IL
  }

{-

module MonoidObj where
  open import Categories.Object.Monoid IL-monoidal using (Monoid; IsMonoid)
  open Monad hiding (F)
  open Comonad hiding (F)

  module _ (L : IL.Obj) (ML : IsMonoid L) where
    open FIL
    open _⇒ᶠⁱˡ_ using (f; g)
    module L = FIL L
    module ML = IsMonoid ML

    source-monad : Monad C
    source-monad .Monad.F = L .F
    source-monad .μ = ML.μ .f
    source-monad .η = ML.η .f
    source-monad .assoc     {X} = {!(ML.sym-assoc .fst) !}
    source-monad .sym-assoc = {! !}
    source-monad .identityˡ = {! !}
    source-monad .identityʳ = {! !}
      where open MR IL

    dest-comonad : Comonad C
    dest-comonad .Comonad.F = L .G
    dest-comonad .δ = ML.μ .g
    dest-comonad .ε = ML.η .g
    dest-comonad .assoc     = {! !}
    dest-comonad .sym-assoc = {! !}
    dest-comonad .identityˡ = {! !}
    dest-comonad .identityʳ = {! !}

  
-}
