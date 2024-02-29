{-# OPTIONS --without-K --allow-unsolved-metas --lossy-unification #-}
open import Prelude
open import Categories.Category.Product renaming (Product to ProductCat)
open import Relation.Binary using (Rel; IsEquivalence; Setoid)
open import Categories.Category.Construction.Monoids using (Monoids)

open import Categories.Monad.Morphism using (module Monad⇒-id) renaming (Monad⇒-id to _M⇒_; Monad⇒-id-id to M⇒-id; Monad⇒-id-∘ to _∘M_)
open import Categories.Comonad.Morphism using (module Comonad⇒-id) renaming (Comonad⇒-id to _CM⇒_; Comonad⇒-id-id to CM⇒-id; Comonad⇒-id-∘ to _∘CM_)

open NaturalTransformation using (app)

module MCIL.Core  {o ℓ e} {C : Category o ℓ e} (MC : Monoidal C) where

open import IL (MC) renaming (id to idIL) --using (IL; FILM⟨_,_,_⟩; _⇒ᶠⁱˡ_; IL-monoidal; isFILM; _≃ᶠⁱˡ_)

open import fil (MC) using (FIL; isFIL;FIL[_,_,_])

private
  module C = Category C
  module C² = Category (ProductCat C C)
  module IL = Category IL
open Monoidal MC using (⊗; _⊗₀_; _⊗₁_)

open C using (_≈_; _∘_) renaming (id to idC)


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

module _ {L : MC-FIL} where
  open _⇒ᵐᶜⁱˡ_
  open _⇒ᶠⁱˡ_
  idMCIL : L ⇒ᵐᶜⁱˡ L
  idMCIL .f = M⇒-id
  idMCIL .g = CM⇒-id
  idMCIL .isMap = IL.id .isMap

module _ {L₁ L₂ L₃ : MC-FIL} where
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
  { Obj       = MC-FIL
  ; _⇒_       = _⇒ᵐᶜⁱˡ_
  ; _≈_       = _≃ᵐᶜⁱˡ_
  ; id        = idMCIL
  ; _∘_       = _∘ᵐᶜⁱˡ_
  -- this is all `; Category IL` but heavily eta expanded lol
  ; ∘-resp-≈  = λ {_} {_} {_} {f} {h} {g} {i} → IL.∘-resp-≈ {f = as-film f} {as-film h} {as-film g} {as-film i}
  ; assoc     = λ {_} {_} {_} {_} {f} {g} {h} → IL.assoc {f = as-film f} {as-film g} {as-film h}
  ; sym-assoc = λ {_} {_} {_} {_} {f} {g} {h} → IL.sym-assoc {f = as-film f} {as-film g} {as-film h}
  ; identityˡ = λ {_} {_} {f = f₁} → IL.identityˡ {f = as-film f₁}
  ; identityʳ = λ {_} {_} {f = f₁} → IL.identityʳ {f = as-film f₁}
  ; identity² = λ {A} → IL.identity² {MC-FIL.as-fil A}
  ; equiv     = λ {f₁ f₂ : MC-FIL} → record
                  { refl = λ {f} → IL.Equiv.refl {x = as-film f}
                  ; sym = λ {f} {g} → IL.Equiv.sym {x = as-film f}
                  ; trans = λ {f} {g} {h} → IL.Equiv.trans {i = as-film f}
                  }
  }
  where open _⇒ᵐᶜⁱˡ_

module MonoidObj where
  open import Categories.Object.Monoid IL-monoidal using (Monoid; IsMonoid)
  open Monad hiding (F)
  open Comonad hiding (F)
  open MR C
  open C.HomReasoning
  open import Categories.Tactic.Category using (solve)

  private module monoidMC-FIL {L : FIL} (ML : IsMonoid L) where
    open FIL L hiding (Φ)
    open FIL L using (Φ) public
    open _⇒ᶠⁱˡ_ using (f; g)
    private
      module L = FIL L
      module ML = IsMonoid ML

    T : Monad C
    T .Monad.F = F
    T .μ = ML.μ .f
    T .η = ML.η .f
    T .assoc     {U} = begin
      ML.μ .f .app U ∘ L.F.₁ (ML.μ .f .app U)
      ≈⟨ solve C ⟩ -- we have to add some identities to get to the monoid form
      ML.μ .f .app U ∘ (L.F.₁ ( ML.μ .f .app U) ∘ idC) ∘ idC
      ≈˘⟨ ML.assoc .fst {U} ⟩
      ML.μ .f .app U ∘ L.F.₁ idC ∘ ML.μ .f .app (L.F.₀ U)
      ≈⟨ refl⟩∘⟨ L.F.identity ⟩∘⟨refl
       ○ refl⟩∘⟨ C.identityˡ  ⟩
      ML.μ .f .app U ∘ ML.μ .f .app (L.F.₀ U)
      ∎
    -- monoids don't even have a sym-assoc field... so why do monads?
    T .sym-assoc = ⟺ (T .assoc)
    -- since our directions here are reversed for T, identityˡ and identityʳ are switched!
    T .identityˡ {U} = begin
      T .μ .app U ∘ F.₁ (T .η .app U)
      ≈˘⟨ refl⟩∘⟨ C.identityʳ ⟩
      T .μ .app U ∘ F.₁ (T .η .app U) ∘ idC
      ≈˘⟨ ML.identityʳ .fst {U} ⟩
      idC
      ∎
    T .identityʳ {U} = begin
      T .μ .app U ∘ T .η .app (F.₀ U)
      ≈˘⟨ refl⟩∘⟨ L.F.identity ⟩∘⟨refl
        ○ refl⟩∘⟨ C.identityˡ  ⟩
      T .μ .app U ∘ F.₁ idC ∘ T .η .app (F.₀ U)
      ≈˘⟨ ML.identityˡ .fst {U} ⟩
      idC
      ∎

    D : Comonad C
    D .Comonad.F = G
    D .δ = ML.μ .g
    D .ε = ML.η .g
    D .assoc     = {! !}
    D .sym-assoc = ⟺ (D .assoc)
    D .identityˡ = {! !}
    D .identityʳ = {! !}

    private
      module T = Monad T
      module D = Comonad D renaming (F to G)


    as-fil : FIL
    as-fil = FIL[ T.F , D.G , Φ ]

    open NaturalTransformation using (app)
    module Φ = NaturalTransformation Φ

    triangle : ∀{X Y : C.Obj} → idC ⊗₁ D.ε .app Y ≈ Φ.app (X , Y) ∘ T.η .app X ⊗₁ idC
    triangle = {! !}
    pentagon : ∀{X Y : C.Obj} → Φ.app (X , Y) ∘ Φ.app (T.F.₀ X , D.G.₀ Y) ∘ (idC ⊗₁ D.δ .app Y) ≈ Φ.app (X , Y) ∘ (T.μ .app X ⊗₁ idC)
    pentagon = {! !}

  module _ where
    open Functor
    iso : Functor (Monoids IL-monoidal) MCIL
    iso .F₀ o = record { monoidMC-FIL (o .isMonoid) }
      where open Monoid
    iso .F₁ = {! !}
    iso .identity = {! !}
    iso .homomorphism = {! !}
    iso .F-resp-≈ _ = {! !}
