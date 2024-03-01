{-# OPTIONS --without-K --allow-unsolved-metas --lossy-unification #-}
open import Prelude

open import Categories.Category.Construction.Monoids using (Monoids)
open import Categories.Category.Product renaming (Product to ProductCat)
open import Categories.Comonad
open import Categories.Comonad.Morphism using (module Comonad⇒-id) renaming (Comonad⇒-id to _CM⇒_; Comonad⇒-id-id to CM⇒-id; Comonad⇒-id-∘ to _∘CM_)
open import Categories.Monad
open import Categories.Monad.Morphism using (module Monad⇒-id) renaming (Monad⇒-id to _M⇒_; Monad⇒-id-id to M⇒-id; Monad⇒-id-∘ to _∘M_)
open import Categories.NaturalTransformation.NaturalIsomorphism using (unitorˡ; unitorʳ)
open import Relation.Binary using (Rel; IsEquivalence; Setoid)

open NaturalTransformation using (app)

module MCIL.Properties  {o ℓ e} {C : Category o ℓ e} (MC : Monoidal C) where

open import IL (MC) renaming (id to idIL) --using (IL; FILM⟨_,_,_⟩; _⇒ᶠⁱˡ_; IL-monoidal; isFILM; _≃ᶠⁱˡ_)

open import fil (MC) using (FIL; isFIL;FIL[_,_,_])

open import MCIL.Core MC

private
  module C = Category C
  module C² = Category (ProductCat C C)
  module IL = Category IL

open C using (_≈_; _∘_) renaming (id to idC)
open Monoidal MC using (⊗; _⊗₀_; _⊗₁_)

module MonoidObj where
  open import Categories.Object.Monoid IL-monoidal using (Monoid; IsMonoid; Monoid⇒)
  open Monad hiding (F)
  open Comonad hiding (F)
  open MR C
  open C.HomReasoning
  open import Categories.Tactic.Category using (solve)

  private module monoidMC-FIL (M : Monoid) where
    private
      module M = Monoid M
      module L = FIL M.Carrier
      module ML = IsMonoid M.isMonoid
    open L hiding (Φ)
    open L using (Φ) public
    open _⇒ᶠⁱˡ_ using (f; g)

    T : Monad C
    T .Monad.F = F
    T .η = ML.η .f
    T .μ = ML.μ .f
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
    D .ε = ML.η .g
    D .δ = ML.μ .g
    D .assoc     {U} = begin
      D .δ .app (G.₀ U) ∘ D .δ .app U
      ≈⟨ ⟺ C.identityˡ
       ○ (⟺ G.identity) ⟩∘⟨refl
       ○ G.F-resp-≈ (⟺ G.identity) ⟩∘⟨refl
       ○ C.sym-assoc ⟩
      (G.₁ (G.₁ idC) ∘ D .δ .app (G.₀ U)) ∘ D .δ .app U
      ≈⟨ ML.assoc .snd {U} ⟩
      (idC ∘ G.₁ (D .δ .app U) ∘ idC) ∘ D .δ .app U
      ≈⟨ solve C ⟩
      G.₁ (D .δ .app U) ∘ D .δ .app U
      ∎
    D .sym-assoc = ⟺ (D .assoc)
    D .identityˡ {U} = begin
      G.₁ (D .ε .app U) ∘ D .δ .app U
      ≈⟨ solve C ⟩
      ((G.₁ (D .ε .app U)) ∘ idC) ∘ D .δ .app U
      ≈˘⟨ ML.identityʳ .snd {U} ⟩
      idC
      ∎
    D .identityʳ {U} = begin
      D .ε .app (G.₀ U) ∘ D .δ .app U
      ≈⟨ solve C ⟩
      (idC ∘ D .ε .app (G.₀ U)) ∘ D .δ .app U
      ≈˘⟨ ML.identityˡ .snd {U} ⟩
      idC
      ∎
    private
      module T = Monad T
      module D = Comonad D renaming (F to G)

    as-fil : FIL
    as-fil = FIL[ F , G , Φ ]

    open NaturalTransformation using (app)
    module Φ = NaturalTransformation Φ

    triangle : ∀{X Y : C.Obj} → idC ⊗₁ D.ε .app Y ≈ Φ.app (X , Y) ∘ T.η .app X ⊗₁ idC
    triangle {X} {Y} = begin
        idC ⊗₁ D.ε .app Y
        ≈⟨ ⟺ C.identityˡ ⟩
        idC ∘ (idC ⊗₁ D .ε .app Y)
        ≈⟨ unit.isMap {X , Y} ⟩
        Φ.app (X , Y) ∘ T.η .app X ⊗₁ idC
        ∎
      where module unit = _⇒ᶠⁱˡ_ ML.η
    pentagon : ∀{X Y : C.Obj} → Φ.app (X , Y) ∘ Φ.app (T.₀ X , D.₀ Y) ∘ (idC ⊗₁ D.δ .app Y) ≈ Φ.app (X , Y) ∘ (T.μ .app X ⊗₁ idC)
    pentagon {X} {Y} = begin
        Φ.app (X , Y) ∘ Φ.app (T.₀ X , D.₀ Y) ∘ (idC ⊗₁ D.δ .app Y)
        ≈⟨ solve C ⟩
        ((Φ.app (X , Y) ∘ Φ.app (F.₀ X , G.₀ Y)) ∘ idC) ∘ (idC ⊗₁ D .δ .app Y)
        ≈⟨ mult.isMap {X , Y} ⟩
        Φ.app (X , Y) ∘ (T.μ .app X ⊗₁ idC)
        ∎
      where module mult = _⇒ᶠⁱˡ_ ML.μ

  monoid-to-MC-FIL : Monoid → MC-FIL
  monoid-to-MC-FIL m = record { monoidMC-FIL m }

  private module _ {M M' : Monoid} (m⇒ : Monoid⇒ M M') where
    private
      f₁ =  monoid-to-MC-FIL M
      f₂ =  monoid-to-MC-FIL M'
      module f₁ = MC-FIL f₁
      open f₁ using (T; D; Φ)
      module f₂ = MC-FIL f₂
      open f₂ using () renaming (Φ to Ψ; T to T'; D to D')
      module m⇒ = Monoid⇒ m⇒

      module map = _⇒ᶠⁱˡ_ m⇒.arr

    module ⇒mcil where
      open Monad⇒-id
      f : T' M⇒ T
      f .α = map.f
      f .unit-comp {U} = begin
        f .α .app U ∘ T.η .app U
        ≈⟨ m⇒.preserves-η .fst {U} ⟩
        T'.η .app U
        ∎
      f .mult-comp {U} = begin
        f .α .app U ∘ T .μ .app U
        ≈⟨ m⇒.preserves-μ .fst {U} ⟩
        T' .μ .app U ∘ T'.₁ (f .α .app U) ∘ f .α .app (T.₀ U)
        ≈⟨ refl⟩∘⟨ f .α.sym-commute (f .α .app U) ⟩
        T' .μ .app U ∘ f .α .app (T'.₀ U) ∘ T.₁ (f .α .app U)
        ∎

      open Comonad⇒-id
      g : D' CM⇒ D
      g .α = map.g
      g .counit-comp {U} = begin
        D .ε .app U ∘ g .α .app U
        ≈⟨ m⇒.preserves-η .snd {U} ⟩
        D' .ε .app U
        ∎
      g .comult-comp {U} = begin
        D .δ .app U ∘ g .α .app U
        ≈⟨ m⇒.preserves-μ .snd {U} ⟩
        (D.₁ (g .α .app U) ∘ g .α .app (D'.₀ U)) ∘ D' .δ .app U
        ≈⟨ g .α.sym-commute (g .α .app U) ⟩∘⟨refl
         ○ C.assoc ⟩
        g .α .app (D.₀ U) ∘ D'.₁ (g .α .app U) ∘ D' .δ .app U
        ∎

    Monoid⇒-to-⇒ᵐᶜⁱˡ : f₁ ⇒ᵐᶜⁱˡ f₂
    Monoid⇒-to-⇒ᵐᶜⁱˡ = record { ⇒mcil ; isMap = map.isMap }

  module _ where
    open Functor
    equiv⇐ : Functor (Monoids IL-monoidal) MCIL
    equiv⇐ .F₀ = monoid-to-MC-FIL
    equiv⇐ .F₁ = Monoid⇒-to-⇒ᵐᶜⁱˡ
    -- `IL.Equiv.refl` has metavariable issues :(
    equiv⇐ .identity = C.Equiv.refl , C.Equiv.refl
    equiv⇐ .homomorphism = C.Equiv.refl , C.Equiv.refl
    equiv⇐ .F-resp-≈ eq = eq

  module _ where
    open Functor
    equiv⇒ : Functor MCIL (Monoids IL-monoidal)
    equiv⇒ .F₀ = ?
    equiv⇒ .F₁ = ?
    equiv⇒ .identity = ?
    equiv⇒ .homomorphism = ?
    equiv⇒ .F-resp-≈ eq = ?

  module _ where
    open import Categories.Category.Equivalence
    open StrongEquivalence
    open WeakInverse
    equiv : StrongEquivalence MCIL (Monoids IL-monoidal)
    equiv .F = equiv⇒
    equiv .G = equiv⇐
    equiv .weak-inverse .F∘G≈id = ?
    equiv .weak-inverse .G∘F≈id = ?
