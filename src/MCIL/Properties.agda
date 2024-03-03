{-# OPTIONS --without-K --allow-unsolved-metas --lossy-unification #-}
open import Prelude

open import Categories.Category.Construction.Monoids using (Monoids)
open import Categories.Category.Product renaming (Product to ProductCat)
open import Categories.Comonad
open import Categories.Comonad.Morphism using (module Comonad⇒-id) renaming (Comonad⇒-id to _CM⇒_; Comonad⇒-id-id to CM⇒-id; Comonad⇒-id-∘ to _∘CM_)
open import Categories.Monad
open import Categories.Monad.Morphism using (module Monad⇒-id) renaming (Monad⇒-id to _M⇒_; Monad⇒-id-id to M⇒-id; Monad⇒-id-∘ to _∘M_)
import Categories.Morphism as Morphism
open import Categories.NaturalTransformation.NaturalIsomorphism using (unitorˡ; unitorʳ; NIHelper) renaming (refl to reflNI)
open import Relation.Binary using (Rel; IsEquivalence; Setoid)

open NaturalTransformation using (app)

module MCIL.Properties  {o ℓ e} {C : Category o ℓ e} (MC : Monoidal C) where

open import IL (MC) renaming (id to idIL) --using (IL; FILM⟨_,_,_⟩; _⇒ᶠⁱˡ_; IL-monoidal; isFILM; _≃ᶠⁱˡ_)

open import fil (MC) using (FIL; isFIL; FIL[_,_,_])

open import MCIL.Core MC

private
  module C = Category C
  module C² = Category (ProductCat C C)
  module IL = Category IL

open C using (_≈_; _∘_; _⇒_) renaming (id to idC)
open Monoidal MC using (⊗; _⊗₀_; _⊗₁_)
open Monoidal IL-monoidal using () renaming (⊗ to ⊗IL)

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

  private module _ (M : MC-FIL) where
    private
      module M = MC-FIL M
      open M --using (T; D; Φ)

    open IsMonoid
    open _⇒ᶠⁱˡ_
    isMonoid : IsMonoid M.as-fil
    isMonoid .η .f = T .η
    isMonoid .η .g = D .ε
    -- triangle
    isMonoid .η .isMap {(X , Y)} = begin
      idC ∘ (idC ⊗₁ D.ε .app Y)
      ≈˘⟨ ⟺ C.identityˡ ⟩
      idC ⊗₁ D.ε .app Y
      ≈⟨ M.triangle ⟩
      Φ .app (X , Y) ∘ T.η .app X ⊗₁ idC
      ∎
    isMonoid .μ .f = T .μ
    isMonoid .μ .g = D .δ
    -- pentagon
    isMonoid .μ .isMap {(X , Y)} = begin
      ((Φ.app (X , Y) ∘ Φ.app (T.₀ X , D.₀ Y)) ∘ idC) ∘ (idC ⊗₁ D.δ .app Y)
      ≈⟨ solve C ⟩
      Φ.app (X , Y) ∘ Φ.app (T.₀ X , D.₀ Y) ∘ (idC ⊗₁ D.δ .app Y)
      ≈⟨ M.pentagon ⟩
      Φ.app (X , Y) ∘ (T.μ .app X ⊗₁ idC)
      ∎
    isMonoid .assoc .fst {U} = begin
      isMonoid .μ .f .app U ∘ T.₁ idC ∘ isMonoid .μ .f .app (T.₀ U)
      ≈⟨ refl⟩∘⟨ T.identity ⟩∘⟨refl
       ○ refl⟩∘⟨ C.identityˡ  ⟩
      isMonoid .μ .f .app U ∘ isMonoid .μ .f .app (T.₀ U)
      ≈˘⟨ T.assoc {U} ⟩
      isMonoid .μ .f .app U ∘ T.₁ (isMonoid .μ .f .app U)
      ≈⟨ solve C ⟩ -- we have to add some identities to get to the monoid form
      isMonoid .μ .f .app U ∘ (T.₁ ( isMonoid .μ .f .app U) ∘ idC) ∘ idC
      ∎
    isMonoid .identityʳ .fst {U} = begin
      idC
      ≈˘⟨ T.identityˡ {U} ⟩
      T.μ .app U ∘ T.₁ (T.η .app U)
      ≈˘⟨ refl⟩∘⟨ C.identityʳ ⟩
      T.μ .app U ∘ T.₁ (T .η .app U) ∘ idC
      ∎
    isMonoid .identityˡ .fst {U} = begin
      idC
      ≈˘⟨ T.identityʳ {U} ⟩
      T.μ .app U ∘ T.η .app (T.₀ U)
      ≈˘⟨ refl⟩∘⟨ T.identity ⟩∘⟨refl
        ○ refl⟩∘⟨ C.identityˡ ⟩
      T.μ .app U ∘ T.₁ idC ∘ T.η .app (T.₀ U)
      ∎
    isMonoid .identityʳ .snd {U} = begin
      idC
      ≈˘⟨ D .identityˡ {U} ⟩
      D.₁ (D .ε .app U) ∘ D .δ .app U
      ≈⟨ solve C ⟩
      ((D.₁ (D .ε .app U)) ∘ idC) ∘ D .δ .app U
      ∎
    isMonoid .identityˡ .snd {U} = begin
      idC
      ≈˘⟨ D .identityʳ {U} ⟩
      D .ε .app (D.₀ U) ∘ D .δ .app U
      ≈⟨ solve C ⟩
      (idC ∘ D .ε .app (D.₀ U)) ∘ D .δ .app U
      ∎
    isMonoid .assoc .snd {U} = begin
      (D.₁ (D.₁ idC) ∘ D .δ .app (D.₀ U)) ∘ D .δ .app U
      ≈˘⟨ ⟺ C.identityˡ
       ○ (⟺ D.identity) ⟩∘⟨refl
       ○ D.F-resp-≈ (⟺ D.identity) ⟩∘⟨refl
       ○ C.sym-assoc ⟩
      D .δ .app (D.₀ U) ∘ D .δ .app U
      ≈⟨ D .assoc {U} ⟩
      D.₁ (D .δ .app U) ∘ D .δ .app U
      ≈⟨ solve C ⟩
      (idC ∘ D.₁ (D .δ .app U) ∘ idC) ∘ D .δ .app U
      ∎

    MC-FIL-to-monoid : Monoid
    MC-FIL-to-monoid .Monoid.Carrier = M.as-fil
    MC-FIL-to-monoid .Monoid.isMonoid = isMonoid

  private module _ {f₁ f₂ : MC-FIL} (l⇒ : f₁ ⇒ᵐᶜⁱˡ f₂) where
    private
      M  = MC-FIL-to-monoid f₁
      M' = MC-FIL-to-monoid f₂
      module M = Monoid M
      module M' = Monoid M'
      module l⇒ = _⇒ᵐᶜⁱˡ_ l⇒
      open l⇒ using (f; g; isMap)
      open module f₁ = MC-FIL f₁ using (T; D; Φ)
      open module f₂ = MC-FIL f₂ using () renaming (Φ to Ψ; T to T'; D to D')
      --module m⇒ = Monoid⇒ m⇒

    open Monoid⇒
    open Monad⇒-id
    open Comonad⇒-id
    ⇒ᵐᶜⁱˡ-to-Monoid⇒ : Monoid⇒ M M'
    ⇒ᵐᶜⁱˡ-to-Monoid⇒ .arr = l⇒.as-film
    ⇒ᵐᶜⁱˡ-to-Monoid⇒ .preserves-η .fst {U} = f .unit-comp {U}
    ⇒ᵐᶜⁱˡ-to-Monoid⇒ .preserves-μ .fst {U} = begin
        f .α .app U ∘ T .μ .app U
        ≈⟨ f .mult-comp {U} ⟩
        T' .μ .app U ∘ f .α .app (T'.₀ U) ∘ T.₁ (f .α .app U)
        ≈˘⟨ refl⟩∘⟨ f .α.sym-commute (f .α .app U) ⟩
        T' .μ .app U ∘ T'.₁ (f .α .app U) ∘ f .α .app (T.₀ U)
        ∎
    ⇒ᵐᶜⁱˡ-to-Monoid⇒ .preserves-η .snd {U} = g .counit-comp {U}
    ⇒ᵐᶜⁱˡ-to-Monoid⇒ .preserves-μ .snd {U} = begin
        D .δ .app U ∘ g .α .app U
        ≈⟨ g .comult-comp {U} ⟩
        g .α .app (D.₀ U) ∘ D'.₁ (g .α .app U) ∘ D' .δ .app U
        ≈˘⟨ g .α.sym-commute (g .α .app U) ⟩∘⟨refl
         ○ C.assoc ⟩
        (D.₁ (g .α .app U) ∘ g .α .app (D'.₀ U)) ∘ D' .δ .app U
        ∎

  module _ where
    open Functor
    equiv⇒ : Functor MCIL (Monoids IL-monoidal)
    equiv⇒ .F₀ = MC-FIL-to-monoid
    equiv⇒ .F₁ = ⇒ᵐᶜⁱˡ-to-Monoid⇒
    equiv⇒ .identity = C.Equiv.refl , C.Equiv.refl
    equiv⇒ .homomorphism = C.Equiv.refl , C.Equiv.refl
    equiv⇒ .F-resp-≈ eq = eq


  private
    IL-Monoids = (Monoids IL-monoidal)
    module IL-Monoids = Category IL-Monoids
    module MCIL = Category MCIL

  module _ where
    open import Categories.Category.Equivalence
    open StrongEquivalence
    open WeakInverse
    equiv : StrongEquivalence MCIL (Monoids IL-monoidal)
    equiv .F = equiv⇒
    equiv .G = equiv⇐
    equiv .weak-inverse .F∘G≈id = niHelper h
      where open NIHelper
            module _ (M : Monoid) where
              open Monoid⇒
              open Monoid M
              L = monoid-to-MC-FIL M
              open module L = MC-FIL L using (T; D; Φ)

              unit : Monoid⇒ (Functor.F₀ (equiv⇒ ∘F equiv⇐) M) M
              unit .arr = IL.id {Carrier}
              unit .preserves-η .fst = C.identityˡ
              unit .preserves-μ .fst {U} = begin
                idC ∘ T.μ .app U
                ≈⟨ solve C ⟩
                T.μ .app U ∘ idC ∘ idC
                ≈⟨ refl⟩∘⟨ ⟺ T.identity ⟩∘⟨refl ⟩
                T.μ .app U ∘ T.₁ idC ∘ idC
                ∎
              unit .preserves-η .snd = C.identityʳ
              unit .preserves-μ .snd {U} = begin
                D.δ .app U ∘ idC
                ≈⟨ solve C ⟩
                (idC ∘ idC) ∘ D.δ .app U
                ≈⟨ (⟺ D.identity ⟩∘⟨refl) ⟩∘⟨refl ⟩
                (D.₁ idC ∘ idC) ∘ D.δ .app U
                ∎
              -- same as unit, but eta again
              counit : Monoid⇒ M (Functor.F₀ (equiv⇒ ∘F equiv⇐) M)
              counit .arr = IL.id {Carrier}
              counit .preserves-η = unit .preserves-η
              counit .preserves-μ = unit .preserves-μ

              open Morphism.Iso
              iso⇒ : Morphism.Iso IL-Monoids unit counit
              iso⇒ .isoˡ .fst = C.identity²
              iso⇒ .isoˡ .snd = C.identity²
              iso⇒ .isoʳ .fst = C.identity²
              iso⇒ .isoʳ .snd = C.identity²
            h : NIHelper (equiv⇒ ∘F equiv⇐) idF
            h .η   = unit
            h .η⁻¹ = counit
            h .iso = iso⇒
            h .commute f .fst = C.identityˡ ○ ⟺ C.identityʳ
            h .commute f .snd = C.identityʳ ○ ⟺ C.identityˡ
    equiv .weak-inverse .G∘F≈id = niHelper h
      where open NIHelper
            open _⇒ᵐᶜⁱˡ_ using (f; g; isMap)
            open Monad⇒-id
            open Comonad⇒-id
            module _ (X : MC-FIL) where
              open MC-FIL X

              unit : Functor.F₀ (equiv⇐ ∘F equiv⇒) X ⇒ᵐᶜⁱˡ X
              unit .f .α = idN
              unit .f .unit-comp = C.identityˡ
              unit .f .mult-comp {U} = begin
                idC ∘ T.μ .app U
                ≈⟨ solve C ⟩
                T.μ .app U ∘ idC ∘ idC
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ T.identity ⟩
                T.μ .app U ∘ idC ∘ T.₁ idC
                ∎
              unit .g .α = idN
              unit .g .counit-comp = C.identityʳ
              unit .g .comult-comp {U} = begin
                D.δ .app U ∘ idC
                ≈⟨ solve C ⟩
                idC ∘ idC ∘ D.δ .app U
                ≈⟨ refl⟩∘⟨ ⟺ D.identity ⟩∘⟨refl ⟩
                idC ∘ D.₁ idC ∘ D.δ .app U
                ∎
              unit .isMap = C.Equiv.refl
              -- the proofs are the same, but we eta expand again
              counit : X  ⇒ᵐᶜⁱˡ Functor.F₀ (equiv⇐ ∘F equiv⇒) X
              counit .f .α = idN
              counit .f .unit-comp = unit .f .unit-comp
              counit .f .mult-comp = unit .f .mult-comp
              counit .g .α = idN
              counit .g .counit-comp = unit .g .counit-comp
              counit .g .comult-comp = unit .g .comult-comp
              counit .isMap = C.Equiv.refl

              open Morphism.Iso
              iso⇐ : Morphism.Iso MCIL unit counit
              iso⇐ .isoˡ .fst = C.identity²
              iso⇐ .isoˡ .snd = C.identity²
              iso⇐ .isoʳ .fst = C.identity²
              iso⇐ .isoʳ .snd = C.identity²

            h : NIHelper (equiv⇐ ∘F equiv⇒) idF
            h .η = unit
            h .η⁻¹ = counit
            h .iso = iso⇐
            h .commute f .fst = C.identityˡ ○ ⟺ C.identityʳ
            h .commute f .snd = C.identityʳ ○ ⟺ C.identityˡ
