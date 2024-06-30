{-# OPTIONS --without-K --lossy-unification --safe #-}
open import Prelude

open import Categories.Category.Construction.Monoids using (Monoids)
import Categories.Morphism as Morphism
open import Categories.NaturalTransformation.NaturalIsomorphism using (unitorˡ; unitorʳ; NIHelper) renaming (refl to reflNI)
open import Relation.Binary using (Rel; IsEquivalence; Setoid)

open NaturalTransformation using (η)

module MCIL.Properties  {o ℓ e} {C : Category o ℓ e} (MC : Monoidal C) where

open import IL (MC) renaming (id to idIL) --using (IL; FILM⟨_,_,_⟩; _⇒ᶠⁱˡ_; IL-monoidal; isFILM; _≃ᶠⁱˡ_)

open import fil (MC) using (FIL; isFIL; FIL[_,_,_])

open import MCIL.Core MC
open import IL.Properties MC using () renaming (stretch to stretch-fil)

private
  module C = Category C
  module C² = Category (C ×ᶜ C)
  module IL = Category IL

open C using (_≈_; _∘_; _⇒_) renaming (id to idC)
open Monoidal MC using (⊗; _⊗₀_; _⊗₁_)
open Monoidal IL-monoidal using () renaming (⊗ to ⊗IL)

module Forget where
  open Functor
  U : Functor MCIL IL
  U .F₀ = mcIL.as-fil
  U .F₁ = _⇒ᵐᶜⁱˡ_.as-film
  U .identity = C.Equiv.refl , C.Equiv.refl
  U .homomorphism = C.Equiv.refl , C.Equiv.refl
  U .F-resp-≈ (e₁ , e₂) = e₁ , e₂

{-
module Stretch (L : mcIL) where
  open module L = mcIL L using (T; D)
  open FIL
  stretch : ∀ {T' D'} → (T M⇒ T') → (D' CM⇒ D) → mcIL
  stretch {T'} {_} _ _ .mcIL.T = T'
  stretch {_} {D'} _ _ .mcIL.D = D'
  stretch f g .mcIL.ψ = stretch-fil L.as-fil f.α g.α .ϕ
    where module f = Monad⇒-id f
          module g = Comonad⇒-id g
  stretch f g .mcIL.triangle = {! !}
  stretch f g .mcIL.pentagon = {! !}
  --stretch {F'} {G'} FIL[ _ , _ , ϕ ] f g = FIL[ F' , G' , ϕ ∘ᵥ ⊗ ∘ˡ (f ⁂ⁿ g) ]
  --stretch {F'} _ _ _ .F = F'
  --stretch {G'} _ _ _ .G = G'
-}

module MonoidObj where
  open import Categories.Object.Monoid IL-monoidal using (Monoid; IsMonoid; Monoid⇒)
  open Monad hiding (F)
  open Comonad hiding (F)
  open MR C
  open C.HomReasoning
  open import Categories.Tactic.Category using (solve)

  private module monoidmcIL (M : Monoid) where
    private
      module M = Monoid M
      module L = FIL M.Carrier
      module ML = IsMonoid M.isMonoid
    open L hiding (ϕ)
    --open L using (ϕ) public
    ψ = L.ϕ

    open _⇒ᶠⁱˡ_ using (f; g)

    T : Monad C
    T .Monad.F = F
    T .η = ML.η .f
    T .μ = ML.μ .f
    T .assoc     {U} = begin
      ML.μ .f .η U ∘ L.F.₁ (ML.μ .f .η U)
      ≈⟨ solve C ⟩ -- we have to add some identities to get to the monoid form
      ML.μ .f .η U ∘ (L.F.₁ ( ML.μ .f .η U) ∘ idC) ∘ idC
      ≈˘⟨ ML.assoc .fst {U} ⟩
      ML.μ .f .η U ∘ L.F.₁ idC ∘ ML.μ .f .η (L.F.₀ U)
      ≈⟨ refl⟩∘⟨ L.F.identity ⟩∘⟨refl
       ○ refl⟩∘⟨ C.identityˡ  ⟩
      ML.μ .f .η U ∘ ML.μ .f .η (L.F.₀ U)
      ∎
    -- monoids don't even have a sym-assoc field... so why do monads?
    T .sym-assoc = ⟺ (T .assoc)
    -- since our directions here are reversed for T, identityˡ and identityʳ are switched!
    T .identityˡ {U} = begin
      T .μ .η U ∘ F.₁ (T .η .η U)
      ≈˘⟨ refl⟩∘⟨ C.identityʳ ⟩
      T .μ .η U ∘ F.₁ (T .η .η U) ∘ idC
      ≈˘⟨ ML.identityʳ .fst {U} ⟩
      idC
      ∎
    T .identityʳ {U} = begin
      T .μ .η U ∘ T .η .η (F.₀ U)
      ≈˘⟨ refl⟩∘⟨ L.F.identity ⟩∘⟨refl
        ○ refl⟩∘⟨ C.identityˡ  ⟩
      T .μ .η U ∘ F.₁ idC ∘ T .η .η (F.₀ U)
      ≈˘⟨ ML.identityˡ .fst {U} ⟩
      idC
      ∎

    D : Comonad C
    D .Comonad.F = G
    D .ε = ML.η .g
    D .δ = ML.μ .g
    D .assoc     {U} = begin
      D .δ .η (G.₀ U) ∘ D .δ .η U
      ≈⟨ ⟺ C.identityˡ
       ○ (⟺ G.identity) ⟩∘⟨refl
       ○ G.F-resp-≈ (⟺ G.identity) ⟩∘⟨refl
       ○ C.sym-assoc ⟩
      (G.₁ (G.₁ idC) ∘ D .δ .η (G.₀ U)) ∘ D .δ .η U
      ≈⟨ ML.assoc .snd {U} ⟩
      (idC ∘ G.₁ (D .δ .η U) ∘ idC) ∘ D .δ .η U
      ≈⟨ solve C ⟩
      G.₁ (D .δ .η U) ∘ D .δ .η U
      ∎
    D .sym-assoc = ⟺ (D .assoc)
    D .identityˡ {U} = begin
      G.₁ (D .ε .η U) ∘ D .δ .η U
      ≈⟨ solve C ⟩
      ((G.₁ (D .ε .η U)) ∘ idC) ∘ D .δ .η U
      ≈˘⟨ ML.identityʳ .snd {U} ⟩
      idC
      ∎
    D .identityʳ {U} = begin
      D .ε .η (G.₀ U) ∘ D .δ .η U
      ≈⟨ solve C ⟩
      (idC ∘ D .ε .η (G.₀ U)) ∘ D .δ .η U
      ≈˘⟨ ML.identityˡ .snd {U} ⟩
      idC
      ∎
    private
      module T = Monad T
      module D = Comonad D renaming (F to G)

    as-fil : FIL
    as-fil = FIL[ F , G , ψ ]

    open NaturalTransformation using (η)
    module ψ = NaturalTransformation ψ

    triangle : ∀{X Y : C.Obj} → idC ⊗₁ D.ε .η Y ≈ ψ.η (X , Y) ∘ T.η .η X ⊗₁ idC
    triangle {X} {Y} = begin
        idC ⊗₁ D.ε .η Y
        ≈⟨ ⟺ C.identityˡ ⟩
        idC ∘ (idC ⊗₁ D .ε .η Y)
        ≈⟨ unit.isMap {X , Y} ⟩
        ψ.η (X , Y) ∘ T.η .η X ⊗₁ idC
        ∎
      where module unit = _⇒ᶠⁱˡ_ ML.η
    pentagon : ∀{X Y : C.Obj} → ψ.η (X , Y) ∘ ψ.η (T.₀ X , D.₀ Y) ∘ (idC ⊗₁ D.δ .η Y) ≈ ψ.η (X , Y) ∘ (T.μ .η X ⊗₁ idC)
    pentagon {X} {Y} = begin
        ψ.η (X , Y) ∘ ψ.η (T.₀ X , D.₀ Y) ∘ (idC ⊗₁ D.δ .η Y)
        ≈⟨ solve C ⟩
        ((ψ.η (X , Y) ∘ ψ.η (F.₀ X , G.₀ Y)) ∘ idC) ∘ (idC ⊗₁ D .δ .η Y)
        ≈⟨ mult.isMap {X , Y} ⟩
        ψ.η (X , Y) ∘ (T.μ .η X ⊗₁ idC)
        ∎
      where module mult = _⇒ᶠⁱˡ_ ML.μ

  monoid-to-mcIL : Monoid → mcIL
  monoid-to-mcIL m = record { monoidmcIL m }

  private module _ {M M' : Monoid} (m⇒ : Monoid⇒ M M') where
    private
      f₁ =  monoid-to-mcIL M
      f₂ =  monoid-to-mcIL M'
      module f₁ = mcIL f₁
      open f₁ using (T; D; ψ)
      module f₂ = mcIL f₂
      open f₂ using () renaming (ψ to φ; T to T'; D to D')
      module m⇒ = Monoid⇒ m⇒

      module map = _⇒ᶠⁱˡ_ m⇒.arr

    module ⇒mcil where
      open Monad⇒-id
      f : T' M⇒ T
      f .α = map.f
      f .unit-comp {U} = begin
        f .α .η U ∘ T.η .η U
        ≈⟨ m⇒.preserves-η .fst {U} ⟩
        T'.η .η U
        ∎
      f .mult-comp {U} = begin
        f .α .η U ∘ T .μ .η U
        ≈⟨ m⇒.preserves-μ .fst {U} ⟩
        T' .μ .η U ∘ T'.₁ (f .α .η U) ∘ f .α .η (T.₀ U)
        ≈⟨ refl⟩∘⟨ f .α.sym-commute (f .α .η U) ⟩
        T' .μ .η U ∘ f .α .η (T'.₀ U) ∘ T.₁ (f .α .η U)
        ∎

      open Comonad⇒-id
      g : D' CM⇒ D
      g .α = map.g
      g .counit-comp {U} = begin
        D .ε .η U ∘ g .α .η U
        ≈⟨ m⇒.preserves-η .snd {U} ⟩
        D' .ε .η U
        ∎
      g .comult-comp {U} = begin
        D .δ .η U ∘ g .α .η U
        ≈⟨ m⇒.preserves-μ .snd {U} ⟩
        (D.₁ (g .α .η U) ∘ g .α .η (D'.₀ U)) ∘ D' .δ .η U
        ≈⟨ g .α.sym-commute (g .α .η U) ⟩∘⟨refl
         ○ C.assoc ⟩
        g .α .η (D.₀ U) ∘ D'.₁ (g .α .η U) ∘ D' .δ .η U
        ∎

    Monoid⇒-to-⇒ᵐᶜⁱˡ : f₁ ⇒ᵐᶜⁱˡ f₂
    Monoid⇒-to-⇒ᵐᶜⁱˡ = record { ⇒mcil ; isMap = map.isMap }

  module _ where
    open Functor
    equiv⇐ : Functor (Monoids IL-monoidal) MCIL
    equiv⇐ .F₀ = monoid-to-mcIL
    equiv⇐ .F₁ = Monoid⇒-to-⇒ᵐᶜⁱˡ
    -- `IL.Equiv.refl` has metavariable issues :(
    equiv⇐ .identity = C.Equiv.refl , C.Equiv.refl
    equiv⇐ .homomorphism = C.Equiv.refl , C.Equiv.refl
    equiv⇐ .F-resp-≈ eq = eq

  private module _ (M : mcIL) where
    private
      module M = mcIL M
      open M --using (T; D; Φ)


    open IsMonoid
    open _⇒ᶠⁱˡ_
    isMonoid : IsMonoid M.as-fil
    isMonoid .η .f = T .η
    isMonoid .η .g = D .ε
    -- triangle
    isMonoid .η .isMap {(X , Y)} = begin
      idC ∘ (idC ⊗₁ D.ε .η Y)
      ≈˘⟨ ⟺ C.identityˡ ⟩
      idC ⊗₁ D.ε .η Y
      ≈⟨ M.triangle ⟩
      ψ.η (X , Y) ∘ T.η .η X ⊗₁ idC
      ∎
    isMonoid .μ .f = T .μ
    isMonoid .μ .g = D .δ
    -- pentagon
    isMonoid .μ .isMap {(X , Y)} = begin
      ((ψ.η (X , Y) ∘ ψ.η (T.₀ X , D.₀ Y)) ∘ idC) ∘ (idC ⊗₁ D.δ .η Y)
      ≈⟨ solve C ⟩
      ψ.η (X , Y) ∘ ψ.η (T.₀ X , D.₀ Y) ∘ (idC ⊗₁ D.δ .η Y)
      ≈⟨ M.pentagon ⟩
      ψ.η (X , Y) ∘ (T.μ .η X ⊗₁ idC)
      ∎
    isMonoid .assoc .fst {U} = begin
      isMonoid .μ .f .η U ∘ T.₁ idC ∘ isMonoid .μ .f .η (T.₀ U)
      ≈⟨ refl⟩∘⟨ T.identity ⟩∘⟨refl
       ○ refl⟩∘⟨ C.identityˡ  ⟩
      isMonoid .μ .f .η U ∘ isMonoid .μ .f .η (T.₀ U)
      ≈˘⟨ T.assoc {U} ⟩
      isMonoid .μ .f .η U ∘ T.₁ (isMonoid .μ .f .η U)
      ≈⟨ solve C ⟩ -- we have to add some identities to get to the monoid form
      isMonoid .μ .f .η U ∘ (T.₁ ( isMonoid .μ .f .η U) ∘ idC) ∘ idC
      ∎
    isMonoid .identityʳ .fst {U} = begin
      idC
      ≈˘⟨ T.identityˡ {U} ⟩
      T.μ .η U ∘ T.₁ (T.η .η U)
      ≈˘⟨ refl⟩∘⟨ C.identityʳ ⟩
      T.μ .η U ∘ T.₁ (T .η .η U) ∘ idC
      ∎
    isMonoid .identityˡ .fst {U} = begin
      idC
      ≈˘⟨ T.identityʳ {U} ⟩
      T.μ .η U ∘ T.η .η (T.₀ U)
      ≈˘⟨ refl⟩∘⟨ T.identity ⟩∘⟨refl
        ○ refl⟩∘⟨ C.identityˡ ⟩
      T.μ .η U ∘ T.₁ idC ∘ T.η .η (T.₀ U)
      ∎
    isMonoid .identityʳ .snd {U} = begin
      idC
      ≈˘⟨ D .identityˡ {U} ⟩
      D.₁ (D .ε .η U) ∘ D .δ .η U
      ≈⟨ solve C ⟩
      ((D.₁ (D .ε .η U)) ∘ idC) ∘ D .δ .η U
      ∎
    isMonoid .identityˡ .snd {U} = begin
      idC
      ≈˘⟨ D .identityʳ {U} ⟩
      D .ε .η (D.₀ U) ∘ D .δ .η U
      ≈⟨ solve C ⟩
      (idC ∘ D .ε .η (D.₀ U)) ∘ D .δ .η U
      ∎
    isMonoid .assoc .snd {U} = begin
      (D.₁ (D.₁ idC) ∘ D .δ .η (D.₀ U)) ∘ D .δ .η U
      ≈˘⟨ ⟺ C.identityˡ
       ○ (⟺ D.identity) ⟩∘⟨refl
       ○ D.F-resp-≈ (⟺ D.identity) ⟩∘⟨refl
       ○ C.sym-assoc ⟩
      D .δ .η (D.₀ U) ∘ D .δ .η U
      ≈⟨ D .assoc {U} ⟩
      D.₁ (D .δ .η U) ∘ D .δ .η U
      ≈⟨ solve C ⟩
      (idC ∘ D.₁ (D .δ .η U) ∘ idC) ∘ D .δ .η U
      ∎

    mcIL-to-monoid : Monoid
    mcIL-to-monoid .Monoid.Carrier = M.as-fil
    mcIL-to-monoid .Monoid.isMonoid = isMonoid

  private module _ {f₁ f₂ : mcIL} (l⇒ : f₁ ⇒ᵐᶜⁱˡ f₂) where
    private
      M  = mcIL-to-monoid f₁
      M' = mcIL-to-monoid f₂
      module M = Monoid M
      module M' = Monoid M'
      module l⇒ = _⇒ᵐᶜⁱˡ_ l⇒
      open l⇒ using (f; g; isMap)
      open module f₁ = mcIL f₁ using (T; D; ψ)
      open module f₂ = mcIL f₂ using () renaming (ψ to φ; T to T'; D to D')
      --module m⇒ = Monoid⇒ m⇒

    open Monoid⇒
    open Monad⇒-id
    open Comonad⇒-id
    ⇒ᵐᶜⁱˡ-to-Monoid⇒ : Monoid⇒ M M'
    ⇒ᵐᶜⁱˡ-to-Monoid⇒ .arr = l⇒.as-film
    ⇒ᵐᶜⁱˡ-to-Monoid⇒ .preserves-η .fst {U} = f .unit-comp {U}
    ⇒ᵐᶜⁱˡ-to-Monoid⇒ .preserves-μ .fst {U} = begin
        f .α .η U ∘ T .μ .η U
        ≈⟨ f .mult-comp {U} ⟩
        T' .μ .η U ∘ f .α .η (T'.₀ U) ∘ T.₁ (f .α .η U)
        ≈˘⟨ refl⟩∘⟨ f .α.sym-commute (f .α .η U) ⟩
        T' .μ .η U ∘ T'.₁ (f .α .η U) ∘ f .α .η (T.₀ U)
        ∎
    ⇒ᵐᶜⁱˡ-to-Monoid⇒ .preserves-η .snd {U} = g .counit-comp {U}
    ⇒ᵐᶜⁱˡ-to-Monoid⇒ .preserves-μ .snd {U} = begin
        D .δ .η U ∘ g .α .η U
        ≈⟨ g .comult-comp {U} ⟩
        g .α .η (D.₀ U) ∘ D'.₁ (g .α .η U) ∘ D' .δ .η U
        ≈˘⟨ g .α.sym-commute (g .α .η U) ⟩∘⟨refl
         ○ C.assoc ⟩
        (D.₁ (g .α .η U) ∘ g .α .η (D'.₀ U)) ∘ D' .δ .η U
        ∎

  module _ where
    open Functor
    equiv⇒ : Functor MCIL (Monoids IL-monoidal)
    equiv⇒ .F₀ = mcIL-to-monoid
    equiv⇒ .F₁ = ⇒ᵐᶜⁱˡ-to-Monoid⇒
    equiv⇒ .identity = C.Equiv.refl , C.Equiv.refl
    equiv⇒ .homomorphism = C.Equiv.refl , C.Equiv.refl
    equiv⇒ .F-resp-≈ eq = eq


  --IL-Monoids : Category (o ⊔ ℓ ⊔ e ⊔ (o ⊔ ℓ ⊔ e) ⊔ (o ⊔ e)) (o ⊔ ℓ ⊔ e ⊔ (o ⊔ e)) (o ⊔ e)
  IL-Monoids = (Monoids IL-monoidal)
  --IL-Monoids' : Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) (o ⊔ e)
  --IL-Monoids' = IL-Monoids
  private
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
              L = monoid-to-mcIL M
              open module L = mcIL L using (T; D; ψ)

              unit : Monoid⇒ (Functor.F₀ (equiv⇒ ∘F equiv⇐) M) M
              unit .arr = IL.id {Carrier}
              unit .preserves-η .fst = C.identityˡ
              unit .preserves-μ .fst {U} = begin
                idC ∘ T.μ .η U
                ≈⟨ solve C ⟩
                T.μ .η U ∘ idC ∘ idC
                ≈⟨ refl⟩∘⟨ ⟺ T.identity ⟩∘⟨refl ⟩
                T.μ .η U ∘ T.₁ idC ∘ idC
                ∎
              unit .preserves-η .snd = C.identityʳ
              unit .preserves-μ .snd {U} = begin
                D.δ .η U ∘ idC
                ≈⟨ solve C ⟩
                (idC ∘ idC) ∘ D.δ .η U
                ≈⟨ (⟺ D.identity ⟩∘⟨refl) ⟩∘⟨refl ⟩
                (D.₁ idC ∘ idC) ∘ D.δ .η U
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
            module _ (X : mcIL) where
              open mcIL X

              unit : Functor.F₀ (equiv⇐ ∘F equiv⇒) X ⇒ᵐᶜⁱˡ X
              unit .f .α = idN
              unit .f .unit-comp = C.identityˡ
              unit .f .mult-comp {U} = begin
                idC ∘ T.μ .η U
                ≈⟨ solve C ⟩
                T.μ .η U ∘ idC ∘ idC
                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ T.identity ⟩
                T.μ .η U ∘ idC ∘ T.₁ idC
                ∎
              unit .g .α = idN
              unit .g .counit-comp = C.identityʳ
              unit .g .comult-comp {U} = begin
                D.δ .η U ∘ idC
                ≈⟨ solve C ⟩
                idC ∘ idC ∘ D.δ .η U
                ≈⟨ refl⟩∘⟨ ⟺ D.identity ⟩∘⟨refl ⟩
                idC ∘ D.₁ idC ∘ D.δ .η U
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
