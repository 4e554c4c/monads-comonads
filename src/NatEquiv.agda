{-# OPTIONS --without-K --hidden-argument-puns --allow-unsolved-metas --lossy-unification #-}
open import Categories.Category using (Category)
open import Categories.Category.Product using (_⁂_; _⁂ⁿ_)
open import Categories.Functor using (Functor) renaming (id to idF)
import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation using (NaturalTransformation; _∘ʳ_; _∘ˡ_; _∘ᵥ_; _∘ₕ_) renaming (id to idN)
--open import Categories.NaturalTransformation.Equivalence using (_≃_; ≃-isEquivalence)
open import Categories.Functor using (Endofunctor) renaming (id to idF)
open import Relation.Binary using (Rel; IsEquivalence; Setoid)

open import Level using (_⊔_) renaming (suc to lsuc)

module NatEquiv {o ℓ e}  where

infix 4 _≃_
-- We use a one-constructor data type, instead of a type alias or record to avoid eta equality.
-- This avoids Agda eagerly expanding the definition of _≃_ as a function, and improves unification.
data _≃_ {C D : Category o ℓ e} {F G : Functor C D} : Rel (NaturalTransformation F G) (o ⊔ ℓ ⊔ e) where
  ≃-ext : (let open Category D) {α β : NaturalTransformation F G} →
          (∀ {x} → (NaturalTransformation.η α x) ≈ (NaturalTransformation.η β x)) →
          α ≃ β

private
  variable
    C D : Category o ℓ e
    F G : Functor C D
    α β : NaturalTransformation F G
    δ γ : NaturalTransformation F G

≃-isEquivalence : ∀ {F G : Functor C D} → IsEquivalence (_≃_ {F = F} {G = G})
≃-isEquivalence {D} = record
  { refl = ≃-ext refl
  ; sym   = λ { (≃-ext f) → ≃-ext (sym f) }
  ; trans = λ { (≃-ext f) (≃-ext g) → ≃-ext (trans f g) }
  }
  where open Category.Equiv D


∘ᵥ-resp-≃ : δ ≃ γ → α ≃ β → δ ∘ᵥ α ≃ γ ∘ᵥ β
∘ᵥ-resp-≃ {_} {(D)} (≃-ext f) (≃-ext g) = ≃-ext (∘-resp-≈ f g)
  where open Category D

∘ᵥ-assoc : (δ ∘ᵥ β) ∘ᵥ α ≃ δ ∘ᵥ β ∘ᵥ α
∘ᵥ-assoc {_} {(D)} = ≃-ext assoc
  where open Category D

∘ᵥ-resp-≃ˡ : δ ≃ γ → δ ∘ᵥ α ≃ γ ∘ᵥ α
∘ᵥ-resp-≃ˡ {α} e = ∘ᵥ-resp-≃ e (refl {x = α})
  where open IsEquivalence ≃-isEquivalence

∘ᵥ-resp-≃ʳ : α ≃ β → δ ∘ᵥ α ≃ δ ∘ᵥ β
∘ᵥ-resp-≃ʳ {δ} e = ∘ᵥ-resp-≃ (refl {x = δ}) e
  where open IsEquivalence ≃-isEquivalence

∘ₕ-resp-≃ : ∀ {E : Category o ℓ e} {F G : Functor C D} {K J : Functor D E}
          {α : NaturalTransformation F G} {β : NaturalTransformation F G}
          {δ : NaturalTransformation K J} {γ : NaturalTransformation K J} →
          δ ≃ γ → α ≃ β → δ ∘ₕ α ≃ γ ∘ₕ β
∘ₕ-resp-≃ {E} {J} (≃-ext f) (≃-ext g) = ≃-ext (∘-resp-≈ (J-resp-≈ g) f)
  where open Category E
        open Functor J renaming (F-resp-≈ to J-resp-≈)

∘ₕ-resp-≃ˡ : δ ≃ γ → δ ∘ₕ α ≃ γ ∘ₕ α
∘ₕ-resp-≃ˡ {α} e = ∘ₕ-resp-≃ e (refl {x = α})
  where open IsEquivalence ≃-isEquivalence

∘ₕ-resp-≃ʳ : α ≃ β → δ ∘ₕ α ≃ δ ∘ₕ β
∘ₕ-resp-≃ʳ {δ} e = ∘ₕ-resp-≃ (refl {x = δ}) e
  where open IsEquivalence ≃-isEquivalence

∘ˡ-resp-≃ʳ : α ≃ β → F ∘ˡ α ≃ F ∘ˡ β
∘ˡ-resp-≃ʳ {F = F} (≃-ext e) = ≃-ext (F-resp-≈ e)
  where open Functor F

-- Here the whiskered functor is more important, so we give it the name 'F'
∘ˡ-distr-∘ᵥ : ∀ {E : Category o ℓ e} {F : Functor D E} {G H I : Functor C D}
                  {α : NaturalTransformation H I} {β : NaturalTransformation G H} →
                  F ∘ˡ (α ∘ᵥ β) ≃ (F ∘ˡ α) ∘ᵥ (F ∘ˡ β)
∘ˡ-distr-∘ᵥ {F = F} = ≃-ext F.homomorphism
  where module F = Functor F

≃-setoid : ∀ {F G : Functor C D} → Setoid (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e)
≃-setoid {F} {G} = record
  { Carrier       = NaturalTransformation F G
  ; _≈_           = _≃_
  ; isEquivalence = ≃-isEquivalence
  }

module NatReasoning where

  module _ {F G : Functor C D} where
    open import Relation.Binary.Reasoning.Setoid (≃-setoid  {F = F} {G}) public
    infixr 4 _⟩∘ᵥ⟨_ refl⟩∘ᵥ⟨_ _⟩∘ₕ⟨_ refl⟩∘ₕ⟨_
    infixl 5 _⟩∘ᵥ⟨refl _⟩∘ₕ⟨refl

    _⟩∘ᵥ⟨_ : δ ≃ γ → α ≃ β → δ ∘ᵥ α ≃ γ ∘ᵥ β
    _⟩∘ᵥ⟨_ = ∘ᵥ-resp-≃

    _⟩∘ᵥ⟨refl : δ ≃ γ → δ ∘ᵥ α ≃ γ ∘ᵥ α
    _⟩∘ᵥ⟨refl  = ∘ᵥ-resp-≃ˡ

    refl⟩∘ᵥ⟨_ : α ≃ β → δ ∘ᵥ α ≃ δ ∘ᵥ β
    refl⟩∘ᵥ⟨_ = ∘ᵥ-resp-≃ʳ

    _⟩∘ₕ⟨_ : δ ≃ γ → α ≃ β → δ ∘ₕ α ≃ γ ∘ₕ β
    _⟩∘ₕ⟨_ = ∘ₕ-resp-≃

    refl⟩∘ₕ⟨_ : δ ≃ γ → δ ∘ₕ α ≃ γ ∘ₕ α
    refl⟩∘ₕ⟨_ = ∘ₕ-resp-≃ˡ

    _⟩∘ₕ⟨refl : α ≃ β → δ ∘ₕ α ≃ δ ∘ₕ β
    _⟩∘ₕ⟨refl = ∘ₕ-resp-≃ʳ


    module _ {E : Category o ℓ e} {F : Functor D E} where
      infixr 4 refl⟩∘ˡ⟨_
      refl⟩∘ˡ⟨_ : α ≃ β → F ∘ˡ α ≃ F ∘ˡ β
      refl⟩∘ˡ⟨_ = ∘ˡ-resp-≃ʳ


    -- convenient inline versions
    infix 2 ⟺
    infixr 3 _○_
    ⟺ : ∀ {α : NaturalTransformation F G} → α ≃ β → β ≃ α
    ⟺ = Equiv.sym
      where module Equiv = IsEquivalence (≃-isEquivalence {F = F} {G = G})

    _○_ : α ≃ β → β ≃ γ → α ≃ γ
    _○_ = Equiv.trans
      where module Equiv = IsEquivalence ≃-isEquivalence

  infixr 4 refl⟩∘ᵥ[_⇛_]⟨_
  infixl 5 _⟩∘ᵥ[_⇛_]⟨refl

  _⟩∘ᵥ[_⇛_]⟨refl : δ ≃ γ → Functor C D → Functor C D → δ ∘ᵥ α ≃ γ ∘ᵥ α
  e ⟩∘ᵥ[ F ⇛ G ]⟨refl  = _⟩∘ᵥ⟨refl {F = F} {G = G} e

  refl⟩∘ᵥ[_⇛_]⟨_ : Functor C D → Functor C D → α ≃ β → δ ∘ᵥ α ≃ δ ∘ᵥ β
  refl⟩∘ᵥ[ F ⇛ G ]⟨ e = refl⟩∘ᵥ⟨_ {F = F} {G = G} e


module Pullsᵥ {C D : Category o ℓ e} {F G H : Functor C D}
              {α : NaturalTransformation G H} {β : NaturalTransformation F G}
              {γ : NaturalTransformation F H} (αβ≃γ : α ∘ᵥ β ≃ γ) where
  open NatReasoning

  pullʳ : ∀ {I : Functor C D} {δ : NaturalTransformation H I} → (δ ∘ᵥ α) ∘ᵥ β ≃ δ ∘ᵥ γ
  pullʳ {δ = δ} = begin
    (δ ∘ᵥ α) ∘ᵥ β ≈⟨ ∘ᵥ-assoc ⟩
    δ ∘ᵥ (α ∘ᵥ β) ≈⟨ refl⟩∘ᵥ[ F ⇛ G ]⟨ αβ≃γ ⟩
    δ ∘ᵥ γ        ∎

  pullˡ : ∀ {I : Functor C D} {δ : NaturalTransformation I F} → α ∘ᵥ β ∘ᵥ δ ≃ γ ∘ᵥ δ
  pullˡ {I = I} {δ = δ} = begin
    α ∘ᵥ β ∘ᵥ δ     ≈˘⟨ ∘ᵥ-assoc ⟩
    (α ∘ᵥ  β) ∘ᵥ δ   ≈⟨ αβ≃γ ⟩∘ᵥ[ F ⇛ G ]⟨refl ⟩
    γ ∘ᵥ δ          ∎

open Pullsᵥ public
{-

≃-whiskerˡ : α ≃ β → K ∘ˡ α ≃ K ∘ˡ β
≃-whiskerˡ e = {! !}

≃-whiskerʳ : ε ≃ κ → ε ∘ʳ F ≃ κ ∘ʳ F
≃-whiskerʳ e = {! !}

-- ------
-- |    |
-- ε    β
-- |    |
-- κ    α
-- |    |
-- ------
≃-interchange : (τ ∘ᵥ κ) ∘ₕ (δ ∘ᵥ α) ≃ (τ ∘ₕ δ) ∘ᵥ (κ ∘ₕ α)
≃-interchange = {! !}

foo : (α ⁂ⁿ δ) ≃ (β ⁂ⁿ γ) → (δ ⁂ⁿ α) ≃ (γ ⁂ⁿ β)
foo e = {! !}


⁂ⁿ∘⁂ⁿ : ∀ {A B : Category o ℓ e} {F G H : Functor A B} {K J L : Functor C D}
          {α : NaturalTransformation G H} {β : NaturalTransformation J L}
          {δ : NaturalTransformation F G} {γ : NaturalTransformation K J} →
          (α ⁂ⁿ β) ∘ᵥ (δ ⁂ⁿ γ) ≃ (α ∘ᵥ δ) ⁂ⁿ (β ∘ᵥ γ)
⁂ⁿ∘⁂ⁿ  = {! !}

-- ⁂ⁿid∘id⁂ⁿ : (α ⁂ⁿ idN) ∘ᵥ (idN ⁂ⁿ β) ≃ α ⁂ⁿ β
-- ⁂ⁿid∘id⁂ⁿ  = {!⁂ⁿ∘⁂ⁿ α idN idN β  !}


id⁂ⁿ∘⁂ⁿid : ∀ {C₁ D₁ : Category o ℓ e} {F G H : Functor C C₁} {K J L : Functor D D₁}
          {α : NaturalTransformation F G} {β : NaturalTransformation K J} →
    (idN ⁂ⁿ α) ∘ᵥ (β ⁂ⁿ idN) ≃ β ⁂ⁿ α
id⁂ⁿ∘⁂ⁿid  = {! !}


⁂ⁿswap : ∀ {C₁ D₁ : Category o ℓ e} {F G H : Functor C C₁} {K J L : Functor D D₁}
          {α : NaturalTransformation F G} {β : NaturalTransformation K J} →
    (α ⁂ⁿ idN) ∘ᵥ (idN ⁂ⁿ β) ≃ (idN ⁂ⁿ β) ∘ᵥ (α ⁂ⁿ idN)
⁂ⁿswap  = {! !}
-}
