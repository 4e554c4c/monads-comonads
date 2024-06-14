{-# OPTIONS --without-K --hidden-argument-puns --allow-unsolved-metas --lossy-unification #-}
open import Level

open import Categories.Category using (Category)
open import Categories.Functor using (Functor) renaming (id to idF)
import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation using (NaturalTransformation; _∘ʳ_; _∘ˡ_; _∘ᵥ_; _∘ₕ_) renaming (id to idN)
open import Categories.NaturalTransformation.Equivalence using (_≃_; ≃-isEquivalence)
open import Categories.Functor using (Endofunctor) renaming (id to idF)
open import Relation.Binary using (Rel; IsEquivalence; Setoid)

open import Level using (_⊔_) renaming (suc to lsuc)

module NatEquiv  where

private
  variable
    o ℓ e : Level

∘ₕ-resp-≃ : {o ℓ e o' ℓ' e' o'' ℓ'' e'' : Level}
            {C : Category o ℓ e}
            {D : Category o' ℓ' e'}
            {E : Category o'' ℓ'' e''}
            {F G : Functor C D} {K J : Functor D E}
            {α β : NaturalTransformation F G}
            {δ γ : NaturalTransformation K J} →
            δ ≃ γ → α ≃ β → δ ∘ₕ α ≃ γ ∘ₕ β
∘ₕ-resp-≃ {E} {J} e₁ e₂ = ∘-resp-≈ (J-resp-≈ e₂) e₁
  where open Category E
        open Functor J renaming (F-resp-≈ to J-resp-≈)

{-

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

∘ₕ-resp-≃ : {E : Category o ℓ e} {F G : Functor C D} {K J : Functor D E}
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

  my-∘ᵥ-resp-≃ : (C D : Category o ℓ e) → {F G H : Functor C D}
                {δ γ : NaturalTransformation G H} {α β : NaturalTransformation F G} →
                 δ ≃ γ → α ≃ β → δ ∘ᵥ α ≃ γ ∘ᵥ β
  my-∘ᵥ-resp-≃ C D = ∘ᵥ-resp-≃

  my-refl∘ᵥ-resp-≃ : (C D : Category o ℓ e) → {F G H : Functor C D}
                {δ : NaturalTransformation G H} {α β : NaturalTransformation F G} →
                 α ≃ β → δ ∘ᵥ α ≃ δ ∘ᵥ β
  my-refl∘ᵥ-resp-≃ C D = ∘ᵥ-resp-≃ refl
    where open IsEquivalence ≃-isEquivalence

  infixr 4 my-∘ᵥ-resp-≃
  syntax my-∘ᵥ-resp-≃ C D e₁ e₂ = e₁ ⟩∘ᵥ[ C ⇒ D ]⟨ e₂

  infixr 4 my-refl∘ᵥ-resp-≃
  syntax my-refl∘ᵥ-resp-≃ C D e = refl⟩∘ᵥ[ C ⇒ D ]⟨ e

  infixr 3 _○[_⇛_]_

  _○[_⇛_]_ : α ≃ β → Functor C D → Functor C D → β ≃ γ → α ≃ γ
  e₁ ○[ F ⇛ G ] e₂ = _○_ {F = F} {G = G} e₁ e₂

  my-○ : (C D : Category o ℓ e) → {F G : Functor C D} {α β γ : NaturalTransformation F G} →
         α ≃ β → β ≃ γ → α ≃ γ
  my-○ C D = Equiv.trans
      where module Equiv = IsEquivalence ≃-isEquivalence

  infixr 3 my-○
  syntax my-○ C D e₁ e₂ = e₁ ○[ C ⇒ D ] e₂

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


module Products where
  open import Categories.Category.Product using (_⁂_; _⁂ⁿ_)
  open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂; <_,_>; swap)

  ≃-swap : (α ⁂ⁿ δ) ≃ (β ⁂ⁿ γ) → (δ ⁂ⁿ α) ≃ (γ ⁂ⁿ β)
  ≃-swap (≃-ext e) = ≃-ext (swap e)

  ⁂ⁿ∘⁂ⁿ : ∀ {A B : Category o ℓ e} {F G H : Functor A B} {K J L : Functor C D}
            {α : NaturalTransformation G H} {β : NaturalTransformation J L}
            {δ : NaturalTransformation F G} {γ : NaturalTransformation K J} →
            (α ⁂ⁿ β) ∘ᵥ (δ ⁂ⁿ γ) ≃ (α ∘ᵥ δ) ⁂ⁿ (β ∘ᵥ γ)
  ⁂ⁿ∘⁂ⁿ  {D} {B}  = ≃-ext (B.refl , D.refl)
    where module B = Category.Equiv B
          module D = Category.Equiv D

  ⁂ⁿ-resp-≃ : α ≃ β → δ ≃ γ → (α ⁂ⁿ δ) ≃ (β ⁂ⁿ γ)
  ⁂ⁿ-resp-≃  (≃-ext e₁) (≃-ext e₂) = ≃-ext (e₁ , e₂)

  infixr 4 _⟩⁂ⁿ⟨_
  infixl 5 _⟩⁂ⁿ⟨refl
  _⟩⁂ⁿ⟨_ : α ≃ β → δ ≃ γ → (α ⁂ⁿ δ) ≃ (β ⁂ⁿ γ)
  _⟩⁂ⁿ⟨_ = ⁂ⁿ-resp-≃

  _⟩⁂ⁿ⟨refl : α ≃ β → (α ⁂ⁿ γ) ≃ (β ⁂ⁿ γ)
  e ⟩⁂ⁿ⟨refl = e ⟩⁂ⁿ⟨ refl
    where open IsEquivalence ≃-isEquivalence

  id⁂ⁿ∘⁂ⁿid : ∀ {A B : Category o ℓ e} {F G : Functor A B} {K J : Functor C D}
                {α : NaturalTransformation F G} {β : NaturalTransformation K J} →
                (idN ⁂ⁿ α) ∘ᵥ (β ⁂ⁿ idN) ≃ β ⁂ⁿ α
  id⁂ⁿ∘⁂ⁿid {D} {B} {α} {β} = begin
      (idN ⁂ⁿ α) ∘ᵥ (β ⁂ⁿ idN) ≈⟨ ⁂ⁿ∘⁂ⁿ ⟩
      (idN ∘ᵥ β) ⁂ⁿ (α ∘ᵥ idN) ≈⟨ ≃-ext D.identityˡ ⟩⁂ⁿ⟨ ≃-ext B.identityʳ ⟩
      β ⁂ⁿ α                   ∎
    where open NatReasoning
          module B = Category B
          module D = Category D

  ⁂ⁿid∘id⁂ⁿ : ∀ {A B : Category o ℓ e} {F G : Functor A B} {K J : Functor C D}
                {α : NaturalTransformation F G} {β : NaturalTransformation K J} →
                (α ⁂ⁿ idN) ∘ᵥ (idN ⁂ⁿ β) ≃ α ⁂ⁿ β
  ⁂ⁿid∘id⁂ⁿ {D} {B} {α} {β} = begin
      (α ⁂ⁿ idN) ∘ᵥ (idN ⁂ⁿ β) ≈⟨ ⁂ⁿ∘⁂ⁿ ⟩
      (α ∘ᵥ idN) ⁂ⁿ (idN ∘ᵥ β) ≈⟨ ≃-ext B.identityʳ ⟩⁂ⁿ⟨ ≃-ext D.identityˡ ⟩
      α ⁂ⁿ β                   ∎
    where open NatReasoning
          module B = Category B
          module D = Category D

  ⁂ⁿ-swap-∘ᵥ : ∀ {C₁ D₁ : Category o ℓ e} {F G : Functor C C₁} {K J : Functor D D₁}
            {α : NaturalTransformation F G} {β : NaturalTransformation K J} →
      (α ⁂ⁿ idN) ∘ᵥ (idN ⁂ⁿ β) ≃ (idN ⁂ⁿ β) ∘ᵥ (α ⁂ⁿ idN)
  ⁂ⁿ-swap-∘ᵥ {F} {G} {K} {J} = ⁂ⁿid∘id⁂ⁿ ○[ F ⁂ K ⇛ G ⁂ J ] ⟺ id⁂ⁿ∘⁂ⁿid
    where open NatReasoning

open Products public

{-
-- ------
-- |    |
-- ε    β
-- |    |
-- κ    α
-- |    |
-- ------
≃-interchange : (τ ∘ᵥ κ) ∘ₕ (δ ∘ᵥ α) ≃ (τ ∘ₕ δ) ∘ᵥ (κ ∘ₕ α)
≃-interchange = {! !}

-}
-}
