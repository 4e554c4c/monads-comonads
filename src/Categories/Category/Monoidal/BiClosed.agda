{-# OPTIONS --without-K --allow-unsolved-metas #-}

open import Categories.Category
open import Categories.Category.Monoidal

module Categories.Category.Monoidal.BiClosed
  {o ℓ e} {C : Category o ℓ e} (M : Monoidal C)  where

private
  module C = Category C
  open Category C

  variable
    X Y A B : Obj



open import Categories.Adjoint
open import Categories.Adjoint.Equivalents using (Hom-NI′)
open import Categories.Adjoint.Mate
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Bifunctor
open import Categories.Functor.Hom
open import Categories.Category.Instance.Setoids
open import Categories.NaturalTransformation hiding (id)
open import Categories.NaturalTransformation.Properties
open import Categories.NaturalTransformation.NaturalIsomorphism as NI using (NaturalIsomorphism)

open import Level
open import Data.Product using (_,_)

module _ {D E : Category o ℓ e} {F : Bifunctor C D E} where
  private
    module D = Category D
    module E = Category E

  appˡ-iso-appʳ : {X : Category.Obj C} → (appˡ F X)  NI.≃ (appʳ (flip-bifunctor F) X)
  appˡ-iso-appʳ = {! !}

  flip-flip-iso : flip-bifunctor (flip-bifunctor F) NI.≃ F
  flip-flip-iso = {! !} 

  appˡ-iso : {G : Bifunctor C D E} {X : Category.Obj C} →
             (F NI.≃ G) → (appˡ F X)  NI.≃ (appˡ G X)
  appˡ-iso f = {! !}

  appʳ-iso : {G : Bifunctor C D E} {X : Category.Obj D} →
             (F NI.≃ G) → (appʳ F X)  NI.≃ (appʳ G X)
  appʳ-iso f = {! !}

  appʳ-iso-appˡ : {X : Category.Obj D} → (appʳ F X)  NI.≃ (appˡ (flip-bifunctor F) X)
  appʳ-iso-appˡ = {! !}


record BiClosed : Set (levelOfTerm M) where
  open Monoidal M public

  field
    [-⇨-]   : Bifunctor C.op C C
    [-⇦-]   : Bifunctor C C.op C
    adjointʳ : (X ⊗-) ⊣ appˡ [-⇨-] X
    adjointˡ : (-⊗ X) ⊣ appʳ [-⇦-] X
    mateʳ    : (f : X ⇒ Y) → Mate (adjointʳ  {X}) (adjointʳ  {Y}) (appˡ-nat ⊗ f) (appˡ-nat [-⇨-] f)
    mateˡ    : (f : X ⇒ Y) → Mate (adjointˡ  {X}) (adjointˡ  {Y}) (appʳ-nat ⊗ f) (appʳ-nat [-⇦-] f)


  module [-⇨-]         = Functor [-⇨-]
  module [-⇦-]         = Functor [-⇦-]
  module adjointˡ {X}  = Adjoint (adjointˡ {X})
  module adjointʳ {X}  = Adjoint (adjointʳ {X})

  [-⇨_] : Obj → Functor C.op C
  [-⇨_] = appʳ [-⇨-]

  [_⇦-] : Obj → Functor C.op C
  [_⇦-] = appˡ [-⇦-]

  [_⇨-] : Obj → Functor C C
  [_⇨-] = appˡ [-⇨-]

  [-⇦_] : Obj → Functor C C
  [-⇦_] = appʳ [-⇦-]

  [_⇨_]₀ : Obj → Obj → Obj
  [ X ⇨ Y ]₀ = [-⇨-].F₀ (X , Y)

  [_⇨_]₁ : A ⇒ B → X ⇒ Y → [ B ⇨ X ]₀ ⇒ [ A ⇨ Y ]₀
  [ f ⇨ g ]₁ = [-⇨-].F₁ (f , g)

  [_⇦_]₀ : Obj → Obj → Obj
  [ X ⇦ Y ]₀ = [-⇦-].F₀ (X , Y)

  [_⇦_]₁ : A ⇒ B → X ⇒ Y → [ A ⇦ Y ]₀ ⇒ [ B ⇦ X ]₀
  [ f ⇦ g ]₁ = [-⇦-].F₁ (f , g)

  open import Categories.Category.Monoidal.Closed using (Closed)
  open import Categories.Adjoint.Properties using (⊣×≃⇒⊣)
  open import Relation.Binary using (Rel; IsEquivalence)

  closed : Closed M
  closed = record
    { [-,-]   = flip-bifunctor [-⇦-]
    ; adjoint = λ {X} → ⊣×≃⇒⊣ (adjointˡ {X = X}) NI≃.refl (appʳ-iso-appˡ {F = [-⇦-]})
    ; mate    = λ {X} {Y} f → record
      { commute₁ = {! C.Equiv.refl !}
      ; commute₂ = {! !}
      }
    }
    where module NI≃ = IsEquivalence NI.isEquivalence

