{-# OPTIONS --without-K --safe #-}

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

record BiClosed : Set (levelOfTerm M) where
  open Monoidal M

  field
    [-,-] ⟦-,-⟧ : Bifunctor C.op C C
    adjointˡ    : (-⊗ X) ⊣ appˡ [-,-] X
    adjointʳ    : (X ⊗-) ⊣ appˡ ⟦-,-⟧ X
    mateˡ       : (f : X ⇒ Y) → Mate (adjointˡ {X}) (adjointˡ {Y}) (appʳ-nat ⊗ f) (appˡ-nat [-,-] f)
    mateʳ       : (f : X ⇒ Y) → Mate (adjointʳ {X}) (adjointʳ {Y}) (appˡ-nat ⊗ f) (appˡ-nat ⟦-,-⟧ f)

  open import Categories.Category.Monoidal.Closed using (Closed)

  closed : Closed M
  closed = record
    { [-,-]   = [-,-]
    ; adjoint = adjointˡ
    ; mate    = mateˡ
    }

  open Closed closed hiding ([-,-]) public

  module ⟦-,-⟧         = Functor ⟦-,-⟧
  module adjointˡ {X}  = Adjoint (adjointˡ {X})
  module adjointʳ {X}  = Adjoint (adjointʳ {X})

  ⟦-,_⟧ : Obj → Functor C.op C
  ⟦-,_⟧ = appʳ ⟦-,-⟧

  ⟦_,-⟧ : Obj → Functor C C
  ⟦_,-⟧ = appˡ ⟦-,-⟧


  ⟦_,_⟧₀ : Obj → Obj → Obj
  ⟦ X , Y ⟧₀ = ⟦-,-⟧.F₀ (X , Y)

  ⟦_,_⟧₁ : A ⇒ B → X ⇒ Y → ⟦ B , X ⟧₀ ⇒ ⟦ A , Y ⟧₀
  ⟦ f , g ⟧₁ = ⟦-,-⟧.F₁ (f , g)
