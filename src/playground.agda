{-# OPTIONS --without-K --hidden-argument-puns --allow-unsolved-metas #-}
open import Level

open import Categories.Category using (module Commutation) renaming (Category to Setoid-Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)

module playground {o ℓ e} {V : Setoid-Category o ℓ e} (MV : Monoidal V) (CV : Closed MV) where

open import Level

open import Categories.Category.Monoidal.Properties MV using (module Kelly's)
open import Categories.Category.Monoidal.Reasoning MV
open import Categories.Category.Monoidal.Utilities MV
open import Categories.Enriched.Category MV using (Category; _[_,_])
open import Categories.Enriched.Category.Underlying MV using (Underlying)
open import Categories.Enriched.Functor MV using (Functor; UnderlyingFunctor; _∘F_)
  renaming (id to idF)
open import Categories.Morphism.Reasoning V
  --using (pushˡ; pullˡ; cancelʳ; pullʳ; pushʳ; switch-tofromˡ; extendˡ; extendʳ; module HomReasoning)
open import Categories.NaturalTransformation using (ntHelper)
  renaming (NaturalTransformation to Setoid-NT)

open import Data.Product using (uncurry; uncurry′; Σ; _,_; _×_) renaming (proj₁ to fst; proj₂ to snd) public

open Setoid-Category V using (_∘_; _⇒_; _≈_; assoc; module HomReasoning)
  renaming (Obj to ObjV; id to idV)
open Commutation V
open Closed CV
--open Shorthands

module playground where

module _ where
  open Category
  open Setoid-NT
  --open HomReasoning
  --open Commutation V
  self : Category o
  self .Obj = ObjV
  self .hom = [_,_]₀
  self .id  = [ idV , unitorˡ.from ]₁ ∘ adjoint.unit.η unit
  self .⊚  {A} {B} {C} =                          -- [ B , C ]₀ ⊗₀  [ A , B ]₀
    adjoint.unit.η {A} ([ B , C ]₀ ⊗₀ [ A , B ]₀) ⇒⟨ [ A , ([ B , C ]₀ ⊗₀ [ A , B ]₀) ⊗₀ A ]₀ ⟩
    [ idV , associator.from ]₁                    ⇒⟨ [ A , [ B , C ]₀ ⊗₀ ([ A , B ]₀ ⊗₀ A) ]₀ ⟩
    [ idV , idV ⊗₁ adjoint.counit.η B ]₁          ⇒⟨ [ A , [ B , C ]₀ ⊗₀ B ]₀ ⟩
    [ idV , adjoint.counit.η C ]₁                 -- ⇒ [ A , C ]₀
  self .⊚-assoc {A} {B} {C} {D} = begin
    ([ idV , adjoint.counit.η D ]₁ ∘
     [ idV , idV ⊗₁ adjoint.counit.η B ]₁ ∘
     [ idV , associator.from ]₁   ∘
     adjoint.unit.η ([ B , D ]₀ ⊗₀ [ A , B ]₀))
    ∘
    ([ idV , adjoint.counit.η D ]₁ ∘
     [ idV , idV ⊗₁ adjoint.counit.η C ]₁ ∘
     [ idV , associator.from ]₁ ∘
     adjoint.unit.η ([ C , D ]₀ ⊗₀  [ B , C ]₀))
     ⊗₁ idV
    ≈⟨ ? ⟩
    (
    [ idV , adjoint.counit.η D ]₁ ∘
    [ idV , idV ⊗₁ adjoint.counit.η C ]₁ ∘
    [ idV , associator.from ]₁   ∘
     adjoint.unit.η ([ C , D ]₀ ⊗₀ [ A , C ]₀)
    ) ∘
    idV ⊗₁ (
     [ idV , adjoint.counit.η C ]₁ ∘
     [ idV , idV ⊗₁ adjoint.counit.η B ]₁ ∘
     [ idV , associator.from ]₁    ∘
     adjoint.unit.η ([ B , C ]₀ ⊗₀ [ A , B ]₀))
    ∘ associator.from
    ∎
  self .unitˡ = {! !}
  self .unitʳ = {! !}


-- yoneda time?
{-

module _ (V : Category o ℓ e) (MV : Monoidal V) (SM : Symmetric MV) (CV : Closed MV) where
  open Monoidal MV using (⊗; _⊗₀_; _⊗₁_; _⊗-; -⊗_)
  open Closed CV using ([-,-])

  --open import Categories.Yoneda
  --open Yoneda using () renaming (embed to よ)
  --module _ (E : Category o ℓ e) where
  --  open Functor よ E renaming (F₀ to よ₀)

  -- we need V to be self enriched?


  -- the object of "internal natural transformations"
  --V[_⇒_] : (F G : Functor D V) → Set _
  --V[ F ⇒ G ] = ∫ ([-,-] ∘F ((Functor.op F) ⁂ G))

  open import Categories.Functor.Hom using (module Hom; Hom[_][-,_]; Hom[_][-,-]; Hom[_][_,-])

  open import Categories.Morphism using (_≅_)

  -- 'strong' enriched yoneda lemma
  module _ (F : Functor E V) where
    private
      module E = Category E
      module F = Functor F


    --strong-yoneda : ∀ (d : E.Obj) {end-exists : C[ Hom[ E ][ d ,-] ⇒ F ]} → (end-exists .end) ≅ (F.₀ d)
    --strong-yoneda = ?
-}

