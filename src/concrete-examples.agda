open import Prelude

open import Categories.Category.Monoidal.BiClosed using (BiClosed)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Data.Product using (uncurry; uncurry′; Σ; _,_; _×_)
open import Level using (_⊔_)

open import Categories.Category.Instance.Setoids
open import Categories.Category.Instance.Properties.Setoids.CCC
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.CartesianClosed using (module CartesianMonoidalClosed; CartesianClosed)
open import Level using (0ℓ)

module concrete-examples  where

open import fil-examples using (module example-1)

C = Setoids 0ℓ 0ℓ
open module C = Category C using (_∘_)
CC = Setoids-CCC 0ℓ

open module CC = CartesianClosed CC using (cartesian)
open Cartesian cartesian using (products)
open BinaryProducts products using (π₁)


MC = CartesianMonoidalClosed.closedMonoidal C CC

open CartesianClosed CC public
open import Relation.Binary.PropositionalEquality.Core as ≡
  using (_≡_)
import Relation.Binary.PropositionalEquality.Properties as ≡
open import Data.Nat using (ℕ;_+_)

ℕₛ = (≡.setoid ℕ)

open example-1 MC {A = ℕₛ}


open Functor F using (F₀; F₁)
open Functor G renaming (F₀ to G₀; F₁ to G₁)

open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Data.Product.Function.NonDependent.Setoid using (<_,_>ₛ)
open import Function.Construct.Setoid using (setoid)


--φ : (X Y : Obj) → (F₀ X) ⊗₀ (G₀ Y) ⇒ (X ⊗₀ Y)
open import Function.Bundles using (_⟶_; Func;mk⟶ )
open Func using (to)

φ' : (X Y : C.Obj) → Func ((F₀ X) ×ₛ (G₀ Y)) X
φ' X Y = π₁ ∘ (φ X Y)

open import Relation.Binary.Bundles using (Setoid)
open Setoid using (Carrier)

ex : ℕ → ℕ
ex n = φ' ℕₛ ℕₛ .to ((mk⟶ (18 +_)) , (2 , n))
_ : ∀ {n} → ex n ≡ 20
_ = refl
