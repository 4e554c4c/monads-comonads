{-# OPTIONS --hidden-argument-puns  #-}
open import Agda.Builtin.Equality

module example where

data this : Set where
  s : this

data that : Set where
  t : that

foo : ∀ {A : Set} {A = B : Set} → A → B → Set
foo {A = _} {B} _ _ = B

_ : foo s t ≡ that
_ = refl
