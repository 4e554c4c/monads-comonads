{-# OPTIONS --without-K --hidden-argument-puns --allow-unsolved-metas #-}
open import Level

module test where
{-

module CategoryCore where
  open import Function.Base using (flip)

  open import Relation.Binary using (Rel; IsEquivalence; Setoid)
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
  import Relation.Binary.Reasoning.Setoid as SetoidR
  record Category (o ℓ e : Level) : Set (suc (o ⊔ ℓ ⊔ e)) where
    no-eta-equality
    infix  4 _≈_ _⇒_
    infixr 9 _∘_

    field
      Obj : Set o
      _⇒_ : Rel Obj ℓ
      _≈_ : ∀ {A B} → Rel (A ⇒ B) e

      id  : ∀ {A} → (A ⇒ A)
      _∘_ : ∀ {A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)

    field
      assoc     : ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} → (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)
      -- We add a symmetric proof of associativity so that the opposite category of the
      -- opposite category is definitionally equal to the original category. See how
      -- `op` is implemented.
      sym-assoc : ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} → h ∘ (g ∘ f) ≈ (h ∘ g) ∘ f
      identityˡ : ∀ {A B} {f : A ⇒ B} → id ∘ f ≈ f
      identityʳ : ∀ {A B} {f : A ⇒ B} → f ∘ id ≈ f
      -- We add a proof of "neutral" identity proof, in order to ensure the opposite of
      -- constant functor is definitionally equal to itself.
      identity² : ∀ {A} → id ∘ id {A} ≈ id {A}
      equiv     : ∀ {A B} → IsEquivalence (_≈_ {A} {B})
      ∘-resp-≈  : ∀ {A B C} {f h : B ⇒ C} {g i : A ⇒ B} → f ≈ h → g ≈ i → f ∘ g ≈ h ∘ i

    module Equiv {A B : Obj} = IsEquivalence (equiv {A} {B})

    open Equiv

    ∘-resp-≈ˡ : ∀ {A B C} {f h : B ⇒ C} {g : A ⇒ B} → f ≈ h → f ∘ g ≈ h ∘ g
    ∘-resp-≈ˡ pf = ∘-resp-≈ pf refl

    ∘-resp-≈ʳ : ∀ {A B C} {f h : A ⇒ B} {g : B ⇒ C} → f ≈ h → g ∘ f ≈ g ∘ h
    ∘-resp-≈ʳ pf = ∘-resp-≈ refl pf

    hom-setoid : ∀ {A B} → Setoid _ _
    hom-setoid {A} {B} = record
      { Carrier       = A ⇒ B
      ; _≈_           = _≈_
      ; isEquivalence = equiv
      }

    -- When a category is quantified, it is convenient to refer to the levels from a module,
    -- so we do not have to explicitly quantify over a category when universe levels do not
    -- play a big part in a proof (which is the case probably all the time).
    o-level : Level
    o-level = o

    ℓ-level : Level
    ℓ-level = ℓ

    e-level : Level
    e-level = e

    -- Reasoning combinators.  _≈⟨_⟩_ and _≈˘⟨_⟩_ from SetoidR.
    -- Also some useful combinators for doing reasoning on _∘_ chains
    module HomReasoning {A B : Obj} where
      open SetoidR (hom-setoid {A} {B}) public
      -- open Equiv {A = A} {B = B} public

      infixr 4 _⟩∘⟨_ refl⟩∘⟨_
      infixl 5 _⟩∘⟨refl
      _⟩∘⟨_ : ∀ {M} {f h : M ⇒ B} {g i : A ⇒ M} → f ≈ h → g ≈ i → f ∘ g ≈ h ∘ i
      _⟩∘⟨_ = ∘-resp-≈

      refl⟩∘⟨_ : ∀ {M} {f : M ⇒ B} {g i : A ⇒ M} → g ≈ i → f ∘ g ≈ f ∘ i
      refl⟩∘⟨_ = Equiv.refl ⟩∘⟨_

      _⟩∘⟨refl : ∀ {M} {f h : M ⇒ B} {g : A ⇒ M} → f ≈ h → f ∘ g ≈ h ∘ g
      _⟩∘⟨refl = _⟩∘⟨ Equiv.refl

      -- convenient inline versions
      infix 2 ⟺
      infixr 3 _○_
      ⟺ : {f g : A ⇒ B} → f ≈ g → g ≈ f
      ⟺ = Equiv.sym
      _○_ : {f g h : A ⇒ B} → f ≈ g → g ≈ h → f ≈ h
      _○_ = Equiv.trans

    op : Category o ℓ e
    op = record
      { Obj       = Obj
      ; _⇒_       = flip _⇒_
      ; _≈_       = _≈_
      ; _∘_       = flip _∘_
      ; id        = id
      ; assoc     = sym-assoc
      ; sym-assoc = assoc
      ; identityˡ = identityʳ
      ; identityʳ = identityˡ
      ; identity² = identity²
      ; equiv     = equiv
      ; ∘-resp-≈  = flip ∘-resp-≈
      }

  private
    variable
      o ℓ e : Level

  -- Convenience functions for working over multiple categories at once:
  -- C [ x , y ] (for x y objects of C) - Hom_C(x , y)
  -- C [ f ≈ g ] (for f g arrows of C)  - that f and g are equivalent arrows
  -- C [ f ∘ g ] (for f g composable arrows of C) - composition in C
  infix 10  _[_,_] _[_≈_] _[_∘_]

  _[_,_] : (C : Category o ℓ e) → (X : Category.Obj C) → (Y : Category.Obj C) → Set ℓ
  _[_,_] = Category._⇒_

  _[_≈_] : (C : Category o ℓ e) → ∀ {X Y} (f g : C [ X , Y ]) → Set e
  _[_≈_] = Category._≈_

  _[_∘_] : (C : Category o ℓ e) → ∀ {X Y Z} (f : C [ Y , Z ]) → (g : C [ X , Y ]) → C [ X , Z ]
  _[_∘_] = Category._∘_

  module Definitions (𝓒 : Category o ℓ e) where
    open Category 𝓒

    CommutativeSquare : {A B C D : Obj} → (f : A ⇒ B) (g : A ⇒ C) (h : B ⇒ D) (i : C ⇒ D) → Set _
    CommutativeSquare f g h i = h ∘ f ≈ i ∘ g

  -- Combinators for commutative diagram
  -- The idea is to use the combinators to write commutations in a more readable way.
  -- It starts with [_⇒_]⟨_≈_⟩, and within the third and fourth places, use _⇒⟨_⟩_ to
  -- connect morphisms with the intermediate object specified.
  module Commutation (𝓒 : Category o ℓ e) where
    open Category 𝓒

    infix 1 [_⇒_]⟨_≈_⟩
    [_⇒_]⟨_≈_⟩ : ∀ (A B : Obj) → A ⇒ B → A ⇒ B → Set _
    [ A ⇒ B ]⟨ f ≈ g ⟩ = f ≈ g

    infixl 2 connect
    connect : ∀ {A C : Obj} (B : Obj) → A ⇒ B → B ⇒ C → A ⇒ C
    connect B f g = g ∘ f

    syntax connect B f g = f ⇒⟨ B ⟩ g

module FunctorCore where
  open CategoryCore
  open import Level
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

  private
    variable
      o ℓ e o′ ℓ′ e′ : Level

  record Functor (C : Category o ℓ e) (D : Category o′ ℓ′ e′) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
    no-eta-equality
    private module C = Category C
    private module D = Category D

    field
      F₀ : C.Obj → D.Obj
      F₁ : ∀ {A B} (f : C [ A , B ]) → D [ F₀ A , F₀ B ]

      identity     : ∀ {A} → D [ F₁ (C.id {A}) ≈ D.id ]
      homomorphism : ∀ {X Y Z} {f : C [ X , Y ]} {g : C [ Y , Z ]} →
                       D [ F₁ (C [ g ∘ f ]) ≈ D [ F₁ g ∘ F₁ f ] ]
      F-resp-≈     : ∀ {A B} {f g : C [ A , B ]} → C [ f ≈ g ] → D [ F₁ f ≈ F₁ g ]

    -- nice shorthands
    ₀ = F₀
    ₁ = F₁

    op : Functor C.op D.op
    op = record
      { F₀           = F₀
      ; F₁           = F₁
      ; identity     = identity
      ; homomorphism = homomorphism
      ; F-resp-≈     = F-resp-≈
      }

  --private
  --  op-involutive : {C : Category o ℓ e} {D : Category o′ ℓ′ e′} → (F : Functor C D) → Functor.op (Functor.op F) ≡ F
  --  op-involutive c = ?
  open import Level
  open import Function renaming (id to id→; _∘_ to _●_) using ()

  --open import Categories.Category
  --open import Categories.Functor.Core public

  private
    variable
      o″ ℓ″ e″ : Level

  Endofunctor : Category o ℓ e → Set _
  Endofunctor C = Functor C C

  id : ∀ {C : Category o ℓ e} → Functor C C
  id {C = C} = record
    { F₀           = id→
    ; F₁           = id→
    ; identity     = Category.Equiv.refl C
    ; homomorphism = Category.Equiv.refl C
    ; F-resp-≈     = id→
    }

  infixr 9 _∘F_

  -- note that this definition could be shortened by inlining the definitions for
  -- identity′ and homomorphism′, but the definitions below are simpler to understand.
  _∘F_ : ∀ {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {E : Category o″ ℓ″ e″}
      → Functor D E → Functor C D → Functor C E
  _∘F_ {C = C} {D = D} {E = E} F G = record
    { F₀ = F.₀ ● G.₀
    ; F₁ = F.₁ ● G.₁
    ; identity = identity′
    ; homomorphism = homomorphism′
    ; F-resp-≈ =  F.F-resp-≈ ● G.F-resp-≈
    }
    where
    module C = Category C using (id)
    module D = Category D using (id)
    module E = Category E using (id; module HomReasoning)
    module F = Functor F
    module G = Functor G

    identity′ : ∀ {A} → E [ F.₁ (G.₁ (C.id {A})) ≈ E.id ]
    identity′ = begin
      F.₁ (G.₁ C.id) ≈⟨ F.F-resp-≈ G.identity ⟩
      F.₁ D.id       ≈⟨ F.identity ⟩
      E.id           ∎
      where open E.HomReasoning

    homomorphism′ : ∀ {X Y Z} {f : C [ X , Y ]} {g : C [ Y , Z ]}
                   → E [ F.₁ (G.₁ (C [ g ∘ f ])) ≈ E [ F.₁ (G.₁ g) ∘ F.₁ (G.₁ f) ] ]
    homomorphism′ {f = f} {g = g} = begin
      F.₁ (G.₁ (C [ g ∘ f ]))         ≈⟨ F.F-resp-≈ G.homomorphism ⟩
      F.₁ (D [ G.₁ g ∘ G.₁ f ])       ≈⟨ F.homomorphism ⟩
      E [ F.₁ (G.₁ g) ∘ F.₁ (G.₁ f) ] ∎
      where open E.HomReasoning

module FunctorProperties where 
  -- Properties valid of all Functors
  open import Level
  open import Data.Product using (proj₁; proj₂; _,_; _×_; Σ)
  open import Function.Surjection using (Surjective)
  open import Function.Equivalence using (Equivalence)
  open import Function.Equality using (Π; _⟶_; _⟨$⟩_; cong)
  open import Relation.Binary using (_Preserves_⟶_)
  open import Relation.Nullary

  open CategoryCore
  --open import Categories.Category.Construction.Core using (module Shorthands)
  open FunctorCore
  --import Categories.Morphism as Morphism
  --import Categories.Morphism.Reasoning as Reas
  --open import Categories.Morphism.IsoEquiv as IsoEquiv
  ---open import Categories.Morphism.Notation

  private
    variable
      o ℓ e o′ ℓ′ e′ : Level
      C D : Category o ℓ e

  -- a series of [ Functor ]-respects-Thing combinators (with respects -> resp)
  module _ (F : Functor C D) where
    private
      module C = Category C using (Obj; _∘_; _⇒_; id; module HomReasoning)
      module D = Category D
    open C hiding (_∘_)
    open Functor F

    private
      variable
        A B E : Obj
        f g h i : A ⇒ B

    [_]-resp-∘ : C [ C [ f ∘ g ] ≈ h ] → D [ D [ F₁ f ∘ F₁ g ] ≈ F₁ h ]
    [_]-resp-∘ {f = f} {g = g} {h = h} eq = begin
      F₁ f D.∘ F₁ g    ≈˘⟨ homomorphism ⟩
      F₁ (C [ f ∘ g ]) ≈⟨ F-resp-≈ eq ⟩
      F₁ h             ∎
      where open D.HomReasoning

    [_]-resp-square : Definitions.CommutativeSquare C f g h i →
                      Definitions.CommutativeSquare D (F₁ f) (F₁ g) (F₁ h) (F₁ i)
    [_]-resp-square {f = f} {g = g} {h = h} {i = i} sq = begin
      D [ F₁ h ∘ F₁ f ]  ≈˘⟨ homomorphism ⟩
      F₁ (C [ h ∘ f ])   ≈⟨ F-resp-≈ sq ⟩
      F₁ (C [ i ∘ g ])   ≈⟨ homomorphism ⟩
      D [ F₁ i ∘ F₁ g ]  ∎
      where open D.HomReasoning

module MorphismReasoning {o ℓ e} (C : CategoryCore.Category o ℓ e) where
  {-
    Helper routines most often used in reasoning with commutative squares,
    at the level of arrows in categories.

    Identity : reasoning about identity
    Assoc4   : associativity combinators for composites of 4 morphisms
    Pulls  : use a ∘ b ≈ c as left-to-right rewrite
    Pushes : use c ≈ a ∘ b as a left-to-right rewrite
    IntroElim : introduce/eliminate an equivalent-to-id arrow
    Extend : 'extends' a commutative square with an equality on left/right/both

    Convention - in this file, extra parentheses are used to clearly show
      associativity. This makes reading the source more pedagogical as to the
      intent of each routine.
  -}
  open CategoryCore

  open import Level
  open import Function renaming (id to idᶠ; _∘_ to _∙_)

  open import Relation.Binary hiding (_⇒_)

  open Category C
  open Definitions C

  private
    variable
      X Y : Obj
      a a′ a″ b b′ b″ c c′ c″ : X ⇒ Y
      f g h i : X ⇒ Y

  open HomReasoning

  module Identity where
    id-unique : ∀ {o} {f : o ⇒ o} → (∀ g → g ∘ f ≈ g) → f ≈ id
    id-unique g∘f≈g = Equiv.trans (Equiv.sym identityˡ) (g∘f≈g id)

    id-comm : ∀ {a b} {f : a ⇒ b} → f ∘ id ≈ id ∘ f
    id-comm = Equiv.trans identityʳ (Equiv.sym identityˡ)

    id-comm-sym : ∀ {a b} {f : a ⇒ b} → id ∘ f ≈ f ∘ id
    id-comm-sym = Equiv.trans identityˡ (Equiv.sym identityʳ)

  open Identity public

  module Assoc4 where
    assoc² : ((i ∘ h) ∘ g) ∘ f ≈ i ∘ (h ∘ (g ∘ f))
    assoc² = Equiv.trans assoc assoc

    assoc²' : (i ∘ (h ∘ g)) ∘ f ≈ i ∘ (h ∘ (g ∘ f))
    assoc²' = Equiv.trans assoc (∘-resp-≈ʳ assoc)

    assoc²'' : i ∘ ((h ∘ g) ∘ f) ≈ (i ∘ h) ∘ (g ∘ f)
    assoc²'' = Equiv.trans (∘-resp-≈ʳ assoc) sym-assoc

  open Assoc4 public

  -- Pulls use "a ∘ b ≈ c" as left-to-right rewrite
  -- pull to the right / left of something existing
  module Pulls (ab≡c : a ∘ b ≈ c) where

    pullʳ : (f ∘ a) ∘ b ≈ f ∘ c
    pullʳ {f = f} = begin
      (f ∘ a) ∘ b ≈⟨ assoc ⟩
      f ∘ (a ∘ b) ≈⟨ refl⟩∘⟨ ab≡c ⟩
      f ∘ c       ∎

    pullˡ : a ∘ (b ∘ f) ≈ c ∘ f
    pullˡ {f = f} = begin
      a ∘ b ∘ f   ≈⟨ sym-assoc ⟩
      (a ∘ b) ∘ f ≈⟨ ab≡c ⟩∘⟨refl ⟩
      c ∘ f       ∎

  open Pulls public

  -- Pushes use "c ≈ a ∘ b" as a left-to-right rewrite
  -- push to the right / left of something existing
  module Pushes (c≡ab : c ≈ a ∘ b) where
    pushʳ : f ∘ c ≈ (f ∘ a) ∘ b
    pushʳ {f = f} = begin
      f ∘ c       ≈⟨ refl⟩∘⟨ c≡ab ⟩
      f ∘ (a ∘ b) ≈⟨ sym-assoc ⟩
      (f ∘ a) ∘ b ∎

    pushˡ : c ∘ f ≈ a ∘ (b ∘ f)
    pushˡ {f = f} = begin
      c ∘ f       ≈⟨ c≡ab ⟩∘⟨refl ⟩
      (a ∘ b) ∘ f ≈⟨ assoc ⟩
      a ∘ (b ∘ f) ∎

  open Pushes public

  -- Introduce/Elimilate an equivalent-to-identity
  -- on left, right or 'in the middle' of something existing
  module IntroElim (a≡id : a ≈ id) where
    elimʳ : f ∘ a ≈ f
    elimʳ {f = f} = begin
      f ∘ a  ≈⟨ refl⟩∘⟨ a≡id ⟩
      f ∘ id ≈⟨ identityʳ ⟩
      f      ∎

    introʳ : f ≈ f ∘ a
    introʳ = Equiv.sym elimʳ

    elimˡ : (a ∘ f) ≈ f
    elimˡ {f = f} = begin
      a ∘ f  ≈⟨ a≡id ⟩∘⟨refl ⟩
      id ∘ f ≈⟨ identityˡ ⟩
      f      ∎

    introˡ : f ≈ a ∘ f
    introˡ = Equiv.sym elimˡ

    intro-center : f ∘ g ≈ f ∘ (a ∘ g)
    intro-center = ∘-resp-≈ʳ introˡ

    elim-center : f ∘ (a ∘ g) ≈ f ∘ g
    elim-center = ∘-resp-≈ʳ elimˡ

  open IntroElim public

  -- given h ∘ f ≈ i ∘ g
  module Extends (s : CommutativeSquare f g h i) where
    -- rewrite (a ∘ h) ∘ f to (a ∘ i) ∘ g
    extendˡ : CommutativeSquare f g (a ∘ h) (a ∘ i)
    extendˡ {a = a} = begin
      (a ∘ h) ∘ f ≈⟨ pullʳ s ⟩
      a ∘ (i ∘ g) ≈⟨ sym-assoc ⟩
      (a ∘ i) ∘ g ∎

    -- rewrite h ∘ (f ∘ a) to i ∘ (g ∘ a)
    extendʳ : CommutativeSquare (f ∘ a) (g ∘ a) h i
    extendʳ {a = a} = begin
      h ∘ (f ∘ a) ≈⟨ pullˡ s ⟩
      (i ∘ g) ∘ a ≈⟨ assoc ⟩
      i ∘ (g ∘ a) ∎

    -- rewrite (a ∘ h) ∘ (f ∘ b) to (a ∘ i) ∘ (g ∘ b)
    extend² : CommutativeSquare (f ∘ b) (g ∘ b) (a ∘ h) (a ∘ i)
    extend² {b = b} {a = a } = begin
      (a ∘ h) ∘ (f ∘ b) ≈⟨ pullʳ extendʳ ⟩
      a ∘ (i ∘ (g ∘ b)) ≈⟨ sym-assoc ⟩
      (a ∘ i) ∘ (g ∘ b) ∎

  open Extends public

  -- essentially composition in the arrow category
  {-
     A₁ -- c --> B₁
     |           |
     b′  comm    b
     |           |
     V           V
     A₂ -- c′ -> B₂
     |           |
     a′  comm    a
     |           |
     V           V
     A₃ -- c″ -> B₃

     then the whole diagram commutes
  -}
  glue : CommutativeSquare c′ a′ a c″ →
         CommutativeSquare c b′ b c′ →
         CommutativeSquare c (a′ ∘ b′) (a ∘ b) c″
  glue {c′ = c′} {a′ = a′} {a = a} {c″ = c″} {c = c} {b′ = b′} {b = b} sq-a sq-b = begin
    (a ∘ b) ∘ c    ≈⟨ pullʳ sq-b ⟩
    a ∘ (c′ ∘ b′)  ≈⟨ extendʳ sq-a ⟩
    c″ ∘ (a′ ∘ b′) ∎

  -- A "rotated" version of glue′. Equivalent to 'Equiv.sym (glue (Equiv.sym sq-a) (Equiv.sym sq-b))'
  glue′ : CommutativeSquare a′ c′ c″ a →
          CommutativeSquare b′ c c′ b →
          CommutativeSquare (a′ ∘ b′) c c″ (a ∘ b)
  glue′ {a′ = a′} {c′ = c′} {c″ = c″} {a = a} {b′ = b′} {c = c} {b = b} sq-a sq-b = begin
    c″ ∘ (a′ ∘ b′) ≈⟨ pullˡ sq-a ⟩
    (a ∘ c′) ∘ b′  ≈⟨ extendˡ sq-b ⟩
    (a ∘ b) ∘ c    ∎

  -- Various gluings of triangles onto sides of squares
  glue◃◽ : a ∘ c′ ≈ c″ → CommutativeSquare c b′ b c′ → CommutativeSquare c b′ (a ∘ b) c″
  glue◃◽ {a = a} {c′ = c′} {c″ = c″} {c = c} {b′ = b′} {b = b} tri-a sq-b = begin
    (a ∘ b) ∘ c   ≈⟨ pullʳ sq-b ⟩
    a ∘ (c′ ∘ b′) ≈⟨ pullˡ tri-a ⟩
    c″ ∘ b′       ∎

  glue◃◽′ : c ∘ c′ ≈ a′ → CommutativeSquare a b a′ b′ → CommutativeSquare (c′ ∘ a) b c b′
  glue◃◽′ {c = c} {c′ = c′} {a′ = a′} {a = a} {b = b} {b′ = b′} tri sq = begin
    c ∘ (c′ ∘ a) ≈⟨ pullˡ tri ⟩
    a′ ∘ a       ≈⟨ sq ⟩
    b′ ∘ b       ∎

  glue◽◃ : CommutativeSquare a b a′ b′ → b ∘ c ≈ c′ → CommutativeSquare (a ∘ c) c′ a′ b′
  glue◽◃ {a = a} {b = b} {a′ = a′} {b′ = b′} {c = c} {c′ = c′} sq tri = begin
    a′ ∘ a ∘ c   ≈⟨ pullˡ sq ⟩
    (b′ ∘ b) ∘ c ≈⟨ pullʳ tri ⟩
    b′ ∘ c′      ∎

  glue▹◽ : b ∘ a″ ≈ c → CommutativeSquare a b a′ b′ → CommutativeSquare (a ∘ a″) c a′ b′
  glue▹◽ {b = b} {a″ = a″} {c = c} {a = a} {a′ = a′} {b′ = b′} tri sq = begin
    a′ ∘ a ∘ a″   ≈⟨ pullˡ sq ⟩
    (b′ ∘ b) ∘ a″ ≈⟨ pullʳ tri ⟩
    b′ ∘ c        ∎

  -- essentially composition in the over category
  glueTrianglesʳ : a ∘ b ≈ a′ → a′ ∘ b′ ≈ a″ → a ∘ (b ∘ b′) ≈ a″
  glueTrianglesʳ {a = a} {b = b} {a′ = a′} {b′ = b′} {a″ = a″} a∘b≡a′ a′∘b′≡a″ = begin
    a ∘ (b ∘ b′) ≈⟨ pullˡ a∘b≡a′ ⟩
    a′ ∘ b′      ≈⟨ a′∘b′≡a″ ⟩
    a″           ∎

  -- essentially composition in the under category
  glueTrianglesˡ : a′ ∘ b′ ≈ b″ → a ∘ b ≈ b′ → (a′ ∘ a) ∘ b ≈ b″
  glueTrianglesˡ {a′ = a′} {b′ = b′} {b″ = b″} {a = a} {b = b} a′∘b′≡b″ a∘b≡b′ = begin
    (a′ ∘ a) ∘ b ≈⟨ pullʳ a∘b≡b′ ⟩
    a′ ∘ b′      ≈⟨ a′∘b′≡b″ ⟩
    b″           ∎

  -- Cancel (or insert) inverses on right/left/middle
  module Cancellers (inv : h ∘ i ≈ id) where

    cancelʳ : (f ∘ h) ∘ i ≈ f
    cancelʳ {f = f} = begin
      (f ∘ h) ∘ i ≈⟨ pullʳ inv ⟩
      f ∘ id      ≈⟨ identityʳ ⟩
      f           ∎

    insertʳ : f ≈ (f ∘ h) ∘ i
    insertʳ = ⟺ cancelʳ

    cancelˡ : h ∘ (i ∘ f) ≈ f
    cancelˡ {f = f} = begin
      h ∘ (i ∘ f) ≈⟨ pullˡ inv ⟩
      id ∘ f      ≈⟨ identityˡ ⟩
      f           ∎

    insertˡ : f ≈ h ∘ (i ∘ f)
    insertˡ = ⟺ cancelˡ

    cancelInner : (f ∘ h) ∘ (i ∘ g) ≈ f ∘ g
    cancelInner = pullˡ cancelʳ

    insertInner : f ∘ g ≈ (f ∘ h) ∘ (i ∘ g)
    insertInner = ⟺ cancelInner
    
  open Cancellers public

  -- operate in the 'center' instead (like pull/push)
  center : g ∘ h ≈ a → (f ∘ g) ∘ (h ∘ i) ≈ f ∘ (a ∘ i)
  center eq = pullʳ (pullˡ eq)

  -- operate on the left part, then the right part
  center⁻¹ : f ∘ g ≈ a → h ∘ i ≈ b →  f ∘ ((g ∘ h) ∘ i) ≈ a ∘ b
  center⁻¹ {f = f} {g = g} {a = a} {h = h} {i = i} {b = b} eq eq′ = begin
    f ∘ (g ∘ h) ∘ i ≈⟨ refl⟩∘⟨ pullʳ eq′ ⟩
    f ∘ (g ∘ b)     ≈⟨ pullˡ eq ⟩
    a ∘ b           ∎

  -- could be called pull₃ʳ
  pull-last : h ∘ i ≈ a → (f ∘ g ∘ h) ∘ i ≈ f ∘ g ∘ a
  pull-last eq = pullʳ (pullʳ eq)

  pull-first : f ∘ g ≈ a → f ∘ ((g ∘ h) ∘ i) ≈ a ∘ (h ∘ i)
  pull-first {f = f} {g = g} {a = a} {h = h} {i = i} eq = begin
    f ∘ (g ∘ h) ∘ i ≈⟨ refl⟩∘⟨ assoc ⟩
    f ∘ g ∘ h ∘ i   ≈⟨ pullˡ eq ⟩
    a ∘ h ∘ i       ∎

  pull-center : g ∘ h ≈ a → f ∘ (g ∘ (h ∘ i)) ≈ f ∘ (a ∘ i)
  pull-center eq = ∘-resp-≈ʳ (pullˡ eq)

  push-center : g ∘ h ≈ a → f ∘ (a ∘ i) ≈ f ∘ (g ∘ (h ∘ i))
  push-center eq = Equiv.sym (pull-center eq)

  intro-first : a ∘ b ≈ id → f ∘ g ≈ a ∘ ((b ∘ f) ∘ g)
  intro-first {a = a} {b = b} {f = f} {g = g} eq = begin
    f ∘ g             ≈⟨ introˡ eq ⟩
    (a ∘ b) ∘ (f ∘ g) ≈⟨ pullʳ sym-assoc ⟩
    a ∘ ((b ∘ f) ∘ g) ∎

  intro-last : a ∘ b ≈ id → f ∘ g ≈ f ∘ (g ∘ a) ∘ b
  intro-last {a = a} {b = b} {f = f} {g = g} eq = begin
    f ∘ g           ≈⟨ introʳ eq ⟩
    (f ∘ g) ∘ a ∘ b ≈⟨ pullʳ sym-assoc ⟩
    f ∘ (g ∘ a) ∘ b ∎



module NaturalTransformationCore where
  open import Level

  open CategoryCore
  open FunctorCore renaming (id to idF)
  open FunctorProperties
  --import Categories.Morphism as Morphism
  module MR = MorphismReasoning

  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

  private
    variable
      o ℓ e o′ ℓ′ e′ : Level
      C D E : Category o ℓ e

  record NaturalTransformation {C : Category o ℓ e}
                               {D : Category o′ ℓ′ e′}
                               (F G : Functor C D) : Set (o ⊔ ℓ ⊔ ℓ′ ⊔ e′) where
    no-eta-equality
    private
      module F = Functor F
      module G = Functor G
    open F using (F₀; F₁)
    open Category D hiding (op)

    field
      η           : ∀ X → D [ F₀ X , G.F₀ X ]
      commute     : ∀ {X Y} (f : C [ X , Y ]) → η Y ∘ F₁ f ≈ G.F₁ f ∘ η X
      -- We introduce an extra proof to ensure the opposite of the opposite of a natural
      -- transformation is definitionally equal to itself.
      sym-commute : ∀ {X Y} (f : C [ X , Y ]) → G.F₁ f ∘ η X ≈ η Y ∘ F₁ f

    op : NaturalTransformation G.op F.op
    op = record
      { η           = η
      ; commute     = sym-commute
      ; sym-commute = commute
      }

  -- Just like `Category`, we introduce a helper definition to ease the actual
  -- construction of a natural transformation.
  record NTHelper {C : Category o ℓ e}
                  {D : Category o′ ℓ′ e′}
                  (F G : Functor C D) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
    private
      module G = Functor G
    open Functor F using (F₀; F₁)
    open Category D hiding (op)
    field
      η           : ∀ X → D [ F₀ X , G.F₀ X ]
      commute     : ∀ {X Y} (f : C [ X , Y ]) → η Y ∘ F₁ f ≈ G.F₁ f ∘ η X

  ntHelper : ∀ {F G : Functor C D} → NTHelper F G → NaturalTransformation F G
  ntHelper {D = D} α = record
    { η           = η
    ; commute     = commute
    ; sym-commute = λ f → Equiv.sym (commute f)
    }
    where open NTHelper α
          open Category D

  -- Don't use ntHelper as it produces non-reduction in other places
  -- and be pedantic about arguments too, this helps inference too.
  id : ∀ {F : Functor C D} → NaturalTransformation F F
  id {D = D} {F} = record
    { η = λ _ → D.id
    ; commute = λ f → id-comm-sym {f = Functor.F₁ F f}
    ; sym-commute = λ f → id-comm {f = Functor.F₁ F f}
    }
    where
    module D = Category D
    open MR D

  infixr 9 _∘ᵥ_ _∘ₕ_ _∘ˡ_ _∘ʳ_

  -- "Vertical composition"
  _∘ᵥ_ : ∀ {F G H : Functor C D} →
           NaturalTransformation G H → NaturalTransformation F G → NaturalTransformation F H
  _∘ᵥ_ {C = C} {D = D} {F} {G} {H} X Y = record
    { η       = λ q → D [ X.η q ∘ Y.η q ]
    ; commute = λ f → glue (X.commute f) (Y.commute f)
    ; sym-commute = λ f → Category.Equiv.sym D (glue (X.commute f) (Y.commute f))
    }
    where module X = NaturalTransformation X
          module Y = NaturalTransformation Y
          open MR D

  -- "Horizontal composition"
  _∘ₕ_ : ∀ {F G : Functor C D} {H I : Functor D E} →
           NaturalTransformation H I → NaturalTransformation F G → NaturalTransformation (H ∘F F) (I ∘F G)
  _∘ₕ_ {E = E} {F} {I = I} Y X = ntHelper record
    { η = λ q → E [ I₁ (X.η q) ∘ Y.η (F.F₀ q) ]
    ; commute = λ f → glue ([ I ]-resp-square (X.commute f)) (Y.commute (F.F₁ f))
    }
    where module F = Functor F
          module X = NaturalTransformation X
          module Y = NaturalTransformation Y
          open Functor I renaming (F₀ to I₀; F₁ to I₁)
          open MR E

  _∘ˡ_ : ∀ {G H : Functor C D} (F : Functor D E) → NaturalTransformation G H → NaturalTransformation (F ∘F G) (F ∘F H)
  _∘ˡ_ F α = record
    { η           = λ X → F₁ (η X)
    ; commute     = λ f → [ F ]-resp-square (commute f)
    ; sym-commute = λ f → [ F ]-resp-square (sym-commute f)
    }
    where open Functor F
          open NaturalTransformation α

  _∘ʳ_ : ∀ {G H : Functor D E} → NaturalTransformation G H → (F : Functor C D) → NaturalTransformation (G ∘F F) (H ∘F F)
  _∘ʳ_ {D = D} {E = E} {G = G} {H = H} α F = record
    { η           = λ X → η (F₀ X)
    ; commute     = λ f → commute (F₁ f)
    ; sym-commute = λ f → sym-commute (F₁ f)
    }
    where open Functor F
          open NaturalTransformation α

  id∘id⇒id : {C : Category o ℓ e} → NaturalTransformation {C = C} {D = C} (idF ∘F idF) idF
  id∘id⇒id {C = C} = record
    { η           = λ _ → Category.id C
    ; commute     = λ f → MR.id-comm-sym C {f = f}
    ; sym-commute = λ f → MR.id-comm C {f = f}
    }

  id⇒id∘id : {C : Category o ℓ e} → NaturalTransformation {C = C} {D = C} idF (idF ∘F idF)
  id⇒id∘id {C = C} = record
    { η           = λ _ → Category.id C
    ; commute     = λ f → MR.id-comm-sym C {f = f}
    ; sym-commute = λ f → MR.id-comm C {f = f}
    }

  module _ {F : Functor C D} where
    open Category.HomReasoning D
    open Functor F
    open Category D
    open MR D
    private module D = Category D

    F⇒F∘id : NaturalTransformation F (F ∘F idF)
    F⇒F∘id = record { η = λ _ → D.id ; commute = λ _ → id-comm-sym ; sym-commute = λ _ → id-comm }

    F⇒id∘F : NaturalTransformation F (idF ∘F F)
    F⇒id∘F = record { η = λ _ → D.id ; commute = λ _ → id-comm-sym ; sym-commute = λ _ → id-comm }

    F∘id⇒F : NaturalTransformation (F ∘F idF) F
    F∘id⇒F = record { η = λ _ → D.id ; commute = λ _ → id-comm-sym ; sym-commute = λ _ → id-comm }

    id∘F⇒F : NaturalTransformation (idF ∘F F) F
    id∘F⇒F = record { η = λ _ → D.id ; commute = λ _ → id-comm-sym ; sym-commute = λ _ → id-comm }

  --private
  --  op-involutive : {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {F G : Functor C D} →
  --                  (α : NaturalTransformation F G) → NaturalTransformation.op (NaturalTransformation.op α) ≡ α
  --  op-involutive _ = ≡.refl


-- ok now we have all the definitions we need
module NatEquiv {o ℓ e} where
  open CategoryCore 
  open FunctorCore using (Functor) renaming (id to idF)
  module MR =  MorphismReasoning
  open NaturalTransformationCore using (NaturalTransformation; _∘ʳ_; _∘ˡ_; _∘ᵥ_; _∘ₕ_) renaming (id to idN)
  --open import Categories.NaturalTransformation.Equivalence using (_≃_; ≃-isEquivalence)
  open import Relation.Binary using (Rel; IsEquivalence; Setoid)

  open import Level using (_⊔_) renaming (suc to lsuc)

  infix 4 _≃_
  -- We use a one-constructor data type, instead of a type alias or record to avoid eta equality.
  -- This avoids Agda eagerly expanding the definition of _≃_ as a function, and improves unification.
  data _≃_ {C D : Category o ℓ e} {F G : Functor C D} : Rel (NaturalTransformation F G) (o ⊔ ℓ ⊔ e) where
    ≃-ext :  {α β : NaturalTransformation F G} →
            (∀ {x} → D [ (NaturalTransformation.η α x) ≈ (NaturalTransformation.η β x) ]) →
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
  ∘ᵥ-resp-≃ˡ {α} e = ∘ᵥ-resp-≃ e (refl )
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

  module Pullsᵥ {C D : Category o ℓ e} {F G H : Functor C D}
                {α : NaturalTransformation G H} {β : NaturalTransformation F G}
                {γ : NaturalTransformation F H} (αβ≃γ : α ∘ᵥ β ≃ γ) where
    open NatReasoning

    pullʳ : ∀ {I : Functor C D} {δ : NaturalTransformation H I} → (δ ∘ᵥ α) ∘ᵥ β ≃ δ ∘ᵥ γ
    pullʳ {δ = δ} = begin
      (δ ∘ᵥ α) ∘ᵥ β ≈⟨ ∘ᵥ-assoc ⟩
      δ ∘ᵥ (α ∘ᵥ β) ≈⟨ refl⟩∘ᵥ⟨ αβ≃γ ⟩
      δ ∘ᵥ γ        ∎

    pullˡ : ∀ {I : Functor C D} {δ : NaturalTransformation I F} → α ∘ᵥ β ∘ᵥ δ ≃ γ ∘ᵥ δ
    pullˡ {I = I} {δ = δ} = begin
      α ∘ᵥ β ∘ᵥ δ     ≈˘⟨ ∘ᵥ-assoc ⟩
      (α ∘ᵥ  β) ∘ᵥ δ   ≈⟨ αβ≃γ ⟩∘ᵥ⟨refl ⟩
      γ ∘ᵥ δ          ∎

  open Pullsᵥ public


  --module Products where
  --  open import Categories.Category.Product using (_⁂_; _⁂ⁿ_)
  --  open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂; <_,_>; swap)

  --  ≃-swap : (α ⁂ⁿ δ) ≃ (β ⁂ⁿ γ) → (δ ⁂ⁿ α) ≃ (γ ⁂ⁿ β)
  --  ≃-swap (≃-ext e) = ≃-ext (swap e)

  --  ⁂ⁿ∘⁂ⁿ : ∀ {A B : Category o ℓ e} {F G H : Functor A B} {K J L : Functor C D}
  --            {α : NaturalTransformation G H} {β : NaturalTransformation J L}
  --            {δ : NaturalTransformation F G} {γ : NaturalTransformation K J} →
  --            (α ⁂ⁿ β) ∘ᵥ (δ ⁂ⁿ γ) ≃ (α ∘ᵥ δ) ⁂ⁿ (β ∘ᵥ γ)
  --  ⁂ⁿ∘⁂ⁿ  {D} {B}  = ≃-ext (B.refl , D.refl)
  --    where module B = Category.Equiv B
  --          module D = Category.Equiv D

  --  ⁂ⁿ-resp-≃ : α ≃ β → δ ≃ γ → (α ⁂ⁿ δ) ≃ (β ⁂ⁿ γ)
  --  ⁂ⁿ-resp-≃  (≃-ext e₁) (≃-ext e₂) = ≃-ext (e₁ , e₂)

  --  infixr 4 _⟩⁂ⁿ⟨_
  --  infixl 5 _⟩⁂ⁿ⟨refl
  --  _⟩⁂ⁿ⟨_ : α ≃ β → δ ≃ γ → (α ⁂ⁿ δ) ≃ (β ⁂ⁿ γ)
  --  _⟩⁂ⁿ⟨_ = ⁂ⁿ-resp-≃

  --  _⟩⁂ⁿ⟨refl : α ≃ β → (α ⁂ⁿ γ) ≃ (β ⁂ⁿ γ)
  --  e ⟩⁂ⁿ⟨refl = e ⟩⁂ⁿ⟨ refl
  --    where open IsEquivalence ≃-isEquivalence

  --  id⁂ⁿ∘⁂ⁿid : ∀ {A B : Category o ℓ e} {F G : Functor A B} {K J : Functor C D}
  --                {α : NaturalTransformation F G} {β : NaturalTransformation K J} →
  --                (idN ⁂ⁿ α) ∘ᵥ (β ⁂ⁿ idN) ≃ β ⁂ⁿ α
  --  id⁂ⁿ∘⁂ⁿid {D} {B} {α} {β} = begin
  --      (idN ⁂ⁿ α) ∘ᵥ (β ⁂ⁿ idN) ≈⟨ ⁂ⁿ∘⁂ⁿ ⟩
  --      (idN ∘ᵥ β) ⁂ⁿ (α ∘ᵥ idN) ≈⟨ ≃-ext D.identityˡ ⟩⁂ⁿ⟨ ≃-ext B.identityʳ ⟩
  --      β ⁂ⁿ α                   ∎
  --    where open NatReasoning
  --          module B = Category B
  --          module D = Category D

  --  ⁂ⁿid∘id⁂ⁿ : ∀ {A B : Category o ℓ e} {F G : Functor A B} {K J : Functor C D}
  --                {α : NaturalTransformation F G} {β : NaturalTransformation K J} →
  --                (α ⁂ⁿ idN) ∘ᵥ (idN ⁂ⁿ β) ≃ α ⁂ⁿ β
  --  ⁂ⁿid∘id⁂ⁿ {D} {B} {α} {β} = begin
  --      (α ⁂ⁿ idN) ∘ᵥ (idN ⁂ⁿ β) ≈⟨ ⁂ⁿ∘⁂ⁿ ⟩
  --      (α ∘ᵥ idN) ⁂ⁿ (idN ∘ᵥ β) ≈⟨ ≃-ext B.identityʳ ⟩⁂ⁿ⟨ ≃-ext D.identityˡ ⟩
  --      α ⁂ⁿ β                   ∎
  --    where open NatReasoning
  --          module B = Category B
  --          module D = Category D

  --  ⁂ⁿ-swap-∘ᵥ : ∀ {C₁ D₁ : Category o ℓ e} {F G : Functor C C₁} {K J : Functor D D₁}
  --            {α : NaturalTransformation F G} {β : NaturalTransformation K J} →
  --      (α ⁂ⁿ idN) ∘ᵥ (idN ⁂ⁿ β) ≃ (idN ⁂ⁿ β) ∘ᵥ (α ⁂ⁿ idN)
  --  ⁂ⁿ-swap-∘ᵥ {F} {G} {K} {J} = ⁂ⁿid∘id⁂ⁿ ○[ F ⁂ K ⇛ G ⁂ J ] ⟺ id⁂ⁿ∘⁂ⁿid
  --    where open NatReasoning

  --open Products public

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
