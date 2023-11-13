module Chapter1-Agda where

module Example-Imports where
  open import Data.Bool hiding (not)
  open import Relation.Binary.PropositionalEquality
  open import Agda.Builtin.Sigma

  _ : Bool
  _ = false

  not : (x : Bool) → Σ Bool (λ y → x ≢ y)
  not false = true , (λ ())
  not true = false , (λ ())

module Example-TypingJudgements where
  postulate
    Bool : Set
    false : Bool
    true : Bool


module Booleans where
  open import Relation.Binary.PropositionalEquality
  open import Agda.Builtin.Sigma

  data Bool : Set where
    false : Bool
    true : Bool

  not : Bool → Bool
  not false = true
  not true = false

  auto-not : (x : Bool) → Σ Bool (x ≢_)
  auto-not false = true , (λ ())
  auto-not true = false , (λ ())

  _ : not (not false) ≡ false
  _ = refl

  _∨_ : Bool → Bool → Bool
  false ∨ y = y
  true ∨ y = true

  _∧_ : Bool → Bool → Bool
  true ∧ other = other
  false ∧ other = false

  _ : ∀ {x} → true ∨ x ≡ true
  _ = refl

module Example-Employees where
  open Booleans
  open import Data.String
    using (String)

  data Department : Set where
    administrative : Department
    engineering    : Department
    finance        : Department
    marketing      : Department
    sales          : Department

  record Employee : Set where
    field
      name :        String
      department :  Department
      is-new-hire : Bool

  tillman : Employee
  tillman = record
    { name        = "Tillman"
    ; department  = engineering
    ; is-new-hire = false
    }

module Sandbox-Tuples where
  record _×_ (A : Set) (B : Set) : Set where
    field
      proj₁ : A
      proj₂ : B

  open Booleans

  my-tuple : Bool × Bool
  my-tuple = record { proj₁ = true ; proj₂ = false }

  first : Bool × Bool → Bool
  first record { proj₁ = proj₁ } = proj₁

  open _×_

  other-first : Bool × Bool → Bool
  other-first = proj₁

  my-copattern : Bool × Bool
  proj₁ my-copattern = false
  proj₂ my-copattern = false

  _,_ : {A B : Set} → A → B → A × B
  x , x₁ = record { proj₁ = x ; proj₂ = x₁ }

module Sandbox-Tuples₂ where
  open Booleans

  record _×_ (A : Set) (B : Set) : Set where
    constructor _,_
    field
      proj₁ : A
      proj₂ : B

  open _×_

  infixr 4 _,_
  infixr 2 _×_

  data _⊎_ (A : Set) (B : Set) : Set where
    inj₁ : A → A ⊎ B
    inj₂ : B → A ⊎ B

  infixr 1 _⊎_

  curry : {A B C : Set} → (A × B → C) → (A → B → C)
  curry x x₁ x₂ = x (x₁ , x₂)

  uncurry : {A B C : Set} → (A → B → C) → (A × B → C)
  uncurry x (proj₃ , proj₄) = x proj₃ proj₄

  _ : Bool × Bool → Bool
  _ = uncurry _∨_

module Sandbox-Implicits where
  open import Data.Bool
    using (Bool; false; true; not; _∨_)
  open import Data.Product
    using (_×_; proj₁; proj₂)
    renaming ( _,′_ to _,_
             ; curry′ to curry
             ; uncurry′ to uncurry
             )

  mk-tuple : (A : Set) → (B : Set) → A → B → A × B
  mk-tuple A B x x₁ = x , x₁

  _ : Bool × Bool
  _ = mk-tuple Bool Bool false false

  data PrimaryColor : Set where
    red green blue : PrimaryColor

  color-bool-tuple : PrimaryColor × Bool
  color-bool-tuple = mk-tuple _ _ red false

open import Data.Bool
  using (Bool; false; true; not; _∨_; _∧_) public
open import Data.Product
  using (_×_; _,_; proj₁; proj₂; curry; uncurry) public
open import Data.Sum
  using (_⊎_; inj₁; inj₂) public
