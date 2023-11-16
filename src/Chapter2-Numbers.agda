module Chapter2-Numbers where

import Chapter1-Agda

module Definition-Naturals where
  data ℕ : Set where
    zero : ℕ
    suc  : ℕ → ℕ

module Sandbox-Naturals where
  open import Data.Nat
    using (ℕ; zero; suc)
  open Chapter1-Agda
    using (Bool; true; false; not)

  one : ℕ
  one = suc zero

  two : ℕ
  two = suc one

  three : ℕ
  three = suc two

  four : ℕ
  four = suc (suc (suc (suc zero)))

  n=0? : ℕ → Bool
  n=0? zero = true
  n=0? (suc x) = false

  n=2? : ℕ → Bool
  n=2? (suc (suc zero)) = true
  n=2? x = false

  is-even? : ℕ → Bool
  is-even? zero = true
  is-even? (suc x) = not (is-even? x)

  data Evenℕ : Set where
    zero : Evenℕ
    suc-suc : Evenℕ → Evenℕ

  toℕ : Evenℕ → ℕ
  toℕ zero = zero
  toℕ (suc-suc x) = suc (suc (toℕ x))

  module Sandbox-Usable where
    postulate
      Usable : Set
      Unusable : Set

    IsEven : ℕ → Set
    IsEven zero = Usable
    IsEven (suc zero) = Unusable
    IsEven (suc (suc x)) = IsEven x

  data IsEven : ℕ → Set where
    zero-even    : IsEven zero
    suc-suc-even : ∀ {n} → IsEven n → IsEven (suc (suc n))

  four-is-even : IsEven four
  four-is-even = suc-suc-even (suc-suc-even zero-even)

  data IsOdd : ℕ → Set where
    one-odd : IsOdd (suc zero)
    succ-succ-odd : ∀ {n} → IsOdd n → IsOdd (suc (suc n))

  data IsOddDep : ℕ → Set where
    suc-even : ∀ {n} → IsEven n → IsOddDep (suc n)

  evenOdd : ∀ {n} → IsEven n → IsOdd (suc n)
  evenOdd zero-even = one-odd
  evenOdd (suc-suc-even x) = succ-succ-odd (evenOdd x)

  evenOdd' : ∀ {n} → IsEven n → IsOddDep (suc n)
  evenOdd' = suc-even

  data Maybe (A : Set) : Set where
    just : A → Maybe A
    nothing : Maybe A

  evenEv : (n : ℕ) → Maybe (IsEven n)
  evenEv zero = just zero-even
  evenEv (suc zero) = nothing
  evenEv (suc (suc n)) with evenEv n
  ... | just x = just (suc-suc-even x)
  ... | nothing = nothing

  _+_ : ℕ → ℕ → ℕ
  zero + y = y
  suc x + y = suc (x + y)

  infixl 6 _+_

  _*_ : ℕ → ℕ → ℕ
  zero * y = zero
  suc x * y = y + (x * y)

  infixl 7 _*_

  _^_ : ℕ → ℕ → ℕ
  x ^ zero = suc zero
  x ^ suc y = x * x ^ y

  _∸_ : ℕ → ℕ → ℕ
  zero ∸ y = zero
  suc x ∸ zero = suc x
  suc x ∸ suc y = x ∸ y

  module Natural-Tests where
    open import Relation.Binary.PropositionalEquality

    _ : one + two ≡ three
    _ = refl

module Misstep-Integers₁ where
  data ℤ : Set where
    zero : ℤ
    suc : ℤ → ℤ
    pred : ℤ → ℤ

  normalize : ℤ → ℤ
  normalize zero = zero
  normalize (suc zero) = suc zero
  normalize (suc (suc x)) = suc (normalize (suc x))
  normalize (suc (pred x)) = normalize x
  normalize (pred zero) = pred zero
  normalize (pred (suc x)) = normalize x
  normalize (pred (pred x)) = pred (normalize (pred x))

  module Counterexample where
    open import Relation.Binary.PropositionalEquality

    _ : normalize (suc (suc (pred (pred zero)))) ≡ suc (pred zero)
    _ = refl

module Misstep-Integers₂ where
  import Data.Nat as ℕ
  open ℕ using (ℕ; zero; suc)

  record ℤ : Set where
    constructor mkℤ
    field
      pos : ℕ
      neg : ℕ

  normalize : ℤ → ℤ
  normalize (mkℤ zero neg) = mkℤ zero neg
  normalize (mkℤ (suc pos) zero) = mkℤ (suc pos) zero
  normalize (mkℤ (suc pos) (suc neg)) = normalize (mkℤ pos neg)

  _+_ : ℤ → ℤ → ℤ
  mkℤ pos neg + mkℤ pos₁ neg₁ = normalize (mkℤ (pos ℕ.+ pos₁) (neg ℕ.+ neg₁))

  infixl 5 _+_

  _-_ : ℤ → ℤ → ℤ
  mkℤ pos neg - mkℤ pos₁ neg₁ = normalize (mkℤ (pos ℕ.+ neg₁) (pos₁ ℕ.+ neg))

  infixl 5 _-_

  _*_ : ℤ → ℤ → ℤ
  mkℤ pos neg * mkℤ pos₁ neg₁ = normalize (mkℤ (pos ℕ.* pos₁ ℕ.+ neg ℕ.* neg₁) (pos ℕ.* neg₁ ℕ.+ neg ℕ.* pos₁))

module Misstep-Integers₃ where
  open import Data.Nat

  data ℤ : Set where
    +_ : ℕ → ℤ
    -_ : ℕ → ℤ

module Sandbox-Ingers where
  import Data.Nat as ℕ
  open ℕ using (ℕ)

  data ℤ : Set where
    +_ : ℕ → ℤ
    -[1+_] : ℕ → ℤ

  0ℤ : ℤ
  0ℤ = + 0

  1ℤ : ℤ
  1ℤ = + 1

  -1ℤ : ℤ
  -1ℤ = -[1+ 0 ]

  suc : ℤ → ℤ
  suc (+ x) = + (ℕ.suc x)
  suc -[1+ ℕ.zero ] = + 0
  suc -[1+ ℕ.suc x ] = -[1+ x ]

  pred : ℤ → ℤ
  pred (+ ℕ.zero) = -[1+ ℕ.zero ]
  pred (+ ℕ.suc x) = (+ x)
  pred -[1+ x ] = -[1+ (ℕ.suc x) ]

  pattern +[1+_] n = + ℕ.suc n

  pattern +0 = + ℕ.zero

  -_ : ℤ → ℤ
  - -[1+ x ] = +[1+ x ]
  - +[1+ x ] = -[1+ x ]
  - +0 = + ℕ.zero

  _⊖_ : ℕ → ℕ → ℤ
  ℕ.zero ⊖ ℕ.zero = +0
  ℕ.zero ⊖ ℕ.suc x₁ = -[1+ x₁ ]
  ℕ.suc x ⊖ ℕ.zero = +[1+ x ]
  ℕ.suc x ⊖ ℕ.suc x₁ = x ⊖ x₁

  _+_ : ℤ → ℤ → ℤ
  (+ x) + (+ x₁) = + (x ℕ.+ x₁)
  (+ x) + -[1+ x₁ ] = x ⊖ (ℕ.suc x₁)
  -[1+ x ] + (+ x₁) = x₁ ⊖ (ℕ.suc x)
  -[1+ x ] + -[1+ x₁ ] = -[1+ 1 ℕ.+ x ℕ.+ x₁ ]

  infixl 5 _-_

  _-_ : ℤ → ℤ → ℤ
  x - x₁ = x + (- x₁)

  infixl 6 _*_

  _*_ : ℤ → ℤ → ℤ
  +0 * _        = +0
  +[1+ ℕ.zero ] *  x = x
  -[1+ ℕ.zero ] *  x = - x
  +[1+ ℕ.suc x ] * y = (+[1+ x ] * y) + y
  -[1+ ℕ.suc x ] * y = (-[1+ x ] * y) - y

  module Tests where
    open import Relation.Binary.PropositionalEquality

    _ : - (+ 2) * - (+ 6) ≡ + 12
    _ = refl

    _ : (+ 3) - (+ 10) ≡ - (+ 7)
    _ = refl

open import Data.Nat
  using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)
  public

open Sandbox-Naturals
  using (one; two; three; four)
  public

open Sandbox-Naturals
  using (IsEven; IsOdd)
  renaming ( zero-even to z-even
           ; suc-suc-even to ss-even
           )
  public

open import Data.Maybe
  using (Maybe; just; nothing)
  public
