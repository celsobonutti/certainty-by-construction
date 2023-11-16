module Chapter6-Decidability where

open import Chapter1-Agda
  using (Bool; true; false)

open import Chapter2-Numbers
  using (ℕ; zero; suc; _+_)

open import Chapter3-Proofs
  using (_≡_; module PropEq; module ≡-Reasoning; suc-injective)

open PropEq

open import Chapter4-Relations
  using (Level; _⊔_; lsuc; Σ; _,_)

module Sandbox-Inequality where
  data _≢_ {A : Set} : A → A → Set where
    ineq : {x y : A} → x ≢ y

module Sandbox-Explosion where
  _IsFalse : Set → Set₁
  P IsFalse = P → {A : Set} → A

  2≢3 : (2 ≡ 3) IsFalse
  2≢3 ()

module Definition-Bottom where
  data ⊥ : Set where

  open import Chapter4-Relations using (Reflexive; Transitive)

  2≢3 : 2 ≡ 3 → ⊥
  2≢3 ()

  ⊥-elim : {A : Set} → ⊥ → A
  ⊥-elim ()

  ⊥-unique : {x y : ⊥} → x ≡ y
  ⊥-unique {x} = ⊥-elim x

  ¬_ : {ℓ : Level} → Set ℓ → Set ℓ
  ¬ P = P → ⊥

  infix 3 ¬_

  _ : ¬ (2 ≡ 3)
  _ = λ ()

  _≢_ : {A : Set} → A → A → Set
  x ≢ y = ¬ x ≡ y

  infix 4 _≢_

  ≢-sym : {A : Set} {x y : A} → x ≢ y → y ≢ x
  ≢-sym x≢y y≡x = x≢y (sym y≡x)

  ¬≢-refl : ¬ ({A : Set} → Reflexive {A = A} _≢_)
  ¬≢-refl ¬≡-refl = ¬≡-refl {ℕ} {zero} refl

  ¬≢-trans : ¬ ({A : Set} → Transitive {A = A} _≢_)
  ¬≢-trans ≢-trans = ≢-trans 2≢3 (≢-sym 2≢3) refl

open import Relation.Nullary
  using (¬_)

module Example-NoMonusLeftIdentity where
  open Chapter2-Numbers using (_∸_)

  ¬∸-identityˡ : ¬ Σ ℕ (λ e → (x : ℕ) → e ∸ x ≡ x)
  ¬∸-identityˡ (e , e-is-id)
    with e-is-id 0 | e-is-id 1
  ...    | refl    | ()

module Sandbox-Decidability where
  open Chapter2-Numbers
    using (Maybe; just; nothing)

  n=5? : (n : ℕ) → Maybe (n ≡ 5)
  n=5? 5 = just refl
  n=5? _ = nothing

  data Dec {ℓ : Level} (P : Set ℓ) : Set ℓ where
    yes :   P → Dec P
    no  : ¬ P → Dec P

open import Relation.Nullary using (Dec; yes; no)

module Nat-Properties where
  _==_ : ℕ → ℕ → Bool
  zero == zero = true
  zero == suc _ = false
  suc _ == zero = false
  suc x == suc y = x == y

  _≟_ : (x y : ℕ) → Dec (x ≡ y)
  zero ≟ zero = yes refl
  zero ≟ suc y = no λ ()
  suc x ≟ zero = no λ ()
  suc x ≟ suc y with x ≟ y
  ... | yes refl = yes refl
  ... | no p = no λ {refl → p refl}

  DecidableEquality : {ℓ : Level} (A : Set ℓ) → Set ℓ
  DecidableEquality A = (x y : A) → Dec (x ≡ y)

  _≟ℕ_ : DecidableEquality ℕ
  _≟ℕ_ = _≟_

  map-dec : {ℓ₁ ℓ₂ : Level} {P : Set ℓ₁} {Q : Set ℓ₂}
    → (P → Q) → (Q → P)
    → Dec P → Dec Q
  map-dec to from (yes p) = yes (to p)
  map-dec to from (no ¬p) = no λ x → ¬p (from x)
