module Chapter5-Modular-Arithmetic where

open import Chapter1-Agda
open import Chapter2-Numbers
open import Chapter3-Proofs
open PropEq using (cong)
open import Chapter4-Relations

module Playground-Instances where

    default : {ℓ : Level} {A : Set ℓ} → ⦃ a : A ⦄ → A
    default ⦃ a ⦄ = a

    private instance
      default-ℕ : ℕ
      default-ℕ = 0

      default-Bool : Bool
      default-Bool = false

    _ : default ≡ 0
    _ = PropEq.refl

    _ : default ≡ false
    _ = PropEq.refl

    private instance
      find-z≤n : { n : ℕ } → 0 ≤ n
      find-z≤n = z≤n

      find-s≤n : { m n : ℕ } → ⦃ m ≤ n ⦄ → suc m ≤ suc n
      find-s≤n ⦃ m≤n ⦄ = s≤s m≤n

    _ : 10 ≤ 20
    _ = default

module Playground-Instances₂ where
  record HasDefault {ℓ : Level} (A : Set ℓ) : Set ℓ where
    constructor default-of
    field
      the-default : A

  default : {ℓ : Level} {A : Set ℓ} → ⦃ HasDefault A ⦄ → A
  default ⦃ default-of val ⦄ = val

  private instance
    _ = default-of 0
    _ = default-of false

  data Color : Set where
    red green blue : Color

  private instance
    _ = green

  open HasDefault ⦃...⦄

open IsEquivalence ⦃...⦄ public

instance
  equiv-to-preorder
    : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {_~_ : Rel A ℓ₂}
    → ⦃ IsEquivalence _~_ ⦄
    → IsPreorder _~_
  equiv-to-preorder = isPreorder

  ≡-is-equivalence = ≡-equiv

module ℕ/nℕ (n : ℕ) where

  record _≈_ (a b : ℕ) : Set where
    constructor ≈-mod
    field
      x y : ℕ
      is-mod : a + x * n ≡ b + y * n

  infix 4 _≈_

  ≈-refl : Reflexive _≈_
  ≈-refl = ≈-mod 0 0 refl

  ≈-sym : Symmetric _≈_
  ≈-sym (≈-mod x y is-mod) = ≈-mod y x (sym is-mod)

  lemma₁ : (a x z : ℕ) → a + (x + z) * n ≡ (a + x * n) + z * n
  lemma₁ a x z =
    begin
    a + (x + z) * n
    ≡⟨ cong (a +_) (*-distribʳ-+ n x z) ⟩
    a + (x * n + z * n)
    ≡⟨ sym (+-assoc a (x * n) (z * n)) ⟩
    (a + x * n) + z * n
    ∎
    where open ≡-Reasoning

  lemma₂ : (i j k : ℕ) → (i + j) + k ≡ (i + k + j)
  lemma₂ i j k =
    begin
    i + j + k
    ≡⟨ +-assoc i j k ⟩
    i + (j + k)
    ≡⟨ cong (i +_) (+-comm j k) ⟩
    i + (k + j)
    ≡⟨ sym (+-assoc i k j) ⟩
    i + k + j
    ∎
    where open ≡-Reasoning

  ≈-trans : Transitive _≈_
  ≈-trans {a} {b} {c} (≈-mod x y pxy) (≈-mod z w pzw) = ≈-mod (x + z) (w + y)
    ( begin
      a + (x + z) * n ≡⟨ lemma₁ a x z ⟩
      (a + x * n) + z * n ≡⟨ cong (_+ z * n) pxy ⟩
      b + y * n + z * n ≡⟨ lemma₂ b (y * n) (z * n) ⟩
      b + z * n + y * n ≡⟨ cong (_+ y * n) pzw ⟩
      c + w * n + y * n ≡⟨ sym (lemma₁ c w y) ⟩
      c + (w + y) * n ∎
    )
    where open ≡-Reasoning

  ≈-preorder : IsPreorder _≈_
  IsPreorder.refl  ≈-preorder = ≈-refl
  IsPreorder.trans ≈-preorder = ≈-trans

  ≈-equiv : IsEquivalence _≈_
  IsEquivalence.isPreorder ≈-equiv = ≈-preorder
  IsEquivalence.sym        ≈-equiv = ≈-sym

  instance
    _ = ≈-equiv

  module Mod-Reasoning where
    open Preorder-Reasoning ≈-preorder
      hiding (refl; trans)
      public

  0≈n : 0 ≈ n
  0≈n = ≈-mod 1 zero PropEq.refl

  suc-cong-mod : {a b : ℕ} → a ≈ b → suc a ≈ suc b
  suc-cong-mod (≈-mod x y is-mod) = ≈-mod x y (cong suc is-mod)

  +-zero-mod : (a b : ℕ) → a ≈ 0 → a + b ≈ b
  +-zero-mod a zero a≈0 =
    begin
    a + zero ≡⟨ +-identityʳ a ⟩
    a        ≈⟨ a≈0 ⟩
    zero     ∎
    where open Mod-Reasoning
  +-zero-mod a (suc b) a≈0 =
    begin
    a + suc b   ≡⟨ +-suc a b ⟩
    suc (a + b) ≈⟨ suc-cong-mod (+-zero-mod a b a≈0) ⟩
    suc b       ∎
    where open Mod-Reasoning

  suc-injective-mod : {a b : ℕ} → suc a ≈ suc b → a ≈ b
  suc-injective-mod (≈-mod x y is-mod) = ≈-mod x y (suc-injective is-mod)

  +-cong₂-mod : {a b c d : ℕ}
    → a ≈ b → c ≈ d
    → a + c ≈ b + d
  +-cong₂-mod {zero} {b} {c} {d} pab pcd = begin
    c     ≈⟨ pcd ⟩
    d     ≈⟨ sym (+-zero-mod b d (sym pab)) ⟩
    b + d ∎
    where open Mod-Reasoning
  +-cong₂-mod {suc a} {zero} {c} {d} pab pcd =
    begin
    suc a + c ≈⟨ +-zero-mod (suc a) c pab ⟩
    c         ≈⟨ pcd ⟩
    d         ∎
    where open Mod-Reasoning
  +-cong₂-mod {suc a} {suc b} {c} {d} pab pcd = suc-cong-mod (+-cong₂-mod (suc-injective-mod pab) pcd)

  *-zero-mod : (a b : ℕ) → b ≈ 0 → a * b ≈ 0
  *-zero-mod zero b _ = refl
  *-zero-mod (suc a) b b≈0 =
    begin
    b + a * b ≈⟨  +-cong₂-mod b≈0 (*-zero-mod a b b≈0) ⟩
    0 ∎
    where open Mod-Reasoning

  *-cong₂-mod
    : {a b c d : ℕ}
    → a ≈ b
    → c ≈ d
    → a * c ≈ b * d
  *-cong₂-mod {zero} {b} {c} {d} a≈b c≈d =
    begin
    zero  ≈⟨ sym (*-zero-mod d b (sym a≈b)) ⟩
    d * b ≡⟨ *-comm d b ⟩
    b * d ∎
    where open Mod-Reasoning
  *-cong₂-mod {suc a} {zero} {c} {d} a≈b c≈d =
    begin
    suc a * c ≡⟨ *-comm (suc a) c ⟩
    c * suc a ≈⟨ *-zero-mod c (suc a) a≈b ⟩
    zero ∎
    where open Mod-Reasoning
  *-cong₂-mod {suc a} {suc b} {c} {d} a≈b c≈d =
    begin
    c + a * c ≈⟨ +-cong₂-mod c≈d (*-cong₂-mod (suc-injective-mod a≈b) c≈d) ⟩
    d + b * d ∎
    where open Mod-Reasoning
