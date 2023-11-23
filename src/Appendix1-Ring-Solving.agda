module Appendix1-Ring-Solving where

open import Chapter2-Numbers
  using (ℕ; zero; suc)
open import Chapter3-Proofs
  using (_≡_; module PropEq; module ≡-Reasoning)
open PropEq
  using (refl; sym; cong)
open import Chapter4-Relations
  using (Level)
open import Chapter7-Structures
  using (List; []; _∷_; _∘_)
open import Chapter8-Isomorphisms
  using (Fin; zero; suc)

module Example-Nat-Solver where
  open import Data.Nat.Solver
  open +-*-Solver

  open import Chapter2-Numbers
    using (_+_; _*_)

  lemma₁
   : (a c n x z : ℕ) → a * c + (c * x + a * z + x * z * n) * n
                      ≡ c * (a + x * n) + z * n * (a + x * n)
  lemma₁ = solve 5 (λ a c n x z
                   → a :* c :+ (c :* x :+ a :* z :+ x :* z :* n) :* n
                   := c :* (a :+ x :* n) :+ z :* n :* (a :+ x :* n)) refl

module Example-Tactical where
  open import Data.Nat.Tactic.RingSolver

  open import Chapter2-Numbers
    using (_+_; _*_)

  ≈-trans
    : (a b c n x y z w : ℕ)
   → a + x * n ≡ b + y * n
   → b + z * n ≡ c + w * n
   → a + (x + z) * n ≡ c + (w + y) * n
  ≈-trans a b c n x y z w pxy pzw = begin
    (a + (x + z) * n)   ≡⟨ solve (a ∷ x ∷ z ∷ n ∷ []) ⟩
    (a + x * n) + z * n ≡⟨ cong ((_+ z * n)) pxy ⟩
    (b + y * n) + z * n ≡⟨ solve (b ∷ y ∷ n ∷ z ∷ []) ⟩
    (b + z * n) + y * n ≡⟨ cong (_+ y * n) pzw ⟩
    (c + (w * n)) + (y * n) ≡⟨ solve (c ∷ w ∷ n ∷ y ∷ []) ⟩
    (c + ((w + y) * n)) ∎
    where open ≡-Reasoning

  lemma₁
   : (a c n x z : ℕ) → a * c + (c * x + a * z + x * z * n) * n
                      ≡ c * (a + x * n) + z * n * (a + x * n)
  lemma₁ = solve-∀

module Sandbox-Univariate-HNF {ℓ : Level} (𝔸 : Set ℓ) where
  data HNF : Set ℓ where
    coeff : 𝔸 → HNF
    _*x+_ : HNF → 𝔸 → HNF

  postulate
    0# : 𝔸

  nonunique : HNF → HNF
  nonunique (coeff a) = coeff 0# *x+ a
  nonunique (a *x+ b) = nonunique a *x+ b

  postulate
    _+_ : 𝔸 → 𝔸 → 𝔸
    _*_ : 𝔸 → 𝔸 → 𝔸

  eval : 𝔸 → HNF → 𝔸
  eval x (coeff a) = a
  eval x (a *x+ b) = (eval x a * x) + b
