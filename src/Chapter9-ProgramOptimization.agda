module Chapter9-ProgramOptimization where

open import Chapter1-Agda
  using (_×_; _,_; proj₁; proj₂; _⊎_; inj₁; inj₂)

open import Chapter2-Numbers
  using (ℕ; zero; suc; _+_; _*_)

open import Chapter3-Proofs
  using (_≡_; case_of_; module PropEq; module ≡-Reasoning)

open PropEq
  using (refl; sym; trans; cong)

open import Chapter4-Relations
  using (Level; _⊔_; lsuc; Σ)

open import Chapter6-Decidability
  using (Dec; yes; no; map-dec)

open import Chapter7-Structures
  using ( id; _∘_; const; _≗_; prop-setoid; Setoid; ⊎-setoid
        ; ×-setoid)

open import Chapter8-Isomorphisms
  using ( Iso; _≅_; ≅-refl; ≅-sym; ≅-trans; ⊎-fin; fin-iso
        ; ×-fin; Vec; []; _∷_; lookup; Fin; zero; suc; toℕ
        ; _Has_Elements; ⊎-prop-homo; ×-prop-homo
        )

data Shape : Set where
  num : ℕ → Shape
  beside : Shape → Shape → Shape
  inside : Shape → Shape → Shape

bintrie : ℕ → Shape
bintrie zero = num 1
bintrie (suc n) = beside (bintrie n) (bintrie n)

private variable
  ℓ ℓ₁ ℓ₂ : Level

data Trie (B : Set ℓ) : Shape → Set ℓ where
  empty : {sh : Shape}                         → Trie B sh
  table : {n : ℕ}      → Vec B n              → Trie B (num n)
  both : {m n : Shape} → Trie B m → Trie B n → Trie B (beside m n)
  nest : {m n : Shape} → Trie (Trie B n) m    → Trie B (inside m n)

Ix : Shape → Set
Ix (num n)      = Fin n
Ix (beside m n) = Ix m ⊎ Ix n
Ix (inside m n) = Ix m × Ix n

∣_∣ : Shape → ℕ
∣ num m      ∣ = m
∣ beside m n ∣ = ∣ m ∣ + ∣ n ∣
∣ inside m n ∣ = ∣ m ∣ * ∣ n ∣

shape-fin : (sh : Shape) → prop-setoid (Ix sh) Has ∣ sh ∣ Elements
shape-fin (num x) = ≅-refl
shape-fin (beside sh sh₁) = ≅-trans (≅-sym ⊎-prop-homo) (⊎-fin (shape-fin sh) (shape-fin sh₁))
shape-fin (inside sh sh₁) = ≅-trans (≅-sym ×-prop-homo) (×-fin (shape-fin sh) (shape-fin sh₁))

open import Data.Fin using (_≟_)
open Iso using (to; from; from∘to)

Ix-dec : {sh : Shape} → (ix₁ ix₂ : Ix sh) → Dec (ix₁ ≡ ix₂)
Ix-dec {sh = sh} ix₁ ix₂
  = let s = shape-fin sh
    in map-dec (λ toix₁=toix₂ → begin
              ix₁               ≡⟨ sym (from∘to s ix₁) ⟩
              from s (to s ix₁) ≡⟨ cong (from s) toix₁=toix₂ ⟩
              from s (to s ix₂) ≡⟨ from∘to s ix₂ ⟩
              ix₂ ∎)
      (cong (to s)) (to s ix₁ ≟ to s ix₂)
      where open ≡-Reasoning

-,_ : {A : Set ℓ₁} {a : A} {B : A → Set ℓ₂} → B a → Σ A B
-,_ {a = a} b = a , b

tabulate : {n : ℕ} {A : Set ℓ} → (Fin n → A) → Vec A n
tabulate {n = zero} f = []
tabulate {n = suc n} f = f zero ∷ tabulate (f ∘ suc)

lookup∘tabulate
  : {n : ℕ} {A : Set ℓ}
 → (f : Fin n → A)
 → (i : Fin n)
 → lookup (tabulate f) i ≡ f i
lookup∘tabulate f zero = refl
lookup∘tabulate f (suc x) = lookup∘tabulate (f ∘ suc) x

private variable
  B : Set ℓ
  sh m n : Shape
  t₁ : Trie B m
  t₂ : Trie B n
  f : Ix sh → B

mutual
  MemoTrie : {B : Set ℓ} {sh : Shape} → (Ix sh → B) → Set ℓ
  MemoTrie {B = B} {sh = sh} f = Σ (Trie B sh) (Memoizes f)

  data Memoizes {B : Set ℓ}
    : {sh : Shape}
   → (f : Ix sh → B)
   → Trie B sh
   → Set ℓ where
    emptyM : {f : Ix sh → B} → Memoizes f empty
    tableM : {n : ℕ} {f : Ix (num n) → B}
           → Memoizes f (table (tabulate f))
    bothM : {f : Ix (beside m n) → B}
           → Memoizes (f ∘ inj₁) t₁
           → Memoizes (f ∘ inj₂) t₂
           → Memoizes f (both t₁ t₂)
    nestM : {f : Ix (inside m n) → B}
         → (subf : (ix : Ix m) → MemoTrie (f ∘ (ix ,_)))
         → Memoizes f (nest (proj₁ (to-trie {f = f} subf)))

  to-trie
    : {m n : Shape}
    → {f : Ix (inside m n) → B}
    → (subf : (ix : Ix m) → Σ (Trie B n) (Memoizes (f ∘ (ix ,_))))
    → MemoTrie (proj₁ ∘ subf)
  to-trie {m = num _} _
    = -, tableM
  to-trie {m = beside _ _} subf
    with proj₂ (to-trie (subf ∘ inj₁)) , proj₂ (to-trie (subf ∘ inj₂))
  ... | mt₁ , mt₂ = -, bothM mt₁ mt₂
  to-trie {m = inside _ _} f2
    = -, nestM (λ i → to-trie λ j → f2 (i , j))

dummy : (sh : Shape) → Ix sh → ℕ
dummy sh ix = toℕ (to (shape-fin sh) ix)

weird : Shape
weird = beside (beside (num 3)
                        (inside (num 2) (num 1)))
                (inside (num 3) (num 1))


replace
  : {fst : Trie B n}
 → (x : Ix m)
 → Memoizes (f ∘ (x ,_)) fst
 → ((ix : Ix m) → MemoTrie (f ∘ (ix ,_)))
 → MemoTrie f
replace x sub-mem subf = -, nestM (λ ix →
   case Ix-dec ix x of λ
     { (yes refl) → -, sub-mem
     ; (no z)     → subf ix
     })

get′ : {t : Trie B sh}
    → Memoizes f t
    → Ix sh
    → B × MemoTrie f
get′ {sh = num x} {f = f} emptyM a =
  let t = tabulate f
    in lookup t a , table t , tableM
get′ {sh = beside m n} emptyM (inj₁ x)
  with get′ emptyM x
... | b , t₁ , memo = b , both t₁ empty , bothM memo emptyM
get′ {sh = beside m n} emptyM (inj₂ y)
  with get′ emptyM y
... | b , t₂ , memo = b , both empty t₂ , bothM emptyM memo
get′ {sh = inside m n} {f = f} emptyM (x , y)
  with get′ { f = f ∘ (x ,_) } emptyM y
... | b , _ , sub-mem = b , replace x sub-mem λ ix → -, emptyM
get′ {sh = num_} {t = table t} tableM a
  = lookup t a , table t , tableM
get′ {sh = beside m n} (bothM l r) (inj₁ x)
  with get′ l x
... | b , t₁ , memo = b , both t₁ _ , bothM memo r
get′ {sh = beside m n} (bothM l r) (inj₂ y)
  with get′ r y
... | b , t₂ , memo = b , both _ t₂ , bothM l memo
get′ {sh = inside m n} (nestM subf) (x , y)
  with subf x
... | _ , sub-mem
  with get′ sub-mem y
... | b , _ , _ = b , replace x sub-mem subf
