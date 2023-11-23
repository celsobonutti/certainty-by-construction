module Chapter8-Isomorphisms where

open import Chapter1-Agda
  using ( Bool; true; false; _×_; proj₁; proj₂; uncurry; _⊎_
        ; inj₁; inj₂)

open import Chapter2-Numbers
  using (ℕ; zero; suc; _+_; _*_; _^_; Maybe; just; nothing)

open import Chapter3-Proofs
  renaming (module PropEq to ≡)

open import Chapter4-Relations

open import Chapter5-Modular-Arithmetic
  using (equiv-to-preorder; ≡-is-equivalence; refl; sym; trans)

open import Chapter6-Decidability
  using (⊥)

open import Chapter7-Structures
  hiding (length)

module Definition-=Fin where
  data Fin : ℕ → Set where
    zero : {n : ℕ} → Fin (ℕ.suc n)
    suc  : {n : ℕ} → Fin n → Fin (ℕ.suc n)

  0f 1f 2f 3f 4f : Fin 5
  0f = zero
  1f = suc zero
  2f = suc (suc zero)
  3f = suc (suc (suc zero))
  4f = suc (suc (suc (suc zero)))

  toℕ : {n : ℕ} → Fin n → ℕ
  toℕ zero = ℕ.zero
  toℕ (suc x) = ℕ.suc (toℕ x)

  inject+ : {m : ℕ} → (n : ℕ) → Fin m → Fin (m + n)
  inject+ n zero = zero
  inject+ n (suc x) = suc (inject+ n x)

  raise : {n : ℕ} → (m : ℕ) → Fin n → Fin (m + n)
  raise zero x = x
  raise (suc m) x = suc (raise m x)

open import Data.Fin
  using (Fin; zero; suc; inject+; raise; #_; _↑ʳ_; _↑ˡ_)

private variable
  ℓ : Level
  m n : ℕ

module Definition-Vectors where
  data Vec (A : Set ℓ) : ℕ → Set ℓ where
    []  : Vec A 0
    _∷_ : A → Vec A n → Vec A (suc n)
  infixr 5 _∷_

open import Data.Vec
  using (Vec; []; _∷_)

module Example-Vectors where
  private variable
    A : Set ℓ

  length : Vec A n → ℕ
  length {n = n} _ = n

  lookup : Vec A n → Fin n → A
  lookup (a ∷ _) zero = a
  lookup (_ ∷ as) (suc ix) = lookup as ix

  _ : lookup (6 ∷ 3 ∷ 5 ∷ []) (# 2) ≡ 5
  _ = ≡.refl

  Vec′ : Set ℓ → ℕ → Set ℓ
  Vec′ A n = Fin n → A

  []′ : Vec′ A 0
  []′ ()

  _∷′_ : A → Vec′ A n → Vec′ A (suc n)
  (x ∷′ x₁) zero = x
  (x ∷′ v) (suc index) = v index

  length′ : Vec′ A n → ℕ
  length′ {n = n} _ = n

  lookup′ : Vec′ A n → Fin n → A
  lookup′ v n = v n

  toVec′ : Vec A n → Vec′ A n
  toVec′ = lookup

  fromVec′ : Vec′ A n → Vec A n
  fromVec′ {n = zero} v = []
  fromVec′ {n = suc n} v = v zero ∷ fromVec′ (v ∘ suc)

  fromVec′∘toVec′ : (v : Vec A n) → fromVec′ (toVec′ v) ≡ v
  fromVec′∘toVec′ [] = ≡.refl
  fromVec′∘toVec′ (x ∷ v)
    rewrite fromVec′∘toVec′ v = ≡.refl

  toVec′∘fromVec′
    : (v : Vec′ A n)
    → toVec′ (fromVec′ v) ≗ v
  toVec′∘fromVec′ v zero = ≡.refl
  toVec′∘fromVec′ v (suc x) = toVec′∘fromVec′ (v ∘ suc) x

private variable
  c₁ c₂ c₃ c₄ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

record Iso
  (s₁ : Setoid c₁ ℓ₁)
  (s₂ : Setoid c₂ ℓ₂)
  : Set (c₁ ⊔ ℓ₁ ⊔ c₂ ⊔ ℓ₂) where
  constructor iso

  open Setoid s₁ using ()
    renaming (Carrier to A; _≈_ to _≈₁_)
    public

  open Setoid s₂ using ()
    renaming (Carrier to B; _≈_ to _≈₂_)
    public

  field
    to : A → B
    from : B → A
    from∘to : (x : A) → from (to x) ≈₁ x
    to∘from : (x : B) → to (from x) ≈₂ x
    to-cong : {x y : A} → x ≈₁ y → to x ≈₂ to y
    from-cong : {x y : B} → x ≈₂ y → from x ≈₁ from y

  module A-Reasoning where
    open Preorder-Reasoning (Setoid.isPreorder s₁)
      public

  module B-Reasoning where
    open Preorder-Reasoning (Setoid.isPreorder s₂)
      public

_≅_ = Iso

open Iso
module _ where
  Fn-map
    : {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
   → (f : A → B)
   → Fn (prop-setoid B) (prop-setoid C)
   → Fn (prop-setoid A) (prop-setoid C)
  Fn-map f x = fn (Fn.func x ∘ f) (Fn.cong x ∘ ≡.cong f)

  open Example-Vectors

  vec-iso
    : {A : Set c₁}
   → prop-setoid (Vec A n)
   ≅ (prop-setoid (Fin n) ⇒ prop-setoid A)
  Fn.func (to vec-iso x) = lookup x
  Fn.cong (to vec-iso x) = ≡.cong (lookup x)
  from vec-iso = fromVec′ ∘ Fn.func
  from∘to vec-iso v
    rewrite fromVec′∘toVec′ v = ≡.refl
  to∘from vec-iso v {idx} ≡.refl = toVec′∘fromVec′ (Fn.func v) idx
  to-cong vec-iso ≡.refl ≡.refl = refl
  from-cong (vec-iso {n = zero}) x = refl
  from-cong (vec-iso {n = suc n}) {v₁} {v₂} vi≡vj
    rewrite vi≡vj {x = zero} refl
    rewrite from-cong vec-iso {Fn-map suc v₁} {Fn-map suc v₂} (vi≡vj ∘ ≡.cong suc)
    = refl

private variable
  s₁ : Setoid c₁ ℓ₁
  s₂ : Setoid c₂ ℓ₂
  s₃ : Setoid c₃ ℓ₃
  s₄ : Setoid c₄ ℓ₄

≅-refl : s₁ ≅ s₁
≅-refl {s₁ = s} =
  iso id id (λ x → Setoid.refl s) (λ x → Setoid.refl s) id id

≅-sym : s₁ ≅ s₂ → s₂ ≅ s₁
≅-sym (iso to₁ from₁ from∘to₁ to∘from₁ to-cong₁ from-cong₁) = iso from₁ to₁ to∘from₁ from∘to₁ from-cong₁ to-cong₁

module _ where
  open Iso

  ≅-trans : s₁ ≅ s₂ → s₂ ≅ s₃ → s₁ ≅ s₃
  to (≅-trans f g) = to g ∘ to f
  from (≅-trans f g) = from f ∘ from g
  from∘to (≅-trans f g) x = begin
    from f (from g (to g (to f x))) ≈⟨ from-cong f (from∘to g _) ⟩
    from f (to f x)                 ≈⟨ from∘to f x ⟩
    x                               ∎
    where open A-Reasoning f
  to∘from (≅-trans f g) x = begin
    to g (to f (from f (from g x))) ≈⟨ to-cong g (to∘from f _) ⟩
    to g (from g x)                 ≈⟨ to∘from g x ⟩
    x                               ∎
    where open B-Reasoning g
  to-cong (≅-trans f g) x≈y = to-cong g (to-cong f x≈y)
  from-cong (≅-trans f g) x≈y = from-cong f (from-cong g x≈y)

≅-equiv : IsEquivalence (_≅_ {c₁ = c₁} {ℓ₁ = ℓ₁})
Setoid-Renaming.refl′ (Setoid-Renaming.pre ≅-equiv) = ≅-refl
Setoid-Renaming.trans′ (Setoid-Renaming.pre ≅-equiv) = ≅-trans
Setoid-Renaming.sym′ ≅-equiv = ≅-sym

≅-prop
  : {A : Set ℓ₁} {B : Set ℓ₂}
  → (f : A → B) → (g : B → A)
  → f ∘ g ≗ id
  → g ∘ f ≗ id
  → prop-setoid A ≅ prop-setoid B
to (≅-prop f g f∘g=id g∘f=id) = f
from (≅-prop f g f∘g=id g∘f=id) = g
from∘to (≅-prop f g f∘g=id g∘f=id) = g∘f=id
to∘from (≅-prop f g f∘g=id g∘f=id) = f∘g=id
to-cong (≅-prop f g f∘g=id g∘f=id) = ≡.cong f
from-cong (≅-prop f g f∘g=id g∘f=id) = ≡.cong g

module Sandbox-Finite where
  _Has_Elements : Setoid c₁ ℓ₁ → ℕ → Set (c₁ ⊔ ℓ₁)
  s Has cardinality Elements =
    s ≅ prop-setoid (Fin cardinality)

  fin-fin : {n : ℕ} → prop-setoid (Fin n) Has n Elements
  fin-fin = ≅-refl

  open Iso

  bool-fin : prop-setoid Bool Has 2 Elements
  to bool-fin false = zero
  to bool-fin true = suc zero
  from bool-fin zero = _
  from bool-fin (suc zero) = _
  from∘to bool-fin false = refl
  from∘to bool-fin true = refl
  to∘from bool-fin zero = refl
  to∘from bool-fin (suc zero) = refl
  to-cong bool-fin ≡.refl = refl
  from-cong bool-fin ≡.refl = refl

  fin-iso
    : s₁ Has n Elements
    → s₂ Has n Elements
    → s₁ ≅ s₂
  fin-iso s₁ s₂ = ≅-trans s₁ (≅-sym s₂)

  module ⊤-Definition where
    record ⊤ : Set where
      constructor tt

  open import Data.Unit
    using (⊤; tt)

  generic-bool : prop-setoid Bool ≅ prop-setoid (⊤ ⊎ ⊤)
  to generic-bool false = inj₁ tt
  to generic-bool true = inj₂ tt
  from generic-bool (inj₁ tt) = _
  from generic-bool (inj₂ tt) = _
  from∘to generic-bool false = refl
  from∘to generic-bool true = refl
  to∘from generic-bool (inj₁ tt) = refl
  to∘from generic-bool (inj₂ tt) = refl
  to-cong generic-bool ≡.refl = refl
  from-cong generic-bool ≡.refl = refl

  record Ratio : Set where
    constructor mkRatio
    field
      numerator : ℕ
      denominator : ℕ

  generic-ratio : prop-setoid Ratio ≅ prop-setoid (ℕ × ℕ)
  to generic-ratio (mkRatio numerator denominator) = numerator , denominator
  from generic-ratio (fst , snd) = mkRatio fst snd
  from∘to generic-ratio (mkRatio numerator denominator) = refl
  to∘from generic-ratio (fst , snd) = refl
  to-cong generic-ratio ≡.refl = refl
  from-cong generic-ratio ≡.refl = refl

  generic-list : {A : Set ℓ}
              → prop-setoid (List A)
               ≅ prop-setoid (⊤ ⊎ (A × List A))
  to generic-list [] = inj₁ tt
  to generic-list (x ∷ x₁) = inj₂ (x , x₁)
  from generic-list (inj₁ tt) = _
  from generic-list (inj₂ (fst , snd)) = _
  from∘to generic-list [] = refl
  from∘to generic-list (x ∷ x₁) = refl
  to∘from generic-list (inj₁ tt) = refl
  to∘from generic-list (inj₂ (fst , snd)) = refl
  to-cong generic-list ≡.refl = refl
  from-cong generic-list ≡.refl = refl

  ⊥-fin : prop-setoid ⊥ Has 0 Elements
  to ⊥-fin ()
  from ⊥-fin ()
  from∘to ⊥-fin ()
  to∘from ⊥-fin ()
  to-cong ⊥-fin ≡.refl = refl
  from-cong ⊥-fin ≡.refl = refl

  ⊤-fin : prop-setoid ⊤ Has 1 Elements
  to ⊤-fin _ = zero
  from ⊤-fin _ = tt
  from∘to ⊤-fin _ = refl
  to∘from ⊤-fin zero = refl
  to-cong ⊤-fin _ = refl
  from-cong ⊤-fin _ = refl

  import Data.Product as ×
  open Setoid-Renaming

  ×-preserves-≅
    : s₁ ≅ s₂
   → s₃ ≅ s₄
   → ×-setoid s₁ s₃ ≅ ×-setoid s₂ s₄
  to (×-preserves-≅ s t) = ×.map (to s) (to t)
  from (×-preserves-≅ s t) = ×.map (from s) (from t)
  from∘to (×-preserves-≅ s t) (fst , snd) = from∘to s fst , from∘to t snd
  to∘from (×-preserves-≅ s t) (fst , snd) = to∘from s fst , to∘from t snd
  to-cong (×-preserves-≅ s t) = ×.map (to-cong s) (to-cong t)
  from-cong (×-preserves-≅ s t) = ×.map (from-cong s) (from-cong t)

  ×-prop-homo
    : {A : Set ℓ₁} {B : Set ℓ₂}
   → ×-setoid (prop-setoid A) (prop-setoid B)
      ≅ prop-setoid (A × B)
  to ×-prop-homo = id
  from ×-prop-homo = id
  from∘to ×-prop-homo x = refl , refl
  to∘from ×-prop-homo x =  refl
  to-cong ×-prop-homo (≡.refl , ≡.refl) = refl
  from-cong ×-prop-homo ≡.refl = refl , refl

  import Data.Sum as ⊎
  open import Data.Sum using (_⊎_; inj₁; inj₂)

  ⊎-preserves-≅
    : s₁ ≅ s₂
   → s₃ ≅ s₄
   → ⊎-setoid s₁ s₃ ≅ ⊎-setoid s₂ s₄
  to (⊎-preserves-≅ s t) = ⊎.map (to s) (to t)
  from (⊎-preserves-≅ s t) = ⊎.map (from s) (from t)
  from∘to (⊎-preserves-≅ s t) (inj₁ x) = inj₁ (from∘to s x)
  from∘to (⊎-preserves-≅ s t) (inj₂ y) = inj₂ (from∘to t y)
  to∘from (⊎-preserves-≅ s t) (inj₁ x) = inj₁ (to∘from s x)
  to∘from (⊎-preserves-≅ s t) (inj₂ y) = inj₂ (to∘from t y)
  to-cong (⊎-preserves-≅ s t) (inj₁ x) = inj₁ (to-cong s x)
  to-cong (⊎-preserves-≅ s t) (inj₂ x) = inj₂ (to-cong t x)
  from-cong (⊎-preserves-≅ s t) (inj₁ x) = inj₁ (from-cong s x)
  from-cong (⊎-preserves-≅ s t) (inj₂ x) = inj₂ (from-cong t x)

  ⊎-prop-homo
    : {A : Set ℓ₁} {B : Set ℓ₂}
   → ⊎-setoid (prop-setoid A) (prop-setoid B)
    ≅ prop-setoid (A ⊎ B)
  to ⊎-prop-homo = id
  from ⊎-prop-homo = id
  to∘from ⊎-prop-homo = refl
  from∘to ⊎-prop-homo (inj₁ x) = inj₁ refl
  from∘to ⊎-prop-homo (inj₂ y) = inj₂ refl
  to-cong ⊎-prop-homo (inj₁ ≡.refl) = refl
  to-cong ⊎-prop-homo (inj₂ ≡.refl) = refl
  from-cong ⊎-prop-homo {inj₁ x} ≡.refl = inj₁ refl
  from-cong ⊎-prop-homo {inj₂ y} ≡.refl = inj₂ refl

  module Definition-Join-SplitAt where
    join : Fin m ⊎ Fin n → Fin (m + n)
    join {n = n} (inj₁ x) = x ↑ˡ n
    join {m = m} (inj₂ y) = m ↑ʳ y

    splitAt : (m : ℕ) → Fin (m + n) → Fin m ⊎ Fin n
    splitAt zero x = inj₂ x
    splitAt (suc m) zero = inj₁ zero
    splitAt (suc m) (suc x) = ⊎.map₁ suc (splitAt m x)

  open Data.Fin using (splitAt; join)
  open import Data.Fin.Properties
    using (splitAt-join; join-splitAt)

  join-splitAt-iso
    : prop-setoid (Fin (m + n))
    ≅ prop-setoid (Fin m ⊎ Fin n)
  to join-splitAt-iso = splitAt _
  from join-splitAt-iso = join _ _
  from∘to (join-splitAt-iso {m = m}) = join-splitAt m _
  to∘from join-splitAt-iso x = splitAt-join _ _ x
  to-cong join-splitAt-iso ≡.refl = refl
  from-cong join-splitAt-iso ≡.refl = refl

  ⊎-fin : s₁ Has m Elements
       → s₂ Has n Elements
       → ⊎-setoid s₁ s₂ Has m + n Elements
  ⊎-fin fin₁ fin₂
    = ≅-trans (⊎-preserves-≅ fin₁ fin₂)
    ( ≅-trans ⊎-prop-homo
              (≅-sym join-splitAt-iso))

  open import Data.Fin using (combine; remQuot)
  open import Data.Fin.Properties using (combine-remQuot; remQuot-combine)


  combine-remQuot-iso
    : prop-setoid (Fin (m * n))
    ≅ (prop-setoid (Fin m × Fin n))
  to combine-remQuot-iso = remQuot _
  from combine-remQuot-iso (fst , snd) = combine fst snd
  from∘to (combine-remQuot-iso {m = m}) x = combine-remQuot {m} _ x
  to∘from combine-remQuot-iso (fst , snd) = remQuot-combine fst snd
  to-cong combine-remQuot-iso ≡.refl = ≡.refl
  from-cong combine-remQuot-iso ≡.refl = ≡.refl

  ×-fin : s₁ Has m Elements → s₂ Has n Elements
       → ×-setoid s₁ s₂ Has m * n Elements
  ×-fin fin₁ fin₂
    = ≅-trans (×-preserves-≅ fin₁ fin₂)
    (≅-trans ×-prop-homo (≅-sym combine-remQuot-iso))

  ips-setoid : Setoid _ _
  Carrier ips-setoid = Set
  _≈_ ips-setoid x y = prop-setoid x ≅ prop-setoid y
  refl′ (pre (equiv ips-setoid)) = ≅-refl
  trans′ (pre (equiv ips-setoid)) = ≅-trans
  sym′ (equiv ips-setoid) = ≅-sym

  assocʳ′ : {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
         → (A × B) × C → A × (B × C)
  assocʳ′ ((fst , snd₁) , snd) = fst , snd₁ , snd

  assocˡ′ : {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
         → A × B × C → (A × B) × C
  assocˡ′ (fst , snd₁ , snd) = ((fst , snd₁) , snd)

  open Monoid

  ×-⊤-monoid : Monoid _ _
  setoid ×-⊤-monoid = ips-setoid
  _∙_ ×-⊤-monoid = _×_
  ε ×-⊤-monoid = ⊤
  assoc ×-⊤-monoid x y z = ≅-prop assocʳ′ assocˡ′ refl refl
  identityˡ ×-⊤-monoid x = ≅-prop proj₂ (tt ,_) refl refl
  identityʳ ×-⊤-monoid x = ≅-prop proj₁ (_, tt) refl refl
  ∙-cong ×-⊤-monoid h k
    = ≅-trans (≅-sym ×-prop-homo)
    ( ≅-trans (×-preserves-≅ h k)
              ×-prop-homo)

  ⊎-assocʳ : {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
          → (A ⊎ B) ⊎ C → A ⊎ (B ⊎ C)
  ⊎-assocʳ (inj₁ (inj₁ x)) = inj₁ x
  ⊎-assocʳ (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
  ⊎-assocʳ (inj₂ y) = inj₂ (inj₂ y)

  ⊎-assocˡ : {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
          → A ⊎ (B ⊎ C) → (A ⊎ B) ⊎ C
  ⊎-assocˡ (inj₁ x) = inj₁ (inj₁ x)
  ⊎-assocˡ (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
  ⊎-assocˡ (inj₂ (inj₂ y)) = inj₂ y

  ⊎-⊥-monoid : Monoid _ _
  setoid ⊎-⊥-monoid = ips-setoid
  _∙_ ⊎-⊥-monoid = _⊎_
  ε ⊎-⊥-monoid = ⊥
  assoc ⊎-⊥-monoid x y z = ≅-prop ⊎-assocʳ ⊎-assocˡ (λ { (inj₁ _) → ≡.refl
                                                       ; (inj₂ (inj₁ _)) → ≡.refl
                                                       ; (inj₂ (inj₂ _)) → ≡.refl
                                                       }
                                                    )
                                                    (λ { (inj₁ (inj₁ x)) → ≡.refl
                                                       ; (inj₁ (inj₂ y)) → ≡.refl
                                                       ; (inj₂ y) → ≡.refl
                                                       }
                                                    )
  identityˡ ⊎-⊥-monoid x = ≅-prop (λ {(inj₂ x₁) → x₁}) inj₂ (λ x → ≡.refl) λ {(inj₂ x₁) → ≡.refl}
  identityʳ ⊎-⊥-monoid x = ≅-prop (λ {(inj₁ x₁) → x₁}) inj₁ (λ x₁ → ≡.refl) (λ {(inj₁ x₁) → ≡.refl})
  ∙-cong ⊎-⊥-monoid h k = ≅-trans (≅-sym ⊎-prop-homo)
                        ( ≅-trans (⊎-preserves-≅ h k) ⊎-prop-homo)

open import Data.Vec
  using (Vec; []; _∷_; lookup)
  public
open import Data.Product
  using (assocʳ′; assocˡ′)
  public
open import Data.Fin
  using (Fin; zero; suc; toℕ; join; splitAt; combine; remQuot)
  public
open Sandbox-Finite
  hiding (assocʳ′; assocˡ′)
  public
