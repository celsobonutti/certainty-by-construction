module Chapter7-Structures where

open import Chapter1-Agda
open import Chapter2-Numbers
open import Chapter3-Proofs
  renaming (module PropEq to ≡)
open import Chapter4-Relations
open import Chapter5-Modular-Arithmetic
  using (equiv-to-preorder; ≡-is-equivalence; sym; trans; refl)
open import Chapter6-Decidability
  using (¬_; ⊥)
open Chapter6-Decidability.BinaryTrees
  using (BinTree; leaf; branch; empty)

private variable
  ℓ ℓ₁ ℓ₂ : Level
  A : Set ℓ
  B : Set ℓ
  C : Set ℓ

private
  Op₂ : {ℓ : Level} → Set ℓ → Set ℓ
  Op₂ A = A → A → A

module Sandbox-Naive-Monoids where
  record IsMonoid {Carrier : Set ℓ}
                  (_∙_ : Op₂ Carrier)
                  (ε : Carrier)
    : Set (lsuc ℓ) where
    field
      assoc : (x y z : Carrier) → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)
      identityˡ : (x : Carrier) → ε ∙ x ≡ x
      identityʳ : (x : Carrier) → x ∙ ε ≡ x

  open IsMonoid

  *-1 : IsMonoid _*_ 1
  *-1 = record { assoc = *-assoc ; identityˡ = *-identityˡ ; identityʳ = *-identityʳ }

  +-0 : IsMonoid _+_ 0
  assoc +-0 = +-assoc
  identityˡ +-0 = +-identityˡ
  identityʳ +-0 = +-identityʳ

  ∨-false : IsMonoid _∨_ false
  assoc ∨-false = ∨-assoc
  identityˡ ∨-false = ∨-identityˡ
  identityʳ ∨-false = ∨-identityʳ

  ∧-true : IsMonoid _∧_ true
  assoc ∧-true = ∧-assoc
  identityˡ ∧-true = ∧-identityˡ
  identityʳ ∧-true = ∧-identityʳ

  xor : Bool → Bool → Bool
  xor false y = y
  xor true y = not y

  xor-false : IsMonoid xor false
  assoc xor-false false false false = ≡.refl
  assoc xor-false false false true = ≡.refl
  assoc xor-false false true false = ≡.refl
  assoc xor-false false true true = ≡.refl
  assoc xor-false true false false = ≡.refl
  assoc xor-false true false true = ≡.refl
  assoc xor-false true true false = ≡.refl
  assoc xor-false true true true = ≡.refl
  identityˡ xor-false x = ≡.refl
  identityʳ xor-false false = ≡.refl
  identityʳ xor-false true = ≡.refl

  record Monoid {c : Level} (Carrier : Set c) : Set (lsuc c) where
    infixl 7 _∙_
    field
      _∙_ : Op₂ Carrier
      ε   : Carrier
      is-monoid : IsMonoid _∙_ ε

  bundle
    : {c : Level} {A : Set c} {∙ : Op₂ A} {ε : A}
    → IsMonoid ∙ ε
    → Monoid A
  Monoid._∙_ (bundle {∙ = ∙} x) = ∙
  Monoid.ε (bundle {ε = ε} x) = ε
  Monoid.is-monoid (bundle x) = x

  open Monoid ⦃...⦄

  module _ ⦃ _ : Monoid Bool ⦄ where
    ex₁ : Bool
    ex₁ = false ∙ true ∙ false ∙ false

    ex₃ : Bool
    ex₃ = ε

  _<∣>_ : Maybe A → Maybe A → Maybe A
  just x <∣> my = just x
  nothing <∣> my = my

  <∣>-nothing : IsMonoid {Carrier = Maybe A} _<∣>_ nothing
  assoc <∣>-nothing (just x) = λ y z → ≡.refl
  assoc <∣>-nothing nothing = λ y z → ≡.refl
  identityˡ <∣>-nothing = λ x → ≡.refl
  identityʳ <∣>-nothing (just x) = ≡.refl
  identityʳ <∣>-nothing nothing = ≡.refl

  flip : (A → B → C) → B → A → C
  flip f b a = f a b

  dual : {_∙_ : Op₂ A} {ε : A}
    → IsMonoid _∙_ ε
    → IsMonoid (flip _∙_) ε
  assoc (dual m) x y z = sym (assoc m z y x)
  identityˡ (dual m)   = identityʳ m
  identityʳ (dual m)   = identityˡ m

  module Definition-List where
    data List (A : Set ℓ) : Set ℓ where
      [] : List A
      _∷_ : A → List A → List A
    infixr 5 _∷_

    _++_ : List A → List A → List A
    [] ++ ys = ys
    (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  open import Data.List using (List; []; _∷_; _++_)

  ++-[] : IsMonoid {Carrier = List A} _++_ []
  assoc ++-[] [] y z = ≡.refl
  assoc ++-[] (x ∷ xs) y z
    rewrite assoc ++-[] xs y z = ≡.refl
  identityˡ ++-[] x = ≡.refl
  identityʳ ++-[] [] = ≡.refl
  identityʳ ++-[] (x ∷ xs)
    rewrite identityʳ ++-[] xs = ≡.refl


  _∘_ : (B → C) → (A → B) → (A → C)
  (g ∘ f) x = g (f x)

  id : A → A
  id x = x

  ∘-id : IsMonoid {Carrier = A → A} _∘_ id
  assoc ∘-id = λ x y z → ≡.refl
  identityˡ ∘-id = λ x → ≡.refl
  identityʳ ∘-id = λ x → ≡.refl

  module ListSummaries where
    foldList : ⦃ Monoid B ⦄ → (A → B) → List A → B
    foldList f [] = ε
    foldList f (x ∷ xs) = f x ∙ foldList f xs

    any? : (A → Bool) → List A → Bool
    any? = foldList ⦃ bundle ∨-false ⦄

    all? : (A → Bool) → List A → Bool
    all? = foldList ⦃ bundle ∧-true ⦄

    sum : List ℕ → ℕ
    sum = foldList ⦃ bundle +-0 ⦄ id

    product : List ℕ → ℕ
    product = foldList ⦃ bundle *-1 ⦄ id

    flatten : List (List A) → List A
    flatten = foldList ⦃ bundle ++-[] ⦄ id

    head : List A → Maybe A
    head = foldList ⦃ bundle <∣>-nothing ⦄ just

    foot : List A → Maybe A
    foot = foldList ⦃ bundle (dual <∣>-nothing) ⦄ just

    reverse : List A → List A
    reverse = foldList ⦃ bundle (dual ++-[]) ⦄ (_∷ [])

    _ : reverse (1 ∷ 2 ∷ 3 ∷ []) ≡ (3 ∷ 2 ∷ 1 ∷ [])
    _ = refl

    const : A → B → A
    const a _ = a

    size : List A → ℕ
    size = foldList ⦃ bundle +-0 ⦄ (const 1)

    empty? : List A → Bool
    empty? = foldList ⦃ bundle ∧-true ⦄ (const false)

  open import Function using (id; const)

  record Foldable {ℓ₁ ℓ₂ : Level} (Container : Set ℓ₁ → Set ℓ₂)
         : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
    field
      fold
        : {B : Set ℓ₂} → ⦃ monoid : Monoid B ⦄
        → (A → B)
        → Container A
        → B

  open Foldable ⦃ ... ⦄

  instance
    fold-list : Foldable {ℓ} List
    Foldable.fold fold-list = ListSummaries.foldList

    fold-bintree : Foldable {ℓ} BinTree
    Foldable.fold fold-bintree f empty = ε
    Foldable.fold fold-bintree f (branch l x r) =
      Foldable.fold fold-bintree f l
        ∙ f x ∙ Foldable.fold fold-bintree f r

    fold-maybe : Foldable {ℓ} Maybe
    Foldable.fold fold-maybe f (just x) = f x
    Foldable.fold fold-maybe f nothing = ε

  size : {A : Set ℓ} {Container : Set ℓ → Set}
    → ⦃ Foldable Container ⦄
    → Container A → ℕ
  size = fold ⦃ monoid = bundle +-0 ⦄ (const 1)

  toList : ∀ {Container} → ⦃ Foldable Container ⦄ → Container A → List A
  toList = fold ⦃ monoid = bundle ++-[] ⦄ (_∷ [])

  module _ ⦃ m₁ : Monoid A ⦄ ⦃ m₂ : Monoid B ⦄ where

    _⊗_ : Op₂ (A × B)
    (fst , snd) ⊗ (fst₁ , snd₁) = ( fst ∙ fst₁ , snd ∙ snd₁ )

    ×-is-monoid : IsMonoid _⊗_ (ε , ε)
    assoc ×-is-monoid (fst , snd) (fst₁ , snd₁) (fst₂ , snd₂)
      rewrite assoc is-monoid fst fst₁ fst₂
      rewrite assoc is-monoid snd snd₁ snd₂ =
        refl
    identityˡ ×-is-monoid (fst , snd)
      rewrite identityˡ is-monoid fst
      rewrite identityˡ is-monoid snd =
        refl
    identityʳ ×-is-monoid (fst , snd)
      rewrite identityʳ is-monoid fst
      rewrite identityʳ is-monoid snd =
        refl

  ⊙ : ⦃ Monoid B ⦄ → Op₂ (A → B)
  ⊙ f g = λ x → f x ∙ g x

  -- pointwise : ⦃ _ : Monoid B ⦄ → IsMonoid (⊙ {A = A}) (const ε)
  -- assoc pointwise = {!!}
  -- identityˡ pointwise = {!!}
  -- identityʳ pointwise = {!!}

module Sandbox-Extensionality where

  f₁ : ℕ → ℕ
  f₁ = (2 +_)

  f₂ : ℕ → ℕ
  f₂ = (_+ 2)

  _≗_
    : {A : Set ℓ₁} {B : A → Set ℓ₂}
    → Rel ((x : A) → B x) _
  _≗_ {A = A} f g = (x : A) → f x ≡ g x

  f₁≗f₂ : f₁ ≗ f₂
  f₁≗f₂ zero = refl
  f₁≗f₂ (suc x) = ≡.cong suc (f₁≗f₂ x)

  module _ {A : Set ℓ₁} {B : A → Set ℓ₂} where
    private
      Fn : Set _
      Fn = (x : A) → B x

    ≗-refl : Reflexive {A = Fn} _≗_
    ≗-refl x = refl

    ≗-sym : Symmetric {A = Fn} _≗_
    ≗-sym x y = sym (x y)

    ≗-trans : Transitive {A = Fn} _≗_
    ≗-trans i≗j j≗k x = trans (i≗j x) (j≗k x)

    ≗-equiv : IsEquivalence {A = Fn} _≗_
    IsPreorder.refl (IsEquivalence.isPreorder ≗-equiv) = ≗-refl
    IsPreorder.trans (IsEquivalence.isPreorder ≗-equiv) = ≗-trans
    IsEquivalence.sym ≗-equiv = ≗-sym

    instance
      ≗-is-equiv = ≗-equiv

  postulate
    fun-ext
      : {A : Set ℓ₁} {B : A → Set ℓ₂}
      → {f g : (x : A) → B x}
      → f ≗ g → f ≡ g

  f₁≡f₂ : f₁ ≡ f₂
  f₁≡f₂ = fun-ext f₁≗f₂

record Setoid (c ℓ : Level) : Set (lsuc (c ⊔ ℓ)) where
  infix 4 _≈_
  field
    Carrier : Set c
    _≈_ : (x y : Carrier) → Set ℓ
    isEquivalence : IsEquivalence _≈_

  open IsEquivalence isEquivalence public

  module Reasoning where
    open Preorder-Reasoning
      (IsEquivalence.isPreorder isEquivalence)
      public

module Setoid-Renaming where
  open Setoid
    hiding (refl; trans; sym)
    renaming (isEquivalence to equiv)
    public
  open IsPreorder
    using ()
    renaming (refl to refl′; trans to trans′)
    public
  open IsEquivalence
    using ()
    renaming (isPreorder to pre; sym to sym′)
    public

module _ where
  open Setoid-Renaming

  prop-setoid : Set ℓ → Setoid ℓ ℓ
  Carrier (prop-setoid A) = A
  _≈_ (prop-setoid A) = _≡_
  refl′ (pre (equiv (prop-setoid A))) = ≡.refl
  trans′ (pre (equiv (prop-setoid A))) = ≡.trans
  sym′ (equiv (prop-setoid A)) = sym

  instance
    prop-setoid-inst : {c : Level} {A : Set c} → Setoid c c
    prop-setoid-inst {A = A} = prop-setoid A

  private variable
    c c₁ c₂ : Level

  module _ (s₁ : Setoid c₁ ℓ₁) (s₂ : Setoid c₂ ℓ₂) where
    private instance
      s₁-equiv = equiv s₁
      s₂-equiv = equiv s₂

    private
      Carrier₁ = s₁ .Carrier
      Carrier₂ = s₂ .Carrier
      _≈₁_ = s₁ ._≈_
      _≈₂_ = s₂ ._≈_

    ×-setoid : Setoid _ _
    Carrier ×-setoid = Carrier₁ × Carrier₂
    (×-setoid ≈ (fst , snd)) (fst₁ , snd₁) = (fst ≈₁ fst₁) × (snd ≈₂ snd₁)
    refl′ (pre (equiv ×-setoid)) = refl , refl
    trans′ (pre (equiv ×-setoid)) (a₁₂ , b₁₂) (a₂₃ , b₂₃) = trans a₁₂ a₂₃ , trans b₁₂ b₂₃
    sym′ (equiv ×-setoid) (fst , snd) = sym fst , sym snd

    data ⊎-Pointwise : Rel (Carrier₁ ⊎ Carrier₂) (ℓ₁ ⊔ ℓ₂ ⊔ c₁ ⊔ c₂) where
      inj₁ : {x y : Carrier₁} → x ≈₁ y → ⊎-Pointwise (inj₁ x) (inj₁ y)
      inj₂ : {x y : Carrier₂} → x ≈₂ y → ⊎-Pointwise (inj₂ x) (inj₂ y)

    ⊎-equiv : IsEquivalence ⊎-Pointwise
    refl′ (pre ⊎-equiv) {inj₁ x} = inj₁ refl
    refl′ (pre ⊎-equiv) {inj₂ y} = inj₂ refl
    trans′ (pre ⊎-equiv) (inj₁ x) (inj₁ x₁) = inj₁ (trans x x₁)
    trans′ (pre ⊎-equiv) (inj₂ x) (inj₂ x₁) = inj₂ (trans x x₁)
    sym′ ⊎-equiv (inj₁ x) = inj₁ (sym x)
    sym′ ⊎-equiv (inj₂ x) = inj₂ (sym x)

    ⊎-setoid : Setoid (c₁ ⊔ c₂) (ℓ₁ ⊔ ℓ₂ ⊔ c₁ ⊔ c₂)
    Carrier ⊎-setoid = Carrier₁ ⊎ Carrier₂
    _≈_ ⊎-setoid = ⊎-Pointwise
    equiv ⊎-setoid = ⊎-equiv

  -- fun-ext : Set ℓ₁ → Set ℓ₂ → Setoid _ _
  -- Carrier (fun-ext A B) = A → B
  -- _≈_ (fun-ext A B) f g = (x : A) → f x ≡ g x
  -- refl′ (pre (equiv (fun-ext A B))) _ = refl
  -- trans′ (pre (equiv (fun-ext A B))) f=g g=h x
  --   rewrite f=g x
  --   rewrite g=h x = refl
  -- sym′ (equiv (fun-ext A B)) f=g x = sym (f=g x)

  -- fun-ext : Set ℓ₁ → Setoid ℓ₂ ℓ → Setoid _ _
  -- Carrier (fun-ext A B) = A → B .Carrier
  -- _≈_ (fun-ext A B) f g = (x : A) → (B ._≈_) (f x) (g x)
  -- refl′ (pre (equiv (fun-ext A B))) _ = refl′ (pre (equiv B))
  -- trans′ (pre (equiv (fun-ext A B))) f=g g=h x =
  --   B .equiv .pre .trans′ (f=g x) (g=h x)
  -- sym′ (equiv (fun-ext A B)) f=g x = B .equiv .sym′ (f=g x)

  module _ {a b : Level} (s₁ : Setoid a ℓ₁) (s₂ : Setoid b ℓ₂) where
    open Setoid s₁ renaming (Carrier to From; _≈_ to _≈₁_)
    open Setoid s₂ renaming (Carrier to To; _≈_ to _≈₂_)

    record Fn : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
      constructor fn
      field
        func : From → To
        cong : {x y : From}
            → x ≈₁ y
            → func x ≈₂ func y

    open Fn

    fun-ext : Setoid _ _
    Carrier fun-ext = Fn
    _≈_ fun-ext f g = {x y : From} → x ≈₁ y → f .func x ≈₂ g .func y
    refl′ (pre (equiv fun-ext)) {f} x=y = f .cong x=y
    trans′ (pre (equiv fun-ext)) ij jk x=y = trans′ ((pre (equiv s₂))) (ij x=y) (jk ((refl′ (pre (equiv s₁)))))
    sym′ (equiv fun-ext) ij x=y = sym′ (equiv s₂) (ij (sym′ (equiv s₁) x=y))

    _⇒_ = fun-ext

record Monoid (c ℓ : Level) : Set (lsuc (c ⊔ ℓ)) where
  field
    setoid : Setoid c ℓ

  open Setoid setoid
    hiding (refl; sym; trans)
    public

  infixl 7 _∙_
  field
    _∙_ : Op₂ Carrier
    ε   : Carrier
    assoc : (x y z : Carrier)
         → (x ∙ y) ∙ z ≈ x ∙ (y ∙ z)
    identityˡ : (x : Carrier) → ε ∙ x ≈ x
    identityʳ : (x : Carrier) → x ∙ ε ≈ x
    ∙-cong : {x y z w : Carrier}
          → x ≈ y → z ≈ w
          → x ∙ z ≈ y ∙ w

module Naive = Sandbox-Naive-Monoids

recover : {_∙_ : Op₂ A} {ε : A} → Naive.IsMonoid _∙_ ε → Monoid _ _
recover {A = A} {_∙_} {ε} x = record
  { setoid = prop-setoid A
  ; _∙_ = _∙_
  ; ε = ε
  ; assoc = assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; ∙-cong = λ { ≡.refl ≡.refl → refl }
  }
  where open Naive.IsMonoid x

∧-true = recover Naive.∧-true
∨-false = recover Naive.∨-false
+-0 = recover Naive.+-0
*-1 = recover Naive.*-1

++-[] <∣>-nothing : {A : Set ℓ} → Monoid _ _
++-[] {A = A} = recover (Naive.++-[] {A = A})
<∣>-nothing {A = A} = recover (Naive.<∣>-nothing {A = A})

module _ {a c : Level} (A : Set a) (mb : Monoid c ℓ) where
  open Monoid
  open Monoid mb
    renaming ( ε to εᴮ; _∙_ to _∙ᴮ_; _≈_ to _≈ᴮ_
             ; setoid to setoidᴮ
             )
  open Fn

  reflᴮ : Reflexive _≈ᴮ_
  reflᴮ = refl′ (pre (equiv setoidᴮ))
    where open Setoid-Renaming

  pointwise : Monoid _ _
  setoid pointwise = prop-setoid A ⇒ setoidᴮ
  func (_∙_ pointwise f g) x = func f x ∙ᴮ func g x
  cong (_∙_ pointwise f g) ≡.refl = ∙-cong mb reflᴮ reflᴮ
  func (ε pointwise) _ = εᴮ
  cong (ε pointwise) ≡.refl = reflᴮ
  assoc pointwise f g h {x} ≡.refl = assoc mb (func f x)
                                              (func g x)
                                              (func h x)
  identityˡ pointwise f {x} ≡.refl = identityˡ mb (func f x)
  identityʳ pointwise f {x} ≡.refl = identityʳ mb (func f x)
  ∙-cong pointwise x=y z=y ≡.refl = ∙-cong mb (x=y refl) (z=y refl)

private variable
  c c₁ c₂ : Level

module _ (m₁ : Monoid c₁ ℓ₁) (m₂ : Monoid c₂ ℓ₂) where
  open Monoid ⦃ ... ⦄

  instance
    _ = m₁
    _ = m₂

  From = m₁ .Monoid.Carrier
  To = m₂ .Monoid.Carrier

  private
    ε₁ = m₁ .Monoid.ε
    ε₂ = m₂ .Monoid.ε
    _∙₁_ = m₁ .Monoid._∙_
    _∙₂_ = m₂ .Monoid._∙_
    _≈₁_ = m₁ .Monoid._≈_
    _≈₂_ = m₂ .Monoid._≈_

  record MonHom (f : From → To)
    : Set (c₁ ⊔ ℓ₁ ⊔ c₂ ⊔ ℓ₂) where
    field
      preserves-ε : f ε₁ ≈₂ ε₂
      preserves-∙ : (a b : From) → f (a ∙₁ b) ≈₂ (f a ∙₂ f b)
      f-cong      : {a b : From} → a ≈₁ b → f a ≈₂ f b

open MonHom

not-hom : MonHom ∧-true ∨-false not
preserves-ε not-hom = refl
preserves-∙ not-hom false b = refl
preserves-∙ not-hom true b = refl
f-cong not-hom ≡.refl = refl

open import Function using (const)

const-hom : MonHom ∧-true ∨-false (const false)
preserves-ε const-hom = refl
preserves-∙ const-hom a b = refl
f-cong const-hom ≡.refl = refl

obviously-untrue : true ≡ false → ⊥
obviously-untrue ()

not-hom′ : MonHom ∨-false ∧-true not
preserves-ε not-hom′ = refl
preserves-∙ not-hom′ false b = refl
preserves-∙ not-hom′ true b = refl
f-cong not-hom′ ≡.refl = refl

¬false-hom′ : ¬ MonHom ∨-false ∧-true (const false)
¬false-hom′ x with preserves-ε x
... | ()

open import Data.List using (List; []; _∷_; _++_)

length : {A : Set} → List A → ℕ
length = Naive.size

length-hom : MonHom (++-[] {A = A}) +-0 length
preserves-ε length-hom = refl
preserves-∙ length-hom [] y = refl
preserves-∙ length-hom (x ∷ x₁) y
  rewrite preserves-∙ length-hom x₁ y = refl
f-cong length-hom ≡.refl = refl

open import Function using (_∘_; id)

open Fn

module _ where
  open Monoid

  ∘-id : Set ℓ → Monoid _ _
  setoid (∘-id A) = prop-setoid A ⇒ prop-setoid A
  _∙_ (∘-id A) f g = fn (func f ∘ func g) λ { ≡.refl → refl }
  ε (∘-id A) = fn id λ { ≡.refl → refl}
  assoc (∘-id A) x y z ≡.refl = refl
  identityˡ (∘-id A) x ≡.refl = refl
  identityʳ (∘-id A) x ≡.refl = refl
  ∙-cong (∘-id A) {x} {y} {z} {w} x=y z=w {a} ≡.refl =
    (func x ∘ func z) a ≡⟨⟩
    func x (func z a) ≡⟨ x=y refl ⟩
    func y (func z a) ≡⟨ ≡.cong (func y) (z=w refl) ⟩
    func y (func w a) ≡⟨⟩
    (func y ∘ func w) a ∎
    where open ≡-Reasoning

module DList where
  open Data.List using (_++_)

  dlist-mon : Set ℓ → Monoid _ _
  dlist-mon A = ∘-id (List A)

  DList : Set ℓ → Set ℓ
  DList A = Monoid.Carrier (dlist-mon A)

  hurry : List A → DList A
  hurry l = fn (l ++_) λ { ≡.refl → refl }

  build : DList A → List A
  build dl = func dl []

  build∘hurry : (x : List A) → build (hurry x) ≡ x
  build∘hurry = Monoid.identityʳ ++-[]

  open MonHom

  hurry-hom : MonHom ++-[] (dlist-mon A) hurry
  preserves-ε hurry-hom ≡.refl = refl
  preserves-∙ hurry-hom a b {c} ≡.refl = Monoid.assoc ++-[] a b c
  f-cong hurry-hom ≡.refl ≡.refl = refl

open import Algebra
  using (Op₂)
  public

open import Data.List
  using (List; []; _∷_; _++_)
  public

open import Data.Maybe
  using (_<∣>_)
  public

open import Function
  using (id; _∘_; const; flip)
  public

open import Relation.Binary.PropositionalEquality
  using (_≗_)
  public
