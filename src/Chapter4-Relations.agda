module Chapter4-Relations where

open import Chapter1-Agda
  using (Bool; false; true; not; _×_)

open import Chapter2-Numbers
  using (ℕ; zero; suc; _+_)

open import Chapter3-Proofs

_ : Set₁
_ = Set

_ : Set₂
_ = Set₁

open import Agda.Primitive
  using (Level; _⊔_; lzero; lsuc)

module Playground-Level where
  data Maybe₀ (A : Set) : Set where
    just₀ : A → Maybe₀ A
    nothing₀ : Maybe₀ A


  data Maybe₁ {ℓ : Level} (A : Set ℓ) : Set ℓ where
    just₁ : A → Maybe₁ A
    nothing₁ : Maybe₁ A

  _ : Maybe₁ Set
  _ = just₁ ℕ

  private variable
    ℓ : Level

  data Maybe₂ (A : Set ℓ) : Set ℓ where
    just₂ : A -> Maybe₂ A
    nothing₂ : Maybe₂ A

private variable
  ℓ ℓ₁ ℓ₂ a b c : Level
  A : Set a
  B : Set b
  C : Set c


module Definition-DependentPair where
  open Chapter3-Proofs

  record Σ (A : Set ℓ₁) (B : A → Set ℓ₂)
      : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
    constructor _,_
    field
      proj₁ : A
      proj₂ : B proj₁

  ∃n,n+1≡5 : Σ ℕ (λ x → x + 1 ≡ 5)
  ∃n,n+1≡5 = 4 , PropEq.refl

open import Data.Product
  using (Σ; _,_)

module Sandbox-Relations where
  REL : Set a → Set b → (ℓ : Level) → Set (a ⊔ b ⊔ lsuc ℓ)
  REL A B ℓ = A → B → Set ℓ

  data Unrelated : REL A B lzero where

  data Related {A : Set a} {B : Set b} : REL A B (lsuc a ⊔ lsuc b) where
    related : {a : A} {b : B} → Related a b

  data Foo : Set where
    f1 f2 f3 : Foo

  data Bar : Set where
    b1 b2 b3 : Bar

  data FooBar : REL Foo Bar lzero where
    f2-b2  : FooBar f2 b2
    f2-b2′ : FooBar f2 b2
    f2-b   : (b : Bar) → FooBar f2 b
    f3-b2  : FooBar f3 b2

  data _maps_↦_ {A : Set a} {B : Set b} (f : A → B) : REL A B (lsuc a) where
    app : {x : A} → f maps x ↦ f x

  _ : not maps false ↦ true
  _ = app

  _ : not maps true ↦ false
  _ = app

  Functional : REL A B ℓ → Set _
  Functional {A = A} {B = B} _~_
    = {x : A} {y z : B}
    → x ~ y → x ~ z
    → y ≡ z

  Total : REL A B ℓ → Set _
  Total {A = A} {B = B} _~_
    = (x : A) → Σ B (x ~_)

  relToFn : (_~_ : REL A B ℓ)
          → Functional _~_
          → Total _~_
          → A → B
  relToFn _~_ _ total x
    with total x
  ... | y , _ = y

  Rel : Set a → (ℓ : Level) → Set (a ⊔ lsuc ℓ)
  Rel A ℓ = REL A A ℓ

  data _≡′_ {A : Set a} : Rel A a where
    refl : {x : A} → x ≡′ x

  Reflexive : Rel A ℓ → Set _
  Reflexive {A = A} _~_ = {x : A} → x ~ x

  Symmetric : Rel A ℓ → Set _
  Symmetric {A = A} _~_
    = {x y : A} → x ~ y → y ~ x

  Transitivity : Rel A ℓ → Set _
  Transitivity {A = A} _~_
    = {x y z : A} → x ~ y → y ~ z → x ~ z

open import Relation.Binary
  using (Rel; Reflexive; Transitive; Symmetric)

module Naive-≤₁ where
  data _≤_ : Rel ℕ lzero where
    lte : (a b : ℕ) → a ≤ a + b
  infix 4 _≤_

  _ : 2 ≤ 5
  _ = lte 2 3

  suc-mono : {x y : ℕ} → x ≤ y → suc x ≤ suc y
  suc-mono (lte x b) = lte (suc x) b

  ≤-refl : Reflexive _≤_
  ≤-refl {zero} = lte zero zero
  ≤-refl {suc x}
    with ≤-refl {x}
  ... | x≤x = suc-mono x≤x

  open Chapter3-Proofs
    using (+-identityʳ)

  subst : {x y : A} → (P : A → Set ℓ) → x ≡ y → P x → P y
  subst _ PropEq.refl px = px

  ≤-refl′ : Reflexive _≤_
  ≤-refl′ {x} = subst (λ ϕ → x ≤ ϕ) (+-identityʳ x) (lte x 0)

module Definition-LessThanOrEqualTo where
  data _≤_ : Rel ℕ lzero where
    z≤n : {n : ℕ} → zero ≤ n
    s≤s : {m n : ℕ} → m ≤ n → suc m ≤ suc n
  infix 4 _≤_

open import Data.Nat
  using (_≤_; z≤n; s≤s)

module Sandbox-≤ where
  _ : 2 ≤ 5
  _ = s≤s (s≤s z≤n)

  suc-mono : {x y : ℕ} → x ≤ y → suc x ≤ suc y
  suc-mono x≤y = s≤s x≤y

  ≤-refl : Reflexive _≤_
  ≤-refl {zero} = z≤n
  ≤-refl {suc x} = s≤s ≤-refl

  ≤-trans : {x y z : ℕ} → x ≤ y → y ≤ z → x ≤ z
  ≤-trans z≤n z≤n = z≤n
  ≤-trans z≤n y≤z = z≤n
  ≤-trans (s≤s x≤y) (s≤s y≤z) = s≤s (≤-trans x≤y y≤z)

module Sandbox-Preorders where
  open Sandbox-≤

  record IsPreorder {A : Set a} (_~_ : Rel A ℓ) : Set (a ⊔ ℓ) where
    constructor MkPreorder
    field
      refl  : Reflexive _~_
      trans : Transitive _~_

  ≤-preorder : IsPreorder _≤_
  ≤-preorder = MkPreorder ≤-refl ≤-trans

  ≡-preorder : IsPreorder (_≡_ {A = A})
  ≡-preorder = MkPreorder PropEq.refl PropEq.trans

  open Sandbox-Relations using (Related; related)

  Related-preorder : IsPreorder (Related { A = A })
  Related-preorder = MkPreorder related λ _ _ → related

  module Preorder-Reasoning
    {_~_ : Rel A ℓ} (~-preorder : IsPreorder _~_) where

    open IsPreorder ~-preorder public

    begin_ : {x y : A} → x ~ y → x ~ y
    begin_ x~y = x~y

    infix 1 begin_

    _∎ : (x : A) → x ~ x
    _∎ x = refl

    infix 3 _∎

    _≡⟨⟩_ : (x : A) → {y : A} → x ~ y → x ~ y
    x ≡⟨⟩ p = p

    infixr 2 _≡⟨⟩_

    _≈⟨_⟩_ : (x : A) → ∀ {y z} → x ~ y → y ~ z → x ~ z
    _ ≈⟨ x~y ⟩ y~z = trans x~y y~z

    infixr 2 _≈⟨_⟩_

    _≡⟨_⟩_ : (x : A) → ∀ {y z} → x ≡ y → y ~ z → x ~ z
    _ ≡⟨ PropEq.refl ⟩ y~z = y~z

    infixr 2 _≡⟨_⟩_

  n≤1+n : (n : ℕ) → n ≤ 1 + n
  n≤1+n zero = z≤n
  n≤1+n (suc n) = s≤s (n≤1+n n)

  open Chapter3-Proofs using (+-comm)

  n≤n+1 : (n : ℕ) → n ≤ n + 1
  n≤n+1 n =
    begin
      n ≈⟨ n≤1+n n ⟩
      1 + n ≡⟨ +-comm 1 n ⟩
      n + 1
    ∎
    where open Preorder-Reasoning ≤-preorder

  module ≤-Reasoning where
    open Preorder-Reasoning ≤-preorder
      renaming (_≈⟨_⟩_ to _≤⟨_⟩_)
      public

  n≤n+1′ : (n : ℕ) → n ≤ n + 1
  n≤n+1′ n =
    begin
      n
    ≤⟨ n≤1+n n ⟩
      1 + n
    ≡⟨ +-comm 1 n ⟩
      n + 1
    ∎
    where open ≤-Reasoning

  module Reachability {V : Set ℓ₁} (_⇒_ : Rel V ℓ₂) where

    private variable
      v v₁ v₂ v₃ : V

    data Path : Rel V (ℓ₁ ⊔ ℓ₂) where
      ↪_ : v₁ ⇒ v₂ → Path v₁ v₂
      here : Path v v
      connect : Path v₁ v₂ → Path v₂ v₃ → Path v₁ v₃

    open Path

    Path-preorder : IsPreorder Path
    IsPreorder.refl Path-preorder = here
    IsPreorder.trans  Path-preorder = connect

  module Example-AboutABoy where
    data Person : Set where
      ellie fiona marcus rachel susie will : Person

    private variable
      p₁ p₂ : Person

    data _IsFriendsWith_ : Rel Person lzero where
      marcus-will : marcus IsFriendsWith will
      marcus-fiona : marcus IsFriendsWith fiona
      fiona-susie : fiona IsFriendsWith susie
      sym : p₁ IsFriendsWith p₂ → p₂ IsFriendsWith p₁

    data _IsInterestedIn_ : Rel Person lzero where
      marcus-ellie : marcus IsInterestedIn ellie
      will-rachel  : will IsInterestedIn rachel
      rachel-will  : rachel IsInterestedIn will
      susie-will   : susie IsInterestedIn will

    data SocialTie : Rel Person lzero where
      friendship : p₁ IsFriendsWith p₂ → SocialTie p₁ p₂
      interest   : p₁ IsInterestedIn p₂ → SocialTie p₁ p₂

    open Reachability SocialTie

    will-fiona : Path will fiona
    will-fiona =
      begin
        will
      ≈⟨ ↪ friendship (sym marcus-will) ⟩
        marcus
      ≈⟨ ↪ friendship marcus-fiona ⟩
        fiona
      ∎
      where open Preorder-Reasoning Path-preorder

    rachel-ellie : Path rachel ellie
    rachel-ellie =
      begin
        rachel
      ≈⟨ ↪ interest rachel-will ⟩
        will
      ≈⟨ ↪ friendship (sym marcus-will) ⟩
        marcus
      ≈⟨ ↪ interest marcus-ellie ⟩
        ellie
      ∎
      where open Preorder-Reasoning Path-preorder

  ≤-antisym : {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
  ≤-antisym z≤n z≤n = PropEq.refl
  ≤-antisym (s≤s x) (s≤s x₁) = PropEq.cong suc (≤-antisym x x₁)

  Antisymmetric : Rel A ℓ₁ → Rel A ℓ₂ → Set _
  Antisymmetric _≈_ _≤_ = ∀ {x y} → x ≤ y → y ≤ x → x ≈ y

  _ : Antisymmetric _≡_ _≤_
  _ = ≤-antisym

  module _ {a ℓ : Level} {A : Set a} (_~_ : Rel A ℓ) where

    record IsEquivalence : Set (a ⊔ ℓ) where
      field
        isPreorder : IsPreorder _~_
        sym        : Symmetric _~_

      open IsPreorder isPreorder public

    record IsPartialOrder : Set (a ⊔ ℓ) where
      field
        isPreorder : IsPreorder _~_
        antisym    : Antisymmetric _≡_ _~_

      open IsPreorder isPreorder public

  ≡-equiv : IsEquivalence (_≡_ {A = A})
  IsEquivalence.isPreorder ≡-equiv = MkPreorder PropEq.refl PropEq.trans
  IsEquivalence.sym ≡-equiv = PropEq.sym

  ≤-poset : IsPartialOrder _≤_
  IsPartialOrder.isPreorder ≤-poset = MkPreorder ≤-refl ≤-trans
  IsPartialOrder.antisym ≤-poset = ≤-antisym

  _<_ : Rel ℕ lzero
  m < n = m ≤ suc n

  infix 4 _<_

open import Agda.Primitive
  using (Level; _⊔_; lzero; lsuc)
  public

open import Data.Product
  using (Σ; _,_)
  public

open import Relation.Binary
  using (Rel; REL; Transitive; Reflexive; Symmetric; Antisymmetric)
  public

open import Relation.Binary.PropositionalEquality
  using (subst)
  public

open import Data.Nat
  using (_≤_; z≤n; s≤s; _<_)
  public

open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-antisym; n≤1+n; module ≤-Reasoning)
  public

open Sandbox-Preorders
  using ( IsPreorder; IsEquivalence; IsPartialOrder
        ; module Preorder-Reasoning
        ; ≡-preorder; ≡-equiv
        ; ≤-preorder; ≤-poset
        )
  public
