module Pi where

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Data.Nat as Nat
open import Data.Fin as Fin
open import Data.Product as Product renaming (_,_ to _&_)
open import Data.Sum as Sum
open import Data.Unit as Unit

--
-- Infixity
--

infix  10 _∋_⦂_ _⊢_⦂_
infixl 11 _,_
infixl 16 _`∙_ Π_⇒_
infixl 20 _[_]
infix  21 `_

--
-- Syntax
--

Var : ℕ → Set
Var n = Fin n

data Term : ℕ → Set where
  `_    : ∀ {n} → Var n  → Term n
  `Π_⇒_ : ∀ {n} → Term n → Term (suc n) → Term n
  _`∙_  : ∀ {n} → Term n → Term n → Term n
  `⋆    : ∀ {n} → Term n

coerce : ∀ {m} {n} → m ≡ n → Term m → Term n
coerce refl a = a


--
-- Context
--

data Ctx : ℕ → Set where
  ∅   : ∀ {n} → Ctx n
  _,_ : ∀ {n} → Ctx n → Term n → Ctx (suc n)


--
-- Renaming
--

Ren : ℕ → ℕ → Set
Ren m n = Var m → Var n

renWeaken : ∀ {m n} → Ren m (n Nat.+ m)
renWeaken {n = n} x = raise n x

--
-- Substitution
--

Sub : ℕ → ℕ → Set
Sub m n = Var m → Term n

subWeaken : ∀ {m n} → Sub m (n Nat.+ m)
subWeaken {n = n} x = ` renWeaken x

postulate
  n+sm≡sn+m : ∀ m n → n Nat.+ suc m ≡ suc (n Nat.+ m)
  sn≡n+1 : ∀ n → suc n ≡ n Nat.+ 1

weaken : ∀ {m} {n} → Term m → Term (n Nat.+ m)
weaken (` x)         = ` renWeaken x
weaken {m} {n} (`Π α ⇒ b) = `Π (weaken α) ⇒ (coerce (n+sm≡sn+m m n) (weaken {suc m} {n} b))
weaken (f `∙ a)         = weaken f `∙ weaken a
weaken `⋆               = `⋆

substitute : ∀ {n} → Term n → Sub (suc n) n
substitute {n} a x with splitAt n {1} (cast (sn≡n+1 n) x)
... | inj₁ y = ` y
... | inj₂ _ = a

_[_] : ∀ {n} → Term (suc n) → Term n → Term n
` x        [ a ] = substitute a x
(`Π α ⇒ b) [ a ] = `Π (α [ a ]) ⇒ (b [ weaken a ])
(f `∙ a)   [ b ] = f [ b ] `∙ a [ b ]
`⋆         [ a ] = `⋆


--
-- Typing
--

data _∋_⦂_ : ∀ {n} → Ctx n → Var n → Term n → Set where
  zero : ∀ {n} {Γ : Ctx n} {α}     → (Γ , α) ∋ zero ⦂ weaken α
  suc  : ∀ {n} {Γ : Ctx n} {α β x} → Γ ∋ x ⦂ β → Γ , α ∋ suc x ⦂ weaken β

data _⊢_⦂_ : ∀ {n} → Ctx n → Term n → Term n → Set where

  var : ∀ {n} {Γ : Ctx n} {x α} →
    Γ ∋ x ⦂ α →
    ------------
    Γ ⊢ ` x ⦂ α

  Π : ∀ {n} {Γ : Ctx n} {α β b} →
    Γ     ⊢ α ⦂ `⋆ →
    Γ , α ⊢ b ⦂ β →
    ----------------
    Γ     ⊢ `Π α ⇒ b ⦂ `Π α ⇒ β

  ∙ : ∀ {n} {Γ : Ctx n} {α β f a} →
    Γ     ⊢ α ⦂ `⋆ →
    Γ , α ⊢ β ⦂ `⋆ →
    Γ     ⊢ f ⦂ `Π α ⇒ β →
    Γ     ⊢ a ⦂ α →
    ----------------
    Γ     ⊢ f `∙ a ⦂ (β [ a ])

  Π⋆ : ∀ {n} {Γ : Ctx n} {α β} →
    Γ ⊢ β ⦂ `⋆ →
    ---------------
    Γ ⊢ `Π α ⇒ weaken β ⦂ `⋆

  ⋆ : ∀ {n} {Γ : Ctx n} →
    ------------
    Γ ⊢ `⋆ ⦂ `⋆

weaken-⊢ : ∀ {n} {Γ : Ctx n} {a α β} →
  Γ ⊢ a ⦂ α →
  ------------
  Γ , β ⊢ weaken a ⦂ weaken α
weaken-⊢ {n} {Γ} {.(` _)} {α} {β} (var Γ∋x⦂α) = var (suc Γ∋x⦂α)
weaken-⊢ {n} {Γ} {.(`Π _ ⇒ _)} {.(`Π _ ⇒ _)} {β} (Π Γ,α⊢b⦂β Γ⊢α⦂⋆) = {!!}
weaken-⊢ {n} {Γ} {.(_ `∙ _)} {.(_ [ _ ])} {β} (∙ h h₁ h₂ h₃) = {!!}
weaken-⊢ {n} {Γ} {.(`Π _ ⇒ weaken _)} {.`⋆} {β} (Π⋆ h) = {!!}
weaken-⊢ {n} {Γ} {.`⋆} {.`⋆} {β} ⋆ = {!!}

--
-- Examples
--

-- note that there are no concrete base types

-- polymorphic identity
-- - term
`id : Term 0
`id = `Π `⋆ ⇒ (`Π (` zero) ⇒ (` zero))
-- - signature
`id-sig : Term 0
`id-sig = `Π `⋆ ⇒ (`Π (` zero) ⇒ (` suc zero))
-- - judgement
`id-judge : ∅ ⊢ `id ⦂ `id-sig
`id-judge = Π ⋆ (Π (var zero) (var zero))
-- - judgement sig
`id-sig-judge : ∅ ⊢ `id-sig ⦂ `⋆
`id-sig-judge = {!Π⋆!}

-- `id∙id : ∅ ⊢ `id `∙ `id-sig `∙ `id ⦂ `id-sig
-- `id∙id = ∙ `id-sig-judge {!!} {!!} `id-judge
