module Lambda where

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Data.Nat as Nat
open import Data.Nat.Properties
open import Data.Fin as Fin
open import Data.Product as Product
open import Data.Sum as Sum
open import Data.Maybe as Maybe


data Result {A : Set} (P : A → Set) (a : A) : Set where
  terminated : P a → Result P a
  out-of-gas : Result P a
  maltyped   : Result P a
  

module Syntax where

  infixr 20 `λ_
  infixl 21 _`∙_
  infix  22 `_

  -- using DeBruijn indices gaurantees well-formedness

  ∋_ : ℕ → Set
  ∋ n = Fin n

  data ⊢_ : ℕ → Set where
    `_   : ∀ {n} → ∋ n → ⊢ n -- variable
    `⋆   : ∀ {n} → ⊢ n -- unit
    `λ_  : ∀ {n} → ⊢ suc n → ⊢ n -- abstraction
    _`∙_ : ∀ {n} → ⊢ n → ⊢ n → ⊢ n -- application


module Substitution where
  open Syntax

  infixl 22 _[_]

  Rename : ℕ → ℕ → Set
  Rename m n = ∋ m → ∋ n

  Substitute : ℕ → ℕ → Set
  Substitute m n = ∋ m → ⊢ n

  Recontext : ℕ → ℕ → Set
  Recontext m n = ⊢ m → ⊢ n

  extend-Rename : ∀ {m n} → Rename m n → Rename (suc m) (suc n)
  extend-Rename ρ  zero   = zero
  extend-Rename ρ (suc x) = suc (ρ x)

  rename : ∀ {m n} → Rename m n → Recontext m n
  rename ρ (` x)    = ` ρ x
  rename ρ  `⋆      = `⋆
  rename ρ (`λ a)   = `λ rename (extend-Rename ρ) a
  rename ρ (f `∙ a) = rename ρ f `∙ rename ρ a

  extend-Substitute : ∀ {m n} → Substitute m n → Substitute (suc m) (suc n)
  extend-Substitute σ  zero   = ` zero
  extend-Substitute σ (suc x) = rename suc (σ x)

  substitute : ∀ {m n} → Substitute m n → Recontext m n
  substitute σ (` x)    = σ x
  substitute σ `⋆       = `⋆
  substitute σ (`λ a)   = `λ substitute (extend-Substitute σ) a
  substitute σ (f `∙ a) = substitute σ f `∙ substitute σ a

  _[_] : ∀ {n} → ⊢ suc n → ⊢ n → ⊢ n
  _[_] {n} b a = substitute σ b where
    σ : ∋ suc n → ⊢ n
    σ  zero   = a
    σ (suc x) = ` x



module Evaluation where
  open Syntax
  open Substitution

  infix 10 _⇓ _↝_ _⇝_

  -- "_ is a value"
  data _⇓ : ∀ {n} → ⊢ n → Set where

    unit : ∀ {n} →
      ---------
      `⋆ {n} ⇓

    lam : ∀ {n} {b : ⊢ suc n} →
      -------
      `λ b ⇓

  -- "_ steps to _"
  data _↝_ : ∀ {n} → ⊢ n → ⊢ n → Set where

    appₗ : ∀ {n} {f f′ : ⊢ n} {a : ⊢ n} →
      f ↝ f′ →
      -----------------
      f `∙ a ↝ f′ `∙ a

    appᵣ : ∀ {n} {f : ⊢ n} {a a′ : ⊢ n} →
      a ↝ a′ →
      -----------------
      f `∙ a ↝ f `∙ a′

    app : ∀ {n} {a : ⊢ n} {b : ⊢ suc n} →
      a ⇓ →
      ----------------------
      (`λ b) `∙ a ↝ b [ a ]


  -- "_ reduces to _"
  data _⇝_ : ∀ {n} → ⊢ n → ⊢ n → Set where

    end : ∀ {n} {a : ⊢ n} →
      a ⇝ a

    step : ∀ {n} {a a′ a″ : ⊢ n} →
      a  ↝ a′ →
      a′ ⇝ a″ →
      -----------
      a ⇝ a″


  data Progress (a : ⊢ 0) : Set where
    evaluated : a ⇓ → Progress a
    reduces   : ∃[ a′ ] (a ↝ a′) → Progress a
    maltyped  : Progress a


  progress : ∀ (a : ⊢ 0) → Progress a
  progress `⋆            = evaluated unit
  progress (`λ a)        = evaluated lam
  progress (f `∙ a)   with progress f
  progress (f `∙ a)      | evaluated f⇓     with progress a
  progress (.`⋆ `∙ a)    | evaluated unit      | evaluated a⇓        = maltyped
  progress ((`λ b) `∙ a) | evaluated lam       | evaluated a⇓        = reduces (b [ a ] , app a⇓)
  progress (f `∙ a)      | evaluated f⇓        | reduces (a′ , a↝a′) = reduces (f `∙ a′ , appᵣ a↝a′)
  progress (f `∙ a)      | evaluated f⇓        | maltyped            = maltyped
  progress (f `∙ a)      | reduces (f′ , f↝f′) = reduces (f′ `∙ a , appₗ f↝f′)
  progress (f `∙ a)      | maltyped            = maltyped


  evaluate : ∀ (a : ⊢ 0) → ℕ → Result (λ a → ∃[ a′ ] (a ⇝ a′ × a′ ⇓)) a
  evaluate a zero       = out-of-gas
  evaluate a (suc g) with progress a
  evaluate a (suc g)    | evaluated a⇓           = terminated (a , end , a⇓)
  evaluate a (suc g)    | reduces (a′ , a↝a′) with evaluate a′ g
  evaluate a (suc g)    | reduces (a′ , a↝a′)    | terminated (a″ , a′⇝a″ , a″⇓) = terminated (a″ , step a↝a′ a′⇝a″ , a″⇓)
  evaluate a (suc g)    | reduces (a′ , a↝a′)    | out-of-gas                     = out-of-gas
  evaluate a (suc g)    | reduces (a′ , a↝a′)    | maltyped                       = maltyped
  evaluate a (suc g)    | maltyped               = maltyped


module Examples where
  open Syntax
  open Evaluation

  -- beta-reduction
  _ : evaluate ((`λ ` zero) `∙ `⋆) 100 ≡
      terminated (`⋆ , _ , _)
  _ = refl

  -- y-combinator
  yc : ⊢ 0
  yc = `λ ((`λ (` suc zero) `∙ ((` zero) `∙ (` zero))) `∙ (`λ (` suc zero) `∙ ((` zero) `∙ (` zero))))

  id : ⊢ 0
  id = `λ (` zero)

  -- Church numerals
  
  ch : ℕ → ⊢ 0
  ch n = `λ `λ compositions (` suc zero) n (` zero) where
    compositions : ⊢ 2 → ℕ → ⊢ 2 → ⊢ 2
    compositions f zero x    = x
    compositions f (suc n) x = f `∙ compositions f n x

  zeroCh : ⊢ 0
  zeroCh = ch 0

  sucCh : ⊢ 0
  sucCh = `λ `λ `λ (` suc zero) `∙ ((` suc (suc zero)) `∙ (` zero))

  +Ch : ⊢ 0
  +Ch = `λ `λ `λ `λ ((` suc (suc (suc zero))) `∙ (` suc zero) `∙ ((` suc (suc zero)) `∙ (` suc zero) `∙ (` zero)))

  _ : evaluate (+Ch `∙ ch 10 `∙ ch 5 `∙ id `∙ `⋆) 1000 ≡
      terminated (`⋆ , _ , _)
  _ = refl
