module STLC where

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


module Syntax where

  infix 9 _∋_ _⊢_
  infixl 10 _◂_

  infixr 20 _`→_

  infixr 20 `λ[_]_
  infixl 21 _`∙_
  infix  22 `_
  infixr 23 s_

  -- using intrinsic typing gaurantees well-typedness

  data Type : Set where
    `⋆   : Type
    _`→_ : Type → Type → Type

  data Ctx : Set where
    ∅   : Ctx
    _◂_ : Ctx → Type → Ctx

  data _∋_ : Ctx → Type → Set where
    z  : ∀ {Γ α}   → (Γ ◂ α ∋ α)
    s_ : ∀ {Γ α β} → (Γ ∋ β) → (Γ ◂ α ∋ β)

  data _⊢_ : Ctx → Type → Set where
    `_     : ∀ {Γ α}     → (Γ ∋ α) → (Γ ⊢ α)
    `⋆     : ∀ {Γ}       → (Γ ⊢ `⋆)
    `λ[_]_ : ∀ {Γ} α {β} → (Γ ◂ α ⊢ β) → (Γ ⊢ α `→ β)
    _`∙_   : ∀ {Γ α β}   → (Γ ⊢ α `→ β) → (Γ ⊢ α) → (Γ ⊢ β)


module Substitution where
  open Syntax

  infixl 22 _[_]
  
  Rename : Ctx → Ctx → Set
  Rename Γ Γ′ = ∀ {α} → (Γ ∋ α) → (Γ′ ∋ α)

  Substitute : Ctx → Ctx → Set
  Substitute Γ Γ′ = ∀ {α} → (Γ ∋ α) → (Γ′ ⊢ α)

  Recontext : Ctx → Ctx → Set
  Recontext Γ Γ′ = ∀ {α} → (Γ ⊢ α) → (Γ′ ⊢ α)

  extend-Rename : ∀ {Γ Γ′ α} → Rename Γ Γ′ → Rename (Γ ◂ α) (Γ′ ◂ α)
  extend-Rename ρ    z  = z
  extend-Rename ρ (s x) = s (ρ x)

  rename : ∀ {Γ Γ′} → Rename Γ Γ′ → Recontext Γ Γ′
  rename ρ (` x)       = ` ρ x
  rename ρ `⋆          = `⋆
  rename ρ (`λ[ α ] b) = `λ[ α ] rename (extend-Rename ρ) b
  rename ρ (f `∙ a)    = rename ρ f `∙ rename ρ a

  extend-Substitute : ∀ {Γ Γ′ α} → Substitute Γ Γ′ → Substitute (Γ ◂ α) (Γ′ ◂ α)
  extend-Substitute σ z = ` z
  extend-Substitute σ (s x) = rename s_ (σ x)

  substitute : ∀ {Γ Γ′} → Substitute Γ Γ′ → Recontext Γ Γ′
  substitute σ (` x)       = σ x
  substitute σ `⋆          = `⋆
  substitute σ (`λ[ α ] b) = `λ[ α ] substitute (extend-Substitute σ) b
  substitute σ (f `∙ a)    = substitute σ f `∙ substitute σ a

  _[_] : ∀ {Γ α β} → (Γ ◂ α ⊢ β) → (Γ ⊢ α) → (Γ ⊢ β)
  _[_] {Γ} {α} {β} b a = substitute σ b where
    σ : ∀ {β} → (Γ ◂ α ∋ β) → (Γ ⊢ β)
    σ    z  = a
    σ (s x) = ` x


module Evaluation where
  open Syntax
  open Substitution

  infix 10 _⇓ _↝_ _⇝_


  -- "_ is a value"
  data _⇓ : ∀ {Γ α} → (Γ ⊢ α) → Set where

    unit : ∀ {Γ} →
      -------------
      `⋆ {Γ} ⇓

    lam : ∀ {Γ α β} {b : Γ ◂ α ⊢ β} →
      --------------------------------
      `λ[ α ] b ⇓


  -- "_ steps to _"
  data _↝_ : ∀ {Γ α} → (Γ ⊢ α) → (Γ ⊢ α) → Set where

    appₗ : ∀ {Γ α β} {f f′ : Γ ⊢ α `→ β} {a : Γ ⊢ α} →
      f ↝ f′ →
      -----------------
      f `∙ a ↝ f′ `∙ a

    appᵣ : ∀ {Γ α β} {f : Γ ⊢ α `→ β} {a a′ : Γ ⊢ α} →
      f ⇓ →
      a ↝ a′ →
      -----------------
      f `∙ a ↝ f `∙ a′

    app : ∀ {Γ α β} {a : Γ ⊢ α} {b : Γ ◂ α ⊢ β} →
      a ⇓ →
      -----
      (`λ[ α ] b) `∙ a ↝ b [ a ]


  -- "_ reduces to _"
  data _⇝_ : ∀ {Γ α} → (Γ ⊢ α) → (Γ ⊢ α) → Set where

    end : ∀ {Γ α} {a : Γ ⊢ α} →
      -------
      a ⇝ a

    step : ∀ {Γ α} {a a′ a″ : Γ ⊢ α} →
      a  ↝ a′ →
      a′ ⇝ a″ →
      -----------
      a  ⇝ a″


  data Progress {α} (a : ∅ ⊢ α) : Set where
    evaluated : a ⇓              → Progress a
    reduces   : ∃[ a′ ] (a ↝ a′) → Progress a

  progress : ∀ {α} (a : ∅ ⊢ α) → Progress a
  progress `⋆                  = evaluated unit
  progress (`λ[ α ] b)         = evaluated lam
  progress (f `∙ a)         with progress f
  progress (f `∙ a)            | evaluated lam    with progress a
  progress ((`λ[ _ ] b) `∙ a)  | evaluated lam       | evaluated a⇓        = reduces (b [ a ] , app a⇓)
  progress (f `∙ a)            | evaluated lam       | reduces (a′ , a↝a′) = reduces (f `∙ a′ , appᵣ lam a↝a′)
  progress (f `∙ a)            | reduces (f′ , f↝f′) = reduces (f′ `∙ a , appₗ f↝f′)


  evaluate : ∀ {α} (a : ∅ ⊢ α) → ℕ → Result (λ a → Σ[ a′ ∈ ∅ ⊢ α ] (a ⇝ a′ × a′ ⇓)) a
  evaluate _ zero       = out-of-gas
  evaluate a (suc g) with progress a
  evaluate a (suc g)    | evaluated a⇓ = terminated (a , end , a⇓)
  evaluate a (suc g)    | reduces (a′ , a↝a′) with evaluate a′ g
  evaluate a (suc g)    | reduces (a′ , a↝a′)    | terminated (a″ , a′⇝a″ , a″⇓) = terminated (a″ , step a↝a′ a′⇝a″ , a″⇓)
  evaluate a (suc g)    | reduces (a′ , a↝a′)    | out-of-gas                    = out-of-gas


module Examples where
  open Syntax
  open Evaluation

  -- beta-reduction
  _ : evaluate ((`λ[ `⋆ ] ` z) `∙ `⋆) 100 ≡
      terminated (`⋆ , _ , _)
  _ = refl

  -- identity function
  id : ∀ {α} → (∅ ⊢ α `→ α)
  id {α} = `λ[ α ] ` z

  -- application
  _ : evaluate ((`λ[ `⋆ `→ `⋆ ] (`λ[ `⋆ ] ` s z `∙ ` z)) `∙ id `∙ `⋆) 100 ≡
      terminated (`⋆ , _ , _)
  _ = refl
