module Lambda where

open import Relation.Binary.PropositionalEquality hiding (subst)
open import Relation.Nullary
open import Data.Nat as Nat
open import Data.Nat.Properties
open import Data.Fin as Fin
open import Data.Product as Product
open import Data.Sum as Sum
open import Data.Maybe as Maybe

--
-- Infixity
--

infixr 20 `λ_
infixl 21 _`∙_
infix  22 `_

--
-- Syntax
--

∋_ : ℕ → Set
∋ n = Fin n

data ⊢_ : ℕ → Set where
  `_   : ∀ {n} → ∋ n → ⊢ n -- variable
  `⋆   : ∀ {n} → ⊢ n -- unit
  `λ_  : ∀ {n} → ⊢ suc n → ⊢ n -- abstraction
  _`∙_ : ∀ {n} → ⊢ n → ⊢ n → ⊢ n -- application

weaken : ∀ {n} → ⊢ n → ⊢ suc n
weaken (` x)    = ` suc x
weaken  `⋆      = `⋆
weaken (`λ a)   = `λ weaken a
weaken (f `∙ a) = weaken f `∙ weaken a

--
-- Evaluation
--

module Normalization where
  infix 10 ⊢_⇓ ⊢_↓

  data ⊢_⇓ {n} : ⊢ n → Set
  data ⊢_↓ {n} : ⊢ n → Set

  data ⊢_⇓ {n} where
    unit : ⊢ `⋆ ⇓
    lam  : ∀ {b : ⊢ suc n} → ⊢ `λ b ⇓
    neu  : ∀ {a : ⊢ n}     → ⊢ a ↓ → ⊢ a ⇓

  data ⊢_↓ {n} where
    var  : ∀ {x : ∋ n}   → ⊢ ` x ↓
    app  : ∀ {f a : ⊢ n} → ⊢ f ↓ → ⊢ a ⇓ → ⊢ f `∙ a ↓

  weaken-↓ : ∀ {n} {a : ⊢ n} → ⊢ a ↓ → ⊢ weaken a ↓
  weaken-⇓ : ∀ {n} {a : ⊢ n} → ⊢ a ⇓ → ⊢ weaken a ⇓

  weaken-⇓ {a = ` x}    _ = neu var
  weaken-⇓ {a = `⋆}     _ = unit
  weaken-⇓ {a = `λ b}   _ = lam
  weaken-⇓ {a = f `∙ a} (neu ⊢fa↓) = neu (weaken-↓ ⊢fa↓)

  weaken-↓ {a = ` x} var = var
  weaken-↓ {a = f `∙ a} (app f↓ a⇓) = app (weaken-↓ f↓) (weaken-⇓ a⇓)

  {-# TERMINATING #-}
  norm  : ∀ {n} → (a : ⊢ n) → Maybe (Σ[ a′ ∈ ⊢ n ] (⊢ a′ ⇓)) 
  apply : ∀ {n} → (f⇓ : Σ[ f ∈ ⊢ n ] (⊢ f ⇓)) → (a⇓ : Σ[ a ∈ ⊢ n ] (⊢ a ⇓)) → Maybe (Σ[ fa ∈ ⊢ n ] (⊢ fa ⇓))
  subst : ∀ {n} (b : ⊢ suc n) (a⇓ : Σ[ a ∈ ⊢ n ] (⊢ a ⇓)) → ⊢ n

  norm (` x)  = just (` x , (neu var))
  norm  `⋆    = just (`⋆ , unit)
  norm (`λ a) = just (`λ a , lam)
  norm (f `∙ a) with norm f  | norm a
  norm (f `∙ a) | just f⇓ | just a⇓ = apply f⇓ a⇓
  norm (f `∙ a) | just f⇓ | nothing = nothing
  norm (f `∙ a) | nothing | just a⇓ = nothing
  norm (f `∙ a) | nothing | nothing = nothing  

  apply (.`⋆ , unit) a⇓ = nothing
  apply (`λ b , lam) a⇓ = norm (subst b a⇓)
  apply (f , neu ⊢f↓) (a , ⊢a⇓) = just ((f `∙ a) , neu (app ⊢f↓ ⊢a⇓))

  subst {n} (` x)    a⇓ with Fin.splitAt n {1} (cast (sym (+-comm n 1)) x)
  subst {_} (` x)    a⇓    | inj₁ y = ` y
  subst {_} (` x)    a⇓    | inj₂ _ = proj₁ a⇓
  subst      `⋆      a⇓ = `⋆
  subst     (`λ b)   a⇓ = `λ (subst b (weaken (proj₁ a⇓) , weaken-⇓ (proj₂ a⇓)))
  subst     (f `∙ c) a⇓ = subst f a⇓ `∙ subst c a⇓


module Examples where

  open Normalization

  tm1 : ⊢ 0
  tm1 = `λ (` zero)

  nm1 : Maybe.map proj₁ (norm tm1) ≡ just tm1
  nm1 = refl

  tm2 : ⊢ 0
  tm2 = (`λ (`λ ((` suc zero) `∙ (` zero)))) `∙ (`λ ` zero) `∙ `⋆

  nm2 : Maybe.map proj₁ (norm tm2) ≡ just `⋆
  nm2 = refl
