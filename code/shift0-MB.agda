-- Type system for shift0/reset0 (MB)
-- Based on Materzok & Biernacki [ICFP 2011]
-- The version where σ in (ABS) and σ₁ and σ₂ in (SHIFT0) cannot be ε.

module shift0-MB where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Bool using (true; false; if_then_else_) renaming (Bool to 𝔹)
open import Data.String using (String)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning

-- Types
data Ty : Set

data Ann : Set

data Ty where
  Nat   : Ty
  Bool  : Ty
  _⇒_,[_,_]_,_ : Ty → Ty → Ty → Ann → Ty → Ann → Ty

data Ann where
  ε        : Ann
  [_,_]_,_ : Ty → Ann → Ty → Ann → Ann

-- Terms
-- e : Exp var τ ([ α , a ] β , b) means that e
--  * has type τ
--  * requires a context that yields a computation of type α and effect a
--  * eventually returns a computation of type β and effect b
data Exp  (var : Ty → Set) : Ty → Ann → Set where
  Var    : {τ α : Ty} {a : Ann} →
           var τ → Exp var τ ([ α , a ] α , a)
  Num    : {α : Ty} {a : Ann} →
           ℕ → Exp var Nat ([ α , a ] α , a)
  Bol    : {α : Ty} {a : Ann} →
           𝔹 → Exp var Bool ([ α , a ] α , a)
  Lam    : {τ₁ τ₂ τ₃ τ₄ β : Ty} {a₃ a₄ b : Ann} →
           (var τ₁ → Exp var τ₂ ([ τ₃ , a₃ ] τ₄ , a₄)) →
           Exp var (τ₁ ⇒ τ₂ ,[ τ₃ , a₃ ] τ₄ , a₄) ([ β , b ] β , b)
  App    : {τ₁ τ₂ α β γ δ : Ty} {a b c d : Ann} →
           Exp var (τ₁ ⇒ τ₂ ,[ α , a ] β , b) ([ γ , c ] δ , d) →
           Exp var τ₁ ([ β , b ] γ , c) →
           Exp var τ₂ ([ α , a ] δ , d)
  Shift0 : {τ τ₃ τ₄ τ₅ τ₆ α β : Ty} {a₃ a₄ b₅ b₆ : Ann} →
           (var (τ ⇒ α ,[ τ₃ , a₃ ] τ₄ , a₄) →
            Exp var β ([ τ₅ , b₅ ] τ₆ , b₆)) →
           Exp var τ ([ α , [ τ₃ , a₃ ] τ₄ , a₄ ] β , [ τ₅ , b₅ ] τ₆ , b₆)
  Reset0 : {τ α β : Ty} {a b : Ann} →
           Exp var τ ([ τ , ([ α , a ] α , a) ] β , b) → Exp var β b

-- Interpretation of types and annotated types
〚_〛     : Ty → Set
〚_,_〛'  : Ty → Ann → Set

〚 Nat 〛 = ℕ
〚 Bool 〛 = 𝔹
〚 τ₁ ⇒ τ₂ ,[ α , a ] β , b 〛 = 〚 τ₁ 〛 → 〚 τ₂ , [ α , a ] β , b 〛'

〚 τ , ε 〛' = 〚 τ 〛
〚 τ , ([ α , a ] β , b) 〛' = (〚 τ 〛 → 〚 α , a 〛') → 〚 β , b 〛'

-- Empty continuation
k0 : {A : Set} → A → A
k0 v = v

k1 : {A B : Set} → A → (A → B) → B
k1 x k = k x

-- Interpretation of terms
g : {τ : Ty} {a : Ann} → Exp 〚_〛 τ a → 〚 τ , a 〛'

g (Var x) k = k x
g (Num n) k = k n
g (Bol b) k = k b
g (Lam f) k = k (λ x → g (f x))
g (App e₁ e₂) k = g e₁ (λ v₁ → g e₂ (λ v₂ → v₁ v₂ k))
g (Shift0 f) k = g (f k)
g (Reset0 e) = g e k1

-- Top-level evaluation
go : {τ : Ty} → Exp 〚_〛 τ ([ τ , ε ] τ , ε) → 〚 τ 〛
go e = g e k0
