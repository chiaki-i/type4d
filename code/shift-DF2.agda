-- Type system for shift/reset in 2CPS (DF2)
-- without trail, with functionalized meta continuations

module shift-DF2 where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Bool using (true; false; if_then_else_) renaming (Bool to 𝔹)
open import Data.String using (String)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning

-- Types
data Ty : Set

data Mc : Set

data Ty where
  Nat   : Ty
  Bool  : Ty
  Str   : Ty
  _⇒_⟨_⟩_⟨_⟩_ : Ty → Ty → Mc → Ty → Mc → Ty → Ty

data Mc where
  _⇨_ : Ty → Ty → Mc

-- Terms
-- e : Exp var τ σα α σβ β  means that e
--  * has type τ
--  * requires
--      - a context that yields a computation of type α
--        when given a metacontext of type σα
--      - a metacontext of type σβ
--  * eventually returns a value of type β
data Exp (var : Ty → Set) : Ty → Mc → Ty → Mc → Ty → Set where
  Var    : {τ α : Ty} {σα : Mc} →
           var τ → Exp var τ σα α σα α
  Num    : {α : Ty} {σα : Mc} →
           ℕ → Exp var Nat σα α σα α
  Bol    : {α : Ty} {σα : Mc} →
           𝔹 → Exp var Bool σα α σα α
  Lam    : {τ₁ τ₂ α β γ : Ty} {σα σβ σγ : Mc} →
           (var τ₁ → Exp var τ₂ σα α σβ β) →
           Exp var (τ₁ ⇒ τ₂ ⟨ σα ⟩ α ⟨ σβ ⟩ β) σγ γ σγ γ
  App    : {τ₁ τ₂ α β γ δ : Ty} {σα σβ σγ σδ : Mc} →
           Exp var (τ₁ ⇒ τ₂ ⟨ σα ⟩ α ⟨ σβ ⟩ β) σγ γ σδ δ →
           Exp var τ₁ σβ β σγ γ →
           Exp var τ₂ σα α σδ δ
  Shift  : {τ τ₁ τ₂ α β γ γ' : Ty} {σ₁ σβ : Mc} →
           (var (τ ⇒ τ₁ ⟨ σ₁ ⟩ τ₂ ⟨ σ₁ ⟩ α) →
             Exp var γ (γ ⇨ γ') γ' σβ β) →
           Exp var τ (τ₁ ⇨ τ₂) α σβ β
  Reset  : {τ α β γ γ' : Ty} {σα : Mc} →
           Exp var γ (γ ⇨ γ') γ' (τ ⇨ α) β →
           Exp var τ σα α σα β
