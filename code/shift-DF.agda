-- Type system for shift/reset in 1CPS (DF)
-- Based on [Danvy and Filinski '89]

module shift-DF where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Bool using (true; false; if_then_else_) renaming (Bool to 𝔹)
open import Data.String using (String)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning

data Ty : Set where
  Nat   : Ty
  Bool  : Ty
  Str   : Ty
  _⇒_[_,_] : Ty → Ty → Ty → Ty → Ty

data Tm (var : Ty → Set) : Ty → Ty → Ty → Set where
  Num : {α : Ty} → ℕ → Tm var Nat α α
  Bol : {α : Ty} → 𝔹 → Tm var Bool α α
  Var : {τ α : Ty} → var τ → Tm var τ α α
  Lam : {τ₁ τ₂ α β γ : Ty} →
        (var τ₂ → Tm var τ₁ α β) →
        Tm var (τ₂ ⇒ τ₁ [ α , β ]) γ γ
  App : {τ₁ τ₂ α β γ δ : Ty} →
        Tm var (τ₂ ⇒ τ₁ [ α , β ]) γ δ →
        Tm var τ₂ β γ →
        Tm var τ₁ α δ
  Sft : {τ α β γ δ : Ty} →
        (var (τ ⇒ α [ β , β ]) → Tm var γ γ δ) →
        Tm var τ α δ
  Rst : {τ α γ : Ty} →
        Tm var γ γ τ →
        Tm var τ α α
