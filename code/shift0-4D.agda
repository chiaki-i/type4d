-- 4D Type system for shift0/reset0
-- This file includes below:
--   * a definition of a subset of λD: λ-calculus and shift0/reset0, with typing rules
--   * a CPS interpreter

module 4d-shift0 where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Bool using (true; false; if_then_else_) renaming (Bool to 𝔹)
open import Data.String using (String)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; _×_)
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning

-- Types
data Ty : Set

data Mc : Set

data Ty where
  Nat   : Ty
  Bool  : Ty
  _⇒_,_,_,_,_ : Ty → Ty → Mc → Ty → Mc → Ty → Ty

data Mc where
  ●σ     : Mc
  _⇨_,_∷_ : Ty → Mc → Ty → Mc → Mc

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
           Exp var (τ₁ ⇒ τ₂ , σα , α , σβ , β) σγ γ σγ γ
  App    : {τ₁ τ₂ α β γ δ : Ty} {σα σβ σγ σδ : Mc} →
           Exp var (τ₁ ⇒ τ₂ , σα , α , σβ , β) σγ γ σδ δ →
           Exp var τ₁ σβ β σγ γ →
           Exp var τ₂ σα α σδ δ
  Plus   : {α β γ : Ty} {σα σβ σγ : Mc} →
           Exp var Nat σα α σβ β →
           Exp var Nat σγ γ σα α →
           Exp var Nat σγ γ σβ β
  Shift0 : {τ τ' τ₀ α α' α₀ β : Ty} {σ' σ₀ σ₀' σ₁' : Mc} →
           (var (τ ⇒ τ' , σ₁' , α' , σ' , α) →
            Exp var τ₀ σ₀ α₀ σ₀' β) →
           Exp var τ (τ' ⇨ σ₁' , α' ∷ σ') α (τ₀ ⇨ σ₀ , α₀ ∷ σ₀') β
  Reset0 : {τ α α' β β' : Ty} {σ σ' σ₁ : Mc} →
           Exp var β (β ⇨ σ' , β' ∷ σ') β' (τ ⇨ σ₁ , α ∷ σ) α' →
           Exp var τ σ₁ α σ α'

-- Interpretation of types
〚_〛τ : Ty → Set
〚_〛σ : Mc → Set

〚 Nat 〛τ = ℕ
〚 Bool 〛τ = 𝔹
〚 τ₂ ⇒ τ₁ , σα , α , σβ , β 〛τ =
  〚 τ₂ 〛τ → (〚 τ₁ 〛τ → 〚 σα 〛σ → 〚 α 〛τ) → 〚 σβ 〛σ → 〚 β 〛τ

〚 ●σ 〛σ = ⊤
〚 τ ⇨ σ , τ' ∷ σ' 〛σ = (〚 τ 〛τ → 〚 σ 〛σ → 〚 τ' 〛τ) × 〚 σ' 〛σ

-- Initial continuation
θ₀ : {τ : Ty} →
     〚 τ 〛τ → 〚 ●σ 〛σ → 〚 τ 〛τ
θ₀ v tt = v

θ₁ : {τ τ' : Ty} {σ : Mc} →
     〚 τ 〛τ → 〚 τ ⇨ σ , τ' ∷ σ 〛σ → 〚 τ' 〛τ
θ₁ v (k , m) = k v m

-- Interpretation of terms
g : {var : Ty → Set} {τ α β : Ty} {σα σβ : Mc} →
    Exp 〚_〛τ τ σα α σβ β →
    (〚 τ 〛τ → 〚 σα 〛σ → 〚 α 〛τ) → 〚 σβ 〛σ → 〚 β 〛τ
g (Var x) k m = k x m
g (Num n) k m = k n m
g (Bol b) k m = k b m
g (Lam f) k m = k (λ x → g {var = 〚_〛τ} (f x)) m
g (App e₁ e₂) k m =
  g {var = 〚_〛τ} e₁
    (λ v₁ m₁ → g {var = 〚_〛τ} e₂ (λ v₂ m₂ → v₁ v₂ k m₂) m₁) m
g (Plus e₁ e₂) k m =
  g {var = 〚_〛τ} e₁
    (λ v₁ m₁ → g {var = 〚_〛τ} e₂ (λ v₂ m₂ → k (v₁ + v₂) m₂) m₁) m
g (Shift0 f) k (k₀ , m₀) = g {var = 〚_〛τ} (f λ v k' m' → k v (k' , m')) k₀ m₀
g (Reset0 e) k m = g {var = 〚_〛τ} e θ₁ (k , m)

-- Top-level evaluation
go : {τ : Ty} → Exp 〚_〛τ τ ●σ τ ●σ τ → 〚 τ 〛τ
go e = g {var = 〚_〛τ} e θ₀ tt
