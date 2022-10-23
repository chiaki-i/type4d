-- Type system for control/prompt in 1CPS (CP)
-- Based on Cong et al. [FSCD 2021]

module control-CP where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Bool using (true; false; if_then_else_) renaming (Bool to 𝔹)
open import Data.String using (String)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; _×_; Σ)
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning

-- Expression types
data Ty : Set

-- Trail types
data Tr : Set

data Ty where
  Nat   : Ty
  Bool  : Ty
  Str   : Ty
  _⇒_,_,_,_,_ : Ty → Ty → Tr → Ty → Tr → Ty → Ty

data Tr where
  ●     : Tr
  _⇨_,_ : (τ₁ τ₁' : Ty) → Tr → Tr

-- Compatibility relation
compatible : Tr → Tr → Tr → Set
compatible ● μ₂ μ₃ = μ₂ ≡ μ₃
compatible (τ₁ ⇨ τ₁' , μ₁) ● μ₃ = (τ₁ ⇨ τ₁' , μ₁) ≡ μ₃
compatible (τ₁ ⇨ τ₁' , μ₁) (τ₂ ⇨ τ₂' , μ₂) ● = ⊥
compatible (τ₁ ⇨ τ₁' , μ₁) (τ₂ ⇨ τ₂' , μ₂) (τ₃ ⇨ τ₃' , μ₃) =
  τ₁ ≡ τ₃ × τ₁' ≡ τ₃' × compatible (τ₂ ⇨ τ₂' , μ₂) μ₃ μ₁

-- Identity trail check
is-id-trail : (τ τ' : Ty) → (μ : Tr) → Set
is-id-trail τ τ' ● = τ ≡ τ'
is-id-trail τ τ' (τ₁ ⇨ τ₁' , μ) = τ ≡ τ₁ × τ' ≡ τ₁' × μ ≡ ●

-- Expressions
-- e : Exp var τ μα α μβ β  means
--  * e has type τ
--  * e produces a value of type β when
--      - surrounded by a context that receives a trail of type μα
--        and returns a value of type α
--      - given a trail of type μβ
data Exp (var : Ty → Set) : Ty → Tr → Ty → Tr → Ty → Set where
  Var     : {τ α : Ty} {μα : Tr} →
            var τ → Exp var τ μα α μα α
  Num     : {α : Ty} {μα : Tr} →
            ℕ → Exp var Nat μα α μα α
  Bol     : {α : Ty} {μα : Tr} →
            𝔹 → Exp var Bool μα α μα α
  Lam     : {τ₁ τ₂ α β γ : Ty} {μα μβ μγ : Tr} →
            (var τ₁ → Exp var τ₂ μα α μβ β) →
            Exp var (τ₁ ⇒ τ₂ , μα , α , μβ , β) μγ γ μγ γ
  App     : {τ₁ τ₂ α β γ δ : Ty} {μα μβ μγ μδ : Tr} →
            Exp var (τ₁ ⇒ τ₂ , μα , α , μβ , β) μγ γ μδ δ →
            Exp var τ₁ μβ β μγ γ →
            Exp var τ₂ μα α μδ δ
  Control : {τ α β γ γ' τ₁ τ₂ : Ty} {μid μ₀ μ₁ μ₂ μα μβ : Tr} →
            is-id-trail γ γ' μid →
            compatible (τ₁ ⇨ τ₂ , μ₁) μ₂ μ₀ →
            compatible μβ μ₀ μα →
            (var (τ ⇒ τ₁ , μ₁ , τ₂ , μ₂ , α) →
             Exp var γ μid γ' ● β) →
            Exp var τ μα α μβ β
  Prompt  : {τ α β β' : Ty} {μid μα : Tr} →
            is-id-trail β β' μid →
            Exp var β μid β' ● τ →
            Exp var τ μα α μα α

-- CPS interpreter

-- Interpretation of types
〚_〛τ : Ty → Set
〚_〛μ : Tr → Set

〚 Nat 〛τ = ℕ
〚 Bool 〛τ = 𝔹
〚 Str 〛τ = String
〚 τ₂ ⇒ τ₁ , μα , α , μβ , β 〛τ =
  〚 τ₂ 〛τ → (〚 τ₁ 〛τ → 〚 μα 〛μ → 〚 α 〛τ) → 〚 μβ 〛μ → 〚 β 〛τ

〚 ● 〛μ = ⊤
〚 τ ⇨ τ' , μ 〛μ = 〚 τ 〛τ → 〚 μ 〛μ → 〚 τ' 〛τ

-- Trail composition
compose-trail : {μ₁ μ₂ μ₃ : Tr} →
  compatible μ₁ μ₂ μ₃ → 〚 μ₁ 〛μ → 〚 μ₂ 〛μ → 〚 μ₃ 〛μ
compose-trail {●} refl tt t₂ = t₂
compose-trail {τ₁ ⇨ τ₁' , μ₁} {●} refl t₁ tt = t₁
compose-trail {τ₁ ⇨ τ₁' , μ₁} {τ₂ ⇨ τ₂' , μ₂} {.τ₁ ⇨ .τ₁' , μ₃}
              (refl , refl , c) t₁ t₂ =
  λ v t' → t₁ v (compose-trail c t₂ t')

-- Identity continuation
id-cont : {τ τ' : Ty} → {μ : Tr} →
     is-id-trail τ τ' μ →
     〚 τ 〛τ → 〚 μ 〛μ → 〚 τ' 〛τ
id-cont {μ = ●} refl v tt = v
id-cont {μ = τ₁ ⇨ τ₁' , .●} (refl , refl , refl) v k = k v tt

-- Interpretation of terms
g : {var : Ty → Set} {τ α β : Ty} {μα μβ : Tr} →
    Exp 〚_〛τ τ μα α μβ β →
    (〚 τ 〛τ → 〚 μα 〛μ → 〚 α 〛τ) → 〚 μβ 〛μ → 〚 β 〛τ
g (Var x) k t = k x t
g (Num n) k t = k n t
g (Bol b) k t = k b t
g (Lam f) k t = k (λ x → g {var = 〚_〛τ} (f x)) t
g (App e₁ e₂) k t =
  g {var = 〚_〛τ} e₁
    (λ v₁ t₁ → g {var = 〚_〛τ} e₂ (λ v₂ t₂ → v₁ v₂ k t₂) t₁) t
g (Control is-id c₁ c₂ f) k t =
  g {var = 〚_〛τ}
    (f (λ v k' t' → k v (compose-trail c₂ t (compose-trail c₁ k' t'))))
    (id-cont is-id) tt
g (Prompt is-id e) k t = k (g {var = 〚_〛τ} e (id-cont is-id) tt) t

-- Top-level evaluation
go : {τ : Ty} → Exp 〚_〛τ τ ● τ ● τ → 〚 τ 〛τ
go e = g {var = 〚_〛τ} e (λ z _ → z) tt
