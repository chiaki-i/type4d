-- Type system for control/prompt in 2CPS with functionalized meta continuation
-- Based on Shan [HOSC 2007]

module control-4Dfun where

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

data Tr : Set

data Mc : Set

data Ty where
  Nat  : Ty
  Bool : Ty
  Str  : Ty
  _⇒_⟨_,_⟩_⟨_,_⟩_ : Ty → Ty → Tr → Mc → Ty → Tr → Mc → Ty → Ty

data Tr where
  ● : Tr
  _⇨⟨_,_⟩_  : Ty → Tr → Mc → Ty → Tr

infix 5 _⇨⟨_,_⟩_

data Mc where
  _⇒_ : Ty → Ty → Mc

infix 6 _⇒_


id-cont-type : Ty → Tr → Mc → Ty → Set
id-cont-type τ ● (τ₁ ⇒ τ₁') τ' = (τ₁ ≡ τ) × (τ₁' ≡ τ')
id-cont-type τ (τ₁ ⇨⟨ μ₁ , τ₂ ⇒ τ₃ ⟩ τ₁') (τ₂' ⇒ τ₃') τ' =
  (τ ≡ τ₁) × (μ₁ ≡ ●) × (τ₂ ≡ τ₂') × (τ₃ ≡ τ₃') × (τ₁' ≡ τ')

compatible : Tr → Tr → Tr → Set
compatible ● μ₂ μ₃ = μ₂ ≡ μ₃
compatible (τ₁ ⇨⟨ μ₁ , σ₁ ⟩ τ₁') ● μ₃ = (τ₁ ⇨⟨ μ₁ , σ₁ ⟩ τ₁') ≡ μ₃
compatible (τ₁ ⇨⟨ μ₁ , σ₁ ⟩ τ₁') (τ₂ ⇨⟨ μ₂ , σ₂ ⟩ τ₂') ● = ⊥
compatible (τ₁ ⇨⟨ μ₁ , σ₁ ⟩ τ₁') (τ₂ ⇨⟨ μ₂ , σ₂ ⟩ τ₂') (τ₃ ⇨⟨ μ₃ , σ₃ ⟩ τ₃') = (τ₁ ≡ τ₃) × (σ₁ ≡ σ₃) × (τ₁' ≡ τ₃') × (compatible (τ₂ ⇨⟨ μ₂ , σ₂ ⟩ τ₂') μ₃ μ₁)

data Exp (var : Ty → Set) : Ty → Tr → Mc → Ty → Tr → Mc → Ty → Set where
  Var     : {τ α : Ty} {μα : Tr} {σα : Mc} →
            var τ → Exp var τ μα σα α μα σα α
  Num     : {α : Ty} {μα : Tr} {σα : Mc} →
            ℕ → Exp var Nat μα σα α μα σα α
  Bol     : {α : Ty} {μα : Tr} {σα : Mc} →
            𝔹 → Exp var Bool μα σα α μα σα α
  Lam     : {τ₁ τ₂ α β γ : Ty} {μα μβ μγ : Tr} {σα σβ σγ : Mc} →
            (var τ₁ → Exp var τ₂ μα σα α μβ σβ β) →
            Exp var (τ₁ ⇒ τ₂ ⟨ μα , σα ⟩ α ⟨ μβ , σβ ⟩ β) μγ σγ γ μγ σγ γ
  App     : {τ₁ τ₂ α β γ δ : Ty} {μα μβ μγ μδ : Tr} {σα σβ σγ σδ : Mc} →
            Exp var (τ₁ ⇒ τ₂ ⟨ μα , σα ⟩ α ⟨ μβ , σβ ⟩ β) μγ σγ γ μδ σδ δ →
            Exp var τ₁ μβ σβ β μγ σγ γ →
            Exp var τ₂ μα σα α μδ σδ δ
  Control : {τ τ₁ τ₂ α β γ γ' : Ty} {μ₀ μ₁ μ₂ μ' μid μα μβ : Tr} {σ₁ σα σβ σid : Mc} →
            id-cont-type γ μid σid γ' →
            compatible (τ₁ ⇨⟨ μ₁ , σ₁ ⟩ τ₂) μ₂ μ' →
            compatible μβ μ' μα →
            (var (τ ⇒ τ₁ ⟨ μ₁ , σ₁ ⟩ τ₂ ⟨ μ₂ , σα ⟩ α) → Exp var γ μid σid γ' ● σβ β) →
            Exp var τ μα σα α μβ σβ β
  Reset   : {τ α β γ γ' : Ty} {μα μid : Tr} {σα σid : Mc} →
            id-cont-type γ μid σid γ' →
            Exp var γ μid σid γ' ● (τ ⇒ α) β →
            Exp var τ μα σα α μα σα β


-- Interpretation of types
〚_〛τ : Ty → Set
〚_〛μ : Tr → Set
〚_〛σ : Mc → Set

〚 Nat 〛τ = ℕ
〚 Bool 〛τ = 𝔹
〚 Str 〛τ = String
〚 τ₂ ⇒ τ₁ ⟨ μα , σα ⟩ α ⟨ μβ , σβ ⟩ β 〛τ =
  〚 τ₂ 〛τ → (〚 τ₁ 〛τ → 〚 μα 〛μ → 〚 σα 〛σ → 〚 α 〛τ) →
  〚 μβ 〛μ → 〚 σβ 〛σ → 〚 β 〛τ

〚 ● 〛μ = ⊤
〚 τ ⇨⟨ μ , σ ⟩ τ' 〛μ = 〚 τ 〛τ → 〚 μ 〛μ → 〚 σ 〛σ → 〚 τ' 〛τ

〚 τ₁ ⇒ τ₂ 〛σ = 〚 τ₁ 〛τ → 〚 τ₂ 〛τ


-- Initial continuation
idc : {τ τ' : Ty} → {μ : Tr} → {σ : Mc} →
      id-cont-type τ μ σ τ' → 〚 τ 〛τ → 〚 μ 〛μ → 〚 σ 〛σ → 〚 τ' 〛τ
idc {μ = ●} {τ₁ ⇒ τ₂} (refl , refl) v tt m = m v
idc {μ = τ ⇨⟨ .● , τ₂ ⇒ τ₃ ⟩ τ₁} {.τ₂ ⇒ .τ₃} (refl , refl , refl , refl , refl) v c m = c v tt m

-- compose-trail
compose-trail : {μ₁ μ₂ μ₃ : Tr} → compatible μ₁ μ₂ μ₃ → 〚 μ₁ 〛μ → 〚 μ₂ 〛μ → 〚 μ₃ 〛μ
compose-trail {●} refl tt t₂ = t₂
compose-trail {x₃ ⇨⟨ μ₁ , x₄ ⟩ x₅} {●} refl t₁ tt = t₁
compose-trail {x₃ ⇨⟨ μ₁ , x₄ ⟩ x₅} {x₆ ⇨⟨ μ₂ , x₇ ⟩ x₈} {.x₃ ⇨⟨ μ₃ , .x₄ ⟩ .x₅} (refl , refl , refl , c) t₁ t₂ =
  λ v t m → t₁ v (compose-trail c t₂ t) m

-- Interpretation of terms
g : {τ α β : Ty} {μα μβ : Tr} {σα σβ : Mc} →
    Exp 〚_〛τ τ μα σα α μβ σβ β →
    (〚 τ 〛τ → 〚 μα 〛μ → 〚 σα 〛σ → 〚 α 〛τ) →
    〚 μβ 〛μ → 〚 σβ 〛σ → 〚 β 〛τ
g (Var x) c t m = c x t m
g (Num n) c t m = c n t m
g (Bol b) c t m = c b t m
g (Lam e) c t m = c (λ v c' t' m' → g (e v) c' t' m') t m
g (App e₁ e₂) c t m =
  g e₁ (λ v₁ t₁ m₁ → g e₂ (λ v₂ t₂ m₂ → v₁ v₂ c t₂ m₂) t₁ m₁) t m
g (Control id-c-t ct₁ ct₂ e) c t m =
  g (e (λ v c' t' m' → c v (compose-trail ct₂ t (compose-trail ct₁ c' t')) m'))
  (idc id-c-t) tt m
g (Reset id-c-t e) c t m = g e (idc id-c-t) tt (λ v → c v t m)
