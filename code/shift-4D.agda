-- Type system for shift/reset in 2CPS, with defunctionalized meta continuation
-- This is a subset of 4D.agda (with only shift/reset as delimited control operator)

module shift-4D where

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
  Nat   : Ty
  Bool  : Ty
  Str   : Ty
  _⇒_⟨_,_⟩_⟨_,_⟩_ : Ty → Ty → Tr → Mc → Ty → Tr → Mc → Ty → Ty

data Tr where
  ●       : Tr
  _⇨⟨_,_⟩_ : Ty → Tr → Mc → Ty → Tr

infix 5 _⇨⟨_,_⟩_

data Mc where
  []       : Mc
  _⇨⟨_,_⟩_×_∷_ : Ty → Tr → Mc → Ty → Tr → Mc → Mc

infix 6 _⇨⟨_,_⟩_×_∷_

compatible : Tr → Tr → Tr → Set
compatible ● μ₂ μ₃ = μ₂ ≡ μ₃
compatible (τ₁ ⇨⟨ μ₁ , σ₁ ⟩ τ₁') ● μ₃ = (τ₁ ⇨⟨ μ₁ , σ₁ ⟩ τ₁') ≡ μ₃
compatible (τ₁ ⇨⟨ μ₁ , σ₁ ⟩ τ₁') (τ₂ ⇨⟨ μ₂ , σ₂ ⟩ τ₂') ● = ⊥
compatible (τ₁ ⇨⟨ μ₁ , σ₁ ⟩ τ₁') (τ₂ ⇨⟨ μ₂ , σ₂ ⟩ τ₂') (τ₃ ⇨⟨ μ₃ , σ₃ ⟩ τ₃') =
  τ₁ ≡ τ₃ × τ₁' ≡ τ₃' × σ₁ ≡ σ₃ × compatible (τ₂ ⇨⟨ μ₂ , σ₂ ⟩ τ₂') μ₃ μ₁

id-cont-type : Ty → Tr → Mc → Ty → Set
id-cont-type τ ● [] τ' = τ ≡ τ'
id-cont-type τ ● (τ₁ ⇨⟨ μ₁ , σ₁ ⟩ τ₁' × μ₂ ∷ σ₂) τ' = (τ ≡ τ₁) × (τ' ≡ τ₁') × (μ₁ ≡ μ₂) × (σ₁ ≡ σ₂)
id-cont-type τ (τ₁ ⇨⟨ μ₁ , σ₁ ⟩ τ₁') σ₂ τ' = (τ ≡ τ₁) × (τ' ≡ τ₁') × (μ₁ ≡ ●) × (σ₁ ≡ σ₂)

-- Terms
-- e : Exp var τ μα σα α μβ σβ β  means that e
--  * has type τ
--  * requires
--      - a context that yields a computation of type α
--        when given a trail of type μα and a metacontext of type σα
--      - a trail of type μβ
--      - a metacontext of type σβ
--  * eventually returns a value of type β
data Exp (var : Ty → Set) : Ty → Tr → Mc → Ty → Tr → Mc → Ty → Set where
  Var      : {τ α : Ty} {σα : Mc} →
             var τ → Exp var τ ● σα α ● σα α
  Num      : {α : Ty} {σα : Mc} →
             ℕ → Exp var Nat ● σα α ● σα α
  Bol      : {α : Ty} {σα : Mc} →
             𝔹 → Exp var Bool ● σα α ● σα α
  Lam      : {τ₁ τ₂ α β γ : Ty} {σα σβ σγ : Mc} →
             (var τ₁ → Exp var τ₂ ● σα α ● σβ β) →
             Exp var (τ₁ ⇒ τ₂ ⟨ ● , σα ⟩ α ⟨ ● , σβ ⟩ β) ● σγ γ ● σγ γ
  App      : {τ₁ τ₂ α β γ δ : Ty} {σα σβ σγ σδ : Mc} →
             Exp var (τ₁ ⇒ τ₂ ⟨ ● , σα ⟩ α ⟨ ● , σβ ⟩ β) ● σγ γ ● σδ δ →
             Exp var τ₁ ●  σβ β ● σγ γ →
             Exp var τ₂ ● σα α ● σδ δ
  Shift    : {τ τ₁ τ₂ α β γ γ' : Ty} {σ₁ σβ σid : Mc} →
             id-cont-type γ ● σid γ' →
             (var (τ ⇒ τ₁ ⟨ ● , σ₁ ⟩ τ₂ ⟨ ● , σ₁ ⟩ α) →
              Exp var γ ● σid γ' ● σβ β) →
             Exp var τ ● (τ₁ ⇨⟨ ● , σ₁ ⟩ τ₂ × ● ∷ σ₁) α ● σβ β
  Prompt0  : {τ α β γ γ' : Ty} {σα σid : Mc} →
             id-cont-type γ ● σid γ' →
             Exp var γ ● σid γ' ● (τ ⇨⟨ ● , σα ⟩ α × ● ∷ σα) β →
             Exp var τ ● σα α ● σα β

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

〚 [] 〛σ = ⊤
〚 τ ⇨⟨ μ , σ ⟩ τ' × μ' ∷ σ' 〛σ =
  ((〚 τ 〛τ → 〚 μ 〛μ → 〚 σ 〛σ → 〚 τ' 〛τ) × 〚 μ' 〛μ) × 〚 σ' 〛σ

-- Trail composition
compose-trail : {μ₁ μ₂ μ₃ : Tr} →
                compatible μ₁ μ₂ μ₃ → 〚 μ₁ 〛μ → 〚 μ₂ 〛μ → 〚 μ₃ 〛μ
compose-trail {●} refl tt t2 = t2
compose-trail {τ₁ ⇨⟨ μ₁ , σ₁ ⟩ τ₁'} {●} refl t1 tt = t1
compose-trail {τ₁ ⇨⟨ μ₁ , σ₁ ⟩ τ₁'} {τ₂ ⇨⟨ μ₂ , σ₂ ⟩ τ₂'} {.τ₁ ⇨⟨ μ₃ , .σ₁ ⟩ .τ₁'} (refl , refl , refl , c) t1 t2 =
  λ v t' m' → t1 v (compose-trail c t2 t') m'

-- Initial continuation
idk : {τ τ' : Ty} → {μ : Tr} → {σ : Mc} →
      id-cont-type τ μ σ τ' →
      〚 τ 〛τ → 〚 μ 〛μ → 〚 σ 〛σ → 〚 τ' 〛τ
idk {μ = ●} {[]} refl v tt tt = v
idk {μ = ●} {x ⇨⟨ x₁ , σ ⟩ x₂ × .x₁ ∷ .σ} (refl , refl , refl , refl) v tt ((k₀ , t₀) , m₀) = k₀ v t₀ m₀
idk {μ = x₁ ⇨⟨ .● , x₃ ⟩ x₄} (refl , refl , refl , refl) v t m = t v tt m

-- Interpretation of terms
g : {var : Ty → Set} {τ α β : Ty} {μβ : Tr} {σα σβ : Mc} →
    Exp 〚_〛τ τ ● σα α μβ σβ β →
    (〚 τ 〛τ → 〚 ● 〛μ → 〚 σα 〛σ → 〚 α 〛τ) →
    〚 μβ 〛μ → 〚 σβ 〛σ → 〚 β 〛τ
g (Var x) k t m = k x t m
g (Num n) k t m = k n t m
g (Bol b) k t m = k b t m
g (Lam f) k t m = k (λ x t₁ m₁ → g {var = 〚_〛τ} (f x) t₁ m₁) t m
g (App e₁ e₂) k t m =
  g {var = 〚_〛τ} e₁
    (λ v₁ t₁ m₁ → g {var = 〚_〛τ} e₂ (λ v₂ t₂ m₂ → v₁ v₂ k t₂ m₂) t₁ m₁) t m
g (Shift is-id f) k t m = g {var = 〚_〛τ} (f (λ v k' t' m' → k v t (((k' , t') , m')))) (idk is-id) tt m
g (Prompt0 is-id e) k t m =
  g {var = 〚_〛τ} e (idk is-id) tt ((k , t) , m)

-- Top-level evaluation
go : {τ : Ty} → id-cont-type τ ● [] τ → Exp 〚_〛τ τ ● [] τ ● [] τ → 〚 τ 〛τ
go refl e = g {var = 〚_〛τ} e (λ z _ _ → z) tt tt
