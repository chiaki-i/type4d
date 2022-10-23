-- Type system for four delimited control operators (4D):
-- for shift/reset, control/prompt, shift0/reset0, and control0/prompt0

module 4D where

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

-- Term types
data Ty where
  Nat   : Ty
  Bool  : Ty
  _⇒_⟨_,_⟩_⟨_,_⟩_ : Ty → Ty → Tr → Mc → Ty → Tr → Mc → Ty → Ty

-- Trail types
data Tr where
  ●μ       : Tr
  _⇨⟨_,_⟩_ : Ty → Tr → Mc → Ty → Tr

infix 5 _⇨⟨_,_⟩_

-- Meta continuation types
data Mc where
  ●σ       : Mc
  _⇨⟨_,_⟩_×_∷_ : Ty → Tr → Mc → Ty → Tr → Mc → Mc

infix 6 _⇨⟨_,_⟩_×_∷_

-- Compatibility relation
compatible : Tr → Tr → Tr → Set
compatible ●μ μ₂ μ₃ = μ₂ ≡ μ₃
compatible (τ₁ ⇨⟨ μ₁ , σ₁ ⟩ τ₁') ●μ μ₃ = (τ₁ ⇨⟨ μ₁ , σ₁ ⟩ τ₁') ≡ μ₃
compatible (τ₁ ⇨⟨ μ₁ , σ₁ ⟩ τ₁') (τ₂ ⇨⟨ μ₂ , σ₂ ⟩ τ₂') ●μ = ⊥
compatible (τ₁ ⇨⟨ μ₁ , σ₁ ⟩ τ₁') (τ₂ ⇨⟨ μ₂ , σ₂ ⟩ τ₂') (τ₃ ⇨⟨ μ₃ , σ₃ ⟩ τ₃') =
  τ₁ ≡ τ₃ × τ₁' ≡ τ₃' × σ₁ ≡ σ₃ × compatible (τ₂ ⇨⟨ μ₂ , σ₂ ⟩ τ₂') μ₃ μ₁

-- Identity continuation check
id-cont-type : Ty → Tr → Mc → Ty → Set
id-cont-type τ ●μ ●σ τ' = τ ≡ τ'
id-cont-type τ ●μ (τ₁ ⇨⟨ μ₁ , σ₁ ⟩ τ₁' × μ₂ ∷ σ₂) τ' = (τ ≡ τ₁) × (τ' ≡ τ₁') × (μ₁ ≡ μ₂) × (σ₁ ≡ σ₂)
id-cont-type τ (τ₁ ⇨⟨ μ₁ , σ₁ ⟩ τ₁') σ₂ τ' = (τ ≡ τ₁) × (τ' ≡ τ₁') × (μ₁ ≡ ●μ) × (σ₁ ≡ σ₂)

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
  Var      : {τ α : Ty} {μα : Tr} {σα : Mc} →
             var τ → Exp var τ μα σα α μα σα α
  Num      : {α : Ty} {μα : Tr} {σα : Mc} →
             ℕ → Exp var Nat μα σα α μα σα α
  Bol      : {α : Ty} {μα : Tr} {σα : Mc} →
             𝔹 → Exp var Bool μα σα α μα σα α
  Lam      : {τ₁ τ₂ α β γ : Ty} {μα μβ μγ : Tr} {σα σβ σγ : Mc} →
             (var τ₁ → Exp var τ₂ μα σα α μβ σβ β) →
             Exp var (τ₁ ⇒ τ₂ ⟨ μα , σα ⟩ α ⟨ μβ , σβ ⟩ β) μγ σγ γ μγ σγ γ
  App      : {τ₁ τ₂ α β γ δ : Ty} {μα μβ μγ μδ : Tr} {σα σβ σγ σδ : Mc} →
             Exp var (τ₁ ⇒ τ₂ ⟨ μα , σα ⟩ α ⟨ μβ , σβ ⟩ β) μγ σγ γ μδ σδ δ →
             Exp var τ₁ μβ σβ β μγ σγ γ →
             Exp var τ₂ μα σα α μδ σδ δ
  Shift    : {τ τ₁ τ₂ α β γ γ' : Ty} {μ₁ μ₂ μβ μid : Tr} {σ₁ σ₂ σβ σid : Mc} →
             id-cont-type γ μid σid γ' →
             (var (τ ⇒ τ₁ ⟨ μ₁ , σ₁ ⟩ τ₂ ⟨ μ₂ , σ₂ ⟩ α) →
              Exp var γ μid σid γ' ●μ σβ β) →
             Exp var τ μβ (τ₁ ⇨⟨ μ₁ , σ₁ ⟩ τ₂ × μ₂ ∷ σ₂) α μβ σβ β
  Shift0   : {τ τ₀ τ₀' τ₁ τ₂ α β : Ty} {μ₀ μ₀' μ₁ μ₂ μβ : Tr} {σ₀ σ₀' σ₁ σ₂ : Mc} →
             (var (τ ⇒ τ₁ ⟨ μ₁ , σ₁ ⟩ τ₂ ⟨ μ₂ , σ₂ ⟩ α) →
              (Exp var τ₀ μ₀ σ₀ τ₀' μ₀' σ₀' β)) →
             Exp var τ μβ (τ₁ ⇨⟨ μ₁ , σ₁ ⟩ τ₂ × μ₂ ∷ σ₂ ) α μβ (τ₀ ⇨⟨ μ₀ , σ₀ ⟩ τ₀' × μ₀' ∷ σ₀' ) β
  Control  : {τ τ₁ τ₂ α β γ γ' : Ty} {μ₀ μ₁ μ₂ μid μα μβ : Tr} {σ₁ σα σβ σid : Mc} →
             id-cont-type γ μid σid γ' →
             compatible (τ₁ ⇨⟨ μ₁ , σ₁ ⟩ τ₂) μ₂ μ₀ →
             compatible μβ μ₀ μα →
             (var (τ ⇒ τ₁ ⟨ μ₁ , σ₁ ⟩ τ₂ ⟨ μ₂ , σα ⟩ α) →
              Exp var γ μid σid γ' ●μ σβ β) →
             Exp var τ μα σα α μβ σβ β
  Control0 : {τ τ₀ τ₀' τ₁ τ₂ α β : Ty} {μ₀ μ₀' μ₁ μ₂ μα μβ μγ : Tr}
             {σ₀ σ₀' σ₁ σα : Mc} →
             compatible (τ₁ ⇨⟨ μ₁ , σ₁ ⟩ τ₂) μ₂ μγ →
             compatible μβ μγ μα →
             (var (τ ⇒ τ₁ ⟨ μ₁ , σ₁ ⟩ τ₂ ⟨ μ₂ , σα ⟩ α) →
              Exp var τ₀ μ₀ σ₀ τ₀' μ₀' σ₀' β) →
             Exp var τ μα σα α μβ (τ₀ ⇨⟨ μ₀ , σ₀ ⟩ τ₀' × μ₀' ∷ σ₀') β
  Prompt0  : {τ α β γ γ' : Ty} {μα μβ μid : Tr} {σα σβ σid : Mc} →
             id-cont-type γ μid σid γ' →
             Exp var γ μid σid γ' ●μ (τ ⇨⟨ μα , σα ⟩ α × μβ ∷ σβ) β →
             Exp var τ μα σα α μβ σβ β

-- Interpretation of types
〚_〛τ : Ty → Set
〚_〛μ : Tr → Set
〚_〛σ : Mc → Set

〚 Nat 〛τ = ℕ
〚 Bool 〛τ = 𝔹
〚 τ₂ ⇒ τ₁ ⟨ μα , σα ⟩ α ⟨ μβ , σβ ⟩ β 〛τ =
  〚 τ₂ 〛τ → (〚 τ₁ 〛τ → 〚 μα 〛μ → 〚 σα 〛σ → 〚 α 〛τ) →
  〚 μβ 〛μ → 〚 σβ 〛σ → 〚 β 〛τ

〚 ●μ 〛μ = ⊤
〚 τ ⇨⟨ μ , σ ⟩ τ' 〛μ = 〚 τ 〛τ → 〚 μ 〛μ → 〚 σ 〛σ → 〚 τ' 〛τ

〚 ●σ 〛σ = ⊤
〚 τ ⇨⟨ μ , σ ⟩ τ' × μ' ∷ σ' 〛σ =
  ((〚 τ 〛τ → 〚 μ 〛μ → 〚 σ 〛σ → 〚 τ' 〛τ) × 〚 μ' 〛μ) × 〚 σ' 〛σ

-- Trail composition
compose-trail : {μ₁ μ₂ μ₃ : Tr} →
                compatible μ₁ μ₂ μ₃ → 〚 μ₁ 〛μ → 〚 μ₂ 〛μ → 〚 μ₃ 〛μ
compose-trail {●μ} refl tt t2 = t2
compose-trail {τ₁ ⇨⟨ μ₁ , σ₁ ⟩ τ₁'} {●μ} refl t1 tt = t1
compose-trail {τ₁ ⇨⟨ μ₁ , σ₁ ⟩ τ₁'} {τ₂ ⇨⟨ μ₂ , σ₂ ⟩ τ₂'} {.τ₁ ⇨⟨ μ₃ , .σ₁ ⟩ .τ₁'} (refl , refl , refl , c) t1 t2 =
  λ v t' m' → t1 v (compose-trail c t2 t') m'

-- Initial continuation
idk : {τ τ' : Ty} → {μ : Tr} → {σ : Mc} →
      id-cont-type τ μ σ τ' →
      〚 τ 〛τ → 〚 μ 〛μ → 〚 σ 〛σ → 〚 τ' 〛τ
idk {μ = ●μ} {●σ} refl v tt tt = v
idk {μ = ●μ} {x ⇨⟨ x₁ , σ ⟩ x₂ × .x₁ ∷ .σ} (refl , refl , refl , refl) v tt ((k₀ , t₀) , m₀) = k₀ v t₀ m₀
idk {μ = x₁ ⇨⟨ .●μ , x₃ ⟩ x₄} (refl , refl , refl , refl) v t m = t v tt m

-- Interpretation of terms
g : {var : Ty → Set} {τ α β : Ty} {μα μβ : Tr} {σα σβ : Mc} →
    Exp 〚_〛τ τ μα σα α μβ σβ β →
    (〚 τ 〛τ → 〚 μα 〛μ → 〚 σα 〛σ → 〚 α 〛τ) →
    〚 μβ 〛μ → 〚 σβ 〛σ → 〚 β 〛τ
g (Var x) k t m = k x t m
g (Num n) k t m = k n t m
g (Bol b) k t m = k b t m
g (Lam f) k t m = k (λ x t₁ m₁ → g {var = 〚_〛τ} (f x) t₁ m₁) t m
g (App e₁ e₂) k t m =
  g {var = 〚_〛τ} e₁
    (λ v₁ t₁ m₁ → g {var = 〚_〛τ} e₂ (λ v₂ t₂ m₂ → v₁ v₂ k t₂ m₂) t₁ m₁) t m
g (Shift is-id f) k t m = g {var = 〚_〛τ} (f (λ v k' t' m' → k v t (((k' , t') , m')))) (idk is-id) tt m
g (Shift0 f) k t ((k₀ , t₀) , m₀) = g {var = 〚_〛τ} (f (λ v k' t' m' → k v t ((k' , t') , m'))) k₀ t₀ m₀
g (Control is-id c₁ c₂ f) k t m =
  g {var = 〚_〛τ}
    (f (λ v k' t' m' → k v (compose-trail c₂ t (compose-trail c₁ k' t')) m'))
    (idk is-id) tt m
g (Control0 c₁ c₂ f) k t ((k₀ , t₀) , m₀) =
  g {var = 〚_〛τ}
    (f (λ v k' t' m' → k v (compose-trail c₂ t (compose-trail c₁ k' t')) m'))
    k₀ t₀ m₀
g (Prompt0 is-id e) k t m =
  g {var = 〚_〛τ} e (idk is-id) tt ((k , t) , m)

-- Top-level evaluation
go : {τ : Ty} {μ : Tr} → id-cont-type τ μ ●σ τ → Exp 〚_〛τ τ μ ●σ τ μ ●σ τ → 〚 τ 〛τ
go {μ = ●μ} refl e = g {var = 〚_〛τ} e (λ z _ _ → z) tt tt
go {μ = τ₁ ⇨⟨ ●μ , σ ⟩ τ₁} (refl , refl , refl , refl) e =
  g {var = 〚_〛τ} e (λ z _ _ → z) (λ t _ _ → t) tt
