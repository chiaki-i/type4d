-- Translation between DF and DF2 (for shift/reset)

module shift-DF-DF2-eq where

open import shift-DF renaming (Ty to Ty1; Tm to Tm1)
open import shift-DF2 renaming (Ty to Ty2; Mc to Mc2; Exp to Tm2)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Bool using (true; false; if_then_else_) renaming (Bool to 𝔹)
open import Data.String using (String)
open import Function using (_∘_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning

-- Type-level translation from DF (1CPS) to DF2 (2CPS)
[_,_]* : (γ : Ty2) → Ty1 → Ty2
[ γ , Nat ]* = Nat
[ γ , Bool ]* = Bool
[ γ , Str ]* = Str
[ γ , τ₂ ⇒ τ₁ [ α , β ] ]* =
  _⇒_⟨_⟩_⟨_⟩_
    [ γ , τ₂ ]* [ γ , τ₁ ]*
    ([ γ , α ]* ⇨ γ) γ
    ([ γ , β ]* ⇨ γ) γ

-- Theorem 5.1 (1)
One-to-Two : {var : Ty2 → Set} {τ α β : Ty1} {γ : Ty2} →
             Tm1 (var ∘ ([_,_]* γ )) τ α β →
             Tm2 var [ γ , τ ]*
             ([ γ , α ]* ⇨ γ) γ
             ([ γ , β ]* ⇨ γ) γ
One-to-Two (Num n) = Num n
One-to-Two (Bol b) = Bol b
One-to-Two (Var x) = Var x
One-to-Two (Lam e) = Lam (λ x → One-to-Two (e x))
One-to-Two (App e₁ e₂) = App (One-to-Two e₁) (One-to-Two e₂)
One-to-Two (Sft e) = Shift (λ k → One-to-Two (e k))
One-to-Two (Rst e) = Reset (One-to-Two e)

-- Type-level translation from DF2 (2CPS, Tm2) to DF (1CPS, Tm1)
[_]** : Ty2 → Ty1
[ Nat ]** = Nat
[ Bool ]** = Bool
[ Str ]** = Str
[ τ₁ ⇒ τ₂ ⟨ α ⇨ γ₁ ⟩ γ₂ ⟨ β ⇨ γ₃ ⟩ γ₄ ]** = [ τ₁ ]** ⇒ [ τ₂ ]** [ [ α ]** , [ β ]** ]

-- Theorem 5.1 (2)
Two-to-One : {var : Ty1 → Set} {τ α β γ₁ γ₂ γ₃ γ₄ : Ty2} →
             Tm2 (var ∘ [_]**) τ (α ⇨ γ₁) γ₂ (β ⇨ γ₃) γ₄ →
             Tm1 var [ τ ]** [ α ]** [ β ]**
Two-to-One (Var x) = Var x
Two-to-One (Num n) = Num n
Two-to-One (Bol b) = Bol b
Two-to-One (Lam {σα = x ⇨ x₁} {x₂ ⇨ x₃} e) = Lam (λ x → Two-to-One (e x))
Two-to-One (App {σβ = x ⇨ x₁} {x₂ ⇨ x₃} e₁ e₂) = App (Two-to-One e₁) (Two-to-One e₂)
Two-to-One (Shift {σ₁ = x ⇨ x₁} e) = Sft (λ k → Two-to-One (e k))
Two-to-One (Reset e) = Rst (Two-to-One e)
