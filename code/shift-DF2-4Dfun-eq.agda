module shift-DF2-4Dfun-eq where

open import shift-4Dfun
open import shift-DF2 renaming (Ty to Ty2; Mc to Mc2; Exp to Tm2)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Bool using (true; false; if_then_else_) renaming (Bool to 𝔹)
open import Data.String using (String)
open import Function using (_∘_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning

-- Type-level translation from DF2 to 4Dfun
[_]* : Ty2 → Ty
[_]m* : Mc2 → Mc

-- Translation for term type
[ Nat ]* = Nat
[ Bool ]* = Bool
[ Str ]* = Str
[ τ₂ ⇒ τ₁ ⟨ σα ⟩ α ⟨ σβ ⟩ β ]* =
  _⇒_⟨_,_⟩_⟨_,_⟩_
    [ τ₂ ]* [ τ₁ ]*
    ● [ σα ]m* [ α ]*
    ● [ σβ ]m* [ β ]*

-- Translation for meta continuation type
[ τ₂ ⇨ τ₁ ]m* = [ τ₂ ]* ⇒ [ τ₁ ]*

-- Theorem 5.2 (1)
Two-to-4Dfun : {var : Ty → Set} {τ α β : Ty2} {σα σβ : Mc2} →
             Tm2 (var ∘ [_]*) τ σα α σβ β →
             Exp var [ τ ]* ● [ σα ]m* [ α ]* ● [ σβ ]m* [ β ]*
Two-to-4Dfun (Var x) = Var x
Two-to-4Dfun (Num n) = Num n
Two-to-4Dfun (Bol b) = Bol b
Two-to-4Dfun (Lam e) = Lam (λ x → Two-to-4Dfun (e x))
Two-to-4Dfun (App e₁ e₂) = App (Two-to-4Dfun e₁) (Two-to-4Dfun e₂)
Two-to-4Dfun (Shift e) = Shift (refl , refl) (λ k → Two-to-4Dfun (e k))
Two-to-4Dfun (Reset e) = Reset (refl , refl) (Two-to-4Dfun e)

-- Type-level translation from 4Dfun to DF2
r[_]* : Ty → Ty2
r[_]m* : Mc → Mc2
r[_]* Nat = Nat
r[_]* Bool = Bool
r[_]* Str = Str
r[_]* (_⇒_⟨_,_⟩_⟨_,_⟩_ τ₂ τ₁ μα σα α μβ σβ β) =
  _⇒_⟨_⟩_⟨_⟩_ r[ τ₂ ]* r[ τ₁ ]* r[ σα ]m* r[ α ]* r[ σβ ]m* r[ β ]*
r[ τ₁ ⇒ τ₂ ]m* = r[ τ₁ ]* ⇨ r[ τ₂ ]*

-- Theorem 5.2 (2)
4Dfun-to-Two : {var : Ty2 → Set} {τ α β : Ty} {μα μβ : Tr} {σα σβ : Mc} →
               Exp (var ∘ r[_]*) τ μα σα α μβ σβ β →
               Tm2 var r[ τ ]* r[ σα ]m* r[ α ]* r[ σβ ]m* r[ β ]*
4Dfun-to-Two (Var x) = Var x
4Dfun-to-Two (Num x) = Num x
4Dfun-to-Two (Bol x) = Bol x
4Dfun-to-Two (Lam e) = Lam (λ x → 4Dfun-to-Two (e x))
4Dfun-to-Two (App e₁ e₂) = App (4Dfun-to-Two e₁) (4Dfun-to-Two e₂)
4Dfun-to-Two (Shift {σid = τ₁ ⇒ τ₂} (refl , refl) e) = Shift (λ k → 4Dfun-to-Two (e k))
4Dfun-to-Two (Reset {σid = x₂ ⇒ x₃} (refl , refl) e) = Reset (4Dfun-to-Two e)
