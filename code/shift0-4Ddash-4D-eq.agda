module shift0-4Ddash-4D-eq where

open import shift0-4Ddash renaming (Ty to Ty'; Mc to Mc'; Exp to Exp')
open import shift0-4D
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Bool using (true; false; if_then_else_) renaming (Bool to 𝔹)
open import Data.String using (String)
open import Function using (_∘_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning

-- Type-level translation from 4Ddash to 4D
[_]* : Ty' → Ty
[_]m* : Mc' → Mc

-- Term type translation
[ Nat ]* = Nat
[ Bool ]* = Bool
[ τ₂ ⇒ τ₁ , σα , α , σβ , β ]* =
  _⇒_⟨_,_⟩_⟨_,_⟩_
    [ τ₂ ]* [ τ₁ ]*
    ●μ [ σα ]m* [ α ]*
    ●μ [ σβ ]m* [ β ]*

-- Meta continuation type translation
[ ●σ ]m* = ●σ
[ τ ⇨ σ , τ₁ ∷ σ₁ ]m* =
  _⇨⟨_,_⟩_×_∷_ [ τ ]* ●μ [ σ ]m* [ τ₁ ]* ●μ [ σ₁ ]m*

4Ddash-to-4D : {var : Ty → Set} {τ α β : Ty'} {σα σβ : Mc'} →
               Exp' (var ∘ [_]*) τ σα α σβ β →
               Exp var [ τ ]* ●μ [ σα ]m* [ α ]* ●μ [ σβ ]m* [ β ]*
4Ddash-to-4D (Var x) = Var x
4Ddash-to-4D (Num n) = Num n
4Ddash-to-4D (Bol b) = Bol b
4Ddash-to-4D (Lam e) = Lam (λ x → 4Ddash-to-4D (e x))
4Ddash-to-4D (App e₁ e₂) = App (4Ddash-to-4D e₁) (4Ddash-to-4D e₂)
4Ddash-to-4D (Shift0 e) = Shift0 (λ k → 4Ddash-to-4D (e k))
4Ddash-to-4D (Reset0 {β = β} {β'} {σ' = σ'} e) =
  Prompt0 {σid = [ β ⇨ σ' , β' ∷ σ' ]m*} (refl , refl , refl , refl) (4Ddash-to-4D e)

-- Type-level translation from 4D to 4Ddash
[_]** : Ty → Ty'
[_]m** : Mc → Mc'

-- Term type translation
[ Nat ]** = Nat
[ Bool ]** = Bool
[ τ₁ ⇒ τ₂ ⟨ μ₁ , σ₁ ⟩ α ⟨ μ₂ , σ₂ ⟩ β ]** =
  _⇒_,_,_,_,_ [ τ₁ ]** [ τ₂ ]** [ σ₁ ]m** [ α ]** [ σ₂ ]m** [ β ]**

-- Meta continuation type translation
[ ●σ ]m** = ●σ
[ τ₁ ⇨⟨ μ₁ , σ₁ ⟩ τ₂ × μ₂ ∷ σ₂ ]m** =
  _⇨_,_∷_ [ τ₁ ]** [ σ₁ ]m** [ τ₂ ]** [ σ₂ ]m**

4D-to-4Ddash : {var : Ty' → Set} {τ α β : Ty} {μα μβ : Tr} {σα σβ : Mc} →
               Exp (var ∘ [_]**) τ μα σα α μβ σβ β →
               Exp' var [ τ ]** [ σα ]m** [ α ]** [ σβ ]m** [ β ]**
4D-to-4Ddash (Var x) = Var x
4D-to-4Ddash (Num n) = Num n
4D-to-4Ddash (Bol b) = Bol b
4D-to-4Ddash (Lam e) = Lam (λ x → 4D-to-4Ddash (e x))
4D-to-4Ddash (App e₁ e₂) = App (4D-to-4Ddash e₁) (4D-to-4Ddash e₂)
4D-to-4Ddash (Shift0 e) = Shift0 (λ k → 4D-to-4Ddash (e k))
4D-to-4Ddash (Prompt0 {μid = ●μ} (refl , refl , refl , refl) e) = Reset0 (4D-to-4Ddash e)
4D-to-4Ddash (Prompt0 {μid = τ₁ ⇨⟨ ●μ , (τ₁ ⇨⟨ _ , _ ⟩ τ₂ × _ ∷ _) ⟩ τ₂} (refl , refl , refl , refl) e) = Reset0 (4D-to-4Ddash e)
