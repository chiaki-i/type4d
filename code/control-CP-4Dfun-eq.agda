-- Translation between CP and 4Dfun

module control-CP-4Dfun-eq where

open import control-CP renaming (Ty to Ty1; Tr to Tr1; Exp to Tm1;
                             compatible to compatible1; is-id-trail to id-cont-type1)
open import control-4Dfun renaming (Ty to Ty2; Tr to Tr2; Mc to Mc2; Exp to Tm2;
                                  compatible to compatible2; id-cont-type to id-cont-type2)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Bool using (true; false; if_then_else_) renaming (Bool to 𝔹)
open import Data.String using (String)
open import Function using (_∘_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning

-- Type-level translations from CP to 4Dfun
[_,_]* : (γ : Ty2) → Ty1 → Ty2
[_,_]t* : (γ : Ty2) → Tr1 → Tr2

-- Translation for term type
[ γ , Nat ]* = Nat
[ γ , Bool ]* = Bool
[ γ , Str ]* = Str
[ γ , _⇒_,_,_,_,_ τ₂ τ₁ μ₁ α μ₂ β ]* =
  _⇒_⟨_,_⟩_⟨_,_⟩_
    [ γ , τ₂ ]* [ γ , τ₁ ]*
    [ γ , μ₁ ]t* ([ γ , α ]* ⇒ γ) γ
    [ γ , μ₂ ]t* ([ γ , β ]* ⇒ γ) γ

-- Translation for trail type
[ γ , ● ]t* = ●
[ γ , τ₂ ⇨ τ₁ , μ ]t* =
   [ γ , τ₂ ]* ⇨⟨ [ γ , μ ]t* , [ γ , τ₁ ]* ⇒ γ ⟩ γ

-- Translation for constraints
id* : {γ : Ty2} {τ₁ τ₂ : Ty1} {μ : Tr1} →
      id-cont-type1 τ₂ τ₁ μ →
      id-cont-type2 [ γ , τ₂ ]* [ γ , μ ]t* ([ γ , τ₁ ]* ⇒ γ) γ
id* {γ} {τ₁ = τ₂} {τ₂} {μ = ●}  refl  = refl , refl
id* {γ} {τ₁} {τ₂} {τ₂ ⇨ τ₁ , ●} (refl , refl , refl) = refl , refl , refl , refl , refl

com* : {γ : Ty2} {μ₁ μ₂ μ₃ : Tr1}  →
       compatible1 μ₁ μ₂ μ₃ →
       compatible2 [ γ , μ₁ ]t* [ γ , μ₂ ]t* [ γ , μ₃ ]t*
com* {γ} {●} {μ₂} {μ₂} refl = refl
com* {γ} {τ₁ ⇨ τ₁' , μ₁} {●} {τ₁ ⇨ τ₁' , μ₁} refl = refl
com* {γ} {τ₁ ⇨ τ₁' , μ₁} {τ₂ ⇨ τ₂' , μ₂} {τ₁ ⇨ τ₁' , μ₃} (refl , refl , c₂) =
  refl , refl , refl , com* c₂

-- Theorem 5.4 (1)
One-to-Two : {var : Ty2 → Set} {τ α β : Ty1} {μ₁ μ₂ : Tr1} {γ : Ty2} →
             Tm1 (var ∘ ([_,_]* γ)) τ μ₁ α μ₂ β →
             Tm2 var [ γ , τ ]*
               [ γ , μ₁ ]t* ([ γ , α ]* ⇒ γ) γ
               [ γ , μ₂ ]t* ([ γ , β ]* ⇒ γ) γ
One-to-Two (Var x) = Var x
One-to-Two (Num n) = Num n
One-to-Two (Bol b) = Bol b
One-to-Two (Lam e) = Lam (λ x → One-to-Two (e x))
One-to-Two (App e₁ e₂) = App (One-to-Two e₁) (One-to-Two e₂)
One-to-Two {γ = γ} (Control {γ' = γ'} {μid = μid} {μ₀ = μ₀} i₁ c₁ c₂ e) =
  Control {μ₀ = [ γ , μ₀ ]t*} (id* i₁) (com* c₁) (com* c₂) (λ k → One-to-Two (e k))
One-to-Two (Prompt i₁ e) = Reset (id* i₁) (One-to-Two e)

-- Type-level translation from 4Dfun to CP
[_]** : Ty2 → Ty1
[_]t** : Tr2 → Tr1

-- Translation for term type
[ Nat ]** = Nat
[ Bool ]** = Bool
[ Str ]** = Str
[ τ₁ ⇒ τ₂ ⟨ μ₁ , (α ⇒ γ₁) ⟩ γ₂ ⟨ μ₂ , (β ⇒ γ₃) ⟩ γ₄ ]** =
  _⇒_,_,_,_,_ [ τ₁ ]** [ τ₂ ]** [ μ₁ ]t** [ α ]** [ μ₂ ]t** [ β ]**

-- Translation for trail type
[ ● ]t** = ●
[ τ₁ ⇨⟨ μ , (γ₁ ⇒ γ₂) ⟩ τ₂ ]t** = _⇨_,_ [ τ₁ ]** [ τ₂ ]** [ μ ]t**

id** : {τ₁ τ₂ γ₁ γ₂ : Ty2} {μ : Tr2} {σ : Mc2} →
       id-cont-type2 τ₁ μ (γ₁ ⇒ γ₁) τ₂ →
       id-cont-type1 [ τ₁ ]** [ τ₂ ]** [ μ ]t**
id** {μ = ●} {γ₁ ⇒ γ₂} (refl , refl) = refl
id** {μ = τ ⇨⟨ ● , τ₁ ⇒ τ₁' ⟩ τ'} {γ₁ ⇒ γ₂} (refl , refl , refl , refl , refl) = refl , refl , refl

com** : {μ₁ μ₂ μ₃ : Tr2} →
        compatible2 μ₁ μ₂ μ₃ → compatible1 [ μ₁ ]t** [ μ₂ ]t** [ μ₃ ]t**
com** {●} {μ₂} {μ₃ = μ₂} refl = refl
com** {τ ⇨⟨ μ , γ ⇒ γ' ⟩ τ'} {●} {μ₃ = τ ⇨⟨ μ , γ ⇒ γ' ⟩ τ'} refl = refl
com** {τ₁ ⇨⟨ μ₁ , γ ⇒ γ' ⟩ τ₁'} {τ₂ ⇨⟨ μ₂ , γ₂ ⇒ γ₂' ⟩ τ₂'}
      {τ₁ ⇨⟨ μ₃ , γ ⇒ γ' ⟩ τ₁'} (refl , refl , refl , com) =
  refl , refl , com** com
