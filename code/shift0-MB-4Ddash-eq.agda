{-# OPTIONS --rewriting #-}

-- Translation between MB and 4Ddash (for shift0/reset0)

module shift0-MB-4Ddash-eq where

open import shift0-4Ddash
open import shift0-MB
  renaming (Ty to TyMB; Ann to AnnMB; Exp to ExpMB)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to _,p_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

-- Translation into MB, for types
toMB-Ty : Ty → TyMB
toMB-Mc : Mc → Ty → Mc → Ty → AnnMB
toMB-Mc' : Mc → Ty → TyMB × AnnMB

toMB-Ty Nat = Nat
toMB-Ty Bool = Bool
toMB-Ty (τ₁ ⇒ τ₂ , σα , α , σβ , β) =
  let pα = toMB-Mc' σα α in
  let pβ = toMB-Mc' σβ β in
  toMB-Ty τ₁ ⇒ toMB-Ty τ₂ ,[ proj₁ pα , proj₂ pα ] proj₁ pβ , proj₂ pβ
  -- toMB-Ty τ₁ ⇒ toMB-Ty τ₂ ,[ σα , α ] σβ , β

toMB-Mc σα α σβ β =
  let pα = toMB-Mc' σα α in
  let pβ = toMB-Mc' σβ β in
  [ proj₁ pα , proj₂ pα ] proj₁ pβ , proj₂ pβ

-- Second argument represents answer type
-- Goes to tail position of resulting annotation
toMB-Mc' ●σ τ = toMB-Ty τ ,p ε
toMB-Mc' (τ ⇨ σ , τ' ∷ σ') τ₁ =
  let p₁ = toMB-Mc' σ τ' in
  let p₂ = toMB-Mc' σ' τ₁ in
  toMB-Ty τ ,p ([ proj₁ p₁ , proj₂ p₁ ] proj₁ p₂ , proj₂ p₂)

-- Translation from MB, for types
fromMB-Ty : TyMB → Ty
fromMB-Ann : TyMB → AnnMB → Mc × Ty

fromMB-Ty Nat = Nat
fromMB-Ty Bool = Bool
fromMB-Ty (τ₁ ⇒ τ₂ ,[ τ , σ ] τ' , σ') =
  let pα = fromMB-Ann τ σ in
  let pβ = fromMB-Ann τ' σ' in
  fromMB-Ty τ₁ ⇒ fromMB-Ty τ₂ ,
                 proj₁ pα , proj₂ pα , proj₁ pβ , proj₂ pβ

fromMB-Ann τ ε = ●σ ,p fromMB-Ty τ
fromMB-Ann τ₁ ([ τ , σ ] τ' , σ') =
  let pα = fromMB-Ann τ σ in
  let pβ = fromMB-Ann τ' σ' in
  (fromMB-Ty τ₁ ⇨ proj₁ pα , proj₂ pα ∷ proj₁ pβ) ,p proj₂ pβ

-- Converting into MB and back is identity
from-to-Ty : (τ : Ty) → fromMB-Ty (toMB-Ty τ) ≡ τ
from-to-Mc-σ : (σ : Mc) (α : Ty) →
  let p = toMB-Mc' σ α in
  proj₁ (fromMB-Ann (proj₁ p) (proj₂ p)) ≡ σ
from-to-Mc-α : (σ : Mc) (α : Ty) →
  let p = toMB-Mc' σ α in
  proj₂ (fromMB-Ann (proj₁ p) (proj₂ p)) ≡ α

from-to-Ty Nat = refl
from-to-Ty Bool = refl
from-to-Ty (τ₁ ⇒ τ₂ , σα , α , σβ , β) =
  begin
    fromMB-Ty (toMB-Ty (τ₁ ⇒ τ₂ , σα , α , σβ , β))
  ≡⟨ refl ⟩
    fromMB-Ty
      (let pα = toMB-Mc' σα α in
       let pβ = toMB-Mc' σβ β in
       toMB-Ty τ₁ ⇒ toMB-Ty τ₂
       ,[ proj₁ pα , proj₂ pα ] proj₁ pβ , proj₂ pβ)
  ≡⟨ refl ⟩
    let pα = fromMB-Ann (proj₁ (toMB-Mc' σα α)) (proj₂ (toMB-Mc' σα α)) in
    let pβ = fromMB-Ann (proj₁ (toMB-Mc' σβ β)) (proj₂ (toMB-Mc' σβ β)) in
    fromMB-Ty (toMB-Ty τ₁) ⇒ fromMB-Ty (toMB-Ty τ₂) ,
                             proj₁ pα , proj₂ pα , proj₁ pβ , proj₂ pβ
  ≡⟨ cong (λ x →
    let pα = fromMB-Ann (proj₁ (toMB-Mc' σα α)) (proj₂ (toMB-Mc' σα α)) in
    let pβ = fromMB-Ann (proj₁ (toMB-Mc' σβ β)) (proj₂ (toMB-Mc' σβ β)) in
    x ⇒ fromMB-Ty (toMB-Ty τ₂) , proj₁ pα , proj₂ pα , proj₁ pβ , proj₂ pβ)
          (from-to-Ty τ₁) ⟩
    let pα = fromMB-Ann (proj₁ (toMB-Mc' σα α)) (proj₂ (toMB-Mc' σα α)) in
    let pβ = fromMB-Ann (proj₁ (toMB-Mc' σβ β)) (proj₂ (toMB-Mc' σβ β)) in
    τ₁ ⇒ fromMB-Ty (toMB-Ty τ₂) , proj₁ pα , proj₂ pα , proj₁ pβ , proj₂ pβ
  ≡⟨ cong (λ x →
    let pα = fromMB-Ann (proj₁ (toMB-Mc' σα α)) (proj₂ (toMB-Mc' σα α)) in
    let pβ = fromMB-Ann (proj₁ (toMB-Mc' σβ β)) (proj₂ (toMB-Mc' σβ β)) in
    τ₁ ⇒ x , proj₁ pα , proj₂ pα , proj₁ pβ , proj₂ pβ)
          (from-to-Ty τ₂) ⟩
    let pα = fromMB-Ann (proj₁ (toMB-Mc' σα α)) (proj₂ (toMB-Mc' σα α)) in
    let pβ = fromMB-Ann (proj₁ (toMB-Mc' σβ β)) (proj₂ (toMB-Mc' σβ β)) in
    τ₁ ⇒ τ₂ , proj₁ pα , proj₂ pα , proj₁ pβ , proj₂ pβ
  ≡⟨ cong (λ x →
    let pα = fromMB-Ann (proj₁ (toMB-Mc' σα α)) (proj₂ (toMB-Mc' σα α)) in
    let pβ = fromMB-Ann (proj₁ (toMB-Mc' σβ β)) (proj₂ (toMB-Mc' σβ β)) in
    τ₁ ⇒ τ₂ , x , proj₂ pα , proj₁ pβ , proj₂ pβ)
          (from-to-Mc-σ σα α) ⟩
    let pα = fromMB-Ann (proj₁ (toMB-Mc' σα α)) (proj₂ (toMB-Mc' σα α)) in
    let pβ = fromMB-Ann (proj₁ (toMB-Mc' σβ β)) (proj₂ (toMB-Mc' σβ β)) in
    τ₁ ⇒ τ₂ , σα , proj₂ pα , proj₁ pβ , proj₂ pβ
  ≡⟨ cong (λ x →
    let pα = fromMB-Ann (proj₁ (toMB-Mc' σα α)) (proj₂ (toMB-Mc' σα α)) in
    let pβ = fromMB-Ann (proj₁ (toMB-Mc' σβ β)) (proj₂ (toMB-Mc' σβ β)) in
    τ₁ ⇒ τ₂ , σα , x , proj₁ pβ , proj₂ pβ)
          (from-to-Mc-α σα α) ⟩
    let pα = fromMB-Ann (proj₁ (toMB-Mc' σα α)) (proj₂ (toMB-Mc' σα α)) in
    let pβ = fromMB-Ann (proj₁ (toMB-Mc' σβ β)) (proj₂ (toMB-Mc' σβ β)) in
    τ₁ ⇒ τ₂ , σα , α , proj₁ pβ , proj₂ pβ
  ≡⟨ cong (λ x →
    let pα = fromMB-Ann (proj₁ (toMB-Mc' σα α)) (proj₂ (toMB-Mc' σα α)) in
    let pβ = fromMB-Ann (proj₁ (toMB-Mc' σβ β)) (proj₂ (toMB-Mc' σβ β)) in
    τ₁ ⇒ τ₂ , σα , α , x , proj₂ pβ)
          (from-to-Mc-σ σβ β) ⟩
    let pα = fromMB-Ann (proj₁ (toMB-Mc' σα α)) (proj₂ (toMB-Mc' σα α)) in
    let pβ = fromMB-Ann (proj₁ (toMB-Mc' σβ β)) (proj₂ (toMB-Mc' σβ β)) in
    τ₁ ⇒ τ₂ , σα , α , σβ , proj₂ pβ
  ≡⟨ cong (λ x →
    let pα = fromMB-Ann (proj₁ (toMB-Mc' σα α)) (proj₂ (toMB-Mc' σα α)) in
    let pβ = fromMB-Ann (proj₁ (toMB-Mc' σβ β)) (proj₂ (toMB-Mc' σβ β)) in
    τ₁ ⇒ τ₂ , σα , α , σβ , x)
          (from-to-Mc-α σβ β) ⟩
    τ₁ ⇒ τ₂ , σα , α , σβ , β
  ∎

from-to-Mc-σ ●σ α = refl
from-to-Mc-σ (τ ⇨ σ , τ' ∷ σ') α =
  begin
    let p = toMB-Mc' (τ ⇨ σ , τ' ∷ σ') α in
    proj₁ (fromMB-Ann (proj₁ p) (proj₂ p))
  ≡⟨ refl ⟩
    let p = let p₁ = toMB-Mc' σ τ' in
            let p₂ = toMB-Mc' σ' α in
            toMB-Ty τ ,p ([ proj₁ p₁ , proj₂ p₁ ] proj₁ p₂ , proj₂ p₂) in
    proj₁ (fromMB-Ann (proj₁ p) (proj₂ p))
  ≡⟨ refl ⟩
    proj₁ {B = λ _ → Ty} (
      let pα = fromMB-Ann (proj₁ (toMB-Mc' σ τ')) (proj₂ (toMB-Mc' σ τ')) in
      let pβ = fromMB-Ann (proj₁ (toMB-Mc' σ' α)) (proj₂ (toMB-Mc' σ' α)) in
      (fromMB-Ty (toMB-Ty τ) ⇨ proj₁ pα , proj₂ pα ∷ proj₁ pβ) ,p proj₂ pβ)
   ≡⟨ cong (λ x → proj₁ {B = λ _ → Ty} (
      let pα = fromMB-Ann (proj₁ (toMB-Mc' σ τ')) (proj₂ (toMB-Mc' σ τ')) in
      let pβ = fromMB-Ann (proj₁ (toMB-Mc' σ' α)) (proj₂ (toMB-Mc' σ' α)) in
      (x ⇨ proj₁ pα , proj₂ pα ∷ proj₁ pβ) ,p proj₂ pβ))
      (from-to-Ty τ) ⟩
    proj₁ {B = λ _ → Ty} (
      let pα = fromMB-Ann (proj₁ (toMB-Mc' σ τ')) (proj₂ (toMB-Mc' σ τ')) in
      let pβ = fromMB-Ann (proj₁ (toMB-Mc' σ' α)) (proj₂ (toMB-Mc' σ' α)) in
      (τ ⇨ proj₁ pα , proj₂ pα ∷ proj₁ pβ) ,p proj₂ pβ)
   ≡⟨ cong (λ x → proj₁ {B = λ _ → Ty} (
      let pα = fromMB-Ann (proj₁ (toMB-Mc' σ τ')) (proj₂ (toMB-Mc' σ τ')) in
      let pβ = fromMB-Ann (proj₁ (toMB-Mc' σ' α)) (proj₂ (toMB-Mc' σ' α)) in
      (τ ⇨ x , proj₂ pα ∷ proj₁ pβ) ,p proj₂ pβ))
           (from-to-Mc-σ σ τ') ⟩
    proj₁ {B = λ _ → Ty} (
      let pα = fromMB-Ann (proj₁ (toMB-Mc' σ τ')) (proj₂ (toMB-Mc' σ τ')) in
      let pβ = fromMB-Ann (proj₁ (toMB-Mc' σ' α)) (proj₂ (toMB-Mc' σ' α)) in
      (τ ⇨ σ , proj₂ pα ∷ proj₁ pβ) ,p proj₂ pβ)
  ≡⟨ cong (λ x → proj₁ {B = λ _ → Ty} (
      let pα = fromMB-Ann (proj₁ (toMB-Mc' σ τ')) (proj₂ (toMB-Mc' σ τ')) in
      let pβ = fromMB-Ann (proj₁ (toMB-Mc' σ' α)) (proj₂ (toMB-Mc' σ' α)) in
      (τ ⇨ σ , x ∷ proj₁ pβ) ,p proj₂ pβ))
           (from-to-Mc-α σ τ') ⟩
    proj₁ {B = λ _ → Ty} (
      let pα = fromMB-Ann (proj₁ (toMB-Mc' σ τ')) (proj₂ (toMB-Mc' σ τ')) in
      let pβ = fromMB-Ann (proj₁ (toMB-Mc' σ' α)) (proj₂ (toMB-Mc' σ' α)) in
      (τ ⇨ σ , τ' ∷ proj₁ pβ) ,p proj₂ pβ)
  ≡⟨ cong (λ x → proj₁ {B = λ _ → Ty} (
      let pα = fromMB-Ann (proj₁ (toMB-Mc' σ τ')) (proj₂ (toMB-Mc' σ τ')) in
      let pβ = fromMB-Ann (proj₁ (toMB-Mc' σ' α)) (proj₂ (toMB-Mc' σ' α)) in
      (τ ⇨ σ , τ' ∷ x) ,p proj₂ pβ))
           (from-to-Mc-σ σ' α) ⟩
    proj₁ {B = λ _ → Ty} (
      let pα = fromMB-Ann (proj₁ (toMB-Mc' σ τ')) (proj₂ (toMB-Mc' σ τ')) in
      let pβ = fromMB-Ann (proj₁ (toMB-Mc' σ' α)) (proj₂ (toMB-Mc' σ' α)) in
      (τ ⇨ σ , τ' ∷ σ') ,p proj₂ pβ)
  ≡⟨ refl ⟩
    τ ⇨ σ , τ' ∷ σ'
  ∎

from-to-Mc-α ●σ α = from-to-Ty α
from-to-Mc-α (τ ⇨ σ , τ' ∷ σ') α =
  begin
    let p = toMB-Mc' (τ ⇨ σ , τ' ∷ σ') α in
    proj₂ (fromMB-Ann (proj₁ p) (proj₂ p))
  ≡⟨ refl ⟩
    let p = let p₁ = toMB-Mc' σ τ' in
            let p₂ = toMB-Mc' σ' α in
            toMB-Ty τ ,p ([ proj₁ p₁ , proj₂ p₁ ] proj₁ p₂ , proj₂ p₂) in
    proj₂ (fromMB-Ann (proj₁ p) (proj₂ p))
  ≡⟨ refl ⟩
    proj₂ {B = λ _ → Ty} (
      let pα = fromMB-Ann (proj₁ (toMB-Mc' σ τ')) (proj₂ (toMB-Mc' σ τ')) in
      let pβ = fromMB-Ann (proj₁ (toMB-Mc' σ' α)) (proj₂ (toMB-Mc' σ' α)) in
      (fromMB-Ty (toMB-Ty τ) ⇨ proj₁ pα , proj₂ pα ∷ proj₁ pβ) ,p proj₂ pβ)
  ≡⟨ refl ⟩
    proj₂ {B = λ _ → Ty}
      (fromMB-Ann (proj₁ (toMB-Mc' σ' α)) (proj₂ (toMB-Mc' σ' α)))
  ≡⟨ from-to-Mc-α σ' α ⟩
    α
  ∎

{-# REWRITE from-to-Ty from-to-Mc-σ from-to-Mc-α #-}
-- Translation into MB, for expressions
toMB-Exp : {var : Ty → Set} {τ α β : Ty} {σα σβ : Mc} →
           Exp var τ σα α σβ β →
           ExpMB (var ∘ fromMB-Ty) (toMB-Ty τ) (toMB-Mc σα α σβ β)

toMB-Exp (Var x) = Var x

toMB-Exp (Num n) = Num n

toMB-Exp (Bol b) = Bol b

toMB-Exp (Lam f) = Lam (λ x → toMB-Exp (f x))

toMB-Exp (App e₁ e₂) = App (toMB-Exp e₁) (toMB-Exp e₂)

toMB-Exp (Shift0 f) =  Shift0 (λ k → toMB-Exp (f k))

toMB-Exp {var} (Reset0 e) = Reset0 (toMB-Exp e)

-- Converting from MB and back is identity
to-from-Ty : (τ : TyMB) → toMB-Ty (fromMB-Ty τ) ≡ τ
to-from-Ann-α : (τ : TyMB) (σ : AnnMB) →
                proj₁ (toMB-Mc' (proj₁ (fromMB-Ann τ σ)) (proj₂ (fromMB-Ann τ σ))) ≡ τ
to-from-Ann-σ : (τ : TyMB) (σ : AnnMB) →
                proj₂ (toMB-Mc' (proj₁ (fromMB-Ann τ σ)) (proj₂ (fromMB-Ann τ σ))) ≡ σ

to-from-Ty Nat = refl
to-from-Ty Bool = refl

to-from-Ty (τ₁ ⇒ τ₂ ,[ τ , σ ] τ' , σ') =
  begin
    toMB-Ty (fromMB-Ty (τ₁ ⇒ τ₂ ,[ τ , σ ] τ' , σ'))
  ≡⟨ refl ⟩
    toMB-Ty (let pα = fromMB-Ann τ σ in
             let pβ = fromMB-Ann τ' σ' in
             fromMB-Ty τ₁ ⇒ fromMB-Ty τ₂ ,
                            proj₁ pα , proj₂ pα , proj₁ pβ , proj₂ pβ)
  ≡⟨ refl ⟩
    toMB-Ty (fromMB-Ty τ₁ ⇒ fromMB-Ty τ₂ ,
                            proj₁ (fromMB-Ann τ σ) , proj₂ (fromMB-Ann τ σ) ,
                            proj₁ (fromMB-Ann τ' σ') , proj₂ (fromMB-Ann τ' σ'))
  ≡⟨ refl ⟩
    let pα = toMB-Mc' (proj₁ (fromMB-Ann τ σ)) (proj₂ (fromMB-Ann τ σ)) in
    let pβ = toMB-Mc' (proj₁ (fromMB-Ann τ' σ')) (proj₂ (fromMB-Ann τ' σ')) in
    toMB-Ty (fromMB-Ty τ₁) ⇒ toMB-Ty (fromMB-Ty τ₂)
    ,[ (proj₁ pα) , (proj₂ pα) ] (proj₁ pβ) , (proj₂ pβ)
  ≡⟨ cong (λ x →
    let pα = toMB-Mc' (proj₁ (fromMB-Ann τ σ)) (proj₂ (fromMB-Ann τ σ)) in
    let pβ = toMB-Mc' (proj₁ (fromMB-Ann τ' σ')) (proj₂ (fromMB-Ann τ' σ')) in
    x ⇒ toMB-Ty (fromMB-Ty τ₂)
    ,[ (proj₁ pα) , (proj₂ pα) ] (proj₁ pβ) , (proj₂ pβ) )
          (to-from-Ty τ₁) ⟩
    let pα = toMB-Mc' (proj₁ (fromMB-Ann τ σ)) (proj₂ (fromMB-Ann τ σ)) in
    let pβ = toMB-Mc' (proj₁ (fromMB-Ann τ' σ')) (proj₂ (fromMB-Ann τ' σ')) in
    τ₁ ⇒ toMB-Ty (fromMB-Ty τ₂)
    ,[ (proj₁ pα) , (proj₂ pα) ] (proj₁ pβ) , (proj₂ pβ)
  ≡⟨ cong (λ x →
    let pα = toMB-Mc' (proj₁ (fromMB-Ann τ σ)) (proj₂ (fromMB-Ann τ σ)) in
    let pβ = toMB-Mc' (proj₁ (fromMB-Ann τ' σ')) (proj₂ (fromMB-Ann τ' σ')) in
    τ₁ ⇒ x
    ,[ (proj₁ pα) , (proj₂ pα) ] (proj₁ pβ) , (proj₂ pβ) )
          (to-from-Ty τ₂) ⟩
    let pα = toMB-Mc' (proj₁ (fromMB-Ann τ σ)) (proj₂ (fromMB-Ann τ σ)) in
    let pβ = toMB-Mc' (proj₁ (fromMB-Ann τ' σ')) (proj₂ (fromMB-Ann τ' σ')) in
    τ₁ ⇒ τ₂
    ,[ (proj₁ pα) , (proj₂ pα) ] (proj₁ pβ) , (proj₂ pβ)
  ≡⟨ cong (λ x →
    let pα = toMB-Mc' (proj₁ (fromMB-Ann τ σ)) (proj₂ (fromMB-Ann τ σ)) in
    let pβ = toMB-Mc' (proj₁ (fromMB-Ann τ' σ')) (proj₂ (fromMB-Ann τ' σ')) in
    τ₁ ⇒ τ₂
    ,[ x , (proj₂ pα) ] (proj₁ pβ) , (proj₂ pβ) )
          (to-from-Ann-α τ σ) ⟩
    let pα = toMB-Mc' (proj₁ (fromMB-Ann τ σ)) (proj₂ (fromMB-Ann τ σ)) in
    let pβ = toMB-Mc' (proj₁ (fromMB-Ann τ' σ')) (proj₂ (fromMB-Ann τ' σ')) in
    τ₁ ⇒ τ₂
    ,[ τ , (proj₂ pα) ] (proj₁ pβ) , (proj₂ pβ)
  ≡⟨ cong (λ x →
    let pα = toMB-Mc' (proj₁ (fromMB-Ann τ σ)) (proj₂ (fromMB-Ann τ σ)) in
    let pβ = toMB-Mc' (proj₁ (fromMB-Ann τ' σ')) (proj₂ (fromMB-Ann τ' σ')) in
    τ₁ ⇒ τ₂
    ,[ τ , x ] (proj₁ pβ) , (proj₂ pβ) )
          (to-from-Ann-σ τ σ) ⟩
    let pα = toMB-Mc' (proj₁ (fromMB-Ann τ σ)) (proj₂ (fromMB-Ann τ σ)) in
    let pβ = toMB-Mc' (proj₁ (fromMB-Ann τ' σ')) (proj₂ (fromMB-Ann τ' σ')) in
    τ₁ ⇒ τ₂
    ,[ τ , σ ] (proj₁ pβ) , (proj₂ pβ)
  ≡⟨ cong (λ x →
    let pα = toMB-Mc' (proj₁ (fromMB-Ann τ σ)) (proj₂ (fromMB-Ann τ σ)) in
    let pβ = toMB-Mc' (proj₁ (fromMB-Ann τ' σ')) (proj₂ (fromMB-Ann τ' σ')) in
    τ₁ ⇒ τ₂
    ,[ τ , σ ] x , (proj₂ pβ) )
          (to-from-Ann-α τ' σ') ⟩
    let pα = toMB-Mc' (proj₁ (fromMB-Ann τ σ)) (proj₂ (fromMB-Ann τ σ)) in
    let pβ = toMB-Mc' (proj₁ (fromMB-Ann τ' σ')) (proj₂ (fromMB-Ann τ' σ')) in
    τ₁ ⇒ τ₂
    ,[ τ , σ ] τ' , (proj₂ pβ)
  ≡⟨ cong (λ x →
    let pα = toMB-Mc' (proj₁ (fromMB-Ann τ σ)) (proj₂ (fromMB-Ann τ σ)) in
    let pβ = toMB-Mc' (proj₁ (fromMB-Ann τ' σ')) (proj₂ (fromMB-Ann τ' σ')) in
    τ₁ ⇒ τ₂
    ,[ τ , σ ] τ' , x )
          (to-from-Ann-σ τ' σ') ⟩
    let pα = toMB-Mc' (proj₁ (fromMB-Ann τ σ)) (proj₂ (fromMB-Ann τ σ)) in
    let pβ = toMB-Mc' (proj₁ (fromMB-Ann τ' σ')) (proj₂ (fromMB-Ann τ' σ')) in
    τ₁ ⇒ τ₂ ,[ τ , σ ] τ' , σ'
  ≡⟨ refl ⟩
    τ₁ ⇒ τ₂ ,[ τ , σ ] τ' , σ'
  ∎

to-from-Ann-α α ε = to-from-Ty α
to-from-Ann-α α ([ τ , σ ] τ' , σ') = to-from-Ty α

to-from-Ann-σ α ε = refl
to-from-Ann-σ α ([ τ , σ ] τ' , σ') =
  begin
    [ proj₁ (toMB-Mc' (proj₁ (fromMB-Ann τ σ)) (proj₂ (fromMB-Ann τ σ))) ,
      proj₂ (toMB-Mc' (proj₁ (fromMB-Ann τ σ)) (proj₂ (fromMB-Ann τ σ))) ]
    proj₁ (toMB-Mc' (proj₁ (fromMB-Ann τ' σ')) (proj₂ (fromMB-Ann τ' σ'))) ,
    proj₂ (toMB-Mc' (proj₁ (fromMB-Ann τ' σ')) (proj₂ (fromMB-Ann τ' σ')))
  ≡⟨ cong (λ x → [ x , proj₂ (toMB-Mc' (proj₁ (fromMB-Ann τ σ)) (proj₂ (fromMB-Ann τ σ))) ]
                 proj₁ (toMB-Mc' (proj₁ (fromMB-Ann τ' σ')) (proj₂ (fromMB-Ann τ' σ'))) ,
                 proj₂ (toMB-Mc' (proj₁ (fromMB-Ann τ' σ')) (proj₂ (fromMB-Ann τ' σ'))))
          (to-from-Ann-α τ σ) ⟩
    [ τ , proj₂ (toMB-Mc' (proj₁ (fromMB-Ann τ σ)) (proj₂ (fromMB-Ann τ σ))) ]
    proj₁ (toMB-Mc' (proj₁ (fromMB-Ann τ' σ')) (proj₂ (fromMB-Ann τ' σ'))) ,
    proj₂ (toMB-Mc' (proj₁ (fromMB-Ann τ' σ')) (proj₂ (fromMB-Ann τ' σ')))
  ≡⟨ cong (λ x → [ τ , x ]
                 proj₁ (toMB-Mc' (proj₁ (fromMB-Ann τ' σ')) (proj₂ (fromMB-Ann τ' σ'))) ,
                 proj₂ (toMB-Mc' (proj₁ (fromMB-Ann τ' σ')) (proj₂ (fromMB-Ann τ' σ'))))
          (to-from-Ann-σ τ σ) ⟩
    [ τ , σ ]
    proj₁ (toMB-Mc' (proj₁ (fromMB-Ann τ' σ')) (proj₂ (fromMB-Ann τ' σ'))) ,
    proj₂ (toMB-Mc' (proj₁ (fromMB-Ann τ' σ')) (proj₂ (fromMB-Ann τ' σ')))
  ≡⟨ cong (λ x → [ τ , σ ] x , proj₂ (toMB-Mc' (proj₁ (fromMB-Ann τ' σ')) (proj₂ (fromMB-Ann τ' σ'))))
          (to-from-Ann-α τ' σ') ⟩
    [ τ , σ ] τ' , proj₂ (toMB-Mc' (proj₁ (fromMB-Ann τ' σ')) (proj₂ (fromMB-Ann τ' σ')))
  ≡⟨ cong (λ x → [ τ , σ ] τ' , x) (to-from-Ann-σ τ' σ') ⟩
    [ τ , σ ] τ' , σ'
  ∎

{-# REWRITE to-from-Ty to-from-Ann-α to-from-Ann-σ #-}
-- Translation from MB, for expressions
fromMB-Exp : {var : TyMB → Set} {τ α β : TyMB} {σα σβ : AnnMB} →
             ExpMB var τ ([ α , σα ] β , σβ) →
             let pα = fromMB-Ann α σα in
             let pβ = fromMB-Ann β σβ in
             Exp (var ∘ toMB-Ty) (fromMB-Ty τ) (proj₁ pα) (proj₂ pα) (proj₁ pβ) (proj₂ pβ)

fromMB-Exp (Var x) = Var x

fromMB-Exp (Num n) = Num n

fromMB-Exp (Bol b) = Bol b

fromMB-Exp (Lam f) = Lam (λ x → fromMB-Exp (f x))

fromMB-Exp (App e₁ e₂) = App (fromMB-Exp e₁) (fromMB-Exp e₂)

fromMB-Exp (Shift0 f) = Shift0 (λ k → fromMB-Exp (f k))

fromMB-Exp (Reset0 e) = Reset0 (fromMB-Exp e)
