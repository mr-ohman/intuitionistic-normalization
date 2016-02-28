module SystemTPO.Intended where

import Prelude as P
open P hiding (⊥; ⊤; fst; snd; case; ordrec)
open import SystemTPO.Syntax

⟦_⟧ : Type → Set
⟦ A ⇒ B ⟧ = ⟦ A ⟧ → ⟦ B ⟧
⟦ Nat ⟧ = ℕ
⟦ ⊥ ⟧ = P.⊥
⟦ ⊤ ⟧ = P.⊤
⟦ A ∧ B ⟧ = ⟦ A ⟧ × ⟦ B ⟧
⟦ A ∨ B ⟧ = ⟦ A ⟧ ⊎ ⟦ B ⟧
⟦ Ord ⟧ = O

⟦_⟧ₜ : {A : Type} → Term A → ⟦ A ⟧
⟦ K ⟧ₜ = λ x y → x
⟦ S ⟧ₜ = λ g f x → g x (f x)
⟦ app c a ⟧ₜ = ⟦ c ⟧ₜ ⟦ a ⟧ₜ
⟦ zero ⟧ₜ = zero
⟦ suc a ⟧ₜ = suc ⟦ a ⟧ₜ
⟦ rec d e ⟧ₜ = natrec ⟦ d ⟧ₜ ⟦ e ⟧ₜ
⟦ case0 ⟧ₜ = contradiction
⟦ <> ⟧ₜ = P.<>
⟦ inl a ⟧ₜ = inl ⟦ a ⟧ₜ
⟦ inr b ⟧ₜ = inr ⟦ b ⟧ₜ
⟦ case d e ⟧ₜ = P.case ⟦ d ⟧ₜ ⟦ e ⟧ₜ
⟦ < a , b > ⟧ₜ = < ⟦ a ⟧ₜ , ⟦ b ⟧ₜ >
⟦ fst c ⟧ₜ = P.fst ⟦ c ⟧ₜ
⟦ snd c ⟧ₜ = P.snd ⟦ c ⟧ₜ
⟦ ozero ⟧ₜ = zero
⟦ sup b ⟧ₜ = sup ⟦ b ⟧ₜ
⟦ ordrec d e ⟧ₜ = P.ordrec ⟦ d ⟧ₜ ⟦ e ⟧ₜ
