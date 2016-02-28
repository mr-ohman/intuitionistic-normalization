module SystemTPO.Proof.Intended where

import Prelude as P
open P hiding (case; fst; snd; ordrec; ⊥)
import Equality as E
open E using (_≡_; refl)

open import SystemTPO.Syntax
open import SystemTPO.Conversion
open import SystemTPO.Intended

Theorem1 : {A : Type} {a a' : Term A} → a conv a' → ⟦ a ⟧ₜ ≡ ⟦ a' ⟧ₜ
Theorem1 refl = refl
Theorem1 (trans a b) = E.trans (Theorem1 a) (Theorem1 b)
Theorem1 (sym a) = E.sym (Theorem1 a)
Theorem1 (app f a) = E.cong-app (Theorem1 f) (Theorem1 a)
Theorem1 (suc a) = E.cong suc (Theorem1 a)
Theorem1 (rec d e) = E.cong₂ natrec (Theorem1 d) (Theorem1 e)
Theorem1 app-K = refl
Theorem1 app-S = refl
Theorem1 rec-zero = refl
Theorem1 rec-suc = refl
Theorem1 (inl x) = E.cong inl (Theorem1 x)
Theorem1 (inr x) = E.cong inr (Theorem1 x)
Theorem1 (case x x₁) = E.cong₂ P.case (Theorem1 x) (Theorem1 x₁)
Theorem1 (tuple x x₁) = E.cong₂ <_,_> (Theorem1 x) (Theorem1 x₁)
Theorem1 (fst x) = E.cong P.fst (Theorem1 x)
Theorem1 (snd x) = E.cong P.snd (Theorem1 x)
Theorem1 case-inl = refl
Theorem1 case-inr = refl
Theorem1 tuple-fst = refl
Theorem1 tuple-snd = refl
Theorem1 (sup a) = E.cong sup (Theorem1 a)
Theorem1 (ordrec a a₁) = E.cong₂ P.ordrec (Theorem1 a) (Theorem1 a₁)
Theorem1 ordrec-ozero = refl
Theorem1 (ordrec-sup b) = refl

lemma : ¬ (⟦ zero ⟧ₜ ≡ ⟦ suc zero ⟧ₜ)
lemma ()

Collary2 : ¬ (zero conv suc zero)
Collary2 a = lemma (Theorem1 a)

Theorem10 : ¬ (Term ⊥)
Theorem10 a = ⟦ a ⟧ₜ
