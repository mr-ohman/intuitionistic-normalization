module SystemTPO.Normalization where

import Prelude as P
open P hiding (⊤; ⊥; case; fst; snd; ordrec)
open import SystemTPO.Syntax

data Oₘ : Set where
  zero : Oₘ
  sup : Term (Nat ⇒ Ord) → (ℕ → Oₘ) → Oₘ

ordrecₘ : {C : Set}
        → C → (Term (Nat ⇒ Ord) → (ℕ → Oₘ) → (ℕ → C) → C) → Oₘ → C
ordrecₘ d e zero = d
ordrecₘ d e (sup c b) = e c b (λ x → ordrecₘ d e (b x))

⟦_⟧ : Type → Set
⟦ A ⇒ B ⟧ = Term (A ⇒ B) × (⟦ A ⟧ → ⟦ B ⟧)
⟦ Nat ⟧ = ℕ
⟦ ⊥ ⟧ = P.⊥
⟦ ⊤ ⟧ = P.⊤
⟦ A ∧ B ⟧ = ⟦ A ⟧ × ⟦ B ⟧
⟦ A ∨ B ⟧ = ⟦ A ⟧ ⊎ ⟦ B ⟧
⟦ Ord ⟧ = Oₘ

quote' : {A : Type} → ⟦ A ⟧ → Term A
quote' {A ⇒ B} < c , f > = c
quote' {Nat} (suc p) = suc (quote' p)
quote' {Nat} zero = zero
quote' {⊥} ()
quote' {⊤} <> = <>
quote' {A ∨ B} (inl p) = inl (quote' p)
quote' {A ∨ B} (inr q) = inr (quote' q)
quote' {A ∧ B} < p , q > = < quote' p , quote' q >
quote' {Ord} zero = ozero
quote' {Ord} (sup c f) = sup c

appₘ : {A B : Type} → ⟦ A ⇒ B ⟧ → ⟦ A ⟧ → ⟦ B ⟧
appₘ < c , f > q = f q

natrecₘ : {C : Type} → ⟦ C ⟧ → ⟦ Nat ⇒ C ⇒ C ⟧ → ⟦ Nat ⇒ C ⟧
natrecₘ d e = < rec (quote' d) (quote' e)
              , natrec d (λ m c → appₘ (appₘ e m) c)
              >

caseₘ : {A B C : Type} → ⟦ A ⇒ C ⟧ → ⟦ B ⇒ C ⟧ → ⟦ (A ∨ B) ⇒ C ⟧
caseₘ d e = < (case (quote' d) (quote' e)) , P.case (appₘ d) (appₘ e) >

supₘ : ⟦ Nat ⇒ Ord ⟧ → ⟦ Ord ⟧
supₘ c = sup (quote' c) (appₘ c)

ordrecₘ₀ : {C : Type} → ⟦ C ⟧ → ⟦ (Nat ⇒ Ord) ⇒ (Nat ⇒ C) ⇒ C ⟧ → Oₘ → ⟦ C ⟧
ordrecₘ₀ d e = ordrecₘ d (λ x x₁ x₂ → appₘ (appₘ e < x , x₁ >)
                                           < ordrec (quote' d) (quote' e) ∘ x
                                           , x₂
                                           >
                         )

ordrecₘ₁ : {C : Type} → ⟦ C ⟧ → ⟦ (Nat ⇒ Ord) ⇒ (Nat ⇒ C) ⇒ C ⟧ → ⟦ Ord ⇒ C ⟧
ordrecₘ₁ d e = < ordrec (quote' d) (quote' e) , ordrecₘ₀ d e >

ordrecₘ₂ : {C : Type} → ⟦ C ⟧ → ⟦ (Nat ⇒ Ord) ⇒ (Nat ⇒ C) ⇒ C ⟧ → ⟦ Nat ⇒ Ord ⟧
         → ⟦ Nat ⇒ C ⟧
ordrecₘ₂ d e < x , x₁ > = < ordrec (quote' d) (quote' e) ∘ x
                          , (λ n → ordrecₘ₀ d e (x₁ n))
                          >

⟦_⟧ₜ : {A : Type} → Term A → ⟦ A ⟧
⟦ K ⟧ₜ = < K , (λ p → < app K (quote' p) , (λ q → p) >) >
⟦ S ⟧ₜ = < S , (λ p → < app S (quote' p)
                      , (λ q → < app (app S (quote' p)) (quote' q)
                               , (λ r → appₘ (appₘ p r) (appₘ q r))
                               >) >) >
⟦ app c a ⟧ₜ = appₘ ⟦ c ⟧ₜ ⟦ a ⟧ₜ
⟦ zero ⟧ₜ = zero
⟦ suc a ⟧ₜ = suc ⟦ a ⟧ₜ
⟦ rec d e ⟧ₜ = < rec (quote' ⟦ d ⟧ₜ) (quote' ⟦ e ⟧ₜ)
               , natrec ⟦ d ⟧ₜ (λ x y → appₘ (appₘ ⟦ e ⟧ₜ x) y)
               >
⟦ case0 ⟧ₜ = < case0 , contradiction >
⟦ <> ⟧ₜ = <>
⟦ inl a ⟧ₜ = inl ⟦ a ⟧ₜ
⟦ inr a ⟧ₜ = inr ⟦ a ⟧ₜ
⟦ case d e ⟧ₜ = < case (quote' ⟦ d ⟧ₜ) (quote' ⟦ e ⟧ₜ)
                , P.case (λ x → appₘ ⟦ d ⟧ₜ x) (λ y → appₘ ⟦ e ⟧ₜ y)
                >
⟦ < a , b > ⟧ₜ = < ⟦ a ⟧ₜ , ⟦ b ⟧ₜ >
⟦ fst a ⟧ₜ = P.fst ⟦ a ⟧ₜ
⟦ snd a ⟧ₜ = P.snd ⟦ a ⟧ₜ
⟦ ozero ⟧ₜ = zero
⟦ sup b ⟧ₜ = sup (quote' ⟦ b ⟧ₜ) (λ x → appₘ ⟦ b ⟧ₜ x)
⟦ ordrec d e ⟧ₜ = < ordrec (quote' ⟦ d ⟧ₜ) (quote' ⟦ e ⟧ₜ)
                  , ordrecₘ ⟦ d ⟧ₜ
                      (λ x y z →
                         appₘ (appₘ ⟦ e ⟧ₜ < x , y >)
                              < (ordrec (quote' ⟦ d ⟧ₜ) (quote' ⟦ e ⟧ₜ)) ∘ x
                              , z
                              >
                      ) >

nf : {A : Type} → Term A → Term A
nf a = quote' ⟦ a ⟧ₜ
