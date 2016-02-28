module SystemTPO.Proof.Normalization where

import Prelude as P
open P hiding (⊤; ⊥; case; fst; snd; ordrec)
import Equality as E
open E hiding (trans; sym)

open import SystemTPO.Syntax
open import SystemTPO.Conversion
open import SystemTPO.Normalization

Theorem3' : {A : Type} {a a' : Term A} → a conv a' → ⟦ a ⟧ₜ ≡ ⟦ a' ⟧ₜ
Theorem3' refl = refl
Theorem3' (trans p p₁) = E.trans (Theorem3' p) (Theorem3' p₁)
Theorem3' (sym p) = E.sym (Theorem3' p)
Theorem3' (app p p₁) = E.cong₂ appₘ (Theorem3' p) (Theorem3' p₁)
Theorem3' (suc p) = E.cong suc (Theorem3' p)
Theorem3' (rec p p₁) = E.cong₂ natrecₘ (Theorem3' p) (Theorem3' p₁)
Theorem3' app-K = refl
Theorem3' app-S = refl
Theorem3' rec-zero = refl
Theorem3' rec-suc = refl
Theorem3' (inl x) = E.cong inl (Theorem3' x)
Theorem3' (inr x) = E.cong inr (Theorem3' x)
Theorem3' (case x x₁) = E.cong₂ caseₘ (Theorem3' x) (Theorem3' x₁)
Theorem3' (tuple x x₁) = E.cong₂ <_,_> (Theorem3' x) (Theorem3' x₁)
Theorem3' (fst x) = E.cong P.fst (Theorem3' x)
Theorem3' (snd x) = E.cong P.snd (Theorem3' x)
Theorem3' case-inl = refl
Theorem3' case-inr = refl
Theorem3' tuple-fst = refl
Theorem3' tuple-snd = refl
Theorem3' (sup a) = E.cong supₘ (Theorem3' a)
Theorem3' (ordrec a a₁) = E.cong₂ ordrecₘ₁ (Theorem3' a) (Theorem3' a₁)
Theorem3' ordrec-ozero = refl
Theorem3' (ordrec-sup b) with ⟦ b ⟧ₜ
Theorem3' (ordrec-sup b) | < x , x₁ > with x₁ zero
Theorem3' (ordrec-sup b) | < x , x₁ > | zero = refl
Theorem3' (ordrec-sup b) | < x , x₁ > | sup x₂ x₃ = refl

Theorem3 : {A : Type} {a a' : Term A} → a conv a' → nf a ≡ nf a'
Theorem3 p = E.cong quote' (Theorem3' p)

Gl : (A : Type) → (a : ⟦ A ⟧) → Set
Gl (A ⇒ B) q = (p : ⟦ A ⟧) → Gl A p → Gl B (appₘ q p)
             × (app (quote' q) (quote' p) conv (quote' (appₘ q p)))
Gl Nat n = Const ℕ n
Gl ⊥ a = P.⊥
Gl ⊤ a = P.⊤
Gl (A ∨ B) (inl a) = Gl A a
Gl (A ∨ B) (inr b) = Gl B b
Gl (A ∧ B) < a , b > = Gl A a × Gl B b
Gl Ord zero = P.⊤
Gl Ord (sup c f) = (p : ℕ) → Gl Ord (f p)
               × (app c (quote' p) conv quote' (f p))

S-proof : {A B C : Type} (p : ⟦ A ⇒ B ⇒ C ⟧) (p₁ : ⟦ A ⇒ B ⟧) (p₂ : ⟦ A ⟧)
        → app (quote' (appₘ p p₂)) (quote' (appₘ p₁ p₂))
          conv quote' (appₘ (appₘ p p₂) (appₘ p₁ p₂))
        → app (quote' p) (quote' p₂) conv quote' (appₘ p p₂)
        → app (quote' p₁) (quote' p₂) conv quote' (appₘ p₁ p₂)
        → app (app (app S (quote' p)) (quote' p₁)) (quote' p₂)
          conv quote' (appₘ (appₘ p p₂) (appₘ p₁ p₂))
S-proof p p₁ p₂ prf prf₁ prf₂ = trans app-S (trans (app prf₁ prf₂) prf)

rec-proof : {C : Type} (d : ⟦ C ⟧) (e : ⟦ Nat ⇒ C ⇒ C ⟧) (m : ℕ)
          → ((n : ℕ) → let c = natrec d (λ z → appₘ (appₘ e z)) n in
                         app (quote' (appₘ e n)) (quote' c)
                         conv quote' (appₘ (appₘ e n) c))
          → ((n : ℕ) → app (quote' e) (quote' n) conv quote' (appₘ e n))
          → app (rec (quote' d) (quote' e)) (quote' m)
            conv quote' (natrec d (λ x y → appₘ (appₘ e x) y) m)
rec-proof d e (suc m) prf prf₁ = rec-suc
                               ~> (app (prf₁ m)
                                       (rec-proof d e m prf prf₁))
                               ~> (prf m)
rec-proof d e zero prf prf₁ = rec-zero

sup-proof : (a : Term (Nat ⇒ Ord)) → Gl (Nat ⇒ Ord) ⟦ a ⟧ₜ → (p : ℕ)
          → app (quote' ⟦ a ⟧ₜ) (quote' p) conv quote' (appₘ ⟦ a ⟧ₜ p)
sup-proof a gla p = P.snd (gla p (const p))

ordrec-proof' : {C : Type} (d : ⟦ C ⟧) (e : ⟦ (Nat ⇒ Ord) ⇒ (Nat ⇒ C) ⇒ C ⟧)
              → (x : Term (Nat ⇒ Ord)) (x₁ : ℕ → Oₘ) (n : ℕ)
              → app x (quote' n) conv quote' (x₁ n)
              → app (ordrec (quote' d) (quote' e)) (quote' (x₁ n))
                conv quote' (ordrecₘ₀ d e (x₁ n))
              → app (ordrec (quote' d) (quote' e) ∘ x) (quote' n)
                conv quote' (ordrecₘ₀ d e (x₁ n))
ordrec-proof' d e x x₁ n prf prf₁ = trans app-S (trans (app app-K prf) prf₁)

Gl-app : {A B : Type} (f : ⟦ A ⇒ B ⟧) (a : ⟦ A ⟧)
       → Gl (A ⇒ B) f → Gl A a → Gl B (appₘ f a)
Gl-app f' a' f a = P.fst (f a' a)

Gl-K : {A B : Type} → Gl (A ⇒ B ⇒ A) ⟦ K ⟧ₜ
Gl-K p x = < (λ p₁ x₁ → < x , app-K >) , refl >

Gl-S : {A B C : Type} → Gl ((A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C) ⟦ S ⟧ₜ
Gl-S p x = < (λ p₁ x₁ → < (λ p₂ x₂ →
  < Gl-app (appₘ p p₂) (appₘ p₁ p₂)
      (Gl-app p p₂ x x₂)
      (Gl-app p₁ p₂ x₁ x₂)
  , S-proof p p₁ p₂
      (P.snd (P.fst (x p₂ x₂) (appₘ p₁ p₂) (P.fst (x₁ p₂ x₂))))
      (P.snd (x p₂ x₂))
      (P.snd (x₁ p₂ x₂))
  >) , refl >) , refl >

Gl-rec : {C : Type} (d : ⟦ C ⟧) (e : ⟦ Nat ⇒ C ⇒ C ⟧)
       → Gl C d → Gl (Nat ⇒ C ⇒ C) e → Gl (Nat ⇒ C) (natrecₘ d e)
Gl-rec d' e' d e m x =
  < Gl-rec' d' e' m d e x
  , rec-proof d' e' m
      (λ n → P.snd (P.fst (e n (const n)) (natrec d'
                      (λ z → appₘ (appₘ e' z)) n)
                      (Gl-rec' d' e' n d e (const n))))
      (λ n → P.snd (e n (const n)))
  >
  where
    Gl-rec' : {C : Type} (d : ⟦ C ⟧) (e : ⟦ Nat ⇒ C ⇒ C ⟧) (m : ℕ)
            → Gl C d → Gl (Nat ⇒ C ⇒ C) e → Gl Nat m
            → Gl C (appₘ (natrecₘ d e) m)
    Gl-rec' d' e' (suc m') d e (const .(suc m')) =
      Gl-app (appₘ e' m') (natrec d' (λ z → appₘ (appₘ e' z)) m')
        (Gl-app e' m' e (const m'))
        (Gl-rec' d' e' m' d e (const m'))
    Gl-rec' d' e' zero d e a = d

Gl-case0 : {C : Type} (c : ⟦ ⊥ ⇒ C ⟧) → Gl (⊥ ⇒ C) c → (b : P.⊥) → Gl ⊥ b
         → Gl C (appₘ c b) × (app (quote' c) (quote' b) conv quote' (appₘ c b))
Gl-case0 c' c b' b = c b' b

Gl-case : {A B C : Type} (a : ⟦ A ⇒ C ⟧) (b : ⟦ B ⇒ C ⟧)
        → Gl (A ⇒ C) a → Gl (B ⇒ C) b → Gl ((A ∨ B) ⇒ C) (caseₘ a b)
Gl-case a' b' a b (inl p) x = < Gl-app a' p a x
                              , trans case-inl (P.snd (a p x))
                              >
Gl-case a' b' a b (inr p) x = < Gl-app b' p b x
                              , trans case-inr (P.snd (b p x))
                              >

Gl-fst : (A B : Type) (c : ⟦ A ∧ B ⟧)
       → Gl (A ∧ B) c → Gl A (P.fst c)
Gl-fst A B < a' , b' > < a , b > = a

Gl-snd : (A B : Type) (c : ⟦ A ∧ B ⟧)
       → Gl (A ∧ B) c → Gl B (P.snd c)
Gl-snd A B < a' , b' > < a , b > = b

mutual
  ordrec-lemma : {C : Type}
               → (d : ⟦ C ⟧) (e : ⟦ (Nat ⇒ Ord) ⇒ (Nat ⇒ C) ⇒ C ⟧) (o : ⟦ Ord ⟧)
               → Gl C d → Gl ((Nat ⇒ Ord) ⇒ (Nat ⇒ C) ⇒ C) e → Gl Ord o
               → app (ordrec (quote' d) (quote' e)) (quote' o) conv
                 quote' (ordrecₘ₀ d e o)
  ordrec-lemma d' e' zero d e o = ordrec-ozero
  ordrec-lemma d' e' (sup x x₁) d e o =
    let f' = < x , x₁ >
        f  = (λ p _ → o p)
        e₁ = e f' f 
    in
       ordrec-sup x
    ~> app (P.snd e₁)
           refl
    ~> P.snd ((P.fst e₁) (ordrecₘ₂ d' e' f') (Gl-ordrec₂ d' e' f' d e f))

  Gl-ordrec₁ : {C : Type} (d : ⟦ C ⟧) (e : ⟦ (Nat ⇒ Ord) ⇒ (Nat ⇒ C) ⇒ C ⟧)
               (o : ⟦ Ord ⟧)
             → Gl C d → Gl ((Nat ⇒ Ord) ⇒ (Nat ⇒ C) ⇒ C) e → Gl Ord o
             → Gl C (ordrecₘ₀ d e o)
  Gl-ordrec₁ d' e' zero d e o = d
  Gl-ordrec₁ d' e' (sup x x₁) d e o =
    let f' = < x , x₁ >
        f  = (λ p _ → o p)
    in
    Gl-app (appₘ e' f')
           (ordrecₘ₂ d' e' f')
           (Gl-app e' f' e f)
           (Gl-ordrec₂ d' e' f' d e f)

  Gl-ordrec₂ : {C : Type} (d : ⟦ C ⟧) (e : ⟦ (Nat ⇒ Ord) ⇒ (Nat ⇒ C) ⇒ C ⟧)
             → (f : ⟦ Nat ⇒ Ord ⟧)
             → Gl C d → Gl ((Nat ⇒ Ord) ⇒ (Nat ⇒ C) ⇒ C) e → Gl (Nat ⇒ Ord) f
             → Gl (Nat ⇒ C) (ordrecₘ₂ d e f)
  Gl-ordrec₂ d' e' < x , x₁ > d e f p' p =
    < Gl-ordrec₁ d' e' (x₁ p') d e (Gl-app < x , x₁ > p' f p)
    , ordrec-proof' d' e' x x₁ p' (P.snd (f p' p))
                    (ordrec-lemma d' e' (x₁ p') d e (Gl-app < x , x₁ > p' f p)) >

Gl-ordrec : {C : Type} (d : ⟦ C ⟧) (e : ⟦ (Nat ⇒ Ord) ⇒ (Nat ⇒ C) ⇒ C ⟧)
          → Gl C d → Gl ((Nat ⇒ Ord) ⇒ (Nat ⇒ C) ⇒ C) e
          → Gl (Ord ⇒ C) (ordrecₘ₁ d e)
Gl-ordrec d' e' d e o' o =
  < Gl-ordrec₁ d' e' o' d e o
  , ordrec-lemma d' e' o' d e o >

Lemma5 : {A : Type} → (a : Term A) → Gl A ⟦ a ⟧ₜ
Lemma5 K = Gl-K
Lemma5 S = Gl-S
Lemma5 (app c a) = Gl-app ⟦ c ⟧ₜ ⟦ a ⟧ₜ (Lemma5 c) (Lemma5 a)
Lemma5 zero = const zero
Lemma5 (suc n) = constMap suc (Lemma5 n)
Lemma5 (rec d e) = Gl-rec ⟦ d ⟧ₜ ⟦ e ⟧ₜ (Lemma5 d) (Lemma5 e)
Lemma5 case0 = Gl-case0 < case0 , contradiction > (λ p₁ → λ ())
Lemma5 <> = <>
Lemma5 (inl a) = Lemma5 a
Lemma5 (inr a) = Lemma5 a
Lemma5 (case a a₁) = Gl-case ⟦ a ⟧ₜ ⟦ a₁ ⟧ₜ (Lemma5 a) (Lemma5 a₁)
Lemma5 < a , a₁ > = < Lemma5 a , Lemma5 a₁ >
Lemma5 (fst {A} {B} a) = Gl-fst A B ⟦ a ⟧ₜ (Lemma5 a)
Lemma5 (snd {A} {B} a) = Gl-snd A B ⟦ a ⟧ₜ (Lemma5 a)
Lemma5 ozero = <>
Lemma5 (sup a) p = < (Gl-app ⟦ a ⟧ₜ p (Lemma5 a) (const p))
                   , sup-proof a (Lemma5 a) p >
Lemma5 (ordrec a a₁) = Gl-ordrec ⟦ a ⟧ₜ ⟦ a₁ ⟧ₜ (Lemma5 a) (Lemma5 a₁)

Lemma6 : {A B : Type} (c : Term (A ⇒ B)) (a : Term A)
       → app (quote' ⟦ c ⟧ₜ) (quote' ⟦ a ⟧ₜ) conv quote' (appₘ ⟦ c ⟧ₜ ⟦ a ⟧ₜ)
Lemma6 c a = P.snd (Lemma5 c ⟦ a ⟧ₜ (Lemma5 a))

Lemma6-fst : {A B : Type} (a : ⟦ A ∧ B ⟧)
           → fst (quote' {A ∧ B} a) conv quote' (P.fst a)
Lemma6-fst < x , x₁ > = tuple-fst

Lemma6-snd : {A B : Type} (a : ⟦ A ∧ B ⟧)
           → snd (quote' {A ∧ B} a) conv quote' (P.snd a)
Lemma6-snd < x , x₁ > = tuple-snd

Theorem4 : {A : Type} (a : Term A) → a conv nf a
Theorem4 K = refl
Theorem4 S = refl
Theorem4 (app a a₁) = trans (app (Theorem4 a) (Theorem4 a₁)) (Lemma6 a a₁)
Theorem4 zero = refl
Theorem4 (suc a) = suc (Theorem4 a)
Theorem4 (rec a a₁) = rec (Theorem4 a) (Theorem4 a₁)
Theorem4 case0 = refl
Theorem4 <> = refl
Theorem4 (inl a) = inl (Theorem4 a)
Theorem4 (inr a) = inr (Theorem4 a)
Theorem4 (case a a₁) = case (Theorem4 a) (Theorem4 a₁)
Theorem4 < a , a₁ > = tuple (Theorem4 a) (Theorem4 a₁)
Theorem4 (fst a) = trans (fst (Theorem4 a)) (Lemma6-fst ⟦ a ⟧ₜ)
Theorem4 (snd a) = trans (snd (Theorem4 a)) (Lemma6-snd ⟦ a ⟧ₜ)
Theorem4 ozero = refl
Theorem4 (sup x) = sup (Theorem4 x)
Theorem4 (ordrec x x₁) = ordrec (Theorem4 x) (Theorem4 x₁)

unSucc : Term Nat → Term Nat
unSucc (app n n₁) = app n n₁
unSucc zero = zero
unSucc (suc n) = n
unSucc (fst n) = fst n
unSucc (snd n) = snd n

lem2 : (a b : Term Nat) → nf (suc a) ≡ nf (suc b) → nf a ≡ nf b
lem2 a b prf = cong unSucc prf

lem11 : {A : Type} (a b : Term A) → a ≡ b → a conv b
lem11 a .a refl = refl

lem121 : {A : Type} (a b : Term A) → nf a conv nf b → a conv nf b
lem121 a b prf = trans (Theorem4 a) prf

lem122 : {A : Type} (a b : Term A) → a conv nf b → a conv b
lem122 a b prf = trans prf (sym (Theorem4 b))

lem12 : {A : Type} (a b : Term A) → nf a conv nf b → a conv b
lem12 a b prf = lem122 a b (lem121 a b prf)

lem3 : {A : Type} (a b : Term A) → nf a ≡ nf b → a conv b
lem3 a b prf = lem12 a b (lem11 (nf a) (nf b) prf)

Theorem11 : (a b : Term Nat) → suc a conv suc b → a conv b
Theorem11 a b c = lem3 a b (lem2 a b (Theorem3 c))

unSup : Term Ord → Term (Nat ⇒ Ord)
unSup (app a a₁) = app K (app a a₁)
unSup (fst a) = app K (fst a)
unSup (snd a) = app K (snd a)
unSup ozero = app K ozero
unSup (sup a) = a

lem2b : (a b : Term (Nat ⇒ Ord)) → nf (sup a) ≡ nf (sup b) → nf a ≡ nf b
lem2b a b prf = cong unSup prf

Theorem12 : (a b : Term (Nat ⇒ Ord)) → sup a conv sup b → a conv b
Theorem12 a b c = lem3 a b (lem2b a b (Theorem3 c))
