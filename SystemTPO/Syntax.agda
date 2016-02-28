module SystemTPO.Syntax where

data Type : Set where
  _⇒_ : Type → Type → Type
  Nat : Type
  ⊥ : Type
  ⊤ : Type
  _∧_ : Type → Type → Type
  _∨_ : Type → Type → Type
  Ord : Type

infixr 20 _⇒_

data Term : Type → Set where
  K : {A B : Type} → Term (A ⇒ B ⇒ A)
  S : {A B C : Type} → Term ((A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C)
  app : {A B : Type} → Term (A ⇒ B) → Term A → Term B
  zero : Term Nat
  suc : Term Nat → Term Nat
  rec : {C : Type} → Term C → Term (Nat ⇒ C ⇒ C) → Term (Nat ⇒ C)
  case0 : {C : Type} → Term (⊥ ⇒ C)
  <> : Term ⊤
  inl : {A B : Type} → Term A → Term (A ∨ B)
  inr : {A B : Type} → Term B → Term (A ∨ B)
  case : {A B C : Type} → Term (A ⇒ C) → Term (B ⇒ C) → Term ((A ∨ B) ⇒ C)
  <_,_> : {A B : Type} → Term A → Term B → Term (A ∧ B)
  fst : {A B : Type} → Term (A ∧ B) → Term A
  snd : {A B : Type} → Term (A ∧ B) → Term B
  ozero : Term Ord
  sup : Term (Nat ⇒ Ord) → Term Ord
  ordrec : {C : Type} → Term C → Term ((Nat ⇒ Ord) ⇒ (Nat ⇒ C) ⇒ C)
         → Term (Ord ⇒ C)

_∘_ : {A B C : Type} → Term (B ⇒ C) → Term (A ⇒ B) → Term (A ⇒ C)
c ∘ b = app (app S (app K c)) b
