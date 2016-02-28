module Prelude where

data ℕ : Set where
  suc  : ℕ → ℕ
  zero : ℕ

natrec : {C : Set} → C → (ℕ → C → C) → ℕ → C
natrec d e zero = d
natrec d e (suc a) = e a (natrec d e a)

data Const (A : Set) : A → Set where
  const : (a : A) → Const A a

constMap : {A : Set} {a : A} → (f : A → A) → Const A a → Const A (f a)
constMap f (const a) = const (f a)

data ⊤ : Set where
  <> : ⊤

data ⊥ : Set where

contradiction : {C : Set} → ⊥ → C
contradiction ()

¬_ : Set → Set
¬ A = A → ⊥

data _×_ (A B : Set) : Set where
  <_,_> : A → B → A × B

fst : {A B : Set} → A × B → A
fst < a , _ > = a

snd : {A B : Set} → A × B → B
snd < _ , b > = b

data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

case : {A B C : Set} → (A → C) → (B → C) → A ⊎ B → C
case d e (inl a) = d a
case d e (inr a) = e a

_⇔_ : Set → Set → Set
A ⇔ B = (A → B) × (B → A)

data O : Set where
  zero : O
  sup : (ℕ → O) → O

ordrec : {C : Set} → C → ((ℕ → O) → (ℕ → C) → C) → O → C
ordrec d e zero = d
ordrec d e (sup b) = e b (λ x → ordrec d e (b x))
