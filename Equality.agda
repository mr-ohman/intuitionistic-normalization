module Equality where

data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a

sym : {A : Set} {a a' : A} → a ≡ a' → a' ≡ a
sym refl = refl

trans : {A : Set} {a a' a'' : A} → a ≡ a' → a' ≡ a'' → a ≡ a''
trans refl refl = refl

subst : {A : Set} → {C : A → Set} → (a₁ a₂ : A) → a₁ ≡ a₂ → C a₁ → C a₂
subst a .a refl c = c

cong : {A B : Set} → {a₁ a₂ : A} → (f : A → B) → a₁ ≡ a₂ → (f a₁) ≡ (f a₂)
cong f refl = refl

cong-app : {A B : Set} → {a₁ a₂ : A} → {c₁ c₂ : A → B} → c₁ ≡ c₂ → a₁ ≡ a₂
         → c₁ a₁ ≡ c₂ a₂
cong-app refl refl = refl

cong₂ : {A B C : Set} → {d₁ d₂ : A} → {e₁ e₂ : B} → (g : A → B → C)
      → d₁ ≡ d₂ → e₁ ≡ e₂ → (g d₁ e₁) ≡ (g d₂ e₂)
cong₂ g refl refl = refl
