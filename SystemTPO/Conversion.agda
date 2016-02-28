module SystemTPO.Conversion where

open import SystemTPO.Syntax


data _conv_ : {A : Type} → Term A → Term A → Set where
  refl : {A : Type} {a : Term A} → a conv a
  trans : {A : Type} {a a' a'' : Term A} → a conv a' → a' conv a'' → a conv a''
  sym : {A : Type} {a b : Term A} → a conv b → b conv a
  app : {A B : Type} {a a' : Term A} {c c' : Term (A ⇒ B)}
      → c conv c' → a conv a' → app c a conv app c' a'
  suc : {a a' : Term Nat} → a conv a' → suc a conv suc a'
  rec : {C : Type} {d d' : Term C} {e e' : Term (Nat ⇒ C ⇒ C)}
      → d conv d' → e conv e' → rec d e conv rec d' e'
  app-K : {A B : Type} {a : Term A} {b : Term B} → app (app K a) b conv a
  app-S : {A B C : Type} {g : Term (A ⇒ B ⇒ C)} {f : Term (A ⇒ B)} {a : Term A}
        → app (app (app S g) f) a conv app (app g a) (app f a)
  rec-zero : {C : Type} {d : Term C} {e : Term (Nat ⇒ C ⇒ C)}
           → app (rec d e) zero conv d
  rec-suc : {C : Type} {d : Term C} {e : Term (Nat ⇒ C ⇒ C)} {a : Term Nat}
          → app (rec d e) (suc a) conv app (app e a) (app (rec d e) a)
  inl : {A B : Type} {a a' : Term A}
      → a conv a' → inl {A} {B} a conv inl {A} {B} a' 
  inr : {A B : Type} {b b' : Term B}
      → b conv b' → inr {A} {B} b conv inr {A} {B} b' 
  case : {A B C : Type} {f f' : Term (A ⇒ C)} {g g' : Term (B ⇒ C)}
       → f conv f' → g conv g' → case f g conv case f' g'
  tuple : {A B : Type} {a a' : Term A} {b b' : Term B}
        → a conv a' → b conv b' → < a , b > conv < a' , b' >
  fst : {A B : Type} {c c' : Term (A ∧ B)} → c conv c' → fst c conv fst c'
  snd : {A B : Type} {c c' : Term (A ∧ B)} → c conv c' → snd c conv snd c'
  case-inl : {A B C : Type} {a : Term A} {d : Term (A ⇒ C)} {e : Term (B ⇒ C)}
           → app (case d e) (inl a) conv app d a
  case-inr : {A B C : Type} {b : Term B} {d : Term (A ⇒ C)} {e : Term (B ⇒ C)}
           → app (case d e) (inr b) conv app e b
  tuple-fst : {A B : Type} {a : Term A} {b : Term B} → fst < a , b > conv a
  tuple-snd : {A B : Type} {a : Term A} {b : Term B} → snd < a , b > conv b
  sup : {b b' : Term (Nat ⇒ Ord)} → b conv b' → sup b conv sup b'
  ordrec : {C : Type} {d d' : Term C} {e e' : Term ((Nat ⇒ Ord) ⇒ (Nat ⇒ C) ⇒ C)}
         → d conv d' → e conv e' → ordrec d e conv ordrec d' e'
  ordrec-ozero : {C : Type} {d : Term C} {e : Term ((Nat ⇒ Ord) ⇒ (Nat ⇒ C) ⇒ C)}
               → app (ordrec d e) ozero conv d
  ordrec-sup : {C : Type} {d : Term C} {e : Term ((Nat ⇒ Ord) ⇒ (Nat ⇒ C) ⇒ C)}
             → (b : Term (Nat ⇒ Ord))
             → app (ordrec d e) (sup b) conv app (app e b) ((ordrec d e) ∘ b)

infixr 20 _~>_

_~>_ : {A : Type} {a b c : Term A} → a conv b → b conv c → a conv c
_~>_ = trans
