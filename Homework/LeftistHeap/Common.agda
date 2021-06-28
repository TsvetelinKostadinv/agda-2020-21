module Homework.LeftistHeap.Common where

open import Lib.Nat
open import Lib.One
open import Lib.Zero
open import Lib.Sum
open import Lib.Eq

Leq : Nat -> Nat -> Set
Leq zero m = One
Leq (suc n) zero = Zero
Leq (suc n) (suc m) = Leq n m

decLeq : (n m : Nat) -> Leq n m + Leq m n
decLeq zero m = inl <>
decLeq (suc n) zero = inr <>
decLeq (suc n) (suc m) = decLeq n m

<=-Leq : {n m : Nat} -> n <= m -> Leq n m
<=-Leq ozero = <>
<=-Leq (osuc p) = <=-Leq p

Leq-refl : (n : Nat) -> Leq n n
Leq-refl n = <=-Leq (<=-refl n)

Leq-trans : (n m k : Nat) -> Leq n m -> Leq m k -> Leq n k
Leq-trans zero m k p q = <>
Leq-trans (suc n) zero zero () q         -- Needed, cuz of the old version of Agda I have
Leq-trans (suc n) (suc m) zero p ()      -- Needed, cuz of the old version of Agda I have
Leq-trans (suc n) zero (suc k) () q      -- Needed, cuz of the old version of Agda I have
Leq-trans (suc n) (suc m) (suc k) p q = Leq-trans n m k p q

Priority : Set
Priority = Nat

Rank : Set
Rank = Nat

data Maybe (A : Set) : Set where
  no : Maybe A
  yes : A -> Maybe A

min : Nat -> Nat -> Nat
min a b with decLeq a b 
min a b | inl x = a
min a b | inr x = b

min-Leq-left : (n m : Nat) -> Leq (min n m) n
min-Leq-left n m with decLeq n m 
min-Leq-left n m | inl x = Leq-refl n
min-Leq-left n m | inr x = x

min-right-zero : (m : Nat) -> min m zero == zero
min-right-zero zero = refl
min-right-zero (suc m) = refl

min-sucs : (n m : Nat) -> min (suc n) (suc m) == suc (min n m)
min-sucs zero m = refl
min-sucs (suc n) zero = refl
min-sucs (suc n) (suc m) with decLeq n m 
min-sucs (suc n) (suc m) | inl x = refl
min-sucs (suc n) (suc m) | inr x = refl 

min-symm : (n m : Nat) -> min n m == min m n
min-symm zero m rewrite min-right-zero m = refl
min-symm (suc n) zero = refl
min-symm (suc n) (suc m) = 
  min (suc n) (suc m)
    =[ min-sucs n m >=
  suc (min n m)
    =[ ap suc (min-symm n m) >=
  suc (min m n)
    =[ ==-symm (min-sucs m n) >=
  min (suc m) (suc n)
    QED

min-Leq-right : (n m : Nat) -> Leq (min n m) m
min-Leq-right zero zero = <>
min-Leq-right zero (suc m) = <>
min-Leq-right (suc n) zero = <>
min-Leq-right (suc n) (suc m) rewrite min-sucs n m with decLeq n m 
... | inl x = x
... | inr x = Leq-refl m

max : Nat -> Nat -> Nat
max a b with decLeq a b
max a b | inl x = b
max a b | inr x = a

+N-assoc-no-braces : (n m k : Nat) -> (n +N m) +N k == n +N m +N k
+N-assoc-no-braces zero m k = refl
+N-assoc-no-braces (suc n) m k = ap suc (+N-assoc-no-braces n m k)

-- deserves a better name, couldn't come up with one
helper : (n m k p : Nat) -> n +N m +N suc (k +N p) == (k +N p) +N suc (n +N m)
helper n m k p = 
  n +N m +N suc (k +N p)
    =[ ==-symm (+N-assoc-no-braces n m (suc (k +N p))) >=
  (n +N m) +N suc (k +N p)
    =[ +N-right-suc (n +N m) (k +N p) >=
  suc ( (n +N m) +N (k +N p) )
    =[ ap suc (+N-commut (n +N m) (k +N p)) >=
  suc ((k +N p) +N (n +N m))
    =[ ==-symm (+N-right-suc (k +N p) (n +N m)) >=
  (k +N p) +N suc (n +N m)
    QED