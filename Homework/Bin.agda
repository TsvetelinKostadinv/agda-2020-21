module Homework.Bin where

import Lib.Nat as Nat
open Nat using (Nat; _+N_)
open import Lib.Eq
open import Lib.Sigma
open import Lib.Zero
open import Lib.One

data Bin : Set where
  end : Bin
  _O : Bin -> Bin
  _I : Bin -> Bin

infixr 12 _O
infixr 12 _I

_ : Bin
_ = end I O I

suc : Bin -> Bin
suc end = end I
suc (n O) = n I
suc (n I) = (suc n) O

_ : suc end == end I
_ = refl

_ : suc (end I I) == end I O O
_ = refl

toNat : Bin -> Nat
toNat end = 0
toNat (end O) = 0
toNat (end I) = 1
toNat (n O) = (toNat n) +N toNat n
toNat (n I) = Nat.suc (toNat n +N toNat n)

_ : toNat (end I I I) == 7
_ = refl

_ : toNat (end I I O) == 6
_ = refl

_ : toNat (end O) == 0
_ = refl

_ : toNat end == 0
_ = refl

fromNat : Nat -> Bin
fromNat Nat.zero = end
fromNat (Nat.suc n) = suc (fromNat n)

_ : fromNat 0 == end
_ = refl

_ : fromNat 1 == end I
_ = refl

_ : fromNat 8 == end I O O O
_ = refl

to-nat-trailing-1 : (b : Bin) → toNat (b I) == Nat.suc (toNat (b O))
to-nat-trailing-1 end = refl
to-nat-trailing-1 (b O) = refl
to-nat-trailing-1 (b I) = refl

toNat-suc : (b : Bin) -> toNat (suc b) == Nat.suc (toNat b)
toNat-suc end = refl
toNat-suc (b O) = to-nat-trailing-1 b 
toNat-suc (b I) = helper b where
  helper : (b : Bin) → toNat (suc b O) == Nat.suc (toNat (b I))
  helper end = refl
  helper (b O) = 
    toNat (b I) +N toNat (b I)
      =[ ap (toNat (b I) +N_) (to-nat-trailing-1 b) >=
    toNat (b I) +N Nat.suc (toNat (b O))
      =[ ap (_+N Nat.suc (toNat (b O))) (to-nat-trailing-1 b) >=
    Nat.suc (toNat (b O) +N Nat.suc (toNat (b O)))
      =[ Nat.+N-right-suc (Nat.suc (toNat (b O))) (toNat (b O)) >=
    Nat.suc (Nat.suc (toNat (b O) +N toNat (b O)))
      QED
  helper (b I) = 
    toNat (suc b O) +N toNat (suc b O) 
        =[ ap (toNat (suc b O) +N_) (toNat-suc (b I)) >=
      toNat (suc b O) +N Nat.suc (toNat (b I))
        =[ ap (_+N Nat.suc (toNat (b I))) (toNat-suc (b I)) >=
      Nat.suc (toNat (b I) +N Nat.suc (toNat (b I)))
        =[ Nat.+N-right-suc (Nat.suc (toNat (b I))) (toNat (b I)) >=
      Nat.suc (Nat.suc (toNat (b I) +N toNat (b I)))
        QED

to-from-id : (n : Nat) -> toNat (fromNat n) == n
to-from-id Nat.zero = refl
to-from-id (Nat.suc n) = 
  toNat (suc (fromNat n))
    =[ toNat-suc ((fromNat n)) >=
  Nat.suc (toNat (fromNat n))
    =[ ap Nat.suc (to-from-id n) >=
    Nat.suc n
  QED

from-to-counterexample : Bin >< \b -> fromNat (toNat b) == b -> Zero
from-to-counterexample = (end O O) , (λ ())

data LeadingOne : Bin -> Set where
  endI : LeadingOne (end I)
  _O : {b : Bin} -> LeadingOne b -> LeadingOne (b O)
  _I : {b : Bin} -> LeadingOne b -> LeadingOne (b I)

data Can : Bin -> Set where
  zero : Can end
  leadingOne : {b : Bin} -> LeadingOne b -> Can b

suc-LeadingOne : (b : Bin) -> LeadingOne b -> LeadingOne (suc b)
suc-LeadingOne (end I) endI = endI O
suc-LeadingOne (b O) (leadingB O) = leadingB I
suc-LeadingOne (b I) (leadingB I) = suc-LeadingOne b leadingB O


suc-Can : (b : Bin) -> Can b -> Can (suc b)
suc-Can end zero = leadingOne endI
suc-Can end (leadingOne x) = leadingOne endI
suc-Can b (leadingOne x) = leadingOne (suc-LeadingOne b x)

fromNat-Can : (n : Nat) -> Can (fromNat n)
fromNat-Can Nat.zero = zero
fromNat-Can (Nat.suc n) = suc-Can (fromNat n) (fromNat-Can n)

_+B_ : Bin -> Bin -> Bin
end +B b = b
a +B end = a
(a O) +B (b O) = (a +B b) O
(a O) +B (b I) = (a +B b) I
(a I) +B (b O) = (a +B b) I
(a I) +B (b I) = ( suc (a +B b) ) O

infixr 11 _+B_

_ : end +B end I I I I == end I I I I
_ = refl

_ : end I O O +B end == end I O O
_ = refl

_ : end I I +B end I I I I == end I O O I O
_ = refl

_ : end I I I +B end I O I == end I I O O
_ = refl

+B-right-end : (b : Bin) -> b +B end == b
+B-right-end end = refl
+B-right-end (b O) = refl
+B-right-end (b I) = refl

+B-left-suc : (b v : Bin) -> suc b +B v == suc (b +B v)
+B-left-suc b end = 
  suc b +B end
    =[ +B-right-end (suc b) >=
  suc b
    =[ ap suc (==-symm (+B-right-end b)) >=
  suc (b +B end)
    QED
+B-left-suc end (v O) = refl
+B-left-suc (b O) (v O) = refl
+B-left-suc (b I) (v O) = ap _O (+B-left-suc b v)
+B-left-suc end (v I) = refl
+B-left-suc (b O) (v I) = refl
+B-left-suc (b I) (v I) = ap _I (+B-left-suc b v)

+B-right-suc : (b v : Bin) -> b +B suc v == suc (b +B v)
+B-right-suc end v = refl
+B-right-suc (b O) end = ap _I (+B-right-end b)
+B-right-suc (b O) (v O) = refl
+B-right-suc (b O) (v I) = ap _O (+B-right-suc b v)
+B-right-suc (b I) end = ap _O (ap suc (+B-right-end b))
+B-right-suc (b I) (v O) = refl
+B-right-suc (b I) (v I) = ap _I (+B-right-suc b v)

fromNat-+N-+B-commutes : (n m : Nat) -> fromNat (n +N m) == fromNat n +B fromNat m
fromNat-+N-+B-commutes Nat.zero m = refl
fromNat-+N-+B-commutes (Nat.suc n) Nat.zero = 
  suc (fromNat (n +N Nat.zero))
    =[ ap suc (ap fromNat (Nat.+N-right-zero n)) >=
  suc (fromNat n)
    =[ ==-symm (+B-right-end (suc (fromNat n))) >=
  suc (fromNat n) +B end
    QED
fromNat-+N-+B-commutes (Nat.suc n) (Nat.suc m) = 
  suc (fromNat (n +N Nat.suc m))
    =[ ap suc (fromNat-+N-+B-commutes n (Nat.suc m)) >=
  suc (fromNat n +B suc (fromNat m))
    =[ ==-symm (+B-left-suc (fromNat n) (suc (fromNat m))) >=
  suc (fromNat n) +B suc (fromNat m)
    QED

+B-same-shift : (b : Bin) -> LeadingOne b -> b +B b == b O
+B-same-shift end ()
+B-same-shift (b O) (leadingOneB O) = ap _O (+B-same-shift b leadingOneB)
+B-same-shift (end I) endI = refl
+B-same-shift (b I) (leadingOneB I) = ap _O (
  suc (b +B b)
    =[ ap suc (+B-same-shift b leadingOneB) >= 
  b I
    QED
  )

reduction-toNat-b-0 : (b : Bin ) → toNat (b O) == toNat b +N toNat b
reduction-toNat-b-0 end = refl
reduction-toNat-b-0 (b O) = refl
reduction-toNat-b-0 (b I) = refl

reduction-toNat-b-1 : (b : Bin ) → toNat (b I) ==  Nat.suc (toNat b +N toNat b)
reduction-toNat-b-1 end = refl
reduction-toNat-b-1 (b O) = refl
reduction-toNat-b-1 (b I) = refl

reduction-suc-b-0 : (b : Bin ) → suc (b O) == b I
reduction-suc-b-0 b = refl

from-to-id-Can : (b : Bin) -> Can b -> fromNat (toNat b) == b
from-to-id-Can end zero = refl
from-to-id-Can end (leadingOne ()) -- required for some reason
from-to-id-Can (b O) (leadingOne (x O)) = 
  fromNat (toNat (b O))
    =[ ap fromNat (reduction-toNat-b-0 b) >=
  fromNat (toNat b +N toNat b)
    =[ fromNat-+N-+B-commutes (toNat b) (toNat b) >=
  fromNat (toNat b) +B fromNat (toNat b)
    =[ ap (fromNat (toNat b) +B_) (from-to-id-Can b (leadingOne x)) >=
  fromNat (toNat b) +B b
    =[ ap (_+B b) (from-to-id-Can b (leadingOne x)) >=
  b +B b
    =[ +B-same-shift b x >=
  b O
    QED
from-to-id-Can (end I) (leadingOne endI) = refl
from-to-id-Can (b I) (leadingOne (x I)) = 
  fromNat (toNat (b I))
    =[ ap fromNat (reduction-toNat-b-1 b) >=
  suc (fromNat (toNat b +N toNat b))
    =[ ap suc (ap fromNat (==-symm (reduction-toNat-b-0 b))) >=
  suc (fromNat (toNat (b O)))
    =[ {!  !} >=
  b I
    QED

