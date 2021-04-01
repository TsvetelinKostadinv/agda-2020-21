module Lectures.Three where

open import Lectures.Two
open import Lib.EqReasoning

Even : ℕ → Set
Even zero = One
Even (suc zero) = Zero
Even (suc (suc n)) = Even n 

Odd : ℕ → Set
Odd zero = Zero
Odd (suc zero) = One
Odd (suc (suc n)) = Odd n

data Even' : ℕ → Set where
  ezero : Even' zero
  esuc   : {n : ℕ} → Even' n → Even' (suc (suc n))


data Odd' : ℕ → Set where
  oone : Odd' (suc zero)
  osuc   : {n : ℕ} → Odd' n → Odd' (suc (suc n))

suc-even-is-odd : (n : ℕ) → Even n → Odd (suc n)
suc-even-is-odd zero evenn = <>
suc-even-is-odd (suc zero) ()
suc-even-is-odd (suc (suc n)) evenn = suc-even-is-odd n evenn

suc-even-is-odd-prime : {n : ℕ} → Even' n → Odd' (suc n)
suc-even-is-odd-prime ezero = oone
suc-even-is-odd-prime (esuc evenn) = osuc (suc-even-is-odd-prime evenn)

double : ℕ → ℕ
double zero = zero
double (suc n) = suc (suc (double n))

doubleEven : (n : ℕ) → Even (double n)
doubleEven zero = <>
doubleEven (suc n) = doubleEven n


data _≤_ : ℕ → ℕ → Set where
  ltezero : {n : ℕ} → 0 ≤ n
  ltesuc   : {n m : ℕ} → n ≤ m → suc n ≤ suc m

≤-trans : {n m k : ℕ} → n ≤ m → m ≤ k → n ≤ k
≤-trans ltezero mLTEk = ltezero
≤-trans (ltesuc nLTEm) (ltesuc mLTEk) = ltesuc (≤-trans nLTEm mLTEk)

decEvenOrOdd : (n : ℕ) → Even n + Odd n
decEvenOrOdd zero = inl <>
decEvenOrOdd (suc zero) = inr <>
decEvenOrOdd (suc (suc n)) = decEvenOrOdd n

decEvenOrOdd-prime : (n : ℕ) → Even' n + Odd' n
decEvenOrOdd-prime zero = inl ezero
decEvenOrOdd-prime (suc zero) = inr oone
decEvenOrOdd-prime (suc (suc n)) with decEvenOrOdd-prime n
decEvenOrOdd-prime (suc (suc n)) | inl x = inl (esuc x)
decEvenOrOdd-prime (suc (suc n)) | inr x = inr (osuc x)

<=-refl : {n : ℕ} → n ≤ n
<=-refl {zero} = ltezero
<=-refl {suc n} = ltesuc <=-refl

<=-antisym : {n m : ℕ} → n ≤ m → m ≤  n → n ≡ m
<=-antisym ltezero ltezero = refl
<=-antisym (ltesuc NlteM) (ltesuc MlteN) rewrite <=-antisym NlteM MlteN = refl

<=-mono-left-+ : {n m : ℕ} (k : ℕ) → n ≤ m → (k +ℕ n) ≤ (k +ℕ m)
<=-mono-left-+ zero NlteM = NlteM
<=-mono-left-+ (suc k) NlteM = ltesuc (<=-mono-left-+ k NlteM)

<=-add : {n : ℕ} (k : ℕ) → k ≤ (n +ℕ k)
<=-add zero = ltezero
<=-add {n} (suc k) rewrite ≡-symm (+ℕ-right-suc n k) = ltesuc (<=-add {n} k) 

<=-mono-right-+ : {n m : ℕ} (k : ℕ) → n ≤ m → (n +ℕ k) ≤ (m +ℕ k)
<=-mono-right-+ k ltezero = <=-add k
<=-mono-right-+ k (ltesuc NlteM) = ltesuc (<=-mono-right-+ k NlteM)

_*ℕ_ : ℕ → ℕ → ℕ
zero *ℕ m = zero
suc n *ℕ m = m +ℕ n *ℕ m
infixr 40 _*ℕ_

*N-right-id : (n : ℕ) -> n *ℕ 1 ≡ n
*N-right-id zero = refl
*N-right-id (suc n) = ap suc (*N-right-id n)


+N-commut' : (n m : ℕ) → (n +ℕ m) ≡ (m +ℕ n)
+N-commut' zero m =
  m
    =[ ≡-symm 0-plus-comm-right ]
  m +ℕ zero
    QED
+N-commut' (suc n) m =
  suc (n +ℕ m)
    =[ ap suc (+N-commut' n m) ]
  suc (m +ℕ n)
    =[ +ℕ-right-suc m n ]
  m +ℕ suc n
    QED

*ℕ-distrib-+ℕ-right : (n m k : ℕ) → ((n +ℕ m) *ℕ k) ≡ (n *ℕ k +ℕ m *ℕ k)
*ℕ-distrib-+ℕ-right zero m k = refl
*ℕ-distrib-+ℕ-right (suc n) m k rewrite *ℕ-distrib-+ℕ-right n m k = ≡-symm (+ℕ-assoc k (n *ℕ k) (m *ℕ k))

*ℕ-distrib-+ℕ-left : (n m k : ℕ) → (k *ℕ (n +ℕ m)) ≡ (k *ℕ n +ℕ k *ℕ m)
*ℕ-distrib-+ℕ-left n m zero = refl
*ℕ-distrib-+ℕ-left n m (suc k) = 
  ((n +ℕ m) +ℕ (k *ℕ (n +ℕ m)))
    =[ ap ((n +ℕ m) +ℕ_) (*ℕ-distrib-+ℕ-left n m k) ]
  ((n +ℕ m) +ℕ ((k *ℕ n) +ℕ (k *ℕ m)))
    =[ +ℕ-assoc n m ((k *ℕ n) +ℕ (k *ℕ m)) ]
  (n +ℕ (m +ℕ ((k *ℕ n) +ℕ (k *ℕ m))))
    =[ ap ( n +ℕ_) (≡-symm (+ℕ-assoc m (k *ℕ n) (k *ℕ m))) ]
  (n +ℕ ((m +ℕ k *ℕ n) +ℕ k *ℕ m))
    =[ ap (n +ℕ_) (ap (_+ℕ k *ℕ m) (+ℕ-commut m (k *ℕ n))) ] -- ugly
  ((n +ℕ ((k *ℕ n +ℕ m) +ℕ k *ℕ m)))
    =[ ap (n +ℕ_) (+ℕ-assoc (k *ℕ n) m (k *ℕ m)) ]
  (((n +ℕ (k *ℕ n +ℕ (m +ℕ k *ℕ m)))))
    =[ ≡-symm (+ℕ-assoc n (k *ℕ n) (m +ℕ (k *ℕ m))) ]
  (((((n +ℕ k *ℕ n) +ℕ (m +ℕ k *ℕ m)))))
  QED

*ℕ-assoc : (n m k : ℕ) → (n *ℕ m) *ℕ k ≡ n *ℕ (m *ℕ k)
*ℕ-assoc zero m k = refl
*ℕ-assoc (suc n) m k =
  (m +ℕ (n *ℕ m)) *ℕ k
    =[ *ℕ-distrib-+ℕ-right m (n *ℕ m) k ]
  ap ((m *ℕ k) +ℕ_) (*ℕ-assoc n m k)

*ℕ-right-zero : (n : ℕ) → n *ℕ zero ≡ zero
*ℕ-right-zero zero = refl
*ℕ-right-zero (suc n) = *ℕ-right-zero n

add-same-double : (n : ℕ) → (n +ℕ n) ≡ n *ℕ 2
add-same-double zero = refl
add-same-double (suc n) = 
  (suc n) +ℕ (suc n)
    =[ ≡-symm (+ℕ-right-suc (suc n) n) ]
  suc (suc (n +ℕ n))
    =[ ap (2 +ℕ_) (add-same-double n)  ]
  (2 +ℕ (n *ℕ 2))
    =[ refl ]
  (suc n) *ℕ 2
    QED

*ℕ-right-suc : (n m : ℕ) → (m +ℕ (m *ℕ n)) ≡ (m *ℕ (suc n))
*ℕ-right-suc zero m =
  m +ℕ (m *ℕ zero)
    =[ ap (m +ℕ_ ) (*ℕ-right-zero m) ]
  (m +ℕ zero)
    =[ 0-plus-comm-right ]
  m
    =[ ≡-symm (*N-right-id m) ]
  m *ℕ 1
  QED
*ℕ-right-suc (suc n) m =
  (m +ℕ (m *ℕ (suc n)))
    =[ ap (m +ℕ_) (≡-symm (*ℕ-right-suc n m)) ]
  (m +ℕ (m +ℕ (m *ℕ n)))
    =[ ≡-symm (+ℕ-assoc m m (m *ℕ n)) ]
  ((m +ℕ m) +ℕ (m *ℕ n))
    =[ ap (_+ℕ (m *ℕ n)) (add-same-double m) ]
  (m *ℕ 2 +ℕ m *ℕ n)
    =[ ≡-symm (*ℕ-distrib-+ℕ-left 2 n m) ]
  (m *ℕ suc (suc n))
    QED

*ℕ-commut : (n m : ℕ) → n *ℕ m ≡ m *ℕ n
*ℕ-commut zero m = ≡-symm (*ℕ-right-zero m) 
*ℕ-commut (suc n) m =
  (m +ℕ (n *ℕ m))
    =[ ap (m +ℕ_) (*ℕ-commut n m) ]
  (m +ℕ (m *ℕ n))
    =[ *ℕ-right-suc n m ]
  m *ℕ suc n
  QED
  
