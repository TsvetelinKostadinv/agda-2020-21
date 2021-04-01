module Lectures.Two where

-- Implicit params in {...}

data One : Set where
  <> : One

data Zero : Set where

data Bool : Set where
  tt ff : Bool

-- Either type
data _+_ (A B : Set) : Set where
  inl : A → A + B
  inr : B → A + B

-- Swap the Either
+-swap : {A B : Set} → A + B → B + A
+-swap (inl x) = inr x
+-swap (inr x) = inl x

-- The Pair type
record _×_ (A B : Set) : Set where
  constructor _,_
  field
    left : A
    right : B

-- Example
_ : One × Bool
_ = <> , tt

-- Swap the product
×-swap : {A B : Set } → A × B → B × A
×-swap (left , right) = right , left

-- Peano coded natural numbers
-- We have a constant zero
-- All other are the previous + 1
data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

_+ℕ_ : ℕ → ℕ → ℕ
zero +ℕ b = b
suc a +ℕ b = suc (a +ℕ b)
infixr 20 _+ℕ_

-- Equality of 2 values of a given type
data _≡_ {A : Set} : A → A → Set where
  -- Reflexivity property
  refl : ∀{a} → a ≡ a
  -- Symetricity property
  --sym : ∀{a b} → (a ≡ b) → (b ≡ a)
  -- Transitivity property
  --trans : ∀{a b c} → (a ≡ b) → (b ≡ c) → (a ≡ c)

{-# BUILTIN EQUALITY _≡_ #-}

_ : zero ≡ zero
_ = refl

2-plus-2-eq-4 : {n : ℕ} → n ≡ 2 → (n +ℕ 2) ≡ 4
2-plus-2-eq-4 refl = refl

0-plus-comm-left : {n : ℕ} → (0 +ℕ n) ≡ n
0-plus-comm-left {n} = refl

apℕ : {a b : ℕ} → a ≡ b → suc a ≡ suc b
apℕ refl = refl

-- Functionality = if x≡y ⇒ f(x)≡f(y)
ap : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
ap f (refl) = refl

apℕ-with-ap : {a b : ℕ} → a ≡ b → suc a ≡ suc b
apℕ-with-ap refl = ap suc refl 

0-plus-comm-right : {n : ℕ} → (n +ℕ 0) ≡ n
0-plus-comm-right {zero} = refl
0-plus-comm-right {suc n'} =  ap suc 0-plus-comm-right

-- Exercises

+ℕ-assoc : (n m k : ℕ) → ((n +ℕ m) +ℕ k) ≡ (n +ℕ (m +ℕ k))
+ℕ-assoc zero m k = refl
+ℕ-assoc (suc n') m k = ap suc (+ℕ-assoc n' m k)

+-assoc : {A B C : Set} → A + (B + C) → (A + B) + C
+-assoc (inl a) = inl (inl a)
+-assoc (inr (inl b)) = inl (inr b)
+-assoc (inr (inr c)) = inr c

×-assoc : {A B C : Set} → A × (B × C) → (A × B) × C
×-assoc (a , (b , c)) = (a , b) , c

×-distrib-+ : {A B C : Set} → A × (B + C) → (A × B) + (A × C)
×-distrib-+ (a , inl b) = inl (a , b)
×-distrib-+ (a , inr c) = inr (a , c)

+ℕ-right-suc : (n m : ℕ) → (suc (n +ℕ m)) ≡ (n +ℕ suc m)
+ℕ-right-suc zero m = refl
+ℕ-right-suc (suc n') m = ap suc (+ℕ-right-suc n' m)

≡-symm : {X : Set} {x y : X} → x ≡ y → y ≡ x
≡-symm refl = refl

≡-trans : {X : Set} {x y z : X} → x ≡ y → y ≡ z → x ≡ z
≡-trans refl refl = refl

+ℕ-commut : (n m : ℕ) → (n +ℕ m) ≡ (m +ℕ n)
+ℕ-commut zero m = ≡-symm 0-plus-comm-right
+ℕ-commut (suc n') m = ≡-trans (ap suc (+ℕ-commut n' m))  (+ℕ-right-suc m n')

data List (a : Set) : Set where
  [] : List a
  _,-_ : a → List a → List a

infixr 20 _,-_ 

_+L_ : {A : Set} → List A → List A → List A
[] +L ys = ys
(x ,- xs) +L ys = x ,- (xs +L ys)

_ : ((3 ,- (5 ,- [])) +L  (4 ,- (2 ,- []))) ≡ (3 ,- (5 ,- (4 ,- (2 ,- []))))
_ = refl

+L-assoc : {A : Set} (xs ys zs : List A) → ((xs +L ys) +L zs) ≡ (xs +L (ys +L zs))
+L-assoc [] ys zs = refl
+L-assoc (x ,- xs) ys zs = ap ((_,-_ x)) (+L-assoc xs ys zs)

+L-right-id : {A : Set} (xs : List A) → (xs +L []) ≡ xs
+L-right-id [] = refl
+L-right-id (x ,- xs) = ap (_,-_ x) (+L-right-id xs)

length : {A : Set} → List A → ℕ
length [] = 0
length (x ,- xs) = 1 +ℕ (length xs)

_ : length (<> ,- []) ≡ 1
_ = refl
_ : length (3 ,- (5 ,- [])) ≡ 2
_ = refl

replicate : {A : Set} → ℕ → A → List A
replicate zero el = []
replicate (suc len) el = el ,- (replicate len el)

_ : (replicate 2 <>) ≡ (<> ,- (<> ,- []))
_ = refl

length-replicate : {A : Set} {x : A} (n : ℕ) → length (replicate n x) ≡ 
length-replicate {x} zero = refl
length-replicate {x} (suc len) = ap suc (length-replicate len)

map : {A B : Set} → (f : A → B) → List A → List B
map f [] = []
map f (x ,- xs) = (f x) ,- (map f xs)

lift : {A B : Set} → (f : A → B) → (List A → List B)
lift f = λ listA → map f listA

All : {X : Set} (P : X → Set) → List X → Set
All {X} P [] = One
All {X} P (x ,- xs) = (P x) × (All P xs)

replicate-all-≡-orig : {A : Set} {x : A} (n : ℕ) → All (_≡_ x) (replicate n x)
replicate-all-≡-orig {A} {x} zero = <>
replicate-all-≡-orig {A} {x} (suc n) = refl , replicate-all-≡-orig n

