module Lectures.Four where

open import Lectures.Two
open import Lectures.Three
open import Lib.EqReasoning

record _><_ (A : Set) (P : A -> Set) : Set where
  constructor _,_
  field
    fst : A
    snd : P fst

open _><_ public
infixr 8 _><_

data Vec (A : Set) : ℕ → Set where
  [] : Vec A zero
  _,-_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

vHead : {A : Set} {n : ℕ} → Vec A (suc n) → A
vHead (x ,- _) = x


vTail : {A : Set} {n : ℕ} → Vec A (suc n) → Vec A n
vTail (_ ,- xs) = xs


_+V_ : {A : Set} {n m : ℕ} → Vec A n → Vec A m → Vec A (n +ℕ m)
[] +V ys = ys
(x ,- xs) +V ys = x ,- (xs +V ys)

infixr 12 _+V_

listToVec : {A : Set} → List A → ℕ >< \ n -> Vec A n
listToVec [] = zero , []
listToVec (x ,- xs) =
  let n , xs' = listToVec xs
  in suc n , (x ,- xs')

length-+L-distrib : {A : Set} → (xs ys : List A) → (length (xs +L ys)) ≡ (length xs +ℕ length ys)
length-+L-distrib [] ys = refl
length-+L-distrib (x ,- xs) ys = ap suc (length-+L-distrib xs ys)

vecToList : {A : Set} {n : ℕ} → Vec A n → List A
vecToList [] = []
vecToList (x ,- vec) = x ,- vecToList vec

vecToList-listToVec-id : {A : Set} → (xs : List A) → vecToList (snd (listToVec xs)) ≡ xs
vecToList-listToVec-id [] = refl
vecToList-listToVec-id (x ,- xs) = ap (x ,-_) (vecToList-listToVec-id xs)

vTake : {A : Set} {m n : ℕ} → n ≤ m → Vec A m → Vec A n
vTake ltezero xs = []
vTake (ltesuc proof) (x ,- xs) = x ,- vTake proof xs

vTake-id : {A : Set} (n : ℕ) (v : Vec A n) → (vTake (<=-refl {n}) v) ≡  v
vTake-id zero [] = refl
vTake-id (suc n) (x ,- xs) = ap (x ,-_) (vTake-id n xs)

-- m - n
-- d for difference
difference<= : (m n : ℕ) → n ≤ m → ℕ >< λ d → m ≡ (n +ℕ d)
difference<= m n  proof = {!!}

-- naively reverse a list, by appending at the end
reverse : {A : Set} → List A → List A
reverse [] = []
reverse (x ,- xs) = reverse xs +L (x ,- [])

_ : reverse (1 ,- 2 ,- 3 ,- []) ≡ (3 ,- 2 ,- 1 ,- [])
_ = refl

-- might need +L-assoc here
reverse-+L-distrib : {A : Set} (xs ys : List A) → reverse (xs +L ys) ≡ (reverse ys +L reverse xs)
reverse-+L-distrib [] ys = ≡-symm (+L-right-id (reverse ys))
reverse-+L-distrib (x ,- xs) ys =
  (reverse (xs +L ys) +L (x ,- []))
    =[ ap (_+L (x ,- [])) (reverse-+L-distrib xs ys) ]
  ((reverse ys +L reverse xs) +L (x ,- []))
    =[ +L-assoc (reverse ys) (reverse xs) (x ,- []) ]
  (reverse ys +L (reverse xs +L (x ,- [])))
    QED

reverse-involut : {A : Set} (xs : List A) -> reverse (reverse xs) ≡ xs
reverse-involut [] = refl
reverse-involut (x ,- xs) =
  reverse (reverse xs +L (x ,- []))
    =[ reverse-+L-distrib (reverse xs) (x ,- []) ]
  x ,- reverse (reverse xs)
    =[ ap (x ,-_) (reverse-involut xs) ]
  x ,- xs
    QED

go : {A : Set} -> List A -> List A -> List A
go [] acc = acc
go (x ,- xs) acc = go xs (x ,- acc)

_ : go (1 ,- 2 ,- []) [] ≡ (2 ,- 1 ,- [])
_ = refl
_ : go (1 ,- 2 ,- []) (4 ,- 5 ,- []) ≡ (2 ,- 1 ,- 4 ,- 5 ,- [])
_ = refl


-- implement an O(n) reverse by using go
linear-reverse : {A : Set} -> List A -> List A
linear-reverse xs = go xs []

go-reverse : {A : Set} (xs ys : List A) -> go xs ys ≡ (reverse xs +L ys)
go-reverse [] ys = refl
go-reverse (x ,- xs) ys =
  go xs (x ,- ys)
    =[ go-reverse xs (x ,- ys) ]
  (reverse xs +L (x ,- ys))
    =< +L-assoc (reverse xs) (x ,- []) ys ]=
  ((reverse xs +L (x ,- [])) +L ys)
    QED


linear-reverse-is-reverse : {A : Set} (xs : List A) -> linear-reverse xs ≡ reverse xs
linear-reverse-is-reverse [] = refl
linear-reverse-is-reverse (x ,- xs) =
  linear-reverse (x ,- xs)
    =[ refl ]
  go (x ,- xs) []
    =[ go-reverse xs (x ,- []) ]
  (reverse xs +L (x ,- []))
    QED


map-+L-distrib : {A B : Set} -> (f : A -> B) -> (xs ys : List A) -> map f (xs +L ys) ≡ (map f xs +L map f ys)
map-+L-distrib f [] ys = refl
map-+L-distrib f (x ,- xs) ys = ap (f x ,-_) (map-+L-distrib f xs ys)

id : {A : Set} -> A -> A
id x = x
map-id : {A : Set} (xs : List A) -> map id xs ≡ xs
map-id [] = refl
map-id (x ,- xs) =
  id x ,- map id xs
    =[]
  x ,- map id xs
    =[ ap (x ,-_) (map-id xs) ]
  x ,- xs
    QED

_<<_ : {A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
(f << g) x = f (g x)

map-compose : {A B C : Set} -> (f : B -> C) (g : A -> B) -> (xs : List A) -> map (f << g) xs ≡ map f (map g xs)
map-compose f g [] = refl
map-compose f g (x ,- xs) =
  ((f << g) x ,- map (f << g) xs)
    =[]
  ( f (g x) ,- map (f << g) xs)
    =[ ap (f (g x) ,-_) (map-compose f g xs) ]
  f (g x) ,- map f (map g xs)
  QED

foldl : {A B : Set} -> (B -> A -> B) -> B -> List A -> B
foldl f init [] = init
foldl f init (x ,- xs) = foldl f (f init x) xs

foldr : {A B : Set} -> (A -> B -> B) -> B -> List A -> B
foldr f init [] = init
foldr f init (x ,- xs) = f x (foldr f init xs)

foldr-+L :
  {A B : Set}
  (f : A -> B -> B)
  (xs ys : List A)
  (v : B) ->
  foldr f (foldr f v ys) xs ≡ foldr f v (xs +L ys)
foldr-+L f [] ys v = refl
foldr-+L f (x ,- xs) ys v = ap (f x) (foldr-+L f xs ys v) 

map-foldr :
  {A B : Set}
  (f : A -> B)
  (xs : List A) ->
  map f xs ≡ foldr (\x r -> f x ,- r) [] xs
map-foldr f [] = refl
map-foldr f (x ,- xs) = ap (f x ,-_) (map-foldr f xs)

even+even : (n m : ℕ) → Even n → Even m → Even (n +ℕ m)
even+even n m evenN evenM with decEvenOrOdd n
even+even n m evenN evenM | inl n' with decEvenOrOdd m
even+even n m evenN evenM | inl n' | inl m' = even+even n {!!} {!!} {!!}
even+even n m evenN evenM | inl n' | inr m' = {!!}
even+even n m evenN evenM | inr n' = {!!}

times-2-is-double : {n : ℕ} → n *ℕ 2 ≡ double n
times-2-is-double {zero} = refl
times-2-is-double {suc n} = ap suc (ap suc times-2-is-double)

lemma : (n : ℕ) → (n +ℕ n) ≡ double n
lemma zero = refl
lemma (suc n) =
  suc (n +ℕ suc n)
   =[ ≡-symm (ap suc (+ℕ-right-suc n n)) ]
  suc (suc (n +ℕ n))
    =[ ap suc (ap suc (add-same-double n)) ]
  suc (suc (n *ℕ 2))
    =[ ap suc (ap suc times-2-is-double) ]
 suc (suc (double n))
   QED

add-two-Even : (n m : ℕ) -> Even m -> Even (n +ℕ n +ℕ m)
add-two-Even n m evenM = {!!}

