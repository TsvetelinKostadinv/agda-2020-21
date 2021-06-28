{-# OPTIONS --no-unicode #-}

module Lecture.FourStart where

open import Lib.List
open import Lib.Eq
open import Lib.Nat
open import Lib.Sum
open import Lib.One
open import Lib.Zero
open import Lib.Sigma

-- describe modules
-- show example with open

module Listy (A : Set) where
  x : Nat
  x = zero

  id' : A -> A
  id' y = y

  bla : Nat -> Set
  bla n = A

-- z : Nat
-- z = {!id'!}

-- show bst constructions
-- write Bound
-- write LeqBound
-- write BST
-- explain "pushing down constraints"
-- examples for bst
-- show tree diagram

LeqNat : Nat -> Nat -> Set
LeqNat zero m = One
LeqNat (suc n) zero = Zero
LeqNat (suc n) (suc m) = LeqNat n m

_ : 3 <= 5
_ = osuc (osuc (osuc ozero))

_ : LeqNat 3 5
_ = <>

decLeqNat : (n m : Nat) -> LeqNat n m + LeqNat m n
decLeqNat zero m = inl <>
decLeqNat (suc n) zero = inr <>
decLeqNat (suc n) (suc m) = decLeqNat n m

<=-LeqNat : {n m : Nat} -> n <= m -> LeqNat n m
<=-LeqNat ozero = <>
<=-LeqNat (osuc p) = <=-LeqNat p

module
  Sorting
    (Key : Set)
    (Leq : Key -> Key -> Set)
    (_<=?_ : (x y : Key) -> Leq x y + Leq y x)
  where

  data Bound : Set where
    -inf : Bound
    inKey : Key -> Bound
    +inf : Bound

  LeqBound : Bound -> Bound -> Set
  LeqBound -inf y = One
  LeqBound x +inf = One
  LeqBound (inKey x) (inKey y) = Leq x y
  LeqBound _ _ = Zero

  data BST (lo hi : Bound) : Set where
    empty : LeqBound lo hi -> BST lo hi
    node :
      (k : Key) ->
      (left : BST lo (inKey k)) ->
      (right : BST (inKey k) hi) ->
      BST lo hi

  -- you can use _<=?_ to compare two values
  insert :
    {lo hi : Bound} (k : Key) ->
    LeqBound lo (inKey k) -> 
    LeqBound (inKey k) hi ->
    BST lo hi -> 
    BST lo hi
  insert k lok khi (empty x) = node k (empty lok) (empty khi)
  insert k lok khi (node root left right) with k <=? root
  insert k lok khi (node root left right) | inl x = node root (insert k lok x left) right -- k <= root
  insert k lok khi (node root left right) | inr x = node root left (insert k x khi right) -- k >= root

  makeTree : List Key -> BST -inf +inf
  makeTree [] = empty <>
  makeTree (x ,- xs) = insert x <> <> (makeTree xs)

  -- use the same idea as in BST to define "ordered lists"
  -- be careful about what constraints you need in your recursive case!
  data OList (lo hi : Bound) : Set where
    empty : LeqBound lo hi -> OList lo hi
    ocons : (k : Key) -> LeqBound lo (inKey k) -> OList (inKey k) hi -> OList lo hi

  -- append ordered lists
  -- note that we require a key to "bridge" the two lists
  -- try to implement
  -- append : {lo mid hi : Bound} -> OList lo mid -> OList mid hi -> OList lo hi
  -- and see where you get stuck
  appendKeyed : {lo hi : Bound} -> (k : Key) -> OList lo (inKey k) -> OList (inKey k) hi -> OList lo hi
  appendKeyed k (empty leqbK) oys = ocons k leqbK oys
  appendKeyed k (ocons x lo<=x oxs) oys = ocons x lo<=x (appendKeyed k oxs oys)

  flatten : {lo hi : Bound} -> BST lo hi -> OList lo hi
  flatten (empty x) = empty x
  flatten (node k left right) = appendKeyed k (flatten left) (flatten right)

  sort : List Key -> OList -inf +inf
  sort xs = flatten (makeTree xs)

--          2
--       1  .  3
--     <=.<=.<=.<=
--       .  .  .
-- -inf<=1<=2<=3<=+inf

open Sorting Nat LeqNat decLeqNat

one : BST -inf (inKey 2)
one = node 1 (empty <>) (empty <>)

three : BST (inKey 2) +inf
three = node 3 (empty <>) (empty <>)

two : BST -inf +inf
two = node 2 one three

-- TODO:
-- grey highlight

-- plusnat : Nat -> Nat -> Nat
-- plusnat zero m = m
-- plusnat n zero = n
-- plusnat (suc n) m = suc (plusnat n m)
--
-- f : (m : Nat) -> plusnat zero m == m
-- f m = refl
--
-- g : (m : Nat) -> plusnat m zero == m
-- g zero = {!!}
-- g (suc m) = {!!}

-- case n of
--   zero -> m
--   suc n ->
--     case m of
--       zero -> n
--       ...

-- plusnat n m == plusnat m n // n -> zero
-- plusnat zero m -> m
-- Goal: m == plusnat m zero
-- m == m
-- plusnat-commut : (n m : Nat) -> plusnat n m == plusnat m n
-- plusnat-commut zero m = {!!}
-- plusnat-commut (suc n) m = {!!}

-- "pipe"s in goal
-- with generalises (show vs lambda)
-- show generalised:
-- goal type

-- original args
-- other later withs
--
-- dots ??

-- asd : Nat -> Nat
-- asd n with decLeqNat n 5
-- ... | inl x = 5
-- ... | inr x = n
--
-- pasd : (n : Nat) -> LeqNat 5 n -> asd n == n
-- pasd n x with decLeqNat n 5
-- ... | inl x1 = {!!}
-- ... | inr x1 = {!!}


-- bla : (n : Nat) -> n == 10 -> 0 == n
-- bla n x with n
-- ... | z = {!z!}
--
-- bla2 : (n : Nat) -> 0 == n
-- bla2 n with n
-- bla2 n | zero with 5
-- bla2 n | zero | q = {!!}
-- bla2 n | suc z = {!!}

-- pasd : (n : Nat) -> 6 <= n -> asd n == n
-- pasd = {!!}

-- +N-right-zero' : (n : Nat) -> n +N 0 == n
-- +N-right-zero' zero = refl
-- -- +N-right-zero' (suc n) rewrite +N-right-zero' n = refl
-- +N-right-zero' (suc n) with n +N 0 with +N-right-zero' n
-- ... | .n | refl = refl

-- Goal: suc (n +N 0) == suc n
-- ————————————————————————————————————————————————————————————
-- z : n +N 0 == n
-- n : Nat
-- after
-- Goal: suc u == suc n
-- ————————————————————————————————————————————————————————————
-- z : u == n
-- u : Nat
-- n : Nat


-- used a module to introduce global vars
-- in here, you can compare values for equality with _==?_
-- in all proofs for functions defined with a `with`
-- you're most likely going to need to do another with
-- because your proof will be stuck on the result of the with in the original function def
module listy {A : Set} {_==?_ : (x y : A) -> Dec (x == y)} where

  infix 10 _In_

  data _In_ (x : A) : List A -> Set where
    here : {xs : List A} -> x In (x ,- xs)
    there : {y : A} {xs : List A} -> x In xs -> x In (y ,- xs)

{-
  +L-monoL-In : {y : A} {ys : List A} -> (xs : List A) -> y In ys -> y In xs +L ys
  +L-monoL-In [] yInYs = yInYs
  +L-monoL-In (x ,- xs) yInYs = there (+L-monoL-In xs yInYs)

  +L-splits-In : {x : A} (xs ys : List A) -> x In xs +L ys -> x In xs + x In ys
  +L-splits-In [] ys xInSum = inr xInSum
  +L-splits-In (x ,- xs) ys here = inl here
  +L-splits-In (headXS ,- xs) ys (there xInSum) with +L-splits-In xs ys xInSum
  +L-splits-In (headXS ,- xs) ys (there xInSum) | inl inXS = inl (there inXS)
  +L-splits-In (headXS ,- xs) ys (there xInSum) | inr inYS = inr inYS

  notIn[] : {x : A} -> x In [] -> Zero
  notIn[] ()

  nowhere : {x y : A} {ys : List A} -> (x == y -> Zero) -> (x In ys -> Zero) -> x In y ,- ys -> Zero
  nowhere xyZero xInYSZero here = xyZero refl
  nowhere xyZero xInYSZero (there xInYYS) = xInYSZero xInYYS

  -- if there is one, return the first x in the list
  find : (x : A) (xs : List A) -> Dec (x In xs)
  find x [] = inl notIn[]
  find x (x1 ,- xs) with x ==? x1
  find x (x1 ,- xs) | inl no with find x xs
  find x (x1 ,- xs) | inl no | inl notInTail = inl (nowhere no notInTail)
  find x (x1 ,- xs) | inl no | inr x2 = inr (there x2)
  find x (x ,- xs) | inr refl = inr here

  -- delete all the occurrences of x in the list
  remove : (x : A) -> (xs : List A) -> List A
  remove x [] = []
  remove x (head ,- xs) with x ==? head 
  remove x (head ,- xs) | inl no = head ,- remove x xs
  remove x (x ,- xs) | inr refl = remove x xs

  -- You don't say
  remove-removes : (xs : List A) -> (x : A) -> x In remove x xs -> Zero
  remove-removes [] x ()
  remove-removes (head ,- xs) x with x ==? head
  remove-removes (head ,- xs) x | inl no with find x (remove x xs)
  remove-removes (head ,- xs) x | inl no | inl notInTail = nowhere no notInTail -- nowhere no notInTail
  remove-removes (head ,- xs) x | inl no | inr inTail = λ _ -> remove-removes xs x inTail
  remove-removes (x ,- xs) x | inr refl = remove-removes xs x

  remove-keeps : (xs : List A) (y : A) -> y In xs -> (x : A) -> (x == y -> Zero) -> y In remove x xs
  remove-keeps [] y () x x!=y
  remove-keeps (y ,- xs) y here x x!=y with x ==? y
  remove-keeps (y ,- xs) y here x x!=y | inl no = here
  remove-keeps (y ,- xs) y here .y x!=y | inr refl = zero-elim (x!=y refl)
  remove-keeps (x1 ,- xs) y (there yInXS) x x!=y with x ==? x1
  remove-keeps (x1 ,- xs) y (there yInXS) x x!=y | inl no = there (remove-keeps xs y yInXS x x!=y)
  remove-keeps (x ,- xs) y (there yInXS) .x x!=y | inr refl = remove-keeps xs y yInXS x x!=y

  -- xs Sub ys - xs is a subsequence of ys
  -- [] Sub []
  -- 5 ,- [] Sub 5 ,- []
  -- 3 ,- 5 ,- [] Sub 3 ,- 5 ,- []
  -- 3 ,- 5 ,- [] Sub 3 ,- 5 ,- 4 ,- []
  -- 3 ,- 5 ,- [] Sub 3 ,- 4 ,- 5 ,- []
  data _Sub_ : List A -> List A -> Set where
    s[] : [] Sub []
    s-cons : {x : A} {xs ys : List A} -> xs Sub ys -> (x ,- xs) Sub (x ,- ys)
    s-skip : {x : A} {xs ys : List A} -> xs Sub ys -> xs Sub (x ,- ys)

  infix 10 _Sub_

  s[]-all : {xs : List A} -> [] Sub xs
  s[]-all {[]} = s[]
  s[]-all {x ,- xs} = s-skip (s[]-all {xs})

  Sub-refl : (xs : List A) -> xs Sub xs
  Sub-refl [] = s[]
  Sub-refl (x ,- xs) = s-cons (Sub-refl xs)

  -- try to make the definition "as lazy" as possible - meaning pattern matching on as few things as possible
  -- this will affect your proof for Sub-trans-assoc
  Sub-trans : {xs ys zs : List A} -> xs Sub ys -> ys Sub zs -> xs Sub zs
  Sub-trans xsSubYs s[] = xsSubYs
  Sub-trans (s-cons xsSubYs) (s-cons ysSubZs) = s-cons (Sub-trans xsSubYs ysSubZs)
  Sub-trans (s-skip xsSubYs) (s-cons ysSubZs) = s-skip (Sub-trans xsSubYs ysSubZs)
  Sub-trans xsSubYs (s-skip ysSubZs) = s-skip (Sub-trans  xsSubYs ysSubZs)

  +L-monoL-Sub : (xs ys : List A) -> xs Sub (xs +L ys)
  +L-monoL-Sub [] ys = s[]-all
  +L-monoL-Sub (x ,- xs) ys = s-cons (+L-monoL-Sub xs ys)

  +L-monoR-Sub : (xs ys : List A) -> xs Sub (ys +L xs)
  +L-monoR-Sub xs [] = Sub-refl xs
  +L-monoR-Sub [] (y ,- ys) = s-skip s[]-all
  +L-monoR-Sub (x ,- xs) (y ,- ys) = s-skip (+L-monoR-Sub (x ,- xs) ys)

  Sub-all-In : {xs ys : List A} -> xs Sub ys -> {x : A} -> x In xs -> x In ys
  Sub-all-In (s-cons xsSubYs) {x} here = here
  Sub-all-In (s-skip xsSubYs) {x} here = there (Sub-all-In xsSubYs here)
  Sub-all-In (s-cons xsSubYs) {x} (there xInXs) = there (Sub-all-In xsSubYs xInXs)
  Sub-all-In (s-skip xsSubYs) {x} (there xInXs) = there (Sub-all-In xsSubYs (there xInXs))

  remove-Sub : (x : A) (xs : List A) -> remove x xs Sub xs
  remove-Sub x [] = s[]
  remove-Sub x (x1 ,- xs) with x ==? x1
  remove-Sub x (x1 ,- xs) | inl no = s-cons (remove-Sub x xs)
  remove-Sub x (x ,- xs) | inr refl = s-skip (remove-Sub x xs)

  -- might need to make an implicit arg explicit in one of the cases
  remove-preserves-Sub : {xs ys : List A} (x : A) -> xs Sub ys -> remove x xs Sub ys
  remove-preserves-Sub {xs} x xsSubYs = Sub-trans (remove-Sub x xs) xsSubYs

  ,-Sub-remove : {xs ys : List A} (x : A) -> xs Sub x ,- ys -> remove x xs Sub ys
  ,-Sub-remove x (s-cons xsSubXYs) with x ==? x
  ,-Sub-remove x (s-cons xsSubXYs) | inl no = zero-elim (no refl)
  ,-Sub-remove x (s-cons xsSubXYs) | inr refl = remove-preserves-Sub x xsSubXYs
  ,-Sub-remove x (s-skip xsSubXYs) = remove-preserves-Sub x xsSubXYs

  Sub-trans-assoc :
    {xs ys zs vs : List A} (sub1 : xs Sub ys) (sub2 : ys Sub zs) (sub3 : zs Sub vs) ->
    Sub-trans (Sub-trans sub1 sub2) sub3 == Sub-trans sub1 (Sub-trans sub2 sub3)
  Sub-trans-assoc xsSubYs ysSubZs s[] = refl
  Sub-trans-assoc (s-cons xsSubYs) (s-cons ysSubZs) (s-cons zsSubVs) = ap s-cons (Sub-trans-assoc xsSubYs ysSubZs zsSubVs)
  Sub-trans-assoc (s-skip xsSubYs) (s-cons ysSubZs) (s-cons zsSubVs) = ap s-skip (Sub-trans-assoc xsSubYs ysSubZs zsSubVs)
  Sub-trans-assoc s[] (s-skip ysSubZs) (s-cons zsSubVs) = ap s-skip (Sub-trans-assoc s[] ysSubZs zsSubVs)
  Sub-trans-assoc (s-cons xsSubYs) (s-skip ysSubZs) (s-cons zsSubVs) = ap s-skip (Sub-trans-assoc (s-cons xsSubYs) ysSubZs zsSubVs)
  Sub-trans-assoc (s-skip xsSubYs) (s-skip ysSubZs) (s-cons zsSubVs) = ap s-skip (Sub-trans-assoc (s-skip xsSubYs) ysSubZs zsSubVs)
  Sub-trans-assoc xsSubYs ysSubZs (s-skip zsSubVs) = ap s-skip (Sub-trans-assoc xsSubYs ysSubZs zsSubVs)
-}
{-
decNatEq : (n m : Nat) -> Dec (n == m)
decNatEq = {!!}

open listy {Nat} {decNatEq}

_ : 3 In 3 ,- 5 ,- []
_ = here

_ : 5 In 3 ,- 5 ,- []
_ = there here

5notIn[] : 5 In [] -> Zero
5notIn[] ()

5notIn3 : 5 In 3 ,- [] -> Zero
5notIn3 (there ())

_ : [] Sub []
_ = s[]

_ : 5 ,- [] Sub 5 ,- []
_ = s-cons s[]

_ : 3 ,- 5 ,- [] Sub 3 ,- 5 ,- []
_ = s-cons (s-cons s[])

_ : 3 ,- 5 ,- [] Sub 3 ,- 5 ,- 4 ,- []
_ = s-cons (s-cons (s-skip s[]))

_ : 3 ,- 5 ,- [] Sub 3 ,- 4 ,- 5 ,- []
_ = s-cons (s-skip (s-cons s[]))

32notSub23 : 3 ,- 2 ,- [] Sub 2 ,- 3 ,- [] -> Zero
32notSub23 (s-skip (s-cons ()))
32notSub23 (s-skip (s-skip ()))

332notSub32 : 3 ,- 3 ,- 2 ,- [] Sub 3 ,- 2 ,- [] -> Zero
332notSub32 (listy.s-cons (listy.s-skip ()))
332notSub32 (listy.s-skip (listy.s-skip ()))
-}
