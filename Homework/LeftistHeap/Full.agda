{-# OPTIONS --no-unicode #-}

module Homework.LeftistHeap.Full where

open import Lib.Nat
open import Lib.One
open import Lib.Eq
open import Lib.List
open import Lib.Sum
open import Homework.LeftistHeap.Common
open import Lecture.FourStart

-- 0.
data Heap (lower : Priority) : Rank -> Set where
    empty : Heap lower 0
    node : {r1 r2 : Rank} -> {_ : Leq r2 r1} 
            -> {x y : Priority} -> (p : Priority) 
            -> {_ : Leq lower p} -> {_ : Leq p x} -> {_ : Leq p y}  
            -> Heap x r1 -> Heap y r2 -> Heap lower (suc (r1 +N r2))

-- 1.

-- 2.

-- 3.
mkNode : {lr rr : Rank} {b : Priority} (p : Priority) -> Leq b p -> Heap p lr -> Heap p rr -> Heap b (suc (lr +N rr))
mkNode {lr}{rr}  {b} p leqBP heapPLR heapPRR with decLeq rr lr
mkNode {lr} {rr} {b} p leqBP heapPLR heapPRR | inl x = node {b} {_} {_} {x} {p} {p} p {leqBP} {Leq-refl p} {Leq-refl p} heapPLR heapPRR
mkNode {lr} {rr} {b} p leqBP heapPLR heapPRR | inr x rewrite +N-commut lr rr = node {b} {_} {_} {x} {p} p {leqBP} {Leq-refl p} {Leq-refl p} heapPRR heapPLR


-- 3.
rank : {lower : Priority}{r : Rank} -> Heap lower r -> Rank
rank {lower}{r} heap = r

weakenHeap : {r : Rank} (n m : Priority) -> Leq n m -> Heap m r -> Heap n r
weakenHeap n m leqNM empty = empty
weakenHeap n m leqNM (node {_}{_}{_}{pl}{pr} p {m<=p}{p<=pl}{p<=pr} l r)
    = mkNode {_}{_} {n} p (Leq-trans n m p leqNM m<=p ) 
        (weakenHeap p _ p<=pl l) 
        (weakenHeap p _ p<=pr r)

{-# TERMINATING #-}
merge : {lr rr : Rank} {p : Priority} -> Heap p lr -> Heap p rr -> Heap p (lr +N rr)
merge empty empty = empty
merge empty h2@(node p l r) = h2
merge {lr} {ll} {p} h1@(node p1 l r) empty rewrite (+N-right-zero (rank h1)) = h1
merge {lr} {ll} {p} h1@(node p1 l1 r1) h2@(node p2 l2 r2) with decLeq p1 p2
merge {lr} {ll} {p} h1@(node p1 {p<=p1} {p1<=pl1} {p1<=pr2} l1 r1) h2@(node p2 {p<=p2} {p2<=prl1} {p2<=prr2} l2 r2) | inl x 
        rewrite (+N-assoc-no-braces (rank l1) (rank r1) (suc (rank l2 +N rank r2)))
    = mkNode p (Leq-refl p)
        (weakenHeap p _ (Leq-trans p p1 _ p<=p1 p1<=pl1) l1) 
        (merge 
            (weakenHeap p _ (Leq-trans p p1 _ p<=p1 p1<=pr2) r1) 
            (weakenHeap p _ (Leq-refl p) h2))
merge {lr} {ll} {p} h1@(node p1 {p<=p1} {p1<=pl1} {p1<=pr2} l1 r1) h2@(node p2 {p<=p2} {p2<=prl1} {p2<=prr2} l2 r2) | inr x
        rewrite (==-symm (helper (rank l2) (rank r2) (rank l1) (rank r1)))
    = mkNode p (Leq-refl p) 
        (weakenHeap p _ (Leq-trans p p2 _ p<=p2 p2<=prl1 ) l2) 
        (merge 
            (weakenHeap p _ (Leq-trans p p2 _ p<=p2 p2<=prr2) r2) 
            (weakenHeap p _ (Leq-refl p) h1) )

-- 4.
singleton : (p x : Priority) -> Leq p x -> Heap p 1
singleton p x p<=x = mkNode x p<=x empty empty

insert : {r : Rank} {p : Priority} (x : Priority) -> Heap p r -> Heap (min p x) (suc r)
insert {r} {p} x heap with decLeq p x
insert {r} {p} x heap | inl x1 = merge  (singleton p x x1) heap
insert {r} {p} x heap | inr x1 = merge (singleton x x (Leq-refl x)) (weakenHeap x p x1 heap)

-- 5.
findMin : {p : Priority} {r : Rank} -> Heap p (suc r) -> Priority
findMin (node p heap heap1) = p

delMin : {p : Priority} {r : Rank} -> Heap p (suc r) -> Heap p r
delMin {p} (node p1 {p<=p1} {p1<=lp} {p1<=rp} left right) 
    = merge 
        (weakenHeap _ _ (Leq-trans p p1 _ p<=p1 p1<=lp) left) 
        (weakenHeap _ _ (Leq-trans p p1 _ p<=p1 p1<=rp) right)

-- 6.
minimum : List Priority -> Priority
minimum [] = 0 -- should have been a Maybe Priority, but then we can't use in the type signature
minimum (x ,- xs) with decLeq x (minimum xs)
minimum (x ,- xs) | inl x1 = x
minimum (x ,- xs) | inr x1 = minimum xs

==-no-sucs : (x y : Nat) -> suc x == suc y -> x == y
==-no-sucs x .x refl = refl

decEq : (x y : Priority) -> Dec (x == y)
decEq zero zero = yes refl
decEq zero (suc y) = no (\ ())
decEq (suc x) zero = no (\ ())
decEq (suc x) (suc y) with decEq x y
decEq (suc x) (suc y) | no nope = no \ x2 -> nope (==-no-sucs x y x2)
decEq (suc x) (suc .x) | yes refl = yes refl

open Lecture.FourStart.listy {Priority} {decEq}

minimum-is-lowest : (x : Priority) -> (xs : List Priority) -> Leq (minimum (x ,- xs)) x
minimum-is-lowest zero [] = <>
minimum-is-lowest (suc x) [] = <>
minimum-is-lowest x tail@(x1 ,- xs) with decLeq x (minimum tail)
minimum-is-lowest x tail@(x1 ,- xs) | inl x<=min = Leq-refl x
minimum-is-lowest x tail@(x1 ,- xs) | inr min<=x with decLeq x1 (minimum xs)
minimum-is-lowest x tail@(x1 ,- xs) | inr min<=x | inl x2 = min<=x
minimum-is-lowest x tail@(x1 ,- xs) | inr min<=x | inr x2 = min<=x

{-# TERMINATING #-}
fromList : (xs : List Priority) -> Heap (minimum xs) (length xs)
fromList [] = empty
fromList xs@(x ,- rest) with decLeq x (minimum rest)
fromList xs@(x ,- rest) | inl x1 = merge (singleton x x (Leq-refl x)) (weakenHeap x _ x1 (fromList rest))
fromList xs@(x ,- rest) | inr x1 = merge (weakenHeap (minimum rest) x x1 (singleton x x (Leq-refl x))) (fromList rest)
