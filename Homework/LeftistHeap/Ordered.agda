{-# OPTIONS --no-unicode #-}

module Homework.LeftistHeap.Ordered where

open import Lib.Sum
open import Lib.One
open import Homework.LeftistHeap.Common
open import Lib.Nat

-- 0.
-- parametrised by the lower bound of the heap
data Heap (lower : Priority) : Set where
  empty : Heap lower
  node  : {x y : Priority} -> {_ : Leq lower x} -> {_ : Leq lower y} 
          -> Rank -> (p : Priority )
          -> {_ : Leq lower p}
          -> Heap x -> Heap y
          -> Heap lower

-- 1.
correct : Heap 0
correct = node {0} {1} {0} 2 0 (node {1} {2} {2} 1 2 empty empty) empty

-- 2.
wrongRank : Heap 0
wrongRank = node {0} {1} {0} 3521123 0 (node {1} {2} {2} 1 2 empty empty) empty

-- 3.
rankPropertyWrong : Heap 0
rankPropertyWrong = node {0} {0} {1} 3521123 0 empty (node {1} {2} {2} 1 2 empty empty)

-- 4.
rank : {lower : Priority} -> Heap lower -> Rank
rank empty = 0
rank (node r prior left right) = suc (rank left +N rank right)

mkNode :
  (x : Priority) -> {lower : Priority}
  -> {_ : Leq lower x}
  -> Heap lower -> Heap lower -> Heap lower
mkNode x {lower} {leqLowX} heapX heapY = node {lower} {lower} {lower} {Leq-refl lower} {Leq-refl lower} (suc ((rank heapX) +N (rank heapY))) x {leqLowX} heapX heapY

weakenHeap : (n m : Priority) -> Leq n m -> Heap m -> Heap n
weakenHeap n m leqNM empty = empty
weakenHeap n m leqNM (node {lPrior} {rPrior} {lProof} {rProof} r p left right) 
    = mkNode n {n} {Leq-refl n} 
        (weakenHeap n lPrior (Leq-trans n m lPrior leqNM lProof) left) 
        ((weakenHeap n rPrior (Leq-trans n m rPrior leqNM rProof) right))

{-# TERMINATING #-}
merge :
  {lower : Priority} -> 
  Heap lower -> Heap lower -> Heap lower
merge empty empty = empty
merge h1@(node r p left right) empty = h1
merge empty h2@(node r p left right) = h2
merge {lower} heap1@(node r1 p1 left1 right1) heap2@(node r2 p2 left2 right2) with decLeq p1 p2
merge {lower} heap1@(node {lx} {ly} {leqLowerlx} {leqLowerly} r1 p1 {leqLowerP1} left1 right1) heap2@(node {rx} {ry} {leqLowerrx} {leqLowerry}  r2 p2 left2 right2) | inl x 
    = mkNode p1 {lower} {leqLowerP1}
         (weakenHeap _ _ leqLowerlx left1) -- Leq p1 lx
        (merge (weakenHeap _ _ leqLowerly right1) heap2)
merge {lower} heap1@(node {lx} {ly} {leqLowerlx} {leqLowerly} r1 p1 left1 right1) heap2@(node {rx} {ry} {leqLowerrx} {leqLowerry}  r2 p2 left2 right2) | inr x 
    = mkNode lower {_} {Leq-refl lower} 
        (weakenHeap lower rx leqLowerrx left2) 
        (merge (weakenHeap lower ry leqLowerry right2) heap1)

-- 5.
singleton : {lower : Priority} (x : Priority) -> Leq lower x -> Heap lower
singleton {lower} x leqLowerX = mkNode x {lower} {leqLowerX} empty empty

insert : {lower : Priority} (x : Priority) -> Heap lower -> Heap (min lower x)
insert {lower} x heap with decLeq lower x
insert {lower} x heap | inl x1 = merge (singleton x x1) heap
insert {lower} x heap | inr x1 = merge (singleton x (Leq-refl x)) (weakenHeap x lower x1 heap)

-- 6.
findMin : {lower : Priority} -> Heap lower -> Maybe Priority
findMin empty = no
findMin (node r p left right) = yes p

delMin : {lower : Priority} -> Heap lower -> Maybe (Heap lower)
delMin empty = no
delMin (node {lp} {rp} {leqLowerLP} {leqLowerRP} r p left right) = yes (merge (weakenHeap _ _ leqLowerLP left) (weakenHeap _ _ leqLowerRP right))
