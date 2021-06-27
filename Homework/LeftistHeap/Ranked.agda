{-# OPTIONS --no-unicode #-}

module Homework.LeftistHeap.Ranked where

open import Homework.LeftistHeap.Common
open import Lib.Sum
open import Lib.One
open import Lib.Zero
open import Lib.Nat
open import Lib.Eq

-- type index, since we will need it to vary for the different constructors
data Heap : Rank -> Set where
  empty : Heap 0
  node : {r1 r2 : Rank} -> {_ : Leq r2 r1} 
          -> Priority 
          -> Heap r1 -> Heap r2 -> Heap (suc (r1 +N r2))

-- 1.

-- 2.

-- 3.
rank : {r : Rank} -> Heap r -> Rank
rank {r} heap = r

mkNode :
  {lr rr : Rank}
  -> Priority -> Heap lr -> Heap rr -> Heap (suc (lr +N rr))
mkNode {lr} {rr} p heapL heapR with decLeq rr lr
mkNode {lr} {rr} p heapL heapR | inl x = node {_} {_} {x} p heapL heapR
mkNode {lr} {rr} p heapL heapR | inr x rewrite +N-commut lr rr = node {_} {_} {x} p heapR heapL

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

{-# TERMINATING #-}
merge :
  {lr rr : Rank} ->
  Heap lr -> Heap rr -> Heap (lr +N rr)
merge empty empty = empty
merge {lr} {rr} h1@(node x heapL heapL1) empty rewrite +N-right-zero lr = h1
merge {lr} {rr} empty h2@(node x heapR heapR1) = h2
merge {lr} {rr} h1@(node p1 left1 right1) h2@(node p2 left2 right2) with decLeq p1 p2
merge {lr} {rr} h1@(node p1 left1 right1) h2@(node p2 left2 right2) | inl x 
    rewrite +N-assoc-no-braces (rank left1) (rank right1) (suc(rank left2 +N rank right2)) 
  = mkNode p1 left1 (merge right1 h2)
merge {lr} {rr} h1@(node p1 left1 right1) h2@(node p2 left2 right2) | inr x
  rewrite (==-symm (helper (rank left2) (rank right2) (rank left1) (rank right1)))
  = mkNode p2 left2 (merge right2 h1)
  
singleton : Priority -> Heap 1
singleton p = mkNode p empty empty

insert : {r : Rank} -> Priority -> Heap r -> Heap (suc r)
insert p heap = merge (singleton p) heap

findMin : {r : Rank} -> Heap r -> {_ : Leq 1 r} -> Priority
findMin {0} empty {()}
findMin (node x left right) = x

delMin : { r : Rank} -> Heap (suc r) -> Heap r
delMin (node x left right) = merge left right
