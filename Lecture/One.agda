module Lectures.One where

-- Impossible event = absurd
data Zero : Set where

zero-elim : {A : Set} → Zero → A
zero-elim () -- impossible event

-- The truth event
data One : Set where
  <> : One

-- The trivial proof
trivial : {A : Set} → A → One
trivial a = <>

-- The either type
data _+_ (A : Set) (B : Set) : Set where
  inl : A → A + B
  inr : B → A + B

-- Swaps the types in the sum ( proves it is symetric )
swap-+ : {A B : Set} → A + B → B + A
swap-+ (inl x) = inr x
swap-+ (inr x) = inl x

-- The pair type
record _×_ (A : Set) (B : Set) : Set where
  constructor _,_ 
  field
    left : A
    right : B

-- Swaps the arguments of the product ( proves it is symetric )
swap-× : {A B : Set} → A × B → B × A
swap-× record { left = left ; right = right } = record { left = right; right = left}

-- The simple 2 type
data Bool : Set where
  true  : Bool
  false : Bool

--data _≡_ :  (a b : Bool) → Set where
--  refl : {x : Bool} → x ≡ x
--  sym : {a b : Bool} → (a ≡ b) → (b ≡ a)
--  trans : {a b c : Bool} → (a ≡ b) → (b ≡ c) → (a ≡ c)
--
--≡-reduce : {a b : Bool} → (a ≡ b) → Set
--≡-reduce {true} {true} proof = One
--≡-reduce {true} {false} proof = Zero
--≡-reduce {false} {true} proof = Zero
--≡-reduce {false} {false} proof = One

-- Equivalence of booleans
_≡_ : (a b : Bool) → Set
true ≡ true = One
true ≡ false = Zero
false ≡ true = Zero
false ≡ false = One

-- Proves ≡ is symetric
≡-sym : ∀{a b} → ( a ≡ b ) → (b ≡ a)
≡-sym {true} {true} proof = <>
≡-sym {true} {false} proof = proof
≡-sym {false} {true} proof = proof
≡-sym {false} {false} proof = <>

-- Proves ≡ is transitive
≡-trans : ∀{a b c} → (a ≡ b) → (b ≡ c) → (a ≡ c)
≡-trans {true} {true} {true} proof1 proof2 = <>
≡-trans {true} {true} {false} proof1 proof2  = proof2
≡-trans {true} {false} {true} proof1 proof2 = <>
≡-trans {true} {false} {false} proof1 proof2 = proof1
≡-trans {false} {true} {true} proof1 proof2 = proof1
≡-trans {false} {true} {false} proof1 proof2 = <>
≡-trans {false} {false} {true} proof1 proof2 = proof2
≡-trans {false} {false} {false} proof1 proof2 = <>

-- Negation operation for booleans
¬_ : Bool → Bool
¬ true  = false
¬ false = true

-- Proves ¬ is bipotent
¬-bipotent : Bool → Set
¬-bipotent a = (¬ ¬ a) ≡ a

¬-bipotent-proof : (a : Bool) → (¬ ¬ a) ≡ a
¬-bipotent-proof true = <>
¬-bipotent-proof false = <>

-- The or/disjunction  operation
_∨_ : (a b : Bool) → Bool
true ∨ b =  true
false ∨ b = b

-- Proves ∨ is commutative
∨-comm : ∀{a b} → (a ∨ b) ≡ (b ∨ a) 
∨-comm {true} {true} = <>
∨-comm {true} {false} = <>
∨-comm {false} {true} = <>
∨-comm {false} {false} = <>

-- Proves ∨ is reflexive
∨-bipotent : ∀{a : Bool} → (a ∨ a) ≡ a
∨-bipotent {true} = <>
∨-bipotent {false} = <>

-- The and/conjunction
_∧_ : (a b : Bool) → Bool
true ∧ b =  b 
false ∧ b = false

-- Proves ∧ is commutative
∧-comm : ∀{a b} → (a ∧ b) ≡ (b ∧ a)
∧-comm {true} {true} = <>
∧-comm {true} {false} = <>
∧-comm {false} {true} = <>
∧-comm {false} {false} = <>

-- Proves ∧ is reflexive
∧-bipotent : ∀{a} → (a ∧ a) ≡ a
∧-bipotent {true} = <>
∧-bipotent {false} = <>

-- De Morgan law for ∨
∨-de-morgan : ∀{a b} → ( ¬(a ∨ b)) ≡ ((¬ a) ∧ (¬ b))
∨-de-morgan {true} {true} = <>
∨-de-morgan {true} {false} = <>
∨-de-morgan {false} {true} = <>
∨-de-morgan {false} {false} = <>

-- De Morgan law for ∧
∧-de-morgan : ∀{a b} → ( ¬(a ∧ b)) ≡ ((¬ a) ∨ (¬ b))
∧-de-morgan {true} {true} = <>
∧-de-morgan {true} {false} = <>
∧-de-morgan {false} {true} = <>
∧-de-morgan {false} {false} = <>

-- Maybe next prove that a ∧ (b ∨ c) ≡ ((a ∧ b) ∨ (a ∧ c))
-- And the analogous for a ∨ (b ∧ c)

-- Prove also that a ∧ true ≡ a
--                        a ∧ false ≡ false
--                        a ∨ true ≡ true
--                        a ∨ false ≡ a

-- The most important of all a ∨ (¬ a) ≡ true
