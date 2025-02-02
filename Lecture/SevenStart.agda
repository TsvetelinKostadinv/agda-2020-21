-- TODO discuss
{-# OPTIONS --type-in-type #-}
{-# OPTIONS --no-unicode #-}

module Lecture.SevenStart where

open import Lib.Eq
open import Lib.List
open import Lib.Vec
open import Lib.Nat
open import Lib.One
open import Lib.Two
open import Lib.Zero
open import Lib.Sigma

{-
-- Type : Type
-- Set 0 : Set 1
-- Set 1 : Set 2
-- Set 2 : Set 3
-- Set 0 : Set 0
record A : Set where
  field
   B : Set

x : Zero
x = neshtosi

zero-elim : {A : Set} -> Zero -> A
-}

{-
-- TODO: ext

-- ∀f. ∀g. ∀x. f(x) == g(x) => f == g
-- f = linear search
-- g = binary search
-- are they the same?

postulate
  extensionality :
    {A B : Set} {f g : A -> B} ->
    ((x : A) -> f x == g x) ->
    f == g
-}


record Category : Set where
  field
    -- data
    Obj : Set
    _~>_ : (S : Obj) -> (T : Obj) -> Set

    -- operations
    id~> : (x : Obj) -> x ~> x
    -- (f ∘ g  ∘ h) x == f(g(h(x)))
    -- (h >~> g >~> f) x == f(g(h(x)))
    _>~>_ : {S T R : Obj} -> S ~> T -> T ~> R -> S ~> R

    -- laws
    left-id :
      {S T : Obj} (f : S ~> T) ->
      id~> S >~> f == f
    right-id :
      {S T : Obj} (f : S ~> T) ->
      f >~> id~> T == f
    assoc :
      {S T R Q : Obj}
      (f : S ~> T) (g : T ~> R) (h : R ~> Q) ->
      (f >~> g) >~> h == f >~> (g >~> h)

open Category public

-- TODO: use a record here!
-- <SPC> m r
-- C-c C-r
AGDA : Category
AGDA =
  record
    { Obj = Set
    ; _~>_ = \ S T -> S -> T
    ; id~> = \ S x -> x
    ; _>~>_ = \ f g x -> g (f x)
    ; left-id = \ f -> refl
    ; right-id = \ f -> refl
    ; assoc = \ f g h -> refl
    }

-- * --> *
--  \    |
--   \   |
--    \  |
--     \ |
--      \|
--       v
--       *
module Three where
  -- One + One + One
  data Three : Set where
    -- zero : Three
    -- one : Three
    -- two : Three
    zero one two : Three

  data Arrow : Three -> Three -> Set where
    idArr : (x : Three) -> Arrow x x
    zero-one : Arrow zero one
    one-two : Arrow one two
    zero-two : Arrow zero two


  -- _+N_
  -- zero +N m = m
  -- (suc n) +N m = suc (n +N m)

  -- <SPC> m c
  -- THREE' : Category
  -- THREE' = record
  --            { Obj = Three
  --            ; _~>_ = Arrow
  --            ; id~> = \ x -> idArr x
  --            ; _>~>_ = {!!}
  --            ; left-id = {!!}
  --            ; right-id = {!!}
  --            ; assoc = {!!}
  --            }
  THREE : Category
  Obj THREE = Three
  _~>_ THREE = Arrow
  id~> THREE = idArr
  _>~>_ THREE (idArr _) (idArr x) = idArr x
  _>~>_ THREE (idArr .zero) zero-one = zero-one
  _>~>_ THREE (idArr .one) one-two = one-two
  _>~>_ THREE (idArr .zero) zero-two = zero-two
  _>~>_ THREE (zero-one) (idArr .one) = zero-one
  _>~>_ THREE (zero-one) one-two = zero-two
  _>~>_ THREE (one-two) (idArr .two) = one-two
  _>~>_ THREE (zero-two) (idArr .two) = zero-two
  left-id THREE (idArr _) = refl
  left-id THREE zero-one = refl
  left-id THREE one-two = refl
  left-id THREE zero-two = refl
  right-id THREE (idArr _) = refl
  right-id THREE zero-one = refl
  right-id THREE one-two = refl
  right-id THREE zero-two = refl
  assoc THREE (idArr _) (idArr _) (idArr _) = refl
  assoc THREE (idArr .zero) (idArr .zero) zero-one = refl
  assoc THREE (idArr .one) (idArr .one) one-two = refl
  assoc THREE (idArr .zero) (idArr .zero) zero-two = refl
  assoc THREE (idArr .zero) zero-one (idArr .one) = refl
  assoc THREE (idArr .zero) zero-one one-two = refl
  assoc THREE (idArr .one) one-two (idArr .two) = refl
  assoc THREE (idArr .zero) zero-two (idArr .two) = refl
  assoc THREE zero-one (idArr .one) (idArr .one) = refl
  assoc THREE zero-one (idArr .one) one-two = refl
  assoc THREE zero-one one-two (idArr .two) = refl
  assoc THREE one-two (idArr .two) (idArr .two) = refl
  assoc THREE zero-two (idArr .two) (idArr .two) = refl

-- all of the info is in the objects
record Preorder : Set where
  field
    cat : Category
    one-arrow : {S T : Obj cat} (f g : _~>_ cat S T) -> f == g

<=-unique : {n m : Nat} (p q : n <= m) -> p == q
<=-unique ozero ozero = refl
<=-unique (osuc p) (osuc q) = ap osuc (<=-unique p q)

-- TODO: show copatterns here
-- https://agda.readthedocs.io/en/v2.6.1.3/language/copatterns.html
-- n <= m
-- m <= k
-- n <= k
<=-Cat : Category
Obj <=-Cat = Nat
_~>_ <=-Cat = _<=_
id~> <=-Cat = <=-refl
_>~>_ <=-Cat = <=-trans
left-id <=-Cat {n} {m} p = <=-unique (<=-trans (<=-refl n) p) p
right-id <=-Cat {S} {T} f = <=-unique (<=-trans f (<=-refl T)) f
assoc <=-Cat f g h =
  <=-unique
    (<=-trans (<=-trans f g) h)
    (<=-trans f (<=-trans g h))

<=-Preorder : Preorder
Preorder.cat <=-Preorder = <=-Cat
Preorder.one-arrow <=-Preorder = <=-unique

-- all of the info is in the arrows
record Monoid : Set where
  field
    cat : Category
    Obj-is-One : Obj cat == One

-- *
Nat+N-Cat : Category
Obj Nat+N-Cat = One
_~>_ Nat+N-Cat _ _ = Nat
id~> Nat+N-Cat _ = zero
_>~>_ Nat+N-Cat = _+N_
left-id Nat+N-Cat n = refl -- zero +N n == n
right-id Nat+N-Cat = +N-right-zero  -- n +N zero == n
assoc Nat+N-Cat = +N-assoc

Nat+N-Monoid : Monoid
Monoid.cat Nat+N-Monoid = Nat+N-Cat
Monoid.Obj-is-One Nat+N-Monoid = refl

-- a category with one object
-- *
ONE : Category
Obj ONE = One
_~>_ ONE _ _ = One
id~> ONE <> = <>
_>~>_ ONE <> <> = <>
left-id ONE <> = refl
right-id ONE <> = refl
assoc ONE <> <> <> = refl

-- a category with two objects
-- * --> *
module TwoCat where
  data ArrTwo : Two -> Two -> Set where
    idArr : { x : Two} -> ArrTwo x x
    tt-ff : ArrTwo tt ff

  TWO : Category
  Obj TWO = Two
  _~>_ TWO = ArrTwo
  id~> TWO x = idArr
  _>~>_ TWO (idArr) idArr = idArr
  _>~>_ TWO (idArr) tt-ff = tt-ff
  _>~>_ TWO (tt-ff) idArr = tt-ff
  left-id TWO idArr = refl
  left-id TWO tt-ff = refl
  right-id TWO idArr = refl
  right-id TWO tt-ff = refl
  assoc TWO idArr idArr idArr = refl
  assoc TWO idArr idArr tt-ff = refl
  assoc TWO idArr tt-ff idArr = refl
  assoc TWO tt-ff idArr idArr = refl

-- we'll be making this a monoid, so the objects will be One for sure
-- with our arrows being List A s
List-+L-Cat : Set -> Category
List-+L-Cat A = ListACat where
  ListACat : Category
  Obj ListACat = One
  _~>_ ListACat <> <> = List A
  id~> ListACat <> = []
  _>~>_ ListACat = Lib.List._+L_
  left-id ListACat list = refl
  right-id ListACat list = +L-right-id list
  assoc ListACat = +L-assoc

List-+L-Monoid : Set -> Monoid
List-+L-Monoid A = listAMonoid where
  listAMonoid : Monoid
  Monoid.cat listAMonoid = List-+L-Cat A
  Monoid.Obj-is-One listAMonoid = refl

-- a Discrete category is one in which the only arrows are the identity arrows
-- an example of such a category is the one formed with an arbitrary type, and _==_ as arrows
Discrete== : Set -> Category
Obj (Discrete== X) = X
_~>_ (Discrete== X) = _==_
id~> (Discrete== X) x = refl
_>~>_ (Discrete== X) = ==-trans
left-id (Discrete== X) refl = refl
right-id (Discrete== X) refl = refl
assoc (Discrete== X) refl refl refl = refl

-- we can make a category with whatever arrows we like
-- if we have no objects
EMPTY : Set -> Category
Obj (EMPTY X) = Zero
_~>_ (EMPTY X) _ _ = X
id~> (EMPTY X) ()
_>~>_ (EMPTY X) {()}
left-id (EMPTY X) {()}
right-id (EMPTY X) {()}
assoc (EMPTY X) {()}

-- we can always "flip" the arrows in a category, to get a "dual" notion of something
-- very powerful concept
Op : Category -> Category
Op catA = opCatA where 
  opCatA : Category
  Obj opCatA = Obj catA
  _~>_ opCatA x y = _~>_ catA y x
  id~> opCatA x = id~> catA x
  _>~>_ opCatA f g = _>~>_ catA g f
  left-id opCatA f = right-id catA f
  right-id opCatA = left-id catA 
  assoc opCatA {S} {T} {R} {Q} f g h = ==-symm (assoc catA h g f) -- there were tears and blood

-- a product of two other categories - we want to "carry" our operations pointwise
Product : Category -> Category -> Category
Obj (Product X Y) = Obj X * Obj Y
_~>_ (Product X Y) x y = _~>_ X (fst x) (fst y) * _~>_ Y (snd x) (snd y) -- afk
id~> (Product X Y) x = idArr where
  idArr : (X ~> fst x) (fst x) * (Y ~> snd x) (snd x)
  fst idArr = id~> X (fst x) 
  snd idArr = id~> Y (snd x)
_>~>_ (Product X Y) {S}{T}{R} x y = comArr where
  comArr : (X ~> fst .S) (fst .R) * (Y ~> snd .S) (snd .R)
  fst comArr = {!  !}
  snd comArr = ?{!   !}
left-id (Product X Y) = {!!}
right-id (Product X Y) = {!!}
assoc (Product X Y) = {!!}

-- like homomorphisms
record _=>_ (C D : Category) : Set where
  field
    F-Obj : Obj C -> Obj D
    F-map : {S T : Obj C} -> (_~>_ C S T) -> _~>_ D (F-Obj S) (F-Obj T)

    F-map-id : {S : Obj C} -> F-map (id~> C S) == id~> D (F-Obj S)
    F-map->~> :
      {S T R : Obj C}
      (f : _~>_ C S T) (g : _~>_ C T R) ->
      F-map (_>~>_ C f g) == _>~>_ D (F-map f) (F-map g)

open _=>_ public

data Maybe (A : Set) : Set where
  just : A -> Maybe A
  nothing : Maybe A

postulate
  ext :
    {A B : Set} {f g : A -> B} ->
    ((x : A) -> f x == g x) ->
    f == g

-- parseInt :: String -> Maybe Int

-- F-Obj Maybe : Set -> Set
-- * == Set
-- id~> == id
-- (F-map MAYBE F \x -> x) == (\ x -> x)
-- Homotopy type theory
MAYBE : AGDA => AGDA
F-Obj MAYBE = Maybe
F-map MAYBE f (just x) = just (f x)
F-map MAYBE f nothing = nothing
F-map-id MAYBE =
  ext
    \{ (just x) -> refl ;
       nothing -> refl -- nothing == nothing
     }
F-map->~> MAYBE f g =
  ext
    \{ (just x) -> refl ;
         -- F-map MAYBE (f >> g) (just x) == (F-map MAYBE f >> F-map MAYBE g) (just x)
         -- F-map MAYBE (f >> g) (just x) == (\x1 -> F-map MAYBE g (F-map MAYBE f x1)) (just x)
         -- F-map MAYBE (f >> g) (just x) == F-map MAYBE g (F-map MAYBE f (just x))
         -- F-map MAYBE (f >> g) (just x) == F-map MAYBE g (just (f x))
         -- F-map MAYBE (f >> g) (just x) == just (g (f x))
         -- F-map MAYBE (\x1 -> g (f x1)) (just x) == just (g (f x))
         -- just ((\x1 -> g (f x1)) x) == just (g (f x))
         -- just (g (f x)) == just (g (f x))
       nothing -> refl
     }

id : {A : Set} -> A -> A
id x = x

-- the identity functor
-- does nothing
ID : (C : Category) -> C => C
ID categ = idFunct where
  idFunct : categ => categ
  F-Obj idFunct x = x
  F-map idFunct = {!   !}
  F-map-id idFunct = {!   !}
  F-map->~> idFunct  = {!   !}

{-
map : {A B : Set} -> (A -> B) -> List A -> List B
map = {!!}

map-id : {A : Set} (xs : List A) -> map id xs == xs
map-id = {!!}

_>>_ : {S R T : Set} -> (S -> R) -> (R -> T) -> S -> T
_>>_ f g x = g (f x)

map-compose :
  {A B C : Set} (f : A -> B) (g : B -> C) (xs : List A) ->
  map (f >> g) xs == map g (map f xs)
map-compose = {!!}

-- lists are a functor
LIST : SET => SET
F-Obj LIST = List
F-map LIST = map
F-map-id LIST = ext {!!}
F-map->~> LIST f g = ext {!!}

-- addition with some constant is a functor over our previous Nat preorder category
ADD : Nat -> <=-Cat => <=-Cat
ADD k = {!!}

-- every function generates a functor over the list monoid,
-- showing that applying it for each element respects the list structure
LIST+L : {X Y : Set} (f : X -> Y) -> List-+L-Cat X => List-+L-Cat Y
LIST+L = {!!}

vTake : {A : Set} {n m : Nat} -> n <= m -> Vec A m -> Vec A n
vTake = {!!}

-- vTake forms a functor, sending a perorder into a type (Vec X n)
-- we need to use the opposite category of <=-Cat here, to make the "directions" match up
VTAKE : Set -> Op <=-Cat => SET
VTAKE = {!!}

-- form a set of "free arrows" based on a relation
-- this is exactly the same as a reflexive and transitive closure of a relation
data Free {X : Set}(R : X -> X -> Set) (x : X) : X -> Set where
  idArr : Free R x x
  trans : {y z : X} -> R x y -> Free R y z -> Free R x z

composeFree : {X : Set} {R : X -> X -> Set} {x y z : X} -> Free R x y -> Free R y z -> Free R x z
composeFree = {!!}

FREE : (X : Set) -> (X -> X -> Set) -> Category
FREE = {!!}

data Fin : Nat -> Set where
  zero : {n : Nat} -> Fin (suc n)
  suc : {n : Nat} -> Fin n -> Fin (suc n)

-- we want there to be an arrow from (x : Fin n) to suc x, except for the "last number" in Fin n
Next : {n : Nat} -> Fin n -> Fin n -> Set
Next = {!!}

-- now we can form all the finite categories by choosing how many objects we want via n
Finite : Nat -> Category
Finite = ?
-}
