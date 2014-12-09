----------------------------------------------------------------------
--                                                                  --
-- Author  : Jan Stolarek <jan.stolarek@p.lodz.pl>                  --
-- License : Public Domain                                          --
--                                                                  --
-- This module contains Agda implementation of code presented in    --
-- "Why Dependent Types Matter" by Thorsten Altenkirch, Conor       --
-- McBride and James McKinna. Original code in the paper was        --
-- written in Epigram but with its official web page offline        --
-- Epigram seems to be dead. Original paper elides details of some  --
-- proofs. I supplied the missing parts so that this module is      --
-- complete and self-contained. I avoided using the standard        --
-- library to show how the proofs are constructed from              --
-- scratch. This means I have to reinvent some of basic things like --
-- natural numbers, lists or vector. Some of the code below is not  --
-- mine, in which case I refer to the original source. If you're    --
-- reading "Why Dependent Types Matter" I encourage you to try and  --
-- implement all the code by yourself. I assure you that this will  --
-- be very rewarding.                                               --
--                                                                  --
-- This code was written and tested in Agda 2.3.2.1. YMMV           --
--                                                                  --
----------------------------------------------------------------------

module WhyDependentTypesMatter where

-- Reinventing the wheel: we will need a type of pairs to implement
-- deal function that splits list into a pair of lists. Sg is in fact
-- type of dependent pairs. This code is taken from Conor McBride:
-- https://github.com/pigworker/MetaprogAgda/blob/master/Basics.agda
record Sg (S : Set)(T : S → Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open Sg public
_×_ : Set → Set → Set
S × T = Sg S λ _ → T
infixr 4 _,_ _×_

-- Section 1 : Introduction
-- ~~~~~~~~~~~~~~~~~~~~~~~~
-- Standard implementation of merge sort with no dependent types. This
-- implements code shown in the paper in Figure 1.

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

data Order : Set where
  le ge : Order

data List (X : Set) : Set where
  nil  : List X
  _::_ : X → List X → List X

order : Nat → Nat → Order
order zero    y       = le
order (suc x) zero    = ge
order (suc x) (suc y) = order x y

-- deal splits a list into a pair of lists. If the input list has even length
-- then the output lists have the same length. If input has odd length then
-- first output list is longer by one.
deal : {X : Set} → List X → List X × List X
deal nil        = nil , nil
deal (x :: nil) = x :: nil , nil
deal (y :: (z :: xs)) with deal xs
deal (y :: (z :: xs)) | ys , zs = y :: ys , z :: zs

-- We have a small problem with merge and sort functions - Agda's termination
-- checker complains about merge and sort. The problem is that it doesn't see
-- that parameteres to merge are actually getting smaller in the recursive
-- calls. This results from the usage of "with" pattern, which is desugared to
-- an auxiliary function (say, "go"). Here's an explanation from Andreas Abel:
--
-- the termination checker refutes this call pattern.
--
--    merge (x :: xs) (y :: ys)
--       --> go x xs y ys ...
--       --> merge xs (y :: ys)
--
-- The termination checker sees that in merge-->go, the arguments all become
-- smaller, but in go--->merge, one argument becomes bigger. Since it has
-- simplistic, it cannot remember where y and ys came from and that taken
-- together, they are actually the same as we started out.
--
-- See Andreas' full explanation on Agda mailing list here:
-- https://lists.chalmers.se/pipermail/agda/2013/005948.html
--
-- I could rewrite the code to avoid this problem, but I'm leaving it as-is
-- because IMO it teaches something important about Agda's termination checker.
merge : List Nat → List Nat → List Nat
merge nil       ys             = ys
merge xs        nil            = xs
merge (x :: xs) (y :: ys) with order x y
merge (x :: xs) (y :: ys) | le = x :: merge xs (y :: ys)
merge (x :: xs) (y :: ys) | ge = y :: merge (x :: xs) ys

-- After I posted the original code I realized that it is not obvious that this
-- function is total. We know that (deal xs) is smaller than xs, but I think
-- that this isn't obvious.
sort : List Nat → List Nat
sort xs with deal xs
sort xs | ys , nil = ys
sort xs | ys , zs  = merge (sort ys) (sort zs)

-- Section 3.1 : Totality is Good for more than the Soul
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- Here we reinvent another wheel - refl

data _≡_ {S : Set} (s : S) : S → Set where
  refl : s ≡ s

infixl 1 _≡_

-- Section 3.2 : Defusing General Recursion
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- Merge sort with explicit structure of recursion.

data Parity : Set where
  p0 p1 : Parity

data DealT (X : Set) : Set where
  empT  : DealT X
  leafT : X → DealT X
  nodeT : Parity → DealT X → DealT X → DealT X

insertT : {X : Set} → X → DealT X → DealT X
insertT x empT = leafT x
insertT x (leafT y) = nodeT p0 (leafT y) (leafT x)
insertT x (nodeT p0 l r) = nodeT p1 (insertT x l) r
insertT x (nodeT p1 l r) = nodeT p0 l (insertT x r)

dealT : {X : Set} → List X → DealT X
dealT nil = empT
dealT (x :: xs) = insertT x (dealT xs)

mergeT : DealT Nat → List Nat
mergeT empT = nil
mergeT (leafT x) = x :: nil
mergeT (nodeT p l r) = merge (mergeT l) (mergeT r)

-- In the paper this function is called sort. Here and in other places I rename
-- functions to avoid name clashes.
sortT : List Nat → List Nat
sortT xs = mergeT (dealT xs)

-- Section 4 : Maintaining Invariants by Static Indexing
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

-- Note that I'm using (suc n) instead of (1 + n). Why?
-- becuase I'm not using Agda's BUILTIN pragmas, so I'd
-- have to write (suc zero) instead of 1. This doesn't
-- change much in the proofs we'll be doing.
data Vec (X : Set) : Nat → Set where
  vnil  : Vec X zero
  vcons : {n : Nat} → X → Vec X n → Vec X (suc n)

vtail : {X : Set} {n : Nat} → Vec X (suc n) → Vec X n
vtail (vcons x xs) = xs

-- @ is a reserved sign in Agda, so I'm using vapp to denote
-- vectorized application.
vapp : {A B : Set} {n : Nat} → Vec (A → B) n → Vec A n → Vec B n
vapp vnil         vnil         = vnil
vapp (vcons f fs) (vcons s ss) = vcons (f s) (vapp fs ss)

_+_ : Nat → Nat → Nat
zero  + n = n
suc m + n = suc (m + n)

infixl 4 _+_

_++_ : {X : Set} {n m : Nat} → Vec X n → Vec X m → Vec X (n + m)
vnil       ++ ys = ys
vcons x xs ++ ys = vcons x (xs ++ ys)

vec : {X : Set} {n : Nat} → X → Vec X n
vec {X} {zero}  x = vnil
vec {X} {suc n} x = vcons x (vec x)

xpose : {X : Set} {n m : Nat} → Vec (Vec X n) m → Vec (Vec X m) n
xpose vnil            = vec vnil
xpose (vcons xj xi'j) = vapp (vapp (vec vcons) xj) (xpose xi'j)

-- Section 4.1 : Static Indexing and Proofs
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- This section is the one that is missing some of the proofs.

vrevacc : {X : Set} {n m : Nat} → Vec X n → Vec X m → Vec X (n + m)
vrevacc vnil         ys = ys
vrevacc (vcons x xs) ys = {!!} -- vrevacc xs (vcons x ys)
-- We can't fill in the correct code, because Agda doesn't know that m + (1 + n)
-- eqauls 1 + (m + n). We will have to prove it.

-- To conduct a proof we will need three properties:
-- a) symmetry: if a equals b then b equals a
sym : {A : Set} → {a b : A} → a ≡ b → b ≡ a
sym refl = refl

-- b) congruence: if a equals b, then (f a) equals (f b)
cong : {A B : Set} (f : A → B) → ∀ {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

-- c) substitution: if we have a proposition that is true for a
-- and a equals b, then proposition is also true for b
subst : {A : Set}(P : A → Set) → {a b : A} → a ≡ b → P a → P b
subst prp refl p = p

-- These three properties were taken from Thorsten Altenkirch's course
-- on Computer Aided Formal Reasoning: http://www.cs.nott.ac.uk/~txa/g53cfr/
-- If you don't know how they work and why do we need them now is a good moment
-- to stop reading "Why Dependent Types Matter" and go through lectures 1-9
-- of Thorsten's course.

plusSuc : (m n : Nat) → suc (m + n) ≡ m + (suc n)
plusSuc zero n = refl
plusSuc (suc m) n = cong suc (plusSuc m n)

vrevacc2 : {X : Set} {n m : Nat} → Vec X n → Vec X m → Vec X (n + m)
vrevacc2                 vnil         ys = ys
vrevacc2 {X} {suc n} {m} (vcons x xs) ys =
  subst (Vec X) (sym (plusSuc n m)) (vrevacc2 xs (vcons x ys))

-- Last line corresponds to
--
--    {[plusSuc m' n⟩} vrevacc2 xs (vcons x ys)
--
-- in the paper. Call to vrevacc2 produces Vec with index n + (suc m). The
-- problem is we need index suc (n + m). We need to prove their equality.  we
-- already proved with plusSuc that suc (n + m) equals n + (suc m). Since now
-- we're proving something opposite we make use of symmetry: we apply sym to
-- plusSuc. Having a proof is not enough - we must apply it to convert from the
-- result produced by vrevacc2 to the result expected by the typechecker. To do
-- this we use subst function. Our proposition is (Vec X). Look at the type
-- signature of subst - the proposition is something that will take an element
-- of Set (in this case Nat) and produce an element of Set. Vec X will return an
-- element of Set (ie a type) when we pass it an index of type Nat. subst
-- replaces (substitutes) index n + (suc m) produced by vrevacc2 with
-- suc (n + m).

plusZero : (n : Nat) → n + zero ≡ n
plusZero zero    = refl
plusZero (suc n) = cong suc (plusZero n)

vrev : {X : Set} {n : Nat} → Vec X n → Vec X n
vrev {X} {n} xs = subst (Vec X) (plusZero n) (vrevacc2 xs vnil)

-- Section 4.2 : Sized Merge-Sort
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

-- note that mergeS is a renamed merge from the paper
mergeS : {n m : Nat} → Vec Nat n → Vec Nat m → Vec Nat (n + m)
mergeS {zero } {_    } vnil         ys   = ys
mergeS {suc n} {zero } (vcons x xs) vnil =
  subst (Vec Nat) (sym (plusZero (suc n))) (vcons x xs)
mergeS {suc n} {suc m} (vcons x xs) (vcons y ys) with order x y
mergeS {suc n} {suc m} (vcons x xs) (vcons y ys) | le =
  vcons x (mergeS xs (vcons y ys))
mergeS {suc n} {suc m} (vcons x xs) (vcons y ys) | ge =
  subst (Vec Nat) (plusSuc (suc n) m) (vcons y (mergeS (vcons x xs) ys))

p2n : Parity → Nat
p2n p0 = zero
p2n p1 = suc zero

-- Data types and functions below have S (mnemonic for Sized) appended to their
-- name to avoid name clash.
data DealTS (X : Set) : Nat → Set where
  empT  : DealTS X zero
  leafT : X → DealTS X (suc zero)
  nodeT : {n : Nat} → (p : Parity) → DealTS X (p2n p + n) → DealTS X n
        → DealTS X ((p2n p + n) + n)

mergeTS : {n : Nat} → DealTS Nat n → Vec Nat n
mergeTS empT          = vnil
mergeTS (leafT x)     = vcons x vnil
mergeTS (nodeT p l r) = mergeS (mergeTS l) (mergeTS r)

insertTS : {n : Nat} {X : Set} → X → DealTS X n → DealTS X (suc n)
insertTS x empT               = leafT x
insertTS x (leafT y         ) = nodeT p0 (leafT y) (leafT x)
insertTS x (nodeT     p0 l r) = nodeT p1 (insertTS x l) r
insertTS {.(p2n p1 + n + n)} {X} x (nodeT {n} p1 l r) =
  subst (DealTS X) (sym (cong suc (plusSuc n n))) (nodeT p0 l (insertTS x r))
--                  |    |         |
--                  |    |         +---- suc (n + n) ≡ n + suc n
--                  |    +-------------- suc (suc (n + n)) ≡ suc (n + suc n))
--                  +------------------- suc (n + suc n))  ≡ suc (suc (n + n))
--
-- It took me a while to figure out this proof (though in retrospect it is
-- simple). The expected size of the resulting vector is:
--
--   suc (suc (n + n))
--
-- First suc comes from the type signature of insertTS, second suc comes from
-- p2n p1 (which is suc zero), and n + n comes from nodeT definition. The actual
-- size produced by recursive call to nodeT is:
--
--   suc (n + suc n))
--
-- Outer suc comes from type signature, n is size of l, suc n is size of new r
-- (ie. r with x inserted into it).

dealTS : {X : Set} {n : Nat} → Vec X n → DealTS X n
dealTS vnil = empT
dealTS (vcons x xs) = insertTS x (dealTS xs)

sortTS : {n : Nat} → Vec Nat n → Vec Nat n
sortTS xs = mergeTS (dealTS xs)

-- Section 5.1 : Evidence of Ordering
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

data _≤_ : Nat → Nat → Set where
  le0 : {y : Nat} → zero ≤ y
  leS : {x : Nat} {y : Nat} → x ≤ y → suc x ≤ suc y

data OrderD : Nat → Nat → Set where
  le : {x : Nat} {y : Nat} → x ≤ y → OrderD x y
  ge : {x : Nat} {y : Nat} → y ≤ x → OrderD x y

orderD : (x : Nat) → (y : Nat) → OrderD x y
orderD zero    y       = le le0
orderD (suc x) zero    = ge le0
orderD (suc x) (suc y) with orderD x y
orderD (suc x) (suc y) | le xley = le (leS xley)
orderD (suc x) (suc y) | ge ylex = ge (leS ylex)

leRefl : {x : Nat} → x ≤ x
leRefl {zero}  = le0
leRefl {suc x} = leS leRefl

leTrans : {x y z : Nat} → x ≤ y → y ≤ z → x ≤ z
leTrans le0      yz       = le0
leTrans (leS xy) (leS yz) = leS (leTrans xy yz)

leASym : {x y : Nat} → x ≤ y → y ≤ x → x ≡ x
leASym le0      le0      = refl
leASym (leS xy) (leS yx) = refl

-- Second equation for leASym is surprisingly simple. I admit I don't fully
-- understand why I could simply use refl here, without doing inductive proof.

-- Section 5.2 : Locally Sorted Lists
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

-- LNat = Nat lifted with infinity
data LNat : Set where
  zero : LNat
  suc  : LNat → LNat
  inf  : LNat

lift : Nat → LNat
lift zero    = zero
lift (suc x) = suc (lift x)

-- In the paper ≤ is used for comparisons on lifted Nats. I'm using ≤' to avoid
-- name clash.
data _≤'_ : LNat → LNat → Set where
  le0 : {y : LNat} → zero ≤' y
  leS : {x : LNat} {y : LNat} → x ≤' y → suc x ≤' suc y
  leI : {x : LNat} → x ≤' inf

data CList : LNat → Set where
  cnil  : CList inf
  ccons : {y : LNat} → (x : Nat) → (lift x) ≤' y → CList y → CList (lift x)
--                                          |
--              +---------------------------+
--              +--> Paper compares lifted and unlifted Nat using ≤.
--                   This seems incorrect or at least unprecise.

-- The problem with CList is that we can't create it if we don't know the least
-- element. That's why the paper says sort is bound by min.
clist : CList zero
clist = ccons zero le0 (
        ccons (suc (suc zero)) (leS (leS le0)) (
        ccons (suc (suc zero))  leI cnil))

data OList : Nat → Set where
  onil  : {b : Nat} → OList b
  ocons : {b : Nat} → (x : Nat) → b ≤ x → OList x → OList b

-- With OList we can just create the list by saying it is bound by zero.
olist : OList zero
olist = ocons (suc zero) le0 onil

olist2 : OList zero
olist2 = ocons (suc zero) le0 (ocons (suc (suc zero)) (leS le0) onil)

-- mergeO (ie. merge for open-bounds lists) has the same problem that we've seen
-- earlier with merge and sort - termination checker complains because we use
-- "with" pattern.
mergeO : {b : Nat} → OList b → OList b → OList b
mergeO onil ys = ys
mergeO (ocons x blex xs) onil = ocons x blex xs
mergeO (ocons x blex xs) (ocons y bley ys) with orderD x y
mergeO (ocons x blex xs) (ocons y bley ys) | le xley =
  ocons x blex (mergeO xs (ocons y xley ys))
mergeO (ocons x blex xs) (ocons y bley ys) | ge ylex =
  ocons y bley (mergeO (ocons x ylex xs) ys)

-- The important thing here is that both lists passed to mergeO must share their
-- lower bound. That's why we have to replace old evidence of ordering (bley in
-- the first case) with the new one (xley).

mergeTO : DealT Nat → OList zero
mergeTO empT          = onil
mergeTO (leafT x)     = ocons x le0 onil
mergeTO (nodeT p l r) = mergeO (mergeTO l) (mergeTO r)

sortO : List Nat → OList zero
sortO xs = mergeTO (dealT xs)
