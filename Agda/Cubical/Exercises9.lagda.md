# Week 9 - Cubical Agda Exercises

## Standard disclaimer:

**The exercises are designed to increase in difficulty so that we can cater to
our large and diverse audience. This also means that it is *perfectly fine* if
you don't manage to do all exercises: some of them are definitely a bit hard for
beginners and there are likely too many exercises! You *may* wish to come back
to them later when you have learned more.**

Having said that, here we go!

In case you haven't done the other Agda exercises:
This is a markdown file with Agda code, which means that it displays nicely on
GitHub, but at the same time you can load this file in Agda and fill the holes
to solve exercises.

**When solving the problems,
please make a copy of this file to work in, so that it doesn't get overwritten
(in case we update the exercises through `git`)!**


```agda
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Exercises9 where

open import cubical-prelude
open import Lecture7-notes
-- open import Lecture8-notes
open import Lecture9-notes
open import Solutions7 hiding (rUnit)
open import Solutions8
open import Lecture9-live using (SemiGroupℕ)
```

## Part I: More hcomps

### Exercise 1 (★★)
### (a)
Show the left cancellation law for path composition using an hcomp.
Hint: one hcomp should suffice. Use `comp-filler` and connections

```agda
lUnit : {A : Type ℓ} {x y : A} (p : x ≡ y) → refl ∙ p ≡ p
lUnit {x = x} p i j =
  hcomp (λ where k (i = i1) → p (j ∧ k)
                 k (j = i0) → x
                 k (j = i1) → p k)
        x

```
### (b)
Try to mimic the construction of lUnit for rUnit (i.e. redefine it)
in such a way that `rUnit refl ≡ lUnit refl` holds by `refl`.
Hint: use (almost) the exact same hcomp.

```agda
rUnit : {A : Type ℓ} {x y : A} (p : x ≡ y) → p ∙ refl ≡ p
rUnit {x = x} {y = y} p i j =
  hcomp (λ where k (i = i1) → p j
                 k (j = i0) → x
                 k (j = i1) → y)
        (p j)

-- uncomment to see if it type-checks

rUnit≡lUnit : ∀ {ℓ} {A : Type ℓ} {x : A} → rUnit (refl {x = x}) ≡ lUnit refl
rUnit≡lUnit = refl

```


### Exercise 2 (★★)
Show the associativity law for path composition
Hint: one hcomp should suffice. This one can be done without connections
  (but you might need comp-filler in more than one place)

```agda
comp-filler' : {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z)
             → PathP (λ j → p (~ j) ≡ z) q (p ∙ q)
comp-filler' {x = x} p q i j = 
  hcomp (λ where k (i = i0) → q (j ∧ k)
                 k (j = i0) → p (~ i)
                 k (j = i1) → q k)
        (p (~ i ∨ j))

assoc : {A : Type ℓ} {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
  → p ∙ (q ∙ r) ≡ (p ∙ q) ∙ r
assoc {x = x} p q r i j =
  hcomp (λ where k (j = i0) → x
                 k (j = i1) → comp-filler' q r (~ i) k)
        (comp-filler p q i j)

```

### Exercise 3 (Master class in connections) (🌶)
The goal of this exercise is to give a cubical proof of the Eckmann-Hilton argument,
which says that path composition for higher loops is commutative

(a) While we cannot get `p ∙ q ≡ q ∙ p` as a one-liner, we can get a
one-liner showing that the identiy holds up to some annoying
coherences.  Try to understand the following statement (and why it's
well-typed). After that, fill the holes

Hint: each hole will need a `∨` or a `∧`

```agda
pre-EH : {A : Type ℓ} {x : A} (p q : refl {x = x} ≡ refl)
  → ap (λ x → x ∙ refl) p ∙ ap (λ x → refl ∙ x) q
   ≡ ap (λ x → refl ∙ x) q ∙ ap (λ x → x ∙ refl) p
pre-EH {x = x} p q i = (λ j → p (j ∧ ~ i) ∙ q (j ∧ i))
                     ∙ (λ j → p (~ i ∨ j) ∙ q (i ∨ j))

```
(b) If we manage to cancel out all of the annoying aps, we get Eckmann-Hilton:
For paths (p q : refl ≡ refl), we have p ∙ q ≡ q ∙ p. Try to prove this, using the above lemma.

Hint: Use the pre-EH as the bottom of an hcomp (one should be enough).
For the sides, use lUnit and rUnit wherever they're needed. Note that this will only work out smoothly if
you've solved Exercise 1 (b).

```agda
Eckmann-Hilton : {A : Type ℓ} {x : A} (p q : refl {x = x} ≡ refl) → p ∙ q ≡ q ∙ p
Eckmann-Hilton {x = x} p q i j =
  hcomp (λ where k (i = i0) → ((λ j → rUnit (p j) k) ∙ (λ j → lUnit (q j) k)) j
                 k (i = i1) → ((λ j → lUnit (q j) k) ∙ (λ j → rUnit (p j) k)) j
                 k (j = i0) → lUnit (λ _ → x) k
                 k (j = i1) → lUnit (λ _ → x) k)
        (pre-EH p q i j)

```
# Part 2: Binary numbers as a HIT
Here is another HIT describing binary numbers. The idea is that a binary number is a list of booleans, modulo trailing zeros.

For instance, `true ∷ true ∷ true ∷ []` is the binary number 110 ...
... and so is `true ∷ true ∷ false ∷ false ∷ false ∷ []`

(!) Note that we're interpreting 110 as 1·2⁰ + 1·2¹ + 0·2² here.

```agda
0B = false
1B = true

data ListBin : Type where
  []    : ListBin
  _∷_   : (x : Bool) (xs : ListBin) → ListBin
  drop0 : 0B ∷ [] ≡ []

-- 1 as a binary number
1LB : ListBin
1LB = 1B ∷ []
```
### Exercise 4 (★)
Define the successor function on ListBin
```agda

sucListBin : ListBin → ListBin
sucListBin [] = 1LB
sucListBin (true ∷ l) = false ∷ sucListBin l
sucListBin (false ∷ l) = true ∷ l
sucListBin (drop0 i) = 1LB

```
### Exercise 5 (★★)
Define an addition `+LB` on ListBin and prove that `x +LB [] ≡ x`
Do this by mutual induction! Make sure the three cases for the right unit law hold by refl.
```agda

_+LB_ : ListBin → ListBin → ListBin
rUnit+LB : (x : ListBin) → x +LB [] ≡ x
[] +LB x = x
(a ∷ x) +LB [] = a ∷ x
(true ∷ x) +LB (true ∷ y) = false ∷ sucListBin (x +LB y)
(true ∷ x) +LB (false ∷ y) = true ∷ (x +LB y)
(false ∷ x) +LB (b ∷ y) = b ∷ (x +LB y)
(true ∷ y) +LB drop0 i = true ∷ rUnit+LB y i
(false ∷ y) +LB drop0 i = false ∷ rUnit+LB y i
drop0 i +LB [] = drop0 i
drop0 i +LB (x ∷ y) = x ∷ y
drop0 i +LB drop0 j = drop0 (i ∧ j)
rUnit+LB [] = refl
rUnit+LB (x ∷ x₁) = refl
rUnit+LB (drop0 i) = refl

```
(c) Prove that sucListBin is left distributive over `+LB`
Hint: If you pattern match deep enough, there should be a lot of refls...
```agda

sucListBinDistrL : (x y : ListBin) → sucListBin (x +LB y) ≡ (sucListBin x +LB y)
sucListBinDistrL [] [] = refl
sucListBinDistrL [] (true ∷ y) = refl
sucListBinDistrL [] (false ∷ y) = refl
sucListBinDistrL [] (drop0 i) = refl
sucListBinDistrL (x ∷ x₁) [] = sym (rUnit+LB _)
sucListBinDistrL (true ∷ x₁) (true ∷ y) = ap (true ∷_) (sucListBinDistrL x₁ y)
sucListBinDistrL (true ∷ x₁) (false ∷ y) = ap (false ∷_) (sucListBinDistrL x₁ y)
sucListBinDistrL (false ∷ x₁) (true ∷ y) = refl
sucListBinDistrL (false ∷ x₁) (false ∷ y) = refl
sucListBinDistrL (true ∷ x₁) (drop0 i) j = false ∷ {!   !}
sucListBinDistrL (false ∷ x₁) (drop0 i) = {!   !}
sucListBinDistrL (drop0 i) y = {!   !}
```

### Exercise 6 (★)
Define a map `LB→ℕ : ListBin → ℕ` and show that it preserves addition

```agda
ℕ→ListBin : ℕ → ListBin
ℕ→ListBin zero = []
ℕ→ListBin (suc n) = sucListBin (ℕ→ListBin n)

ℕ→ListBin-pres+ : (x y : ℕ) → ℕ→ListBin (x + y) ≡ (ℕ→ListBin x +LB ℕ→ListBin y)
ℕ→ListBin-pres+ zero y = refl
ℕ→ListBin-pres+ (suc x) y = ap sucListBin (ℕ→ListBin-pres+ x y) ∙ sucListBinDistrL (ℕ→ListBin x) _

```

### Exercise 7 (★★★)
Show that `ℕ ≃ ListBin`.

```agda

ListBin→ℕ : ListBin → ℕ
ListBin→ℕ [] = zero
ListBin→ℕ (true ∷ y) = suc (doubleℕ (ListBin→ℕ y))
ListBin→ℕ (false ∷ y) = doubleℕ (ListBin→ℕ y)
ListBin→ℕ (drop0 i) = zero

ℕ→ListBin-doubleℕ : (n : ℕ) → ℕ→ListBin (doubleℕ n) ≡ 0B ∷ ℕ→ListBin n
ℕ→ListBin-doubleℕ zero = sym drop0
ℕ→ListBin-doubleℕ (suc n) = ap (λ x → sucListBin (sucListBin x)) (ℕ→ListBin-doubleℕ n)

ListBin→ℕ→ListBin : (x : ListBin) → ℕ→ListBin (ListBin→ℕ x) ≡ x
ListBin→ℕ→ListBin [] = refl
ListBin→ℕ→ListBin (true ∷ y) = ap sucListBin (ℕ→ListBin-doubleℕ (ListBin→ℕ y)) ∙ ap (1B ∷_) (ListBin→ℕ→ListBin y)
ListBin→ℕ→ListBin (false ∷ y) = ℕ→ListBin-doubleℕ (ListBin→ℕ y) ∙ ap (0B ∷_) (ListBin→ℕ→ListBin y)
ListBin→ℕ→ListBin (drop0 i) j = hcomp (λ where k (i = i1) → []
                                               k (j = i0) → []
                                               k (j = i1) → drop0 i)
                                      (drop0 (i ∨ ~ j))

ListBin→ℕ-sucListBin : (b : ListBin) → ListBin→ℕ (sucListBin b) ≡ suc (ListBin→ℕ b)
ListBin→ℕ-sucListBin [] = refl
ListBin→ℕ-sucListBin (true ∷ b) = ap doubleℕ (ListBin→ℕ-sucListBin b)
ListBin→ℕ-sucListBin (false ∷ b) = refl
ListBin→ℕ-sucListBin (drop0 i) = refl

ℕ→ListBin→ℕ : (x : ℕ) → ListBin→ℕ (ℕ→ListBin x) ≡ x
ℕ→ListBin→ℕ zero = refl
ℕ→ListBin→ℕ (suc x) = ListBin→ℕ-sucListBin (ℕ→ListBin x) ∙ ap suc (ℕ→ListBin→ℕ x)

ℕ≃ListBin : ℕ ≃ ListBin
ℕ≃ListBin = isoToEquiv (iso ℕ→ListBin ListBin→ℕ ListBin→ℕ→ListBin ℕ→ListBin→ℕ)

```
# Part 3: The SIP
### Exercise 8 (★★)
Show that, using an SIP inspired argument, if `(A , _+A_)` is a semigroup and `(B , _+B_)` is some other type with a composition satisfying:

(i) `e : A ≃ B`

(ii) `((x y : A) → e (x +A y) ≡ e x +B e y`

then `(B , _+B_)` defines a semigroup.

Conclude that `(ListBin , _+LB_)` is a semigroup

For inspiration, see Lecture9-notes
```agda

SemiGroupListBin : SemiGroup ListBin
SemiGroupListBin = substEquiv SemiGroup ℕ≃ListBin SemiGroupℕ

```
