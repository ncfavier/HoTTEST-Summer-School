# Week 8 - Cubical Agda Exercises

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

module Exercises8 where

open import cubical-prelude
open import Lecture7-notes
open import Lecture8-notes
open import Solutions7
```

## Part I: `transp` and `hcomp`

### Exercise 1 (★)

Prove the propositional computation law for `J`:

```agda
JRefl : {A : Type ℓ} {x : A} (P : (z : A) → x ≡ z → Type ℓ'')
  (d : P x refl) → J P d refl ≡ d
JRefl {x = x} P d i = transp (λ _ → P x refl) i d
```

### Exercise 2 (★★)

Using `transp`, construct a method for turning dependent paths into paths.

**Hint**:
Transport the point `p i` to the fibre `A i1`, and set `φ = i` such that the
transport computes away at `i = i1`.
```text
   x ----(p i)----> y
  A i0    A i      A i1
```

```agda
fromPathP : {A : I → Type ℓ} {x : A i0} {y : A i1} →
  PathP A x y → transport (λ i → A i) x ≡ y
fromPathP {A = A} p i = transp (λ j → A (i ∨ j)) i (p i)
```

### Exercise 3 (★★★)

Using `hcomp`, construct a method for turning paths into dependent paths.

**Hint**:
At each point `i`, the vertical fibre of the following diagram should lie in
`A i`. The key is to parametrise the bottom line with a dependent path from `x`
to `transport A x`. This requires writing a `transp` that computes away at
`i = i0`.

```text
       x  - - - -> y
       ^           ^
       ¦           ¦
  refl ¦           ¦ p i
       ¦           ¦
       ¦           ¦
       x ---> transport A x
```


```agda
toPathP : {A : I → Type ℓ} {x : A i0} {y : A i1} →
  transport (λ i → A i) x ≡ y → PathP A x y
toPathP {A = A} {x = x} p i =
  hcomp
    (λ {j (i = i0) → x ;
        j (i = i1) → p j })
   (transp (λ j → A (i ∧ j)) (~ i) x)
```

### Exercise 4 (★)

Using `toPathP`, prove the following lemma, which lets you fill in dependent
lines in hProps, provided their boundary.

```agda
isProp→PathP : {A : I → Type ℓ} (p : (i : I) → isProp (A i))
  (a₀ : A i0) (a₁ : A i1) → PathP A a₀ a₁
isProp→PathP p a₀ a₁ = toPathP (p _ _ _)
```

### Exercise 5 (★★)

Prove the following lemma characterising equality in subtypes:

```agda
Σ≡Prop : {A : Type ℓ} {B : A → Type ℓ'} {u v : Σ A B} (h : (x : A) → isProp (B x))
       → (p : pr₁ u ≡ pr₁ v) → u ≡ v
Σ≡Prop {u = u} {v = v} h p i .pr₁ = p i
Σ≡Prop {u = u} {v = v} h p i .pr₂ = isProp→PathP (λ i → h (p i)) (pr₂ u) (pr₂ v) i
```

### Exercise 6 (★★★)

Prove that `isContr` is a proposition:

**Hint**:
This requires drawing a cube (yes, an actual 3D one)!

```agda
isPropIsContr : {A : Type ℓ} → isProp (isContr A)
isPropIsContr (c0 , h0) (c1 , h1) i .pr₁ = h0 c1 i
isPropIsContr (c0 , h0) (c1 , h1) i .pr₂ y j =
  hcomp (λ where k (i = i0) → h0 y (j ∧ k)
                 k (i = i1) → h1 y j
                 k (j = i0) → h0 c1 i
                 k (j = i1) → h0 y (i ∨ k))
        (h0 (h1 y j) i)
```
