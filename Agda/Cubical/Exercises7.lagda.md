# Week 7 - Cubical Agda Exercises

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

module Exercises7 where

open import cubical-prelude
open import Lecture7-notes
```

```agda
private
  variable
    A : Type ℓ
    B : A → Type ℓ
```

## Part I: Generalizing to dependent functions

### Exercise 1 (★)

State and prove funExt for dependent functions `f g : (x : A) → B x`

```agda
funExtP : {f g : (x : A) → B x} → ((x : A) → f x ≡ g x) → f ≡ g
funExtP p i x = p x i
```

### Exercise 2 (★)

Generalize the type of ap to dependent function `f : (x : A) → B x`
(hint: the result should be a `PathP`)

```agda
apd : {x y : A} → (f : (x : A) → B x) → (p : x ≡ y) → PathP (λ i → B (p i)) (f x) (f y)
apd f p i = f (p i)
```

## Part II: Some facts about (homotopy) propositions and sets

The first three homotopy levels `isContr`, `isProp` and `isSet`
are defined in `cubical-prelude` in the usual way
(only using path types of course).

### Exercise 3 (★)

State and prove that inhabited propositions are contractible

```agda
inhabited-prop : isProp A → A → isContr A
inhabited-prop h a = a , h a
```

### Exercise 4 (deleted) (★★)

We could have stated isProp as follows:

```agda
isProp' : Type ℓ → Type ℓ
isProp' A = (x y : A) → isContr (x ≡ y)
```

Prove that isProp' A implies isProp A and vice versa.
Hint: for one direction you need path composition `_·_`, which one?

```agda
isProp'→isProp : isProp' A → isProp A
isProp'→isProp h x y = h x y .pr₁

isProp→isProp' : isProp A → isProp' A
isProp→isProp' {A = A} h x y .pr₁ = h x y
isProp→isProp' {A = A} h x y .pr₂ q i j =
  hcomp (λ where k (i = i0) → h (h x y j) (h x y j) k
                 k (i = i1) → q j
                 k (j = i0) → h x x (i ∨ k)
                 k (j = i1) → h y y (i ∨ k))
        (h (h x y j) (q j) i)
```

### Exercise 4 (★)

Prove

```agda
isPropΠ : (h : (x : A) → isProp (B x)) → isProp ((x : A) → B x)
isPropΠ h f g i x = h x (f x) (g x) i
```

### Exercise 5 (★)

Prove the inverse of `funExt` (sometimes called `happly`):

```agda
funExt⁻ : {f g : (x : A) → B x} → f ≡ g → ((x : A) → f x ≡ g x)
funExt⁻ p x i = p i x
```

### Exercise 6 (★★)

Use funExt⁻ to prove isSetΠ:

```agda
isSetΠ : (h : (x : A) → isSet (B x)) → isSet ((x : A) → B x)
isSetΠ h a b p q i j x = h x (a x) (b x) (funExt⁻ p x) (funExt⁻ q x) i j
```

### Exercise 7 (★★★): alternative contractibility of singletons

We could have defined the type of singletons as follows

```agda
singl' : {A : Type ℓ} (a : A) → Type ℓ
singl' {A = A} a = Σ x ꞉ A , x ≡ a
```

Prove the corresponding version of contractibility of singetons for
`singl'` (hint: use a suitable combinations of connections and `~_`)

```agda
isContrSingl' : (x : A) → isContr (singl' x)
isContrSingl' x = (x , refl) , (λ (y , p) i → p (~ i) , λ j → p (~ i ∨ j))
```

## Part III: Equality in Σ-types
### Exercise 8 (★★)

Having the primitive notion of equality be heterogeneous is an
easily overlooked, but very important, strength of cubical type
theory. This allows us to work directly with equality in Σ-types
without using transport.

Fill the following holes (some of them are easier than you might think):

```agda
module _ {A : Type ℓ} {B : A → Type ℓ'} {x y : Σ A B} where

  ΣPathP : Σ p ꞉ pr₁ x ≡ pr₁ y , PathP (λ i → B (p i)) (pr₂ x) (pr₂ y)
         → x ≡ y
  ΣPathP p i .pr₁ = p .pr₁ i
  ΣPathP p i .pr₂ = p .pr₂ i

  PathPΣ : x ≡ y
         → Σ p ꞉ pr₁ x ≡ pr₁ y , PathP (λ i → B (p i)) (pr₂ x) (pr₂ y)
  PathPΣ p .pr₁ i = p i .pr₁
  PathPΣ p .pr₂ i = p i .pr₂

  ΣPathP-PathPΣ : ∀ p → PathPΣ (ΣPathP p) ≡ p
  ΣPathP-PathPΣ p = refl

  PathPΣ-ΣPathP : ∀ p → ΣPathP (PathPΣ p) ≡ p
  PathPΣ-ΣPathP p = refl
```

If one looks carefully the proof of prf in Lecture 7 uses ΣPathP
inlined, in fact this is used all over the place when working
cubically and simplifies many proofs which in Book HoTT requires long
complicated reasoning about transport.


## Part IV: Some HITs

Now we want prove some identities of HITs analogous to `Torus ≡ S¹ × S¹`
Hint: you can just use `isoToPath` in all of them.


### Exercise 9 (★★)

We saw two definitions of the torus:
`Torus` having a dependent path constructor `square`
and `Torus'` with a path constructor `square` that involves composition.

Using these two ideas, define the *Klein bottle* in two different ways.

```agda
data Klein : Type where
  point : Klein
  line1 : point ≡ point
  line2 : point ≡ point
  square : PathP (λ i → line1 i ≡ line1 (~ i)) line2 line2

data Klein' : Type where
  point : Klein'
  line1 : point ≡ point
  line2 : point ≡ point
  square : line1 ∙ line2 ≡ line2 ∙ sym line1
```

### Exercise 10 (★★)

Prove

```agda
suspUnitChar : Susp Unit ≡ Interval
suspUnitChar = isoToPath (iso to from to-from from-to) where
  to : Susp Unit → Interval
  to north = zero
  to south = one
  to (merid ⋆ i) = seg i
  from : Interval → Susp Unit
  from zero = north
  from one = south
  from (seg i) = merid ⋆ i
  to-from : ∀ x → to (from x) ≡ x
  to-from zero = refl
  to-from one = refl
  to-from (seg i) = refl
  from-to : ∀ x → from (to x) ≡ x
  from-to north = refl
  from-to south = refl
  from-to (merid ⋆ i) = refl
```


### Exercise 11 (★★★)

Define suspension using the Pushout HIT and prove that it's equal to Susp.

```agda
Susp' : ∀ {ℓ} → Type ℓ → Type ℓ
Susp' A = Pushout {A = A} (λ _ → ⋆) (λ _ → ⋆)

Susp≡Susp' : ∀ {ℓ} {A : Type ℓ} → Susp A ≡ Susp' A
Susp≡Susp' {A = A} = isoToPath (iso to from to-from from-to) where
  to : Susp A → Susp' A
  to north = inl ⋆
  to south = inr ⋆
  to (merid a i) = push a i
  from : Susp' A → Susp A
  from (inl x) = north
  from (inr x) = south
  from (push a i) = merid a i
  to-from : ∀ x → to (from x) ≡ x
  to-from (inl ⋆) = refl
  to-from (inr ⋆) = refl
  to-from (push a i) = refl
  from-to : ∀ x → from (to x) ≡ x
  from-to north = refl
  from-to south = refl
  from-to (merid a i) = refl
```

### Exercise 12 (🌶)

The goal of this exercise is to prove

```agda
suspBoolChar : Susp Bool ≡ S¹
```

For the map `Susp Bool → S¹`, we have to specify the behavior of two
path constructors. The idea is to map one to `loop` and one to `refl`.

For the other direction, we have to fix one base point in `Susp Bool`
and give a non-trivial loop on it, i.e. one that shouldn't cancel out
to `refl`.

Proving that the two maps cancel each other requires some primitives
of `Cubical Agda` that we won't really discuss in the lectures,
namely `hcomp` and `hfill`. These are used (among other things)
to define path composition and ensure that it behaves correctly.

Path composition corresponds to the top of the following square:

```text
            p∙q
       x --------> z
       ^           ^
       ¦           ¦
  refl ¦     sq    ¦ q
       ¦           ¦
       ¦           ¦
       x --------> y
             p
```

The type of `sq` is a `PathP` sending `p` to `p ∙ q`
over `q` and the following lemma lets us construct such a *square*:

```agda
comp-filler : {x y z : A} (p : x ≡ y) (q : y ≡ z)
            → PathP (λ j → refl {x = x} j ≡ q j) p (p ∙ q)
comp-filler {x = x} p q j i = hfill (λ k → λ { (i = i0) → x
                                              ; (i = i1) → q k })
                                    (inS (p i)) j
```

You can use this `comp-filler` as a black-box for proving the round-trips
in this exercise.

**Hint:** For one of the round-trips you only need the following familiar
result, that is a direct consequence of `comp-filler` in `Cubical Agda`

```agda
rUnit : {x y : A} (p : x ≡ y) → p ∙ refl ≡ p
rUnit p = sym (comp-filler p refl)
```

```agda
suspBoolChar = isoToPath (iso to from to-from from-to) where
  to : Susp Bool → S¹
  to north = base
  to south = base
  to (merid true i) = base
  to (merid false i) = loop i
  from : S¹ → Susp Bool
  from base = north
  from (loop i) = (merid false ∙ sym (merid true)) i
  to-from : ∀ x → to (from x) ≡ x
  to-from base = refl
  to-from (loop i) j = rUnit loop j i
  from-to : ∀ x → from (to x) ≡ x
  from-to north = refl
  from-to south = merid true
  from-to (merid true i) j = merid true (i ∧ j)
  from-to (merid false i) j = comp-filler (merid false) (sym (merid true)) (~ j) i
    -- or directly:
    -- hcomp (λ where k (i = i0) → north
    --                k (i = i1) → merid true (j ∨ ~ k)
    --                k (j = i1) → merid false i)
    --       (merid false i)
```
