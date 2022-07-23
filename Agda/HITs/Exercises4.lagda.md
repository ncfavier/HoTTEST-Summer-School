```agda
{-# OPTIONS --without-K --rewriting --allow-unsolved-metas #-}

open import new-prelude
open import Lecture4-notes

module Exercises4 where
```

# Constructing homotopies between paths

(⋆) Give two "different" path-between-paths/homotopies between (loop ∙ !
loop) ∙ loop and loop.  They should be different in the sense that one
should cancel the !loop with the first loop, and one with the second
loop.  But these aren't really *really* different, in that there will be
a path-between-paths-between-paths between the two!

```agda
homotopy1-p : {A : Type} {x y : A} (p : x ≡ y) → (p ∙ ! p) ∙ p ≡ p
homotopy1-p p = ap (_∙ p) (!-inv-r p) ∙ ∙unit-l _

homotopy1 : (loop ∙ ! loop) ∙ loop ≡ loop
homotopy1 = homotopy1-p loop

homotopy2-p : {A : Type} {x y : A} (p : x ≡ y) → (p ∙ ! p) ∙ p ≡ p
homotopy2-p p = ! (∙assoc p (! p) _) ∙ ap (p ∙_) (!-inv-l p) ∙ ∙unit-r _

homotopy2 : (loop ∙ ! loop) ∙ loop ≡ loop
homotopy2 = homotopy2-p loop
```

(Harder exercise (🌶️): give a path between homotopy1 and
homotopy2! I'd recommend saving this until later though, because there
is a trick to it that we haven't covered in lecture yet.)

```agda
coherence : {A : Type} {x y : A} (p : x ≡ y) → homotopy1-p p ≡ homotopy2-p p
coherence (refl _) = refl _

path-between-paths-between-paths : homotopy1 ≡ homotopy2
path-between-paths-between-paths = coherence loop
```

# Functions are group homomorphism

(⋆⋆) State and prove a general lemma about what ap of a function on the
inverse of a path (! p) does (see ap-∙ for inspiration).

```agda
ap-! : {A B : Type} {f : A → B} {x y : A} (p : x ≡ y)
       → ap f (! p) ≡ ! (ap f p)
ap-! (refl _) = refl _
```

State and prove a general lemma about what ! (p ∙ q) is.

```agda
!-∙ : {A : Type} {x y z : A} → (p : x ≡ y) → (q : y ≡ z) → ! (p ∙ q) ≡ ! q ∙ ! p
!-∙ (refl _) (refl _) = refl _
```

Use them to prove that the double function takes loop-inverse to
loop-inverse concatenated with itself.

```agda
double-!loop : ap double (! loop) ≡ ! loop ∙ ! loop
double-!loop = ap-! loop ∙ ap ! calculate-double-loop ∙ !-∙ loop loop
```

(⋆) Define a function invert : S1 → S1 such that (ap invert) inverts a path
on the circle, i.e. sends the n-fold loop to the -n-fold loop.

```agda
invert : S1 → S1
invert = S1-rec base (! loop)
```

# Circles equivalence

See the maps between the 1 point circle and the 2 point circle in the
lecture code.  Check that the composite map S1 → S1
is homotopic to the identity on base and loop:

(⋆)

```agda
to-from-base : from (to base) ≡ base
to-from-base = refl _
```

(⋆⋆⋆)

```agda
to-from-loop : ap from (ap to loop) ≡ loop
to-from-loop = ap from (ap to loop)            ≡⟨ ap (ap from) (S1-rec-loop _ _) ⟩
               ap from (east ∙ ! west)         ≡⟨ ap-∙ east _ ⟩
               ap from east ∙ ap from (! west) ≡⟨ ap (_∙ ap from (! west)) (Circle2-rec-east _ _ _ _) ⟩
               loop ∙ ap from (! west)         ≡⟨ ap (loop ∙_) (ap-! _) ⟩
               loop ∙ ! (ap from west)         ≡⟨ ap (λ x → loop ∙ ! x) (Circle2-rec-west _ _ _ _) ⟩
               loop ∎
```

Note: the problems below here are progressively more optional, so if you
run out of time/energy at some point that is totally fine.

# Torus to circles

The torus is equivalent to the product of two circles S1 × S1.  The idea
for the map from the torus to S1 × S1 that is part of this equivalence
is that one loop on on the torus is sent to to the circle loop in one
copy of S1, and the other loop on the torus to the loop in the other
copy of the circle.  Define this map.

Hint: for the image of the square, you might want a lemma saying how
paths in product types compose (⋆⋆⋆):

```agda
compose-pair≡ : {A B : Type} {x1 x2 x3 : A} {y1 y2 y3 : B}
                (p12 : x1 ≡ x2) (p23 : x2 ≡ x3)
                (q12 : y1 ≡ y2) (q23 : y2 ≡ y3)
              → ((pair≡ p12 q12) ∙ (pair≡ p23 q23)) ≡ pair≡ (p12 ∙ p23) (q12 ∙ q23) [ (x1 , y1) ≡ (x3 , y3) [ A × B ] ]
compose-pair≡ (refl _) (refl _) (refl _) (refl _) = refl _
```

(🌶️)
```agda
torus-to-circles : Torus → S1 × S1
torus-to-circles = T-rec (base , base) (pair≡ loop (refl _)) (pair≡ (refl _) loop) square
  where
    square : pair≡ loop (refl _) ∙ pair≡ (refl _) loop ≡ pair≡ (refl _) loop ∙ pair≡ loop (refl _)
    square =
      pair≡ loop (refl _) ∙ pair≡ (refl _) loop ≡⟨ compose-pair≡ loop (refl _) (refl _) loop ⟩
      pair≡ (loop ∙ refl _) (refl _ ∙ loop)     ≡⟨ ap (pair≡ loop) (∙unit-l _) ⟩
      pair≡ loop loop                           ≡⟨ ! (ap (λ x → pair≡ x loop) (∙unit-l _)) ⟩
      pair≡ (refl _ ∙ loop) loop                ≡⟨ ! (compose-pair≡ (refl _) loop loop (refl _)) ⟩
      pair≡ (refl _) loop ∙ pair≡ loop (refl _) ∎
```

# Suspensions (🌶️)

Find a type X such that the two-point circle Circle2 is equivalent to
the suspension Susp X.  Check your answer by defining a logical
equivalence (functions back and forth), since we haven't seen how to
prove that such functions are inverse yet.

```agda
c2s : Circle2 → Susp Bool
c2s = Circle2-rec northS southS (merid true) (merid false)

s2c : Susp Bool → Circle2
s2c = Susp-rec north south (λ b → if b then west else east)
```

Suspension is a functor from types, which means that it acts on
functions as well as types.  Define the action of Susp on functions:

```agda
susp-func : {X Y : Type} → (f : X → Y) → Susp X → Susp Y
susp-func f = Susp-rec northS southS (λ x → merid (f x))
```

To really prove that Susp is a functor, we should check that this action
on functions preserves the identity function and composition of
functions. But to do that we would need the dependent elimination rule
for suspensions, which we haven't talked about yet.

# Pushouts (🌶️)

Fix a type X.  Find types A,B,C with functions f : C → A and g : C → B
such that the suspension Susp X is equivalent to the Pushout C A B f g.
Check your answer by defining a logical equivalence (functions back and
forth), since we haven't seen how to prove that such functions are
inverse yet.

```agda
SuspFromPush : Type → Type
SuspFromPush A = Pushout A 𝟙 𝟙 (λ _ → ⋆) (λ _ → ⋆)

s2p : (A : Type) → Susp A → SuspFromPush A
s2p A = Susp-rec (inl ⋆) (inr ⋆) glue

p2s : (A : Type) → SuspFromPush A → Susp A
p2s A = Push-rec (λ _ → northS) (λ _ → southS) merid
```
