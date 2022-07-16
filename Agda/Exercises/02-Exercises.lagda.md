# Week 02 - Agda Exercises

## Please read before starting the exercises

**The exercises are designed to increase in difficulty so that we can cater to
our large and diverse audience. This also means that it is *perfectly fine* if
you don't manage to do all exercises: some of them are definitely a bit hard for
beginners and there are likely too many exercises! You *may* wish to come back
to them later when you have learned more.**

Having said that, here we go!

This is a markdown file with Agda code, which means that it displays nicely on
GitHub, but at the same time you can load this file in Agda and fill the holes
to solve exercises.

**Please make a copy of this file to work in, so that it doesn't get overwritten
  (in case we update the exercises through `git`)!**

```agda
{-# OPTIONS --without-K --allow-unsolved-metas #-}

module 02-Exercises where

open import prelude
open import decidability
open import sums
```

## Part I: Propositions as types


### Exercise 1 (★)

Prove
```agda
uncurry : {A B X : Type} → (A → B → X) → (A × B → X)
uncurry f (a , b) = f a b

curry : {A B X : Type} → (A × B → X) → (A → B → X)
curry f a b = f (a , b)
```
You might know these functions from programming e.g. in Haskell.
But what do they say under the propositions-as-types interpretation?


### Exercise 2 (★)

Consider the following goals:
```agda
LEM : Type₁
LEM = {A : Type} → A ∔ ¬ A

wLEM : Type₁
wLEM = {A : Type} → ¬ ¬ A ∔ ¬ A

[i] : {A B C : Type} → (A × B) ∔ C → (A ∔ C) × (B ∔ C)
[i] (inl (a , b)) = inl a , inl b
[i] (inr c) = inr c , inr c

[ii] : {A B C : Type} → (A ∔ B) × C → (A × C) ∔ (B × C)
[ii] (inl a , c) = inl (a , c)
[ii] (inr b , c) = inr (b , c)

[iii] : {A B : Type} → ¬ (A ∔ B) → ¬ A × ¬ B
[iii] k = (λ a → k (inl a)) , (λ b → k (inr b))

[iv] : {A B : Type} → ¬ (A × B) → ¬ A ∔ ¬ B
[iv] = {!!} -- impossible

[v] : {A B : Type} → (A → B) → ¬ B → ¬ A
[v] f ¬b a = ¬b (f a)

[vi] : {A B : Type} → (¬ A → ¬ B) → B → A
[vi] = {!!} -- impossible

[vii] : {A B : Type} → ((A → B) → A) → A
[vii] = {!!} -- impossible

[viii] : {A : Type} {B : A → Type}
    → ¬ (Σ a ꞉ A , B a) → (a : A) → ¬ B a
[viii] k a b = k (a , b)

IX : Type₁
IX = {A : Type} {B : A → Type}
    → ¬ ((a : A) → B a) → (Σ a ꞉ A , ¬ B a)

[ix] : IX
[ix] = {!!} -- impossible

case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x

LEM→IX : LEM → IX
LEM→IX lem {A} {B} ¬∀ with lem {Σ λ a → ¬ B a}
...                    | inl y = y
...                    | inr n = 𝟘-nondep-elim (¬∀ λ a →
                          case lem {B a} of λ
                            { (inl y') → y'
                            ; (inr n') → 𝟘-nondep-elim (n (a , n'))
                            })

IX→wLEM : IX → wLEM
IX→wLEM ix {A} with dec
  where
    dec = ix {B = λ { false → ¬ A; true → A }} (λ f → f false (f true))
... | false , ¬¬a = inl ¬¬a
... | true , ¬a = inr ¬a

IX→LEM : IX → LEM
IX→LEM ix with IX→wLEM ix
...        | inl ¬¬a = inl (pr₁ (ix ¬¬a))
...        | inr ¬a = inr ¬a

[x] : {A B : Type} {C : A → B → Type}
      → ((a : A) → (Σ b ꞉ B , C a b))
      → Σ f ꞉ (A → B) , ((a : A) → C a (f a))
[x] f = (λ a → pr₁ (f a)) , λ a → pr₂ (f a)
```
For each goal determine whether it is provable or not.
If it is, fill it. If not, explain why it shouldn't be possible.
Propositions-as-types might help.


### Exercise 3 (★★)

```agda
¬¬_ : Type → Type
¬¬ A = ¬ (¬ A)

¬¬¬ : Type → Type
¬¬¬ A = ¬ (¬¬ A)
```
In the lecture we have discussed that we can't  prove `∀ {A : Type} → ¬¬ A → A`.
What you can prove however, is
```agda
tne : ∀ {A : Type} → ¬¬¬ A → ¬ A
tne k a = k λ ¬a → ¬a a
```


### Exercise 4 (★★★)
Prove
```agda
¬¬-functor : {A B : Type} → (A → B) → ¬¬ A → ¬¬ B
¬¬-functor f ¬¬a ¬b = ¬¬a λ a → ¬b (f a)

¬¬-kleisli : {A B : Type} → (A → ¬¬ B) → ¬¬ A → ¬¬ B
¬¬-kleisli f ¬¬a ¬b = ¬¬a λ a → f a ¬b
```
Hint: For the second goal use `tne` from the previous exercise





## Part II: `_≡_` for `Bool`

**In this exercise we want to investigate what equality of booleans looks like.
In particular we want to show that for `true false : Bool` we have `true ≢ false`.**

### Exercise 1 (★)

Under the propositions-as-types paradigm, an inhabited type corresponds
to a true proposition while an uninhabited type corresponds to a false proposition.
With this in mind construct a family
```agda
bool-as-type : Bool → Type
bool-as-type true = 𝟙
bool-as-type false = 𝟘
```
such that `bool-as-type true` corresponds to "true" and
`bool-as-type false` corresponds to "false". (Hint:
we have seen canonical types corresponding true and false in the lectures)


### Exercise 2 (★★)

Prove
```agda
bool-≡-char₁ : ∀ (b b' : Bool) → b ≡ b' → (bool-as-type b ⇔ bool-as-type b')
bool-≡-char₁ b b' (refl _) = id , id
```


### Exercise 3 (★★)

Using ex. 2, conclude that
```agda
true≢false : ¬ (true ≡ false)
true≢false ()
```
You can actually prove this much easier! How?


### Exercise 4 (★★★)

Finish our characterisation of `_≡_` by proving
```agda
bool-≡-char₂ : ∀ (b b' : Bool) → (bool-as-type b ⇔ bool-as-type b') → b ≡ b'
bool-≡-char₂ true false (f , _) = 𝟘-elim (f ⋆)
bool-≡-char₂ false true (_ , f) = 𝟘-elim (f ⋆)
bool-≡-char₂ true true _ = refl _
bool-≡-char₂ false false _ = refl _
```

## Part III (🌶)
A type `A` is called *discrete* if it has decidable equality.
Consider the following predicate on types:
```agda
has-bool-dec-fct : Type → Type
has-bool-dec-fct A = Σ f ꞉ (A → A → Bool) , (∀ x y → x ≡ y ⇔ (f x y) ≡ true)
```

Prove that

```agda
decidable-equality-char : (A : Type) → has-decidable-equality A ⇔ has-bool-dec-fct A
decidable-equality-char A = to , from where
  to : has-decidable-equality A → has-bool-dec-fct A
  to dec = f , spec where
    f : A → A → Bool
    f a a' with dec a a'
    ...    | inl _ = true
    ...    | inr _ = false
    spec : ∀ a a' → a ≡ a' ⇔ f a a' ≡ true
    spec a a' with dec a a'
    ...    | inl p = (λ _ → refl _) , λ _ → p
    ...    | inr ¬p = (λ p → 𝟘-nondep-elim (¬p p)) , λ ()
  from : has-bool-dec-fct A → has-decidable-equality A
  from (f , spec) a a' with f a a' in eq
  ...                  | true = inl (pr₂ (spec a a') eq)
  ...                  | false = inr λ p → true≢false (sym (pr₁ (spec a a') p) ∙ eq)
```
