{-# OPTIONS --without-K --rewriting --exact-split #-}
module Trident where
open import new-prelude
open import Lecture4-notes hiding (to; from)

private variable
  ℓ : Level
  A B : Type ℓ
  x y z : A

data Trident {ℓ : Level} {A : Type ℓ} : A → A → A → Type ℓ where
  trefl : (a : A) → Trident a a a

apt : (f : A → B) → Trident x y z → Trident (f x) (f y) (f z)
apt f (trefl _) = trefl _

module Trident≃≡ where
  to : Trident x y z → Sigma ((x ≡ y) × (y ≡ z) × (x ≡ z)) (λ (p , q , r) → p ∙ q ≡ r)
  to (trefl _) = (refl _ , refl _ , refl _) , refl _

  from : Sigma ((x ≡ y) × (y ≡ z) × (x ≡ z)) (λ (p , q , r) → p ∙ q ≡ r) → Trident x y z
  from ((refl _ , refl _ , _) , _) = trefl _

  homotopy-≡ : (e : Sigma ((x ≡ y) × (y ≡ z) × (x ≡ z)) (λ (p , q , r) → p ∙ q ≡ r)) → to (from e) ≡ e
  homotopy-≡ ((refl _ , refl _ , .(refl _ ∙ refl _)) , refl _) = refl _

  homotopy-Trident : (t : Trident x y z) → from (to t) ≡ t
  homotopy-Trident (trefl _) = refl _

postulate
  Shape : Type
  point : Shape
  surf : Trident point point point
  Shape-rec : (x : A) (t : Trident x x x) → Shape → A
  Shape-rec-point : (x : A) (t : Trident x x x) → Shape-rec x t point ≡ x
  {-# REWRITE Shape-rec-point #-}
  Shape-rec-surf : (x : A) (t : Trident x x x) → apt (Shape-rec x t) surf ≡ t

S1∨S1 : Type
S1∨S1 = Pushout 𝟙 S1 S1 (λ _ → base) (λ _ → base)

module Shape≃S1∨S1 where
  to : Shape → S1∨S1
  to = Shape-rec (inl base) {!   !}

  from : S1∨S1 → Shape
  from = Push-rec (S1-rec point {!   !}) (S1-rec point {!   !}) {!   !}

data Weirdent {ℓ : Level} {A : Type ℓ} : A → A → A → Type ℓ where
  lrefl : (a b : A) → Weirdent a a b
  rrefl : (a b : A) → Weirdent a b b

apw : (f : A → B) → Weirdent x y z → Weirdent (f x) (f y) (f z)
apw f (lrefl _ _) = lrefl _ _
apw f (rrefl _ _) = rrefl _ _

postulate
  What : Type
  whoint : What
  whoop : Weirdent whoint whoint whoint
  What-rec : (x : A) (w : Weirdent x x x) → What → A
  What-rec-whoint : (x : A) (w : Weirdent x x x) → What-rec x w whoint ≡ x
  {-# REWRITE What-rec-whoint #-}
  What-rec-whoop : (x : A) (w : Weirdent x x x) → apw (What-rec x w) whoop ≡ w

data Reflexive {ℓ : Level} {A : Type ℓ} (R : A → A → Type ℓ) : A → A → Type ℓ where
  inc : {x y : A} → R x y → Reflexive R x y
  rfl : {x : A} → Reflexive R x x

data R : A → A → Type ℓ where

module ReflexiveR≃≡ where
  to : Reflexive R x x → x ≡ x
