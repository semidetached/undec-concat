module logic where

open import Data.Empty using (⊥)

data _and_ (σ : Set) (τ : Set) : Set where
  and-intro : σ → τ → σ and τ

data _or_ (σ : Set) (τ : Set) : Set where
  or-intro₁ : σ → σ or τ
  or-intro₂ : τ → σ or τ

data Ex (A : Set) (P : A → Set) : Set where
  exists : (a : A) → P a → Ex A P

Pi : (S : Set) → (T : S -> Set) -> Set
Pi S T = (s : S) -> T s

data Eq {A : Set} (x : A) : A → Set where
  refl : Eq x x 

symEq : ∀ {A} {a : A} {b : A} → Eq a b → Eq b a
symEq refl = refl

efq : {P : Set} → ⊥ → P
efq ()
