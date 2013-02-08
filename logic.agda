module logic where

data _and_ (σ : Set) (τ : Set) : Set where
  ∧-intro : σ → τ → σ and τ

data _or_ (σ : Set) (τ : Set) : Set where
  ∨-intro₁ : σ → σ or τ
  ∨-intro₂ : τ → σ or τ

data Ex (A : Set) (P : A → Set) : Set where
  exists : (a : A) → P a → Ex A P

Pi : (S : Set) → (T : S -> Set) -> Set
Pi S T = (s : S) -> T s

data Eq {A : Set} (x : A) : A → Set where
  refl : Eq x x 
