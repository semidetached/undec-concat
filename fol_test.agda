module fol_test where

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

data _∧_ (σ : Set) (τ : Set) : Set where
  ∧-intro : σ → τ → σ ∧ τ

data _∨_ (σ : Set) (τ : Set) : Set where
  ∨-intro₁ : σ → σ ∨ τ
  ∨-intro₂ : τ → σ ∨ τ

data ∃ (A : Set) (P : A → Set) : Set where
  exists : (a : A) → P a → ∃ A P

Π : (S : Set)(T : S -> Set) -> Set
Π S T = (s : S) -> T s

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

data Tc : Set where
  α : Tc
  β : Tc
  _*_ : Tc → Tc → Tc

mutual
  data U (A : Set) : Set where
    _∧′_ : U A → U A → U A
    _∨′_ : U A → U A → U A
    ∃′   : (A → U A) → U A
    ∀′   : (A → U A) → U A
    ¬′   : U A → U A

    _≡′_ : A → A → U A

    lit  : A → U A

  El : ∀ A → U A → Set
  El A (lit x)    = A
  El A (x ∧′ x₁)  = (El A x) ∧ (El A x₁)
  El A (x ∨′ x₁)  = (El A x) ∨ (El A x₁)
  El A (∃′ p )    = ∃ A (λ w → (El A (p w)))
  El A (∀′ p)     = Π A (λ w → (El A (p w)))
  El A (¬′ p)     = (El A p) → ⊥
  El A (l₁ ≡′ l₂) = l₁ ≡ l₂

Axiom2 : U Tc
Axiom2 = ∃′ (λ w → w ≡′ α )

prfAxiom2 : El Tc Axiom2
prfAxiom2 = exists α refl

Axiom3 : U Tc
Axiom3 = ∀′ (λ w → w ≡′ w)

prfAxiom3 : El Tc Axiom3
prfAxiom3 = λ s → refl

Axiom4 : U Tc
Axiom4 = ¬′ (α ≡′ β)

prfAxiom4 : El Tc Axiom4
prfAxiom4 = λ ()

