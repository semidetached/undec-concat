module fol_test where

open import Data.Fin
open import Data.Nat hiding (_*_; _⊔_)
open import Data.Empty using (⊥)

open import logic

record Codable (A : Set) (B : Set) : Set where
  field ♯ : ℕ → A
        ♭ : A → B

{- Object language symbols -}
data Tc : Set where
  α   : Tc
  β   : Tc
  _*_ : Tc → Tc → Tc
  v   : ℕ → Tc

infixl 10 _*_

{- Meta language symbols -}
data Tx : Set where
  a : Tx
  b : Tx
  _!_ : Tx → Tx → Tx

TctoTx : Tc → Tx
TctoTx α        = b ! a ! b
TctoTx β        = b ! a ! a ! b
TctoTx (x₁ * x₂) = (TctoTx x₁) ! b ! a ! a ! a ! a ! a ! b ! (TctoTx x₂)
TctoTx (v x)    = b ! a ! a ! a ! a ! a ! a ! b  
 
varTc : Codable Tc Tx
varTc = record { ♯ = v; 
                 ♭ = TctoTx }

infixl 10 _!_

mutual
  data U (A : Set) : Set where
    _⇒_ : U A → U A → U A
    _∧_ : U A → U A → U A
    _∨_ : U A → U A → U A
    ∃   : (A → U A) → U A
    ∃′  : ℕ → U A → U A
    Π   : (A → U A) → U A
    Π′  : ℕ → U A → U A
    ¬   : U A → U A
    [_] : U A → U A
    
    _≡_ : A → A → U A

  infixl 5 _⇒_
  infixl 6 _∧_
  infixl 6 _∨_
  infixl 7 _≡_

  El : ∀ {A} → U A → Set
  El (t₁ ⇒ t₂) = (El t₁) →   (El t₂)
  El (t₁ ∧ t₂) = (El t₁) and (El t₂)
  El (t₁ ∨ t₂) = (El t₁) or  (El t₂)
  El (∃ prop)  = Ex _ (λ w → (El (prop w)))
  El (Π prop)  = Pi _ (λ w → (El (prop w)))
  El (¬ t)     = El t → ⊥
  El ([ t ])   = El t
  El (l₁ ≡ l₂) = Eq l₁ l₂
  El _ = ⊥

Elp : ∀ {A : Set} → {{vA : Codable A Tx}} → ℕ → U A → U A
Elp n (t₁ ⇒ t₂) = (Elp n t₁) ⇒ (Elp n t₂)
Elp n (x ∧ x₁) = (Elp n x) ∧ (Elp n x₁)
Elp n (x ∨ x₁) = (Elp n x) ∨ (Elp n x₁)
Elp {{vA}} n (∃ p) = ∃′ n (Elp (suc n) (p ((Codable.♯ vA) n)))
Elp {{vA}} n (Π p) = Π′ n (Elp (suc n) (p ((Codable.♯ vA) n)))
Elp n (¬ x) = ¬ (Elp n x)
Elp n [ x ] = Elp n x
Elp _ (l₁ ≡ l₂) = l₁ ≡ l₂
Elp _ x = x


{----- Tc Axioms -----}
Axiom1 : U Tc
Axiom1 = Π λ x → Π λ y → Π λ z → x * (y * z) ≡ x * y * z

postulate prfAxiom1 : El Axiom1

Axiom2 : U Tc
Axiom2 = Π λ x → Π λ y → Π λ z → Π λ u →
           [ x * y ≡ z * u ] ⇒ [ x ≡ z ∧ y ≡ u ] ∨ ∃ λ w → [ [ x * w ≡ z ∧ w * u ≡ y ] ∨
                                                             [ z * w ≡ x ∧ w * y ≡ u ] ]

postulate prfAxiom2 : El Axiom2

Axiom3 : U Tc
Axiom3 = Π λ x → Π λ y → ¬ (α ≡ x * y)

prfAxiom3 : El Axiom3
prfAxiom3 = λ s s₁ → λ ()

Axiom4 : U Tc
Axiom4 = Π λ x → Π λ y → ¬ (β ≡ x * y)

prfAxiom4 : El Axiom4
prfAxiom4 = λ s s₁ → λ ()

Axiom5 : U Tc
Axiom5 = ¬ (α ≡ β)

prfAxiom5 : El Axiom5
prfAxiom5 = λ ()

{----- Tc Theorems -----}
Theorem1_α : U Tc
Theorem1_α = Π λ y → Π λ u → α * y ≡ α * u ⇒ y ≡ u

prfTheorem1_α : El Theorem1_α
prfTheorem1_α y u ev1 with (prfAxiom2 α y α u ev1)
prfTheorem1_α y u ev1 | or-intro₁ (and-intro x x₁) = x₁
prfTheorem1_α y u ev1 | or-intro₂ (exists l (or-intro₁ (and-intro x x₁))) = efq (prfAxiom3 α l (symEq x))
prfTheorem1_α y u ev1 | or-intro₂ (exists l (or-intro₂ (and-intro x x₁))) = efq (prfAxiom3 α l (symEq x))

Theorem7 : U Tc
Theorem7 = Π λ x → Π λ y → ¬ (x * α ≡ y * β)

prfTheorem7 : El Theorem7
prfTheorem7 x y ()

toTx : ℕ → Tx
toTx n = b ! helper n ! b
  where helper : ℕ → Tx
        helper (suc zero) = a
        helper (suc n) = helper n ! a
        helper _ = a

Code : ∀ {A} → {{vA : Codable A Tx}} → U A → Tx
Code (t₁ ⇒ t₂) = Code t₁ ! toTx 11 ! Code t₂
Code (t₁ ∧ t₂) = Code t₁ ! toTx 12 ! Code t₂
Code (t₁ ∨ t₂) = Code t₁ ! toTx 13 ! Code t₂
Code (∃ x) = a
Code (Π x) = a
Code {{vA}} (∃′ n t) = toTx 9 ! (Codable.♭ vA (Codable.♯ vA n)) ! Code t
Code {{vA}} (Π′ n t) = toTx 10 ! (Codable.♭ vA (Codable.♯ vA n)) ! Code t
Code (¬ t) = (toTx 14) ! Code t 
Code [ t ] = toTx 3 ! Code t ! toTx 4
Code {{vA}} (a₁ ≡ a₂) = (Codable.♭ vA a₁) ! toTx 8 ! (Codable.♭ vA a₂)

--codeAxiom5 = Code Axiom5
