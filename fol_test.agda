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

{- Meta language symbols -}
data Tx : Set where
  a : Tx
  b : Tx
  _!_ : Tx → Tx → Tx

TctoTx : Tc → Tx
TctoTx α        = b ! a ! b
TctoTx β        = b ! a ! a ! b
TctoTx (x * x₁) = (TctoTx x) ! b ! a ! a ! a ! a ! a ! b ! (TctoTx x₁)
TctoTx (v x)    = b ! a ! a ! a ! a ! a ! a ! b  
 
varTc : Codable Tc Tx
varTc = record { ♯ = v; 
                 ♭ = TctoTx }

infixl 5 _!_

mutual
  data U (A : Set) : Set where
    _∧_ : U A → U A → U A
    _∨_ : U A → U A → U A
    ∃   : (A → U A) → U A
    ∃′  : ℕ → U A → U A
    Π   : (A → U A) → U A
    Π′  : ℕ → U A → U A
    ¬   : U A → U A
    [_] : U A → U A
    
    _≡_ : A → A → U A

  El : ∀ {A} → U A → Set
  El (x ∧ x₁)  = (El x) and (El x₁)
  El (x ∨ x₁)  = (El x) or (El x₁)
  El (∃ p )    = Ex _ (λ w → (El (p w)))
  El (Π p)     = Pi _ (λ w → (El (p w)))
  El (¬ p)     = (El p) → ⊥
  El ([ p ])   = El p
  El (l₁ ≡ l₂) = Eq l₁ l₂
  El _ = ⊥

Elp : ∀ {A : Set} → {{vA : Codable A Tx}} → ℕ → U A → U A
Elp n (x ∧ x₁) = (Elp n x) ∧ (Elp n x₁)
Elp n (x ∨ x₁) = (Elp n x) ∨ (Elp n x₁)
Elp {{vA}} n (∃ p) = ∃′ n (Elp (suc n) (p ((Codable.♯ vA) n)))
Elp {{vA}} n (Π p) = Π′ n (Elp (suc n) (p ((Codable.♯ vA) n)))
Elp n (¬ x) = ¬ (Elp n x)
Elp n [ x ] = Elp n x
Elp _ (l₁ ≡ l₂) = l₁ ≡ l₂
Elp _ x = x

Axiom2 : U Tc
Axiom2 = ∃ (λ w → w ≡ α )

prfAxiom2 : El Axiom2
prfAxiom2 = exists α refl

Axiom3 : U Tc
Axiom3 = Π (λ w → w ≡ w)

prfAxiom3 : El Axiom3
prfAxiom3 = λ s → refl

Axiom4 : U Tc
Axiom4 = ¬ (α ≡ β)

prfAxiom4 : El Axiom4
prfAxiom4 = λ ()

Axiom5 : U Tc
Axiom5 = ¬ [ α ≡ β ]

prfAxiom5 : El Axiom5
prfAxiom5 = λ ()

Axiom6 : U Tc
Axiom6 = Π λ x → (∃ λ y → x ≡ y)

prfAxiom6 : El Axiom6
prfAxiom6 = λ s → exists s refl

toTx : ℕ → Tx
toTx n = b ! helper n ! b
  where helper : ℕ → Tx
        helper (suc zero) = a
        helper (suc n) = helper n ! a
        helper _ = a

Code : ∀ {A} → {{vA : Codable A Tx}} → U A → Tx
Code (t₁ ∧ t₂) = Code t₁ ! toTx 12 ! Code t₂
Code (t₁ ∨ t₂) = Code t₁ ! toTx 13 ! Code t₂
Code (∃ x) = a
Code (Π x) = a
Code {{vA}} (∃′ n t) = toTx 9 ! (Codable.♭ vA (Codable.♯ vA n)) ! Code t
Code {{vA}} (Π′ n t) = toTx 10 ! (Codable.♭ vA (Codable.♯ vA n)) ! Code t
Code (¬ t) = (toTx 14) ! Code t 
Code [ t ] = toTx 3 ! Code t ! toTx 4
Code {{vA}} (a₁ ≡ a₂) = (Codable.♭ vA a₁) ! toTx 8 ! (Codable.♭ vA a₂)

codeAxiom5 = Code Axiom5
