module Simulation.Base where
open import Level
  using (Level)
  renaming (zero to lzero; suc to lsuc)
open import Data.Nat
  using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Fin
  using (Fin; inject₁; inject≤; inject+; cast; toℕ; fromℕ; fromℕ<)
  renaming (zero to zeroF; suc to sucF)
open import Data.Fin.Patterns
open import Data.Product
  using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum
  using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)
  renaming (sym to ≡sym; cong to ≡cong; cong-app to ≡cong-app)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Relation.Unary
  using (_∈_; _⟨⊎⟩_; ∅; Satisfiable; Universal; Empty; Pred)
open import Function.Base
  using (id; case_of_)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation
  using (contradiction; contraposition; ¬∃⟶∀¬)
  
open import Data.Empty
  using (⊥; ⊥-elim)
open import Data.Unit.Base
  using (⊤; tt)

open import Base
open import Word
open import NA

-- first required property of ordinary simulation,
-- regarding _acceptance_

Acceptance : {a : Level} {X₁ X₂ A : Set}
             → (na₁ : NA X₁ A) → (na₂ : NA X₂ A)
             → Pred (X₁ × X₂) a → Set _
Acceptance na₁ na₂ R =
  -- given any `x : X₁` and `y : X₂` that are related by `R`,
  ∀ x y → (x , y) ∈ R →
    -- if `x` is accepted, then `y` is also accepted
    x ∈ (NA.accept na₁) → y ∈ (NA.accept na₂)

-- second required property of ordinary simulation,
-- regarding _step-wise match_

StepMatch : {a : Level} {X₁ X₂ A : Set}
            → (na₁ : NA X₁ A) → (na₂ : NA X₂ A)
            → Pred (X₁ × X₂) a → Set _
StepMatch na₁ na₂ R =
  -- given any `x : X₁` and `y : X₂` that are related by `R`,
  ∀ x y → (x , y) ∈ R →
  -- for any `a : A` and `x' : X₁`,
  ∀ a → ∀ x' →
  -- if `(x , a , x')` is a transition in `na₁`,
  (x , a , x') ∈ (NA.trans na₁) →
  -- then there exists some state `y' : X₂` s.t.
  ∃ λ y' →
    -- [1] (y , a , y') is a valid transition in na₂
    (y , a , y') ∈ (NA.trans na₂)
    -- [2] x' and y' are related by R again
    × (x' , y') ∈ R

-- the type of "proofs that a binary relation is a simulation"

record IsSimulation {a : Level} {X₁ X₂ A : Set} (na₁ : NA X₁ A) (na₂ : NA X₂ A)
                    (R : Pred (X₁ × X₂) a) : Set a where
  constructor isSim
  field
    acceptance : Acceptance na₁ na₂ R
    step-match : StepMatch na₁ na₂ R

-- the type of simulations
-- between two NA `NA X₁ A` and `NA X₂ A` with the same alphabet `A`
-- NB. `X₁`, `X₂` and `A` are are again parameters
--     so that they are visible from outside
--     (cf. the definition of `NA`)

record Simulation {a : Level} {X₁ X₂ A : Set} (na₁ : NA X₁ A) (na₂ : NA X₂ A)
                  : Set (lsuc a) where
  constructor aSim
  field
    𝑅            : Pred (X₁ × X₂) a -- the simulation relation
    isSimulation : IsSimulation na₁ na₂ 𝑅 -- proof
