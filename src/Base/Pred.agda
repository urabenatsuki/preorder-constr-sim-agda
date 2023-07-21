module Base.Pred where

open import Level
  using (Level)
  renaming (suc to lsuc)
open import Data.Sum using (_⊎_)
open import Relation.Unary
  using (Pred; _∈_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)
  renaming (subst to ≡subst)

-- Pred with implicit level
-- cf. https://github.com/ziman/agda-stuff/blob/master/dfa.agda

Pred' : {ℓ : Level} -> (A : Set ℓ) -> Set (lsuc ℓ)
Pred' {ℓ} A = Pred A ℓ

_∪_ : {A : Set} -> (P Q : Pred' A) -> Pred' A
P ∪ Q = λ x -> P x ⊎ Q x

-- convenient syntax for equational reasoning
-- cf. ≡-Reasoning in
--     https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.Core.html

infixr 2 step-∋ step-∈

step-∋ : {A : Set} -> {x y : A} -> (P : Pred' A)
         -> (x ∈ P) -> (x ≡ y) -> (y ∈ P)
step-∋ P x∈P x≡y = ≡subst P x≡y x∈P

syntax step-∋ P P∋x x≡y = P ⟨ P∋x ⟩∋ x≡y

step-∈ : {A : Set} -> {P Q : Pred' A} -> (x : A)
         -> (P ≡ Q) -> (x ∈ P) -> (x ∈ Q)
step-∈ x refl x∈P = x∈P

syntax step-∈ x P≡Q x∈P = x ⟨ x∈P ⟩∈ P≡Q

