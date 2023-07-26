module Base.Relation where

open import Data.Product using (_×_; _,_; ∃)
open import Relation.Unary using (_∈_)
open import Relation.Binary using (REL)
open import Level renaming (zero to lzero; suc to lsuc)

open import Base.Pred using (Pred')

module Rel where
  Rel : (A B : Set) {ℓ : Level} → Set (lsuc ℓ)
  Rel A B {ℓ} = Pred' (A × B) {ℓ}

  _∘ᵣ_ : {A B C : Set} {ℓ : Level} → Rel A B {ℓ} → Rel B C {ℓ} → Rel A C {ℓ}
  R ∘ᵣ S = λ (a , c) → ∃ (λ b → (a , b) ∈ R × (b , c) ∈ S)

  infixl 30 _∘ᵣ_

open Rel public

record Preorder {X : Set} : Set₁ where
  constructor aPreorder
  field
    carrier : Rel X X
    refl : ∀ (s : X) → carrier (s , s)
    trans : ∀ (s s' s'' : X)
      → carrier (s , s') → carrier (s' , s'') → carrier (s , s'')
