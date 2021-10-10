module Base.Relation where

open import Data.Product using (_×_; _,_; ∃)
open import Relation.Unary using (_∈_)
open import Relation.Binary using (REL)
open import Level renaming (zero to lzero; suc to lsuc)

open import Base.Pred using (Pred')

module Rel where
  Rel : (A B : Set) → Set₁
  Rel A B = Pred' (A × B)

  _∘ᵣ_ : {A B C : Set} → Rel A B → Rel B C → Rel A C
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
