module Base.Equivalence where

open import Level using (Level)
open import Function.Base using (_∘_)

-- "if and only if"
-- cf. https://agda.github.io/agda-stdlib/Function.Equivalence.html

record Equiv {ℓ : Level} (A B : Set ℓ) : Set ℓ where
  constructor _,_
  field
    ⇒ : A -> B
    ⇐ : B -> A

infix 2 _⇔_ -- lower precedence than `infix 3 ¬_`

_⇔_ : {ℓ : Level} -> Set ℓ -> Set ℓ -> Set ℓ
A ⇔ B = Equiv A B

infixr 9 _⊙_

_⊙_ : {A B C : Set} -> (A ⇔ B) -> (B ⇔ C) -> (A ⇔ C)
(pf⇒₁ , pf⇐₁) ⊙ (pf⇒₂ , pf⇐₂) = ( (pf⇒₂ ∘ pf⇒₁) , (pf⇐₁ ∘ pf⇐₂) )
