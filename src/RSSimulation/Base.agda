----------------------------------------------------------------------
-- reachability-sensitive simulation between NA

module RSSimulation.Base where
open import Data.Product
  using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum
  using (_⊎_; inj₁; inj₂)
open import Data.Empty
  using (⊥; ⊥-elim)

open import Base
open import Word
open import NA
open import Simulation.Base

-- combinator
-- cf. _⟨⊎⟩_ in
--     https://agda.github.io/agda-stdlib/Relation.Unary.html

infixr  1 _⟨⊎⟩ʳ_

_⟨⊎⟩ʳ_ : {A B C : Set}
         -> Pred' (A × B) -> Pred' (A × C) -> Pred' (A × (B ⊎ C))
(P ⟨⊎⟩ʳ Q) (a , inj₁ b) = P (a , b)
(P ⟨⊎⟩ʳ Q) (a , inj₂ c) = Q (a , c)

-- the type of reachability-sensitive simulations
-- between two NA `NA X₁ A` and `NA X₂ A` with the same alphabet `A`

record RSSimulation {X₁ X₂ A : Set}
                    (na₁ : NA X₁ A) (na₂ : NA X₂ A)
                    : Set₁ where
  constructor aRSSim
  field
    𝑅            : Pred' (X₁ × X₂)  -- the r.s. simulation relation
    𝑅'           : Pred' (X₁ × One) -- a helper relation
    isSimulation : IsSimulation na₁ [ na₂ ]⊥ (𝑅 ⟨⊎⟩ʳ 𝑅') -- proof
