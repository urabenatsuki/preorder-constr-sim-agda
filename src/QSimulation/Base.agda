open import NA.Base
module QSimulation.Base where

open import Data.Nat
open import Data.Nat.Properties using (≤-step)
open import Data.Fin
  using (Fin; inject₁; fromℕ; fromℕ< )
  renaming (zero to zeroF; suc to sucF)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_)
  renaming (refl to ≡refl; sym to ≡sym)
open import Relation.Unary using (_∈_; _⊆_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁)
open import Data.Sum using (_⊎_)

open import Base
open import Word

-- Q-trace inclusion
-- `x` refines `y` up to `Q`
Q-trace-incl : {A : Set} {X₁ X₂ : Set}
  → NA X₁ A → NA X₂ A → Preorder → X₁ → X₂ → Set
Q-trace-incl {A} {X₁} {X₂} na₁ na₂ Q@(aPreorder ∣Q∣ _ _) x y =
  -- for any w ∈ A*
  (w : FINWord A)
  -- if w ∈ L*na₁(x)
  → (w ∈ FINAccLang na₁ x)
  -- there exists w' ∈ A*
  → ∃[ w' ]
    -- such that w' ∈ L*na₂(y) and wQW'
    (w' ∈ FINAccLang na₂ y) × ((w , w') ∈ ∣Q∣)

_≤[_,_,_]_ : {A : Set} {X₁ X₂ : Set}
  → X₁ → (na₁ : NA X₁ A) → (na₂ : NA X₂ A) → Preorder → X₂ → Set
x ≤[ na₁ , na₂ , Q ] y =
  Q-trace-incl na₁ na₂ Q x y

infixl 20 _≤[_,_,_]_

module ConditionOnQ (A : Set) where
  [_]-is-closed-under-concat : (Q : Preorder {FINWord A}) → Set
  [ Q@(aPreorder ∣Q∣ _ _) ]-is-closed-under-concat =
    ((w₁ , w₂) : FINWord A × FINWord A) → (w₁ , w₂) ∈ ∣Q∣ →
    ((v₁ , v₂) : FINWord A × FINWord A) → (v₁ , v₂) ∈ ∣Q∣ →
      (w₁ · v₁ , w₂ · v₂) ∈ ∣Q∣
  
  [_,_,_]-is-reasonable : (Q Q₁ Q₂ : Preorder {FINWord A}) → Set
  [ Q@(aPreorder ∣Q∣ _ _) , Q₁@(aPreorder ∣Q₁∣ _ _) , Q₂@(aPreorder ∣Q₂∣ _ _) ]-is-reasonable =
    [ Q ]-is-closed-under-concat ×
    (∀ w → ∀ w' → (w , w') ∈ ∣Q₁∣ → ∣ w' ∣ ≤ ∣ w ∣ ) ×
    (∣Q₁∣ ∘ᵣ ∣Q∣ ∘ᵣ ∣Q₂∣) ⊆ ∣Q∣

module QSimulationBase (A X₁ X₂ : Set) (na₁ : NA X₁ A) (na₂ : NA X₂ A) where
    
  Final[_][_] : ℕ → Preorder → Pred' (X₁ × X₂) → X₁ → X₂ → Set
  Final[ M ][ Q@(aPreorder ∣Q∣ Qrefl Qtrans) ] R x y =
    -- for any n, xs ∈ X₁ⁿ⁺¹, and w ∈ Σⁿ,
    (n : ℕ) →
    (xs : FinWord (suc n) X₁) →
    (w : FinWord n A) →
    -- if x ≡ x₀ ⇝[a₀] x₁ ⇝[a₁] ⋯ ⇝[aₙ₋₁] xₙ ∈ F₁ (where aᵢ = w i)
    x ≡ xs zeroF →
    ((i : Fin n) → NA.trans na₁ ((xs (inject₁ i)) , w i , xs (sucF i))) →
    xs (fromℕ n) ∈ NA.accept na₁ →
    -- and n < M,
    (n < M) →
    -- then
    -- there exist
    -- a word w' ∈ Σ*
    ∃[ w' ] -- w' : FINWord A
    -- and a state y' ∈ X₂
    ∃[ y' ] -- y' : X₂
    -- such that
    -- w Q w'
    (inj n w , w') ∈ ∣Q∣ ×
    -- y ⇝[w'] y' ∈ F₂
    (w' ∈ FINWord-from[ y ]to[ y' ] na₂) × (y' ∈ NA.accept na₂)

  Step[_][_] : ℕ → Preorder → Pred' (X₁ × X₂) → X₁ → X₂ → Set
  Step[ M ][ Q@(aPreorder ∣Q∣ Qrefl Qtrans) ] R x y =
    -- for any xs ∈ X₁ᴹ and w ∈ Σᴹ,
    (xs : FinWord (suc M) X₁) →
    (w : FinWord M A) →
    -- if x ≡ x₀ ⇝[a₀] x₁ ⇝[a₁] ⋯ ⇝[a_{M-1}] xM (where aᵢ = w i)
    x ≡ xs zeroF →
    ((i : Fin M) → NA.trans na₁ ((xs (inject₁ i)) , w i , xs (sucF i))) →
    -- then
    -- there exists a natural number k ∈ { 1, ⋯ , M }
    ∃[ k ] -- k : ℕ
    (k ≢ zero) × ∃ λ (k<sM : k < (suc M)) →
    -- a word w' ∈ Σ*
    ∃[ w' ] -- w' : FINWord A
    -- and a state y' ∈ X₂ such that
    ∃[ y' ] -- y' : X₂
    -- a₀a₁⋯aₖ₋₁ Q w'
    (inj k (w ↾ k<sM) ,  w') ∈ ∣Q∣ ×
    -- y ⇝[w'] y'
    w' ∈ FINWord-from[ y ]to[ y' ] na₂ ×
    -- xₖ R y'
    (xs (fromℕ< k<sM) , y') ∈ R

  
  Final[_] : Preorder → Pred' (X₁ × X₂) → X₁ → X₂ → Set
  Final[ Q@(aPreorder ∣Q∣ Qrefl Qtrans) ] R x y =
    -- if x is accept state,
    x ∈ NA.accept na₁ →
    -- there exist w' and y' such that
    ∃[ w' ] -- w' : FINWord A
    ∃[ y' ] -- y' : X₂
    -- y ⇝[w'] y' ∈ F₂
    (w' ∈ FINWord-from[ y ]to[ y' ] na₂) × (y' ∈ NA.accept na₂) ×
    -- ε Q w
    (ε-word A , w') ∈ ∣Q∣
  
  
  Step[_] : Preorder → Pred' (X₁ × X₂) → X₁ → X₂ → Set
  Step[ Q@(aPreorder ∣Q∣ Qrefl Qtrans) ] R x y =
    (n : ℕ) →
    (xs : FinWord (suc (suc n)) X₁) →
    (as : FinWord (suc n) A) →
    -- if x ≡ x₀ ⇝[a₀] x₁ ⇝[a₁] ⋯ ⇝[aₙ] xₙ₊₁ ∈ F₁
    x ≡ xs zeroF →
    ((i : Fin (suc n)) → NA.trans na₁ ((xs (inject₁ i)) , as i , xs (sucF i))) →
    xs (fromℕ (suc n)) ∈ NA.accept na₁ →
    -- then
    -- there exist
    -- a natural number k ∈ {1 , ⋯ , n + 1}, (suc k ≤ suc n)
    ∃[ k ] -- k : ℕ
    (k ≢ zero) × ∃ λ (k<ssn : k < suc (suc n)) →
    -- a word w' ∈ Σ*
    ∃[ w' ] -- w' : FINWord A
    -- and a state y' ∈ X₂ such that
    ∃[ y' ] -- y' : X₂
    -- a₀a₁⋯aₖ₋₁ Q w'
    (inj k (as ↾ k<ssn) , w') ∈ ∣Q∣ ×
    -- y ⇝[w'] y'
    w' ∈ FINWord-from[ y ]to[ y' ] na₂ ×
    -- (xₖ R y') or (k ≡ suc n and y' ∈ F₂)
    ((xs (fromℕ< k<ssn) , y') ∈ R  ⊎  (k ≡ (suc n) × NA.accept na₂ y'))
  
  StepUpto[_,_,_] : Preorder → Pred' (X₁ × X₁) → Pred' (X₂ × X₂)
    → Pred' (X₁ × X₂) → X₁ → X₂ → Set
  StepUpto[ Q@(aPreorder ∣Q∣ Qrefl Qtrans) , R₁ , R₂ ] R x y =
    (n : ℕ) →
    (xs : FinWord (suc (suc n)) X₁) →
    (as : FinWord (suc n) A) →
    -- if x ≡ x₀ ⇝[a₀] x₁ ⇝[a₁] ⋯ ⇝[aₙ] xₙ₊₁ ∈ F₁
    x ≡ xs zeroF →
    ((i : Fin (suc n)) → NA.trans na₁ ((xs (inject₁ i)) , as i , xs (sucF i))) →
    xs (fromℕ (suc n)) ∈ NA.accept na₁ →
    -- then
    -- there exist
    -- a natural number k ∈ {1 , ⋯ , n + 1}, (suc k ≤ suc n)
    ∃[ k ] -- k : ℕ
    (k ≢ zero) × ∃ λ (k<ssn : k < suc (suc n)) →
    -- a word w' ∈ Σ*
    ∃[ w' ] -- w' : FINWord A
    -- and a state y' ∈ X₂ such that
    ∃[ y' ] -- y' : X₂
    -- a₀a₁⋯aₖ₋₁ Q w'
    (inj k (as ↾ k<ssn) , w') ∈ ∣Q∣ ×
    -- y ⇝[w'] y'
    w' ∈ FINWord-from[ y ]to[ y' ] na₂ ×
    -- (xₖ R₁RR₂ y') or (k ≡ suc n and y' ∈ F₂)
    ((xs (fromℕ< k<ssn) , y') ∈ (R₁ ∘ᵣ R ∘ᵣ R₂) ⊎  (k ≡ (suc n) × NA.accept na₂ y'))
  
  record [_]-bounded-[_]-constrained-simulation (M : ℕ) (Q : Preorder) : Set₁ where
    constructor aBoundedConstrainedSimulation
    field
      R : Pred' (X₁ × X₂)
      final : ∀ x y → R (x , y) → Final[ M ][ Q ] R x y
      step : ∀ x y → R (x , y) → Step[ M ][ Q ] R x y
  
  record [_]-constrained-simulation (Q : Preorder) : Set₁ where
    constructor aConstrainedSimulation
    field
      R : Pred' (X₁ × X₂)
      final : ∀ x y → R (x , y) → Final[ Q ] R x y
      step : ∀ x y → R (x , y) → Step[ Q ] R x y
  
  record [_,_,_]-constrained-simulation-upto
    (Q : Preorder) (R₁ : Pred' (X₁ × X₁)) (R₂ : Pred' (X₂ × X₂)) : Set₁
    where
    constructor aConstrainedSimulationUpto
    field
      R : Pred' (X₁ × X₂)
      final : ∀ x y → R (x , y) → Final[ Q ] R x y
      step : ∀ x y → R (x , y) → StepUpto[ Q , R₁ , R₂ ] R x y
