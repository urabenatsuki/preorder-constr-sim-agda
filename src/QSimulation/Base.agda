open import NA.Base
module QSimulation.Base where

open import Data.Nat
open import Data.Fin
  using (Fin; inject₁; fromℕ; fromℕ< )
  renaming (zero to zeroF; suc to sucF)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_)
  renaming (refl to ≡refl; sym to ≡sym)
open import Relation.Unary using (_∈_; _⊆_)
open import Data.Product using (_×_; _,_; ∃; proj₁)
open import Data.Sum using (_⊎_)

open import Base
open import Word

-- Q-trace inclusion
-- `x` refines `y` up to `Q`
Q-trace-incl : {A : Set} {X₁ X₂ : Set}
  → NA X₁ A → NA X₂ A → Preorder → X₁ → X₂ → Set
Q-trace-incl {A} {X₁} {X₂} na₁ na₂ Q@(aPreorder ∣Q∣ _ _) x y =
  -- for any w ∈ A*
  ∀ (w : FINWord A)
  -- if w ∈ L*na₁(x)
  → (w ∈ FINAccLang na₁ x)
  -- there exists w' ∈ A*
  → ∃ (λ (w' : FINWord A)
    -- such that w' ∈ L*na₂(y) and wQW'
    → (w' ∈ FINAccLang na₂ y) × ((w , w') ∈ ∣Q∣))

_≤[_,_,_]_ : {A : Set} {X₁ X₂ : Set}
  → X₁ → (na₁ : NA X₁ A) → (na₂ : NA X₂ A) → Preorder → X₂ → Set
x ≤[ na₁ , na₂ , Q ] y =
  Q-trace-incl na₁ na₂ Q x y

infixl 20 _≤[_,_,_]_

module ConditionOnQ (A : Set) where
  [_]-is-closed-under-concat : (Q : Preorder {FINWord A}) → Set
  [ Q@(aPreorder ∣Q∣ _ _) ]-is-closed-under-concat =
    ∀ ((w₁ , w₂) : FINWord A × FINWord A) → (w₁ , w₂) ∈ ∣Q∣ →
    ∀ ((v₁ , v₂) : FINWord A × FINWord A) → (v₁ , v₂) ∈ ∣Q∣ →
      (w₁ · v₁ , w₂ · v₂) ∈ ∣Q∣
  
  [_,_,_]-is-reasonable : (Q Q₁ Q₂ : Preorder {FINWord A}) → Set
  [ Q@(aPreorder ∣Q∣ _ _) , Q₁@(aPreorder ∣Q₁∣ _ _) , Q₂@(aPreorder ∣Q₂∣ _ _) ]-is-reasonable =
    [ Q ]-is-closed-under-concat ×
    (∀ w → ∀ w' → (w , w') ∈ ∣Q₁∣ → ∣ w' ∣ ≤ ∣ w ∣ ) ×
    (∣Q₁∣ ∘ᵣ ∣Q∣ ∘ᵣ ∣Q₂∣) ⊆ ∣Q∣

module QSimulationBase (A X₁ X₂ : Set) (na₁ : NA X₁ A) (na₂ : NA X₂ A) where
  Final[_] : Preorder → Pred' (X₁ × X₂) → X₁ → X₂ → Set
  Final[ Q@(aPreorder ∣Q∣ Qrefl Qtrans) ] R x y =
    -- if x is accept state,
    x ∈ NA.accept na₁ →
    -- there exist w' and y' such that
    ∃ (λ (w' : FINWord A) →
    ∃ (λ (y' : X₂) →
    -- y ⇝[w'] y' ∈ F₂
    (w' ∈ FINWord-from[ y ]to[ y' ] na₂) × (y' ∈ NA.accept na₂) ×
    -- ε Q w'
    (ε-word A , w') ∈ ∣Q∣ ))
  
  _↾_ : {n k : ℕ} → FinWord (suc n) A → k < suc (suc n) → FinWord k A
  as ↾ (s≤s k≤sn) = proj₁ (split as k≤sn)
  
  Step[_] : Preorder → Pred' (X₁ × X₂) → X₁ → X₂ → Set
  Step[ Q@(aPreorder ∣Q∣ Qrefl Qtrans) ] R x y =
    ∀ (n : ℕ) →
    ∀ (xs : FinWord (suc (suc n)) X₁) →
    ∀ (as : FinWord (suc n) A) →
    -- if x ≡ x₀ ⇝[a₀] x₁ ⇝[a₁] ⋯ ⇝[aₙ] xₙ₊₁ ∈ F₁
    x ≡ xs zeroF →
    (∀ (i : Fin (suc n)) → NA.trans na₁ ((xs (inject₁ i)) , as i , xs (sucF i))) →
    xs (fromℕ (suc n)) ∈ NA.accept na₁ →
    -- then
    -- there exist
    -- a natural number k ∈ {1 , ⋯ , n + 1}, (suc k ≤ suc n)
    ∃ (λ (k : ℕ) → (k ≢ zero) × ∃ (λ (k<ssn : k < suc (suc n)) →
    -- a word w' ∈ Σ*
    ∃ (λ (w' : FINWord A) →
    -- and a state y' ∈ X₂ such that
    ∃ (λ (y' : X₂) →
    -- a₀a₁⋯aₖ₋₁ Q w'
    (inj k (as ↾ k<ssn) , w') ∈ ∣Q∣ ×
    -- y ⇝[w'] y'
    w' ∈ FINWord-from[ y ]to[ y' ] na₂ ×
    -- (xₖ R y') or (k ≡ suc n and y' ∈ F₂)
    ((xs (fromℕ< k<ssn) , y') ∈ R  ⊎  (k ≡ (suc n) × NA.accept na₂ y')) )))) 
  
  StepUpto[_,_,_] : Preorder → Pred' (X₁ × X₁) → Pred' (X₂ × X₂)
    → Pred' (X₁ × X₂) → X₁ → X₂ → Set
  StepUpto[ Q@(aPreorder ∣Q∣ Qrefl Qtrans) , R₁ , R₂ ] R x y =
    ∀ (n : ℕ) →
    ∀ (xs : FinWord (suc (suc n)) X₁) →
    ∀ (as : FinWord (suc n) A) →
    -- if x ≡ x₀ ⇝[a₀] x₁ ⇝[a₁] ⋯ ⇝[aₙ] xₙ₊₁ ∈ F₁
    x ≡ xs zeroF →
    (∀ (i : Fin (suc n)) → NA.trans na₁ ((xs (inject₁ i)) , as i , xs (sucF i))) →
    xs (fromℕ (suc n)) ∈ NA.accept na₁ →
    -- then
    -- there exist
    -- a natural number k ∈ {1 , ⋯ , n + 1}, (suc k ≤ suc n)
    ∃ (λ (k : ℕ) → (k ≢ zero) × ∃ (λ (k<ssn : k < suc (suc n)) →
    -- a word w' ∈ Σ*
    ∃ (λ (w' : FINWord A) →
    -- and a state y' ∈ X₂ such that
    ∃ (λ (y' : X₂) →
    -- a₀a₁⋯aₖ₋₁ Q w'
    (inj k (as ↾ k<ssn) , w') ∈ ∣Q∣ ×
    -- y ⇝[w'] y'
    w' ∈ FINWord-from[ y ]to[ y' ] na₂ ×
    -- (xₖ R₁RR₂ y') or (k ≡ suc n and y' ∈ F₂)
    ((xs (fromℕ< k<ssn) , y') ∈ (R₁ ∘ᵣ R ∘ᵣ R₂) ⊎  (k ≡ (suc n) × NA.accept na₂ y')) ))))
  
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
