open import NA.Base
module QSimulation.Base
  (X₁ X₂ A : Set) (na₁ : NA X₁ A) (na₂ : NA X₂ A) where

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

module Rel where
  Rel : (A B : Set) → Set₁
  Rel A B = Pred' (A × B)

  _∘ᵣ_ : {A B C : Set} → Rel A B → Rel B C → Rel A C
  R ∘ᵣ S = λ (a , c) → ∃ (λ b → (a , b) ∈ R × (b , c) ∈ S)

  infixl 30 _∘ᵣ_

open Rel public

record Preorder : Set₁ where
  constructor aPreorder
  field
    carrier : Rel (FINWord A) (FINWord A)
    refl : ∀ (s : FINWord A) → carrier (s , s)
    trans : ∀ (s s' s'' : FINWord A)
      → carrier (s , s') → carrier (s' , s'') → carrier (s , s'')

-- Q-trace inclusion
-- `x` refines `y` up to `Q`
_≤[_,_,_]_ : {Z₁ Z₂ : Set} → Z₁ → (a₁ : NA Z₁ A) → (a₂ : NA Z₂ A) → Preorder → Z₂ → Set
x ≤[ a₁ , a₂ , Q@(aPreorder ∣Q∣ _ _) ] y =
  -- for any w ∈ A*
  ∀ (w : FINWord A)
  -- if w ∈ L*na₁(x)
  → (w ∈ FINAccLang a₁ x)
  -- there exists w' ∈ A*
  → ∃ (λ (w' : FINWord A)
    -- such that w' ∈ L*na₂(y) and wQW'
    → (w' ∈ FINAccLang a₂ y) × ((w , w') ∈ ∣Q∣))

infixl 20 _≤[_,_,_]_

module Example where
  TrivQcarrier : Pred' ((FINWord A) × (FINWord A))
  TrivQcarrier (w , w') = w ≡ w'
  TrivQrefl : ∀ (s : FINWord A) → TrivQcarrier (s , s)
  TrivQrefl w = ≡refl
  TrivQtrans : ∀ (s s' s'' : FINWord A)
          → TrivQcarrier (s , s')
          → TrivQcarrier (s' , s'')
          → TrivQcarrier (s , s'')
  TrivQtrans w .w .w ≡refl ≡refl = ≡refl
  
  TrivQ = aPreorder TrivQcarrier TrivQrefl TrivQtrans  
  
  LanguageInclusion :
    (x : X₁) → (y : X₂)
    → (x ≤[ na₁ , na₂ , TrivQ ] y)
    → (w : FINWord A)
    → (w ∈ FINAccLang na₁ x)
    → (w ∈ FINAccLang na₂ y)
  LanguageInclusion x y x≤[na₁,na₂,≡]y w w∈L₁[x] with x≤[na₁,na₂,≡]y w w∈L₁[x]
  ... | (w' , w'∈L₂y , wQw') = step-∋ (FINAccLang na₂ y) w'∈L₂y (≡sym wQw')

-- monotonicity of Q-trace inclusion
Monotonicity-≤ : {X X' : Set} {na : NA X A} {na' : NA X' A} →
  (Q Q' : Preorder) →
  Preorder.carrier Q ⊆ Preorder.carrier Q' →
  ∀ ((x , y) : X × X') →
  x ≤[ na , na' , Q ] y →
  x ≤[ na , na' , Q' ] y
Monotonicity-≤ Q Q' Q⊆Q' (x , y) x≤[Q]y w w∈L*[x] with x≤[Q]y w w∈L*[x]
... | (w' , w'∈L*[y] , [w,w']∈Q) = (w' ,  w'∈L*[y] , Q⊆Q' [w,w']∈Q)

[_]-is-closed-under-concat : (Q : Preorder) → Set
[ Q@(aPreorder ∣Q∣ _ _) ]-is-closed-under-concat =
  ∀ ((w₁ , w₂) : FINWord A × FINWord A) → (w₁ , w₂) ∈ ∣Q∣ →
  ∀ ((v₁ , v₂) : FINWord A × FINWord A) → (v₁ , v₂) ∈ ∣Q∣ →
    (w₁ · v₁ , w₂ · v₂) ∈ ∣Q∣

[_,_,_]-is-reasonable : (Q Q₁ Q₂ : Preorder) → Set
[ Q@(aPreorder ∣Q∣ _ _) , Q₁@(aPreorder ∣Q₁∣ _ _) , Q₂@(aPreorder ∣Q₂∣ _ _) ]-is-reasonable =
  [ Q ]-is-closed-under-concat ×
  (∀ (w : FINWord A) → ∀ (w' : FINWord A) → (w , w') ∈ ∣Q₁∣ → ∣ w' ∣ ≤ ∣ w ∣ ) ×
  (∣Q₁∣ ∘ᵣ ∣Q∣ ∘ᵣ ∣Q₂∣) ⊆ ∣Q∣

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
