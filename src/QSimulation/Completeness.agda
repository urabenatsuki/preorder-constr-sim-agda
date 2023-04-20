open import NA.Base
module QSimulation.Completeness
  (X₁ X₂ A : Set) (na₁ : NA X₁ A) (na₂ : NA X₂ A)
  where

open import Data.Nat
open import Data.Fin
  using (Fin; inject₁; inject≤; fromℕ; toℕ; cast)
  renaming (zero to zeroF; suc to sucF; _+_ to _+F_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; inspect; [_])
  renaming (refl to ≡refl; sym to ≡sym; cong to ≡cong)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Relation.Unary using (_∈_)
open import Data.Product using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Base
open import Word
open import QSimulation.Base
open QSimulation.Base.ConditionOnQ A
open QSimulation.Base.QSimulationBase A X₁ X₂ na₁ na₂

module Completeness
  (Q@(aPreorder ∣Q∣ Qrefl Qtrans) : Preorder)
  -- (Q-is-closed-under-concat : [ Q ]-is-closed-under-concat)
  where
  
  completeness :
    ∃ λ (R : [ Q ]-constrained-simulation)
    → ∀ x → ∀ y
    → x ≤[ na₁ , na₂ , Q ] y
    → ( x , y ) ∈ [_]-constrained-simulation.R R
  completeness = ( aConstrainedSimulation R final step , λ x y [x,y]∈R → [x,y]∈R )
    where
      -- prove completeness by showing that ≤Q itself is a Q-constrained-simulation
      R : Pred' (X₁ × X₂)
      R (x , y) = x ≤[ na₁ , na₂ , Q ] y
  
      {-
      - x   ⇝[ε]  x  ∈ F₁
      - | ≤Q   Q
      - y   ⇝[w'] y' ∈ F₂
      -}
      final : (x : X₁) (y : X₂) → R (x , y) → Final[ Q ] R x y
      final x y [x,y]∈R x∈F₁
        with [x,y]∈R (ε-word A) ((λ i → x) , ≡refl , (λ ()) , x∈F₁)
      final x y [x,y]∈R x∈F₁
        | (n , w') , w'∈L[y]@(ys , ≡refl , tr , last[ys]∈F₂) , [ε,w']∈Q =
        ( inj n w' , ys (fromℕ n) , (ys , ≡refl , tr , ≡refl) , last[ys]∈F₂ , [ε,w']∈Q )
  
      {-
      - x   ⇝[w]  x' ∈ F₁
      - |≤Q    Q
      - y   ⇝[w'] y' ∈ F₂
      -}
      step : (x : X₁) (y : X₂) → R (x , y) → Step[ Q ] R x y
      step .(xs zeroF) y [x,y]∈R n xs w x≡xs0@≡refl tr last[xs]∈F₁
        with [x,y]∈R (inj (suc n) w) (xs , ≡refl , tr , last[xs]∈F₁)
      step .(xs zeroF) y [x,y]∈R n xs w x≡xs0@≡refl tr last[xs]∈F₁
        | (n' , w') , w'∈L[y]@(ys , ≡refl , tr' , last[ys]∈F₂) , [w,w']∈Q =
        ( suc n , (λ ()) , n≤n
        , inj n' w' -- w'
        , ys (fromℕ n') -- y'
        , wQw' -- (w , w') ∈ Q
        , (ys , ≡refl , tr' , ≡refl) -- y ⇝[w'] y'
        , inj₂ (≡refl , last[ys]∈F₂)
        )
        where
          n≤n : ∀ {m : ℕ} → m ≤ m
          n≤n {zero} = z≤n
          n≤n {suc m} = s≤s n≤n
  
          w≡w↾n≤n : w ≡ w ↾ n≤n
          w≡w↾n≤n = begin
            w
            ≡⟨ ≡sym (proj₁[split[w][n≤n]]≡w {A} {suc n} w n≤n) ⟩
            proj₁ (split w n≤n)
            ∎
  
          wQw' : (inj (suc n) (w ↾ n≤n) , inj n' w') ∈ ∣Q∣
          wQw' = step-∋ ∣Q∣ [w,w']∈Q
            (≡cong (λ v → (inj (suc n) v , inj n' w')) w≡w↾n≤n )

open Completeness using (completeness) public
