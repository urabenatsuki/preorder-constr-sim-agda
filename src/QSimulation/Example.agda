module QSimulation.Example where

open import Data.Product using (_×_; _,_)
open import Relation.Unary using (_∈_; _⊆_)
open import Relation.Binary.PropositionalEquality
  using (_≡_)
  renaming (refl to ≡refl; sym to ≡sym)

open import Base
open import Word
open import NA
open import QSimulation.Base

module LangIncl (A X₁ X₂ : Set) (na₁ : NA X₁ A) (na₂ : NA X₂ A) where
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
