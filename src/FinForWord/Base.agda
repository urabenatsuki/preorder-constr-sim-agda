module FinForWord.Base where

open import Data.Nat
  using (ℕ; _+_; zero; suc; _≤_; ≤-pred)
open import Data.Fin
  using (Fin;  inject₁; inject≤; inject+; cast; toℕ; fromℕ; fromℕ<)
  renaming (zero to zeroF; suc to sucF)
open import Data.Product
  using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum
  using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong)
open Relation.Binary.PropositionalEquality.≡-Reasoning

inject+' : ∀ {l} k → Fin l → Fin (k + l)
inject+' {l} zero j = j
inject+' {l} (suc k) j = sucF (inject+' k j)

Prop[inject[k≡n∧k≤n]] : ∀ {k n : ℕ} → (i : Fin k) → k ≡ n → k ≤ n → Set
Prop[inject[k≡n∧k≤n]] {n} {.n} i refl k≤n = inject≤ i k≤n ≡ i
inject[k≡n∧k≤n] : {k n : ℕ} → (i : Fin k) → (k≡n : k ≡ n) → (k≤n : k ≤ n)
  → Prop[inject[k≡n∧k≤n]] i k≡n k≤n
inject[k≡n∧k≤n] {suc n} {.(suc n)} zeroF refl k≤n = refl
inject[k≡n∧k≤n] {suc n} {.(suc n)} (sucF i) refl k≤n =
  cong sucF (inject[k≡n∧k≤n] {n} i refl (≤-pred k≤n))

splitFin : ∀ {s t : ℕ} → (i : Fin (s + t)) → Fin s ⊎ Fin t
splitFin {zero} {t} i = inj₂ i
splitFin {suc s} {t} zeroF = inj₁ zeroF
splitFin {suc s} {t} (sucF i) with splitFin {s} {t} i
splitFin {suc s} {t} (sucF i) | inj₁ j = inj₁ (sucF j)
splitFin {suc s} {t} (sucF i) | inj₂ j = inj₂ j

