module FinForWord.Base where

open import Data.Nat
  using (ℕ; _+_; zero; suc; _≤_; _<_; ≤-pred; s≤s; z≤n)
open import Data.Fin
  using (Fin; inject₁; inject+; cast; toℕ; fromℕ)
  renaming (zero to zeroF; suc to sucF)
open import Data.Product
  using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum
  using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong)
open Relation.Binary.PropositionalEquality.≡-Reasoning

m≤n⇒m≤1+n : ∀ {m n : ℕ} → m ≤ n → m ≤ 1 + n
m≤n⇒m≤1+n {zero} {n} z≤n = z≤n
m≤n⇒m≤1+n {suc m} {.(suc _)} (s≤s m≤n) = s≤s (m≤n⇒m≤1+n m≤n)

inject+' : ∀ {l} k → Fin l → Fin (k + l)
inject+' {l} zero j = j
inject+' {l} (suc k) j = sucF (inject+' k j)

fromℕ< : ∀ {m n} → m < n → Fin n
fromℕ< {zero} {suc n} m≤n = zeroF
fromℕ< {suc m} {suc n} m≤n = sucF (fromℕ< (≤-pred m≤n))

inject≤ : ∀ {m n} → Fin m → m ≤ n → Fin n
inject≤ {_} {suc n} zeroF le = zeroF
inject≤ {_} {suc n} (sucF i) le = sucF (inject≤ i (≤-pred le))

inject≤-idempotent : ∀ {m n k} (i : Fin m) (m≤n : m ≤ n) (n≤k : n ≤ k) (m≤k : m ≤ k) →
  inject≤ (inject≤ i m≤n) n≤k ≡ inject≤ i m≤k
inject≤-idempotent {_} {suc n} {suc k} zeroF _ _ _ = refl
inject≤-idempotent {_} {suc n} {suc k} (sucF i) m≤n n≤k _ = cong sucF (inject≤-idempotent i (≤-pred m≤n) (≤-pred n≤k) _)

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

