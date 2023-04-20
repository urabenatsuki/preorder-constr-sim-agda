module Word.Base where
open import Level
  using (Level)
  renaming (zero to lzero; suc to lsuc)
open import Data.Nat
  using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s)
open import Data.Fin
  using (Fin; inject₁; inject+; cast; toℕ; fromℕ; fromℕ<)
  renaming (zero to 0F; suc to sucF)
open import Data.Product
  using (∃; _×_; _,_; proj₁; proj₂; Σ; Σ-syntax)
open import Data.Sum
  using (_⊎_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import FinForWord

----------------------------------------------------------------------
-- infinitary disjoint sum
--
-- cf. https://agda.github.io/agda-stdlib/Data.Sum.Base.html
--       (esp. how to deal with levels)
--     https://agda.github.io/agda-stdlib/Relation.Unary.html
--       (esp. infinitary union)
module InfinitarySum where

  ［_］' : {ℓ ℓ' : Level} → {I : Set}
         → {As : I → Set ℓ} → {B : Σ I As → Set ℓ'}
         → ((i : I) → (a : As i) → B (i , a))
         → (a : Σ I As) → B a
  ［ fs ］' (i , a) = (fs i) a

  ［_］ : {ℓ ℓ' : Level} → {I : Set}
        → {As : I → Set ℓ} → {B : Set ℓ'}
        → ((i : I) → (As i) → B) → Σ I As → B
  ［ fs ］ = ［ fs ］'

open InfinitarySum public

-- A^n as a `Fin n`-indexed data type
FinWord : (n : ℕ) → Set → Set
FinWord n A = Fin n → A

-- A^* := Σ A^n
FINWord : Set → Set
FINWord A = Σ[ n ∈ ℕ ] FinWord n A

inj : {A : Set} → (n : ℕ) → FinWord n A → FINWord A
inj n w = (n , w)

headF : {A : Set} -> {n : ℕ} → FinWord (suc n) A → A
headF w = w 0F

tailF : {A : Set} → {n : ℕ} → FinWord (suc n) A → FinWord n A
tailF w = λ { i → w (sucF i) }

lastF : {A : Set} → {n : ℕ} → FinWord (suc n) A → A
lastF {A} {n} w = w (fromℕ n)

_∷ᶠ_ : {A : Set} → {n : ℕ}
       → A → FinWord n A → FinWord (suc n) A
a ∷ᶠ w = λ { 0F → a; (sucF i) → w i }

-- concatenation
concat : {A : Set} → {m n : ℕ} → FinWord m A → FinWord n A → FinWord (m + n) A
concat {A} {zero} {n} w v = v
concat {A} {suc m} {n} w v 0F = w 0F
concat {A} {suc m} {n} w v (sucF i) = concat (tailF w) v i
_·_ : {A : Set} → FINWord A → FINWord A → FINWord A
(m , w) · (n , v) = (m + n , concat w v)

-- the empty word
emptyF : {A : Set} → FinWord 0 A
emptyF ()

-- the empty word with explicit character set
ε-word' : (A : Set) → FinWord 0 A
ε-word' A = emptyF {A}
ε-word : (A : Set) → FINWord A
ε-word A = (0 , ε-word' A)

-- auxiality function to construct `split`
n-k : {n k : ℕ} → k ≤ n → ∃ (λ (l : ℕ) → k + l ≡ n)
n-k {zero} {.zero} z≤n = zero , refl
n-k {suc n} {.zero} z≤n = suc n , refl
n-k {suc n} {suc k} (s≤s k≤n) =
  (l , ( begin (suc k + l) ≡⟨⟩ suc (k + l) ≡⟨ n≡m→sn≡sm k+l≡n ⟩ (suc n) ∎ ))
  where
    [l]and[k+l≡n] = n-k {n} {k} k≤n
    l = proj₁ [l]and[k+l≡n]
    k+l≡n = proj₂ [l]and[k+l≡n]
    n≡m→sn≡sm : {n m : ℕ} → n ≡ m → suc n ≡ suc m
    n≡m→sn≡sm {n} {.n} refl = refl

-- split word `w` of length `n` at `k`
split : {A : Set} {n k : ℕ} → (w : FinWord n A) → (k≤n : k ≤ n) →
  (FinWord k A) × (FinWord (proj₁ (n-k k≤n)) A)
split {A} {n} {k} w k≤n with n-k k≤n
split {A} {.(k + l)} {k} w k≤n | l , p@refl = (w₁ , w₂)
  where
    w₁ : FinWord k A
    w₁ i = w (inject≤ i k≤n)
    w₂ : FinWord l A
    w₂ j = w (cast p (inject+' k j))

-- get the prefix of length k
_↾_ : {A : Set} {n k : ℕ} → FinWord n A → k < suc n → FinWord k A
w ↾ (s≤s k≤n) = proj₁ (split w k≤n)

-- length
∣_∣ : {A : Set} → FINWord A → ℕ
∣ (n , w) ∣ = n


-- A^ω as a `Nat`-indexed data type
INFWord : Set → Set
INFWord A = ℕ → A

headI : {A : Set} → INFWord A → A
headI w = w 0

tailI : {A : Set} → INFWord A → INFWord A
tailI w n = w (suc n)

_∷ⁱ_ : {A : Set} → A → INFWord A → INFWord A
a ∷ⁱ w = λ { 0 -> a; (suc n) -> w n }

-- A^∞ := A^* ⊎ A^ω
Word : Set → Set
Word A = (FINWord A) ⊎ (INFWord A)
