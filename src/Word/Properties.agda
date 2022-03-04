module Word.Properties where
open import Level
  using (Level)
  renaming (zero to lzero; suc to lsuc)
open import Data.Nat
  using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Fin
  using (Fin; inject₁; inject≤; inject+; cast; toℕ; fromℕ; fromℕ<)
  renaming (zero to 0F; suc to sucF)
open import Data.Product
  using (∃; _×_; _,_; proj₁; proj₂; Σ; Σ-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Axiom.Extensionality.Propositional
  using (Extensionality)

open import FinForWord
open import Word.Base

postulate
  ex : Extensionality lzero lzero

-- Path lifting property for words.
-- see [HoTT, Lemma 2.3.2] for example.
module PathLiftingProperty where
  path* :  {ℓ : Level} → {I : Set} → {A : I → Set ℓ}
    → {i j : I} → i ≡ j → A i → A j
  path* refl u = u

  Path-lifting-property : {A : Set} → {i j : ℕ}
    → (u : FinWord i A) → (p : i ≡ j)
    → Set
  Path-lifting-property {A} {i} {j} u p = LHS ≡ RHS
    where
      LHS : Σ[ n ∈ ℕ ] (FinWord n A)
      LHS = inj i u
      RHS : Σ[ n ∈ ℕ ] (FinWord n A)
      RHS = inj j (path* p u)
  path-lifting-property : {A : Set} → {i j : ℕ}
    → (u : FinWord i A) → (p : i ≡ j)
    → Path-lifting-property {A} {i} {j} u p
  path-lifting-property {A} {i} {.i} u refl = refl
open PathLiftingProperty public

-- A word of length 0 equals to `ε-word' A`
0-length-word≡ε : {A : Set} → (w : FinWord 0 A) → w ≡ ε-word' A
0-length-word≡ε w = ex λ ()

-- Lemma for former part of split word
w₁i≡wi : {A : Set} {n k : ℕ} → (w : FinWord n A) → (k≤n : k ≤ n)
  → (i : Fin k)
  → proj₁ (split {A} {n} {k} w k≤n) i ≡ w (inject≤ i k≤n)
w₁i≡wi {A} {n} {k} w k≤n i with n-k k≤n
w₁i≡wi {A} {n} {k} w k≤n i | l , refl = refl
  

-- Lemma for latter part of split word
w₂i≡w[k+i] : {A : Set} {n k : ℕ} → (w : FinWord n A) → (k≤n : k ≤ n)
  → (i : Fin (proj₁ (n-k k≤n)))
  → proj₂ (split {A} {n} {k} w k≤n) i ≡ w (cast (proj₂ (n-k k≤n)) (inject+' k i))
w₂i≡w[k+i] {A} {n} {k} w k≤n i with n-k k≤n
w₂i≡w[k+i] {A} {n} {k} w k≤n i | l , refl with split w k≤n
w₂i≡w[k+i] {A} {n} {k} w k≤n i | l , refl | w₁ , w₂ = refl


-- The word split at the right end equals to the original word.
-- This proposition is used in the proof of completeness of Q-simulation
proj₁[split[w][n≤n]]≡w : {A : Set} {n : ℕ} → (w : FinWord n A) → (n≤n : n ≤ n)
  → proj₁ (split w n≤n) ≡ w
proj₁[split[w][n≤n]]≡w {A} {n} w n≤n with split w n≤n | w₁i≡wi w n≤n
proj₁[split[w][n≤n]]≡w {A} {n} w n≤n | w₁ , w₂ | w₁i≡ = begin
  w₁
  ≡⟨ ex (λ i → w₁i≡ i) ⟩
  (λ i → w (inject≤ i n≤n))
  ≡⟨ ex (λ i → cong w (inject[k≡n∧k≤n] i refl n≤n)) ⟩
  (λ i → w i)
  ≡⟨⟩
  w
  ∎

concat[a∷u][v]i≡a∷concat[u][v]i : {A : Set} {m n : ℕ}
  → (a : A)
  → (u : FinWord n A)
  → (v : FinWord m A)
  → ∀ (i : Fin (suc n + m)) → concat (a ∷ᶠ u) v i ≡ (a ∷ᶠ concat u v) i
concat[a∷u][v]i≡a∷concat[u][v]i {A} {m} {n} a u v 0F = refl
concat[a∷u][v]i≡a∷concat[u][v]i {A} {m} {n} a u v (sucF i) = refl


concat[w][si]≡concat[tail[w]][i] : {A : Set} {n k : ℕ}
  → (w : FinWord (suc n) A) → (k≤n : k ≤ n)
  → (i : Fin (k + proj₁ (n-k k≤n)))
  → concat (proj₁ (split w (s≤s k≤n))) (proj₂ (split w (s≤s k≤n))) (sucF i)
           ≡ concat (proj₁ (split (tailF w) k≤n)) (proj₂ (split (tailF w) k≤n)) i
concat[w][si]≡concat[tail[w]][i] {A} {n} {zero} w k≤n@z≤n i with n-k k≤n
concat[w][si]≡concat[tail[w]][i] {A} {n} {zero} w z≤n i | l , refl = refl
concat[w][si]≡concat[tail[w]][i] {A} {n} {suc k} w k≤n 0F with n-k k≤n
concat[w][si]≡concat[tail[w]][i] {A} {n} {suc k} w k≤n 0F | l , refl = refl
concat[w][si]≡concat[tail[w]][i] {A} {n} {suc k} w k≤n (sucF i) with n-k k≤n
concat[w][si]≡concat[tail[w]][i] {A} {n} {suc k} w k≤n (sucF i) | l , refl = refl

∀i[[concat-split-w]i≡wi] : {A : Set} {n k : ℕ} → (w : FinWord n A) → (k≤n : k ≤ n)
  → (i : Fin (k + proj₁ (n-k k≤n)))
  → concat (proj₁ (split w k≤n)) (proj₂ (split w k≤n)) i ≡ w (cast (proj₂ (n-k k≤n)) i)
∀i[[concat-split-w]i≡wi] {A} {n} {zero} w z≤n i with w₂i≡w[k+i] w z≤n i
∀i[[concat-split-w]i≡wi] {A} {n} {zero} w z≤n i | p = p
∀i[[concat-split-w]i≡wi] {A} {sn@.(suc _)} {suc k} w sk≤sn@(s≤s k≤n) 0F with n-k sk≤sn
∀i[[concat-split-w]i≡wi] {A} {sn@.(suc _)} {suc k} w sk≤sn@(s≤s k≤n) 0F | l , refl = refl
∀i[[concat-split-w]i≡wi] {A} {sn@.(suc _)} {suc k} w sk≤sn@(s≤s k≤n) (sucF i) =
  begin
  concat (proj₁ (split w (s≤s k≤n))) (proj₂ (split w (s≤s k≤n))) (sucF i)
  ≡⟨ concat[w][si]≡concat[tail[w]][i] {A} {_} {k} w k≤n i ⟩
  concat (proj₁ (split (tailF w) k≤n)) (proj₂ (split (tailF w) k≤n)) i
  ≡⟨ ∀i[[concat-split-w]i≡wi] {A} {_} {k} (tailF w) k≤n i ⟩
  w (sucF (cast (proj₂ (n-k k≤n)) i))
  ∎

[concat-split-w]≡w' : {A : Set} {n k : ℕ} → (w : FinWord n A) → (k≤n : k ≤ n) →
  concat (proj₁ (split w k≤n)) (proj₂ (split w k≤n)) ≡ λ i → w (cast (proj₂ (n-k k≤n)) i)
[concat-split-w]≡w' {A} {n} {k} w k≤n = ex (∀i[[concat-split-w]i≡wi] w k≤n)

Prop[∀i[w'i≡wi]] : {A : Set} {n m : ℕ} → (w : FinWord n A) → (m≡n : m ≡ n) → Set
Prop[∀i[w'i≡wi]] {A} {n} {m} w m≡n@refl = ∀ i → ((λ (j : Fin m) → w (cast m≡n j)) i ≡ w i)
∀i[w'i≡wi] : {A : Set} {n m : ℕ} → (w : FinWord n A) → (m≡n : m ≡ n)
  → Prop[∀i[w'i≡wi]] {A} {n} {m} w m≡n
∀i[w'i≡wi] {A} {suc n} {.(suc n)} w refl 0F = refl
∀i[w'i≡wi] {A} {suc n} {.(suc n)} w refl (sucF i) = begin
  w (cast refl (sucF i))
  ≡⟨ refl ⟩
  w (sucF (cast refl i))
  ≡⟨ ∀i[w'i≡wi] {A} {n} {_} (λ j → w (sucF j)) refl i ⟩
  w (sucF i)
  ≡⟨ refl ⟩
  w (sucF i)
  ∎

Prop[w'≡w] : {A : Set} {n m : ℕ} → (w : FinWord n A) → (m≡n : m ≡ n) → Set
Prop[w'≡w] {A} {n} {m} w m≡n@refl = (λ (j : Fin m) → w (cast m≡n j)) ≡ w
w'≡w : {A : Set} {n m : ℕ} → (w : FinWord n A) → (m≡n : m ≡ n) → Prop[w'≡w] w m≡n
w'≡w {A} {n} {m} w m≡n@refl = ex (∀i[w'i≡wi] w refl)

Prop[w₁w₂≡w] : {A : Set} {n k : ℕ} → (w : FinWord n A) → (k≤n : k ≤ n) → Set
Prop[w₁w₂≡w] {A} {n} {k} w k≤n with split w k≤n
Prop[w₁w₂≡w] {A} {n} {k} w k≤n | w₁ , w₂ with n-k k≤n
Prop[w₁w₂≡w] {A} {n} {k} w k≤n | w₁ , w₂ | l , refl  = concat w₁ w₂ ≡ w
w₁w₂≡w : {A : Set} {n k : ℕ} → (w : FinWord n A) → (k≤n : k ≤ n) → Prop[w₁w₂≡w] w k≤n
w₁w₂≡w {A} {n} {k} w k≤n with [concat-split-w]≡w' w k≤n 
w₁w₂≡w {A} {n} {k} w k≤n | p with n-k k≤n
w₁w₂≡w {A} {n} {k} w k≤n | p | l , refl with split w k≤n
w₁w₂≡w {A} {n} {k} w k≤n | p | l , refl | w₁ , w₂ =
  begin concat (λ i → w (inject≤ i k≤n)) (λ j → w (cast _ (inject+' k j)))
  ≡⟨ p ⟩
  (λ (i : Fin (k + l)) → w (cast refl i))
  ≡⟨ w'≡w w refl ⟩
  w
  ∎

a≡a+0 : ∀ {a : ℕ} → a ≡ a + 0
a≡a+0 {zero} = refl
a≡a+0 {suc a} = cong suc a≡a+0
a+0≡a : ∀ {a : ℕ} → a + 0 ≡ a
a+0≡a = sym a≡a+0

-- inj n (λ i → w (inject≤ i k≤m))  ≡   inj m w
Prop[inj[n]w[inj≤i]≡inj[m]w] : {A : Set} → {k n m : ℕ}
  → FinWord m A → n ≡ m → k ≡ n → k ≤ m → Set
Prop[inj[n]w[inj≤i]≡inj[m]w] {A} {k} {n@.k} {m@.k} w refl refl k≤m =
  LHS ≡ RHS
  where
    LHS : FINWord A
    LHS = inj n (λ i → w (inject≤ i k≤m))
    RHS : FINWord A
    RHS = inj m w
inj[n]w[inj≤i]≡inj[m]w : {A : Set} → {k n m : ℕ}
  → (w : FinWord m A) → (n≡m : n ≡ m) → (k≡n : k ≡ n) → (k≤m : k ≤ m)
  → Prop[inj[n]w[inj≤i]≡inj[m]w] w n≡m k≡n k≤m
inj[n]w[inj≤i]≡inj[m]w {A} {k} {.k} {.k} w refl refl k≤m =
  begin
  inj k (λ x → w (inject≤ x k≤m))
  ≡⟨ cong (inj k) (ex (λ i → cong w (inject[k≡n∧k≤n] i refl k≤m) )) ⟩
  inj k w
  ∎

l≡k∧k≤l→[i↦w[inj[i][k≤l]]]≡[l≡k⋆w] : {A : Set} → {k l : ℕ}
  → {l≡k : l ≡ k} → {k≤l : k ≤ l}
  → (w : FinWord l A)
  → (λ i → w (inject≤ i k≤l)) ≡ (path* {_} {ℕ} {λ n → FinWord n A} {l} {k} l≡k w)
l≡k∧k≤l→[i↦w[inj[i][k≤l]]]≡[l≡k⋆w] {A} {k} {.k} {refl} {k≤k} w = begin
  (λ i → w (inject≤ i k≤k))
  ≡⟨ ex (λ i → cong w (inject[k≡n∧k≤n] i refl k≤k)) ⟩
  (λ i → w i)
  ≡⟨⟩
  w
  ∎

inj[m][w]≡inj[n][λi→w[cast[i]]] : {A : Set}
  → (m n : ℕ)
  → (w : FinWord m A)
  → (p : n ≡ m)
  → inj m w ≡ inj n (λ i → w (cast p i))
inj[m][w]≡inj[n][λi→w[cast[i]]] m .m w refl = begin
  m , w
  ≡⟨⟩
  m , (λ i → w i)
  ≡⟨ cong (λ a → m , a) (ex (λ i → cong w (i≡casti refl i))) ⟩
  m , (λ i → w (cast refl i))
  ∎
  where
    i≡casti : ∀ {n : ℕ} → (p : n ≡ n) → (i : Fin n) → i ≡ cast p i
    i≡casti {.(suc _)} refl 0F = refl
    i≡casti {.(suc _)} refl (sucF i) = cong sucF (i≡casti refl i)

-- inj n (λ i → w (inject≤ i k≤n+0))   ≡   inj (n + 0) w
-- This proposition is used in the proof of soundness of Q-simulation
Prop[inj[n]w[inj≤i]≡inj[n+0]w] : {A : Set} → {k n : ℕ}
  → (w : FinWord (n + 0) A) → k ≡ n → k ≤ n + 0 → Set
Prop[inj[n]w[inj≤i]≡inj[n+0]w] {A} {.n} {n} w refl k≤n+0 = LHS ≡ RHS
  where
    LHS : FINWord A
    LHS = inj n (λ i → w (inject≤ i k≤n+0))
    RHS : FINWord A
    RHS = inj (n + 0) w
inj[n]w[inj≤i]≡inj[n+0]w : {A : Set} → {k n : ℕ}
  → (w : FinWord (n + 0) A)
  → (k≡n : k ≡ n) → (k≤n+0 : k ≤ n + 0)
  → Prop[inj[n]w[inj≤i]≡inj[n+0]w] w k≡n k≤n+0
inj[n]w[inj≤i]≡inj[n+0]w {A} {k} {.k} w refl k≤n+0 = begin
  inj k (λ i → w (inject≤ i k≤n+0))
  ≡⟨ cong (inj k) (l≡k∧k≤l→[i↦w[inj[i][k≤l]]]≡[l≡k⋆w] w) ⟩
  inj k (path* {_} {ℕ} {λ n → FinWord n A} {k + 0} {k} a+0≡a w)
  ≡⟨ sym (path-lifting-property w a+0≡a ) ⟩
  inj (k + zero) w
  ∎


last-concat : {X : Set} → {s t : ℕ} → (a : Fin (suc s) → X) → (b : Fin (suc t) → X)
  → (b0≡last[a] : b 0F ≡ a (fromℕ s))
  → b (fromℕ t) ≡ concat a (tailF b) (fromℕ (s + t))
last-concat {X₂} {zero} {zero} a b b0≡last[a] = b0≡last[a]
last-concat {X₂} {zero} {suc t} a b b0≡last[a] = refl
last-concat {X₂} {suc s} {t} a b b0≡last[a] = begin
  b (fromℕ t)
  ≡⟨ last-concat {X₂} {s} {t} (tailF a) b b0≡last[a] ⟩
  concat (tailF a) (tailF b) (fromℕ (s + t))
  ≡⟨⟩
  concat a (tailF b) (fromℕ (suc s + t))
  ∎
  