-- Lemma for soundness

module QSimulation.Lemma where
open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin
  using (Fin; inject₁; inject≤; fromℕ; fromℕ<; toℕ; cast)
  renaming (zero to zeroF; suc to sucF; _+_ to _+F_)
open import Data.Fin.Properties
  using (toℕ-fromℕ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; inspect; [_])
  renaming (refl to ≡refl; sym to ≡sym; cong to ≡cong)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.Product using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (_∈_)

open import Base
open import FinForWord
open import Word
open import NA

-- properties of natural number
a≡a+b→b≡0 : ∀ {a b : ℕ} → a ≡ a + b → b ≡ zero
a≡a+b→b≡0 {zero} {.zero} ≡refl = ≡refl
a≡a+b→b≡0 {suc a} {b} p = a≡a+b→b≡0 {a} {b} (≡cong (λ i → i ∸ 1) p)

≡-pred : ∀ {n m : ℕ} → suc n ≡ suc m → n ≡ m
≡-pred ≡refl = ≡refl

k≢0→k<sn→sk'≡k : ∀ {k n : ℕ}
  → k ≢ zero
  → k < suc n
  → ∃ (λ k' → suc k' ≡ k)
k≢0→k<sn→sk'≡k {zero} {n} p (s≤s q) = contradiction ≡refl p
k≢0→k<sn→sk'≡k {suc k} {n} p q = (k , ≡refl)

k≤n⊎n<k : (k n : ℕ) → (k ≤ n) ⊎ (n < k)
k≤n⊎n<k zero n = inj₁ z≤n
k≤n⊎n<k (suc k) zero = inj₂ (s≤s z≤n)
k≤n⊎n<k (suc k) (suc n) with k≤n⊎n<k k n
k≤n⊎n<k (suc k) (suc n) | inj₁ k≤n = inj₁ (s≤s k≤n)
k≤n⊎n<k (suc k) (suc n) | inj₂ n<k = inj₂ (s≤s n<k)

s[k+l']≡ss[k+l]→l'≡sl : ∀ {k l l' : ℕ}
  → suc (k + l') ≡ suc (suc (k + l)) → l' ≡ suc l
s[k+l']≡ss[k+l]→l'≡sl {zero} {l} {.(suc l)} ≡refl = ≡refl
s[k+l']≡ss[k+l]→l'≡sl {suc k} {l} {l'} p =
  s[k+l']≡ss[k+l]→l'≡sl {k} {l} {l'} (≡-pred p)
    
ss[k'+l']≡ss[k'+l]→l'≡l : ∀ {k' l' l : ℕ}
  → suc (suc (k' + l')) ≡ suc (suc (k' + l)) → l' ≡ l
ss[k'+l']≡ss[k'+l]→l'≡l {zero} {l'} {.l'} ≡refl = ≡refl
ss[k'+l']≡ss[k'+l]→l'≡l {suc k'} {l'} {l} p =
  ss[k'+l']≡ss[k'+l]→l'≡l {k'} {l'} {l} (≡cong (λ i → i ∸ 1) p)

s≤s-≤ : ∀ {n m : ℕ} → (n≤m : n ≤ m) (sn≤sm : suc n ≤ suc m) → (s≤s n≤m) ≡ sn≤sm
s≤s-≤ {zero} {zero} z≤n (s≤s z≤n) = ≡refl
s≤s-≤ {zero} {suc m} z≤n (s≤s z≤n) = ≡refl
s≤s-≤ {suc n} {.(suc _)} (s≤s n≤m) (s≤s sn≤sm) = ≡cong s≤s (s≤s-≤ n≤m sn≤sm)

-- conversion of index of type `Fin m`
casti≡i : ∀ {n : ℕ} → {p : n ≡ n} → (i : Fin n) → cast p i ≡ i
casti≡i {suc n} {≡refl} zeroF = ≡refl
casti≡i {suc n} {≡refl} (sucF i) = ≡cong sucF (casti≡i {n} {≡refl} i)

cast-sucF : ∀ {n m : ℕ} {p : n ≡ m} {q : suc n ≡ suc m} → (i : Fin n)
  → cast q (sucF i) ≡ sucF (cast p i)
cast-sucF {n} {.n} {≡refl} {≡refl} i = ≡refl

cast-cast : ∀ {l m n : ℕ}
  → (p : l ≡ m) → (q : m ≡ n) → (r : l ≡ n)
  → (i : Fin l)
  → cast q (cast p i) ≡ cast r i
cast-cast ≡refl ≡refl ≡refl zeroF = ≡refl
cast-cast {suc n} {.(suc n)} {.(suc n)} ≡refl ≡refl ≡refl (sucF i) =
  begin
  cast ≡refl (cast ≡refl (sucF i))
  ≡⟨ ≡cong (λ j → cast ≡refl j) (cast-sucF {n} {n} {≡refl} {≡refl} i) ⟩
  cast ≡refl (sucF (cast ≡refl i))
  ≡⟨ cast-sucF {n} {n} {≡refl} {≡refl} (cast ≡refl i) ⟩
  sucF (cast ≡refl (cast ≡refl i))
  ≡⟨ ≡cong sucF (cast-cast ≡refl ≡refl ≡refl i) ⟩
  sucF (cast ≡refl i)
  ≡⟨ ≡refl ⟩
  cast ≡refl (sucF i)
  ∎

+F-sucF : ∀ {m n : ℕ} (i : Fin m) (j : Fin n)
  → i +F sucF j ≡ cast (≡sym (+-suc (toℕ i) n)) (sucF (i +F j))
+F-sucF {suc m} {suc n} zeroF zeroF = ≡refl
+F-sucF {suc m} {suc n} zeroF (sucF j) =
  begin
  sucF (sucF j)
  ≡⟨ ≡cong sucF (≡sym (casti≡i {suc n} {≡refl} (sucF j))) ⟩
  sucF (cast ≡refl (sucF j))
  ≡⟨ ≡sym (cast-sucF {suc n} {suc n} {≡refl} {≡refl} (sucF j)) ⟩
  cast ≡refl (sucF (sucF j))
  ∎
+F-sucF {suc m} {suc n} (sucF i) zeroF =
  begin
  sucF (i +F sucF zeroF)
  ≡⟨ ≡cong sucF (+F-sucF i zeroF) ⟩
  sucF (cast _ (sucF i +F zeroF))
  ≡⟨ ≡sym (cast-sucF {suc (toℕ i + suc n)} {toℕ i + suc (suc n)} {≡sym (+-suc (toℕ i) (suc n))} {≡sym (+-suc (suc (toℕ i)) (suc n))} (sucF i +F zeroF)) ⟩
  cast (≡sym (+-suc (suc (toℕ i)) (suc n))) (sucF (sucF i +F zeroF))
  ∎
+F-sucF {suc m} {suc n} (sucF i) (sucF j) =
  begin
  sucF (i +F sucF (sucF j))
  ≡⟨ ≡cong sucF (+F-sucF i (sucF j)) ⟩
  sucF (cast (≡sym (+-suc (toℕ i) (suc n))) (sucF (i +F (sucF j))))
  ≡⟨ ≡sym (cast-sucF {suc (toℕ i + suc n)} {toℕ i + suc (suc n)} {≡sym (+-suc (toℕ i) (suc n))} {≡sym (+-suc (suc (toℕ i)) (suc n))} (sucF (i +F (sucF j)))) ⟩
  cast (≡sym (+-suc (suc (toℕ i)) (suc n))) (sucF (sucF (i +F (sucF j))))
  ∎

fromℕ-+F-+ : (m n : ℕ)
  → {p : toℕ (fromℕ m) + suc n ≡ suc (m + n)}
  → cast p (fromℕ m +F fromℕ n) ≡ fromℕ (m + n)
fromℕ-+F-+ zero zero {p} = ≡refl
fromℕ-+F-+ zero (suc n) {p} = begin
  cast p (fromℕ zero +F fromℕ (suc n))
  ≡⟨⟩
  sucF (cast (≡cong (λ z → z ∸ 1) p) (fromℕ n))
  ≡⟨ ≡cong sucF (casti≡i {suc n} {≡refl} (fromℕ n)) ⟩
  sucF (fromℕ n)
  ∎
fromℕ-+F-+ (suc m) n {p} = begin
  cast p (fromℕ (suc m) +F fromℕ n)
  ≡⟨⟩
  sucF (cast (≡cong (λ z → z ∸ 1) p) (fromℕ m +F fromℕ n))
  ≡⟨ ≡cong sucF (fromℕ-+F-+ m n {≡cong (λ z → z ∸ 1) p}) ⟩
  sucF (fromℕ (m + n))
  ∎

fromℕ-+F-+-cast : (l m n : ℕ)
  → {p : toℕ (fromℕ m) + suc n ≡ l}
  → {q : suc (m + n) ≡ l}
  → (cast p (fromℕ m +F fromℕ n)) ≡ (cast q (fromℕ (m + n)))
fromℕ-+F-+-cast .(suc (m + n)) m n {p} {≡refl} =
  begin
  (cast p (fromℕ m +F fromℕ n))
  ≡⟨ fromℕ-+F-+ m n {p} ⟩
  fromℕ (m + n)
  ≡⟨ ≡sym (casti≡i {suc (m + n)} {≡refl} (fromℕ (m + n))) ⟩
  cast ≡refl (fromℕ (m + n))
  ∎

cast-fromℕ : (l m n : ℕ)
  → (p : suc m ≡ l) → (q : suc n ≡ l)
  → (r : m ≡ n)
  → cast p (fromℕ m) ≡ cast q (fromℕ n)
cast-fromℕ .(suc m) m .m ≡refl ≡refl ≡refl = ≡refl


inject≤inject₁≡inject₁inject≤ : ∀ {m n} {i : Fin m} → (m≤n : m ≤ n)
  → inject≤ (inject₁ i) (s≤s m≤n) ≡ inject₁ (inject≤ i m≤n)
inject≤inject₁≡inject₁inject≤ {.(suc _)} {.(suc _)} {zeroF} (s≤s m≤n) = ≡refl
inject≤inject₁≡inject₁inject≤ {.(suc _)} {.(suc _)} {sucF i} (s≤s m≤n) =
  begin
  sucF (inject≤ (inject₁ i) (s≤s m≤n))
  ≡⟨ ≡cong sucF (inject≤inject₁≡inject₁inject≤ m≤n) ⟩
  sucF (inject₁ (inject≤ i m≤n))
  ∎

inject≤[fromℕ<[sa≤b][b≤c]]≡inject≤[fromℕ[a]][sa≤c] : {a b c : ℕ}
  → (sa≤b : suc a ≤ b)
  → (b≤c : b ≤ c)
  → (sa≤c : suc a ≤ c)
  → inject≤ (fromℕ< sa≤b) (b≤c) ≡ inject≤ (fromℕ a) sa≤c
inject≤[fromℕ<[sa≤b][b≤c]]≡inject≤[fromℕ[a]][sa≤c] {zero} {.(suc _)} {.(suc _)} (s≤s sa≤b) (s≤s b≤c) (s≤s sa≤c) = ≡refl
inject≤[fromℕ<[sa≤b][b≤c]]≡inject≤[fromℕ[a]][sa≤c] {suc a} {.(suc _)} {.(suc _)} (s≤s sa≤b) (s≤s b≤c) (s≤s sa≤c) =
  begin
  sucF (inject≤ (fromℕ< sa≤b) b≤c)
  ≡⟨ ≡cong sucF (inject≤[fromℕ<[sa≤b][b≤c]]≡inject≤[fromℕ[a]][sa≤c] sa≤b b≤c sa≤c) ⟩
  sucF (inject≤ (fromℕ a) sa≤c)
  ∎

+F-inject₁ : {b c : ℕ}
  → (a : Fin b)
  → (i : Fin c)
  → (p : toℕ a + suc c ≡ suc (toℕ a + c))
  → cast p (a +F inject₁ i) ≡ inject₁ (a +F i)
+F-inject₁ {.(suc _)} {.(suc _)} zeroF zeroF p = ≡refl
+F-inject₁ {.(suc _)} {.(suc _)} zeroF (sucF i) p = begin
  sucF (cast (≡cong (λ z → z ∸ 1) p) (inject₁ i))
  ≡⟨ ≡cong sucF (casti≡i {_} {≡refl} (inject₁ i)) ⟩
  sucF (inject₁ i)
  ∎
+F-inject₁ {.(suc _)} {c} (sucF a) i p = begin
  sucF (cast (≡cong (λ z → z ∸ 1) p) (a +F inject₁ i))
  ≡⟨ ≡cong sucF (+F-inject₁ a i (≡cong (λ z → z ∸ 1) p)) ⟩
  sucF (inject₁ (a +F i))
  ∎

cast-fromℕ-+F-inject₁ : {b c d : ℕ}
  → (a : Fin d)
  → (i : Fin b)
  → (p : toℕ a + suc b ≡ suc c)
  → (q : toℕ a + b ≡ c)
  → cast p (a +F inject₁ i) ≡ inject₁ (cast q (a +F i))
cast-fromℕ-+F-inject₁ {b} {.(toℕ a + b)} a i p ≡refl = begin
  cast p (a +F inject₁ i)
  ≡⟨ +F-inject₁ a i p ⟩
  inject₁ (a +F i)
  ≡⟨ ≡cong inject₁ (≡sym (casti≡i {_} {≡refl} (a +F i))) ⟩
  inject₁ (cast ≡refl (a +F i))
  ∎

inject≤[fromℕ<[a≤b]][b≤c]≡fromℕ<[a≤c] : {a b c : ℕ}
  → (sa≤b : suc a ≤ b)
  → (b≤c : b ≤ c)
  → (sa≤c : suc a ≤ c)
  → inject≤ (fromℕ< sa≤b) (b≤c) ≡ fromℕ< sa≤c
inject≤[fromℕ<[a≤b]][b≤c]≡fromℕ<[a≤c] {zero} {suc b} {suc c} (s≤s a≤b) (s≤s b≤c) (s≤s a≤c) = ≡refl
inject≤[fromℕ<[a≤b]][b≤c]≡fromℕ<[a≤c] {suc a} {suc b} {suc c} (s≤s a≤b) (s≤s b≤sc) (s≤s a≤c) =
  begin
  sucF (inject≤ (fromℕ< a≤b) b≤sc)
  ≡⟨ ≡cong sucF (inject≤[fromℕ<[a≤b]][b≤c]≡fromℕ<[a≤c] a≤b b≤sc a≤c) ⟩
  sucF (fromℕ< a≤c)
  ∎

inject≤[fromℕ[sa]][sa<sb]≡s[fromℕ<[a<b]] : {a b : ℕ}
  → (ssa≤sb : suc (suc a) ≤ suc b)
  → (sa≤b : suc a ≤ b)
  → inject≤ (fromℕ (suc a)) ssa≤sb ≡ sucF (fromℕ< sa≤b)
inject≤[fromℕ[sa]][sa<sb]≡s[fromℕ<[a<b]] {zero} {suc b} p q = ≡refl
inject≤[fromℕ[sa]][sa<sb]≡s[fromℕ<[a<b]] {suc a} {.(suc _)} (s≤s p) (s≤s q)
  = ≡cong sucF (inject≤[fromℕ[sa]][sa<sb]≡s[fromℕ<[a<b]] {a} p q)

[sk]+iˡ≡k+siˡ : ∀ {k l : ℕ} → {i : Fin l}
  → {p : suc k + suc l ≡ suc (toℕ (fromℕ k)) + suc l}
  → cast p (inject+' (suc k) (inject₁ i)) ≡ inject₁ (cast ≡refl (fromℕ k +F sucF i))
[sk]+iˡ≡k+siˡ {zero} {l} {zeroF} {≡refl} = ≡refl
[sk]+iˡ≡k+siˡ {zero} {suc l} {sucF i} {≡refl} =
  ≡cong sucF ([sk]+iˡ≡k+siˡ {zero} {l} {i} {≡refl})
[sk]+iˡ≡k+siˡ {suc k} {l} {i} {p} =
  ≡cong sucF ([sk]+iˡ≡k+siˡ {k} {l} {i} {≡cong (λ i → i ∸ 1) p})

s[k+iˡ]≡k+siˡ : ∀ {k l n : ℕ} → {i : Fin l}
  → (p : toℕ (fromℕ k) + suc l ≡ suc n)
  → (q : k + suc l ≡ suc n)
  → sucF (cast q (inject+' k (inject₁ i))) ≡ inject₁ (cast p (fromℕ k +F sucF i))
s[k+iˡ]≡k+siˡ {zero} {suc l} {.(suc l)} {zeroF} ≡refl ≡refl = ≡refl
s[k+iˡ]≡k+siˡ {zero} {suc l} {.(suc l)} {sucF i} ≡refl ≡refl =
  ≡cong sucF (s[k+iˡ]≡k+siˡ {zero} {l} {_} {i} ≡refl ≡refl)
s[k+iˡ]≡k+siˡ {suc k} {sl@.(suc _)} {.(toℕ (fromℕ k) + suc (suc _))} {zeroF} p@≡refl q =
  begin
  sucF (cast q (inject+' (suc k) (inject₁ zeroF)))
  ≡⟨ ≡cong sucF ([sk]+iˡ≡k+siˡ {k} {sl} {zeroF} {q}) ⟩
  sucF (inject₁ (cast ≡refl (fromℕ k +F sucF zeroF)))
  ≡⟨⟩
  inject₁ (cast ≡refl (fromℕ (suc k) +F sucF zeroF))
  ∎
s[k+iˡ]≡k+siˡ {suc k} {sl@.(suc _)} {.(toℕ (fromℕ k) + suc (suc _))} {sucF i} ≡refl q =
  ≡cong sucF ([sk]+iˡ≡k+siˡ {k} {sl} {sucF i} {q})

[inject+]≡[+F] : ∀ {k l n : ℕ}
  → (i : Fin l)
  → (p : k + l ≡ n)
  → (q : toℕ (fromℕ k) + l ≡ n)
  → cast p (inject+' k i) ≡ cast q (fromℕ k +F i)
[inject+]≡[+F] {zero} {.n} {n} i ≡refl ≡refl = ≡refl
[inject+]≡[+F] {suc k} {suc l} {.(suc k + suc l)} i ≡refl q =
  ≡cong sucF ([inject+]≡[+F] {k} i ≡refl (≡cong (λ j → j ∸ 1) q))

cast-inject+'-fromℕ : ∀ (a b : ℕ)
    → (i : Fin a)
    → (q : toℕ (fromℕ b) + suc a ≡ suc (b + a))
    → inject+' (suc b) i ≡ cast q (fromℕ b +F sucF i)
cast-inject+'-fromℕ (suc a) b i q = begin
    inject+' (suc b) i
    ≡⟨⟩
    sucF (inject+' b i)
    ≡⟨ ≡cong sucF (≡sym (casti≡i {b + suc a} {≡refl} (inject+' b i))) ⟩
    sucF (cast ≡refl (inject+' b i))
    ≡⟨ ≡cong sucF ([inject+]≡[+F] {b} i ≡refl p₂) ⟩
    sucF (cast p₂ (fromℕ b +F i))
    ≡⟨ cast-sucF {toℕ (fromℕ b) + suc a} {b + suc a} {p₂} {p₃} (fromℕ b +F i) ⟩
    cast p₃ (sucF (fromℕ b +F i))
    ≡⟨ ≡sym (cast-cast p₁ q p₃  (sucF (fromℕ b +F i))) ⟩
    cast q (cast p₁ (sucF (fromℕ b +F i)))
    ≡⟨ ≡cong (λ i → cast q i) (≡sym (+F-sucF (fromℕ b) i)) ⟩
    cast q (fromℕ b +F sucF i)
    ∎
    where
        p₁ : suc (toℕ (fromℕ b) + suc a) ≡ toℕ (fromℕ b) + suc (suc a)
        p₁ = ≡sym (+-suc (toℕ (fromℕ b)) (suc a))
        p₂ : toℕ (fromℕ b) + suc a ≡ b + suc a
        p₂ = ≡cong (λ i → (i + suc a)) (toℕ-fromℕ b)
        p₃ : suc (toℕ (fromℕ b) + suc a) ≡ suc (b + suc a)
        p₃ = ≡cong suc p₂
                    
cast-inject+'-cast-fromℕ : ∀ (a b c : ℕ)
    → (i : Fin a)
    → (p : suc (b + a) ≡ c)
    → (q : toℕ (fromℕ b) + suc a ≡ c)
    → cast p (inject+' (suc b) i) ≡ cast q (fromℕ b +F sucF i)
cast-inject+'-cast-fromℕ a b .(suc (b + a)) i ≡refl q = begin
    cast ≡refl (inject+' (suc b) i)
    ≡⟨ casti≡i {suc (b + a)} {≡refl} (sucF (inject+' b i)) ⟩
    inject+' (suc b) i
    ≡⟨ cast-inject+'-fromℕ a b i q ⟩
    cast q (fromℕ b +F sucF i)
    ∎

inject≤[i][n≤n]≡i : {n : ℕ}
  → (i : Fin n)
  → (n≤n : n ≤ n)
  → inject≤ i n≤n ≡ i
inject≤[i][n≤n]≡i {.(suc _)} zeroF n≤n = ≡refl
inject≤[i][n≤n]≡i {.(suc _)} (sucF i) n≤n = ≡cong sucF (inject≤[i][n≤n]≡i i (≤-pred n≤n))

inject≤[fromℕ[a]][a<b]≡cast[fromℕ[a]+F0] : ∀ {a b c : ℕ}
  → (sa≤b : suc a ≤ b)
  → (p : toℕ (fromℕ a) + suc c ≡ b)
  → inject≤ (fromℕ a) sa≤b ≡ cast p (fromℕ a +F zeroF)
inject≤[fromℕ[a]][a<b]≡cast[fromℕ[a]+F0]
  {zero} {.(toℕ (fromℕ zero) + suc c)} {c} sa≤b ≡refl = ≡refl
inject≤[fromℕ[a]][a<b]≡cast[fromℕ[a]+F0]
  {suc a} {.(toℕ (fromℕ (suc a)) + suc c)} {c} (s≤s sa≤a+sc) ≡refl =
  ≡cong sucF (inject≤[fromℕ[a]][a<b]≡cast[fromℕ[a]+F0] {a} {_} {c} sa≤a+sc ≡refl)

inject≤[fromℕ[k]][k<ssn]≡inject₁[cast[fromℕ[k]+F0]] : ∀ {k l n : ℕ}
  → (sk≤ssn : suc k ≤ suc n)
  → (p : toℕ (fromℕ k) + suc l ≡ n)
  → inject≤ (fromℕ k) sk≤ssn ≡ inject₁ (cast p (fromℕ k +F zeroF))
inject≤[fromℕ[k]][k<ssn]≡inject₁[cast[fromℕ[k]+F0]] {zero} {n} sk≤ssn ≡refl = ≡refl
inject≤[fromℕ[k]][k<ssn]≡inject₁[cast[fromℕ[k]+F0]] {suc k} {n} (s≤s q) ≡refl =
  ≡cong sucF (inject≤[fromℕ[k]][k<ssn]≡inject₁[cast[fromℕ[k]+F0]] q ≡refl)

s[cast[fromℕ[a]+Fiᵇ]]≡cast[fromℕ[a]+Fsiᵇ] : ∀ {a b c : ℕ} → {i : Fin b }
  → (p : toℕ (fromℕ a) + b ≡ c)
  → (q : toℕ (fromℕ a) + suc b ≡ suc c)
  → sucF (cast p (fromℕ a +F i)) ≡ cast q (fromℕ a +F sucF i)
s[cast[fromℕ[a]+Fiᵇ]]≡cast[fromℕ[a]+Fsiᵇ]
  {zero} {b} {.(toℕ (fromℕ zero) + b)} {j} ≡refl ≡refl = ≡refl
s[cast[fromℕ[a]+Fiᵇ]]≡cast[fromℕ[a]+Fsiᵇ]
  {suc a} {b} {.(toℕ (fromℕ (suc a)) + b)} {j} ≡refl q =
  ≡cong sucF (s[cast[fromℕ[a]+Fiᵇ]]≡cast[fromℕ[a]+Fsiᵇ] {a} {b} {_} {j} ≡refl (≡cong (λ i → i ∸ 1) q) )

cast[fromℕ[sk']+Ffromℕ[l]]≡s[fromℕ[k'+l]] : ∀ {k' l : ℕ}
  → (p : toℕ (fromℕ (suc k')) + suc l ≡ suc (suc k' + l))
  → cast p (fromℕ (suc k') +F fromℕ l) ≡ sucF (fromℕ (k' + l))
cast[fromℕ[sk']+Ffromℕ[l]]≡s[fromℕ[k'+l]] {zero} {zero} ≡refl = ≡refl
cast[fromℕ[sk']+Ffromℕ[l]]≡s[fromℕ[k'+l]] {zero} {suc l} ≡refl =
  ≡cong (λ i → sucF (sucF i))
    (casti≡i {suc l} {≡refl} (fromℕ l))
cast[fromℕ[sk']+Ffromℕ[l]]≡s[fromℕ[k'+l]] {suc k'} {l} p =
  ≡cong sucF (cast[fromℕ[sk']+Ffromℕ[l]]≡s[fromℕ[k'+l]] {k'} {l} (≡cong (λ i → i ∸ 1) p))


--- lemma for trw'w''
module Transition
  (Y A : Set)
  (na@(anNA ⇝ _ _) : NA Y A)
  (m m' : ℕ)
  (y : Fin (suc m) → Y) (y' : Fin (suc m') → Y)
  (y'0≡last[y] :  y' zeroF ≡ y (fromℕ m))
  (w : FinWord m A) (w' : FinWord m' A)
  (trw  : (i : Fin m)  → (y (inject₁ i) ,  w i ,  y (sucF i)) ∈ ⇝)
  (trw' : (i : Fin m') → (y' (inject₁ i) , w' i , y' (sucF i)) ∈ ⇝)
  where

  Lemma-for-trans-state : {s t : ℕ}
    → (a : Fin (suc s) → Y)
    → (b : Fin (suc t) → Y)
    → (i : Fin (s + t)) → Set
  Lemma-for-trans-state {s} {t} a b i with concat a (tailF b) | splitFin {s} {t} i
  Lemma-for-trans-state {s} {t} a b i | a·b | inj₁ i' =
    (a (inject₁ i') ≡ a·b (inject₁ i)) × (a (sucF i') ≡ a·b (sucF i))
  Lemma-for-trans-state {s} {t} a b i | a·b | inj₂ i'' =
    (b (inject₁ i'') ≡ a·b (inject₁ i)) × (b (sucF i'') ≡ a·b (sucF i))
  
  lemma-for-trans-state : {s t : ℕ}
    → (a : Fin (suc s) → Y) → (b : Fin (suc t) → Y)
    → (b0≡last[a] : b zeroF ≡ a (fromℕ s))
    → (i : Fin (s + t))
    → Lemma-for-trans-state a b i
  lemma-for-trans-state {zero} {t@.(suc _)} a b b0≡last[a] zeroF
    with splitFin {zero} {t} zeroF
  lemma-for-trans-state {zero} {.(suc _)} a b b0≡last[a] zeroF
    | inj₂ i'' = b0≡last[a] , ≡refl
  lemma-for-trans-state {zero} {.(suc _)} a b b0≡last[a] (sucF i) = ≡refl , ≡refl
  lemma-for-trans-state {suc s} {t} a b b0≡last[a] zeroF
    with splitFin {suc s} {t} zeroF
  lemma-for-trans-state {suc s} {t} a b b0≡last[a] zeroF
    | inj₁ i' = ≡refl , ≡refl
  lemma-for-trans-state {suc s} {t} a b b0≡last[a] zeroF
    | inj₂ i'' = ≡refl , ≡refl
  lemma-for-trans-state {suc s} {t} a b b0≡last[a] (sucF i)
    with lemma-for-trans-state {s} {t} (tailF a) b b0≡last[a] i
  lemma-for-trans-state {suc s} {t} a b b0≡last[a] (sucF i)
    | IH with splitFin {suc s} {t} (sucF i) | inspect (splitFin {suc (suc s)} {t}) (sucF (sucF i))
  lemma-for-trans-state {suc s} {t} a b b0≡last[a] (sucF i)
    | IH | inj₁ si' | [ q₁ ] with splitFin {suc (suc s)} {t} (sucF (sucF i)) | inspect (splitFin {suc (suc s)} {t}) (sucF (sucF i))
  lemma-for-trans-state {suc s} {t} a b b0≡last[a] (sucF i)
    | IH | inj₁ si' | [ q₁ ] | inj₁ ssi' | [ q₂ ] with splitFin {s} {t} i
  lemma-for-trans-state {suc s} {t} a b b0≡last[a] (sucF i)
    | IH | inj₁ .(sucF i') | [ ≡refl ] | inj₁ .(sucF (sucF i')) | [ ≡refl ] | inj₁ i' = IH
  lemma-for-trans-state {suc s} {t} a b b0≡last[a] (sucF i)
    | IH | inj₂ y | [ q₁ ] with splitFin {suc (suc s)} {t} (sucF (sucF i)) | inspect (splitFin {suc (suc s)} {t}) (sucF (sucF i))
  lemma-for-trans-state {suc s} {t} a b b0≡last[a] (sucF i)
    | IH | inj₂ y | [ q₁ ] | inj₂ y₁ | [ q₂ ] with splitFin {s} {t} (i)
  lemma-for-trans-state {suc s} {t} a b b0≡last[a] (sucF i)
    | IH | inj₂ .y₂ | [ ≡refl ] | inj₂ y₂ | [ ≡refl ] | inj₂ y₂ = IH


  Lemma-for-trans-word : {s t : ℕ}
    → (a : Fin s → A) → (b : Fin t → A) → (i : Fin (s + t)) → Set
  Lemma-for-trans-word {s} {t} a b i
    with splitFin {s} {t} i
  Lemma-for-trans-word {s} {t} a b i
    | inj₁ i' = a i' ≡ concat a b i
  Lemma-for-trans-word {s} {t} a b i
    | inj₂ i'' = b i'' ≡ concat a b i
  
  lemma-for-trans-word : {s t : ℕ}
    → (a : Fin s → A) → (b : Fin t → A)
    → (i : Fin (s + t)) → Lemma-for-trans-word {s} {t} a b i
  lemma-for-trans-word {zero} {t} a b i = ≡refl
  lemma-for-trans-word {suc s} {t} a b zeroF = ≡refl
  lemma-for-trans-word {suc s} {t} a b (sucF i)
    with lemma-for-trans-word {s} {t} (λ j → a (sucF j)) b i
  lemma-for-trans-word {suc s} {t} a b (sucF i)
    | IH with splitFin {suc s} {t} (sucF i) | inspect (splitFin {suc (suc s)} {t}) (sucF (sucF i))
  lemma-for-trans-word {suc s} {t} a b (sucF i)
    | IH | inj₁ x | [ _ ] with splitFin {s} {t} i
  lemma-for-trans-word {suc s} {t} a b (sucF i)
    | IH | inj₁ .(sucF x) | [ ≡refl ] | inj₁ x = IH
  lemma-for-trans-word {suc s} {t} a b (sucF i)
    | IH | inj₂ y | [ _ ] with splitFin {s} {t} i
  lemma-for-trans-word {suc s} {t} a b (sucF i)
    | IH | inj₂ .y | [ ≡refl ] | inj₂ y = IH

  y·y' : Fin (suc (m + m')) → Y
  y·y' = concat y (tailF y')

  tr : (i : Fin (m + m')) → (y·y' (inject₁ i) , concat w w' i , y·y' (sucF i)) ∈ ⇝
  tr i with lemma-for-trans-state y y' y'0≡last[y] i | lemma-for-trans-word w w' i
  tr i | p₁p₂ | q with splitFin {m} {m'} i
  tr i | y[j]≡y·y'[i] , y[sj]≡tail[y]·y'[i] | q | inj₁ j =
    step-∋ ⇝ (trw j)
      (begin
      y (inject₁ j) , w j , y (sucF j)
      ≡⟨ ≡cong (λ a → a , w j , y (sucF j)) y[j]≡y·y'[i] ⟩
      y·y' (inject₁ i) , w j , y (sucF j)
      ≡⟨ ≡cong (λ a → y·y' (inject₁ i) , a , y (sucF j)) q ⟩
      y·y' (inject₁ i) , concat w w' i , y (sucF j)
      ≡⟨ ≡cong (λ a → y·y' (inject₁ i) , concat w w' i , a) y[sj]≡tail[y]·y'[i] ⟩
      y·y' (inject₁ i) , concat w w' i , concat (tailF y) (tailF y') i
      ∎)
  tr i | y'[j']≡y·y'[i] , y'[sj']≡tail[y]·y'[i] | q | inj₂ j' =
    step-∋ ⇝ (trw' j')
      (begin
      y' (inject₁ j') , w' j' , y' (sucF j')
      ≡⟨ ≡cong (λ a → a , w' j' , y' (sucF j')) y'[j']≡y·y'[i] ⟩
      y·y' (inject₁ i) , w' j' , y' (sucF j')
      ≡⟨ ≡cong (λ a → y·y' (inject₁ i) , a , y' (sucF j')) q ⟩
      y·y' (inject₁ i) , concat w w' i , y' (sucF j')
      ≡⟨ ≡cong (λ a → y·y' (inject₁ i) , concat w w' i , a) y'[sj']≡tail[y]·y'[i] ⟩
      y·y' (inject₁ i) , concat w w' i , concat (tailF y) (tailF y') i
      ∎)
 
 