-- Lemma for soundness

module QSimulation.Lemma where
open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin
  using (Fin; inject₁; inject≤; fromℕ; fromℕ<; toℕ; cast)
  renaming (zero to zeroF; suc to sucF; _+_ to _+F_)
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

a≤b+a : {a b : ℕ} → a ≤ b + a
a≤b+a {a} {zero} = ≤-refl
a≤b+a {a} {suc b} = ≤-step a≤b+a

≡-pred : ∀ {n m : ℕ} → suc n ≡ suc m → n ≡ m
≡-pred ≡refl = ≡refl

k≢0→k<sn→sk'≡k : ∀ {k n : ℕ}
  → k ≢ zero
  → k < suc n
  → ∃ (λ k' → suc k' ≡ k)
k≢0→k<sn→sk'≡k {zero} {n} p (s≤s q) = contradiction ≡refl p
k≢0→k<sn→sk'≡k {suc k} {n} p q = (k , ≡refl)

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


-- conversion of index of type `Fin m`
toℕfromℕ≡id : ∀ (i : ℕ) → toℕ (fromℕ i) ≡ i
toℕfromℕ≡id zero = ≡refl
toℕfromℕ≡id (suc i) = ≡cong suc (toℕfromℕ≡id i)

inject≤[fromℕ[sa]][sa<sb]≡s[fromℕ<[a<b]] : {a b : ℕ}
  → (ssa≤sb : suc (suc a) ≤ suc b)
  → (sa≤b : suc a ≤ b)
  → inject≤ (fromℕ (suc a)) ssa≤sb ≡ sucF (fromℕ< sa≤b)
inject≤[fromℕ[sa]][sa<sb]≡s[fromℕ<[a<b]] {zero} {suc b} p q = ≡refl
inject≤[fromℕ[sa]][sa<sb]≡s[fromℕ<[a<b]] {suc a} {.(suc _)} (s≤s p) (s≤s q)
  = ≡cong sucF (inject≤[fromℕ[sa]][sa<sb]≡s[fromℕ<[a<b]] {a} p q)

[sk]+iˡ≡k+siˡ : ∀ {k l n : ℕ} → {i : Fin l}
  → {p : suc k + suc l ≡ suc (toℕ (fromℕ k)) + suc l}
  → cast p (inject+' (suc k) (inject₁ i)) ≡ inject₁ (cast ≡refl (fromℕ k +F sucF i))
[sk]+iˡ≡k+siˡ {zero} {l} {n} {zeroF} {≡refl} = ≡refl
[sk]+iˡ≡k+siˡ {zero} {suc l} {n} {sucF i} {≡refl} =
  ≡cong sucF ([sk]+iˡ≡k+siˡ {zero} {l} {n} {i} {≡refl})
[sk]+iˡ≡k+siˡ {suc k} {l} {n} {i} {p} =
  ≡cong sucF ([sk]+iˡ≡k+siˡ {k} {l} {n} {i} {≡cong (λ i → i ∸ 1) p})

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
  ≡⟨ ≡cong sucF ([sk]+iˡ≡k+siˡ {k} {sl} {toℕ (fromℕ k) + suc sl} {zeroF} {q}) ⟩
  sucF (inject₁ (cast ≡refl (fromℕ k +F sucF zeroF)))
  ≡⟨⟩
  inject₁ (cast ≡refl (fromℕ (suc k) +F sucF zeroF))
  ∎
s[k+iˡ]≡k+siˡ {suc k} {sl@.(suc _)} {.(toℕ (fromℕ k) + suc (suc _))} {sucF i} ≡refl q =
  ≡cong sucF ([sk]+iˡ≡k+siˡ {k} {sl} {toℕ (fromℕ k) + suc sl} {sucF i} {q})

[inject+]≡[+F] : ∀ {k l n : ℕ}
  → (i : Fin l)
  → (p : k + l ≡ n)
  → (q : toℕ (fromℕ k) + l ≡ n)
  → cast p (inject+' k i) ≡ cast q (fromℕ k +F i)
[inject+]≡[+F] {zero} {.n} {n} i ≡refl ≡refl = ≡refl
[inject+]≡[+F] {suc k} {suc l} {.(suc k + suc l)} i ≡refl q =
  ≡cong sucF ([inject+]≡[+F] {k} i ≡refl (≡cong (λ j → j ∸ 1) q))

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

cast[fromℕ[a]]≡fromℕ[a] : ∀ {a : ℕ} → {p : suc a ≡ suc a} → cast p (fromℕ a) ≡ fromℕ a
cast[fromℕ[a]]≡fromℕ[a] {zero} {≡refl} = ≡refl
cast[fromℕ[a]]≡fromℕ[a] {suc a} {≡refl} = ≡cong sucF (cast[fromℕ[a]]≡fromℕ[a] {a} {≡refl})

cast[fromℕ[sk']+Ffromℕ[l]]≡s[fromℕ[k'+l]] : ∀ {k' l : ℕ}
  → (p : toℕ (fromℕ (suc k')) + suc l ≡ suc (suc k' + l))
  → cast p (fromℕ (suc k') +F fromℕ l) ≡ sucF (fromℕ (k' + l))
cast[fromℕ[sk']+Ffromℕ[l]]≡s[fromℕ[k'+l]] {zero} {zero} ≡refl = ≡refl
cast[fromℕ[sk']+Ffromℕ[l]]≡s[fromℕ[k'+l]] {zero} {suc l} ≡refl =
  ≡cong (λ i → sucF (sucF i))
    (cast[fromℕ[a]]≡fromℕ[a] {l} {≡refl})
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
