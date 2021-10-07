open import NA.Base

module QSimulation.Soundness
  (X₁ X₂ A : Set) (na₁ : NA X₁ A) (na₂ : NA X₂ A)
  where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Induction using (<-rec)
open import Data.Fin
  using (Fin; inject₁; inject≤; fromℕ; fromℕ<; toℕ; cast)
  renaming (zero to zeroF; suc to sucF; _+_ to _+F_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; inspect; [_])
  renaming (refl to ≡refl; sym to ≡sym; cong to ≡cong)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Relation.Unary using (_∈_)
open import Data.Product using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary.Negation using (contradiction)

open import Base
open import FinForWord
open import Word
open import QSimulation.Base X₁ X₂ A na₁ na₂

module Soundness
  (Q@(aPreorder ∣Q∣ Qrefl Qtrans) : Preorder)
  (Q-is-closed-under-concat : [ Q ]-is-closed-under-concat)
  (R@(aConstrainedSimulation ∣R∣ Rfinal Rstep) : [ Q ]-constrained-simulation)
  where
  
  k≢0→k<sn→sk'≡k : ∀ {k n : ℕ} → k ≢ zero → k < suc n → ∃ (λ k' → suc k' ≡ k)
  k≢0→k<sn→sk'≡k {zero} {n} p (s≤s q) = contradiction ≡refl p
  k≢0→k<sn→sk'≡k {suc k} {n} p q = (k , ≡refl)

  a≡a+b→b≡0 : ∀ {a b : ℕ} → a ≡ a + b → b ≡ zero
  a≡a+b→b≡0 {zero} {.zero} ≡refl = ≡refl
  a≡a+b→b≡0 {suc a} {b} p = a≡a+b→b≡0 {a} {b} (≡cong (λ i → i ∸ 1) p)
  
  toℕfromℕ≡id : ∀ (i : ℕ) → toℕ (fromℕ i) ≡ i
  toℕfromℕ≡id zero = ≡refl
  toℕfromℕ≡id (suc i) = ≡cong suc (toℕfromℕ≡id i)
  
  ≡-pred : ∀ {n m : ℕ} → suc n ≡ suc m → n ≡ m
  ≡-pred ≡refl = ≡refl
  
  s[k+l']≡ss[k+l]→l'≡sl : ∀ {k l l' : ℕ} → suc (k + l') ≡ suc (suc (k + l)) → l' ≡ suc l
  s[k+l']≡ss[k+l]→l'≡sl {zero} {l} {.(suc l)} ≡refl = ≡refl
  s[k+l']≡ss[k+l]→l'≡sl {suc k} {l} {l'} p =
    s[k+l']≡ss[k+l]→l'≡sl {k} {l} {l'} (≡-pred p)
    
  ss[k'+l']≡ss[k'+l]→l'≡l : ∀ {k' l' l : ℕ} → suc (suc (k' + l')) ≡ suc (suc (k' + l)) → l' ≡ l
  ss[k'+l']≡ss[k'+l]→l'≡l {zero} {l'} {.l'} ≡refl = ≡refl
  ss[k'+l']≡ss[k'+l]→l'≡l {suc k'} {l'} {l} p = ss[k'+l']≡ss[k'+l]→l'≡l {k'} {l'} {l} (≡cong (λ i → i ∸ 1) p)


  Lemma-for-trans-state : ∀ {s t : ℕ} → (a : Fin (suc s) → X₂) → (b : Fin (suc t) → X₂) → (i : Fin (s + t)) → Set
  Lemma-for-trans-state {s} {t} a b i with concat a (tailF b) | splitFin {s} {t} i
  Lemma-for-trans-state {s} {t} a b i | a·b | inj₁ i' =
    (a (inject₁ i') ≡ a·b (inject₁ i)) × (a (sucF i') ≡ a·b (sucF i))
  Lemma-for-trans-state {s} {t} a b i | a·b | inj₂ i'' =
    (b (inject₁ i'') ≡ a·b (inject₁ i)) × (b (sucF i'') ≡ a·b (sucF i))
  lemma-for-trans-state : ∀ {s t : ℕ} → (a : Fin (suc s) → X₂) → (b : Fin (suc t) → X₂) → (b0≡last[a] : b zeroF ≡ a (fromℕ s)) → (i : Fin (s + t)) → Lemma-for-trans-state a b i
  lemma-for-trans-state {zero} {t@.(suc _)} a b b0≡last[a] zeroF with splitFin {zero} {t} zeroF
  lemma-for-trans-state {zero} {.(suc _)} a b b0≡last[a] zeroF | inj₂ i'' = b0≡last[a] , ≡refl
  lemma-for-trans-state {zero} {.(suc _)} a b b0≡last[a] (sucF i) = ≡refl , ≡refl
  lemma-for-trans-state {suc s} {t} a b b0≡last[a] zeroF with splitFin {suc s} {t} zeroF
  lemma-for-trans-state {suc s} {t} a b b0≡last[a] zeroF | inj₁ i' = ≡refl , ≡refl
  lemma-for-trans-state {suc s} {t} a b b0≡last[a] zeroF | inj₂ i'' = ≡refl , ≡refl
  lemma-for-trans-state {suc s} {t} a b b0≡last[a] (sucF i) with lemma-for-trans-state {s} {t} (tailF a) b b0≡last[a] i
  lemma-for-trans-state {suc s} {t} a b b0≡last[a] (sucF i) | IH with splitFin {suc s} {t} (sucF i) | inspect (splitFin {suc (suc s)} {t}) (sucF (sucF i))
  lemma-for-trans-state {suc s} {t} a b b0≡last[a] (sucF i) | IH | inj₁ si' | [ q₁ ] with splitFin {suc (suc s)} {t} (sucF (sucF i)) | inspect (splitFin {suc (suc s)} {t}) (sucF (sucF i))
  lemma-for-trans-state {suc s} {t} a b b0≡last[a] (sucF i) | IH | inj₁ si' | [ q₁ ] | inj₁ ssi' | [ q₂ ] with splitFin {s} {t} i
  lemma-for-trans-state {suc s} {t} a b b0≡last[a] (sucF i) | IH | inj₁ .(sucF i') | [ ≡refl ] | inj₁ .(sucF (sucF i')) | [ ≡refl ] | inj₁ i' = IH
  lemma-for-trans-state {suc s} {t} a b b0≡last[a] (sucF i) | IH | inj₂ y | [ q₁ ] with splitFin {suc (suc s)} {t} (sucF (sucF i)) | inspect (splitFin {suc (suc s)} {t}) (sucF (sucF i))
  lemma-for-trans-state {suc s} {t} a b b0≡last[a] (sucF i) | IH | inj₂ y | [ q₁ ] | inj₂ y₁ | [ q₂ ] with splitFin {s} {t} (i)
  lemma-for-trans-state {suc s} {t} a b b0≡last[a] (sucF i) | IH | inj₂ .y₂ | [ ≡refl ] | inj₂ y₂ | [ ≡refl ] | inj₂ y₂ = IH

  Lemma-for-trans-word : ∀ {S : Set} → ∀ {s t : ℕ} → (a : Fin s → S) → (b : Fin t → S) → (i : Fin (s + t)) → Set
  Lemma-for-trans-word {S} {s} {t} a b i with splitFin {s} {t} i
  Lemma-for-trans-word {S} {s} {t} a b i | inj₁ i' = a i' ≡ concat a b i
  Lemma-for-trans-word {S} {s} {t} a b i | inj₂ i'' = b i'' ≡ concat a b i
  lemma-for-trans-word : ∀ {S : Set} → ∀ {s t : ℕ} → (a : Fin s → S) → (b : Fin t → S) → (i : Fin (s + t)) → Lemma-for-trans-word {S} {s} {t} a b i
  lemma-for-trans-word {S} {zero} {t} a b i = ≡refl
  lemma-for-trans-word {S} {suc s} {t} a b zeroF = ≡refl
  lemma-for-trans-word {S} {suc s} {t} a b (sucF i) with lemma-for-trans-word {S} {s} {t} (λ j → a (sucF j)) b i
  lemma-for-trans-word {S} {suc s} {t} a b (sucF i) | IH with splitFin {suc s} {t} (sucF i) | inspect (splitFin {suc (suc s)} {t}) (sucF (sucF i))
  lemma-for-trans-word {S} {suc s} {t} a b (sucF i) | IH | inj₁ x | [ _ ] with splitFin {s} {t} i
  lemma-for-trans-word {S} {suc s} {t} a b (sucF i) | IH | inj₁ .(sucF x) | [ ≡refl ] | inj₁ x = IH
  lemma-for-trans-word {S} {suc s} {t} a b (sucF i) | IH | inj₂ y | [ _ ] with splitFin {s} {t} i
  lemma-for-trans-word {S} {suc s} {t} a b (sucF i) | IH | inj₂ .y | [ ≡refl ] | inj₂ y = IH


  lemma-for-soundness :
    ∀ (l : ℕ)
    → (∀ (l' : ℕ) → (l' < l)
      → ∀ ((x , y) : X₁ × X₂)
      → (x , y) ∈ ∣R∣
      → ∀ (w : FinWord l' A)
      → (inj l' w ∈ FINAccLang na₁ x)
      → ∃ (λ (w' : FINWord A)
        → (w' ∈ FINAccLang na₂ y) × (Preorder.carrier Q (inj l' w , w'))) )
    → ∀ ((x , y) : X₁ × X₂)
    → (x , y) ∈ ∣R∣
    → ∀ (w : FinWord l A)
    → (inj l w ∈ FINAccLang na₁ x)
    → ∃ (λ (w' : FINWord A)
      → (w' ∈ FINAccLang na₂ y) × (Preorder.carrier Q (inj l w , w')))
  -- proof by infuction on length of word w such as x⇝[w]x'
  -- Base case
  lemma-for-soundness zero _ (.(headF xs) , y) [x,y]∈R w w∈L*[x]@(xs , ≡refl , trw , last[xs]∈F₁) with Rfinal (headF xs) y [x,y]∈R last[xs]∈F₁ | 0-length-word≡ε w
  lemma-for-soundness zero rec (.(headF xs) , y) [x,y]∈R w w∈L*[x]@(xs , ≡refl , trw , last[xs]∈F₁) | w'@(inj n as) , y' , y⇝[w']y'@(ys , ≡refl , tr₂ , ≡refl) , y'∈F₂ , ε∣Q∣w' | ≡refl  =
    (w' , (ys , ≡refl , tr₂ , y'∈F₂) , ε∣Q∣w')
  -- Step
  {- By using Step-condition, we have w' and y' such that
    x₀ ⇝[w]  xₙ ∈ F₁
    |R    Q
    y  ⇝[w'] y' ∈ F₂

    or

    x₀ ⇝[w₁] xₖ ⇝[w₂] xₙ ∈ F₁
    |R    Q   |R
    y  ⇝[w'] y'
  -}
  lemma-for-soundness (suc n) rec (.(headF xs) , y) [x,y]∈R w w∈L*[x]@(xs , ≡refl , trw , last[xs]∈F₁)
    -- use Step condition
    with Rstep (headF xs) y [x,y]∈R n xs w ≡refl trw last[xs]∈F₁
  lemma-for-soundness (suc n) rec (.(headF xs) , y) [x,y]∈R w w∈L*[x]@(xs , ≡refl , trw , last[xs]∈F₁)
    | k , k≢0 , sk≤ssn@(s≤s k≤sn) , inj m w' , .(ys (fromℕ m)) , [w₁,w']∈Q , (ys , ≡refl , trw' , ≡refl) , [xs[k],y']∈R∨[k≡n∧y'∈F₂]
    with w₁w₂≡w w k≤sn | k≢0→k<sn→sk'≡k k≢0 (s≤s k≤sn)
  lemma-for-soundness (suc n) rec (.(headF xs) , .(ys zeroF)) [x,y]∈R w (xs , ≡refl , trw , last[xs]∈F₁)
    | k@.(suc k') , k≢0 , s≤s k≤sn , inj m w' , .(ys (fromℕ m)) , [w₁,w']∈Q , (ys , ≡refl , trw' , ≡refl) , [xs[k],y']∈R∨[k≡n∧y'∈F₂]
    | proof-of-w₁w₂≡w | k' , ≡refl
    -- split w into w₁ and w₂ at index k
    with n-k k≤sn | split w k≤sn | w₂i≡w[k+i] {A} {_} {k} w k≤sn | w₁i≡wi w k≤sn | s≤s k≤sn
  lemma-for-soundness (suc n) rec (.(headF xs) , .(ys zeroF)) [x,y]∈R w (xs , ≡refl , trw , last[xs]∈F₁)
    | k@.(suc k') , k≢0 , (s≤s k≤sn) , inj m w' , .(ys (fromℕ m)) , [w₁,w']∈Q , (ys , ≡refl , trw' , ≡refl) , [xs[k],y']∈R∨[k≡n∧y'∈F₂]
    | proof-of-w₁w₂≡w | k' , ≡refl
    | l , k+l≡sn@≡refl | w₁ , w₂ | w₂i≡ | w₁i≡ | sk≤ssn
    -- split xs into xs₁ and xs₂^ at index k
    with n-k sk≤ssn | split xs sk≤ssn | w₂i≡w[k+i] {X₁} {_} {suc k} xs sk≤ssn | w₁i≡wi xs sk≤ssn
  lemma-for-soundness (suc n) rec (.(headF xs) , .(ys zeroF)) [x,y]∈R w (xs , ≡refl , trw , last[xs]∈F₁)
    | k@.(suc k') , k≢0 , (s≤s k≤sn) , inj m w' , .(ys (fromℕ m)) , [w₁,w']∈Q , (ys , ≡refl , trw' , ≡refl) , [xs[k],y']∈R∨[k≡n∧y'∈F₂]
    | proof-of-w₁w₂≡w | k' , ≡refl
    | l , k+l≡sn@≡refl | w₁ , w₂ | w₂i≡ | w₁i≡ | sk≤ssn
    | l' , ss[k+l']≡ss[k'+l] | xs₁ , xs₂^ | xs₂i≡ | xs₁i≡
    -- we have l ≡ l'
    with ss[k'+l']≡ss[k'+l]→l'≡l {k'} {l'} {l} ss[k+l']≡ss[k'+l]
  lemma-for-soundness (suc n@.(k' + l)) rec (.(headF xs) , y@.(ys zeroF)) [x,y]∈R w (xs , ≡refl , trw , last[xs]∈F₁)
    | k@.(suc k') , k≢0 , (s≤s k≤sn) , inj m w' , .(ys (fromℕ m)) , [w₁,w']∈Q , (ys , ≡refl , trw' , ≡refl) , [xs[k],y']∈R∨[k≡n∧y'∈F₂]
    | proof-of-w₁w₂≡w | k' , ≡refl
    | l , ≡refl | w₁ , w₂ | w₂i≡ | w₁i≡ | sk≤ssn
    | .l , s[k+l]≡ss[k'+l] | xs₁ , xs₂^ | xs₂i≡ | xs₁i≡
    | l'≡l@≡refl
    -- case analysis
    with [xs[k],y']∈R∨[k≡n∧y'∈F₂]
  
  -- Case: k ≡ n and y' ∈ F₂
  lemma-for-soundness (suc n@.(k' + l)) rec (.(headF xs) , y@.(ys zeroF)) [x,y]∈R w (xs , ≡refl , trw , last[xs]∈F₁)
    | k@.(suc k') , k≢0 , (s≤s k≤sn) , inj m w' , .(ys (fromℕ m)) , [w₁,w']∈Q , (ys , ≡refl , trw' , ≡refl) , [xs[k],y']∈R∨[k≡n∧y'∈F₂]
    | proof-of-w₁w₂≡w | k' , ≡refl
    | l , ≡refl | w₁ , w₂ | w₂i≡ | w₁i≡ | sk≤ssn
    | .l , s[k+l]≡ss[k'+l] | xs₁ , xs₂^ | xs₂i≡ | xs₁i≡
    | ≡refl
    | inj₂ (sk'≡sk'+l , y'∈F₂)
    -- we have l ≡ 0
    with a≡a+b→b≡0 sk'≡sk'+l
  lemma-for-soundness (suc .(k' + 0)) rec (.(headF xs) , .(ys zeroF)) [x,y]∈R w (xs , ≡refl , trw , last[xs]∈F₁)
    | .(suc k') , k≢0 , s≤s k≤sn , inj m w' , .(ys (fromℕ m)) , [w₁,w']∈Q , (ys , ≡refl , trw' , ≡refl) , [xs[k],y']∈R∨[k≡n∧y'∈F₂]
    | proof-of-w₁w₂≡w | k' , ≡refl
    | .0 , ≡refl | w₁ , w₂ | w₂i≡ | w₁i≡ | sk≤ssn
    | .0 , s[k+l]≡ss[k'+l] | xs₁ , xs₂^ | xs₂i≡ | xs₁i≡
    | ≡refl
    | inj₂ (sk'≡sk'+l , y'∈F₂)
    | l≡0@≡refl =
      (inj m w' , (ys , ≡refl , trw' , y'∈F₂) , [w,w']∈Q)
    where
      -- we obtain (w,w') ∈ Q from (w₁,w') ∈ Q because w ≡ w₁
      [w,w']∈Q : (inj (suc (k' + 0)) w , inj m w') ∈ ∣Q∣
      [w,w']∈Q = step-∋ ∣Q∣ [w₁,w']∈Q
        (begin
        inj (suc k') w₁ , inj m w' -- ∈ ∣Q∣
        ≡⟨ ≡cong (λ a → inj (suc k') a , inj m w') (ex (λ i → w₁i≡ i)) ⟩
        inj (suc k') (λ i → w (inject≤ i k≤sn)) , inj m w'
        ≡⟨ ≡cong (λ a → a , inj m w') (inj[n]w[inj≤i]≡inj[n+0]w w ≡refl k≤sn) ⟩
        inj (suc (k' + 0)) w , inj m w'
        ∎)
  
  -- Case: (xₖ , y') ∈ R
  {- Using induction hypothesis, we get w'₂ and y'' such that
    x₀ ⇝[w₁] xₖ ⇝[w₂] xₙ ∈ F₁
    |R    Q   |R    Q
    y  ⇝[w'] y' ⇝[w'₂] y'' ∈ F₂
  -}
  lemma-for-soundness (suc n@.(k' + l)) rec (.(headF xs) , y@.(ys zeroF)) [x,y]∈R w (xs , ≡refl , trw , last[xs]∈F₁)
    | k@.(suc k') , k≢0 , (s≤s k≤sn) , inj m w' , .(ys (fromℕ m)) , [w₁,w']∈Q , (ys , ≡refl , trw' , ≡refl) , [xs[k],y']∈R∨[k≡n∧y'∈F₂]
    | proof-of-w₁w₂≡w | k' , ≡refl
    | l , ≡refl | w₁ , w₂ | w₂i≡ | w₁i≡ | sk≤ssn
    | .l , s[k+l]≡ss[k'+l] | xs₁ , xs₂^ | xs₂i≡ | xs₁i≡
    | ≡refl
    | inj₁ [xs[k],y']∈R =
      ( inj (m + proj₁ construction) (proj₁ (proj₂ construction)) , proj₂ (proj₂ construction) )
    where
      -- xs₂ is xsₖ ⋯ xsₙ, whose length is 1+l
      xs₂ : FinWord (suc l) X₁
      xs₂ = (xs₁ (fromℕ k)) ∷ᶠ xs₂^
  
      xs₂0≡xs[k] : xs₂ zeroF ≡ xs (sucF (fromℕ< k≤sn))
      xs₂0≡xs[k] = begin
        xs₁ (fromℕ k)
        ≡⟨ xs₁i≡ (fromℕ k) ⟩
        xs (inject≤ (fromℕ k) sk≤ssn)
        ≡⟨ ≡cong xs (lemma sk≤ssn k≤sn) ⟩
        xs (sucF (fromℕ< k≤sn))
        ∎
        where
          lemma : {a b : ℕ}
            → (ssa≤sb : suc (suc a) ≤ suc b)
            → (sa≤b : suc a ≤ b)
            → inject≤ (fromℕ (suc a)) ssa≤sb ≡ sucF (fromℕ< sa≤b)
          lemma {zero} {suc b} p q = ≡refl
          lemma {suc a} {.(suc _)} (s≤s p) (s≤s q) = ≡cong sucF (lemma {a} p q)
  
      [xs₂0,y']∈R : (xs₂ zeroF , ys (fromℕ m)) ∈ ∣R∣
      [xs₂0,y']∈R =
        step-∋ ∣R∣ [xs[k],y']∈R
          (≡cong (λ x → (x , ys (fromℕ m)))
            (begin
            xs (sucF (fromℕ< k≤sn))
            ≡⟨ ≡sym xs₂0≡xs[k] ⟩
            xs₂ zeroF
            ∎)
          )
  
      toℕfromℕk+l≡sn : toℕ (fromℕ k) + l ≡ suc n
      toℕfromℕk+l≡sn = (≡cong (λ i → i + l) (toℕfromℕ≡id k))
  
      toℕfromℕk+sl≡ssn : toℕ (fromℕ k) + suc l ≡ suc (suc n)
      toℕfromℕk+sl≡ssn with toℕfromℕ≡id k
      toℕfromℕk+sl≡ssn | p = begin
        toℕ (fromℕ k) + suc l
        ≡⟨ ≡cong (λ i → i + suc l) p ⟩
        k + suc l
        ≡⟨ sk+l≡k+sl {k} {l} ⟩
        suc (suc n)
        ∎
        where
          sk+l≡k+sl : ∀ {a b : ℕ} → a + suc b ≡ suc (a + b)
          sk+l≡k+sl {zero} {b} = ≡refl
          sk+l≡k+sl {suc a} {b} = ≡cong suc (sk+l≡k+sl {a} {b})
  
      lemma[inj≤[k]≡inj₁[k+0]] : ∀ {k' l' n' : ℕ}
        → (sk'≤ssn' : suc k' ≤ suc n')
        → (p : toℕ (fromℕ k') + suc l' ≡ n')
        → inject≤ (fromℕ k') sk'≤ssn' ≡ inject₁ (cast p (fromℕ k' +F zeroF))
      lemma[inj≤[k]≡inj₁[k+0]] {zero} {n'} sk'≤ssn' ≡refl = ≡refl
      lemma[inj≤[k]≡inj₁[k+0]] {suc k'} {n'} (s≤s q) ≡refl = ≡cong sucF (lemma[inj≤[k]≡inj₁[k+0]] q ≡refl)
  
      xs₂i≡xs[k+i] : ∀ (i : Fin l) → xs₂ (inject₁ i) ≡ xs (inject₁ (cast toℕfromℕk+l≡sn (fromℕ k +F i)))
      xs₂i≡xs[k+i] zeroF = begin
        xs₂ (inject₁ zeroF)
        ≡⟨⟩
        xs₁ (fromℕ k)
        ≡⟨ xs₁i≡ (fromℕ k) ⟩
        xs (inject≤ (fromℕ k) sk≤ssn)
        ≡⟨ ≡cong xs (lemma[inj≤[k]≡inj₁[k+0]] sk≤ssn toℕfromℕk+l≡sn) ⟩
        xs (inject₁ (cast toℕfromℕk+l≡sn (fromℕ k +F zeroF)))
        ∎
          
      xs₂i≡xs[k+i] (sucF i) =
        begin
        xs₂ (inject₁ (sucF i))
        ≡⟨⟩
        xs₂^ (inject₁ i)
        ≡⟨ xs₂i≡ (inject₁ i) ⟩
        xs (sucF (cast ≡refl (inject+' k (inject₁ i))))
        ≡⟨ ≡cong xs (lemma {k} toℕfromℕk+l≡sn ≡refl) ⟩
        xs (inject₁ (cast toℕfromℕk+l≡sn (fromℕ k +F (sucF i))))
        ∎
        where
          claim : ∀ {k'' l'' n'' : ℕ} → {i'' : Fin (suc l'')}
            → {q' : suc k'' + suc (suc l'') ≡ suc (toℕ (fromℕ k'')) + suc (suc l'')}
            → cast q' (inject+' (suc k'') (inject₁ i'')) ≡ inject₁ (cast ≡refl (fromℕ k'' +F sucF i''))
          claim {zero} {l''} {n''} {zeroF} {≡refl} = ≡refl
          claim {zero} {suc l''} {n''} {sucF i''} {≡refl} = ≡cong sucF (claim {zero} {l''} {n''} {i''} {≡refl})
          claim {suc k''} {l''} {n''} {i''} {q'} = ≡cong sucF (claim {k''} {l''} {n''} {i''} {≡cong (λ i → i ∸ 1) q'})
  
          lemma : ∀ {k' l' n' : ℕ} → {i' : Fin l'}
            → (p : toℕ (fromℕ k') + suc l' ≡ suc n')
            → (q : k' + suc l' ≡ suc n')
            → sucF (cast q (inject+' k' (inject₁ i'))) ≡ inject₁ (cast p (fromℕ k' +F sucF i'))
          lemma {zero} {suc l'} {.(suc l')} {zeroF} ≡refl ≡refl = ≡refl
          lemma {zero} {suc l'} {.(suc l')} {sucF i'} ≡refl ≡refl = ≡cong sucF (lemma {zero} {l'} {_} {i'} ≡refl ≡refl)
          lemma {suc k'} {sl'@.(suc _)} {.(toℕ (fromℕ k') + suc (suc _))} {zeroF} p@≡refl q =
            begin
            sucF (cast q (inject+' (suc k') (inject₁ zeroF)))
            ≡⟨ ≡cong sucF (claim {k'} {pred sl'} {toℕ (fromℕ k') + suc sl'} {zeroF} {q}) ⟩
            sucF (inject₁ (cast ≡refl (fromℕ k' +F sucF zeroF)))
            ≡⟨⟩
            inject₁ (cast ≡refl (fromℕ (suc k') +F sucF zeroF))
            ∎
          lemma {suc k'} {sl'@.(suc _)} {.(toℕ (fromℕ k') + suc (suc _))} {sucF i'} ≡refl q =
            ≡cong sucF (claim {k'} {pred sl'} {toℕ (fromℕ k') + suc sl'} {sucF i'} {q})
  
      lemma[cast[k+i]≡cast[k+i]] : ∀ {a b c : ℕ}
        → (j : Fin b)
        → (p : a + b ≡ c)
        → (q : toℕ (fromℕ a) + b ≡ c)
        → cast p (inject+' a j) ≡ cast q (fromℕ a +F j)
      lemma[cast[k+i]≡cast[k+i]] {zero} {.c} {c} i' ≡refl ≡refl = ≡refl
      lemma[cast[k+i]≡cast[k+i]] {suc a} {suc b} {.(suc a + suc b)} j ≡refl q = ≡cong sucF (lemma[cast[k+i]≡cast[k+i]] {a} j ≡refl (≡cong (λ i → i ∸ 1) q))
  
      xs₂^i≡xs[k+i] : ∀ (i : Fin l) → xs₂^ i ≡ xs (sucF (cast toℕfromℕk+l≡sn (fromℕ k +F i)))
      xs₂^i≡xs[k+i] i = begin
        xs₂^ i
        ≡⟨ xs₂i≡ i ⟩
        xs (sucF (cast ≡refl (inject+' k i)))
        ≡⟨ ≡cong (tailF xs) (lemma[cast[k+i]≡cast[k+i]] i ≡refl toℕfromℕk+l≡sn) ⟩
        xs (sucF (cast toℕfromℕk+l≡sn (fromℕ k +F i)))
        ∎
  
      w₂i≡w[k+i]' : ∀ (i : Fin l) →  w₂ i ≡ w (cast toℕfromℕk+l≡sn (fromℕ k +F i))
      w₂i≡w[k+i]' i = begin
        w₂ i
        ≡⟨ w₂i≡ i ⟩
        w (cast ≡refl (inject+' k i))
        ≡⟨ ≡cong (λ i → w i) (lemma[cast[k+i]≡cast[k+i]] i ≡refl toℕfromℕk+l≡sn) ⟩
        w (cast toℕfromℕk+l≡sn (fromℕ k +F i))
        ∎
  
      trw₂ : ∀ (i : Fin l) → NA.trans na₁ (xs₂ (inject₁ i) , w₂ i , xs₂ (sucF i))
      trw₂ i with toℕfromℕ≡id k
      trw₂ i | p = step-∋ (NA.trans na₁) trw[k+i]
        (≡sym (begin
        xs₂ (inject₁ i) ,  w₂ i , xs₂^ i          
        ≡⟨ ≡cong (λ a → a , w₂ i , xs₂^ i) (xs₂i≡xs[k+i] i) ⟩
        xs (inject₁ (cast toℕfromℕk+l≡sn (fromℕ k +F i))) , w₂ i , xs₂^ i
        ≡⟨ ≡cong (λ a → xs (inject₁ (cast toℕfromℕk+l≡sn (fromℕ k +F i))) , w₂ i , a) (xs₂^i≡xs[k+i] i) ⟩
        xs (inject₁ (cast toℕfromℕk+l≡sn (fromℕ k +F i))) , w₂ i , xs (sucF (cast toℕfromℕk+l≡sn (fromℕ k +F i)))
        ≡⟨ ≡cong (λ a → xs (inject₁ (cast toℕfromℕk+l≡sn (fromℕ k +F i))) , a , xs (sucF (cast toℕfromℕk+l≡sn (fromℕ k +F i)))) (w₂i≡w[k+i]' i) ⟩
        (xs (inject₁ (cast toℕfromℕk+l≡sn (fromℕ k +F i))) , w (cast toℕfromℕk+l≡sn (fromℕ k +F i)) , xs (sucF (cast toℕfromℕk+l≡sn (fromℕ k +F i))))
        ∎))
        where
          trw[k+i] : NA.trans na₁
                      (xs (inject₁ (cast toℕfromℕk+l≡sn (fromℕ k +F i))) ,
                      w (cast toℕfromℕk+l≡sn (fromℕ k +F i)) ,
                      xs (sucF (cast toℕfromℕk+l≡sn (fromℕ k +F i))))
          trw[k+i] = trw (cast toℕfromℕk+l≡sn (fromℕ k +F i))
  
      last[xs₂]≡last[xs] : lastF xs₂ ≡ lastF xs
      last[xs₂]≡last[xs] = begin
        xs₂ (fromℕ l)
        ≡⟨ lemma1 {fromℕ l} ⟩
        xs (cast toℕfromℕk+sl≡ssn (fromℕ (suc k') +F (fromℕ l)))
        ≡⟨ ≡cong (λ i → xs i) (lemma2 toℕfromℕk+sl≡ssn) ⟩
        xs (sucF (fromℕ (k' + l)))
        ≡⟨⟩
        xs (fromℕ (suc n))
        ∎
        where
          lemma1 : ∀ {i : Fin (suc l)} →
            xs₂ i ≡ xs (cast toℕfromℕk+sl≡ssn (fromℕ k +F i))
          lemma1 {zeroF} = begin
            xs₂ zeroF
            ≡⟨⟩
            xs₁ (fromℕ k)
            ≡⟨ xs₁i≡ (fromℕ k) ⟩
            xs (inject≤ (fromℕ k) sk≤ssn)
            ≡⟨ ≡cong xs (claim sk≤ssn toℕfromℕk+sl≡ssn) ⟩
            xs (cast toℕfromℕk+sl≡ssn (fromℕ k +F zeroF))
            ∎
            where
              claim : ∀ {a b c : ℕ}
                → (sa≤b : suc a ≤ b)
                → (p : toℕ (fromℕ a) + suc c ≡ b)
                → inject≤ (fromℕ a) sa≤b ≡ cast p (fromℕ a +F zeroF)
              claim {zero} {.(toℕ (fromℕ zero) + suc c)} {c} sa≤b ≡refl = ≡refl
              claim {suc a} {.(toℕ (fromℕ (suc a)) + suc c)} {c} (s≤s sa≤a+sc) ≡refl = ≡cong sucF (claim {a} {_} {c} sa≤a+sc ≡refl)
          lemma1 {sucF i} = begin
            xs₂ (sucF i)
            ≡⟨⟩
            xs₂^ i
            ≡⟨ xs₂^i≡xs[k+i] i ⟩
            xs (sucF (cast toℕfromℕk+l≡sn (fromℕ (suc k') +F i)))
            ≡⟨ ≡cong xs (claim {suc k'} {l} toℕfromℕk+l≡sn toℕfromℕk+sl≡ssn) ⟩
            xs (cast toℕfromℕk+sl≡ssn (fromℕ (suc k') +F (sucF i)))
            ∎
            where
              claim : ∀ {a b c : ℕ} → {j : Fin b }
                → (p : toℕ (fromℕ a) + b ≡ c)
                → (q : toℕ (fromℕ a) + suc b ≡ suc c)
                → sucF (cast p (fromℕ a +F j)) ≡ cast q (fromℕ a +F sucF j)
              claim {zero} {b} {.(toℕ (fromℕ zero) + b)} {j} ≡refl ≡refl = ≡refl
              claim {suc a} {b} {.(toℕ (fromℕ (suc a)) + b)} {j} ≡refl q =
                ≡cong sucF (claim {a} {b} {_} {j} ≡refl (≡cong (λ i → i ∸ 1) q) )
  
          lemma2 : ∀ {k'' l'' : ℕ}
            → (p : toℕ (fromℕ (suc k'')) + suc l'' ≡ suc (suc k'' + l''))
            → cast p (fromℕ (suc k'') +F fromℕ l'') ≡ sucF (fromℕ (k'' + l''))
          lemma2 {zero} {zero} ≡refl = ≡refl
          lemma2 {zero} {suc l''} ≡refl = ≡cong (λ i → sucF (sucF i)) (claim {l''} {≡refl})
            where
              claim : ∀ {a : ℕ} → {p : suc a ≡ suc a} → cast p (fromℕ a) ≡ fromℕ a
              claim {zero} {≡refl} = ≡refl
              claim {suc a} {≡refl} = ≡cong sucF (claim {a} {≡refl})
          lemma2 {suc k''} {l''} p = ≡cong sucF (lemma2 {k''} {l''} (≡cong (λ i → i ∸ 1) p))
  
      last[xs₂]∈F₁ : NA.accept na₁ (lastF xs₂)
      last[xs₂]∈F₁ = step-∋ (NA.accept na₁) last[xs]∈F₁ (≡sym last[xs₂]≡last[xs])
  
      w₂∈L[xs₂0] : inj l w₂ ∈ FINAccLang na₁ (xs₂ zeroF)
      w₂∈L[xs₂0] = (xs₂ , ≡refl , trw₂ , last[xs₂]∈F₁)
  
      -- use induction hypothesis
      -- use well-foundedness of natural numbers. see: https://stackoverflow.com/questions/19642921/assisting-agdas-termination-checker
      IH = rec l (sl≤sn k≢0 ≡refl) (xs₂ zeroF , ys (fromℕ m)) [xs₂0,y']∈R w₂ w₂∈L[xs₂0]
        where
          l≤k+l : ∀ {l' k' : ℕ} → l' ≤ k' + l'
          l≤k+l {zero} {k'} = z≤n
          l≤k+l {suc l'} {k'} with ≡sym (+-suc k' l')
          l≤k+l {suc l'} {k'} | p = step-∋ (λ i → suc l' ≤ i) (s≤s (l≤k+l {l'})) p
  
          sl≤sn : ∀ {k' l' n' : ℕ} → k' ≢ zero → k' + l' ≡ suc n' → suc l' ≤ suc n'
          sl≤sn {zero} {l'} {n'} kz p = contradiction ≡refl kz
          sl≤sn {suc k'} {l'} {.(k' + l')} kz ≡refl = s≤s l≤k+l
  
      -- construct the word w'·w''.
      -- It satisfies y ⇝[w'·w''] y' and (w , w'·w'') ∈ Q
      construction :
        ∃ (λ m'
        → ∃ (λ (w'·w'' : FinWord (m + m') A)
          → (inj (m + m') w'·w'' ∈ FINAccLang na₂ y)
            × ( (inj (suc n) w , inj (m + m') w'·w'') ∈ ∣Q∣ )))
      construction with IH
      construction | inj m' w'' , (ys' , ys'0≡ys[m] , trw'' , last[ys']∈F₂) , w₂Qw'' =
        (m' , concat w' w'' , (ys·ys' , ys·ys'0≡ys0 , trw'w'' , last[ys·ys']∈F₂) , wQw'w'')
        where
          ys·ys' : Fin (suc (m + m')) → X₂
          ys·ys' = concat ys (tailF ys')
          
          ys·ys'0≡ys0 : ys·ys' zeroF ≡ ys zeroF
          ys·ys'0≡ys0 = ≡refl
  
          -- proof of y ⇝[w'·w''] y'
          trw'w'' : (i : Fin (m + m')) → NA.trans na₂ (ys·ys' (inject₁ i) , concat w' w'' i , ys·ys' (sucF i))
          trw'w'' i with lemma-for-trans-state {m} {m'} ys ys' ys'0≡ys[m] i | lemma-for-trans-word {A} {m} {m'} w' w'' i
          trw'w'' i | p | q with splitFin {m} {m'} i
          trw'w'' i | ys[i']≡ys·ys'[i] , ys[si']≡tail[ys]·ys'[i] | q | inj₁ i' =
            step-∋ (NA.trans na₂) (trw' i')
              (begin
              ys (inject₁ i') , w' i' , ys (sucF i')
              ≡⟨ ≡cong (λ a → (a , w' i' , ys (sucF i'))) ys[i']≡ys·ys'[i] ⟩
              concat ys (tailF ys') (inject₁ i) , w' i' , ys (sucF i')
              ≡⟨ ≡cong (λ a → (concat ys (tailF ys') (inject₁ i) , w' i' , a)) ys[si']≡tail[ys]·ys'[i] ⟩
              concat ys (tailF ys') (inject₁ i) , w' i' , concat (tailF ys) (tailF ys') i
              ≡⟨ ≡cong (λ a → (concat ys (tailF ys') (inject₁ i) , a , concat (tailF ys) (tailF ys') i)) q ⟩
              concat ys (tailF ys') (inject₁ i) , concat w' w'' i , concat (tailF ys) (tailF ys') i
              ∎)
          trw'w'' i | ys'[i'']≡ys·ys'[i] , ys'[si'']≡tail[ys]·ys'[i] | q | inj₂ i'' =
            step-∋ (NA.trans na₂) (trw'' i'')
              (begin
              ys' (inject₁ i'') , w'' i'' , ys' (sucF i'')
              ≡⟨ ≡cong (λ a → (a , w'' i'' , ys' (sucF i''))) ys'[i'']≡ys·ys'[i] ⟩
              concat ys (tailF ys') (inject₁ i) , w'' i'' , ys' (sucF i'')
              ≡⟨ ≡cong (λ a → (concat ys (tailF ys') (inject₁ i) , w'' i'' , a)) ys'[si'']≡tail[ys]·ys'[i] ⟩
              concat ys (tailF ys') (inject₁ i) , w'' i'' , concat (tailF ys) (tailF ys') i
              ≡⟨ ≡cong (λ a → (concat ys (tailF ys') (inject₁ i) , a , concat (tailF ys) (tailF ys') i)) q ⟩
              concat ys (tailF ys') (inject₁ i) , concat w' w'' i , concat (tailF ys) (tailF ys') i
              ∎)
  
          last[ys·ys']∈F₂ : NA.accept na₂ (ys·ys' (fromℕ (m + m')))
          last[ys·ys']∈F₂ = step-∋ (NA.accept na₂) last[ys']∈F₂ (last ys ys' ys'0≡ys[m])
            where
              last : {s t : ℕ} → (a : Fin (suc s) → X₂) → (b : Fin (suc t) → X₂)
                → (b0≡last[a] : b zeroF ≡ a (fromℕ s))
                → b (fromℕ t) ≡ concat a (tailF b) (fromℕ (s + t))
              last {zero} {zero} a b b0≡last[a] = b0≡last[a]
              last {zero} {suc t} a b b0≡last[a] = ≡refl
              last {suc s} {t} a b b0≡last[a] = begin
                b (fromℕ t)
                ≡⟨ last {s} {t} (tailF a) b b0≡last[a] ⟩
                concat (tailF a) (tailF b) (fromℕ (s + t))
                ≡⟨⟩
                concat a (tailF b) (fromℕ (suc s + t))
                ∎
  
          -- proof of (w , w'·w'') ∈ Q
          -- use concat-closedness of Q
          wQw'w'' : (inj (suc n) w , inj (m + m') (concat w' w'')) ∈ ∣Q∣
          wQw'w'' = step-∋ ∣Q∣ (Q-is-closed-under-concat (inj k w₁ , inj m w') [w₁,w']∈Q (inj l w₂ , inj m' w'') w₂Qw'')
            (begin
            inj (k + l) (concat w₁ w₂) , inj (m + m') (concat w' w'')
            ≡⟨ ≡cong (λ v → (inj (suc k' + l) v , inj (m + m') (concat w' w''))) proof-of-w₁w₂≡w ⟩
            inj (suc n) w , inj (m + m') (concat w' w'')
            ∎)
  
  -- Theorem[soundness] If R is Q-constrained-simulation and (x, y) ∈ R then x ≤Q y
  soundness : ∀ ((x , y) : X₁ × X₂) → (x , y) ∈ ∣R∣ → x ≤[ na₁ , na₂ , Q ] y
  soundness [x,y] [x,y]∈R (inj l w) w∈L*[x] = soundness' l [x,y] [x,y]∈R w w∈L*[x]
    where
      soundness' :
        ∀ (l : ℕ) →
        ∀ ((x , y) : X₁ × X₂) → (x , y) ∈ ∣R∣ 
        → ∀ (w : FinWord l A)
        → (inj l w ∈ FINAccLang na₁ x)
        → ∃ (λ (w' : FINWord A)
          → (w' ∈ FINAccLang na₂ y) × (Preorder.carrier Q (inj l w , w')))
      soundness' l  = <-rec (λ l → _) lemma-for-soundness l

open Soundness using (soundness) public
