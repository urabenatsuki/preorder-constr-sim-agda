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
open import Data.Fin.Properties
  using (toℕ-fromℕ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; inspect; [_])
  renaming (refl to ≡refl; sym to ≡sym; cong to ≡cong)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Relation.Unary using (_∈_; _⊆_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary.Negation using (contradiction)

open import Base
open import FinForWord
open import Word
open import QSimulation.Base
open QSimulation.Base.ConditionOnQ A
open QSimulation.Base.QSimulationBase A X₁ X₂ na₁ na₂
open import QSimulation.Lemma
open import QSimulation.Bounded A X₁ X₂ na₁ na₂
  using (Mbounded⇒unbounded)

module Soundness
  (Q@(aPreorder ∣Q∣ Qrefl Qtrans) : Preorder)
  (Q-is-closed-under-concat : [ Q ]-is-closed-under-concat)
  (R@(aConstrainedSimulation ∣R∣ Rfinal Rstep) : [ Q ]-constrained-simulation)
  where

  lemma-for-soundness :
    (l : ℕ)
    → (∀ (l' : ℕ) → (l' < l)
      → ((x , y) : X₁ × X₂)
      → (x , y) ∈ ∣R∣
      → (w : FinWord l' A)
      → (inj l' w ∈ FINAccLang na₁ x)
      → ∃[ w' ] -- : FINWord A
        (w' ∈ FINAccLang na₂ y) × (Preorder.carrier Q (inj l' w , w')))
    → ((x , y) : X₁ × X₂)
    → (x , y) ∈ ∣R∣
    → (w : FinWord l A)
    → (inj l w ∈ FINAccLang na₁ x)
    → ∃[ w' ] -- : FINWord A
      (w' ∈ FINAccLang na₂ y) × (Preorder.carrier Q (inj l w , w'))
  -- proof by induction on length of word w such as x⇝[w]x'
  -- Base case
  lemma-for-soundness zero _ (.(headF xs) , y) [x,y]∈R w w∈L*[x]@(xs , ≡refl , trw , last[xs]∈F₁) with Rfinal (headF xs) y [x,y]∈R last[xs]∈F₁ | 0-length-word≡ε w
  lemma-for-soundness zero rec (.(headF xs) , y) [x,y]∈R w w∈L*[x]@(xs , ≡refl , trw , last[xs]∈F₁) | w'@(n , as) , y' , y⇝[w']y'@(ys , ≡refl , tr₂ , ≡refl) , y'∈F₂ , ε∣Q∣w' | ≡refl  =
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
    | k , k≢0 , sk≤ssn@(s≤s k≤sn) , (m , w') , .(ys (fromℕ m)) , [w₁,w']∈Q , (ys , ≡refl , trw' , ≡refl) , [xs[k],y']∈R∨[k≡n∧y'∈F₂]
    with w₁w₂≡w w k≤sn | k≢0→k<sn→sk'≡k k≢0 (s≤s k≤sn)
  lemma-for-soundness (suc n) rec (.(headF xs) , .(ys zeroF)) [x,y]∈R w (xs , ≡refl , trw , last[xs]∈F₁)
    | k@.(suc k') , k≢0 , s≤s k≤sn , (m , w') , .(ys (fromℕ m)) , [w₁,w']∈Q , (ys , ≡refl , trw' , ≡refl) , [xs[k],y']∈R∨[k≡n∧y'∈F₂]
    | proof-of-w₁w₂≡w | k' , ≡refl
    -- split w into w₁ and w₂ at index k
    with n-k k≤sn | split w k≤sn | w₂i≡w[k+i] {A} {_} {k} w k≤sn | w₁i≡wi w k≤sn | s≤s k≤sn
  lemma-for-soundness (suc n) rec (.(headF xs) , .(ys zeroF)) [x,y]∈R w (xs , ≡refl , trw , last[xs]∈F₁)
    | k@.(suc k') , k≢0 , (s≤s k≤sn) , (m , w') , .(ys (fromℕ m)) , [w₁,w']∈Q , (ys , ≡refl , trw' , ≡refl) , [xs[k],y']∈R∨[k≡n∧y'∈F₂]
    | proof-of-w₁w₂≡w | k' , ≡refl
    | l , k+l≡sn@≡refl | w₁ , w₂ | w₂i≡ | w₁i≡ | sk≤ssn
    -- split xs into xs₁ and xs₂^ at index k
    with n-k sk≤ssn | split xs sk≤ssn | w₂i≡w[k+i] {X₁} {_} {suc k} xs sk≤ssn | w₁i≡wi xs sk≤ssn
  lemma-for-soundness (suc n) rec (.(headF xs) , .(ys zeroF)) [x,y]∈R w (xs , ≡refl , trw , last[xs]∈F₁)
    | k@.(suc k') , k≢0 , (s≤s k≤sn) , (m , w') , .(ys (fromℕ m)) , [w₁,w']∈Q , (ys , ≡refl , trw' , ≡refl) , [xs[k],y']∈R∨[k≡n∧y'∈F₂]
    | proof-of-w₁w₂≡w | k' , ≡refl
    | l , k+l≡sn@≡refl | w₁ , w₂ | w₂i≡ | w₁i≡ | sk≤ssn
    | l' , ss[k+l']≡ss[k'+l] | xs₁ , xs₂^ | xs₂i≡ | xs₁i≡
    -- we have l ≡ l'
    with ss[k'+l']≡ss[k'+l]→l'≡l {k'} {l'} {l} ss[k+l']≡ss[k'+l]
  lemma-for-soundness (suc n@.(k' + l)) rec (.(headF xs) , y@.(ys zeroF)) [x,y]∈R w (xs , ≡refl , trw , last[xs]∈F₁)
    | k@.(suc k') , k≢0 , (s≤s k≤sn) , (m , w') , .(ys (fromℕ m)) , [w₁,w']∈Q , (ys , ≡refl , trw' , ≡refl) , [xs[k],y']∈R∨[k≡n∧y'∈F₂]
    | proof-of-w₁w₂≡w | k' , ≡refl
    | l , ≡refl | w₁ , w₂ | w₂i≡ | w₁i≡ | sk≤ssn
    | .l , s[k+l]≡ss[k'+l] | xs₁ , xs₂^ | xs₂i≡ | xs₁i≡
    | l'≡l@≡refl
    -- case analysis
    with [xs[k],y']∈R∨[k≡n∧y'∈F₂]
  
  -- Case: k ≡ n and y' ∈ F₂
  lemma-for-soundness (suc n@.(k' + l)) rec (.(headF xs) , y@.(ys zeroF)) [x,y]∈R w (xs , ≡refl , trw , last[xs]∈F₁)
    | k@.(suc k') , k≢0 , (s≤s k≤sn) , (m , w') , .(ys (fromℕ m)) , [w₁,w']∈Q , (ys , ≡refl , trw' , ≡refl) , [xs[k],y']∈R∨[k≡n∧y'∈F₂]
    | proof-of-w₁w₂≡w | k' , ≡refl
    | l , ≡refl | w₁ , w₂ | w₂i≡ | w₁i≡ | sk≤ssn
    | .l , s[k+l]≡ss[k'+l] | xs₁ , xs₂^ | xs₂i≡ | xs₁i≡
    | ≡refl
    | inj₂ (sk'≡sk'+l , y'∈F₂)
    -- we have l ≡ 0
    with a≡a+b→b≡0 sk'≡sk'+l
  lemma-for-soundness (suc .(k' + 0)) rec (.(headF xs) , .(ys zeroF)) [x,y]∈R w (xs , ≡refl , trw , last[xs]∈F₁)
    | .(suc k') , k≢0 , s≤s k≤sn , (m , w') , .(ys (fromℕ m)) , [w₁,w']∈Q , (ys , ≡refl , trw' , ≡refl) , [xs[k],y']∈R∨[k≡n∧y'∈F₂]
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
    | k@.(suc k') , k≢0 , (s≤s k≤sn) , (m , w') , .(ys (fromℕ m)) , [w₁,w']∈Q , (ys , ≡refl , trw' , ≡refl) , [xs[k],y']∈R∨[k≡n∧y'∈F₂]
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
        ≡⟨ ≡cong xs (inject≤[fromℕ[sa]][sa<sb]≡s[fromℕ<[a<b]] sk≤ssn k≤sn) ⟩
        xs (sucF (fromℕ< k≤sn))
        ∎
  
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
      toℕfromℕk+l≡sn = (≡cong (λ i → i + l) (toℕ-fromℕ k))
  
      toℕfromℕk+sl≡ssn : toℕ (fromℕ k) + suc l ≡ suc (suc n)
      toℕfromℕk+sl≡ssn with toℕ-fromℕ k
      toℕfromℕk+sl≡ssn | p = begin
        toℕ (fromℕ k) + suc l
        ≡⟨ ≡cong (λ i → i + suc l) p ⟩
        k + suc l
        ≡⟨ +-suc k l ⟩
        suc (suc n)
        ∎

      xs₂i≡xs[k+i] : ∀ (i : Fin l) → xs₂ (inject₁ i) ≡ xs (inject₁ (cast toℕfromℕk+l≡sn (fromℕ k +F i)))
      xs₂i≡xs[k+i] zeroF = begin
        xs₂ (inject₁ zeroF)
        ≡⟨⟩
        xs₁ (fromℕ k)
        ≡⟨ xs₁i≡ (fromℕ k) ⟩
        xs (inject≤ (fromℕ k) sk≤ssn)
        ≡⟨ ≡cong xs (inject≤[fromℕ[k]][k<ssn]≡inject₁[cast[fromℕ[k]+F0]] sk≤ssn toℕfromℕk+l≡sn) ⟩
        xs (inject₁ (cast toℕfromℕk+l≡sn (fromℕ k +F zeroF)))
        ∎
      xs₂i≡xs[k+i] (sucF i) =
        begin
        xs₂ (inject₁ (sucF i))
        ≡⟨⟩
        xs₂^ (inject₁ i)
        ≡⟨ xs₂i≡ (inject₁ i) ⟩
        xs (sucF (cast ≡refl (inject+' k (inject₁ i))))
        ≡⟨ ≡cong xs (s[k+iˡ]≡k+siˡ {k} toℕfromℕk+l≡sn ≡refl) ⟩
        xs (inject₁ (cast toℕfromℕk+l≡sn (fromℕ k +F (sucF i))))
        ∎

      xs₂^i≡xs[k+i] : ∀ (i : Fin l) → xs₂^ i ≡ xs (sucF (cast toℕfromℕk+l≡sn (fromℕ k +F i)))
      xs₂^i≡xs[k+i] i = begin
        xs₂^ i
        ≡⟨ xs₂i≡ i ⟩
        xs (sucF (cast ≡refl (inject+' k i)))
        ≡⟨ ≡cong (tailF xs) ([inject+]≡[+F] i ≡refl toℕfromℕk+l≡sn) ⟩
        xs (sucF (cast toℕfromℕk+l≡sn (fromℕ k +F i)))
        ∎
  
      w₂i≡w[k+i]' : ∀ (i : Fin l) →  w₂ i ≡ w (cast toℕfromℕk+l≡sn (fromℕ k +F i))
      w₂i≡w[k+i]' i = begin
        w₂ i
        ≡⟨ w₂i≡ i ⟩
        w (cast ≡refl (inject+' k i))
        ≡⟨ ≡cong (λ i → w i) ([inject+]≡[+F] i ≡refl toℕfromℕk+l≡sn) ⟩
        w (cast toℕfromℕk+l≡sn (fromℕ k +F i))
        ∎
  
      trw₂ : ∀ (i : Fin l) → NA.trans na₁ (xs₂ (inject₁ i) , w₂ i , xs₂ (sucF i))
      trw₂ i with toℕ-fromℕ k
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
        ≡⟨ lemma {fromℕ l} ⟩
        xs (cast toℕfromℕk+sl≡ssn (fromℕ (suc k') +F (fromℕ l)))
        ≡⟨ ≡cong (λ i → xs i) (cast[fromℕ[sk']+Ffromℕ[l]]≡s[fromℕ[k'+l]] toℕfromℕk+sl≡ssn) ⟩
        xs (sucF (fromℕ (k' + l)))
        ≡⟨⟩
        xs (fromℕ (suc n))
        ∎
        where
          lemma : ∀ {i : Fin (suc l)} →
            xs₂ i ≡ xs (cast toℕfromℕk+sl≡ssn (fromℕ k +F i))
          lemma {zeroF} = begin
            xs₂ zeroF
            ≡⟨⟩
            xs₁ (fromℕ k)
            ≡⟨ xs₁i≡ (fromℕ k) ⟩
            xs (inject≤ (fromℕ k) sk≤ssn)
            ≡⟨ ≡cong xs (inject≤[fromℕ[a]][a<b]≡cast[fromℕ[a]+F0] sk≤ssn toℕfromℕk+sl≡ssn) ⟩
            xs (cast toℕfromℕk+sl≡ssn (fromℕ k +F zeroF))
            ∎
          lemma {sucF i} = begin
            xs₂ (sucF i)
            ≡⟨⟩
            xs₂^ i
            ≡⟨ xs₂^i≡xs[k+i] i ⟩
            xs (sucF (cast toℕfromℕk+l≡sn (fromℕ (suc k') +F i)))
            ≡⟨ ≡cong xs (s[cast[fromℕ[a]+Fiᵇ]]≡cast[fromℕ[a]+Fsiᵇ] {suc k'} {l} toℕfromℕk+l≡sn toℕfromℕk+sl≡ssn) ⟩
            xs (cast toℕfromℕk+sl≡ssn (fromℕ (suc k') +F (sucF i)))
            ∎
    
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
        ∃[ m' ]
          ∃ λ (w'·w'' : FinWord (m + m') A)
          → (inj (m + m') w'·w'' ∈ FINAccLang na₂ y)
            × ( (inj (suc n) w , inj (m + m') w'·w'') ∈ ∣Q∣ )
      construction with IH
      construction | (m' , w'') , (ys' , ys'0≡ys[m] , trw'' , last[ys']∈F₂) , w₂Qw'' =
        (m' , concat w' w'' , (ys·ys' , ys·ys'0≡ys0 , trw'w'' , last[ys·ys']∈F₂) , wQw'w'')
        where
          ys·ys' : Fin (suc (m + m')) → X₂
          ys·ys' = concat ys (tailF ys')
          
          ys·ys'0≡ys0 : ys·ys' zeroF ≡ ys zeroF
          ys·ys'0≡ys0 = ≡refl
  
          -- proof of y ⇝[w'·w''] y'
          open QSimulation.Lemma.Transition X₂ A na₂ m m' ys ys' ys'0≡ys[m] w' w'' trw' trw''
          trw'w'' : (i : Fin (m + m')) → NA.trans na₂ (ys·ys' (inject₁ i) , concat w' w'' i , ys·ys' (sucF i))
          trw'w'' i = tr i
          {-
          trw'w'' i with lemma-for-trans-state {m} {m'} ys ys' ys'0≡ys[m] i | lemma-for-trans-word {m} {m'} w' w'' i
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
          -}

          last[ys·ys']∈F₂ : NA.accept na₂ (ys·ys' (fromℕ (m + m')))
          last[ys·ys']∈F₂ = step-∋ (NA.accept na₂) last[ys']∈F₂ (last-concat {X₂} ys ys' ys'0≡ys[m])
  
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
  soundness : ((x , y) : X₁ × X₂) → (x , y) ∈ ∣R∣ → x ≤[ na₁ , na₂ , Q ] y
  soundness [x,y] [x,y]∈R (l , w) w∈L*[x] = soundness' l [x,y] [x,y]∈R w w∈L*[x]
    where
      soundness' :
        (l : ℕ)
        → ((x , y) : X₁ × X₂) → (x , y) ∈ ∣R∣ 
        → (w : FinWord l A)
        → (inj l w ∈ FINAccLang na₁ x)
        → ∃[ w' ] -- : FINWord A
          (w' ∈ FINAccLang na₂ y) × (Preorder.carrier Q (inj l w , w'))
      soundness' l  = <-rec (λ l → _) lemma-for-soundness l


  -- prove soundness from up-to version
  soundness-from-upto :
    ((x , y) : X₁ × X₂) → (x , y) ∈ ∣R∣ → x ≤[ na₁ , na₂ , Q ] y
  soundness-from-upto [x,y] [x,y]∈R =
    a
    where
      -- Q₁ and Q₂ are ≡.
      Eq : Preorder {FINWord A}
      Eq = aPreorder (λ (w , u) → w ≡ u) (λ w → ≡refl)
        (λ w₁ w₂ w₃ → λ { ≡refl → λ { ≡refl → ≡refl } })

      [Q,≡,≡]-is-reasonable : [ Q , Eq , Eq ]-is-reasonable
      [Q,≡,≡]-is-reasonable =
        Q-is-closed-under-concat ,
        [w,w']∈Eq→∣w'∣≤∣w∣ ,
        Eq∘Q∘Eq⊆Q
        where
          [w,w']∈Eq→∣w'∣≤∣w∣ :
            (w w' : FINWord A) → (w , w') ∈ Preorder.carrier Eq → ∣ w' ∣ ≤ ∣ w ∣
          [w,w']∈Eq→∣w'∣≤∣w∣ (n , w) (.n , .w) ≡refl = ≤-reflexive ≡refl
          Eq∘Q∘Eq⊆Q : Preorder.carrier Eq ∘ᵣ ∣Q∣ ∘ᵣ Preorder.carrier Eq ⊆ ∣Q∣
          Eq∘Q∘Eq⊆Q (w , (w' , ≡refl , [w,w']∈Q) , ≡refl) = [w,w']∈Q

      -- R₁ and R₂ are ≡.
      R₁ : Pred' (X₁ × X₁)
      R₁ (x , x') = x ≡ x'
      [R₁]⊆[≤[≡]] : R₁ ⊆ (λ (x , x') → x ≤[ na₁ , na₁ , Eq ] x')
      [R₁]⊆[≤[≡]] ≡refl w w∈F₁[x] = (w , w∈F₁[x] , ≡refl)

      R₂ : Pred' (X₂ × X₂)
      R₂ (y , y') = y ≡ y'
      [R₂]⊆[≤[≡]] : R₂ ⊆ (λ (y , y') → y ≤[ na₂ , na₂ , Eq ] y')
      [R₂]⊆[≤[≡]] ≡refl w w∈F₂[y] = (w , w∈F₂[y] , ≡refl)

      R-as-[Q,R₁,R₂]-sim : [ Q , R₁ , R₂ ]-constrained-simulation-upto
      R-as-[Q,R₁,R₂]-sim = aConstrainedSimulationUpto ∣R∣ Rfinal Rstep-upto
        where
          Rstep-upto : (x' : X₁) (y' : X₂) →
            (x' , y') ∈ ∣R∣ → StepUpto[ Q , R₁ , R₂ ] ∣R∣ x' y'
          Rstep-upto x' y' [x',y']∈R n xs as p tr last[xs]∈F₁
            with Rstep x' y' [x',y']∈R n xs as p tr last[xs]∈F₁
          Rstep-upto x' y' [x',y']∈R n xs as p tr last[xs]∈F₁
            | k , k≢0 , k<ssn , w' , y'' , [as↾k,w']∈Q , y'⇝[w']y'' , inj₁ [last[xs],y'']∈∣R∣ =
            ( k , k≢0 , k<ssn , w' , y'' , [as↾k,w']∈Q , y'⇝[w']y''
            , inj₁ (y'' , (xs (fromℕ< k<ssn) , ≡refl , [last[xs],y'']∈∣R∣) , ≡refl))
          Rstep-upto x' y' [x',y']∈R n xs as p tr last[xs]∈F₁
            | k , k≢0 , k<ssn , w' , y'' , [as↾k,w']∈Q , y'⇝[w']y'' , inj₂ acc = 
            (k , k≢0 , k<ssn , w' , y'' , [as↾k,w']∈Q , y'⇝[w']y'' , inj₂ acc)

      open import QSimulation.SoundnessUpto X₁ X₂ A na₁ na₂
        renaming (soundness to soundness-upto)
      a = soundness-upto Q Eq Eq [Q,≡,≡]-is-reasonable
        R₁ [R₁]⊆[≤[≡]] R₂ [R₂]⊆[≤[≡]] R-as-[Q,R₁,R₂]-sim [x,y] [x,y]∈R
open Soundness using (soundness) public

soundness-of-bounded-simulation :
  (M : ℕ)
  → (0<M : zero < M)
  → (Q : Preorder)
  → (Q-is-closed-under-concat : [ Q ]-is-closed-under-concat)
  → (Mbounded-Qconstrained-simulation@(aBoundedConstrainedSimulation R FinalM StepM) : [ M ]-bounded-[ Q ]-constrained-simulation)
  → ((x , y) : X₁ × X₂) → (x , y) ∈ R → x ≤[ na₁ , na₂ , Q ] y
soundness-of-bounded-simulation M 0<M Q Q-is-closed-under-concat Mbounded-Qconstrained-simulation@(aBoundedConstrainedSimulation R FinalM StepM) (x , y) [x,y]∈R =
  soundness Q Q-is-closed-under-concat unbounded-Qconstrained-simulation (x , y) [x,y]∈R
  where
    unbounded-Qconstrained-simulation : [ Q ]-constrained-simulation
    unbounded-Qconstrained-simulation = Mbounded⇒unbounded M 0<M Q Q-is-closed-under-concat Mbounded-Qconstrained-simulation
