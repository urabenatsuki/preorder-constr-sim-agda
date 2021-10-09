open import NA.Base
module QSimulation.SoundnessUpto
  (X₁ X₂ A : Set)
  (na₁@(anNA ⇝₁ _ F₁) : NA X₁ A)
  (na₂@(anNA ⇝₂ _ F₂) : NA X₂ A)
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
open import Relation.Unary using (_∈_; _⊆_)
open import Data.Product using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Base
open import FinForWord
open import Word
open import QSimulation.Base X₁ X₂ A na₁ na₂
open import QSimulation.Lemma

module Soundness
  (Q@(aPreorder ∣Q∣ Qrefl Qtrans) : Preorder)
  (Q₁@(aPreorder ∣Q₁∣ _ _) : Preorder)
  (Q₂@(aPreorder ∣Q₂∣ _ _) : Preorder)
  (Q-is-reasonable@(Q-is-closed-under-concat , [w,w']∈Q₁→∣w'∣≤∣w∣ , Q₁QQ₂⊆Q) : [ Q , Q₁ , Q₂ ]-is-reasonable)
  (R₁ : Pred' (X₁ × X₁)) (R₁⊆[≤Q₁] : R₁ ⊆ (λ (x , x') → x ≤[ na₁ , na₁ ,  Q₁ ] x'))
  (R₂ : Pred' (X₂ × X₂)) (R₂⊆[≤Q₂] : R₂ ⊆ (λ (y , y') → y ≤[ na₂ , na₂ ,  Q₂ ] y'))
  (R@(aConstrainedSimulationUpto ∣R∣ Rfinal Rstep) : [ Q , R₁ , R₂ ]-constrained-simulation-upto)
  where

  lemma-for-soundness :
    ∀ (l : ℕ)
    → (∀ (l' : ℕ) → (l' < l)
      → ∀ ((x , y) : X₁ × X₂)
      → (x , y) ∈ ∣R∣
      → ∀ (w : FinWord l' A)
      → (inj l' w ∈ FINAccLang na₁ x)
      → ∃ (λ (w' : FINWord A)
        → (w' ∈ FINAccLang na₂ y) × ((inj l' w , w') ∈ ∣Q∣) ))
    → ∀ ((x , y) : X₁ × X₂)
    → (x , y) ∈ ∣R∣
    → ∀ (w : FinWord l A)
    → (inj l w ∈ FINAccLang na₁ x)
    → ∃ (λ (w' : FINWord A)
      → (w' ∈ FINAccLang na₂ y) × ((inj l w , w') ∈ ∣Q∣) )
  -- proof by infuction on length of word w such as x⇝[w]x'
  -- Base case
  lemma-for-soundness zero rec (.(headF xs) , y) [x,y]∈R w w∈L*[x]@(xs , ≡refl , trw , last[xs]∈F₁)
    with Rfinal (headF xs) y [x,y]∈R last[xs]∈F₁ | 0-length-word≡ε w
  lemma-for-soundness zero rec (.(headF xs) , y) [x,y]∈R w w∈L*[x]@(xs , ≡refl , trw , last[xs]∈F₁)
    | w'@(inj n as) , y' , y⇝[w']y'@(ys , ≡refl , tr₂ , ≡refl) , y'∈F₂ , ε∣Q∣w' | ≡refl  =
    (w' , (ys , ≡refl , tr₂ , y'∈F₂) , ε∣Q∣w')
  -- Step
  {- By using Step-condition, we have
    x₀ ⇝[w]  xₙ ∈ F₁
    |R    Q
    y  ⇝[w'] y' ∈ F₂
    or
    x₀ ⇝[w₁] xₖ ⇝[w₂] xₙ ∈ F₁
    |     |   |R₁
    |     |   x^
    |R    |Q  |R
    |     |   y^
    |     |   |R₂
    y  ⇝[w'] y'
  -}
  lemma-for-soundness (suc n) rec (.(headF xs) , y) [x,y]∈R w w∈L*[x]@(xs , ≡refl , trw , last[xs]∈F₁)
    -- use Step condition
    with Rstep (headF xs) y [x,y]∈R n xs w ≡refl trw last[xs]∈F₁
  lemma-for-soundness (suc n) rec (.(headF xs) , y) [x,y]∈R w w∈L*[x]@(xs , ≡refl , trw , last[xs]∈F₁)
    | k , k≢0 , sk≤ssn@(s≤s k≤sn) , inj m w' , .(ys (fromℕ m)) , [w₁,w']∈Q , (ys , ≡refl , trw' , ≡refl) , [xs[k],y']∈R₁RR₂∨[k≡n∧y'∈F₂]
    with w₁w₂≡w w k≤sn | k≢0→k<sn→sk'≡k k≢0 sk≤ssn
  lemma-for-soundness (suc n) rec (.(headF xs) , .(ys zeroF)) [x,y]∈R w (xs , ≡refl , trw , last[xs]∈F₁)
    | k@.(suc k') , k≢0 , s≤s k≤sn , inj m w' , .(ys (fromℕ m)) , [w₁,w']∈Q , (ys , ≡refl , trw' , ≡refl) , [xs[k],y']∈R₁RR₂∨[k≡n∧y'∈F₂]
    | proof-of-w₁w₂≡w | k' , ≡refl
    -- split w into w₁ and w₂ at index k
    with n-k k≤sn | split w k≤sn | w₂i≡w[k+i] {A} {_} {k} w k≤sn | w₁i≡wi w k≤sn | s≤s k≤sn
  lemma-for-soundness (suc n) rec (.(headF xs) , .(ys zeroF)) [x,y]∈R w (xs , ≡refl , trw , last[xs]∈F₁)
    | k@.(suc k') , k≢0 , (s≤s k≤sn) , inj m w' , .(ys (fromℕ m)) , [w₁,w']∈Q , (ys , ≡refl , trw' , ≡refl) , [xs[k],y']∈R₁RR₂∨[k≡n∧y'∈F₂]
    | proof-of-w₁w₂≡w | k' , ≡refl
    | l , k+l≡sn@≡refl | w₁ , w₂ | w₂i≡ | w₁i≡ | sk≤ssn
    -- split xs into xs₁ and xs₂^ at index k
    with n-k sk≤ssn | split xs sk≤ssn | w₂i≡w[k+i] {X₁} {_} {suc k} xs sk≤ssn | w₁i≡wi xs sk≤ssn
  lemma-for-soundness (suc n) rec (.(headF xs) , .(ys zeroF)) [x,y]∈R w (xs , ≡refl , trw , last[xs]∈F₁)
    | k@.(suc k') , k≢0 , (s≤s k≤sn) , inj m w' , .(ys (fromℕ m)) , [w₁,w']∈Q , (ys , ≡refl , trw' , ≡refl) , [xs[k],y']∈R₁RR₂∨[k≡n∧y'∈F₂]
    | proof-of-w₁w₂≡w | k' , ≡refl
    | l , k+l≡sn@≡refl | w₁ , w₂ | w₂i≡ | w₁i≡ | sk≤ssn
    | l' , ss[k+l']≡ss[k'+l] | xs₁ , xs₂^ | xs₂i≡ | xs₁i≡
    -- we have l ≡ l'
    with ss[k'+l']≡ss[k'+l]→l'≡l {k'} {l'} {l} ss[k+l']≡ss[k'+l]
  lemma-for-soundness (suc n@.(k' + l)) rec (.(headF xs) , y@.(ys zeroF)) [x,y]∈R w (xs , ≡refl , trw , last[xs]∈F₁)
    | k@.(suc k') , k≢0 , (s≤s k≤sn) , inj m w' , .(ys (fromℕ m)) , [w₁,w']∈Q , (ys , ≡refl , trw' , ≡refl) , [xs[k],y']∈R₁RR₂∨[k≡n∧y'∈F₂]
    | proof-of-w₁w₂≡w | k' , ≡refl
    | l , ≡refl | w₁ , w₂ | w₂i≡ | w₁i≡ | sk≤ssn
    | .l , s[k+l]≡ss[k'+l] | xs₁ , xs₂^ | xs₂i≡ | xs₁i≡
    | l'≡l@≡refl
    -- case analysis
    with [xs[k],y']∈R₁RR₂∨[k≡n∧y'∈F₂]

  -- Case: k ≡ n and y' ∈ F₂
  {-
    x₀ ⇝[w]  xₙ ∈ F₁
    |R    Q
    y  ⇝[w'] y' ∈ F₂
  -}
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

  -- Case: (xₖ , y') ∈ R₁RR₂
  {-  
    x₀ ⇝[w₁] xₖ ⇝[w₂] xₙ ∈ F₁
    |     |   |R₁⊆≤Q₁
    |     |   x^
    |R    |Q  |R
    |     |   y^
    |     |   |R₂⊆≤Q₂
    y  ⇝[w'] y'
  -}
  lemma-for-soundness (suc n@.(k' + l)) rec (.(headF xs) , .(ys zeroF)) [x,y]∈R w (xs , ≡refl , trw , last[xs]∈F₁)
    | k@.(suc k') , k≢0 , s≤s k≤sn , inj m w' , .(ys (fromℕ m)) , [w₁,w']∈Q , (ys , ≡refl , trw' , ≡refl) , [xs[k],y']∈R∨[k≡n∧y'∈F₂]
    | proof-of-w₁w₂≡w | k' , ≡refl
    | l , ≡refl | w₁ , w₂ | w₂i≡ | w₁i≡ | sk≤ssn
    | .l , s[k+l]≡ss[k'+l] | xs₁ , xs₂^ | xs₂i≡ | xs₁i≡
    | ≡refl | inj₁ (y^ , (x^ , [xₖ,x^]∈R₁ , [x^,y^]∈R) , [y^,y']∈R₂) =
      (inj (m + m') (concat w' w'') , (ys·ys' , ys·ys'0≡ys0 , trw'w'' , last[ys·ys']∈F₂) , [w,w'w'']∈Q)
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

      toℕfromℕk+l≡sn : toℕ (fromℕ k) + l ≡ suc n
      toℕfromℕk+l≡sn = (≡cong (λ i → i + l) (toℕfromℕ≡id k))
  
      toℕfromℕk+sl≡ssn : toℕ (fromℕ k) + suc l ≡ suc (suc n)
      toℕfromℕk+sl≡ssn with toℕfromℕ≡id k
      toℕfromℕk+sl≡ssn | p = begin
        toℕ (fromℕ k) + suc l
        ≡⟨ ≡cong (λ i → i + suc l) p ⟩
        k + suc l
        ≡⟨ +-suc k l ⟩
        suc (suc n)
        ∎

      xs₂^i≡xs[k+i] : ∀ (i : Fin l) → xs₂^ i ≡ xs (sucF (cast toℕfromℕk+l≡sn (fromℕ k +F i)))
      xs₂^i≡xs[k+i] i = begin
        xs₂^ i
        ≡⟨ xs₂i≡ i ⟩
        xs (sucF (cast ≡refl (inject+' k i)))
        ≡⟨ ≡cong (tailF xs) ([inject+]≡[+F] i ≡refl toℕfromℕk+l≡sn) ⟩
        xs (sucF (cast toℕfromℕk+l≡sn (fromℕ k +F i)))
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

      w₂i≡w[k+i]' : ∀ (i : Fin l) →  w₂ i ≡ w (cast toℕfromℕk+l≡sn (fromℕ k +F i))
      w₂i≡w[k+i]' i = begin
        w₂ i
        ≡⟨ w₂i≡ i ⟩
        w (cast ≡refl (inject+' k i))
        ≡⟨ ≡cong (λ i → w i) ([inject+]≡[+F] i ≡refl toℕfromℕk+l≡sn) ⟩
        w (cast toℕfromℕk+l≡sn (fromℕ k +F i))
        ∎

      trw₂ : ∀ (i : Fin l) → (xs₂ (inject₁ i) , w₂ i , xs₂ (sucF i)) ∈ ⇝₁
      trw₂ i with toℕfromℕ≡id k
      trw₂ i | p = step-∋ ⇝₁ trw[k+i]
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
          trw[k+i] : (xs (inject₁ (cast toℕfromℕk+l≡sn (fromℕ k +F i))) ,
                      w (cast toℕfromℕk+l≡sn (fromℕ k +F i)) ,
                      xs (sucF (cast toℕfromℕk+l≡sn (fromℕ k +F i)))) ∈ ⇝₁
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
            xs (sucF (cast toℕfromℕk+l≡sn (fromℕ k +F i)))
            ≡⟨ ≡cong xs (s[cast[fromℕ[a]+Fiᵇ]]≡cast[fromℕ[a]+Fsiᵇ] {k} {l} toℕfromℕk+l≡sn toℕfromℕk+sl≡ssn) ⟩
            xs (cast toℕfromℕk+sl≡ssn (fromℕ k +F (sucF i)))
            ∎
  
      last[xs₂]∈F₁ : lastF xs₂ ∈ F₁
      last[xs₂]∈F₁ = step-∋ F₁ last[xs]∈F₁ (≡sym last[xs₂]≡last[xs])
  
      w₂∈L[xs₂0] : inj l w₂ ∈ FINAccLang na₁ (xs₂ zeroF)
      w₂∈L[xs₂0] = (xs₂ , ≡refl , trw₂ , last[xs₂]∈F₁)

      w₂∈L[xₖ] : inj l w₂ ∈ FINAccLang na₁ (xs (sucF (fromℕ< k≤sn)))
      w₂∈L[xₖ] = (xs₂ , xs₂0≡xs[k] , trw₂ , last[xs₂]∈F₁)

      {-
      -- We have w₂ ∈ L*(xₖ) and (xₖ , x^) ∈ R₁ ⊆ Q₁.
        xₖ ⇝[w₂] xₙ ∈ F₁
        |R₁⊆≤Q₁
        x^
      -- Thus we obtain w^ and x♯ such that
        xₖ ⇝[w₂] xₙ ∈ F₁
        |R₁   Q₁
        x^ ⇝[w^] x♯ ∈ F₁
      -- We also have ∣w^∣ ≤ ∣w₂∣ because (Q,Q₁,Q₂) is reasonable.
      -}
      xₖ≤[Q₁]x^ : xs (sucF (fromℕ< k≤sn)) ≤[ na₁ , na₁ , Q₁ ]  x^
      xₖ≤[Q₁]x^ = R₁⊆[≤Q₁] [xₖ,x^]∈R₁

      [n^,w^,w^∈L[x^],[w₂,w^]∈Q₁,n^≤l] :
        ∃ (λ (n^ : ℕ) → ∃ (λ (w^ : FinWord n^ A)
          → (inj n^ w^ ∈ FINAccLang na₁ x^) × ((inj l w₂ , inj n^ w^) ∈ ∣Q₁∣) × (n^ ≤ l)))
      [n^,w^,w^∈L[x^],[w₂,w^]∈Q₁,n^≤l] with xₖ≤[Q₁]x^ (inj l w₂) w₂∈L[xₖ]
      [n^,w^,w^∈L[x^],[w₂,w^]∈Q₁,n^≤l] | inj n^ w^ , w^∈L[x^] , [w₂,w^]∈Q₁ =
        (n^ , w^ , w^∈L[x^] , [w₂,w^]∈Q₁ , [w,w']∈Q₁→∣w'∣≤∣w∣ (inj l w₂) (inj n^ w^) [w₂,w^]∈Q₁)

      n^ : ℕ
      n^ = proj₁ [n^,w^,w^∈L[x^],[w₂,w^]∈Q₁,n^≤l]
      w^ : FinWord n^ A
      w^ = proj₁ (proj₂ [n^,w^,w^∈L[x^],[w₂,w^]∈Q₁,n^≤l])
      w^∈L[x^] : inj n^ w^ ∈ FINAccLang na₁ x^
      w^∈L[x^] = proj₁ (proj₂ (proj₂ [n^,w^,w^∈L[x^],[w₂,w^]∈Q₁,n^≤l]))
      [w₂,w^]∈Q₁ : (inj l w₂ , inj n^ w^) ∈ ∣Q₁∣
      [w₂,w^]∈Q₁ = proj₁ (proj₂ (proj₂ (proj₂ [n^,w^,w^∈L[x^],[w₂,w^]∈Q₁,n^≤l])))
      n^≤l : n^ ≤ l
      n^≤l = proj₂ (proj₂ (proj₂ (proj₂ [n^,w^,w^∈L[x^],[w₂,w^]∈Q₁,n^≤l])))

      {-
      -- By applying the induction hypothesis to
        x^ ⇝[w^] x♯ ∈ F₁
        |R
        y^
      -- we have v^ and y♯ such that
        x^ ⇝[w^] x♯ ∈ F₁
        |R    Q
        y^ ⇝[v^] y♯ ∈ F₂
      -}
      n^≤k'+l : n^ ≤ k' + l
      n^≤k'+l = ≤-trans n^≤l (a≤b+a {l} {k'})

      [m^,v^,v^∈L[y^],[w^,v^]∈Q] : ∃ (λ (m^ : ℕ) → ∃ (λ (v^ : FinWord m^ A)
          → (inj m^ v^ ∈ FINAccLang na₂ y^) × ((inj n^ w^ , inj m^ v^) ∈ ∣Q∣)))
      [m^,v^,v^∈L[y^],[w^,v^]∈Q] with rec n^ (s≤s n^≤k'+l) (x^ , y^) [x^,y^]∈R w^ w^∈L[x^]
      [m^,v^,v^∈L[y^],[w^,v^]∈Q] | inj m^ v^ , v^∈L[y^] , [w^,v^]∈Q = (m^ , v^ , v^∈L[y^] , [w^,v^]∈Q)

      m^ : ℕ
      m^ = proj₁ [m^,v^,v^∈L[y^],[w^,v^]∈Q]
      v^ : FinWord m^ A
      v^ = proj₁ (proj₂ [m^,v^,v^∈L[y^],[w^,v^]∈Q])
      v^∈L[y^] : inj m^ v^ ∈ FINAccLang na₂ y^
      v^∈L[y^] = proj₁ (proj₂ (proj₂ [m^,v^,v^∈L[y^],[w^,v^]∈Q]))
      [w^,v^]∈Q : (inj n^ w^ , inj m^ v^) ∈ ∣Q∣
      [w^,v^]∈Q = proj₂ (proj₂ (proj₂ [m^,v^,v^∈L[y^],[w^,v^]∈Q]))

      {-
      -- Now, (y^ , y') ∈ ≤Q₂
        y^ ⇝[v^] y♯ ∈ F₂
        |R₂⊆≤Q₂
        y'
      -- We have w'' and y'' such that
        y^ ⇝[v^]  y♯ ∈ F₂
        |R₂   Q₂
        y' ⇝[w''] y'' ∈ F₂
      -}
      y^≤[Q₂]y' : y^ ≤[ na₂ , na₂ , Q₂ ] ys (fromℕ m)
      y^≤[Q₂]y' = R₂⊆[≤Q₂] [y^,y']∈R₂

      [m',w'',w''∈L[y'],[v^,w'']∈Q₂] :
        ∃ (λ (m' : ℕ) → ∃ (λ (w'' : FinWord m' A)
          → (inj m' w'' ∈ FINAccLang na₂ (ys (fromℕ m))) × ((inj m^ v^ , inj m' w'') ∈ ∣Q₂∣)))
      [m',w'',w''∈L[y'],[v^,w'']∈Q₂] with y^≤[Q₂]y' (inj m^ v^) v^∈L[y^]
      [m',w'',w''∈L[y'],[v^,w'']∈Q₂] | inj m' w'' , w''∈L[y'] , [v^,w'']∈Q₂ = (m' , w'' , w''∈L[y'] , [v^,w'']∈Q₂)

      m' : ℕ
      m' = proj₁ [m',w'',w''∈L[y'],[v^,w'']∈Q₂]
      w'' : FinWord m' A
      w'' = proj₁ (proj₂ [m',w'',w''∈L[y'],[v^,w'']∈Q₂])
      w''^∈L[y'] : inj m' w'' ∈ FINAccLang na₂ (ys (fromℕ m))
      w''^∈L[y'] = proj₁ (proj₂ (proj₂ [m',w'',w''∈L[y'],[v^,w'']∈Q₂]))
      [v^,w'']∈Q₂ : (inj m^ v^ , inj m' w'') ∈ ∣Q₂∣
      [v^,w'']∈Q₂ = proj₂ (proj₂ (proj₂ [m',w'',w''∈L[y'],[v^,w'']∈Q₂]))

      {-
      -- (w₂ , w'') ∈ Q₁QQ₂
        xₖ ⇝[w₂] xₙ ∈ F₁
        |R₁   Q₁
        x^ ⇝[w^] x♯ ∈ F₁
        |R    Q
        y^ ⇝[v^] y♯ ∈ F₂
        |R₂   Q₂
        y' ⇝[w''] y'' ∈ F₂
      -- Since (Q,Q₁,Q₂) is reasonable, we have Q₁QQ₂ ⊆ Q and then (w₂,w'') ∈ Q
        xₖ ⇝[w₂] xₙ ∈ F₁
        |R₁   |
        x^    |
        |R    |Q
        y^    |
        |R₂   |
        y' ⇝[w''] y'' ∈ F₂
      -}
      [w₂,w'']∈Q : (inj l w₂ , inj m' w'') ∈ ∣Q∣
      [w₂,w'']∈Q = Q₁QQ₂⊆Q [w₂,w'']∈Q₁QQ₂
        where
          [w₂,w'']∈Q₁QQ₂ : (inj l w₂ , inj m' w'') ∈ ∣Q₁∣ ∘ᵣ ∣Q∣ ∘ᵣ ∣Q₂∣
          [w₂,w'']∈Q₁QQ₂ = (inj m^ v^ , (inj n^ w^ , [w₂,w^]∈Q₁ , [w^,v^]∈Q) , [v^,w'']∈Q₂)

      {-
        x  ⇝[w₁] xₖ ⇝[w₂]  xₙ ∈ F₁
        |R    Q         Q
        y' ⇝[w'] y' ⇝[w''] y'' ∈ F₂
      -}
      -- proof of (w , w'·w'') ∈ Q
      -- use concat-closedness of Q
      [w,w'w'']∈Q : (inj (suc n) w , inj (m + m') (concat w' w'')) ∈ ∣Q∣
      [w,w'w'']∈Q =
        step-∋ ∣Q∣ (Q-is-closed-under-concat (inj k w₁ , inj m w') [w₁,w']∈Q (inj l w₂ , inj m' w'') [w₂,w'']∈Q)
        (begin
        inj (k + l) (concat w₁ w₂) , inj (m + m') (concat w' w'')
        ≡⟨ ≡cong (λ v → (inj (suc k' + l) v , inj (m + m') (concat w' w''))) proof-of-w₁w₂≡w ⟩
        inj (suc n) w , inj (m + m') (concat w' w'')
        ∎)

      ys' : Fin (suc m') → X₂
      ys' = proj₁ w''^∈L[y']
      ys'0≡ys[m] : ys' zeroF ≡ ys (fromℕ m)
      ys'0≡ys[m] = proj₁ (proj₂ w''^∈L[y'])
      trw'' : (i : Fin m') → (ys' (inject₁ i) ,  w'' i , ys' (sucF i)) ∈ ⇝₂
      trw'' = proj₁ (proj₂ (proj₂ w''^∈L[y']))
      last[ys']∈F₂ : ys' (fromℕ m') ∈ F₂
      last[ys']∈F₂ = proj₂ (proj₂ (proj₂ w''^∈L[y']))

      ys·ys' : Fin (suc (m + m')) → X₂
      ys·ys' = concat ys (tailF ys')
 
      ys·ys'0≡ys0 : ys·ys' zeroF ≡ ys zeroF
      ys·ys'0≡ys0 = ≡refl

      -- proof of y ⇝[w'·w''] y'
      open QSimulation.Lemma.Transition X₂ A na₂ m m' ys ys' ys'0≡ys[m] w' w'' trw' trw''
      trw'w'' : (i : Fin (m + m'))
        → (ys·ys' (inject₁ i) , concat w' w'' i , ys·ys' (sucF i)) ∈ ⇝₂
      trw'w'' i = tr i
      {-
      -- The following direct proof `trw'w''` takes too long time to be typechecked.
      -- This is because the terms and types involved the proof is bery large.
      trw'w'' : (i : Fin (m + m'))
        → (ys·ys' (inject₁ i) , concat w' w'' i , ys·ys' (sucF i)) ∈ ⇝₂
      trw'w'' i with lemma-for-trans-state {m} {m'} ys ys' ys'0≡ys[m] i | lemma-for-trans-word {m} {m'} w' w'' i
      trw'w'' i | pair-of-equation | q with splitFin {m} {m'} i
      trw'w'' i | ys[i']≡ys·ys'[i] , ys[si']≡tail[ys]·ys'[i] | q | inj₁ i' =
        step-∋ ⇝₂ (trw' i')
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
        step-∋ ⇝₂ (trw'' i'')
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


      last[ys·ys']∈F₂ : ys·ys' (fromℕ (m + m')) ∈ F₂
      last[ys·ys']∈F₂ = step-∋ F₂ last[ys']∈F₂ (last ys ys' ys'0≡ys[m])
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

  -- Theorem[soundness] If R is [Q,R₁,R₂]-constrained-simulation-upto and (x, y) ∈ R then x ≤Q y
  soundness : ∀ ((x , y) : X₁ × X₂) → (x , y) ∈ ∣R∣ → x ≤[ na₁ , na₂ , Q ] y
  soundness [x,y] [x,y]∈R (inj l w) w∈L*[x] = soundness' l [x,y] [x,y]∈R w w∈L*[x]
    where
      soundness' :
        ∀ (l : ℕ) →
        ∀ ((x , y) : X₁ × X₂) → (x , y) ∈ ∣R∣ 
        → ∀ (w : FinWord l A)
        → (inj l w ∈ FINAccLang na₁ x)
        → ∃ (λ (w' : FINWord A)
          → (w' ∈ FINAccLang na₂ y) × ((inj l w , w') ∈ ∣Q∣))
      soundness' l  = <-rec (λ l → _) lemma-for-soundness l

open Soundness using (soundness) public
