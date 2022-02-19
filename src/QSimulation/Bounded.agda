open import NA.Base
module QSimulation.Bounded
    (X₁ X₂ A : Set)
    (na₁@(anNA ⇝₁ _ F₁) : NA X₁ A)
    (na₂@(anNA ⇝₂ _ F₂) : NA X₂ A)
    where

open import Data.Nat
open import Data.Nat.Properties
    using (≤-trans; m≤n+m; +-suc)
open import Data.Nat.Induction
    using (<-rec)
open import Data.Fin
    using (Fin; inject₁; inject≤; fromℕ; fromℕ<; toℕ; cast)
    renaming (zero to zeroF; suc to sucF; _+_ to _+F_)
open import Data.Fin.Properties
    using (inject≤-idempotent; toℕ-fromℕ)
open import Relation.Binary.PropositionalEquality
    using (_≡_; _≢_; inspect; [_])
    renaming (refl to ≡refl; sym to ≡sym; cong to ≡cong)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Relation.Unary using (_∈_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Base
open import FinForWord
open import Word
open import NA
open import QSimulation.Base
open QSimulation.Base.ConditionOnQ A
open QSimulation.Base.QSimulationBase A X₁ X₂ na₁ na₂
open import QSimulation.Lemma
    using (inject≤inject₁≡inject₁inject≤; inject≤[fromℕ<[a≤b]][b≤c]≡fromℕ<[a≤c]; casti≡i; cast-sucF; +F-sucF; cast-cast; inject≤[fromℕ[a]][a<b]≡cast[fromℕ[a]+F0])

M≤N⇒FinalN⇒FinalM :
    ∀ {M N : ℕ} → M ≤ N
    → (Q : Preorder)
    → (R : Pred' (X₁ × X₂)) → (x : X₁) → (y : X₂)
    → Final[ N ][ Q ] R x y
    → Final[ M ][ Q ] R x y
M≤N⇒FinalN⇒FinalM
    {M} {N} M≤N Q R .(xs zeroF) y finalN
    n xs w ≡refl tr lastx∈F₁ n<M =
    finalN n xs w ≡refl tr lastx∈F₁ (≤-trans n<M M≤N)

M≤N⇒StepM⇒StepN :
    ∀ {M N : ℕ} → M ≤ N
    → (Q : Preorder)
    → (R : Pred' (X₁ × X₂)) → (x : X₁) → (y : X₂)
    → Step[ M ][ Q ] R x y
    → Step[ N ][ Q ] R x y
M≤N⇒StepM⇒StepN {M} {N} M≤N Q R .(xs zeroF) y StepM xs w ≡refl tr
    with split w M≤N | w₁i≡wi w M≤N
M≤N⇒StepM⇒StepN {M} {N} M≤N Q R .(xs zeroF) y StepM xs w ≡refl tr
    | w↾<M , w↾≥M | w↾<Mi≡wi
    with split xs (s≤s M≤N) | w₁i≡wi xs (s≤s M≤N)
M≤N⇒StepM⇒StepN {M} {N} M≤N Q@(aPreorder ∣Q∣ _ _) R .(xs zeroF) y StepM xs w ≡refl tr
    | w↾<M , w↾≥M | w↾<Mi≡wi
    | xs↾≤M , xs↾>M | xs↾≤Mi≡xsi =
    (k , k≢0 , sk≤sN , w' , y' , [w↾sk≤sN,w']∈Q , y⇝[w']y' , [xs[fromℕ<[sk≤sN]],y']∈R )
    where
        xs0≡xs↾≤M0 : (xs zeroF) ≡ (xs↾≤M zeroF)
        xs0≡xs↾≤M0 = begin xs zeroF ≡⟨ ≡sym (xs↾≤Mi≡xsi zeroF) ⟩ xs↾≤M zeroF ∎

        tr↾≤M : (i : Fin M) → (xs↾≤M (inject₁ i) , w↾<M i , xs↾≤M (sucF i)) ∈ NA.trans na₁
        tr↾≤M i = step-∋ (NA.trans na₁) (tr (inject≤ i M≤N)) 
            (begin
                xs (inject₁ (inject≤ i M≤N)) , w (inject≤ i M≤N) , xs (sucF (inject≤ i M≤N))
                ≡⟨ ≡cong (λ a → a , w (inject≤ i M≤N) , xs (sucF (inject≤ i M≤N))) (≡sym p) ⟩
                xs↾≤M (inject₁ i) , w (inject≤ i M≤N) , xs (sucF (inject≤ i M≤N))
                ≡⟨ ≡cong (λ a → xs↾≤M (inject₁ i) , w (inject≤ i M≤N) , a) (≡sym (xs↾≤Mi≡xsi (sucF i))) ⟩
                xs↾≤M (inject₁ i) , w (inject≤ i M≤N) , xs↾≤M (sucF i)
                ≡⟨ ≡cong (λ a → xs↾≤M (inject₁ i) , a ,  xs↾≤M (sucF i)) (≡sym (w↾<Mi≡wi i)) ⟩
                xs↾≤M (inject₁ i) , w↾<M i , xs↾≤M (sucF i)
            ∎)
            where
                p : xs↾≤M (inject₁ i) ≡ xs (inject₁ (inject≤ i M≤N))
                p = begin
                    xs↾≤M (inject₁ i)
                    ≡⟨ xs↾≤Mi≡xsi (inject₁ i) ⟩
                    xs (inject≤ (inject₁ i) (s≤s M≤N))
                    ≡⟨ ≡cong xs (inject≤inject₁≡inject₁inject≤ M≤N) ⟩
                    xs (inject₁ (inject≤ i M≤N))
                    ∎

        stepM = StepM xs↾≤M w↾<M xs0≡xs↾≤M0 tr↾≤M
        k : ℕ
        k = proj₁ stepM
        k≢0 = proj₁ (proj₂ stepM)

        sk≤sM : suc k ≤ suc M
        sk≤sM = proj₁ (proj₂ (proj₂ stepM))

        sk≤sN : suc k ≤ suc N
        sk≤sN = ≤-trans sk≤sM (s≤s M≤N)

        w' : FINWord A
        w' = proj₁ (proj₂ (proj₂ (proj₂ stepM)))

        y' : X₂
        y' = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ stepM))))

        [w↾<M↾≤k,w']∈Q : ((k , (w↾<M ↾ sk≤sM)) , w') ∈ ∣Q∣
        [w↾<M↾≤k,w']∈Q = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ stepM)))))
        

        w↾<M↾≤k[i]≡w↾≤sN↾<k[i] : (i : Fin k) → (w↾<M ↾ sk≤sM) i ≡ (w ↾ sk≤sN) i
        w↾<M↾≤k[i]≡w↾≤sN↾<k[i] i = lemma M≤N sk≤sM sk≤sN w↾<M w w↾<Mi≡wi i
            where
                lemma : {n m k : ℕ} → (m≤n : m ≤ n) → (sk≤sm : suc k ≤ suc m)
                    → (sk≤sn : suc k ≤ suc n)
                    → (u' : Fin m → A) → (u : Fin n → A)
                    → ((i : Fin m) → u' i ≡ u (inject≤ i m≤n))
                    → (i : Fin k)
                    → (u' ↾ sk≤sm) i ≡ (u ↾ sk≤sn) i
                lemma {n} {m} {suc k} m≤n sk≤sm@(s≤s k≤m) sk≤sn@(s≤s k≤n) u' u p i with u' ↾ sk≤sm |  w₁i≡wi u' k≤m | u ↾ sk≤sn | w₁i≡wi u k≤n
                lemma {n} {m} {suc k} m≤n sk≤sm@(s≤s k≤m) sk≤sn@(s≤s k≤n) u' u p i | LHS | qₗ | RHS | qᵣ =
                    begin
                    LHS i
                    ≡⟨ qₗ i ⟩
                    u' (inject≤ i k≤m)
                    ≡⟨ p (inject≤ i k≤m) ⟩
                    u (inject≤ (inject≤ i k≤m) m≤n)
                    ≡⟨ ≡cong u (inject≤-idempotent i k≤m m≤n k≤n ) ⟩
                    u (inject≤ i k≤n)
                    ≡⟨ ≡sym (qᵣ i) ⟩
                    RHS i
                    ∎

        [w↾sk≤sN,w']∈Q : (( k , w ↾ sk≤sN ) , w') ∈ ∣Q∣
        [w↾sk≤sN,w']∈Q = step-∋ ∣Q∣ [w↾<M↾≤k,w']∈Q
            (begin
            ((k , w↾<M ↾ sk≤sM ) , w')
            ≡⟨ ≡cong (λ a → ((k , a), w')) (ex w↾<M↾≤k[i]≡w↾≤sN↾<k[i]) ⟩
            ((k , w ↾ sk≤sN ) , w')
            ∎)

        y⇝[w']y' = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ stepM))))))

        [xs↾≤M[fromℕ<[sk≤sM]],y']∈R : (xs↾≤M (fromℕ< sk≤sM) , y') ∈ R
        [xs↾≤M[fromℕ<[sk≤sM]],y']∈R = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ stepM))))))
        [xs[fromℕ<[sk≤sN]],y']∈R : (xs (fromℕ< sk≤sN) , y') ∈ R
        [xs[fromℕ<[sk≤sN]],y']∈R = step-∋ R [xs↾≤M[fromℕ<[sk≤sM]],y']∈R
            (≡cong (λ x → (x , y'))
                (begin
                xs↾≤M (fromℕ< sk≤sM)
                ≡⟨ xs↾≤Mi≡xsi (fromℕ< sk≤sM) ⟩
                xs (inject≤ (fromℕ< sk≤sM) (s≤s M≤N))
                ≡⟨ ≡cong xs (inject≤[fromℕ<[a≤b]][b≤c]≡fromℕ<[a≤c] sk≤sM (s≤s M≤N) sk≤sN) ⟩
                xs (fromℕ< sk≤sN)
                ∎))

module Lemma
    (M N : ℕ) (0<M : zero < M) (M≤N : M ≤ N)
    (Q@(aPreorder ∣Q∣ _ _) : Preorder)
    (Q-is-closed-under-concat : [ Q ]-is-closed-under-concat)
    (R : Pred' (X₁ × X₂))
    (stepM : ∀ x y → (x , y) ∈ R → Step[ M ][ Q ] R x y)
    (finalM : ∀ x y → (x , y) ∈ R → Final[ M ][ Q ] R x y)
    where

    k≤n⊎n<k : (k n : ℕ) → (k ≤ n) ⊎ (n < k)
    k≤n⊎n<k zero n = inj₁ z≤n
    k≤n⊎n<k (suc k) zero = inj₂ (s≤s z≤n)
    k≤n⊎n<k (suc k) (suc n) with k≤n⊎n<k k n
    k≤n⊎n<k (suc k) (suc n) | inj₁ k≤n = inj₁ (s≤s k≤n)
    k≤n⊎n<k (suc k) (suc n) | inj₂ n<k = inj₂ (s≤s n<k)

    lemma :
        (n : ℕ)
        → ( -- Induction hypothesis
            (n' : ℕ) → (n' < n)
            → (x : X₁) → (y : X₂) → (x , y) ∈ R
            → (xs : FinWord (suc n') X₁)
            → (w : FinWord n' A)
            → x ≡ xs zeroF
            → ((i : Fin n') → NA.trans na₁ ((xs (inject₁ i)) , w i , xs (sucF i)))
            → xs (fromℕ n') ∈ NA.accept na₁
            → (n' < N)
            → ∃[ w' ] -- w' : FINWord A
            ∃[ y' ] -- y' : X₂
            (inj n' w , w') ∈ ∣Q∣ × (w' ∈ FINWord-from[ y ]to[ y' ] na₂) × (y' ∈ NA.accept na₂)
            )
        → (x : X₁) → (y : X₂) → (x , y) ∈ R            
        → (xs : FinWord (suc n) X₁)
        → (w : FinWord n A)
        → x ≡ xs zeroF
        → ((i : Fin n) → NA.trans na₁ ((xs (inject₁ i)) , w i , xs (sucF i)))
        → xs (fromℕ n) ∈ NA.accept na₁
        → (n < N)
        → ∃[ w' ] -- w' : FINWord A
        ∃[ y' ] -- y' : X₂
        (inj n w , w') ∈ ∣Q∣ × (w' ∈ FINWord-from[ y ]to[ y' ] na₂) × (y' ∈ NA.accept na₂)
    lemma n _ x y [x,y]∈R xs w ≡refl tr last[xs]∈F₁ n<N
        -- case analysis
        with k≤n⊎n<k (suc n) M
    lemma n _ x y [x,y]∈R xs w ≡refl tr last[xs]∈F₁ n<N
        -- base case
        | inj₁ sn≤M =
            finalM x y [x,y]∈R n xs w ≡refl tr last[xs]∈F₁ sn≤M
    lemma n rec x y [x,y]∈R xs w ≡refl tr last[xs]∈F₁ n<N
        -- step case
        | inj₂ sM≤sn@(s≤s M≤n)
        -- split `xs` at `suc M`
        with n-k M≤n | split xs sM≤sn | w₁i≡wi xs sM≤sn | w₂i≡w[k+i] {X₁} {_} {suc M} xs sM≤sn
        -- split `w` at `M`
        | split w M≤n | w₁i≡wi w M≤n | w₂i≡w[k+i] {A} {_} {M} w M≤n
    lemma .(M + l) IH x y [x,y]∈R xs w ≡refl tr last[xs]∈F₁ n<N
        | inj₂ sM≤sn@(s≤s M≤n)
        | l , ≡refl
        | xs₁ , xs₂^ | xs₁i≡xs[inject≤[i][sM≤sN]] | xs₂^i≡xs[sucF[cast[inject+'[M][i]]]]
        | w₁ , w₂ | w₁i≡w[inject≤[i][M≤N]] | w₂i≡w[sucF[cast[inject+'[M][i]]]] = ({!   !} , {!   !} , {!   !} , {!   !} , {!   !})
        where
            xs₂ : FinWord (suc l) X₁
            xs₂ = (xs₁ (fromℕ M)) ∷ᶠ xs₂^

            toℕfromℕM+sl≡s[M+l] : toℕ (fromℕ M) + suc l ≡ suc (M + l)
            toℕfromℕM+sl≡s[M+l] = begin
                toℕ (fromℕ M) + suc l
                ≡⟨ ≡cong (λ i → i + suc l) (toℕ-fromℕ M) ⟩
                M + suc l
                ≡⟨ +-suc M l ⟩
                suc (M + l)
                ∎

            
            lem : ∀ {i : Fin (suc l)} →
                xs₂ i ≡ xs (cast toℕfromℕM+sl≡s[M+l] (fromℕ M +F i))
            lem {zeroF} = begin
                xs₂ zeroF
                ≡⟨⟩
                xs₁ (fromℕ M)
                ≡⟨ xs₁i≡xs[inject≤[i][sM≤sN]] (fromℕ M) ⟩
                xs (inject≤ (fromℕ M) sM≤sn)
                ≡⟨ ≡cong xs (inject≤[fromℕ[a]][a<b]≡cast[fromℕ[a]+F0] sM≤sn toℕfromℕM+sl≡s[M+l]) ⟩
                xs (cast toℕfromℕM+sl≡s[M+l] (fromℕ M +F zeroF))
                ∎
            lem {sucF i} = begin
                xs₂ (sucF i)
                ≡⟨⟩
                xs₂^ i
                ≡⟨ xs₂^i≡xs[sucF[cast[inject+'[M][i]]]] i ⟩
                xs (sucF (cast ≡refl (inject+' M i)))
                ≡⟨ ≡cong (λ j → xs (sucF j)) (casti≡i {M + l} {≡refl} (inject+' M i)) ⟩
                xs (sucF (inject+' M i))
                ≡⟨ ≡cong xs
                    (begin
                    sucF (inject+' M i)
                    ≡⟨ ≡cong sucF {!   !} ⟩
                    sucF (cast (≡cong (λ a → (a + l)) (toℕ-fromℕ M)) (fromℕ M +F i))
                    ≡⟨ ≡sym (cast-sucF {toℕ (fromℕ M) + l} {M + l} {(≡cong (λ a → (a + l)) (toℕ-fromℕ M))} {_} (fromℕ M +F i)) ⟩
                    cast (≡cong (λ a → suc (a + l)) (toℕ-fromℕ M)) (sucF (fromℕ M +F i))
                    ≡⟨ ≡sym (cast-cast (≡sym (+-suc (toℕ (fromℕ M)) l)) toℕfromℕM+sl≡s[M+l] (≡cong (λ a → suc (a + l)) (toℕ-fromℕ M)) (sucF (fromℕ M +F i))) ⟩
                    cast toℕfromℕM+sl≡s[M+l] (cast (≡sym (+-suc (toℕ (fromℕ M)) l)) (sucF (fromℕ M +F i)))
                    ≡⟨ ≡cong (λ i → cast toℕfromℕM+sl≡s[M+l] i) (≡sym (+F-sucF (fromℕ M) i)) ⟩
                    cast toℕfromℕM+sl≡s[M+l] (fromℕ M +F sucF i)
                    ∎)
                ⟩
                xs (cast toℕfromℕM+sl≡s[M+l] (fromℕ M +F sucF i))
                ∎

            last[xs₂]≡last[xs] : lastF xs₂ ≡ lastF xs
            last[xs₂]≡last[xs] = begin
                xs₂ (fromℕ l)
                ≡⟨ lem {fromℕ l} ⟩
                xs (cast _ (fromℕ M +F (fromℕ l)))
                ≡⟨ ≡cong xs {!   !} ⟩
                xs (fromℕ (M + l))
                ∎
            {-
                where
                    lem : ∀ {i : Fin (suc l)} →
                        xs₂ i ≡ xs (cast {!   !} (fromℕ M +F i))
                    lem {zeroF} = begin
                        xs₂ zeroF
                        ≡⟨⟩
                        xs₁ (fromℕ M)
                        ≡⟨ xs₁i≡xs[inject≤[i][sM≤sN]] (fromℕ M) ⟩
                        xs (inject≤ (fromℕ M) sM≤sn)
                        ≡⟨ {!   !} ⟩
                        {!   !}
                        ∎
                    lem {sucF i} = begin
                        xs₂ (sucF i)
                        ≡⟨⟩
                        xs₂^ i
                        ≡⟨ xs₂^i≡xs[sucF[cast[inject+'[M][i]]]] i ⟩
                        xs (sucF (cast ≡refl (inject+' M i)))
                        ≡⟨ ≡cong (λ j → xs (sucF j)) (casti≡i {M + l} {≡refl} (inject+' M i)) ⟩
                        xs (sucF (inject+' M i))
                        ≡⟨ {!   !} ⟩
                        {!   !}
                        ∎
            -}
        
            last[xs₂]∈F₁ : NA.accept na₁ (lastF xs₂)
            last[xs₂]∈F₁ = step-∋ (NA.accept na₁) last[xs]∈F₁ (≡sym last[xs₂]≡last[xs])

            ih = IH l (0<b→sa≤b+a l M 0<M) (xs₁ (fromℕ M)) {!   !} {!   !} xs₂ w₂ ≡refl {!   !} last[xs₂]∈F₁ {!   !}
                where
                    0<b→sa≤b+a : (a b : ℕ) → 0 < b → suc a ≤ b + a
                    0<b→sa≤b+a zero .(suc _) (s≤s 0<b) = s≤s z≤n
                    0<b→sa≤b+a (suc a) .(suc _) (s≤s 0<b) = s≤s (m≤n+m (suc a) _)

    finalN : ∀ x y → (x , y) ∈ R → Final[ N ][ Q ] R x y
    finalN x y [x,y]∈R n = <-rec (λ n → _) lemma n x y [x,y]∈R 

M≤N⇒StepM⇒FinalM⇒FinalN :
    ∀ {M N : ℕ} → zero < M → M ≤ N
    → (Q : Preorder)
    → (Q-is-closed-under-concat : [ Q ]-is-closed-under-concat)
    → (R : Pred' (X₁ × X₂))
    → (∀ x y → (x , y) ∈ R → Step[ M ][ Q ] R x y)
    → (∀ x y → (x , y) ∈ R → Final[ M ][ Q ] R x y)
    → (∀ x y → (x , y) ∈ R → Final[ N ][ Q ] R x y)
M≤N⇒StepM⇒FinalM⇒FinalN {M} {N} 0<M M≤N Q Q-is-closed-under-concat R x y stepM finalM =
    Lemma.finalN M N 0<M M≤N Q Q-is-closed-under-concat R x y stepM finalM
