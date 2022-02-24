open import NA.Base
module QSimulation.Bounded
    (X₁ X₂ A : Set)
    (na₁@(anNA ⇝₁ _ F₁) : NA X₁ A)
    (na₂@(anNA ⇝₂ _ F₂) : NA X₂ A)
    where

open import Data.Nat
open import Data.Nat.Properties
    using (≤-trans; m≤n+m; m≤m+n; +-suc; <⇒≤)
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
    using
      ( inject≤inject₁≡inject₁inject≤
      ; inject≤[fromℕ<[a≤b]][b≤c]≡fromℕ<[a≤c]
      ; s≤s-≤
      ; casti≡i; cast-sucF; +F-sucF; cast-cast
      ; [inject+]≡[+F]
      ; cast-fromℕ-+F-inject₁
      ; fromℕ-+F-+-cast; cast-fromℕ
      ; inject≤[fromℕ<[sa≤b][b≤c]]≡inject≤[fromℕ[a]][sa≤c]
      ; cast-inject+'-cast-fromℕ
      ; inject≤[fromℕ[a]][a<b]≡cast[fromℕ[a]+F0]
      ; s[cast[fromℕ[a]+Fiᵇ]]≡cast[fromℕ[a]+Fsiᵇ]
      )

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
    (StepM : ∀ x y → (x , y) ∈ R → Step[ M ][ Q ] R x y)
    (FinalM : ∀ x y → (x , y) ∈ R → Final[ M ][ Q ] R x y)
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
    lemma n _ x y [x,y]∈R xs w ≡refl tr-xs-w last[xs]∈F₁ n<N
        -- case analysis
        with k≤n⊎n<k (suc n) M
    lemma n _ x y [x,y]∈R xs w ≡refl tr-xs-w last[xs]∈F₁ n<N
        -- base case
        | inj₁ sn≤M =
            FinalM x y [x,y]∈R n xs w ≡refl tr-xs-w last[xs]∈F₁ sn≤M
    lemma n rec x y [x,y]∈R xs w ≡refl tr-xs-w last[xs]∈F₁ n<N
        -- step case
        | inj₂ sM≤sn@(s≤s M≤n)
        -- split `xs` at `suc M`
        with n-k M≤n | split xs sM≤sn | w₁i≡wi xs sM≤sn | w₂i≡w[k+i] {X₁} {_} {suc M} xs sM≤sn
        -- split `w` at `M`
        | split w M≤n | w₁i≡wi w M≤n | w₂i≡w[k+i] {A} {_} {M} w M≤n
    lemma .(M + l) IH x y [x,y]∈R xs w ≡refl tr-xs-w last[xs]∈F₁ n<N
        | inj₂ sM≤sn@(s≤s M≤n)
        | l , ≡refl
        | xs₁ , xs₂^ | xs₁i≡xs[inject≤[i][sM≤sn]] | xs₂^i≡xs[sucF[cast[inject+'[M][i]]]]
        | w₁ , w₂ | w₁i≡w[inject≤[i][M≤n]] | w₂i≡w[sucF[cast[inject+'[M][i]]]] = construction
        -- ({!!} , y'' , {!   !} , ({!   !}  , {!   !} , {!   !} , {!   !}) ,  y''∈F₂)
        where
            [xs₁0,y]∈R : (xs₁ zeroF , y) ∈ R
            [xs₁0,y]∈R = step-∋ R [x,y]∈R (≡cong (λ a → (a , y)) (≡sym xs₁0≡xs0))
                where
                    xs₁0≡xs0 : xs₁ zeroF ≡ xs zeroF
                    xs₁0≡xs0 =
                        begin
                        xs₁ zeroF
                        ≡⟨ xs₁i≡xs[inject≤[i][sM≤sn]] zeroF ⟩
                        xs zeroF
                        ∎

            tr₁ : (i : Fin M) → (xs₁ (inject₁ i) , w₁ i , xs₁ (sucF i)) ∈ NA.trans na₁
            tr₁ i = step-∋ (NA.trans na₁) (tr-xs-w (inject≤ i M≤n))
                (begin
                xs (inject₁ (inject≤ i M≤n)) , w (inject≤ i M≤n) , xs (sucF (inject≤ i M≤n))
                ≡⟨ ≡cong (λ a → (a , _ , _)) (≡sym p) ⟩
                xs₁ (inject₁ i) , w (inject≤ i M≤n) , xs (sucF (inject≤ i M≤n))
                ≡⟨ ≡cong (λ a → (_ , _ , a)) (≡sym (xs₁i≡xs[inject≤[i][sM≤sn]] (sucF i))) ⟩
                xs₁ (inject₁ i) , w (inject≤ i M≤n) , xs₁ (sucF i)
                ≡⟨ ≡cong (λ a → (_ , a , _)) (≡sym (w₁i≡w[inject≤[i][M≤n]] i)) ⟩
                xs₁ (inject₁ i) , w₁ i , xs₁ (sucF i)
                ∎)
                where
                    p : xs₁ (inject₁ i) ≡ xs (inject₁ (inject≤ i M≤n))  
                    p =  
                        begin
                        xs₁ (inject₁ i)
                        ≡⟨ xs₁i≡xs[inject≤[i][sM≤sn]] (inject₁ i) ⟩
                        xs (inject≤ (inject₁ i) (s≤s M≤n))
                        ≡⟨ ≡cong xs (inject≤inject₁≡inject₁inject≤ M≤n) ⟩
                        xs (inject₁ (inject≤ i M≤n))
                        ∎

            stepM = StepM (xs₁ zeroF) y  [xs₁0,y]∈R xs₁ w₁ ≡refl tr₁

            k₁ : ℕ
            k₁ = proj₁ stepM

            k₁≢0 : k₁ ≢ 0
            k₁≢0 = proj₁ (proj₂ stepM)

            sk₁≤sM : suc k₁ ≤ suc M
            sk₁≤sM = proj₁ (proj₂ (proj₂ stepM))

            k₁≤M : k₁ ≤ M
            k₁≤M = ≤-pred sk₁≤sM

            sk₁≤sn  : suc k₁ ≤ suc (M + l)
            sk₁≤sn = ≤-trans sk₁≤sM sM≤sn

            k₁≤n : k₁ ≤ M + l
            k₁≤n = ≤-pred sk₁≤sn

            v₁ : FINWord A
            v₁ = proj₁ (proj₂ (proj₂ (proj₂ stepM)))

            y' : X₂
            y' = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ stepM))))

            [w₁↾≤k₁,v₁]∈Q : ((k₁ , (w₁ ↾ sk₁≤sM)) , v₁) ∈ ∣Q∣
            [w₁↾≤k₁,v₁]∈Q = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ stepM)))))

            y⇝[v₁]y' = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ stepM))))))

            [xs₁[fromℕ<[sk₁≤sM]],y']∈R : (xs₁ (fromℕ< sk₁≤sM) , y') ∈ R
            [xs₁[fromℕ<[sk₁≤sM]],y']∈R =
              proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ stepM))))))

            u₁ : FinWord k₁ A
            u₁ = proj₁ (split w k₁≤n)

            k₂ : ℕ
            k₂ = proj₁ (n-k k₁≤n)
            k₁+k₂≡n : k₁ + k₂ ≡ M + l
            k₁+k₂≡n = proj₂ (n-k k₁≤n)

            u₂ : FinWord k₂ A
            u₂ = proj₂ (split w k₁≤n)

            zs₂^ : FinWord k₂ X₁
            zs₂^ = proj₂ (split xs (s≤s k₁≤n))

            zs₂ : FinWord (suc k₂) X₁
            zs₂ zeroF = xs₁ (fromℕ< sk₁≤sM)
            zs₂ (sucF i) = zs₂^ i

            {-
            0            k₁     M         n
            |------------|------|---------|
            |              w              |
            |     w₁            |    w₂   |
            | w₁↾sk₁≤sM  |      |    w₂   |
            |     u₁     |       u₂       |
            |------------|------|---------|
            0            k₁     M         n
            -}

            w₁-u₁ : ∀ i →  (w₁ ↾ sk₁≤sM) i ≡ u₁ i
            w₁-u₁ i = begin
                (w₁ ↾ sk₁≤sM) i
                ≡⟨ ≡cong (λ a → (w₁ ↾ a) i) (≡sym (s≤s-≤ k₁≤M sk₁≤sM)) ⟩
                (w₁ ↾ (s≤s k₁≤M)) i
                ≡⟨⟩
                proj₁ (split w₁ k₁≤M) i
                ≡⟨ w₁i≡wi w₁ k₁≤M i ⟩
                w₁ (inject≤ i k₁≤M)
                ≡⟨ w₁i≡w[inject≤[i][M≤n]] (inject≤ i k₁≤M) ⟩
                w (inject≤ (inject≤ i k₁≤M) M≤n)
                ≡⟨ ≡cong w (inject≤-idempotent i k₁≤M M≤n k₁≤n) ⟩
                w (inject≤ i k₁≤n)
                ≡⟨ ≡sym (w₁i≡wi w k₁≤n i) ⟩
                u₁ i
                ∎
            
            [u₁,v₁]∈Q : ((k₁ , u₁) , v₁) ∈ ∣Q∣
            [u₁,v₁]∈Q = step-∋ ∣Q∣ [w₁↾≤k₁,v₁]∈Q 
                (begin
                (k₁ , (w₁ ↾ sk₁≤sM)) , v₁
                ≡⟨ ≡cong (λ a → (k₁ , a) , v₁) (ex w₁-u₁) ⟩
                (k₁ , u₁) , v₁
                ∎)

            k₁+sk₂≡ : toℕ (fromℕ k₁) + suc k₂ ≡ suc (M + l)
            k₁+sk₂≡ = begin
                toℕ (fromℕ k₁) + suc k₂
                ≡⟨ ≡cong (λ a → a + suc k₂) (toℕ-fromℕ k₁) ⟩
                k₁ + suc k₂
                ≡⟨ +-suc k₁ k₂ ⟩
                suc (k₁ + k₂)
                ≡⟨ ≡cong suc k₁+k₂≡n ⟩
                suc (M + l)
                ∎

            zs₂i≡ : ∀ (i : Fin (suc k₂)) → zs₂ i ≡ xs (cast k₁+sk₂≡ (fromℕ k₁ +F i))
            zs₂i≡ zeroF = begin
                zs₂ zeroF
                ≡⟨⟩
                xs₁ (fromℕ< sk₁≤sM)
                ≡⟨ xs₁i≡xs[inject≤[i][sM≤sn]] (fromℕ< sk₁≤sM)  ⟩
                xs (inject≤ (fromℕ< sk₁≤sM) (sM≤sn))
                ≡⟨ ≡cong xs (inject≤[fromℕ<[sa≤b][b≤c]]≡inject≤[fromℕ[a]][sa≤c] sk₁≤sM sM≤sn sk₁≤sn) ⟩
                xs (inject≤ (fromℕ k₁) sk₁≤sn)
                ≡⟨ ≡cong xs (inject≤[fromℕ[a]][a<b]≡cast[fromℕ[a]+F0] sk₁≤sn k₁+sk₂≡) ⟩
                xs (cast k₁+sk₂≡ (fromℕ k₁ +F zeroF))
                ∎
            zs₂i≡ (sucF i) = begin
                zs₂^ i
                ≡⟨⟩
                proj₂ (split xs (s≤s k₁≤n)) i
                ≡⟨ w₂i≡w[k+i] {X₁} {suc (M + l)} {suc k₁} xs (s≤s k₁≤n) i ⟩ 
                xs (cast (proj₂ (n-k (s≤s k₁≤n))) (inject+' (suc k₁) i))
                ≡⟨⟩
                xs (cast (≡cong suc k₁+k₂≡n) (inject+' (suc k₁) i))
                ≡⟨ ≡cong xs (cast-inject+'-cast-fromℕ k₂ k₁ (suc (M + l)) i (≡cong suc k₁+k₂≡n) k₁+sk₂≡) ⟩
                xs (cast k₁+sk₂≡ (fromℕ k₁ +F sucF i))
                ∎

            last[zs₂]∈F₁ : (zs₂ (fromℕ k₂)) ∈ NA.accept na₁
            last[zs₂]∈F₁ = step-∋ (NA.accept na₁) last[xs]∈F₁ 
                (≡sym (begin
                zs₂ (fromℕ k₂)
                ≡⟨ zs₂i≡ (fromℕ k₂) ⟩
                xs (cast k₁+sk₂≡ (fromℕ k₁ +F fromℕ k₂))
                ≡⟨ ≡cong xs (fromℕ-+F-+-cast (suc (M + l)) k₁ k₂ {k₁+sk₂≡} {≡cong suc k₁+k₂≡n}) ⟩
                xs (cast (≡cong suc k₁+k₂≡n) (fromℕ (k₁ + k₂)))
                ≡⟨ ≡cong xs (cast-fromℕ (suc (M + l)) (k₁ + k₂) (M + l) (≡cong suc k₁+k₂≡n) ≡refl k₁+k₂≡n) ⟩
                xs (cast ≡refl (fromℕ (M + l)))
                ≡⟨ ≡cong xs (casti≡i {suc (M + l)} {≡refl} (fromℕ (M + l))) ⟩
                xs (fromℕ (M + l))
                ∎))

            k₁+k₂≡ : toℕ (fromℕ k₁) + k₂ ≡ M + l
            k₁+k₂≡ = begin
                toℕ (fromℕ k₁) + k₂
                ≡⟨ ≡cong (λ i → i + k₂) (toℕ-fromℕ k₁) ⟩
                k₁ + k₂
                ≡⟨ k₁+k₂≡n ⟩
                M + l
                ∎
            
            xs-zs₂[inject₁i] : ∀ (i : Fin k₂) →  xs (inject₁ (cast k₁+k₂≡ (fromℕ k₁ +F i))) ≡ zs₂ (inject₁ i)
            xs-zs₂[inject₁i] i = ≡sym (begin
                zs₂ (inject₁ i)
                ≡⟨ zs₂i≡ (inject₁ i) ⟩
                xs (cast k₁+sk₂≡ (fromℕ k₁ +F (inject₁ i)))
                ≡⟨ ≡cong xs (cast-fromℕ-+F-inject₁ (fromℕ k₁) i k₁+sk₂≡ k₁+k₂≡) ⟩
                xs (inject₁ (cast k₁+k₂≡ (fromℕ k₁ +F i)))
                ∎)

            xs-zs₂[si] : ∀ (i : Fin k₂) → xs (sucF (cast k₁+k₂≡ (fromℕ k₁ +F i))) ≡ zs₂ (sucF i)
            xs-zs₂[si] i = ≡sym (begin
                zs₂ (sucF i)
                ≡⟨ zs₂i≡ (sucF i) ⟩ 
                xs (cast k₁+sk₂≡ (fromℕ k₁ +F (sucF i)))
                ≡⟨ ≡cong xs (≡sym (s[cast[fromℕ[a]+Fiᵇ]]≡cast[fromℕ[a]+Fsiᵇ] k₁+k₂≡ k₁+sk₂≡)) ⟩
                xs (sucF (cast k₁+k₂≡ (fromℕ k₁ +F i)))
                ∎)

            w-u₂[i] : ∀ (i : Fin k₂) → w (cast k₁+k₂≡ (fromℕ k₁ +F i)) ≡ u₂ i
            w-u₂[i] i = ≡sym (begin
                u₂ i
                ≡⟨ w₂i≡w[k+i] {A} {M + l} {k₁} w k₁≤n i  ⟩
                w (cast k₁+k₂≡n (inject+' k₁ i))
                ≡⟨ ≡cong w ([inject+]≡[+F] i k₁+k₂≡n k₁+k₂≡) ⟩
                w (cast k₁+k₂≡ (fromℕ k₁ +F i))
                ∎)

            tr-zs₂-u₂ : (i : Fin k₂) → (zs₂ (inject₁ i) , u₂ i , zs₂ (sucF i)) ∈ NA.trans na₁
            tr-zs₂-u₂ i = step-∋ (NA.trans na₁) (tr-xs-w[k₁+i])
                (begin
                xs (inject₁ (cast k₁+k₂≡ (fromℕ k₁ +F i))) , w (cast k₁+k₂≡ (fromℕ k₁ +F i)) ,  xs (sucF (cast k₁+k₂≡ (fromℕ k₁ +F i)))
                ≡⟨ ≡cong (λ a → a , w (cast k₁+k₂≡ (fromℕ k₁ +F i)) , xs (sucF (cast k₁+k₂≡ (fromℕ k₁ +F i))) ) (xs-zs₂[inject₁i] i) ⟩
                zs₂ (inject₁ i) , w (cast k₁+k₂≡ (fromℕ k₁ +F i)) , xs (sucF (cast k₁+k₂≡ (fromℕ k₁ +F i)))
                ≡⟨ ≡cong (λ a → zs₂ (inject₁ i) , w (cast k₁+k₂≡ (fromℕ k₁ +F i)) , a) (xs-zs₂[si] i) ⟩
                zs₂ (inject₁ i) , w (cast k₁+k₂≡ (fromℕ k₁ +F i)) , zs₂ (sucF i)
                ≡⟨ ≡cong (λ a → zs₂ (inject₁ i) , a , zs₂ (sucF i)) (w-u₂[i] i) ⟩
                zs₂ (inject₁ i) , u₂ i , zs₂ (sucF i)
                ∎)
                where
                    tr-xs-w[k₁+i] : NA.trans na₁
                        ( xs (inject₁ (cast k₁+k₂≡ (fromℕ k₁ +F i)))
                        , w (cast k₁+k₂≡ (fromℕ k₁ +F i))
                        , xs (sucF (cast k₁+k₂≡ (fromℕ k₁ +F i)))
                        )
                    tr-xs-w[k₁+i] = tr-xs-w (cast k₁+k₂≡ (fromℕ k₁ +F i))

            {- Use induction hypothesis IH -}
            ih : ∃[ v₂ ] {- v₂ : FINWord A -}
                ∃[ y'' ] {- y'' : X₂ -}
                ((k₂ , u₂) , v₂) ∈ ∣Q∣
                × (v₂ ∈ FINWord-from[ y' ]to[ y'' ] na₂)
                × (y'' ∈ NA.accept na₂)
            ih = IH k₂ sk₂≤n (xs₁ (fromℕ< sk₁≤sM)) y' [xs₁[fromℕ<[sk₁≤sM]],y']∈R zs₂ u₂ ≡refl tr-zs₂-u₂ last[zs₂]∈F₁ k₂<N
                where
                    sk₂≤n : suc k₂ ≤ M + l
                    sk₂≤n = a+b≡c→a≢0→sb≤c k₁ k₂ (M + l) k₁+k₂≡n k₁≢0
                        where
                            a+b≡c→a≢0→sb≤c : ∀ (a b c : ℕ) → a + b ≡ c → a ≢  zero → suc b ≤ c
                            a+b≡c→a≢0→sb≤c zero b .(zero + b) ≡refl zero≢zero with zero≢zero ≡refl
                            a+b≡c→a≢0→sb≤c zero b .(zero + b) ≡refl zero≢zero | ()
                            a+b≡c→a≢0→sb≤c (suc a) b .(suc a + b) ≡refl _ = s≤s (m≤n+m b a)

                    k₂<N : suc k₂ ≤ N
                    k₂<N = ≤-trans sk₂≤n (<⇒≤ n<N)

            construction :
                ∃[ v₁v₂ ] {- v₁v₂ : FINWord A -}
                ∃[ y'' ] {- y'' : X₂ -}
                (((M + l) , w) , v₁v₂) ∈ ∣Q∣
                × (v₁v₂ ∈ FINWord-from[ y ]to[ y'' ] na₂)
                × (y'' ∈ NA.accept na₂)
            construction with ih
            construction | v₂ , y'' , [u₂,v₂]∈Q , y'⇝[v₂]y'' , y''∈F₂
                with v₂ | y'⇝[v₂]y''
            construction | v₂ , y'' , [u₂,v₂]∈Q , y'⇝[v₂]y'' , y''∈F₂
                | l₂ , v₂' | ys₂ , ys₂0≡y' , tr-ys₂-v₂ , last[ys₂]≡y'' =
                ((l₁ + l₂ , v₁'v₂') , y'' , [w,v₁v₂]∈Q , (ys₁·ys₂ , ys₁·ys₂0≡ys0  , tr-ys₁·ys₂-v₁v₂ , last[ys₁·ys₂]≡y'') , y''∈F₂)
                where
                    l₁ = proj₁ v₁
                    v₁' = proj₂ v₁
                    
                    v₁'v₂' : FinWord (l₁ + l₂) A
                    v₁'v₂' = concat v₁' v₂'

                    ys₁ : FinWord (suc l₁) X₂
                    ys₁ = proj₁ y⇝[v₁]y'

                    last[ys₁]≡y' : ys₁ (fromℕ l₁) ≡ y'
                    last[ys₁]≡y' = proj₂ (proj₂ (proj₂ y⇝[v₁]y'))

                    ys₁·ys₂ : FinWord (suc (l₁ + l₂)) X₂
                    ys₁·ys₂ = concat ys₁ (tailF ys₂)

                    ys₁·ys₂0≡ys0 : ys₁·ys₂ zeroF ≡ y
                    ys₁·ys₂0≡ys0 = begin
                        ys₁ zeroF
                        ≡⟨ proj₁ (proj₂ y⇝[v₁]y') ⟩
                        y
                        ∎

                    ys₂0≡last[ys₁] : ys₂ zeroF ≡ ys₁ (fromℕ l₁)
                    ys₂0≡last[ys₁] = begin
                        ys₂ zeroF
                        ≡⟨ ys₂0≡y' ⟩
                        y'
                        ≡⟨ ≡sym last[ys₁]≡y' ⟩
                        ys₁ (fromℕ l₁)
                        ∎

                    last[ys₁·ys₂]≡y'' : ys₁·ys₂ (fromℕ (l₁ + l₂)) ≡ y''
                    last[ys₁·ys₂]≡y'' = begin
                        ys₁·ys₂ (fromℕ (l₁ + l₂))
                        ≡⟨ ≡sym (last-concat {X₂} {l₁} {l₂} ys₁ ys₂ ys₂0≡last[ys₁]) ⟩
                        ys₂ (fromℕ l₂)
                        ≡⟨ last[ys₂]≡y'' ⟩
                        y''
                        ∎

                    tr-ys₁-v₁ : (i : Fin l₁) → (ys₁ (inject₁ i) , v₁' i , ys₁ (sucF i)) ∈ NA.trans na₂
                    tr-ys₁-v₁ = proj₁ (proj₂ (proj₂ y⇝[v₁]y'))

                    open QSimulation.Lemma.Transition X₂ A na₂ l₁ l₂ ys₁ ys₂ ys₂0≡last[ys₁] v₁' v₂' tr-ys₁-v₁ tr-ys₂-v₂
                    tr-ys₁·ys₂-v₁v₂ : (i : Fin (l₁ + l₂)) → NA.trans na₂ (ys₁·ys₂ (inject₁ i) , concat v₁' v₂' i , ys₁·ys₂ (sucF i))
                    tr-ys₁·ys₂-v₁v₂ i = tr i

                    [w,v₁v₂]∈Q : ((M + l , w) , (l₁ + l₂ , v₁'v₂')) ∈ ∣Q∣
                    [w,v₁v₂]∈Q = step-∋ ∣Q∣
                        (Q-is-closed-under-concat ((k₁ , u₁) , (l₁ , v₁')) [u₁,v₁]∈Q ((k₂ , u₂) , (l₂ , v₂')) [u₂,v₂]∈Q)
                        (begin
                        (k₁ + k₂ , concat u₁ u₂) , (l₁ + l₂ , v₁'v₂')
                        ≡⟨ ≡cong (λ a → (k₁ + k₂ , a) , (l₁ + l₂ , v₁'v₂')) ([concat-split-w]≡w' w k₁≤n) ⟩
                        (k₁ + k₂ , λ i → w (cast k₁+k₂≡n i)) , (l₁ + l₂ , v₁'v₂')
                        ≡⟨ ≡cong (λ a → a , (l₁ + l₂ , v₁'v₂')) (≡sym (inj[m][w]≡inj[n][λi→w[cast[i]]] (M + l) (k₁ + k₂) w k₁+k₂≡n)) ⟩
                        (M + l , w) , (l₁ + l₂ , v₁'v₂')
                        ∎)

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
