open import NA.Base
module QSimulation.Bounded
    (A X₁ X₂ : Set)
    (na₁@(anNA ⇝₁ _ F₁) : NA X₁ A)
    (na₂@(anNA ⇝₂ _ F₂) : NA X₂ A)
    where

open import Data.Nat
open import Data.Nat.Properties
    using (≤-trans; <-trans; m≤n+m; m≤m+n; +-suc; <⇒≤; ≤-reflexive)
open import Data.Nat.Induction
    using (<-rec)
open import Data.Fin
    using (Fin; inject₁; fromℕ; toℕ; cast)
    renaming (zero to zeroF; suc to sucF; _+_ to _+F_)
open import Data.Fin.Properties
    using (toℕ-fromℕ)
open import Relation.Binary.PropositionalEquality
    using (_≡_; _≢_; inspect; [_])
    renaming (refl to ≡refl; sym to ≡sym; cong to ≡cong)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Relation.Unary using (_∈_; _⊆_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Level renaming (zero to lzero; suc to lsuc)

open import Base
open import FinForWord
open import Word
open import NA
open import QSimulation.Base
open QSimulation.Base.ConditionOnQ A
open QSimulation.Base.QSimulationBase A X₁ X₂ na₁ na₂
open import QSimulation.Lemma
    using
      ( k≤n⊎n<k
      ; inject≤inject₁≡inject₁inject≤
      ; inject≤[fromℕ<[a≤b]][b≤c]≡fromℕ<[a≤c]
      ; s≤s-≤
      ; casti≡i; cast-sucF; +F-sucF; cast-cast
      ; [inject+]≡[+F]
      ; cast-fromℕ-+F-inject₁
      ; fromℕ-+F-+-cast; cast-fromℕ
      ; inject≤[i][n≤n]≡i
      ; inject≤[fromℕ<[sa≤b][b≤c]]≡inject≤[fromℕ[a]][sa≤c]
      ; cast-inject+'-cast-fromℕ
      ; inject≤[fromℕ[a]][a<b]≡cast[fromℕ[a]+F0]
      ; s[cast[fromℕ[a]+Fiᵇ]]≡cast[fromℕ[a]+Fsiᵇ]
      )

M≤N⇒FinalN⇒FinalM :
    ∀ {M N : ℕ}
    → {M>0 : M > 0}
    → {N>0 : N > 0}
    → M ≤ N
    → (Q : Preorder)
    → {ℓ : Level}
    → (R : Pred' (X₁ × X₂) {ℓ}) → (x : X₁) → (y : X₂)
    → Final[ N ][ N>0 ][ Q ] R x y
    → Final[ M ][ M>0 ][ Q ] R x y
M≤N⇒FinalN⇒FinalM
    {M} {N} M≤N Q R .(xs zeroF) y finalN
    n xs w ≡refl tr lastx∈F₁ n<M =
    finalN n xs w ≡refl tr lastx∈F₁ (≤-trans n<M M≤N)

Final1⇒Final :
    (Q : Preorder)
    → {ℓ : Level}
    → (R : Pred' (X₁ × X₂) {ℓ}) → (x : X₁) → (y : X₂)
    → Final[ 1 ][ s≤s z≤n ][ Q ] R x y
    → Final[ Q ] R x y
Final1⇒Final Q R x y final1 x∈F₁ with final1 0 (λ {0f → x}) (λ ()) ≡refl (λ ())  x∈F₁ (s≤s z≤n)
Final1⇒Final Q R x y final1 x∈F₁ | w' , y' , εQw' , tr , y'∈F₂ =
    (w' , y' , tr , y'∈F₂ , step-∋ (Preorder.carrier Q) εQw' (
        begin
        (zero , (λ ())) , w'
        ≡⟨ ≡cong (λ w → ((zero , w) , w')) (ex λ ()) ⟩
        (zero , emptyF) , w'
        ∎
    ))

Final⇒Final1 :
    (Q : Preorder)
    → {ℓ : Level}
    → (R : Pred' (X₁ × X₂) {ℓ}) → (x : X₁) → (y : X₂)
    → Final[ Q ] R x y
    → Final[ 1 ][ s≤s z≤n ][ Q ] R x y
Final⇒Final1 Q R .(xs zeroF) y final .zero xs w ≡refl tr xs0∈F₁ (s≤s z≤n) with final xs0∈F₁
Final⇒Final1 Q R .(xs zeroF) y final .zero xs w ≡refl tr xs0∈F₁ (s≤s z≤n) | w' , y' , tr' , y'∈F₂ , εQw' =
    (w' , y' ,
        (step-∋ (Preorder.carrier Q) εQw' (
            begin
            (zero , emptyF) , w'
            ≡⟨ ≡cong (λ w → ((zero , w) , w')) (ex λ ()) ⟩
            (zero , w) , w'
            ∎)) ,
        tr' , y'∈F₂)

M≤N⇒StepM⇒StepN :
    ∀ {M N : ℕ}
    → {M>0 : M > 0}
    → {N>0 : N > 0}
    → M ≤ N
    → (Q : Preorder)
    → {ℓ : Level}
    → (R : Pred' (X₁ × X₂) {ℓ}) → (x : X₁) → (y : X₂)
    → Step[ M ][ M>0 ][ Q ] R x y
    → Step[ N ][ N>0 ][ Q ] R x y
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

{-
-------- up-to version --------
-}

M≤N⇒StepMupto⇒StepNupto :
    ∀ {M N : ℕ}
    → {M>0 : M > 0}
    → {N>0 : N > 0}
    → M ≤ N
    → (Q : Preorder)
    → {ℓ : Level}
    → (R₁ : Pred' (X₁ × X₁) {ℓ}) (R₂ : Pred' (X₂ × X₂) {ℓ})
    → (R : Pred' (X₁ × X₂) {ℓ}) → (x : X₁) → (y : X₂)
    → StepUpto[ M ][ M>0 ][ Q , R₁ , R₂ ] R x y
    → StepUpto[ N ][ N>0 ][ Q , R₁ , R₂ ] R x y
M≤N⇒StepMupto⇒StepNupto {M} {N} M≤N Q R₁ R₂ R .(xs zeroF) y StepMupto xs w ≡refl tr
    with split w M≤N | w₁i≡wi w M≤N
M≤N⇒StepMupto⇒StepNupto {M} {N} M≤N Q R₁ R₂ R .(xs zeroF) y StepMupto xs w ≡refl tr
    | w↾<M , w↾≥M | w↾<Mi≡wi
    with split xs (s≤s M≤N) | w₁i≡wi xs (s≤s M≤N)
M≤N⇒StepMupto⇒StepNupto {M} {N} M≤N Q@(aPreorder ∣Q∣ _ _) R₁ R₂ R .(xs zeroF) y StepMupto xs w ≡refl tr
    | w↾<M , w↾≥M | w↾<Mi≡wi
    | xs↾≤M , xs↾>M | xs↾≤Mi≡xsi =
    (k , k≢0 , sk≤sN , w' , y' , [w↾sk≤sN,w']∈Q , y⇝[w']y' , [xs[fromℕ<[sk≤sN]],y']∈R₁RR₂ )
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

        stepMupto = StepMupto xs↾≤M w↾<M xs0≡xs↾≤M0 tr↾≤M
        k : ℕ
        k = proj₁ stepMupto
        k≢0 = proj₁ (proj₂ stepMupto)

        sk≤sM : suc k ≤ suc M
        sk≤sM = proj₁ (proj₂ (proj₂ stepMupto))

        sk≤sN : suc k ≤ suc N
        sk≤sN = ≤-trans sk≤sM (s≤s M≤N)

        w' : FINWord A
        w' = proj₁ (proj₂ (proj₂ (proj₂ stepMupto)))

        y' : X₂
        y' = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ stepMupto))))

        [w↾<M↾≤k,w']∈Q : ((k , (w↾<M ↾ sk≤sM)) , w') ∈ ∣Q∣
        [w↾<M↾≤k,w']∈Q = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ stepMupto)))))
        

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

        y⇝[w']y' = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ stepMupto))))))

        [xs↾≤M[fromℕ<[sk≤sM]],y']∈R₁RR₂ : (xs↾≤M (fromℕ< sk≤sM) , y') ∈ (R₁ ∘ᵣ R ∘ᵣ R₂)
        [xs↾≤M[fromℕ<[sk≤sM]],y']∈R₁RR₂ = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ stepMupto))))))
        [xs[fromℕ<[sk≤sN]],y']∈R₁RR₂ : (xs (fromℕ< sk≤sN) , y') ∈ (R₁ ∘ᵣ R ∘ᵣ R₂)
        [xs[fromℕ<[sk≤sN]],y']∈R₁RR₂ =
            step-∋ (R₁ ∘ᵣ R ∘ᵣ R₂) [xs↾≤M[fromℕ<[sk≤sM]],y']∈R₁RR₂
                (≡cong (λ x → (x , y'))
                    (begin
                    xs↾≤M (fromℕ< sk≤sM)
                    ≡⟨ xs↾≤Mi≡xsi (fromℕ< sk≤sM) ⟩
                    xs (inject≤ (fromℕ< sk≤sM) (s≤s M≤N))
                    ≡⟨ ≡cong xs (inject≤[fromℕ<[a≤b]][b≤c]≡fromℕ<[a≤c] sk≤sM (s≤s M≤N) sk≤sN) ⟩
                    xs (fromℕ< sk≤sN)
                    ∎))

module LemmaUpto
    (M N : ℕ) {M>0 : M > 0} {N>0 : N > 0} (M≤N : M ≤ N)
    (Q@(aPreorder ∣Q∣ _ _) : Preorder)
    (Q₁@(aPreorder ∣Q₁∣ _ _) : Preorder)
    (Q₂@(aPreorder ∣Q₂∣ _ _) : Preorder)
    (Q-is-reasonable@(Q-is-closed-under-concat , [w,w']∈Q₁→∣w'∣≤∣w∣ , Q₁QQ₂⊆Q) : [ Q , Q₁ , Q₂ ]-is-reasonable)
    {ℓ : Level}
    (R : Pred' (X₁ × X₂) {ℓ})
    (R₁ : Pred' (X₁ × X₁) {ℓ}) (R₁⊆[≤Q₁] : R₁ ⊆ (λ (x , x') → x ≤[ na₁ , na₁ ,  Q₁ ] x'))
    (R₂ : Pred' (X₂ × X₂) {ℓ}) (R₂⊆[≤Q₂] : R₂ ⊆ (λ (y , y') → y ≤[ na₂ , na₂ ,  Q₂ ] y'))
    (StepMupto : ∀ x y → (x , y) ∈ R → StepUpto[ M ][ M>0 ][ Q , R₁ , R₂ ] R x y)
    (FinalM : ∀ x y → (x , y) ∈ R → Final[ M ][ M>0 ][ Q ] R x y)
    where

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
    lemma n IH x y [x,y]∈R xs w ≡refl tr-xs-w last[xs]∈F₁ n<N
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

            stepMupto = StepMupto (xs₁ zeroF) y  [xs₁0,y]∈R xs₁ w₁ ≡refl tr₁

            k₁ : ℕ
            k₁ = proj₁ stepMupto

            k₁≢0 : k₁ ≢ 0
            k₁≢0 = proj₁ (proj₂ stepMupto)

            sk₁≤sM : suc k₁ ≤ suc M
            sk₁≤sM = proj₁ (proj₂ (proj₂ stepMupto))

            k₁≤M : k₁ ≤ M
            k₁≤M = ≤-pred sk₁≤sM

            sk₁≤sn  : suc k₁ ≤ suc (M + l)
            sk₁≤sn = ≤-trans sk₁≤sM sM≤sn

            k₁≤n : k₁ ≤ M + l
            k₁≤n = ≤-pred sk₁≤sn

            l₁ : ℕ
            l₁ = proj₁ (proj₁ (proj₂ (proj₂ (proj₂ stepMupto))))
            v₁ : FinWord l₁ A
            v₁ = proj₂ (proj₁ (proj₂ (proj₂ (proj₂ stepMupto))))

            y' : X₂
            y' = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ stepMupto))))

            [w₁↾≤k₁,v₁]∈Q : (inj k₁ (w₁ ↾ sk₁≤sM) , inj l₁ v₁) ∈ ∣Q∣
            [w₁↾≤k₁,v₁]∈Q = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ stepMupto)))))

            y⇝[v₁]y' : v₁ ∈ FinWord-from[ y ]to[ y' ] na₂ l₁
            y⇝[v₁]y' = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ stepMupto))))))

            [xs₁[fromℕ<[sk₁≤sM]],y']∈R₁RR₂ : (xs₁ (fromℕ< sk₁≤sM) , y') ∈ (R₁ ∘ᵣ R ∘ᵣ R₂)
            [xs₁[fromℕ<[sk₁≤sM]],y']∈R₁RR₂ =
                proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ stepMupto))))))

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
            
            [u₁,v₁]∈Q : (inj k₁ u₁ , inj l₁ v₁) ∈ ∣Q∣
            [u₁,v₁]∈Q = step-∋ ∣Q∣ [w₁↾≤k₁,v₁]∈Q 
                (begin
                inj k₁ (w₁ ↾ sk₁≤sM) , inj l₁ v₁
                ≡⟨ ≡cong (λ a → (k₁ , a) , inj l₁ v₁) (ex w₁-u₁) ⟩
                inj k₁ u₁ , inj l₁ v₁
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

            head[zs₂]≡xₖ₁ : headF zs₂ ≡ xs₁ (fromℕ< sk₁≤sM)
            head[zs₂]≡xₖ₁ = begin
                headF zs₂
                ≡⟨⟩
                xs₁ (fromℕ< sk₁≤sM)
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

            u₂∈L[xₖ₁] : inj k₂ u₂ ∈ FINAccLang na₁ (xs₁ (fromℕ< sk₁≤sM))
            u₂∈L[xₖ₁] = (zs₂ , head[zs₂]≡xₖ₁ ,  tr-zs₂-u₂ , last[zs₂]∈F₁)

            
            {-
            x₀ ⇝[u₁]  xₖ₁ ⇝[u₂] xₙ ∈ F₁
            |     |   |R₁
            |     |   x^
            |R    |Q  |R
            |     |   y^
            |     |   |R₂
            y  ⇝[v₁]  y'
            -}
            x^ : X₁
            x^ = proj₁ (proj₁ (proj₂ [xs₁[fromℕ<[sk₁≤sM]],y']∈R₁RR₂))

            y^ : X₂
            y^ = proj₁ [xs₁[fromℕ<[sk₁≤sM]],y']∈R₁RR₂

            [xₖ₁,x^]∈R₁ : (xs₁ (fromℕ< sk₁≤sM) , x^) ∈ R₁
            [xₖ₁,x^]∈R₁ = proj₁ (proj₂ (proj₁ (proj₂ [xs₁[fromℕ<[sk₁≤sM]],y']∈R₁RR₂)))

            [x^,y^]∈R : (x^ , y^) ∈ R
            [x^,y^]∈R = proj₂ (proj₂ (proj₁ (proj₂ [xs₁[fromℕ<[sk₁≤sM]],y']∈R₁RR₂)))

            [y^,y']∈R₂ : (y^ , y') ∈ R₂
            [y^,y']∈R₂ = proj₂ (proj₂ [xs₁[fromℕ<[sk₁≤sM]],y']∈R₁RR₂)
            
            module Lemma-A
                (xₖ₁ : X₁)
                (x^ : X₁)
                ([xₖ₁,x^]∈R₁ : (xₖ₁ , x^) ∈ R₁)
                (k₂ : ℕ)
                (k₁+k₂≡n : k₁ + k₂ ≡ M + l)
                (u₂ : FinWord k₂ A)
                (u₂∈L[xₖ₁] : inj k₂ u₂ ∈ FINAccLang na₁ xₖ₁)
                where

                {-
                xₖ₁ ⇝[u₂] xₙ ∈ F₁
                |R₁⊆≤Q₁
                x^
                -}
                xₖ₁≤[Q₁]x^ : xₖ₁ ≤[ na₁ , na₁ , Q₁ ]  x^
                xₖ₁≤[Q₁]x^ = R₁⊆[≤Q₁] [xₖ₁,x^]∈R₁

                {-
                xₖ₁ ⇝[u₂] xₙ ∈ F₁
                |R₁   Q₁
                x^ ⇝[u^] x♯ ∈ F₁
                -}
                [n^,u^,u^∈L[x^],[u₂,u^]∈Q₁,n^≤k₂] :
                    ∃[ n^ ] ∃ λ (u^ : FinWord n^ A)
                    → (inj n^ u^ ∈ FINAccLang na₁ x^) × ((inj k₂ u₂ , inj n^ u^) ∈ ∣Q₁∣) × (n^ ≤ k₂)
                [n^,u^,u^∈L[x^],[u₂,u^]∈Q₁,n^≤k₂] with xₖ₁≤[Q₁]x^ (inj k₂ u₂) u₂∈L[xₖ₁]
                [n^,u^,u^∈L[x^],[u₂,u^]∈Q₁,n^≤k₂] | (n^ , u^) , u^∈L[x^] , [u₂,u^]∈Q₁ =
                    (n^ , u^ , u^∈L[x^] , [u₂,u^]∈Q₁ , [w,w']∈Q₁→∣w'∣≤∣w∣ (inj k₂ u₂) (inj n^ u^) [u₂,u^]∈Q₁)

                n^ : ℕ
                n^ = proj₁ [n^,u^,u^∈L[x^],[u₂,u^]∈Q₁,n^≤k₂]
                u^ : FinWord n^ A
                u^ = proj₁ (proj₂ [n^,u^,u^∈L[x^],[u₂,u^]∈Q₁,n^≤k₂])
                u^∈L[x^] : inj n^ u^ ∈ FINAccLang na₁ x^
                u^∈L[x^] = proj₁ (proj₂ (proj₂ [n^,u^,u^∈L[x^],[u₂,u^]∈Q₁,n^≤k₂]))
                [u₂,u^]∈Q₁ : (inj k₂ u₂ , inj n^ u^) ∈ ∣Q₁∣
                [u₂,u^]∈Q₁ = proj₁ (proj₂ (proj₂ (proj₂ [n^,u^,u^∈L[x^],[u₂,u^]∈Q₁,n^≤k₂])))
                n^≤k₂ : n^ ≤ k₂
                n^≤k₂ = proj₂ (proj₂ (proj₂ (proj₂ [n^,u^,u^∈L[x^],[u₂,u^]∈Q₁,n^≤k₂])))

            open Lemma-A (xs₁ (fromℕ< sk₁≤sM)) x^ [xₖ₁,x^]∈R₁ k₂ k₁+k₂≡n u₂ u₂∈L[xₖ₁]

            module Lemma-B
                (x^ : X₁) (y^ : X₂)
                ([x^,y^]∈R : (x^ , y^) ∈ R)
                (n^ : ℕ)
                (n^≤k₂ : n^ ≤ k₂)
                (u^ : FinWord n^ A)
                (u^∈L[x^] : inj n^ u^ ∈ FINAccLang na₁ x^)
                where
                {-
                -- By applying the induction hypothesis IH to
                    x^ ⇝[u^] x♯ ∈ F₁
                    |R
                    y^
                -- we have v^ and y♯ such that
                    x^ ⇝[u^] x♯ ∈ F₁
                    |R   Q
                    y^ ⇝[v^] y♯ ∈ F₂
                -}
                ih : ∃[ v^ ] {- v^ : FINWord A -}
                    ∃[ y♯ ] {- y♯ : X₂ -}
                    (inj n^ u^ , v^) ∈ ∣Q∣
                    × (v^ ∈ FINWord-from[ y^ ]to[ y♯ ] na₂)
                    × (y♯ ∈ NA.accept na₂)
                ih = IH n^ n^<M+l x^ y^ [x^,y^]∈R xs^ u^ x^≡xs^0 tr-xs^ last[xs^]∈F₁ n^<N
                    where
                        lem : ∀ a b c → a ≢ 0 → a + b ≡ c → b < c
                        lem zero b .(zero + b) a≢0 ≡refl with a≢0 ≡refl
                        lem zero b .(zero + b) a≢0 ≡refl | ()
                        lem (suc a) b .(suc a + b) a≢0 ≡refl = s≤s (m≤n+m b a)
                        n^<M+l : n^ < M + l
                        n^<M+l = ≤-trans (s≤s n^≤k₂) (lem k₁ k₂ (M + l) k₁≢0 k₁+k₂≡n)
    
                        xs^ : Fin (suc n^) → X₁
                        xs^ = proj₁ u^∈L[x^]
    
                        x^≡xs^0 : x^ ≡ xs^ zeroF
                        x^≡xs^0 = ≡sym (proj₁ (proj₂ u^∈L[x^]))
    
                        tr-xs^ : ∀ i → (xs^ (inject₁ i) , u^ i , xs^ (sucF i)) ∈ NA.trans na₁
                        tr-xs^ = proj₁ (proj₂ (proj₂ u^∈L[x^]))
    
                        last[xs^]∈F₁ : (xs^ (fromℕ n^)) ∈ NA.accept na₁
                        last[xs^]∈F₁ = proj₂ (proj₂ (proj₂ u^∈L[x^]))
    
                        n^<N : n^ < N
                        n^<N = <-trans n^<M+l n<N
                m^ : ℕ
                m^ = proj₁ (proj₁ ih)
                v^ : FinWord m^ A
                v^ = proj₂ (proj₁ ih)
                y♯ : X₂
                y♯ = proj₁ (proj₂ ih)
                [u^,v^]∈Q : (inj n^ u^ , inj m^ v^) ∈ ∣Q∣
                [u^,v^]∈Q = proj₁ (proj₂ (proj₂ ih))
                y^-v^-y♯ : inj m^ v^ ∈ FINWord-from[ y^ ]to[ y♯ ] na₂
                y^-v^-y♯ = proj₁ (proj₂ (proj₂ (proj₂ ih)))
                y♯∈F₂ : y♯ ∈ NA.accept na₂
                y♯∈F₂ = proj₂ (proj₂ (proj₂ (proj₂ ih)))
    
                v^∈L₂[y^] : inj m^ v^ ∈ FINAccLang na₂ y^
                v^∈L₂[y^] = (ys₂^ , ys₂^0≡y^ , tr , last[ys₂^]∈F₂)
                    where
                        ys₂^ : FinWord (suc m^) X₂
                        ys₂^ = proj₁ y^-v^-y♯
    
                        ys₂^0≡y^ : headF ys₂^ ≡ y^
                        ys₂^0≡y^ = proj₁ (proj₂ y^-v^-y♯)
    
                        tr : ∀ i → (ys₂^ (inject₁ i) , v^ i , ys₂^ (sucF i)) ∈ NA.trans na₂
                        tr = proj₁ (proj₂ (proj₂ y^-v^-y♯))
    
                        last[ys₂^]∈F₂ : lastF ys₂^ ∈ NA.accept na₂
                        last[ys₂^]∈F₂ = step-∋ (NA.accept na₂) y♯∈F₂ (≡sym (proj₂ (proj₂ (proj₂ y^-v^-y♯))))

            open Lemma-B x^ y^ [x^,y^]∈R n^ n^≤k₂ u^ u^∈L[x^]

            module Lemma-C
                (y^ : X₂) (y' : X₂)
                ([y^,y']∈R₂ : (y^ , y') ∈ R₂)
                (m^ : ℕ)
                (v^ : FinWord m^ A)
                (v^∈L₂[y^] : inj m^ v^ ∈ FINAccLang na₂ y^)
                where
                {-
                -- Now, (y^ , y') ∈ ≤Q₂
                    y^ ⇝[v^] y♯ ∈ F₂
                    |R₂⊆≤Q₂
                    y'
                -- We have v₂ and y'' such that
                    y^ ⇝[v^]  y♯ ∈ F₂
                    |R₂   Q₂
                    y' ⇝[v₂]  y'' ∈ F₂
                -}
                y^≤[Q₂]y' : y^ ≤[ na₂ , na₂ , Q₂ ] y'
                y^≤[Q₂]y' = R₂⊆[≤Q₂] [y^,y']∈R₂
    
                [l₂,v₂,v₂∈L[y'],[v^,v₂]∈Q₂] :
                    ∃[ l₂ ] ∃ λ (v₂ : FinWord l₂ A)
                        → (inj l₂ v₂ ∈ FINAccLang na₂ y') × ((inj m^ v^ , inj l₂ v₂) ∈ ∣Q₂∣)
                [l₂,v₂,v₂∈L[y'],[v^,v₂]∈Q₂] with y^≤[Q₂]y' (inj m^ v^) v^∈L₂[y^]
                [l₂,v₂,v₂∈L[y'],[v^,v₂]∈Q₂] | (l₂ , v₂) , v₂∈L[y'] , [v^,v₂]∈Q₂ = (l₂ , v₂ , v₂∈L[y'] , [v^,v₂]∈Q₂)
    
                l₂ : ℕ
                l₂ = proj₁ [l₂,v₂,v₂∈L[y'],[v^,v₂]∈Q₂]
                v₂ : FinWord l₂ A
                v₂ = proj₁ (proj₂ [l₂,v₂,v₂∈L[y'],[v^,v₂]∈Q₂])
                v₂^∈L[y'] : inj l₂ v₂ ∈ FINAccLang na₂ y'
                v₂^∈L[y'] = proj₁ (proj₂ (proj₂ [l₂,v₂,v₂∈L[y'],[v^,v₂]∈Q₂]))
                [v^,v₂]∈Q₂ : (inj m^ v^ , inj l₂ v₂) ∈ ∣Q₂∣
                [v^,v₂]∈Q₂ = proj₂ (proj₂ (proj₂ [l₂,v₂,v₂∈L[y'],[v^,v₂]∈Q₂]))

            open Lemma-C y^ y' [y^,y']∈R₂ m^ v^ v^∈L₂[y^]

            module Lemma-D
                (k₁ : ℕ) (u₁ : FinWord k₁ A)
                (l₁ : ℕ) (v₁ : FinWord l₁ A)
                (k₂ : ℕ) (u₂ : FinWord k₂ A)
                (n^ : ℕ) (u^ : FinWord n^ A)
                (m^ : ℕ) (v^ : FinWord m^ A)
                (l₂ : ℕ) (v₂ : FinWord l₂ A)
                (k₁+k₂≡n : k₁ + k₂ ≡ M + l)
                ([u₁,v₁]∈Q : (inj k₁ u₁ , inj l₁ v₁) ∈ ∣Q∣)
                ([u₂,u^]∈Q₁ : (inj k₂ u₂ , inj n^ u^) ∈ ∣Q₁∣)
                ([u^,v^]∈Q : (inj n^ u^ , inj m^ v^) ∈ ∣Q∣)
                ([v^,v₂]∈Q₂ : (inj m^ v^ , inj l₂ v₂) ∈ ∣Q₂∣)
                (v₂^∈L[y']@(ys₂ , ys₂0≡y' , tr-ys₂-v₂ , last[ys₂]∈F₂) : inj l₂ v₂ ∈ FINAccLang na₂ y')
                (y⇝[v₁]y' : v₁ ∈ FinWord-from[ y ]to[ y' ] na₂ l₁)
                (eq : concat u₁ u₂ ≡ λ i → w (cast k₁+k₂≡n i))
                where
                {-
                -- (w₂ , w'') ∈ Q₁QQ₂
                    xₖ₁ ⇝[u₂] xₙ ∈ F₁
                    |R₁   Q₁
                    x^ ⇝[u^] x♯ ∈ F₁
                    |R    Q
                    y^ ⇝[v^] y♯ ∈ F₂
                    |R₂   Q₂
                    y' ⇝[v₂] y'' ∈ F₂
                -- Since (Q,Q₁,Q₂) is reasonable, we have Q₁QQ₂ ⊆ Q and then (w₂,w'') ∈ Q
                    xₖ₁ ⇝[w₂] xₙ ∈ F₁
                    |R₁  |
                    x^   |
                    |R   |Q
                    y^   |
                    |R₂  |
                    y' ⇝[v₂] y'' ∈ F₂
                -}
                [u₂,v₂]∈Q : (inj k₂ u₂ , inj l₂ v₂) ∈ ∣Q∣
                [u₂,v₂]∈Q = Q₁QQ₂⊆Q [u₂,v₂]∈Q₁QQ₂
                    where
                        [u₂,v₂]∈Q₁QQ₂ : (inj k₂ u₂ , inj l₂ v₂) ∈ ∣Q₁∣ ∘ᵣ ∣Q∣ ∘ᵣ ∣Q₂∣
                        [u₂,v₂]∈Q₁QQ₂ = (inj m^ v^ , (inj n^ u^ , [u₂,u^]∈Q₁ , [u^,v^]∈Q) , [v^,v₂]∈Q₂)
                construction :
                    ∃[ v₁v₂ ] {- v₁v₂ : FINWord A -}
                    ∃[ y'' ] {- y'' : X₂ -}
                    (((M + l) , w) , v₁v₂) ∈ ∣Q∣
                    × (v₁v₂ ∈ FINWord-from[ y ]to[ y'' ] na₂)
                    × (y'' ∈ NA.accept na₂)
                construction = (inj (l₁ + l₂) v₁v₂ , y'' , [w,v₁v₂]∈Q , (ys₁·ys₂ , ys₁·ys₂0≡ys0  , tr-ys₁·ys₂-v₁v₂ , last[ys₁·ys₂]≡y'')  , last[ys₂]∈F₂)
                    where
                        y'' : X₂
                        y'' = lastF ys₂

                        v₁v₂ : FinWord (l₁ + l₂) A
                        v₁v₂ = concat v₁ v₂

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
                            -- ys₂ (fromℕ l₂)
                            -- ≡⟨⟩
                            y''
                            ∎

                        tr-ys₁-v₁ : (i : Fin l₁) → (ys₁ (inject₁ i) , v₁ i , ys₁ (sucF i)) ∈ NA.trans na₂
                        tr-ys₁-v₁ = proj₁ (proj₂ (proj₂ y⇝[v₁]y'))

                        open QSimulation.Lemma.Transition X₂ A na₂ l₁ l₂ ys₁ ys₂ ys₂0≡last[ys₁] v₁ v₂ tr-ys₁-v₁ tr-ys₂-v₂
                        tr-ys₁·ys₂-v₁v₂ : (i : Fin (l₁ + l₂)) → NA.trans na₂ (ys₁·ys₂ (inject₁ i) , concat v₁ v₂ i , ys₁·ys₂ (sucF i))
                        tr-ys₁·ys₂-v₁v₂ i = tr i

                        [w,v₁v₂]∈Q : (inj (M + l) w , inj (l₁ + l₂) v₁v₂) ∈ ∣Q∣
                        [w,v₁v₂]∈Q = step-∋ ∣Q∣
                            (Q-is-closed-under-concat (inj k₁ u₁ , inj l₁ v₁) [u₁,v₁]∈Q (inj k₂ u₂ , inj l₂ v₂) [u₂,v₂]∈Q)
                            (begin
                            (k₁ + k₂ , concat u₁ u₂) , (l₁ + l₂ , v₁v₂)
                            ≡⟨ ≡cong (λ a → (k₁ + k₂ , a) , (l₁ + l₂ , v₁v₂)) eq ⟩
                            (k₁ + k₂ , λ i → w (cast k₁+k₂≡n i)) , (l₁ + l₂ , v₁v₂)
                            ≡⟨ ≡cong (λ a → a , (l₁ + l₂ , v₁v₂)) (≡sym (inj[m][w]≡inj[n][λi→w[cast[i]]] (M + l) (k₁ + k₂) w k₁+k₂≡n)) ⟩
                            (M + l , w) , (l₁ + l₂ , v₁v₂)
                            ∎)

            open Lemma-D k₁ u₁ l₁ v₁ k₂ u₂ n^ u^ m^ v^ l₂ v₂ k₁+k₂≡n
                    [u₁,v₁]∈Q [u₂,u^]∈Q₁ [u^,v^]∈Q [v^,v₂]∈Q₂ v₂^∈L[y'] y⇝[v₁]y'
                    ([concat-split-w]≡w' w k₁≤n)


    finalN : ∀ x y → (x , y) ∈ R → Final[ N ][ N>0 ][ Q ] R x y
    finalN x y [x,y]∈R n = <-rec (λ n → _) lemma n x y [x,y]∈R

M≤N⇒StepMupto⇒FinalM⇒FinalN :
    ∀ {M N : ℕ} {M>0 : M > 0} {N>0 : N > 0} → M ≤ N
    → (Q Q₁ Q₂ : Preorder)
    → [ Q , Q₁ , Q₂ ]-is-reasonable
    → {ℓ : Level}
    → (R : Pred' (X₁ × X₂) {ℓ})
    → (R₁ : Pred' (X₁ × X₁) {ℓ}) → (R₁⊆[≤Q₁] : R₁ ⊆ (λ (x , x') → x ≤[ na₁ , na₁ ,  Q₁ ] x'))
    → (R₂ : Pred' (X₂ × X₂) {ℓ}) → (R₂⊆[≤Q₂] : R₂ ⊆ (λ (y , y') → y ≤[ na₂ , na₂ ,  Q₂ ] y'))
    → (∀ x y → (x , y) ∈ R → StepUpto[ M ][ M>0 ][ Q , R₁ , R₂ ] R x y)
    → (∀ x y → (x , y) ∈ R → Final[ M ][ M>0 ][ Q ] R x y)
    → (∀ x y → (x , y) ∈ R → Final[ N ][ N>0 ][ Q ] R x y)
M≤N⇒StepMupto⇒FinalM⇒FinalN {M} {N} {M>0} {N>0} M≤N Q Q₁ Q₂ QQ₁Q₂-is-reasonable R R₁ R₁⊆[≤Q₁] R₂ R₂⊆[≤Q₂] x y stepMupto finalM =
    LemmaUpto.finalN M N {M>0} {N>0} M≤N Q Q₁ Q₂ QQ₁Q₂-is-reasonable R R₁ R₁⊆[≤Q₁] R₂ R₂⊆[≤Q₂] x y stepMupto finalM

StepMupto⇒FinalM⇒Stepupto :
    (M : ℕ) {M>0 : M > 0}
    → (Q Q₁ Q₂ : Preorder)
    → [ Q , Q₁ , Q₂ ]-is-reasonable
    → {ℓ : Level}
    → (R : Pred' (X₁ × X₂) {ℓ})
    → (R₁ : Pred' (X₁ × X₁) {ℓ}) → (R₁⊆[≤Q₁] : R₁ ⊆ (λ (x , x') → x ≤[ na₁ , na₁ ,  Q₁ ] x'))
    → (R₂ : Pred' (X₂ × X₂) {ℓ}) → (R₂⊆[≤Q₂] : R₂ ⊆ (λ (y , y') → y ≤[ na₂ , na₂ ,  Q₂ ] y'))
    → (∀ x y → (x , y) ∈ R → StepUpto[ M ][ M>0 ][ Q , R₁ , R₂ ] R x y)
    → (∀ x y → (x , y) ∈ R → Final[ M ][ M>0 ][ Q ] R x y)
    → (∀ x y → (x , y) ∈ R → StepUpto[ Q , R₁ , R₂ ] R x y)
StepMupto⇒FinalM⇒Stepupto M Q Q₁ Q₂ _ R R₁ _ R₂ _ StepMupto FinalM x y [x,y]∈R n xs w x≡xs0 tr-xs-w last[xs]∈F₁
    -- case analysis
    with k≤n⊎n<k (suc (suc n)) M
StepMupto⇒FinalM⇒Stepupto M Q Q₁ Q₂ _ R R₁ _ R₂ _ StepMupto FinalM x y [x,y]∈R n xs w x≡xs0 tr-xs-w last[xs]∈F₁
    -- n + 1 < M
    | inj₁ sn<M
    -- use FinalM
    with FinalM x y [x,y]∈R (suc n) xs w x≡xs0 tr-xs-w last[xs]∈F₁ sn<M
StepMupto⇒FinalM⇒Stepupto M (aPreorder ∣Q∣ Qrefl Qtrans) Q₁ Q₂ _ R R₁ _ R₂ _ StepMupto FinalM x y [x,y]∈R n xs w x≡xs0 tr-xs-w last[xs]∈F₁
    | inj₁ sn<M
    | (l' , w') , y' , [w,w']∈Q , y⇝[w']y' , y'∈F₂ =
    (suc n , (λ ()) , ≤-reflexive ≡refl , inj l' w' , y' , [w↾sn≤sn,w']∈Q , y⇝[w']y' , inj₂ (≡refl , y'∈F₂) )
    where
        lem : (i : Fin (suc n)) → proj₁ (split w (≤-reflexive ≡refl)) i ≡ w i
        lem i = begin
            proj₁ (split w (≤-reflexive ≡refl)) i
            ≡⟨ w₁i≡wi w (≤-reflexive ≡refl) i ⟩
            w (inject≤ i (≤-reflexive ≡refl))
            ≡⟨ ≡cong w (inject≤[i][n≤n]≡i i (≤-reflexive ≡refl)) ⟩
            w i
            ∎
        [w↾sn≤sn,w']∈Q : ((suc n , (w ↾ ≤-reflexive ≡refl)) , (l' , w')) ∈ ∣Q∣
        [w↾sn≤sn,w']∈Q = step-∋ ∣Q∣ [w,w']∈Q
            (begin
            (suc n , w) , (l' , w')
            ≡⟨ ≡cong (λ a → (suc n , a) , (l' , w')) (≡sym (ex lem)) ⟩
            (suc n , proj₁ (split w (≤-reflexive ≡refl))) , (l' , w')
            ≡⟨⟩
            (suc n , (w ↾ (s≤s (≤-reflexive ≡refl)))) , (l' , w')
            ∎)

StepMupto⇒FinalM⇒Stepupto M {M>0} Q@(aPreorder ∣Q∣ Qrefl Qtrans) Q₁ Q₂ QQ₁Q₂-is-reasonable R R₁ R₁⊆[≤Q₁] R₂ R₂⊆[≤Q₂] StepMupto FinalM x y [x,y]∈R n xs w x≡xs0 tr-xs-w last[xs]∈F₁
    -- M ≤ n + 1
    | inj₂ (s≤s M≤sn) =
    (suc n ,  (λ ()) , ≤-reflexive ≡refl , [w'] , y' , [w↾sn≤sn,w']∈Q , y⇝[w']y' , inj₂ (≡refl , y'∈F₂))
    where
        Final[ssn] = M≤N⇒StepMupto⇒FinalM⇒FinalN {M} {suc (suc n)} {M>0} {s≤s z≤n} (m≤n⇒m≤1+n M≤sn) Q Q₁ Q₂ QQ₁Q₂-is-reasonable R R₁ R₁⊆[≤Q₁] R₂ R₂⊆[≤Q₂] StepMupto FinalM x y [x,y]∈R
        [w',y',[w,w']∈Q,y⇝[w']y',y'∈F₂] = Final[ssn] (suc n) xs w x≡xs0 tr-xs-w last[xs]∈F₁ (≤-reflexive ≡refl)


        [w'] = proj₁ [w',y',[w,w']∈Q,y⇝[w']y',y'∈F₂]

        l' : ℕ
        l' = proj₁ [w']

        w' : FinWord l' A
        w' = proj₂ [w']

        y' : X₂
        y' = proj₁ (proj₂ [w',y',[w,w']∈Q,y⇝[w']y',y'∈F₂])

        [w,w']∈Q : (inj (suc n) w , [w']) ∈ ∣Q∣
        [w,w']∈Q = proj₁ (proj₂ (proj₂ [w',y',[w,w']∈Q,y⇝[w']y',y'∈F₂]))

        y⇝[w']y' : w' ∈ FinWord-from[ y ]to[ y' ] na₂ l'
        y⇝[w']y' = proj₁ (proj₂ (proj₂ (proj₂ [w',y',[w,w']∈Q,y⇝[w']y',y'∈F₂])))

        y'∈F₂ : y' ∈ NA.accept na₂
        y'∈F₂ = proj₂ (proj₂ (proj₂ (proj₂ [w',y',[w,w']∈Q,y⇝[w']y',y'∈F₂])))

        lem : (i : Fin (suc n)) → proj₁ (split w (≤-reflexive ≡refl)) i ≡ w i
        lem i = begin
            proj₁ (split w (≤-reflexive ≡refl)) i
            ≡⟨ w₁i≡wi w (≤-reflexive ≡refl) i ⟩
            w (inject≤ i (≤-reflexive ≡refl))
            ≡⟨ ≡cong w (inject≤[i][n≤n]≡i i (≤-reflexive ≡refl)) ⟩
            w i
            ∎
        [w↾sn≤sn,w']∈Q : ((suc n , (w ↾ ≤-reflexive ≡refl)) , [w']) ∈ ∣Q∣
        [w↾sn≤sn,w']∈Q = step-∋ ∣Q∣ [w,w']∈Q
            (begin
            (suc n , w) , [w']
            ≡⟨ ≡cong (λ a → (suc n , a) , [w']) (≡sym (ex lem)) ⟩
            (suc n , proj₁ (split w (≤-reflexive ≡refl))) , [w']
            ≡⟨⟩
            (suc n , (w ↾ (s≤s (≤-reflexive ≡refl)))) , [w']
            ∎)

FinalM⇒Final :
    (M : ℕ)
    → {M>0 : M > 0}
    → (Q : Preorder)
    → {ℓ : Level}
    → (R : Pred' (X₁ × X₂) {ℓ})
    → (x : X₁) → (y : X₂)
    → Final[ M ][ M>0 ][ Q ] R x y
    → Final[ Q ] R x y
FinalM⇒Final M {M>0} (aPreorder ∣Q∣ Qrefl Qtrans) R x y FinalM x∈F₁
    {- ∃[ w' ] ∃[ y' ] ((zero , (λ ())) , w') ∈ ∣Q∣ × (w' ∈ FINWord-from[ y ]to[ y' ] na₂) × (y' ∈ NA.accept na₂) -}
    with FinalM zero (λ i → x) (λ ()) ≡refl (λ ()) x∈F₁ M>0
FinalM⇒Final M {M>0} (aPreorder ∣Q∣ Qrefl Qtrans) R x y FinalM x∈F₁
    | w' , y' , [0length,w']∈Q , y⇝[w']y' , y'∈F₂ =
    ( w' , y' , y⇝[w']y' , y'∈F₂ , [emptyF,w']∈Q )
    where
        [emptyF,w']∈Q : ((0 , emptyF) , w') ∈ ∣Q∣
        [emptyF,w']∈Q = step-∋ ∣Q∣ [0length,w']∈Q
            (begin
            (zero , (λ ())) , w'
            ≡⟨ ≡cong (λ a → (zero , a) , w') (ex λ ()) ⟩
            (zero , emptyF) , w'
            ∎)

Mbounded-upto⇒unbounded-upto :
    (M : ℕ)
    → (M>0 : M > 0)
    → (Q Q₁ Q₂ : Preorder)
    → [ Q , Q₁ , Q₂ ]-is-reasonable
    → {ℓ : Level}
    → (R₁ : Pred' (X₁ × X₁) {ℓ}) → (R₁⊆[≤Q₁] : R₁ ⊆ (λ (x , x') → x ≤[ na₁ , na₁ ,  Q₁ ] x'))
    → (R₂ : Pred' (X₂ × X₂) {ℓ}) → (R₂⊆[≤Q₂] : R₂ ⊆ (λ (y , y') → y ≤[ na₂ , na₂ ,  Q₂ ] y'))
    → [ M ][ M>0 ]-bounded-[ Q , R₁ , R₂ ]-constrained-simulation-upto
    → [ Q , R₁ , R₂ ]-constrained-simulation-upto
Mbounded-upto⇒unbounded-upto M M>0 Q Q₁ Q₂ Q-is-reasonable R₁ R₁⊆[≤Q₁] R₂ R₂⊆[≤Q₂] (QSimulationBase.aBoundedConstrainedSimulationUpto R FinalM StepMupto) =
    QSimulationBase.aConstrainedSimulationUpto R Final StepUpto
    where
        Final : ∀ x y → (x , y) ∈ R → Final[ Q ] R x y
        Final x y [x,y]∈R = FinalM⇒Final M {M>0} Q R x y (FinalM x y [x,y]∈R)

        StepUpto : ∀ x y → (x , y) ∈ R → StepUpto[ Q , R₁ , R₂ ] R x y
        StepUpto x y [x,y]∈R = StepMupto⇒FinalM⇒Stepupto M {M>0} Q Q₁ Q₂ Q-is-reasonable R R₁ R₁⊆[≤Q₁] R₂ R₂⊆[≤Q₂] StepMupto FinalM x y [x,y]∈R

{-
-------- non up-to version --------
-}
import QSimulation.InstanceOfPreorder
open QSimulation.InstanceOfPreorder.Eq A
open QSimulation.InstanceOfPreorder.UptoEq A X₁ na₁ renaming (EqR to EqR₁; EqR⊆[≤Eq] to EqR₁⊆[≤Eq])
open QSimulation.InstanceOfPreorder.UptoEq A X₂ na₂ renaming (EqR to EqR₂; EqR⊆[≤Eq] to EqR₂⊆[≤Eq])

stepM⇒stepMUptoEqEq :
    (M : ℕ) {M>0 : M > 0}
    → (Q : Preorder)
    → (R : Pred' (X₁ × X₂))
    → (∀ x y → R (x , y) → Step[ M ][ M>0 ][ Q ] R x y) 
    → (∀ x y → R (x , y) → StepUpto[ M ][ M>0 ][ Q , EqR₁ , EqR₂ ] R x y)
stepM⇒stepMUptoEqEq M Q R stepM x y [x,y]∈R xs w x≡xs0 tr =
    (k , k≢0 , k<sM , w' , y' , [w↾k,w']∈Q , y⇝[w']y' , [xₖ,y']∈R₁RR₂)
    where
        a = stepM x y [x,y]∈R xs w x≡xs0 tr

        k : ℕ
        k = proj₁ a

        k≢0 : k ≢ 0
        k≢0 = proj₁ (proj₂ a)

        k<sM : k < suc M
        k<sM = proj₁ (proj₂ (proj₂ a))

        w' : FINWord A
        w' = proj₁ (proj₂ (proj₂ (proj₂ a)))

        y' : X₂
        y' = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ a))))

        [w↾k,w']∈Q : (inj k (w ↾ k<sM) , w') ∈ Preorder.carrier Q
        [w↾k,w']∈Q = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ a)))))

        y⇝[w']y' : w' ∈ FINWord-from[ y ]to[ y' ] na₂
        y⇝[w']y' = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ a))))))

        [xₖ,y']∈R : (xs (fromℕ< k<sM) , y') ∈ R
        [xₖ,y']∈R = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ a))))))

        [xₖ,y']∈R₁RR₂ : (xs (fromℕ< k<sM) , y') ∈ EqR₁ ∘ᵣ R ∘ᵣ EqR₂
        [xₖ,y']∈R₁RR₂ = (y' , ((xs (fromℕ< k<sM) , (≡refl , [xₖ,y']∈R)) , ≡refl))


M-bounded⇒M-bounded-upto :
    (M : ℕ) {M>0 : M > 0}
    → (Q : Preorder)
    → [ M ][ M>0 ]-bounded-[ Q ]-constrained-simulation lzero
    → [ M ][ M>0 ]-bounded-[ Q , EqR₁ , EqR₂ ]-constrained-simulation-upto
M-bounded⇒M-bounded-upto M {M>0} Q (QSimulationBase.aBoundedConstrainedSimulation R finalM stepM) =
    QSimulationBase.aBoundedConstrainedSimulationUpto R finalM (stepM⇒stepMUptoEqEq M {M>0} Q R stepM)

[Q,Eq,Eq]-is-reasonable :
    {Q : Preorder}
    → [ Q ]-is-closed-under-concat
    → [ Q , Eq , Eq ]-is-reasonable
[Q,Eq,Eq]-is-reasonable {Q} Q-is-closed-under-concat = (Q-is-closed-under-concat , p , q)
    where
        p : (w w' : FINWord A) → (w , w') ∈ Preorder.carrier Eq → ∣ w' ∣ ≤ ∣ w ∣
        p (l , w) .(l , w) ≡refl = ≤-reflexive ≡refl

        q : EqCarrier ∘ᵣ (Preorder.carrier Q) ∘ᵣ EqCarrier ⊆ Preorder.carrier Q
        q ((l , w) , ((l' , w') , ≡refl , [w,w']∈Q) , ≡refl) = [w,w']∈Q

Mbounded⇒unbounded :
    (M : ℕ)
    → {M>0 : M > 0}
    → (Q : Preorder)
    → [ Q ]-is-closed-under-concat
    → [ M ][ M>0 ]-bounded-[ Q ]-constrained-simulation lzero
    → [ Q ]-constrained-simulation
Mbounded⇒unbounded M {M>0} Q Q-is-closed-under-concat M-bounded-Q-constrained-simulation = removeEqEq [Q,Eq,Eq]-constrained-simulation-upto
    where
        M-bounded-[Q,Eq,Eq]-constrained-simulation-upto = M-bounded⇒M-bounded-upto M {M>0} Q M-bounded-Q-constrained-simulation

        Q-is-reasonable : [ Q , Eq , Eq ]-is-reasonable
        Q-is-reasonable = [Q,Eq,Eq]-is-reasonable {Q} Q-is-closed-under-concat
        
        [Q,Eq,Eq]-constrained-simulation-upto =
            Mbounded-upto⇒unbounded-upto M M>0 Q Eq Eq Q-is-reasonable EqR₁ EqR₁⊆[≤Eq] EqR₂ EqR₂⊆[≤Eq] M-bounded-[Q,Eq,Eq]-constrained-simulation-upto

        removeEqEq :
            [ Q , EqR₁ , EqR₂ ]-constrained-simulation-upto
            → [ Q ]-constrained-simulation
        removeEqEq (aConstrainedSimulationUpto R final stepUpto) =
            aConstrainedSimulation R final step
            where
                step : ∀ x y → R (x , y) → Step[ Q ] R x y
                step x y [x,y]∈R n xs as x≡xs0 tr last[xs]∈F₁ with stepUpto x y [x,y]∈R n xs as x≡xs0 tr last[xs]∈F₁
                step x y [x,y]∈R n xs as x≡xs0 tr last[xs]∈F₁ | k , k≢0 , sk≤ssn , w' , y' , [as↾k,w']∈Q , t , inj₁ (.y' , (.(xs (fromℕ< sk≤ssn)) , ≡refl , ∈R) , ≡refl) =
                    (k , k≢0 , sk≤ssn , w' , y' , [as↾k,w']∈Q , t , inj₁ ∈R)
                step x y [x,y]∈R n xs as x≡xs0 tr last[xs]∈F₁ | k , k≢0 , sk≤ssn , w' , y' , [as↾k,w']∈Q , t , inj₂ a =
                    (k , k≢0 , sk≤ssn , w' , y' , [as↾k,w']∈Q , t , inj₂ a)

stepMuptoEqEq⇒stepM :
    {M : ℕ} {M>0 : M > 0}
    → (Q : Preorder)
    → (R : Pred' (X₁ × X₂))
    → (∀ x y → R (x , y) → StepUpto[ M ][ M>0 ][ Q , EqR₁ , EqR₂ ] R x y)
    → (∀ x y → R (x , y) → Step[ M ][ M>0 ][ Q ] R x y)
stepMuptoEqEq⇒stepM {M} {M>0} Q R stepMuptoEqEq = step
    where
    step : ∀ x y → R (x , y) → Step[ M ][ M>0 ][ Q ] R x y
    step x y [x,y]∈R xs as x≡xs0 tr with stepMuptoEqEq x y [x,y]∈R xs as x≡xs0 tr
    step x y [x,y]∈R xs as x≡xs0 tr | k , k≢0 , sk≤ssn , w' , y' , [as↾k,w']∈Q , t , (.y' , (.(xs (fromℕ< sk≤ssn)) , ≡refl , ∈R) , ≡refl) =
        (k , k≢0 , sk≤ssn , w' , y' , [as↾k,w']∈Q , t , ∈R)

M≤N⇒Mbounded⇒Nbounded :
    {M N : ℕ}
    {M>0 : M > 0}
    {N>0 : N > 0}
    → M ≤ N
    → (Q : Preorder)
    → [ Q ]-is-closed-under-concat
    → [ M ][ M>0 ]-bounded-[ Q ]-constrained-simulation lzero
    → [ N ][ N>0 ]-bounded-[ Q ]-constrained-simulation lzero
M≤N⇒Mbounded⇒Nbounded {M} {N} {M>0} {N>0} M≤N Q Q-is-closed-under-concat (QSimulationBase.aBoundedConstrainedSimulation R finalM stepM) =
    QSimulationBase.aBoundedConstrainedSimulation R finalN stepN
    where
        finalN : (x : X₁) (y : X₂) → R (x , y) → Final[ N ][ N>0 ][ Q ] R x y
        finalN = M≤N⇒StepMupto⇒FinalM⇒FinalN {M} {N} {M>0} {N>0}
            M≤N Q Eq Eq Q-is-reasonable R EqR₁ EqR₁⊆[≤Eq] EqR₂ EqR₂⊆[≤Eq] (stepM⇒stepMUptoEqEq M {M>0} Q R stepM) finalM
            where
            Q-is-reasonable : [ Q , Eq , Eq ]-is-reasonable
            Q-is-reasonable = [Q,Eq,Eq]-is-reasonable {Q} Q-is-closed-under-concat

        stepN : (x : X₁) (y : X₂) → R (x , y) → Step[ N ][ N>0 ][ Q ] R x y
        stepN x y [x,y]∈R = M≤N⇒StepM⇒StepN {M} {N} {M>0} {N>0} M≤N Q R x y (stepM x y [x,y]∈R)


{- ---- closed under union ---- -}
M-bounded-Q-simulation-is-closed-under-union-final :
    {M : ℕ}
    {M>0 : M > 0}
    → (Q : Preorder)
    → {ℓ : Level}
    → (S₁@(aBoundedConstrainedSimulation R₁ final₁ step₁) : [ M ][ M>0 ]-bounded-[ Q ]-constrained-simulation ℓ)
    → (S₂@(aBoundedConstrainedSimulation R₂ final₂ step₂) : [ M ][ M>0 ]-bounded-[ Q ]-constrained-simulation ℓ)
    → ∀ x y → (R₁ ∪ R₂) (x , y) →  Final[ M ][ M>0 ][ Q ] (R₁ ∪ R₂) x y
M-bounded-Q-simulation-is-closed-under-union-final {M} {M>0} Q
    (QSimulationBase.aBoundedConstrainedSimulation R₁ final₁ step₁) (QSimulationBase.aBoundedConstrainedSimulation R₂ final₂ step₂)
    x y (inj₁ [x,y]∈R₁) = final₁ x y [x,y]∈R₁
M-bounded-Q-simulation-is-closed-under-union-final {M} {M>0} Q
    S₁@(aBoundedConstrainedSimulation R₁ final₁ step₁) S₂@(aBoundedConstrainedSimulation R₂ final₂ step₂)
    x y (inj₂ [x,y]∈R₂) = final₂ x y [x,y]∈R₂

M-bounded-Q-simulation-is-closed-under-union-step :
    {M : ℕ}
    {M>0 : M > 0}
    → (Q : Preorder)
    → {ℓ : Level}
    → (S₁@(aBoundedConstrainedSimulation R₁ final₁ step₁) : [ M ][ M>0 ]-bounded-[ Q ]-constrained-simulation ℓ)
    → (S₂@(aBoundedConstrainedSimulation R₂ final₂ step₂) : [ M ][ M>0 ]-bounded-[ Q ]-constrained-simulation ℓ)
    → ∀ x y → (R₁ ∪ R₂) (x , y) →  Step[ M ][ M>0 ][ Q ] (R₁ ∪ R₂) x y
M-bounded-Q-simulation-is-closed-under-union-step {M} {M>0} Q
    (QSimulationBase.aBoundedConstrainedSimulation R₁ final₁ step₁) (QSimulationBase.aBoundedConstrainedSimulation R₂ final₂ step₂)
    x y (inj₁ [x,y]∈R₁)
    xs w x≡xs0 tr 
    with step₁ x y [x,y]∈R₁ xs w x≡xs0 tr
... | k , k>0 , sk≤sM , w' , y' , ([wk,w']∈Q , tr , rel) =
    (k , k>0 , sk≤sM , w' , y' , ([wk,w']∈Q , tr , inj₁ rel))
M-bounded-Q-simulation-is-closed-under-union-step {M} {M>0} Q
    S₁@(aBoundedConstrainedSimulation R₁ final₁ step₁) S₂@(aBoundedConstrainedSimulation R₂ final₂ step₂)
    x y (inj₂ [x,y]∈R₂)
    xs w x≡xs0 tr 
    with step₂ x y [x,y]∈R₂ xs w x≡xs0 tr
... | k , k>0 , sk≤sM , w' , y' , ([wk,w']∈Q , tr , rel) =
    (k , k>0 , sk≤sM , w' , y' , ([wk,w']∈Q , tr , inj₂ rel))

M-bounded-Q-simulation-is-closed-under-union :
    {M : ℕ}
    {M>0 : M > 0}
    → (Q : Preorder)
    → {ℓ : Level}
    → (S₁ : [ M ][ M>0 ]-bounded-[ Q ]-constrained-simulation ℓ)
    → (S₂ : [ M ][ M>0 ]-bounded-[ Q ]-constrained-simulation ℓ)
    → [ M ][ M>0 ]-bounded-[ Q ]-constrained-simulation ℓ
M-bounded-Q-simulation-is-closed-under-union {M} {M>0} Q
    S₁@(aBoundedConstrainedSimulation R₁ final₁ step₁) S₂@(aBoundedConstrainedSimulation R₂ final₂ step₂) =
    aBoundedConstrainedSimulation (R₁ ∪ R₂) final step
    where
        final : ∀ x y → (R₁ ∪ R₂) (x , y) → Final[ M ][ M>0 ][ Q ] (R₁ ∪ R₂) x y
        final = M-bounded-Q-simulation-is-closed-under-union-final {M} {M>0} Q S₁ S₂

        step : ∀ x y → (R₁ ∪ R₂) (x , y) → Step[ M ][ M>0 ][ Q ] (R₁ ∪ R₂) x y
        step = M-bounded-Q-simulation-is-closed-under-union-step {M} {M>0} Q S₁ S₂

{-- the (M,Q)-similarity is a (M,Q)-simulation --}
[M,Q]-similarity : {M : ℕ} {M>0 : M > 0} → (Q : Preorder) → {ℓ : Level} → Pred' (X₁ × X₂) {lsuc ℓ}
[M,Q]-similarity {M} {M>0} Q {ℓ} (x , y) =
    Σ ([ M ][ M>0 ]-bounded-[ Q ]-constrained-simulation ℓ) (λ { (aBoundedConstrainedSimulation R final step) → (x , y) ∈ R})
[M,Q]-similarity-is-[M,Q]-simulation : {M : ℕ} {M>0 : M > 0}
    → (Q : Preorder)
    → {ℓ : Level}
    → [ M ][ M>0 ]-bounded-[ Q ]-constrained-simulation (lsuc ℓ)
[M,Q]-similarity-is-[M,Q]-simulation {M} {M>0} Q {ℓ} =
    aBoundedConstrainedSimulation similarity sim-final sim-step
    where
        similarity : Pred' (X₁ × X₂) {lsuc ℓ}
        similarity = [M,Q]-similarity {M} {M>0} Q {ℓ}

        sim-final : ∀ x y → similarity (x , y) → Final[ M ][ M>0 ][ Q ] similarity x y
        sim-final x y (QSimulationBase.aBoundedConstrainedSimulation R final step , [x,y]∈R) = final x y [x,y]∈R

        sim-step : ∀ x y → similarity (x , y) → Step[ M ][ M>0 ][ Q ] similarity x y
        sim-step x y (simR@(QSimulationBase.aBoundedConstrainedSimulation R final step) , [x,y]∈R) xs w x≡xs0 tr with step x y [x,y]∈R xs w x≡xs0 tr
        ... | k , k>0 , sk≤sM , w' , y' , ([wk,w']∈Q , tr , rel) = k , k>0 , sk≤sM , w' , y' , ([wk,w']∈Q , tr , (simR , rel))
