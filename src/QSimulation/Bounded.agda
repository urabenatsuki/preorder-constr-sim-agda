open import NA.Base
module QSimulation.Bounded
    (X₁ X₂ A : Set)
    (na₁@(anNA ⇝₁ _ F₁) : NA X₁ A)
    (na₂@(anNA ⇝₂ _ F₂) : NA X₂ A)
    where

open import Base
open import Data.Nat
open import Data.Nat.Properties
    using (≤-trans)
open import Data.Fin
    using (Fin; inject₁; inject≤; fromℕ; fromℕ<; toℕ; cast)
    renaming (zero to zeroF; suc to sucF; _+_ to _+F_)
open import Relation.Binary.PropositionalEquality
    using (_≡_; _≢_; inspect; [_])
    renaming (refl to ≡refl; sym to ≡sym; cong to ≡cong)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Relation.Unary using (_∈_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)

open import Base
open import FinForWord
open import Word
open import NA
open import QSimulation.Base
open QSimulation.Base.ConditionOnQ A
open QSimulation.Base.QSimulationBase A X₁ X₂ na₁ na₂
open import QSimulation.Lemma using (inject≤inject₁≡inject₁inject≤)

M≤N⇒FinalN⇒FinalM :
    ∀ {M N : ℕ} → M ≤ N
    → (Q : Preorder)
    → (R : Pred' (X₁ × X₂)) → (x : X₁) → (y : X₂)
    → Final[ N ][ Q ] R x y
    → Final[ M ][ Q ] R x y
M≤N⇒FinalN⇒FinalM
    {M} {N} M≤N Q R .(xs zeroF) y finalN
    n xs w ≡refl tr tailx∈F₁ n<M =
    finalN n xs w ≡refl tr tailx∈F₁ (≤-trans n<M M≤N)

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
    (k , k≢0 , sk≤sN , w' , y' , [w↾sk≤sN,w']∈Q , y⇝[w']y' , {!  !} )
    where
        -- xs↾≤Mi≡xsi : (i : Fin (suc M)) → xs≤M i ≡ xs (inject≤ i (s≤s M≤N))
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
        

        a : {n m k : ℕ} → (m≤n : m ≤ n) → (sk≤sm : suc k ≤ suc m)
            → (sk≤sn : suc k ≤ suc n)
            → (u' : Fin m → A) → (u : Fin n → A)
            → ((i : Fin m) → u' i ≡ u (inject≤ i m≤n))
            → (i : Fin k)
            → (u' ↾ sk≤sm) i ≡ (u ↾ sk≤sn) i
        a {n} {m} {k} m≤n sk≤sm sk≤sn u' u p i = {!   !}


        w↾<M↾≤k[i]≡w↾≤sN↾<k[i] : (i : Fin k) → (w↾<M ↾ sk≤sM) i ≡ (w ↾ sk≤sN) i
        w↾<M↾≤k[i]≡w↾≤sN↾<k[i] i = begin
            (w↾<M ↾ sk≤sM) i
            ≡⟨ {!   !} ⟩
            (w ↾ sk≤sN) i
            ∎
        -- (i : Fin M) → w i ≡ w' (inject≤ i M≤N)

        [w↾sk≤sN,w']∈Q : (( k , w ↾ sk≤sN ) , w') ∈ ∣Q∣
        [w↾sk≤sN,w']∈Q = step-∋ ∣Q∣ [w↾<M↾≤k,w']∈Q
            (begin
            ((k , w↾<M ↾ sk≤sM ) , w')
            ≡⟨ ≡cong (λ a → ((k , a), w')) (ex w↾<M↾≤k[i]≡w↾≤sN↾<k[i]) ⟩
            ((k , w ↾ sk≤sN ) , w')
            ∎)

        y⇝[w']y' = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ stepM))))))

