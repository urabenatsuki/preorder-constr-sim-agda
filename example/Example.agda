module Example where

open import Data.Bool
  using (true; false; Bool; not; _∧_)
  renaming (f≤t to f→ᵇt; b≤b to b→ᵇb; _≤_ to _→ᵇ_)
open import Data.Nat
open import Data.Nat.Properties
  using (≤-reflexive; ≤-trans; ≤-step; _≟_)
open import Data.Fin
  using (Fin; inject≤; fromℕ<; inject₁; cast)
  renaming (zero to zeroF; suc to sucF)
open import Data.Fin.Properties
  using (inject≤-refl; inject≤-idempotent)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Relation.Nullary using (_because_; ofʸ; ofⁿ; ¬_)
open import Relation.Unary using (_∈_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; inspect; [_]; _≢_)
  renaming (refl to ≡refl; sym to ≡sym; cong to ≡cong)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)

open import Base
open import Word
open import NA
open import QSimulation.Base
open import QSimulation.Lemma using (casti≡i)
open import QSimulation.InstanceOfPreorder

module Fig-1-1 where
  data A : Set where
    a : A

  open Addτ A
  
  module NA₁ where
    {-
    x₀ ─τ⟶ x₁ ─τ⟶ x₂
                    ↺a
    -}

    data X : Set where
      x₀ : X
      x₁ : X
      x₂ : X

    tr₁ : Pred' (X × A+τ × X)
    tr₁ (x₀ , τ , x₁) = ⊤
    tr₁ (x₁ , τ , x₂) = ⊤
    tr₁ (x₂ , fromA a , x₂) = ⊤
    tr₁ _ = ⊥

    acc₁ : Pred' X
    acc₁ x₀ = ⊥
    acc₁ x₁ = ⊥
    acc₁ x₂ = ⊤

    init₁ : Pred' X
    init₁ x₀ = ⊤
    init₁ x₁ = ⊥
    init₁ x₂ = ⊥

    na₁ : NA X A+τ
    na₁ = anNA tr₁ init₁ acc₁
  open NA₁

  module NA₂ where
    {-
    y₀ ─────τ────⟶ y₂
                    ↺a
    -}
    data Y : Set where
      y₀ : Y
      y₂ : Y

    tr₂ : Pred' (Y × A+τ × Y)
    tr₂ (y₀ , τ , y₂) = ⊤
    tr₂ (y₂ , fromA a , y₂) = ⊤
    tr₂ _ = ⊥

    acc₂ : Pred' Y
    acc₂ y₀ = ⊥
    acc₂ y₂ = ⊤

    init₂ : Pred' Y
    init₂ y₀ = ⊤
    init₂ y₂ = ⊥

    na₂ : NA Y A+τ
    na₂ = anNA tr₂ init₂ acc₂
  open NA₂
  
  open Remτ A
  open QSimulationBase A+τ X Y na₁ na₂
  
  module 1Bounded where
    R : Pred' (X × Y)
    -- R = { (x₀ , y₀) , (x₁ , y₀) , (x₂ , y₂) }
    R (x₀ , y₀) = ⊤
    R (x₀ , y₂) = ⊥
    R (x₁ , y₀) = ⊤
    R (x₁ , y₂) = ⊥
    R (x₂ , y₀) = ⊥
    R (x₂ , y₂) = ⊤

    final : ∀ x y → (x , y) ∈ R → Final[ 1 ][ ≡τ ] R x y
    final x₀ y [x,y]∈R zero xs w p tr x₀∈F₁ (s≤s z≤n) with step-∋ acc₁ x₀∈F₁ (≡sym p)
    final x₀ y [x,y]∈R zero xs w p tr x₀∈F₁ (s≤s z≤n) | ()
    final x₁ y [x,y]∈R zero xs w p tr x₁∈F₁ (s≤s z≤n) with step-∋ acc₁ x₁∈F₁ (≡sym p)
    final x₁ y [x,y]∈R zero xs w p tr x₁∈F₁ (s≤s z≤n) | ()
    final x₂ y₂ tt zero xs w p tr x₂∈F₂ (s≤s z≤n) = ((zero , emptyF) , y₂ , (λ i → ≡refl) , tr' , tt)
      where
        tr' : (zero , emptyF) ∈ FINWord-from[ y₂ ]to[ y₂ ] na₂
        tr' = (λ y → y₂) , ≡refl , (λ ()) , ≡refl

    step : ∀ x y → (x , y) ∈ R → Step[ 1 ][ ≡τ ] R x y
    step x₀ y₀ tt xs w p tr with tr zeroF 
    step x₀ y₀ tt xs w p tr | tr[0] with xs zeroF | w zeroF | xs (sucF zeroF) | inspect w zeroF | inspect xs (sucF zeroF)
    step x₀ y₀ tt xs w p tr | tt | x₀ | Addτ.τ | x₁ | [ w0≡τ ] | [ xs1≡x₁ ] =
      -- x₀ -τ→ x₁
      (1 , (λ ()) , s≤s (s≤s z≤n) , (zero , emptyF) , y₀ , w↾1≡τε , ((λ i → y₀) , ≡refl , (λ ()) , ≡refl) , [xs1,y₀]∈R)
      where
        [xs1,y₀]∈R : R (xs (fromℕ< (s≤s (s≤s (z≤n)))) , y₀ )
        [xs1,y₀]∈R = step-∋ R tt
          (begin
          x₁ , y₀
          ≡⟨ ≡cong (λ x → x , y₀) (≡sym xs1≡x₁) ⟩
          xs (fromℕ< (s≤s (s≤s (z≤n)))) , y₀
          ∎)
        
        w≡τε : ≡τ-carrier ((1 , w) , (zero , emptyF))
        w≡τε with remτ 1 w | remτ zero emptyF | inspect proj₁ (remτ zero emptyF) | w0≡τ⇒remτ[w]≡remτ[tail[w]] 0 w w0≡τ
        w≡τε | .0 , w' | .0 , .w' | [ ≡refl ] | ≡refl with zero ≟ zero
        w≡τε | _ , w' | _ , .w' | [ ≡refl ] | ≡refl | .true because ofʸ ≡refl = λ ()
        w≡τε | _ , w' | _ , .w' | [ ≡refl ] | ≡refl | .false because ofⁿ _ = λ ()

        w↾1≡τε : ((1 , (w ↾ s≤s (s≤s z≤n))) , (zero , emptyF)) ∈ ≡τ-carrier
        w↾1≡τε = step-∋ ≡τ-carrier w≡τε
          (begin
          (1 , w) , (zero , emptyF)
          ≡⟨ ≡cong (λ u → ((1 , u) , (zero , emptyF))) (ex w↾1i≡wi) ⟩
          (1 , (w ↾ s≤s (s≤s z≤n))) , (zero , emptyF)
          ∎)
          where
            w↾1i≡wi : ∀ i → w i ≡ (w ↾ s≤s (s≤s z≤n)) i
            w↾1i≡wi zeroF = ≡refl
    step x₁ y₀ tt xs w p tr with tr zeroF
    step x₁ y₀ tt xs w p tr | tr[0] with xs zeroF | w zeroF | xs (sucF zeroF) | inspect w zeroF | inspect xs (sucF zeroF)
    step x₁ y₀ tt xs w p tr | tt | x₁ | Addτ.τ | x₂ | [ w0≡τ ] | [ xs1≡x₂ ] =
      -- x₁ -τ→ x₂
      (1 , (λ ()) , (s≤s (s≤s z≤n)) , (1 , u) , y₂ , w↾1≡τu , (ys , ≡refl , tr-ys , ≡refl) ,  [xs1,y₂]∈R )
      where
        [xs1,y₂]∈R : R (xs (fromℕ< (s≤s (s≤s (z≤n)))) , y₂ )
        [xs1,y₂]∈R = step-∋ R tt
          (begin
          x₂ , y₂
          ≡⟨ ≡cong (λ x → x , y₂) (≡sym xs1≡x₂) ⟩
          xs (fromℕ< (s≤s (s≤s (z≤n)))) , y₂
          ∎)

        u : Fin 1 → A+τ
        u = (λ zeroF → τ)

        ys : Fin 2 → Y
        ys zeroF = y₀
        ys (sucF zeroF) = y₂
        
        tr-ys : ∀ i → (ys (inject₁ i) , u i , ys (sucF i)) ∈ tr₂
        tr-ys zeroF = tt
        
        w≡τu : ≡τ-carrier ((1 , w) , (1 , u))
        w≡τu with remτ 1 w | remτ 1 u | inspect proj₁ (remτ 1 u) | w0≡τ⇒remτ[w]≡remτ[tail[w]] 0 w w0≡τ
        w≡τu | .0 , w' | .0 , .w' | [ ≡refl ] | ≡refl with zero ≟ zero
        w≡τu | .0 , w' | .0 , .w' | [ ≡refl ] | ≡refl | _ = λ ()

        w↾1≡τu : ((1 , (w ↾ s≤s (s≤s z≤n))) , (1 , u)) ∈ ≡τ-carrier
        w↾1≡τu = step-∋ ≡τ-carrier w≡τu
          (begin
          (1 , w) , (1 , u)
          ≡⟨ ≡cong (λ v → ((1 , v) , (1 , u))) (ex w↾1i≡wi) ⟩
          (1 , (w ↾ s≤s (s≤s z≤n))) , (1 , u)
          ∎)
          where
            w↾1i≡wi : ∀ i → w i ≡ (w ↾ s≤s (s≤s z≤n)) i
            w↾1i≡wi zeroF = ≡refl
    step x₂ y₂ tt xs w p tr with tr zeroF
    step x₂ y₂ tt xs w p tr | tr[0] with xs zeroF | w zeroF | xs (sucF zeroF) | inspect w zeroF | inspect xs (sucF zeroF)
    step x₂ y₂ tt xs w p tr | tt | x₂ | Addτ.fromA a | x₂ | [ w0≡a ] | [ xs1≡x₂ ] =
      -- x₂ -a→ x₂
      (1 , (λ ()) , (s≤s (s≤s z≤n)) , (1 , u) , y₂ , w↾1≡τu , (ys , ≡refl , tr-ys , ≡refl) ,  [xs1,y₂]∈R )
      where
        [xs1,y₂]∈R : R (xs (fromℕ< (s≤s (s≤s (z≤n)))) , y₂ )
        [xs1,y₂]∈R = step-∋ R tt
          (begin
          x₂ , y₂
          ≡⟨ ≡cong (λ x → x , y₂) (≡sym xs1≡x₂) ⟩
          xs (fromℕ< (s≤s (s≤s (z≤n)))) , y₂
          ∎)

        u : Fin 1 → A+τ
        u = (λ zeroF → fromA a)

        ys : Fin 2 → Y
        ys zeroF = y₂
        ys (sucF zeroF) = y₂
        
        tr-ys : ∀ i → (ys (inject₁ i) , u i , ys (sucF i)) ∈ tr₂
        tr-ys zeroF = tt
        
        lem : (u : FINWord A) → ∀ m → (v : FinWord m A) → u ≡ (m , v)
          → ∃ (λ (proof : m ≡ proj₁ u) → ∀ i → proj₂ u (cast proof i) ≡ v i)
        lem .(m , v) m v ≡refl = ( ≡refl , λ i → ≡cong v (casti≡i {m} {≡refl} i) )

        w≡τu : ≡τ-carrier ((1 , w) , (1 , u))
        w≡τu with remτ 1 w | inspect (remτ 1) w | remτ 1 u | inspect proj₁ (remτ 1 u) | w0≡a⇒remτ[w]≡a∷remτ[tail[w]] 0 w a w0≡a
        w≡τu | .1 , w' | _ | .1 , .w' | [ ≡refl ] | ≡refl with 1 ≟ 1 | w' zeroF | inspect w' zeroF
        w≡τu | _ , w' | [ remτw≡w' ] | _ , .w' | [ ≡refl ] | ≡refl | _ | a | [ w'0≡a ] = w'i≡vi
          where
            v : FinWord 1 A
            v = a ∷ᶠ emptyF
            
            lemma : ∃ (λ proof → ∀ (i : Fin 1) → proj₂ (remτ 1 w) (cast proof i) ≡ w' i)
            lemma = lem (remτ 1 w) 1 w' remτw≡w'

            w'i≡vi : (i : Fin 1) → w' i ≡ v i
            w'i≡vi zeroF = begin w' zeroF ≡⟨ w'0≡a ⟩ a ≡⟨⟩ v zeroF ∎

        w↾1≡τu : ((1 , (w ↾ s≤s (s≤s z≤n))) , (1 , u)) ∈ ≡τ-carrier
        w↾1≡τu = step-∋ ≡τ-carrier w≡τu
          (begin
          (1 , w) , (1 , u)
          ≡⟨ ≡cong (λ v → ((1 , v) , (1 , u))) (ex w↾1i≡wi) ⟩
          (1 , (w ↾ s≤s (s≤s z≤n))) , (1 , u)
          ∎)
          where
            w↾1i≡wi : ∀ i → w i ≡ (w ↾ s≤s (s≤s z≤n)) i
            w↾1i≡wi zeroF = ≡refl

    1-bounded-≡τ-constrained-simulation : [ 1 ]-bounded-[ ≡τ ]-constrained-simulation 
    1-bounded-≡τ-constrained-simulation = aBoundedConstrainedSimulation R final step

    open import QSimulation.Soundness X Y A+τ na₁ na₂
    x≤[≡τ]y : x₀ ≤[ na₁ , na₂ , ≡τ ] y₀
    x≤[≡τ]y = soundness-of-bounded-simulation 1 (s≤s z≤n) ≡τ ≡τ-is-closed-under-concat 1-bounded-≡τ-constrained-simulation (x₀ , y₀) tt

  module 2Bounded where
    R : Pred' (X × Y)
    -- R = { (x₀ , y₀) , (x₂ , y₂) }
    R (x₀ , y₀) = ⊤
    R (x₀ , y₂) = ⊥
    R (x₁ , y₀) = ⊥
    R (x₁ , y₂) = ⊥
    R (x₂ , y₀) = ⊥
    R (x₂ , y₂) = ⊤

    private
      lem : {A B C : Set} {a a' : A} {b b' : B} {c c' : C}
        → (p : a ≡ a')
        → (p' : b ≡ b')
        → (p'' : c ≡ c')
        → (f : A × B × C → Set)
        → f (a , b , c)
        → f (a' , b' , c')
      lem ≡refl ≡refl ≡refl f x = x

      [τ] : FinWord 1 A+τ
      [τ] zeroF = τ
      
      [a'] : FinWord 1 A+τ
      [a'] zeroF = fromA a
      
      [a] : FinWord 1 A
      [a] zeroF = a
      
      {-
      wi≡a'→w≡[a'] : (w : FinWord 1 A+τ) → (∀ i → w i ≡ fromA a) → w ≡ [a']
      wi≡a'→w≡[a'] w p = ex (λ {zeroF → p zeroF })
      
      remτ[a']≡[a] : remτ 1 [a'] ≡ inj 1 [a]
      remτ[a']≡[a] with remτ 1 [a'] | inspect (remτ 1) [a']
      remτ[a']≡[a] | .(suc (proj₁ (remτ 0 (tailF [a'])))) , .(a ∷ᶠ proj₂ (remτ 0 (tailF [a']))) | [ ≡refl ] =
        begin
        suc (proj₁ (remτ 0 (tailF [a']))) , (a ∷ᶠ proj₂ (remτ 0 (tailF [a'])))
        ≡⟨ ≡cong (λ v → (_ , (a ∷ᶠ v))) (remτε≡ε (tailF [a'])) ⟩
        suc (proj₁ (remτ 0 (tailF [a']))) , (a ∷ᶠ ε-word' A)
        ≡⟨ ≡cong (λ v → (_ , v)) (ex (λ {zeroF → ≡refl})) ⟩
        inj (suc (proj₁ (remτ 0 (tailF [a'])))) [a]
        ≡⟨ path-lifting-property [a] (≡cong suc (∣remτε∣≡0 (tailF [a']))) ⟩
        inj (suc zero) [a]
        ∎

      wi≡a'→remτw≡[a] : (w : FinWord 1 A+τ) → (∀ i → w i ≡ fromA a) → remτ 1 w ≡ inj 1 [a]
      wi≡a'→remτw≡[a] w p = begin remτ 1 w ≡⟨ ≡cong (remτ 1) (wi≡a'→w≡[a'] w p) ⟩ remτ 1 [a'] ≡⟨ remτ[a']≡[a] ⟩ inj 1 [a] ∎
      -}
      
      [ττ] : FinWord 2 A+τ
      [ττ] zeroF = τ
      [ττ] (sucF zeroF) = τ
      
      {-
      remτ[ττ]≡ε : remτ 2 [ττ] ≡ inj 0 (ε-word' A)
      remτ[ττ]≡ε with remτ 2 [ττ] | inspect (remτ 2) [ττ]
      remτ[ττ]≡ε | n , e | [ p ] = ≡refl
      -}

      2≢0 : ¬ 2 ≡ 0
      2≢0 = λ ()
      
      2<3 : 2 < 3
      2<3 = s≤s (s≤s (s≤s z≤n))

      1≢0 : ¬ 1 ≡ 0
      1≢0 = λ ()
      
      1<3 : 1 < 3
      1<3 = s≤s (s≤s z≤n)

      {-
      wi≡τ→remτw≡ε : (w : FinWord 2 A+τ) → (∀ i → w i ≡ τ) → remτ 2 (w ↾ 2<3) ≡ inj 0 (ε-word' A)
      wi≡τ→remτw≡ε w p = begin
        remτ 2 (w ↾ 2<3)
        ≡⟨ ≡cong (remτ 2) (ex q) ⟩
        remτ 2 w
        ≡⟨ ≡cong (remτ 2) (ex (λ i → p i )) ⟩
        remτ 2 [ττ]
        ≡⟨ ≡refl ⟩
        inj 0 (ε-word' A)
        ∎
        where
          q : ∀ i → (w ↾ 2<3) i ≡ w i
          q zeroF = ≡refl
          q (sucF zeroF) = ≡refl
      -}

    final : ∀ x y → (x , y) ∈ R → Final[ 2 ][ ≡τ ] R x y
    final x₀ y [x,y]∈R .zero xs w p tr last[xs]∈F₁ (s≤s z≤n) with step-∋ acc₁ last[xs]∈F₁ (≡sym p)
    final x₀ y [x,y]∈R .zero xs w p tr last[xs]∈F₁ (s≤s z≤n) | ()
    final x₁ y [x,y]∈R .zero xs w p tr last[xs]∈F₁ (s≤s z≤n) with step-∋ acc₁ last[xs]∈F₁ (≡sym p)
    final x₁ y [x,y]∈R .zero xs w p tr last[xs]∈F₁ (s≤s z≤n) | ()
    final x₂ y₂ tt .zero xs w p tr last[xs]∈F₁ (s≤s z≤n) =  ((zero , emptyF) , y₂ , (λ i → ≡refl) , tr' , tt)
      where
        tr' : (zero , emptyF) ∈ FINWord-from[ y₂ ]to[ y₂ ] na₂
        tr' = (λ y → y₂) , ≡refl , (λ ()) , ≡refl
    final x₀ y₀ tt .1 xs w p tr last[xs]∈F₁ (s≤s (s≤s z≤n)) with xs (sucF zeroF) | inspect xs (sucF zeroF) | w zeroF | inspect w zeroF
    final x₀ y₀ tt .1 xs w p tr tt (s≤s (s≤s z≤n)) | x₂ | [ p' ] | Addτ.fromA a | [ p'' ] with lem (≡sym p) p'' p' tr₁ (tr zeroF)
    final x₀ y₀ tt .1 xs w p tr tt (s≤s (s≤s z≤n)) | x₂ | [ p' ] | Addτ.fromA a | [ p'' ] | ()
    final x₀ y₀ tt .1 xs w p tr tt (s≤s (s≤s z≤n)) | x₂ | [ p' ] | Addτ.τ | [ p'' ] with lem (≡sym p) p'' p' tr₁ (tr zeroF)
    final x₀ y₀ tt .1 xs w p tr tt (s≤s (s≤s z≤n)) | x₂ | [ p' ] | Addτ.τ | [ p'' ] | ()
    final x₁ y₀ () .1 xs w p tr last[xs]∈F₁ (s≤s (s≤s z≤n))
    final x₁ y₂ () .1 xs w p tr last[xs]∈F₁ (s≤s (s≤s z≤n))
    final x₂ y₂ tt .1 xs w p tr last[xs]∈F₁ (s≤s (s≤s z≤n)) with xs (sucF zeroF) | inspect xs (sucF zeroF) | w zeroF | inspect w zeroF
    final x₂ y₂ tt .1 xs w p tr tt (s≤s (s≤s z≤n)) | x₂ | [ p' ] | Addτ.fromA a | [ p'' ] =
      (inj 1 [a'] , y₂ , (λ i → ≡refl) , ((λ {zeroF → y₂ ; (sucF zeroF) → y₂}) , ≡refl , ((λ {zeroF → tt}) , ≡refl )) , tt)
    final x₂ y₂ tt .1 xs w p tr tt (s≤s (s≤s z≤n)) | x₂ | [ p' ] | Addτ.τ | [ p'' ] with lem (≡sym p) p'' p' tr₁ (tr zeroF)
    final x₂ y₂ tt .1 xs w p tr tt (s≤s (s≤s z≤n)) | x₂ | [ p' ] | Addτ.τ | [ p'' ] | ()

    step : ∀ x y → (x , y) ∈ R → Step[ 2 ][ ≡τ ] R x y
    step x₀ y₀ tt xs w p tr with xs zeroF | w zeroF | xs (sucF zeroF) | w (sucF zeroF) | xs (sucF (sucF zeroF)) | tr zeroF | tr (sucF zeroF)
      | inspect xs zeroF | inspect w zeroF | inspect xs (sucF zeroF) | inspect w (sucF zeroF) | inspect xs (sucF (sucF zeroF))
    step x₀ y₀ tt xs w p tr | x₀ | τ | x₁ | τ | x₂ | tt | tt | [ xs0 ] | [ w0 ] | [ xs1 ] | [ w1 ] | [ xs2 ] =
      (2 , 2≢0 , 2<3 , inj 1 [τ] , y₂ , step-∋ ≡τ-carrier (λ ()) q , (ys , ≡refl , (λ {zeroF → tt}) , ≡refl ) , [last[xs],y₂]∈R)
      {-
      x₀ ──τ─⟶ x₁ ──τ─⟶ x₂
      |R        ≡τ        |R
      y₀ ────────τ─────⟶ y₂
      -}
      where
        ys : FinWord 2 Y
        ys = λ {zeroF → y₀ ; (sucF zeroF) → y₂}

        last[xs]≡x₂ : xs (fromℕ< 2<3) ≡ x₂
        last[xs]≡x₂ = begin xs (fromℕ< 2<3) ≡⟨ xs2 ⟩ x₂ ∎

        [last[xs],y₂]∈R : (xs (fromℕ< 2<3) , y₂) ∈ R
        [last[xs],y₂]∈R = step-∋ R tt (begin
          (x₂ , y₂)
          ≡⟨ ≡cong (λ x → (x , y₂)) (≡sym xs2) ⟩
          (xs (sucF (sucF zeroF)) , y₂)
          ≡⟨⟩
          (xs (fromℕ< 2<3) , y₂)
          ∎)

        q : (inj 2 [ττ] , inj 1 [τ]) ≡ (inj 2 (w ↾ 2<3) , inj 1 [τ])
        q = begin
          (inj 2 [ττ] , inj 1 [τ])
          ≡⟨ ≡cong (λ v → (inj 2 v , inj 1 [τ])) (ex (λ {zeroF → ≡sym w0 ; (sucF zeroF) → ≡sym w1})) ⟩
          (inj 2 (w ↾ 2<3) , inj 1 [τ])
          ∎
    step x₂ y₂ tt xs w p tr with xs zeroF | w zeroF | xs (sucF zeroF) | w (sucF zeroF) | xs (sucF (sucF zeroF)) | tr zeroF | tr (sucF zeroF)
      | inspect xs zeroF | inspect w zeroF | inspect xs (sucF zeroF) | inspect w (sucF zeroF) | inspect xs (sucF (sucF zeroF))
    step x₂ y₂ tt xs w p tr | x₂ | fromA a | x₂ | fromA a | x₂ | tt | tt | [ xs0 ] | [ w0 ] | [ xs1 ] | [ w1 ] | [ xs2 ] =
      (1 , 1≢0 , 1<3 , inj 1 [a'] , y₂ , step-∋ ≡τ-carrier (λ {zeroF → ≡refl}) q , (ys , ≡refl , (λ {zeroF → tt}) , ≡refl) , [last[xs^],y₂]∈R)
      {-
      x₂ ──a─⟶ x₂ ──a─⟶ x₂
      |R   ≡τ   |R
      y₂ ──a─⟶ y₂
      -}
      where
        ys : FinWord 2 Y
        ys = λ {zeroF → y₂ ; (sucF zeroF) → y₂}

        last[xs^]≡x₂ : xs (fromℕ< 1<3) ≡ x₂
        last[xs^]≡x₂ = begin xs (fromℕ< 1<3) ≡⟨ xs1 ⟩ x₂ ∎

        [last[xs^],y₂]∈R : (xs (fromℕ< 1<3) , y₂) ∈ R
        [last[xs^],y₂]∈R = step-∋ R tt (begin
          (x₂ , y₂)
          ≡⟨ ≡cong (λ x → (x , y₂)) (≡sym xs1) ⟩
          (xs (sucF zeroF) , y₂)
          ≡⟨⟩
          (xs (fromℕ< 1<3) , y₂)
          ∎)

        q : (inj 1 [a'] , inj 1 [a']) ≡ (inj 1 (w ↾ 1<3) , inj 1 [a'])
        q = begin
          (inj 1 [a'] , inj 1 [a'])
          ≡⟨ ≡cong (λ v → (inj 1 v , inj 1 [a'])) (ex (λ {zeroF → ≡sym w0})) ⟩
          (inj 1 (w ↾ 1<3) , inj 1 [a'])
          ∎

    2-bounded-≡τ-constrained-simulation : [ 2 ]-bounded-[ ≡τ ]-constrained-simulation 
    2-bounded-≡τ-constrained-simulation = aBoundedConstrainedSimulation R final step

    -- R is not a 1-bounded ≡τ-constrained simulation
    private
      [x₀] : FinWord 1 X
      [x₀] zeroF = x₀
      [x₂] : FinWord 1 X
      [x₂] zeroF = x₀
      [x₀x₁] : FinWord 2 X
      [x₀x₁] = λ { zeroF → x₀ ; (sucF zeroF) → x₁}
    
    ¬step1 : ¬ (∀ x y → (x , y) ∈ R → Step[ 1 ][ ≡τ ] R x y)
    ¬step1 1-bounded-step with 1-bounded-step x₀ y₀ tt [x₀x₁] [τ] ≡refl (λ {zeroF → tt})
    ¬step1 1-bounded-step | .zero , ¬k≡0 , s≤s z≤n , _ with ¬k≡0 ≡refl
    ¬step1 1-bounded-step | .zero , ¬k≡0 , s≤s z≤n , _ | ()
    ¬step1 1-bounded-step | .1 , ¬k≡0 , s≤s (s≤s z≤n) , _ , y₀ , _ , _ , [x₁,y₀]∈R = [x₁,y₀]∈R
    ¬step1 1-bounded-step | .1 , ¬k≡0 , s≤s (s≤s z≤n) , _ , y₂ , _ , _ , [x₁,y₂]∈R = [x₁,y₂]∈R

module Fig-1-2 where
  data A : Set where
    a : A
    b : A

  open Substr A

  module NA₁ where
    data X : Set where
      x₀ : X
      x₂ : X
  
    tr₁ : Pred' (X × A × X)
    tr₁ (x₀ , a , x₂) = ⊤
    tr₁ (x₂ , b , x₂) = ⊤
    tr₁ _ = ⊥

    acc₁ : Pred' X
    acc₁ x₀ = ⊥
    acc₁ x₂ = ⊤

    init₁ : Pred' X
    init₁ x₀ = ⊤
    init₁ x₂ = ⊥

    na₁ : NA X A
    na₁ = anNA tr₁ init₁ acc₁
  open NA₁

  module NA₂ where
    data Y : Set where
      y₀ : Y
      y₁ : Y
      y₂ : Y
      
    tr₂ : Pred' (Y × A × Y)
    tr₂ (y₀ , a , y₁) = ⊤
    tr₂ (y₁ , b , y₂) = ⊤
    tr₂ (y₂ , b , y₂) = ⊤
    tr₂ _ = ⊥
    
    acc₂ : Pred' Y
    acc₂ y₀ = ⊥
    acc₂ y₁ = ⊥
    acc₂ y₂ = ⊤
  
    init₂ : Pred' Y
    init₂ y₀ = ⊤
    init₂ y₁ = ⊥
    init₂ y₂ = ⊥
  
    na₂ : NA Y A
    na₂ = anNA tr₂ init₂ acc₂
  open NA₂

  open QSimulationBase A X Y na₁ na₂
  
  module 1Bounded-a where
    R : Pred' (X × Y)
    -- R = { (x₀, y₀), (x₂, y₂) }
    R (x₀ , y₀) = ⊤
    R (x₂ , y₀) = ⊥
    R (x₀ , y₁) = ⊥
    R (x₂ , y₁) = ⊥
    R (x₀ , y₂) = ⊥
    R (x₂ , y₂) = ⊤

    final : ∀ x y → (x , y) ∈ R → Final[ 1 ][ ⊑substr ] R x y
    final .(xs zeroF) y [x,y]∈R zero xs w ≡refl tr lastxs∈F₁ (s≤s z≤n) with xs zeroF
    final .(xs zeroF) y₂ [x,y]∈R zero xs w ≡refl tr lastxs∈F₁ (s≤s z≤n) | x₂ =
      ((0 , λ ()) , y₂ , ((λ n → n) , (λ ()) , (λ ())) , ((λ x → y₂) , ≡refl , (λ ()) , ≡refl) , tt)

    step : ∀ x y → (x , y) ∈ R → Step[ 1 ][ ⊑substr ] R x y
    step .(xs zeroF) y [x,y]∈R xs w ≡refl tr with tr zeroF 
    step .(xs zeroF) y [x,y]∈R xs w ≡refl tr | tr0 with xs zeroF | w zeroF | xs (sucF zeroF) | inspect w zeroF | inspect xs (sucF zeroF)
    step .(xs zeroF) y₀ [x,y]∈R xs w ≡refl tr | tr0 | x₀ | a | x₂ | [ p ] | [ q ] =
      (1 , (λ ()) , s≤s (s≤s z≤n) , (2 , u) , y₂ , (f , f-is-monotone , λ {zeroF → p}) , (ys , ≡refl , tr-ys , ≡refl) , [lastxs,lastys]∈R)
      where
        u : FinWord 2 A
        u zeroF = a
        u (sucF zeroF) = b
    
        ys : FinWord 3 Y
        ys zeroF = y₀
        ys (sucF zeroF) = y₁
        ys (sucF (sucF zeroF)) = y₂

        f : Fin 1 → Fin 2
        f zeroF = zeroF

        f-is-monotone : f is-monotone
        f-is-monotone zeroF zeroF i<j = i<j
        f-is-monotone zeroF (sucF ()) i<j

        tr-ys : (i : Fin 2) → tr₂ (ys (inject₁ i) , u i , ys (sucF i))
        tr-ys zeroF = tt
        tr-ys (sucF zeroF) = tt
        
        [lastxs,lastys]∈R : (xs (fromℕ< (s≤s (s≤s z≤n))) , y₂) ∈ R
        [lastxs,lastys]∈R with xs (fromℕ< (s≤s (s≤s z≤n)))
        [lastxs,lastys]∈R | x₂ = tt
    step .(xs zeroF) y₂ [x,y]∈R xs w ≡refl tr | tr0 | x₂ | b | x₂ | [ p ] | [ q ] =
      (1 , (λ ()) , s≤s (s≤s z≤n) , (1 , u) , y₂ , (f , f-is-monotone , λ {zeroF → p} ) , (ys , ≡refl , (λ {zeroF → tt}) , ≡refl) , [lastxs,lastys]∈R )
      where
        u : FinWord 1 A
        u zeroF = b
        
        f : Fin 1 → Fin 1
        f zeroF = zeroF

        f-is-monotone : f is-monotone
        f-is-monotone zeroF zeroF i<j = i<j
        f-is-monotone zeroF (sucF ()) i<j

        ys : FinWord 2 Y
        ys zeroF = y₂
        ys (sucF zeroF) = y₂

        [lastxs,lastys]∈R : (xs (fromℕ< (s≤s (s≤s z≤n))) , y₂) ∈ R
        [lastxs,lastys]∈R with xs (fromℕ< (s≤s (s≤s z≤n)))
        [lastxs,lastys]∈R | x₂ = tt

module Fig-1-3 where
  data A : Set where
    a : A
    b : A

  open Subset A
  
  [a] : PA
  [a] a = true
  [a] b = false

  [b] : PA
  [b] a = false
  [b] b = true
  
  [a,b] : PA
  [a,b] a = true
  [a,b] b = true

  module NA₁ where
    data X : Set where
      x₀ : X
      x₁ : X
      x₂ : X
  
    tr₁ : Pred' (X × PA × X)
    tr₁ (x₀ , S , x₁) = (S a ∧ not (S b)) ≡ true -- S = { a }
    tr₁ (x₁ , S , x₂) = (not (S a) ∧ S b) ≡ true -- S = { b }
    tr₁ (x₂ , S , x₂) = (S a ∧ not (S b)) ≡ true -- S = { a }
    tr₁ _ = ⊥

    acc₁ : Pred' X
    acc₁ x₀ = ⊥
    acc₁ x₁ = ⊥
    acc₁ x₂ = ⊤

    init₁ : Pred' X
    init₁ x₀ = ⊤
    init₁ x₁ = ⊥
    init₁ x₂ = ⊥

    na₁ : NA X PA
    na₁ = anNA tr₁ init₁ acc₁
  open NA₁

  module NA₂ where
    data Y : Set where
      y₀ : Y
      y₁ : Y
      y₂ : Y
      
    tr₂ : Pred' (Y × PA × Y)
    tr₂ (y₀ , S , y₁) = S a ∧ S b       ≡ true -- S = { a , b }
    tr₂ (y₁ , S , y₂) = not (S a) ∧ S b ≡ true -- S = { b }
    tr₂ (y₂ , S , y₂) = S a ∧ S b       ≡ true -- S = { a , b }
    tr₂ _ = ⊥
    
    acc₂ : Pred' Y
    acc₂ y₀ = ⊥
    acc₂ y₁ = ⊥
    acc₂ y₂ = ⊤
  
    init₂ : Pred' Y
    init₂ y₀ = ⊤
    init₂ y₁ = ⊥
    init₂ y₂ = ⊥
  
    na₂ : NA Y PA
    na₂ = anNA tr₂ init₂ acc₂
  open NA₂
  
  open QSimulationBase PA X Y na₁ na₂
  
  module 1Bounded where
    R : Pred' (X × Y)
    -- R = { (x₀ , y₀) , (x₁ , y₁) , (x₂ , y₂) }
    R (x₀ , y₀) = ⊤
    R (x₀ , y₁) = ⊥
    R (x₀ , y₂) = ⊥
    
    R (x₁ , y₀) = ⊥
    R (x₁ , y₁) = ⊤
    R (x₁ , y₂) = ⊥
    
    R (x₂ , y₀) = ⊥
    R (x₂ , y₁) = ⊥
    R (x₂ , y₂) = ⊤

    final : ∀ x y → (x , y) ∈ R → Final[ 1 ][ ⊆* ] R x y
    final .(xs zeroF) y [x,y]∈R zero xs w ≡refl tr xs0∈F₁ (s≤s z≤n) with xs zeroF
    final .(xs zeroF) y₂ [x,y]∈R zero xs w ≡refl tr tt (s≤s z≤n) | x₂ =
      ((0 , λ ()) , y₂ , (λ ()) , ((λ { zeroF → y₂ }) , ≡refl , (λ ()) , ≡refl) ,  tt)
    
    p→ᵇtrue : ∀ {p : Bool} → p →ᵇ true
    p→ᵇtrue {false} = f→ᵇt
    p→ᵇtrue {true} = b→ᵇb
    
    step : ∀ x y → (x , y) ∈ R → Step[ 1 ][ ⊆* ] R x y
    step x y [x,y]∈R xs w ≡refl tr with tr zeroF 
    step x y [x,y]∈R xs w ≡refl tr | tr0 with xs zeroF | w zeroF | xs (sucF zeroF) | inspect w zeroF | inspect xs (sucF zeroF)
    step .(xs zeroF) y₀ [x,y]∈R xs w ≡refl tr | tr0 | x₀ | .(w zeroF) | x₁ | [ ≡refl ] | [ _ ] =
      (1 , (λ ()) , (s≤s (s≤s z≤n)) , inj 1 u , y₁ , w⊆*u , (ys , ≡refl , (λ {zeroF → ys0-u0-ys1 }) , ≡refl) , [lastxs,lastys]∈R)
      where
        u : FinWord 1 PA
        u zeroF = [a,b]

        ¬[p∧false≡true] : ∀ {p : Bool} → p ∧ false ≡ true → ⊥
        ¬[p∧false≡true] {false} = λ ()
        ¬[p∧false≡true] {true} = λ ()
        
        w⊆*u : (inj 1 (w ↾ (s≤s (s≤s z≤n))) , inj 1 u) ∈ ⊆*-carrier
        w⊆*u zeroF a with (w ↾ (s≤s (s≤s z≤n))) zeroF a
        w⊆*u zeroF a | true = b→ᵇb
        w⊆*u zeroF b with (w ↾ (s≤s (s≤s z≤n))) zeroF b
        w⊆*u zeroF b | false = f→ᵇt
        w⊆*u zeroF b | true with ¬[p∧false≡true] tr0
        w⊆*u zeroF b | true | ()

        ys : FinWord 2 Y
        ys zeroF = y₀
        ys (sucF zeroF) = y₁

        ys0-u0-ys1 : (y₀ , u zeroF , y₁) ∈ tr₂
        ys0-u0-ys1 = ≡refl

        [lastxs,lastys]∈R : (xs (fromℕ< (s≤s (s≤s z≤n))) , y₁) ∈ R
        [lastxs,lastys]∈R with xs (fromℕ< (s≤s (s≤s z≤n)))
        [lastxs,lastys]∈R | x₁ = tt
    step .(xs zeroF) y₁ [x,y]∈R xs w ≡refl tr | tr0 | x₁ | .(w zeroF) | x₂ | [ ≡refl ] | [ _ ] =
      (1 , (λ ()) , (s≤s (s≤s z≤n)) , inj 1 u , y₂ , w⊆*u , (ys , ≡refl ,  (λ { zeroF → ys0-u0-ys1}) , ≡refl) , [lastxs,lastys]∈R)
      where
        u : FinWord 1 PA
        u zeroF = [b]
        
        w⊆*u : (inj 1 (w ↾ (s≤s (s≤s z≤n))) , inj 1 u) ∈ ⊆*-carrier
        w⊆*u zeroF a with (w ↾ (s≤s (s≤s z≤n))) zeroF a
        w⊆*u zeroF a | false = b→ᵇb
        w⊆*u zeroF b with (w ↾ (s≤s (s≤s z≤n))) zeroF a
        w⊆*u zeroF b | false = p→ᵇtrue
    
        ys : FinWord 2 Y
        ys zeroF = y₁
        ys (sucF zeroF) = y₂

        ys0-u0-ys1 : (y₁ , u zeroF , y₂) ∈ tr₂
        ys0-u0-ys1 = ≡refl

        [lastxs,lastys]∈R : (xs (fromℕ< (s≤s (s≤s z≤n))) , y₂) ∈ R
        [lastxs,lastys]∈R with xs (fromℕ< (s≤s (s≤s z≤n)))
        [lastxs,lastys]∈R | x₂ = tt
    step .(xs zeroF) y₂ [x,y]∈R xs w ≡refl tr | tr0 | x₂ | .(w zeroF) | x₂ | [ ≡refl ] | [ _ ] =
      (1 , (λ ()) , (s≤s (s≤s z≤n)) , inj 1 u , y₂ , w⊆*u , (ys , ≡refl ,  (λ { zeroF → ys0-u0-ys1}) , ≡refl) , [lastxs,lastys]∈R)
      where
        u : FinWord 1 PA
        u zeroF = [a,b]
        
        w⊆*u : (inj 1 (w ↾ (s≤s (s≤s z≤n))) , inj 1 u) ∈ ⊆*-carrier
        w⊆*u zeroF a with (w ↾ (s≤s (s≤s z≤n))) zeroF a
        w⊆*u zeroF a | false = f→ᵇt
        w⊆*u zeroF a | true = b→ᵇb
        w⊆*u zeroF b = p→ᵇtrue
    
        ys : FinWord 2 Y
        ys zeroF = y₂
        ys (sucF zeroF) = y₂

        ys0-u0-ys1 : (y₂ , u zeroF , y₂) ∈ tr₂
        ys0-u0-ys1 = ≡refl

        [lastxs,lastys]∈R : (xs (fromℕ< (s≤s (s≤s z≤n))) , y₂) ∈ R
        [lastxs,lastys]∈R with xs (fromℕ< (s≤s (s≤s z≤n)))
        [lastxs,lastys]∈R | x₂ = tt
    1-bounded-⊆*-constrained-simulation : [ 1 ]-bounded-[ ⊆* ]-constrained-simulation 
    1-bounded-⊆*-constrained-simulation = aBoundedConstrainedSimulation R final step

    open import QSimulation.Soundness X Y PA na₁ na₂
    x≤[⊆*]y : x₀ ≤[ na₁ , na₂ , ⊆* ] y₀
    x≤[⊆*]y = soundness-of-bounded-simulation 1 (s≤s z≤n) ⊆* ⊆*-is-closed-under-concat 1-bounded-⊆*-constrained-simulation (x₀ , y₀) tt
     