module Example where

open import Data.Bool
  using (true; false; Bool; not; _∧_)
  renaming (f≤t to f→ᵇt; b≤b to b→ᵇb; _≤_ to _→ᵇ_)
open import Data.Nat
open import Data.Nat.Properties
  using (≤-reflexive; ≤-trans; ≤-step; _≟_)
open import Data.Integer
  using (ℤ; 0ℤ; 1ℤ)
  renaming (+_ to +ℤ_ ; -[1+_] to -[1+_] ;_≤_ to _≤ᶻ_; +≤+ to +≤ᶻ+; _+_ to _+ᶻ_)
open import Data.Integer.Properties
  using ()
  renaming (≤-reflexive to ≤ᶻ-reflexive; ≤-trans to ≤ᶻ-trans; +-identityˡ to +ᶻ-identityˡ; +-identityʳ to +ᶻ-identityʳ; +-assoc to +ᶻ-assoc; +-mono-≤ to +ᶻ-mono-≤ᶻ)
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
open import Level renaming (zero to lzero; suc to lsuc)

open import Base
open import Word
open import NA
open import QSimulation.Base
open import QSimulation.Lemma using (casti≡i)
open import QSimulation.InstanceOfPreorder

private
  lem-tr : {A B C : Set} {a a' : A} {b b' : B} {c c' : C}
    → (p : a ≡ a')
    → (p' : b ≡ b')
    → (p'' : c ≡ c')
    → (f : A × B × C → Set)
    → f (a , b , c)
    → f (a' , b' , c')
  lem-tr ≡refl ≡refl ≡refl f x = x


1>0 : 1 > 0
1>0 = s≤s z≤n

2>0 : 2 > 0
2>0 = s≤s z≤n

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

    final : ∀ x y → (x , y) ∈ R → Final[ 1 ][ 1>0 ][ ≡τ ] R x y
    final x₀ y [x,y]∈R zero xs w p tr x₀∈F₁ (s≤s z≤n) with step-∋ acc₁ x₀∈F₁ (≡sym p)
    final x₀ y [x,y]∈R zero xs w p tr x₀∈F₁ (s≤s z≤n) | ()
    final x₁ y [x,y]∈R zero xs w p tr x₁∈F₁ (s≤s z≤n) with step-∋ acc₁ x₁∈F₁ (≡sym p)
    final x₁ y [x,y]∈R zero xs w p tr x₁∈F₁ (s≤s z≤n) | ()
    final x₂ y₂ tt zero xs w p tr x₂∈F₂ (s≤s z≤n) = ((zero , emptyF) , y₂ , (λ i → ≡refl) , tr' , tt)
      where
        tr' : (zero , emptyF) ∈ FINWord-from[ y₂ ]to[ y₂ ] na₂
        tr' = (λ y → y₂) , ≡refl , (λ ()) , ≡refl

    step : ∀ x y → (x , y) ∈ R → Step[ 1 ][ 1>0 ][ ≡τ ] R x y
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

    1-bounded-≡τ-constrained-simulation : [ 1 ][ 1>0 ]-bounded-[ ≡τ ]-constrained-simulation lzero
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
      [τ] : FinWord 1 A+τ
      [τ] zeroF = τ
      
      [a'] : FinWord 1 A+τ
      [a'] zeroF = fromA a
      
      [a] : FinWord 1 A
      [a] zeroF = a
      
      [ττ] : FinWord 2 A+τ
      [ττ] zeroF = τ
      [ττ] (sucF zeroF) = τ

      2≢0 : ¬ 2 ≡ 0
      2≢0 = λ ()
      
      2<3 : 2 < 3
      2<3 = s≤s (s≤s (s≤s z≤n))

      1≢0 : ¬ 1 ≡ 0
      1≢0 = λ ()
      
      1<3 : 1 < 3
      1<3 = s≤s (s≤s z≤n)

    final : ∀ x y → (x , y) ∈ R → Final[ 2 ][ 2>0 ][ ≡τ ] R x y
    final x₀ y [x,y]∈R .zero xs w p tr last[xs]∈F₁ (s≤s z≤n) with step-∋ acc₁ last[xs]∈F₁ (≡sym p)
    final x₀ y [x,y]∈R .zero xs w p tr last[xs]∈F₁ (s≤s z≤n) | ()
    final x₁ y [x,y]∈R .zero xs w p tr last[xs]∈F₁ (s≤s z≤n) with step-∋ acc₁ last[xs]∈F₁ (≡sym p)
    final x₁ y [x,y]∈R .zero xs w p tr last[xs]∈F₁ (s≤s z≤n) | ()
    final x₂ y₂ tt .zero xs w p tr last[xs]∈F₁ (s≤s z≤n) =  ((zero , emptyF) , y₂ , (λ i → ≡refl) , tr' , tt)
      where
        tr' : (zero , emptyF) ∈ FINWord-from[ y₂ ]to[ y₂ ] na₂
        tr' = (λ y → y₂) , ≡refl , (λ ()) , ≡refl
    final x₀ y₀ tt .1 xs w p tr last[xs]∈F₁ (s≤s (s≤s z≤n)) with xs (sucF zeroF) | inspect xs (sucF zeroF) | w zeroF | inspect w zeroF
    final x₀ y₀ tt .1 xs w p tr tt (s≤s (s≤s z≤n)) | x₂ | [ p' ] | Addτ.fromA a | [ p'' ] with lem-tr (≡sym p) p'' p' tr₁ (tr zeroF)
    final x₀ y₀ tt .1 xs w p tr tt (s≤s (s≤s z≤n)) | x₂ | [ p' ] | Addτ.fromA a | [ p'' ] | ()
    final x₀ y₀ tt .1 xs w p tr tt (s≤s (s≤s z≤n)) | x₂ | [ p' ] | Addτ.τ | [ p'' ] with lem-tr (≡sym p) p'' p' tr₁ (tr zeroF)
    final x₀ y₀ tt .1 xs w p tr tt (s≤s (s≤s z≤n)) | x₂ | [ p' ] | Addτ.τ | [ p'' ] | ()
    final x₁ y₀ () .1 xs w p tr last[xs]∈F₁ (s≤s (s≤s z≤n))
    final x₁ y₂ () .1 xs w p tr last[xs]∈F₁ (s≤s (s≤s z≤n))
    final x₂ y₂ tt .1 xs w p tr last[xs]∈F₁ (s≤s (s≤s z≤n)) with xs (sucF zeroF) | inspect xs (sucF zeroF) | w zeroF | inspect w zeroF
    final x₂ y₂ tt .1 xs w p tr tt (s≤s (s≤s z≤n)) | x₂ | [ p' ] | Addτ.fromA a | [ p'' ] =
      (inj 1 [a'] , y₂ , (λ i → ≡refl) , ((λ {zeroF → y₂ ; (sucF zeroF) → y₂}) , ≡refl , ((λ {zeroF → tt}) , ≡refl )) , tt)
    final x₂ y₂ tt .1 xs w p tr tt (s≤s (s≤s z≤n)) | x₂ | [ p' ] | Addτ.τ | [ p'' ] with lem-tr (≡sym p) p'' p' tr₁ (tr zeroF)
    final x₂ y₂ tt .1 xs w p tr tt (s≤s (s≤s z≤n)) | x₂ | [ p' ] | Addτ.τ | [ p'' ] | ()

    step : ∀ x y → (x , y) ∈ R → Step[ 2 ][ 2>0 ][ ≡τ ] R x y
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

    2-bounded-≡τ-constrained-simulation : [ 2 ][ 2>0 ]-bounded-[ ≡τ ]-constrained-simulation lzero
    2-bounded-≡τ-constrained-simulation = aBoundedConstrainedSimulation R final step

    -- R is not a 1-bounded ≡τ-constrained simulation
    private
      [x₀] : FinWord 1 X
      [x₀] zeroF = x₀
      [x₂] : FinWord 1 X
      [x₂] zeroF = x₀
      [x₀x₁] : FinWord 2 X
      [x₀x₁] = λ { zeroF → x₀ ; (sucF zeroF) → x₁}
    
    ¬step1 : ¬ (∀ x y → (x , y) ∈ R → Step[ 1 ][ 1>0 ][ ≡τ ] R x y)
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

    final : ∀ x y → (x , y) ∈ R → Final[ 1 ][ 1>0 ][ ⊑substr ] R x y
    final .(xs zeroF) y [x,y]∈R zero xs w ≡refl tr lastxs∈F₁ (s≤s z≤n) with xs zeroF
    final .(xs zeroF) y₂ [x,y]∈R zero xs w ≡refl tr lastxs∈F₁ (s≤s z≤n) | x₂ =
      ((0 , λ ()) , y₂ , ((λ n → n) , (λ ()) , (λ ())) , ((λ x → y₂) , ≡refl , (λ ()) , ≡refl) , tt)

    step : ∀ x y → (x , y) ∈ R → Step[ 1 ][ 1>0 ][ ⊑substr ] R x y
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

    final : ∀ x y → (x , y) ∈ R → Final[ 1 ][ 1>0 ][ ⊆* ] R x y
    final .(xs zeroF) y [x,y]∈R zero xs w ≡refl tr xs0∈F₁ (s≤s z≤n) with xs zeroF
    final .(xs zeroF) y₂ [x,y]∈R zero xs w ≡refl tr tt (s≤s z≤n) | x₂ =
      ((0 , λ ()) , y₂ , (λ ()) , ((λ { zeroF → y₂ }) , ≡refl , (λ ()) , ≡refl) ,  tt)
    
    p→ᵇtrue : ∀ {p : Bool} → p →ᵇ true
    p→ᵇtrue {false} = f→ᵇt
    p→ᵇtrue {true} = b→ᵇb
    
    step : ∀ x y → (x , y) ∈ R → Step[ 1 ][ 1>0 ][ ⊆* ] R x y
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
    1-bounded-⊆*-constrained-simulation : [ 1 ][ 1>0 ]-bounded-[ ⊆* ]-constrained-simulation lzero
    1-bounded-⊆*-constrained-simulation = aBoundedConstrainedSimulation R final step

    open import QSimulation.Soundness X Y PA na₁ na₂
    x≤[⊆*]y : x₀ ≤[ na₁ , na₂ , ⊆* ] y₀
    x≤[⊆*]y = soundness-of-bounded-simulation 1 (s≤s z≤n) ⊆* ⊆*-is-closed-under-concat 1-bounded-⊆*-constrained-simulation (x₀ , y₀) tt
     
  module 2-bounded where
    R : Pred' (X × Y)
    -- R = { (x₀ , y₀) , (x₂ , y₂) }
    R (x₀ , y₀) = ⊤
    R (x₀ , y₁) = ⊥
    R (x₀ , y₂) = ⊥

    R (x₁ , y₀) = ⊥
    R (x₁ , y₁) = ⊥
    R (x₁ , y₂) = ⊥

    R (x₂ , y₀) = ⊥
    R (x₂ , y₁) = ⊥
    R (x₂ , y₂) = ⊤

    final : ∀ x y → (x , y) ∈ R → Final[ 2 ][ 2>0 ][ ⊆* ] R x y
    final x₀ y₀ tt zero xs w x₀≡xs0 tr xs0∈F₁ (s≤s z≤n) with step-∋ acc₁ xs0∈F₁ (≡sym x₀≡xs0)
    final x₀ y₀ tt zero xs w x₀≡xs0 tr xs0∈F₁ (s≤s z≤n) | ()
    final x₁ y₀ () zero xs w x₁≡xs0 tr xs0∈F₁ (s≤s z≤n)
    final x₁ y₁ () zero xs w x₁≡xs0 tr xs0∈F₁ (s≤s z≤n)
    final x₁ y₂ () zero xs w x₁≡xs0 tr xs0∈F₁ (s≤s z≤n)
    final x₂ y₂ tt zero xs w x₂≡xs0 tr xs0∈F₁ (s≤s z≤n) =
      ((0 , λ ()) , y₂ , (λ ()) , ((λ {zeroF → y₂}) , ≡refl , (λ ()) , ≡refl) , tt)
    final x₀ y₀ tt (suc zero) xs w x₀≡xs0 tr xs1∈F₁ (s≤s (s≤s z≤n)) with xs (sucF zeroF) | inspect xs (sucF zeroF) | w zeroF | inspect w zeroF | tr zeroF
    final x₀ y₀ tt (suc zero) xs w x₀≡xs0 tr xs1∈F₁ (s≤s (s≤s z≤n)) | x₂ | [ xs1≡ ] | w1 | [ w≡ ] | tr0 with lem-tr (≡sym x₀≡xs0) w≡ xs1≡ tr₁ (tr zeroF)
    final x₀ y₀ tt (suc zero) xs w x₀≡xs0 tr xs1∈F₁ (s≤s (s≤s z≤n)) | x₂ | [ xs1≡ ] | w1 | [ w≡ ] | tr0 | ()
    final x₁ y₀ () (suc zero) xs w x₁≡xs0 tr xs1∈F₁ (s≤s (s≤s z≤n))
    final x₁ y₁ () (suc zero) xs w x₁≡xs0 tr xs1∈F₁ (s≤s (s≤s z≤n))
    final x₁ y₂ () (suc zero) xs w x₁≡xs0 tr xs1∈F₁ (s≤s (s≤s z≤n))
    final x₂ y₂ tt (suc zero) xs w x₂≡xs0 tr xs1∈F₁ (s≤s (s≤s z≤n)) with xs (sucF zeroF) | inspect xs (sucF zeroF) | tr zeroF
    final x₂ y₂ tt (suc zero) xs w x₂≡xs0 tr xs1∈F₁ (s≤s (s≤s z≤n)) | x₂ | [ xs1≡ ] | tr0 with lem-tr (≡sym x₂≡xs0) ≡refl xs1≡ tr₁ (tr zeroF)
    final x₂ y₂ tt (suc zero) xs w x₂≡xs0 tr xs1∈F₁ (s≤s (s≤s z≤n)) | x₂ | [ xs1≡ ] | tr0 | P with w zeroF a | inspect (w zeroF) a | w zeroF b | inspect (w zeroF) b
    final x₂ y₂ tt (suc zero) xs w x₂≡xs0 tr xs1∈F₁ (s≤s (s≤s z≤n)) | x₂ | [ xs1≡ ] | tr0 | P | true | [ w0a≡true ] | false | [ w0b≡false ] =
      ((1 , (λ {zeroF → [a,b]})) , y₂ , (λ {zeroF → w0⊆[a,b]} ) , ((λ {zeroF → y₂ ; (sucF zeroF) → y₂}) , ≡refl , (λ {zeroF → ≡refl}) , ≡refl) , tt )
      where
        w0⊆[a,b] : subset (w zeroF , [a,b])
        w0⊆[a,b] a with w zeroF a
        w0⊆[a,b] a | true = b→ᵇb
        w0⊆[a,b] b with w zeroF b
        w0⊆[a,b] b | false = f→ᵇt
    final x y [x,y]∈R (suc (suc n)) xs w x≡xs0 tr last[xs]∈F₁ (s≤s (s≤s ()))
    
    step : ∀ x y → (x , y) ∈ R → Step[ 2 ][ 2>0 ][ ⊆* ] R x y
    step x₀ y₀ tt xs w x₀≡xs0 tr with xs zeroF | xs (sucF zeroF) | xs (sucF (sucF zeroF)) | tr zeroF | tr (sucF zeroF)
      | inspect xs zeroF | inspect xs (sucF zeroF) | inspect xs (sucF (sucF zeroF))
    step x₀ y₀ tt xs w x₀≡xs0 tr | x₀ | x₁ | x₂ | tr0 | tr1 | [ xs0≡x₀ ] | [ xs1≡x₁ ] | [ xs2≡x₂ ] =
      (2 , (λ ()) , (s≤s (s≤s (s≤s z≤n))) , (2 , w') , y₂ , (λ {zeroF → w0⊆[a,b] ; (sucF zeroF) → w1⊆[b]}) , (ys , ≡refl , tr' , ≡refl) , [xs2,y₂]∈R)
      where
        w' : FinWord 2 PA
        w' zeroF = [a,b]
        w' (sucF zeroF) = [b]

        ys : FinWord 3 Y
        ys zeroF = y₀
        ys (sucF zeroF) = y₁
        ys (sucF (sucF zeroF)) = y₂

        w0⊆[a,b] : subset ((w ↾ s≤s (s≤s (s≤s z≤n))) zeroF , w' zeroF)
        w0⊆[a,b] a with (w ↾ s≤s (s≤s (s≤s z≤n))) zeroF a
        w0⊆[a,b] a | true = b→ᵇb
        w0⊆[a,b] b with (w ↾ s≤s (s≤s (s≤s z≤n))) zeroF b
        w0⊆[a,b] b | true = b→ᵇb
        w0⊆[a,b] b | false = f→ᵇt

        w1⊆[b] : subset ((w ↾ s≤s (s≤s (s≤s z≤n))) (sucF zeroF) , w' (sucF zeroF))
        w1⊆[b] a with (w ↾ s≤s (s≤s (s≤s z≤n))) (sucF zeroF) a
        w1⊆[b] a | false = b→ᵇb
        w1⊆[b] b with (w ↾ s≤s (s≤s (s≤s z≤n))) (sucF zeroF) b
        w1⊆[b] b | false = f→ᵇt
        w1⊆[b] b | true = b→ᵇb

        tr' : (i : Fin 2) → tr₂ (ys (inject₁ i) , w' i , ys (sucF i))
        tr' zeroF = ≡refl
        tr' (sucF zeroF) = ≡refl

        [xs2,y₂]∈R : R (xs (fromℕ< (s≤s (s≤s (s≤s z≤n)))) , y₂)
        [xs2,y₂]∈R with xs (fromℕ< (s≤s (s≤s (s≤s z≤n))))
        [xs2,y₂]∈R | x₂ = tt
    step x₁ y₀ () xs w x₁≡xs0 tr
    step x₁ y₁ () xs w x₁≡xs0 tr
    step x₁ y₂ () xs w x₁≡xs0 tr
    step x₂ y₂ tt xs w x₂≡xs0 tr with xs zeroF | xs (sucF zeroF) | xs (sucF (sucF zeroF)) | tr zeroF | tr (sucF zeroF)
      | inspect xs zeroF | inspect xs (sucF zeroF) | inspect xs (sucF (sucF zeroF))
    step x₂ y₂ tt xs w x₀≡xs0 tr | x₂ | x₂ | x₂ | tr0 | tr1 | [ xs0≡x₂ ] | [ xs1≡x₂ ] | [ xs2≡x₂ ] =
      (2 , (λ ()) , (s≤s (s≤s (s≤s z≤n))) , (2 , w') , y₂ , (λ {zeroF → w0⊆[a,b] ; (sucF zeroF) → w1⊆[a,b]}) , (ys , ≡refl , tr' , ≡refl) , [xs2,y₂]∈R)
      where
        w' : FinWord 2 PA
        w' zeroF = [a,b]
        w' (sucF zeroF) = [a,b]

        ys : FinWord 3 Y
        ys zeroF = y₂
        ys (sucF zeroF) = y₂
        ys (sucF (sucF zeroF)) = y₂

        w0⊆[a,b] : subset ((w ↾ s≤s (s≤s (s≤s z≤n))) zeroF , w' zeroF)
        w0⊆[a,b] a with (w ↾ s≤s (s≤s (s≤s z≤n))) zeroF a
        w0⊆[a,b] a | true = b→ᵇb
        w0⊆[a,b] b with (w ↾ s≤s (s≤s (s≤s z≤n))) zeroF b
        w0⊆[a,b] b | true = b→ᵇb
        w0⊆[a,b] b | false = f→ᵇt

        w1⊆[a,b] : subset ((w ↾ s≤s (s≤s (s≤s z≤n))) (sucF zeroF) , w' (sucF zeroF))
        w1⊆[a,b] a with (w ↾ s≤s (s≤s (s≤s z≤n))) (sucF zeroF) a
        w1⊆[a,b] a | true = b→ᵇb
        w1⊆[a,b] b with (w ↾ s≤s (s≤s (s≤s z≤n))) (sucF zeroF) b
        w1⊆[a,b] b | false = f→ᵇt
        w1⊆[a,b] b | true = b→ᵇb

        tr' : (i : Fin 2) → tr₂ (ys (inject₁ i) , w' i , ys (sucF i))
        tr' zeroF = ≡refl
        tr' (sucF zeroF) = ≡refl

        [xs2,y₂]∈R : R (xs (fromℕ< (s≤s (s≤s (s≤s z≤n)))) , y₂)
        [xs2,y₂]∈R with xs (fromℕ< (s≤s (s≤s (s≤s z≤n))))
        [xs2,y₂]∈R | x₂ = tt

    2-bounded-⊆*-constrained-simulation : [ 2 ][ 2>0 ]-bounded-[ ⊆* ]-constrained-simulation lzero
    2-bounded-⊆*-constrained-simulation = aBoundedConstrainedSimulation R final step

    -- R is not a 1-bounded ≡τ-constrained simulation
    private
      [x₀x₁] : FinWord 2 X
      [x₀x₁] = λ { zeroF → x₀ ; (sucF zeroF) → x₁}
    
    ¬step1 : ¬ (∀ x y → (x , y) ∈ R → Step[ 1 ][ 1>0 ][ ⊆* ] R x y)
    ¬step1 1-bounded-step with 1-bounded-step x₀ y₀ tt [x₀x₁] (λ {zeroF → [a]}) ≡refl (λ {zeroF → ≡refl})
    ¬step1 1-bounded-step | .zero , ¬k≡0 , s≤s z≤n , _ with ¬k≡0 ≡refl
    ¬step1 1-bounded-step | .zero , ¬k≡0 , s≤s z≤n , _ | ()
    ¬step1 1-bounded-step | .1 , ¬k≡0 , s≤s (s≤s z≤n) , _ , y₀ , _ , _ , [x₁,y₀]∈R = [x₁,y₀]∈R
    ¬step1 1-bounded-step | .1 , ¬k≡0 , s≤s (s≤s z≤n) , _ , y₂ , _ , _ , [x₁,y₂]∈R = [x₁,y₂]∈R


module Fig-1-4 where
  open Sum≥

  module NA₁ where
    {-
      x₀──────1────⟶x₂
        \           /
         0─⟶ x₁ ──2
    -}
    data X : Set where
      x₀ : X
      x₁ : X
      x₂ : X
  
    tr₁ : Pred' (X × ℤ × X)
    tr₁ (x₀ , +ℤ zero ,             x₁) = ⊤ -- 0
    tr₁ (x₀ , +ℤ (suc zero) ,       x₂) = ⊤ -- 1
    tr₁ (x₁ , +ℤ (suc (suc zero)) , x₂) = ⊤ -- 2
    tr₁ _ = ⊥

    acc₁ : Pred' X
    acc₁ x₀ = ⊥
    acc₁ x₁ = ⊥
    acc₁ x₂ = ⊤

    init₁ : Pred' X
    init₁ x₀ = ⊤
    init₁ x₁ = ⊥
    init₁ x₂ = ⊥

    na₁ : NA X ℤ
    na₁ = anNA tr₁ init₁ acc₁
  open NA₁

  module NA₂ where
    {-
      y₀──────3────⟶y₂
        \           /
         1─⟶ y₁ ──0
    -}
    data Y : Set where
      y₀ : Y
      y₁ : Y
      y₂ : Y
  
    tr₂ : Pred' (Y × ℤ × Y)
    tr₂ (y₀ , +ℤ (suc zero) ,             y₁) = ⊤  -- 1
    tr₂ (y₀ , +ℤ (suc (suc (suc zero))) , y₂) = ⊤  -- 3
    tr₂ (y₁ , +ℤ zero ,                   y₂) = ⊤  -- 0
    tr₂ _ = ⊥

    acc₂ : Pred' Y
    acc₂ y₀ = ⊥
    acc₂ y₁ = ⊥
    acc₂ y₂ = ⊤

    init₂ : Pred' Y
    init₂ y₀ = ⊤
    init₂ y₁ = ⊥
    init₂ y₂ = ⊥

    na₂ : NA Y ℤ
    na₂ = anNA tr₂ init₂ acc₂
  open NA₂

  open QSimulationBase ℤ X Y na₁ na₂

  module 2Bounded where
    R : Pred' (X × Y)
    -- R = { (x₀ , y₀) , (x₂ , y₂) }
    R (x₀ , y₀) = ⊤
    R (x₀ , y₁) = ⊥
    R (x₀ , y₂) = ⊥
    
    R (x₁ , y₀) = ⊥
    R (x₁ , y₁) = ⊥
    R (x₁ , y₂) = ⊥
    
    R (x₂ , y₀) = ⊥
    R (x₂ , y₁) = ⊥
    R (x₂ , y₂) = ⊤

    final : ∀ x y → (x , y) ∈ R → Final[ 2 ][ 2>0 ][ ≥+ ] R x y
    final x₀ y₀ tt zero xs w x₀≡xs0 tr xs0∈F₁ (s≤s z≤n) with step-∋ acc₁ xs0∈F₁ (≡sym x₀≡xs0)
    final x₀ y₀ tt zero xs w x₀≡xs0 tr xs0∈F₁ (s≤s z≤n) | ()
    final x₀ y₀ tt (suc zero) xs w x₀≡xs0 tr tail[xs]∈F₁ (s≤s (s≤s z≤n)) with xs zeroF | inspect xs zeroF | xs (sucF zeroF) | inspect xs (sucF zeroF) | w zeroF | inspect w zeroF | tr zeroF
    final x₀ y₀ tt (suc zero) xs w x₀≡xs0 tr tail[xs]∈F₁ (s≤s (s≤s z≤n)) | x₀ | [ xs0≡x₀ ] | x₂ | [ xs1≡x₂ ] | +ℤ (suc zero) | [ w0≡1 ] | tr0 =
      (inj 2 w' , y₂ , +≤ᶻ+ (s≤s z≤n) , (ys , ≡refl , (λ {zeroF → tt ; (sucF zeroF) → tt }) , ≡refl ) , tt)
      where
        w' : FinWord 2 ℤ
        w'  = λ {zeroF → +ℤ (suc zero) ; (sucF zeroF) → +ℤ zero}
        
        ys : FinWord 3 Y
        ys = λ {zeroF → y₀ ; (sucF zeroF) → y₁ ; (sucF (sucF zeroF)) → y₂ }

    final x₁ y₀ () n xs w x≡xs0 tr tail[xs]∈F₁ n<2
    final x₁ y₁ () n xs w x≡xs0 tr tail[xs]∈F₁ n<2
    final x₁ y₂ () n xs w x≡xs0 tr tail[xs]∈F₁ n<2
    final x₂ y₂ tt zero xs w x₂≡xs0 tr xs0∈F₁ 0<2 =
      (inj 0 (λ ()) , y₂ , +≤ᶻ+ z≤n , ((λ {zeroF → y₂}) , ≡refl , (λ ()) , ≡refl) , tt)
    final x₂ y₂ tt (suc zero) xs w x₂≡xs0 tr xs1∈F₁ (s≤s (s≤s z≤n)) with xs zeroF | inspect xs zeroF | xs (sucF zeroF) | inspect xs (sucF zeroF) | w zeroF | inspect w zeroF | tr zeroF
    final x₂ y₂ tt (suc zero) xs w x₂≡xs0 tr xs1∈F₁ (s≤s (s≤s z≤n)) | x₂ | [ xs0≡x₂ ] | x | [ _ ] | n | [ _ ] | ()

    step : ∀ x y → (x , y) ∈ R → Step[ 2 ][ 2>0 ][ ≥+ ] R x y
    step x₀ y₀ tt xs w x≡xs0 tr
      with xs zeroF | inspect xs zeroF | w zeroF | inspect w zeroF
      | xs (sucF zeroF) | inspect xs (sucF zeroF) | w (sucF zeroF) | inspect w (sucF zeroF)
      | xs (sucF (sucF zeroF)) | inspect xs (sucF (sucF zeroF))
      | tr zeroF | tr (sucF zeroF)
    step x₀ y₀ tt xs w x≡xs0 tr | x₀ | [ xs0≡ ] | +ℤ (suc zero)    | [ w0≡ ] | x₀ | [ xs1≡ ] | w1 | [ w1≡ ] | x2 | [ xs2≡ ] | () | tr1
    step x₀ y₀ tt xs w x≡xs0 tr | x₀ | [ xs0≡ ] | +ℤ (suc (suc n)) | [ w0≡ ] | x₀ | [ xs1≡ ] | w1 | [ w1≡ ] | x2 | [ xs2≡ ] | () | tr1
    step x₀ y₀ tt xs w x≡xs0 tr | x₀ | [ xs0≡ ] | +ℤ zero | [ w0≡ ] | x₁ | [ xs1≡ ] | +ℤ (suc (suc zero))    | [ w1≡ ] | x₀ | [ xs2≡ ] | tr0 | ()
    step x₀ y₀ tt xs w x≡xs0 tr | x₀ | [ xs0≡ ] | +ℤ zero | [ w0≡ ] | x₁ | [ xs1≡ ] | +ℤ (suc (suc (suc n))) | [ w1≡ ] | x₀ | [ xs2≡ ] | tr0 | ()
    step x₀ y₀ tt xs w x≡xs0 tr | x₀ | [ xs0≡ ] | +ℤ zero | [ w0≡ ] | x₁ | [ xs1≡ ] | +ℤ (suc (suc zero))    | [ w1≡ ] | x₁ | [ xs2≡ ] | tr0 | ()
    step x₀ y₀ tt xs w x≡xs0 tr | x₀ | [ xs0≡ ] | +ℤ zero | [ w0≡ ] | x₁ | [ xs1≡ ] | +ℤ (suc (suc (suc n))) | [ w1≡ ] | x₁ | [ xs2≡ ] | tr0 | ()
    step x₀ y₀ tt xs w x≡xs0 tr | x₀ | [ xs0≡ ] | +ℤ zero | [ w0≡ ] | x₁ | [ xs1≡ ] | +ℤ (suc (suc zero))    | [ w1≡ ] | x₂ | [ xs2≡ ] | tt | tt =
      (2 , (λ ()) , s≤s (s≤s (s≤s z≤n)) , inj 2 w' , y₂ , sum[w']≤ᶻsum[w] , (ys , ≡refl , (λ {zeroF → tt ; (sucF zeroF) → tt}) , ≡refl) , [xs2,y₂]∈R )
      where
        w' : FinWord 2 ℤ
        w' zeroF = +ℤ (suc zero)
        w' (sucF zeroF) = +ℤ zero

        ys : FinWord 3 Y
        ys zeroF = y₀
        ys (sucF zeroF) = y₁
        ys (sucF (sucF zeroF)) = y₂

        p : sum (w ↾ s≤s (s≤s (s≤s z≤n))) ≡ +ℤ (suc (suc zero))
        p = begin
          sum (w ↾ s≤s (s≤s (s≤s z≤n)))
          ≡⟨⟩
          w zeroF +ᶻ (w (sucF zeroF) +ᶻ +ℤ zero)
          ≡⟨ ≡cong (_+ᶻ (w (sucF zeroF) +ᶻ +ℤ zero)) w0≡ ⟩
          +ℤ zero +ᶻ (w (sucF zeroF) +ᶻ +ℤ zero)
          ≡⟨ +ᶻ-identityˡ (w (sucF zeroF) +ᶻ +ℤ zero) ⟩
          w (sucF zeroF) +ᶻ +ℤ zero
          ≡⟨ +ᶻ-identityʳ (w (sucF zeroF)) ⟩
          w (sucF zeroF)
          ≡⟨ w1≡ ⟩
          +ℤ (suc (suc zero))
          ∎
        sum[w']≤ᶻsum[w] : sum w' ≤ᶻ sum (w ↾ s≤s (s≤s (s≤s z≤n)))
        sum[w']≤ᶻsum[w] = ≤ᶻ-trans (+≤ᶻ+ (s≤s z≤n)) (≤ᶻ-reflexive (≡sym p))

        [xs2,y₂]∈R : (xs (fromℕ< (s≤s (s≤s (s≤s z≤n)))) , y₂) ∈ R
        [xs2,y₂]∈R = step-∋ R tt (≡cong (_, y₂) (≡sym xs2≡))

    step x₀ y₀ tt xs w x≡xs0 tr | x₀ | [ xs0≡ ] | +ℤ (suc zero)    | [ w0≡ ] | x₁ | [ xs1≡ ] | w1 | [ w1≡ ] | x2 | [ xs2≡ ] | () | tr1
    step x₀ y₀ tt xs w x≡xs0 tr | x₀ | [ xs0≡ ] | +ℤ (suc (suc n)) | [ w0≡ ] | x₁ | [ xs1≡ ] | w1 | [ w1≡ ] | x2 | [ xs2≡ ] | () | tr1
    step x₁ y₀ () xs w x≡xs0 tr
    step x₁ y₁ () xs w x≡xs0 tr
    step x₁ y₂ () xs w x≡xs0 tr
    step x₂ y₂ tt xs w x₂≡xs0 tr
      with xs zeroF | inspect xs zeroF | w zeroF | inspect w zeroF | xs (sucF zeroF) | inspect xs (sucF zeroF) | tr zeroF
    step x₂ y₂ tt xs w () tr | x₀ | [ xs0≡ ] | w0 | [ w0≡ ] | x1 | [ xs1≡ ] | tr0
    step x₂ y₂ tt xs w () tr | x₁ | [ xs0≡ ] | w0 | [ w0≡ ] | x1 | [ xs1≡ ] | tr0
    step x₂ y₂ tt xs w ≡refl tr | x₂ | [ xs0≡ ] | +ℤ_ n | [ w0≡ ] | x₀ | [ xs1≡ ] | ()
    step x₂ y₂ tt xs w ≡refl tr | x₂ | [ xs0≡ ] | -[1+_] n | [ w0≡ ] | x₀ | [ xs1≡ ] | ()
    step x₂ y₂ tt xs w ≡refl tr | x₂ | [ xs0≡ ] | w0 | [ w0≡ ] | x₁ | [ xs1≡ ] | ()
    step x₂ y₂ tt xs w ≡refl tr | x₂ | [ xs0≡ ] | w0 | [ w0≡ ] | x₂ | [ xs1≡ ] | ()
    
    2-bounded-≥+-constrained-simulation : [ 2 ][ 2>0 ]-bounded-[ ≥+ ]-constrained-simulation lzero
    2-bounded-≥+-constrained-simulation = aBoundedConstrainedSimulation R final step

module No-closedness-under-composition where
  data A : Set where
    τ : A
  open Total A
  
  module NAX where
    data X : Set where
      x₀ : X
      
      x₁ : X
      
      x₂₁ : X
      x₂₂ : X
      
      x₃₁ : X
      x₃₂ : X
      x₃₃ : X
      x₃₄ : X
  
    trX : Pred' (X × A × X)
    trX (x₀ , τ , x₁) = ⊤
    trX (x₁ , τ , x₂₁) = ⊤
    trX (x₁ , τ , x₂₂) = ⊤
    trX (x₂₁ , τ , x₃₁) = ⊤
    trX (x₂₁ , τ , x₃₂) = ⊤
    trX (x₂₂ , τ , x₃₃) = ⊤
    trX (x₂₂ , τ , x₃₄) = ⊤
    trX (_ , τ , _) = ⊥

    accX : Pred' X
    accX _ = ⊥
  
    initX : Pred' X
    initX x₀ = ⊤
    initX _ = ⊥

    naX : NA X A
    naX = anNA trX initX accX
  open NAX

  module NAY where
    data Y : Set where
      y₀ : Y

      y₁₁ : Y
      y₁₂ : Y

      y₂₁ : Y
      y₂₂ : Y
      y₂₃ : Y
      y₂₄ : Y

    trY : Pred' (Y × A × Y)
    trY (y₀ , τ , y₁₁) = ⊤
    trY (y₀ , τ , y₁₂) = ⊤
    trY (y₁₁ , τ , y₂₁) = ⊤
    trY (y₁₁ , τ , y₂₂) = ⊤
    trY (y₁₂ , τ , y₂₃) = ⊤
    trY (y₁₂ , τ , y₂₄) = ⊤
    trY (_ , τ , _) = ⊥

    accY : Pred' Y
    accY _ = ⊥

    initY : Pred' Y
    initY y₀ = ⊤
    initY _ = ⊥

    naY : NA Y A
    naY = anNA trY initY accY
  open NAY

  module NAZ where
    data Z : Set where
      z₀ : Z

      z₁₁ : Z
      z₁₂ : Z
      z₁₃ : Z
      z₁₄ : Z
    
    trZ : Pred' (Z × A × Z)
    trZ (z₀ , τ , z₁₁) = ⊤
    trZ (z₀ , τ , z₁₂) = ⊤
    trZ (z₀ , τ , z₁₃) = ⊤
    trZ (z₀ , τ , z₁₄) = ⊤
    trZ (_ , τ , _) = ⊥

    accZ : Pred' Z
    accZ _ = ⊥

    initZ : Pred' Z
    initZ z₀ = ⊤
    initZ _ = ⊥

    naZ : NA Z A
    naZ = anNA trZ initZ accZ
  open NAZ


  3≤3 : 3 ≤ 3
  3≤3 = s≤s (s≤s (s≤s z≤n))

  module 2BoundedXY where
    open QSimulationBase A X Y naX naY

    RXY : Pred' (X × Y)
    RXY (x₀ , y₀) = ⊤
    RXY (x₂₁ , y₁₁) = ⊤
    RXY (x₂₂ , y₁₂) = ⊤
    RXY (x₃₁ , y₂₁) = ⊤
    RXY (x₃₂ , y₂₂) = ⊤
    RXY (x₃₃ , y₂₃) = ⊤
    RXY (x₃₄ , y₂₄) = ⊤
    RXY _ = ⊥

    final : ∀ x y → (x , y) ∈ RXY → Final[ 2 ][ 2>0 ][ total ] RXY x y
    final x y [x,y]∈R n xs w x≡xs0 tr () n<2

    step : ∀ x y → (x , y) ∈ RXY → Step[ 2 ][ 2>0 ][ total ] RXY x y
    step x₀ y₀ tt xs w x≡xs0 tr with xs zeroF | inspect xs zeroF | xs (sucF zeroF) | inspect xs (sucF zeroF) | xs (sucF (sucF zeroF)) | inspect xs (sucF (sucF zeroF)) | w zeroF | w (sucF zeroF) | tr zeroF | tr (sucF zeroF)
    step x₀ y₀ tt xs w x≡xs0 tr | x₀ | [ xs0≡ ] | x₁ | [ xs1≡ ] | x₂₁ | [ xs2≡ ] | τ | τ | tt | tt =
      (2 , (λ ()) , 3≤3 ,  w' , y₁₁ , tt , (ys , ≡refl , (λ { zeroF → tt }) , ≡refl) , [xs2,y₁₁]∈R)
      where
        w' : FINWord A
        w' = (1 , (λ {zeroF → τ }))

        ys : Fin 2 → Y
        ys zeroF = y₀
        ys (sucF n) = y₁₁

        [xs2,y₁₁]∈R : (xs (fromℕ< (s≤s (s≤s (s≤s z≤n)))) , y₁₁) ∈ RXY
        [xs2,y₁₁]∈R = step-∋ RXY tt (≡cong (_, y₁₁) (≡sym xs2≡))
    step x₀ y₀ tt xs w x≡xs0 tr | x₀ | [ xs0≡ ] | x₁ | [ xs1≡ ] | x₂₂ | [ xs2≡ ] | τ | τ | tt | tt =
      (2 , (λ ()) , 3≤3 ,  w' , y₁₂ , tt , (ys , ≡refl , (λ { zeroF → tt }) , ≡refl) , [xs2,y₁₁]∈R)
      where
        w' : FINWord A
        w' = (1 , (λ {zeroF → τ }))

        ys : Fin 2 → Y
        ys zeroF = y₀
        ys (sucF n) = y₁₂

        [xs2,y₁₁]∈R : (xs (fromℕ< (s≤s (s≤s (s≤s z≤n)))) , y₁₂) ∈ RXY
        [xs2,y₁₁]∈R = step-∋ RXY tt (≡cong (_, y₁₂) (≡sym xs2≡))
    step x₂₁ y a xs w x≡xs0 tr with xs zeroF | inspect xs zeroF | xs (sucF zeroF) | inspect xs (sucF zeroF) | xs (sucF (sucF zeroF)) | inspect xs (sucF (sucF zeroF)) | w zeroF | w (sucF zeroF) | tr zeroF | tr (sucF zeroF)
    step x₂₁ y a xs w x≡xs0 tr | x₂₁ | [ p ] | x₃₁ | [ q ] | x | [ r ] | τ | τ | tt | ()
    step x₂₁ y a xs w x≡xs0 tr | x₂₁ | [ p ] | x₃₂ | [ q ] | x | [ r ] | τ | τ | tt | ()
    step x₂₂ y a xs w x≡xs0 tr with xs zeroF | inspect xs zeroF | xs (sucF zeroF) | inspect xs (sucF zeroF) | xs (sucF (sucF zeroF)) | inspect xs (sucF (sucF zeroF)) | w zeroF | w (sucF zeroF) | tr zeroF | tr (sucF zeroF)
    step x₂₂ y a xs w x≡xs0 tr | x₂₂ | [ p ] | x₃₃ | [ q ] | x | [ r ] | τ | τ | tt | ()
    step x₂₂ y a xs w x≡xs0 tr | x₂₂ | [ p ] | x₃₄ | [ q ] | x | [ r ] | τ | τ | tt | ()
    step x₃₁ y a xs w x≡xs0 tr with xs zeroF | inspect xs zeroF | xs (sucF zeroF) | inspect xs (sucF zeroF) | w zeroF | tr zeroF
    step x₃₁ y a xs w x≡xs0 tr | x₃₁ | [ p ] | x | [ q ] | τ | ()
    step x₃₂ y a xs w x≡xs0 tr with xs zeroF | inspect xs zeroF | xs (sucF zeroF) | inspect xs (sucF zeroF) | w zeroF | tr zeroF
    step x₃₂ y a xs w x≡xs0 tr | x₃₂ | [ p ] | x | [ q ] | τ | ()
    step x₃₃ y a xs w x≡xs0 tr with xs zeroF | inspect xs zeroF | xs (sucF zeroF) | inspect xs (sucF zeroF) | w zeroF | tr zeroF
    step x₃₃ y a xs w x≡xs0 tr | x₃₃ | [ p ] | x | [ q ] | τ | ()
    step x₃₄ y a xs w x≡xs0 tr with xs zeroF | inspect xs zeroF | xs (sucF zeroF) | inspect xs (sucF zeroF) | w zeroF | tr zeroF
    step x₃₄ y a xs w x≡xs0 tr | x₃₄ | [ p ] | x | [ q ] | τ | ()
    
    2-bounded-tot-constrained-simulation : [ 2 ][ 2>0 ]-bounded-[ total ]-constrained-simulation lzero
    2-bounded-tot-constrained-simulation = aBoundedConstrainedSimulation RXY final step

  module 2BoundedYZ where
    open QSimulationBase A Y Z naY naZ

    RYZ : Pred' (Y × Z)
    RYZ (y₀ , z₀) = ⊤
    RYZ (y₂₁ , z₁₁) = ⊤
    RYZ (y₂₂ , z₁₂) = ⊤
    RYZ (y₂₃ , z₁₃) = ⊤
    RYZ (y₂₄ , z₁₄) = ⊤
    RYZ _ = ⊥

    final : ∀ y z → (y , z) ∈ RYZ → Final[ 2 ][ 2>0 ][ total ] RYZ y z
    final y z [y,z]∈R n ys w y≡ys0 tr () n<2

    step : ∀ y z → (y , z) ∈ RYZ → Step[ 2 ][ 2>0 ][ total ] RYZ y z
    step y₀ z₀ a ys w y≡ys0 tr with ys zeroF | inspect ys zeroF | ys (sucF zeroF) | inspect ys (sucF zeroF) | ys (sucF (sucF zeroF)) | inspect ys (sucF (sucF zeroF)) | w zeroF | w (sucF zeroF) | tr zeroF | tr (sucF zeroF)
    step y₀ z₀ a ys w y≡ys0 tr | y₀ | [ ys0≡ ] | y₁₁ | [ xs1≡ ] | y₂₁ | [ xs2≡ ] | τ | τ | tt | tt =
      (2 , (λ ()) , 3≤3 ,  (1 , (λ {zeroF → τ })) , z₁₁ , tt , ((λ {zeroF → z₀ ; (sucF zeroF) → z₁₁} ) , ≡refl , (λ { zeroF → tt }) , ≡refl) , [ys2,z₁₁]∈R)
      where
        [ys2,z₁₁]∈R : (ys (fromℕ< (s≤s (s≤s (s≤s z≤n)))) , z₁₁) ∈ RYZ
        [ys2,z₁₁]∈R = step-∋ RYZ tt (≡cong (_, z₁₁) (≡sym xs2≡))
    step y₀ z₀ a ys w y≡ys0 tr | y₀ | [ ys0≡ ] | y₁₁ | [ xs1≡ ] | y₂₂ | [ xs2≡ ] | τ | τ | tt | tt =
      (2 , (λ ()) , 3≤3 ,  (1 , (λ {zeroF → τ })) , z₁₂ , tt , ((λ {zeroF → z₀ ; (sucF zeroF) → z₁₂} ) , ≡refl , (λ { zeroF → tt }) , ≡refl) , [ys2,z₁₂]∈R)
      where
        [ys2,z₁₂]∈R : (ys (fromℕ< (s≤s (s≤s (s≤s z≤n)))) , z₁₂) ∈ RYZ
        [ys2,z₁₂]∈R = step-∋ RYZ tt (≡cong (_, z₁₂) (≡sym xs2≡))
    step y₀ z₀ a ys w y≡ys0 tr | y₀ | [ ys0≡ ] | y₁₂ | [ xs1≡ ] | y₂₃ | [ xs2≡ ] | τ | τ | tt | tt =
      (2 , (λ ()) , 3≤3 ,  (1 , (λ {zeroF → τ })) , z₁₃ , tt , ((λ {zeroF → z₀ ; (sucF zeroF) → z₁₃} ) , ≡refl , (λ { zeroF → tt }) , ≡refl) , [ys2,z₁₃]∈R)
      where
        [ys2,z₁₃]∈R : (ys (fromℕ< (s≤s (s≤s (s≤s z≤n)))) , z₁₃) ∈ RYZ
        [ys2,z₁₃]∈R = step-∋ RYZ tt (≡cong (_, z₁₃) (≡sym xs2≡))
    step y₀ z₀ a ys w y≡ys0 tr | y₀ | [ ys0≡ ] | y₁₂ | [ xs1≡ ] | y₂₄ | [ xs2≡ ] | τ | τ | tt | tt =
      (2 , (λ ()) , 3≤3 ,  (1 , (λ {zeroF → τ })) , z₁₄ , tt , ((λ {zeroF → z₀ ; (sucF zeroF) → z₁₄} ) , ≡refl , (λ { zeroF → tt }) , ≡refl) , [ys2,z₁₄]∈R)
      where
        [ys2,z₁₄]∈R : (ys (fromℕ< (s≤s (s≤s (s≤s z≤n)))) , z₁₄) ∈ RYZ
        [ys2,z₁₄]∈R = step-∋ RYZ tt (≡cong (_, z₁₄) (≡sym xs2≡))
    step y₂₁ z a ys w y≡ys0 tr with ys zeroF | inspect ys zeroF | ys (sucF zeroF) | inspect ys (sucF zeroF) | w zeroF | tr zeroF
    step y₂₁ z a ys w y≡ys0 tr | y₂₁ | [ p ] | y | [ q ] | τ | ()
    step y₂₂ z a ys w y≡ys0 tr with ys zeroF | inspect ys zeroF | ys (sucF zeroF) | inspect ys (sucF zeroF) | w zeroF | tr zeroF
    step y₂₂ z a ys w y≡ys0 tr | y₂₂ | [ p ] | y | [ q ] | τ | ()
    step y₂₃ z a ys w y≡ys0 tr with ys zeroF | inspect ys zeroF | ys (sucF zeroF) | inspect ys (sucF zeroF) | w zeroF | tr zeroF
    step y₂₃ z a ys w y≡ys0 tr | y₂₃ | [ p ] | y | [ q ] | τ | ()
    step y₂₄ z a ys w y≡ys0 tr with ys zeroF | inspect ys zeroF | ys (sucF zeroF) | inspect ys (sucF zeroF) | w zeroF | tr zeroF
    step y₂₄ z a ys w y≡ys0 tr | y₂₄ | [ p ] | y | [ q ] | τ | ()

    2-bounded-tot-constrained-simulation : [ 2 ][ 2>0 ]-bounded-[ total ]-constrained-simulation lzero
    2-bounded-tot-constrained-simulation = aBoundedConstrainedSimulation RYZ final step
  
  module Not2BoundedXZ where
    open QSimulationBase A X Z naX naZ

    RXZ : Pred' (X × Z)
    RXZ = 2BoundedXY.RXY ∘ᵣ 2BoundedYZ.RYZ

    no-step2 : (∀ x z → (x , z) ∈ RXZ → Step[ 2 ][ 2>0 ][ total ] RXZ x z) → ⊥
    no-step2 step2 with step2 x₀ z₀ (y₀ , tt , tt)
    no-step2 step2 | step2[x₀,z₀] with step2[x₀,z₀] (λ {zeroF → x₀ ; (sucF zeroF) → x₁ ; (sucF (sucF zeroF)) → x₂₁}) (λ {zeroF → τ ; (sucF zeroF) → τ}) ≡refl (λ {zeroF → tt ; (sucF zeroF) → tt})
    no-step2 step2 | _ | .zero , knon0 , s≤s z≤n , w' , z₀ , tt , tr , y₀ , tt , tt = knon0 ≡refl
    no-step2 step2 | _ | .2 , knon0 , s≤s (s≤s (s≤s z≤n)) , w' , z₀ , tt , tr , y₀ , () , tt
    no-step2 step2 | _ | .zero , knon0 , s≤s z≤n , w' , z₁₁ , tt , tr , y , a , b = knon0 ≡refl
    no-step2 step2 | _ | .2 , knon0 , s≤s (s≤s (s≤s z≤n)) , w' , z₁₁ , tt , tr , y₂₁ , () , tt
    no-step2 step2 | _ | .zero , knon0 , s≤s z≤n , w' , z₁₂ , tt , tr , y , a , b = knon0 ≡refl
    no-step2 step2 | _ | .2 , knon0 , s≤s (s≤s (s≤s z≤n)) , w' , z₁₂ , tt , tr , y₂₂ , () , tt
    no-step2 step2 | _ | .zero , knon0 , s≤s z≤n , w' , z₁₃ , tt , tr , y , a , b = knon0 ≡refl
    no-step2 step2 | _ | .2 , knon0 , s≤s (s≤s (s≤s z≤n)) , w' , z₁₃ , tt , tr , y₂₃ , () , tt
    no-step2 step2 | _ | .zero , knon0 , s≤s z≤n , w' , z₁₄ , tt , tr , y , a , b = knon0 ≡refl
    no-step2 step2 | _ | .2 , knon0 , s≤s (s≤s (s≤s z≤n)) , w' , z₁₄ , tt , tr , y₂₄ , () , tt
