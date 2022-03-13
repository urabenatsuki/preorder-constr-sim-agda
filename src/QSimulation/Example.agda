module QSimulation.Example where

open import Agda.Builtin.Bool
  using (true; false)
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
open import Relation.Unary using (_∈_; _⊆_)
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


module Eq (A X₁ X₂ : Set) (na₁ : NA X₁ A) (na₂ : NA X₂ A) where
  EqCarrier : Pred' ((FINWord A) × (FINWord A))
  EqCarrier (w , w') = w ≡ w'
  EqRefl : ∀ (s : FINWord A) → EqCarrier (s , s)
  EqRefl w = ≡refl
  EqTrans : ∀ (s s' s'' : FINWord A)
    → EqCarrier (s , s')
    → EqCarrier (s' , s'')
    → EqCarrier (s , s'')
  EqTrans w .w .w ≡refl ≡refl = ≡refl
  
  Eq = aPreorder EqCarrier EqRefl EqTrans
  
  LanguageInclusion :
    (x : X₁) → (y : X₂)
    → (x ≤[ na₁ , na₂ , Eq ] y)
    → (FINAccLang na₁ x) ⊆ (FINAccLang na₂ y)
  LanguageInclusion x y x≤[≡]y {w} w∈L₁[x] with x≤[≡]y w w∈L₁[x]
  ... | (w' , w'∈L₂y , wQw') = step-∋ (FINAccLang na₂ y) w'∈L₂y (≡sym wQw')

module Addτ (A : Set) where
  data A+τ : Set where
    fromA : A → A+τ
    τ : A+τ

module Remτ (A X₁ X₂ : Set) where
  open Addτ A
  remτ : (n : ℕ) → FinWord n A+τ → FINWord A
  remτ zero w = ε-word A
  remτ (suc n) w with w zeroF
  remτ (suc n) w | τ = remτ n (tailF w)
  remτ (suc n) w | fromA a with remτ n (tailF w)
  remτ (suc n) w | fromA a | m , w' = (suc m , a ∷ᶠ w')

  w0≡τ⇒remτ[w]≡remτ[tail[w]] :
    ∀ n
    → (w : FinWord (suc n) A+τ)
    → w zeroF ≡ τ
    → remτ (suc n) w ≡ remτ n (tailF w)
  w0≡τ⇒remτ[w]≡remτ[tail[w]] n w p with w zeroF
  w0≡τ⇒remτ[w]≡remτ[tail[w]] n w p | τ = ≡refl

  w0≡a⇒remτ[w]≡a∷remτ[tail[w]] :
    ∀ n
    → (w : FinWord (suc n) A+τ)
    → (a : A)
    → w zeroF ≡ fromA a
    → remτ (suc n) w ≡ (suc (proj₁ (remτ n (tailF w))) , (a ∷ᶠ proj₂ (remτ n (tailF w))))
  w0≡a⇒remτ[w]≡a∷remτ[tail[w]] n w a w0≡a with w zeroF | inspect w zeroF
  w0≡a⇒remτ[w]≡a∷remτ[tail[w]] n w .a ≡refl | Addτ.fromA a | [ eq ] with remτ n (tailF w)
  w0≡a⇒remτ[w]≡a∷remτ[tail[w]] n w a ≡refl | Addτ.fromA a | [ eq ] | m , w' = ≡refl

  ∣remτw∣≤∣w∣ :
    ∀ n
    → (w : FinWord n A+τ)
    → proj₁ (remτ n w) ≤ n
  ∣remτw∣≤∣w∣ zero w = z≤n
  ∣remτw∣≤∣w∣ (suc n) w with w zeroF
  ∣remτw∣≤∣w∣ (suc n) w | τ = ≤-step (∣remτw∣≤∣w∣ n (tailF w))
  ∣remτw∣≤∣w∣ (suc n) w | fromA a = s≤s (∣remτw∣≤∣w∣ n (tailF w))
  
  ≡τ-carrier : Pred' ((FINWord A+τ) × (FINWord A+τ))
  ≡τ-carrier ((m , u) , (n , v)) with remτ m u | remτ n v
  ≡τ-carrier ((m , u) , (n , v)) | m' , u' | n' , v' with m' ≟ n'
  ≡τ-carrier ((m , u) , (n , v)) | m' , u' | .m' , v' | true because ofʸ ≡refl =
    ∀ (i : Fin m') → u' i ≡ v' i
  ≡τ-carrier ((m , u) , (n , v)) | m' , u' | n' , v' | false because ofⁿ ¬p =
    ⊥

  -- another definition of carrier of ≡τ
  ≡τ-carrier' : Pred' ((FINWord A+τ) × (FINWord A+τ))
  ≡τ-carrier' ((m , u) , (n , v)) = remτ m u ≡ remτ n v

  -- equivalence between ≡τ-carrier and ≡τ-carrier'
  ≡τ-carrier-carrier' : ∀ (uv : (FINWord A+τ) × (FINWord A+τ)) → ≡τ-carrier uv → ≡τ-carrier' uv
  ≡τ-carrier-carrier' ((m , u) , (n , v)) u≡τv with remτ m u | remτ n v
  ≡τ-carrier-carrier' ((m , u) , (n , v)) u≡τv | m' , u' | n' , v' with m' ≟ n'
  ≡τ-carrier-carrier' ((m , u) , n , v) u≡τv | m' , u' | .m' , v' | .true because ofʸ ≡refl =
    begin m' , u' ≡⟨ ≡cong (λ t → m' , t) (ex u≡τv) ⟩ m' , v' ∎
  
  ≡τ-carrier'-carrier : ∀ (uv : (FINWord A+τ) × (FINWord A+τ)) → ≡τ-carrier' uv → ≡τ-carrier uv
  ≡τ-carrier'-carrier ((m , u) , (n , v)) u≡τ'v with remτ m u | remτ n v
  ≡τ-carrier'-carrier ((m , u) , (n , v)) u≡τ'v | m' , u' | n' , v' with m' ≟ n'
  ≡τ-carrier'-carrier ((m , u) , n , v) u≡τv | m' , u' | .m' , v' | .true because ofʸ ≡refl = (lem m' u' v' u≡τv)
    where
      lem : ∀ k → (x y : FinWord k A) → inj k x ≡ inj k y → ∀ i → x i ≡ y i
      lem k x .x ≡refl i = ≡refl
  ≡τ-carrier'-carrier ((m , u) , n , v) u≡τv | m' , u' | n' , v' | .false because ofⁿ ¬m'≡n' with ¬m'≡n' (word-≡-proj₁ (m' , u') (n' , v') u≡τv)
  ≡τ-carrier'-carrier ((m , u) , n , v) u≡τv | m' , u' | n' , v' | .false because ofⁿ ¬m'≡n' | ()
  

  ≡τ-refl : ∀ (w : FINWord A+τ) → ≡τ-carrier (w , w)
  ≡τ-refl (n , w) with remτ n w
  ≡τ-refl (n , w) | n' , w' with n' ≟ n'
  ≡τ-refl (n , w) | n' , w' | true because ofʸ ≡refl = λ i → ≡refl
  ≡τ-refl (n , w) | n' , w' | false because ofⁿ ¬n'≡n' = ¬n'≡n' ≡refl

  ≡τ-trans : ∀ (u v w : FINWord A+τ)
    → ≡τ-carrier (u , v)
    → ≡τ-carrier (v , w)
    → ≡τ-carrier (u , w)
  ≡τ-trans (l , u) (m , v) (n , w) p q with remτ l u | remτ m v | remτ n w
  ≡τ-trans (l , u) (m , v) (n , w) p q | l' , u' | m' , v' | n' , w' with l' ≟ n'
  ≡τ-trans (l , u) (m , v) (n , w) p q | l' , u' | m' , v' | l' , w' | true because ofʸ ≡refl
    with l' ≟ m' | m' ≟ l'
  ≡τ-trans (l , u) (m , v) (n , w) p q | l' , u' | l' , v' | l' , w' | true because ofʸ ≡refl
    | .true because ofʸ ≡refl | .true because ofʸ ≡refl =
    λ i → begin u' i ≡⟨ p i ⟩ v' i ≡⟨ q i ⟩ w' i ∎
  ≡τ-trans (l , u) (m , v) (n , w) p q | l' , u' | m' , v' | n' , w' | false because ofⁿ ¬l'≡n'
    with l' ≟ m' | m' ≟ n'
  ≡τ-trans (l , u) (m , v) (n , w) p q | l' , u' | l' , v' | .l' , w' | false because ofⁿ ¬l'≡l'
    | .true because ofʸ ≡refl | .true because ofʸ ≡refl
    with ¬l'≡l' ≡refl
  ≡τ-trans (l , u) (m , v) (n , w) p q | l' , u' | l' , v' | .l' , w' | false because ofⁿ ¬l'≡l'
    | .true because ofʸ ≡refl | .true because ofʸ ≡refl
    | ()

  ≡τ = aPreorder ≡τ-carrier ≡τ-refl ≡τ-trans

  remτ-concat : (m n : ℕ) → (u  : FinWord m A+τ) → (v : FinWord n A+τ)
    → (proj₁ (remτ m u) + proj₁ (remτ n v) , concat (proj₂ (remτ m u)) (proj₂ (remτ n v))) ≡ remτ (m + n) (concat u v)
  remτ-concat zero n u v with remτ zero u | inspect proj₁ (remτ zero u)
  remτ-concat zero n u v | .0 , u' | [ ≡refl ] = ≡refl
  remτ-concat (suc m) n u v with u zeroF | inspect u zeroF
  remτ-concat (suc m) n u v | τ | [ u0≡τ ] with remτ (suc m) u | w0≡τ⇒remτ[w]≡remτ[tail[w]] m u u0≡τ
  remτ-concat (suc m) n u v | τ | [ u0≡τ ] | .(proj₁ (remτ m (λ i → u (sucF i)))) , .(proj₂ (remτ m (λ i → u (sucF i)))) | ≡refl = remτ-concat m n (λ z → u (sucF z)) v
  remτ-concat (suc m) n u v | fromA a | [ u0≡a ] with remτ (suc m) u | w0≡a⇒remτ[w]≡a∷remτ[tail[w]] m u a u0≡a
  remτ-concat (suc m) n u v | fromA a | [ u0≡a ] | m' , u' | q with remτ-concat m n (tailF u) v
  remτ-concat (suc m) n u v | fromA a | [ u0≡a ] | m' , u' | q | ih = begin
    suc (proj₁ (remτ m (tailF u))) + proj₁ (remτ n v)
    , concat (a ∷ᶠ (proj₂ (remτ m (tailF u)))) (proj₂ (remτ n v))
    ≡⟨ ≡cong (λ R → _ , R) (ex (λ i → concat[a∷u][v]i≡a∷concat[u][v]i a (proj₂ (remτ m (tailF u))) (proj₂ (remτ n v)) i)) ⟩
    suc (proj₁ (remτ m (tailF u))) + proj₁ (remτ n v)
    , a ∷ᶠ concat (proj₂ (remτ m (tailF u))) (proj₂ (remτ n v))
    ≡⟨ lemma a _ _ (concat (proj₂ (remτ m (tailF u))) (proj₂ (remτ n v))) (proj₂ (remτ (m + n) (concat (tailF u) v))) ih ⟩ 
    suc (proj₁ (remτ (m + n) (concat (tailF u) v)))
    , a ∷ᶠ proj₂ (remτ (m + n) (concat (tailF u) v))
    ∎
    where
      lemma : (a : A)
        → (l₁ l₂ : ℕ)
        → (w₁ : FinWord l₁ A)
        → (w₂ : FinWord l₂ A)
        → (p : inj l₁ w₁ ≡ inj l₂ w₂)
        → inj (suc l₁) (a ∷ᶠ w₁) ≡ inj (suc l₂) (a ∷ᶠ w₂)
      lemma a l₁ .l₁ w₁ .w₁ ≡refl = ≡refl

  u0≡a⇒u'0≡τ⇒u-≡τ-tailu' : (m m' : ℕ)
    → (u : FinWord (suc m) A+τ)
    → (u' : FinWord (suc m') A+τ)
    → (inj (suc m) u , inj (suc m') u') ∈ ≡τ-carrier
    → (a : A)
    → (u zeroF ≡ fromA a)
    → (u' zeroF ≡ τ)
    → (inj (suc m) u , inj m' (tailF u')) ∈ ≡τ-carrier
  u0≡a⇒u'0≡τ⇒u-≡τ-tailu' m m' u u' u-u' a u0≡a u'≡τ with u zeroF | u' zeroF
  u0≡a⇒u'0≡τ⇒u-≡τ-tailu' m m' u u' u-u' a u0≡a u'≡τ | fromA _ | τ with remτ m (tailF u) | remτ m' (tailF u')
  u0≡a⇒u'0≡τ⇒u-≡τ-tailu' m m' u u' u-u' a u0≡a u'≡τ | fromA _ | τ | n , v | n' , v' with (suc n) ≟ n'
  u0≡a⇒u'0≡τ⇒u-≡τ-tailu' m m' u u' u-u' a u0≡a u'≡τ | fromA _ | τ | n , v | .(suc n) , v' | .true because ofʸ ≡refl = u-u'

  ≡τ'-concat : (m m' n n' : ℕ)
    → (u  : FinWord m  A+τ) → (v  : FinWord n  A+τ)
    → (u' : FinWord m' A+τ) → (v' : FinWord n' A+τ)
    → (inj m u , inj m' u') ∈ ≡τ-carrier'
    → (inj n v , inj n' v') ∈ ≡τ-carrier'
    → (inj (m + n) (concat u v) , inj (m' + n') (concat u' v')) ∈ ≡τ-carrier'
  ≡τ'-concat m m' n n' u v u' v' u-u' v-v' with remτ m u | remτ m' u' | remτ n v | remτ n' v' | remτ-concat m n u v | remτ-concat m' n' u' v'
  ≡τ'-concat m m' n n' u v u' v' u-u' v-v' | rm , ru  | rm' , ru' | rn , rv | rn' , rv' | p | p' =
    begin
    remτ (m + n) (concat u v)
    ≡⟨ ≡sym p ⟩
    rm + rn , concat ru rv
    ≡⟨ lemma ru rv ru' rv' u-u' v-v' ⟩
    rm' + rn' , concat ru' rv'
    ≡⟨ p' ⟩
    remτ (m' + n') (concat u' v')
    ∎
    where
      lemma : ∀ {l₁ l₂ l₁' l₂' : ℕ}
        → (w₁ : FinWord l₁ A) → (w₂ : FinWord l₂ A)
        → (w₁' : FinWord l₁' A) → (w₂' : FinWord l₂' A)
        → (p₁ : inj l₁ w₁ ≡ inj l₁' w₁')
        → (p₂ : inj l₂ w₂ ≡ inj l₂' w₂')
        → inj (l₁ + l₂) (concat w₁ w₂) ≡ inj (l₁' + l₂') (concat w₁' w₂')
      lemma {l₁} {l₂} {.l₁} {.l₂} w₁ w₂ .w₁ .w₂ ≡refl ≡refl = ≡refl
  
  ≡τ-concat : (m m' n n' : ℕ)
    → (u  : FinWord m  A+τ) → (v  : FinWord n  A+τ)
    → (u' : FinWord m' A+τ) → (v' : FinWord n' A+τ)
    → (inj m u , inj m' u') ∈ ≡τ-carrier
    → (inj n v , inj n' v') ∈ ≡τ-carrier
    → (inj (m + n) (concat u v) , inj (m' + n') (concat u' v')) ∈ ≡τ-carrier
  ≡τ-concat m m' n n' u v u' v' u-u' v-v' =
    ≡τ-carrier'-carrier (inj (m + n) (concat u v) , inj (m' + n') (concat u' v'))
      (≡τ'-concat m m' n n' u v u' v' (≡τ-carrier-carrier' (inj m u , inj m' u') u-u') (≡τ-carrier-carrier' (inj n v , inj n' v') v-v'))
  
  open ConditionOnQ A+τ
  ≡τ-is-closed-under-concat : [ ≡τ ]-is-closed-under-concat
  ≡τ-is-closed-under-concat ((m , u) , (m' , u')) u≡τu' ((n , v) , (n' , v')) v≡τv' =
    step-∋ ≡τ-carrier (≡τ-concat m m' n n' u v u' v' u≡τu' v≡τv')
      (begin
      inj (m + n) (concat u v) , inj (m' + n') (concat u' v')
      ≡⟨⟩
      (m , u) · (n , v) , (m' , u') · (n' , v')
      ∎)


module Prefix (A X₁ X₂ : Set) (na₁ : NA X₁ A) (na₂ : NA X₂ A) where
  ⊑-carrier : Pred' ((FINWord A) × (FINWord A))
  ⊑-carrier ((m , u) , (n , v)) =
    -- u is a prefix of v
    ∃[ m≤n ] ∀ (i : Fin m) → (u i ≡ v (inject≤ i m≤n))

  ⊑-refl : ∀ (w : FINWord A) → ⊑-carrier (w , w)
  ⊑-refl (n , w) = (≤-reflexive ≡refl , λ i → ≡cong w (≡sym (inject≤-refl i (≤-reflexive ≡refl))))

  ⊑-trans : ∀ (w w' w'' : FINWord A)
    → ⊑-carrier (w , w')
    → ⊑-carrier (w' , w'')
    → ⊑-carrier (w , w'')
  ⊑-trans (l , w) (m , w') (n , w'') (l≤m , w⊑w') (m≤n , w'⊑w'') =
    (≤-trans l≤m m≤n , λ i →
      (begin
      w i
      ≡⟨ w⊑w' i ⟩
      w' (inject≤ i l≤m)
      ≡⟨ w'⊑w'' (inject≤ i l≤m) ⟩
      w'' (inject≤ (inject≤ i l≤m) m≤n)
      ≡⟨ ≡cong w'' (inject≤-idempotent i l≤m m≤n (≤-trans l≤m m≤n)) ⟩
      w'' (inject≤ i (≤-trans l≤m m≤n)) 
      ∎)
    )

  Prefix = aPreorder ⊑-carrier ⊑-refl ⊑-trans

  Equivalent-to-≤[⊑] : (x : X₁) → (y : X₂) → Set
  Equivalent-to-≤[⊑] x y =
    (w : FINWord A) → w ∈ FINAccLang na₁ x → ∃[ w' ] (w' ∈ FINAccLang na₂ y) × (w , w') ∈ ⊑-carrier
  
  x≤[⊑]y⇒∀w∈L₁[x]∃w'∈L₂[y]w⊑w' :
    (x : X₁) → (y : X₂)
    → (x ≤[ na₁ , na₂ , Prefix ] y)
    → Equivalent-to-≤[⊑] x y
  x≤[⊑]y⇒∀w∈L₁[x]∃w'∈L₂[y]w⊑w' x y x≤[⊑]y w w∈L₁[x] = x≤[⊑]y w w∈L₁[x]
  
  ∀w∈L₁[x]∃w'∈L₂[y]w⊑w'⇒x≤[⊑]y :
    (x : X₁) → (y : X₂)
    → Equivalent-to-≤[⊑] x y
    → (x ≤[ na₁ , na₂ , Prefix ] y)
  ∀w∈L₁[x]∃w'∈L₂[y]w⊑w'⇒x≤[⊑]y x y f w w∈L₁[x] = f w w∈L₁[x]

module Fig-1-1 where
  data A : Set where
    a : A

  open Addτ A
  
  module NA₁ where
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
  
  open Remτ A X Y
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


module Fig-1-2 where
  data A : Set where
    a : A
    b : A

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
    tr₂ (y₂ , b , y₁) = ⊤
    tr₂ (y₂ , c , y₂) = ⊤
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
