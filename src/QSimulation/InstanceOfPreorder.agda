module QSimulation.InstanceOfPreorder where

open import Data.Bool
  using (true; false; Bool)
  renaming (f≤t to f→ᵇt; b≤b to b→ᵇb; _≤_ to _→ᵇ_)
open import Data.Bool.Properties
  using ()
  renaming (≤-trans to →ᵇ-trans)
open import Data.Nat
open import Data.Nat.Properties
  using (≤-reflexive; ≤-trans; ≤-step; m≤n⇒m≤1+n; _≟_; n≤0⇒n≡0)
open import Data.Integer
  using (ℤ; -[1+_]; 0ℤ)
  renaming (+_ to +ᶻ_; _≤_ to _≤ᶻ_; _+_ to _+ᶻ_)
open import Data.Integer.Properties
  using ()
  renaming (≤-reflexive to ≤ᶻ-reflexive; ≤-trans to ≤ᶻ-trans; +-identityˡ to +ᶻ-identityˡ; +-assoc to +ᶻ-assoc; +-mono-≤ to +ᶻ-mono-≤ᶻ)
open import Data.Fin
  using (Fin; inject≤; fromℕ; fromℕ<; inject₁; cast; toℕ)
  renaming (zero to zeroF; suc to sucF; _<_ to _<ᶠ_)
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
open import Function.Base using (_∘′_)

open import Base
open import Word
open import NA
open import QSimulation.Base
open import QSimulation.Lemma using (casti≡i)


module Eq (A : Set) where
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

  open ConditionOnQ A
  Eq-is-closed-under-concat : [ Eq ]-is-closed-under-concat
  Eq-is-closed-under-concat ((m , u) , .m , .u) ≡refl ((n , v) , .n , .v) ≡refl = ≡refl

module UptoEq (A X : Set) (na : NA X A) where
  {- up-to equality, R = (=) -}
  EqR  : Pred' (X × X)
  EqR (x , x') = x ≡ x'

  open Eq A
  EqR⊆[≤Eq] : EqR ⊆ (λ (x , x') → x ≤[ na , na ,  Eq ] x')
  EqR⊆[≤Eq] ≡refl (l , w) (xs , ≡refl , tr , last[xs]∈F) = ((l , w) , (xs , ≡refl , tr , last[xs]∈F) , ≡refl)

LanguageInclusion :
  {X₁ X₂ A : Set} →
  (na₁ : NA X₁ A) → (na₂ : NA X₂ A)
  (x : X₁) → (y : X₂)
  → (x ≤[ na₁ , na₂ , Eq.Eq A ] y)
  → (FINAccLang na₁ x) ⊆ (FINAccLang na₂ y)
LanguageInclusion na₁ na₂ x y x≤[≡]y {w} w∈L₁[x] with x≤[≡]y w w∈L₁[x]
... | (w' , w'∈L₂y , wQw') = step-∋ (FINAccLang na₂ y) w'∈L₂y (≡sym wQw')

module Addτ (A : Set) where
  data A+τ : Set where
    fromA : A → A+τ
    τ : A+τ

module Remτ (A : Set) where
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
  ∣remτw∣≤∣w∣ (suc n) w | τ = m≤n⇒m≤1+n (∣remτw∣≤∣w∣ n (tailF w))
  ∣remτw∣≤∣w∣ (suc n) w | fromA a = s≤s (∣remτw∣≤∣w∣ n (tailF w))

  ∣remτε∣≡0 : (w : FinWord 0 A+τ) → proj₁ (remτ 0 w) ≡ 0
  ∣remτε∣≡0 w = n≤0⇒n≡0 (∣remτw∣≤∣w∣ 0 w)

  remτε≡ε : (w : FinWord 0 A+τ) → proj₂ (remτ 0 w) ≡ ε-word' A
  remτε≡ε w = ex (λ ())
  
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
  ⊑prefix-carrier : Pred' ((FINWord A) × (FINWord A))
  ⊑prefix-carrier ((m , u) , (n , v)) =
    -- u is a prefix of v
    ∃[ m≤n ] ∀ (i : Fin m) → (u i ≡ v (inject≤ i m≤n))

  ⊑prefix-refl : ∀ (w : FINWord A) → ⊑prefix-carrier (w , w)
  ⊑prefix-refl (n , w) = (≤-reflexive ≡refl , λ i → ≡cong w (≡sym (inject≤-refl i (≤-reflexive ≡refl))))

  ⊑prefix-trans : ∀ (w w' w'' : FINWord A)
    → ⊑prefix-carrier (w , w')
    → ⊑prefix-carrier (w' , w'')
    → ⊑prefix-carrier (w , w'')
  ⊑prefix-trans (l , w) (m , w') (n , w'') (l≤m , w⊑w') (m≤n , w'⊑w'') =
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

  Prefix = aPreorder ⊑prefix-carrier ⊑prefix-refl ⊑prefix-trans

  Equivalent-to-≤[⊑] : (x : X₁) → (y : X₂) → Set
  Equivalent-to-≤[⊑] x y =
    (w : FINWord A) → w ∈ FINAccLang na₁ x → ∃[ w' ] (w' ∈ FINAccLang na₂ y) × (w , w') ∈ ⊑prefix-carrier
  
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

module Substr (A : Set) where

  _is-monotone : ∀ {m n} → (Fin m → Fin n) → Set
  _is-monotone {m} {n} f = ∀ (i j : Fin m) → i <ᶠ j → f i <ᶠ f j
  
  idᶠ : ∀ {m} → Fin m → Fin m
  idᶠ i = i
  idᶠ-is-monotone : ∀ {m} → (idᶠ {m}) is-monotone
  idᶠ-is-monotone {m} = λ i j p → p

  ⊑substr-carrier : Pred' ((FINWord A) × (FINWord A))
  ⊑substr-carrier ((m , u) , (n , v)) = ∃[ f ] (f is-monotone) × (∀ i → u i ≡ v (f i))

  ⊑substr-refl : ∀ (w : FINWord A) → ⊑substr-carrier (w , w)
  ⊑substr-refl (n , w) = (idᶠ , idᶠ-is-monotone , (λ i → ≡refl))

  compose : ∀ {l m n} → (Fin l → Fin m) → (Fin m → Fin n) → (Fin l → Fin n)
  compose {l} {m} {n} f g i = g (f i)
  
  compose-monotone : ∀ {l m n}
    → (f : Fin l → Fin m)
    → (f is-monotone)
    → (g : Fin m → Fin n)
    → (g is-monotone)
    → ( (compose f g) is-monotone ) 
  compose-monotone {l} {m} {n} f f-is-monotone g g-is-monotone i j i<j = g-is-monotone (f i) (f j) (f-is-monotone i j i<j)
    
  ⊑substr-trans : (w w' w'' : FINWord A)
    → ⊑substr-carrier (w , w')
    → ⊑substr-carrier (w' , w'')
    → ⊑substr-carrier (w , w'')
  ⊑substr-trans (n , w) (n' , w') (n'' , w'') (f , f-monotone , w-f-w') (f' , f'-monotone , w'-f'-w'') =
    (compose f f' , compose-monotone f f-monotone f' f'-monotone , (λ i → begin w i ≡⟨ w-f-w' i ⟩ w' (f i) ≡⟨ w'-f'-w'' (f i) ⟩ w'' (f' (f i)) ∎))

  ⊑substr = aPreorder ⊑substr-carrier ⊑substr-refl ⊑substr-trans

module Subset (A : Set) where
  PA : Set
  PA = A → Bool

  subset : Pred' (PA × PA)
  subset (s , t) = ∀ a → s a →ᵇ t a

  ⊆*-carrier : Pred' ((FINWord PA) × (FINWord PA))
  ⊆*-carrier ((k , w) , (k' , w')) with k ≟ k'
  ⊆*-carrier ((k , w) , (.k , w')) | .true because ofʸ ≡refl = ∀ i → subset ((w i) , (w' i))
  ⊆*-carrier ((k , w) , (k' , w')) | .false because ofⁿ _ = ⊥

  ⊆*-refl : ∀ (w : FINWord PA) → ⊆*-carrier (w , w)
  ⊆*-refl (k , w) with k ≟ k
  ⊆*-refl (k , w) | .true because ofʸ ≡refl = λ i a → b→ᵇb
  ⊆*-refl (k , w) | .false because ofⁿ ¬k≡k = ¬k≡k ≡refl

  ⊆*-trans : ∀ (w w' w'' : FINWord PA)
    → ⊆*-carrier (w , w')
    → ⊆*-carrier (w' , w'')
    → ⊆*-carrier (w , w'')
  ⊆*-trans (l , w) (m , w') (n , w'') w-w' w'-w'' with l ≟ m | m ≟ n
  ⊆*-trans (l , w) (l , w') (.l , w'') w-w' w'-w'' | .true because ofʸ ≡refl | .true because ofʸ ≡refl with l ≟ l
  ⊆*-trans (l , w) (l , w') (l , w'') w-w' w'-w'' | .true because ofʸ ≡refl | .true because ofʸ ≡refl | .true because ofʸ ≡refl =
    λ i → λ a → →ᵇ-trans (w-w' i a) (w'-w'' i a)
  ⊆*-trans (l , w) (l , w') (l , w'') _ _ | .true because ofʸ ≡refl | .true because ofʸ ≡refl | .false because ofⁿ ¬p = ¬p ≡refl

  ⊆* = aPreorder ⊆*-carrier ⊆*-refl ⊆*-trans

  lemma-⊆*-is-closed-under-concat : ∀ m n m' n'
    → (u  : FinWord m PA)
    → (v : FinWord n PA)
    → (u'  : FinWord m' PA)
    → (v' : FinWord n' PA)
    → (inj m u , inj m' u') ∈ ⊆*-carrier
    → (inj n v , inj n' v') ∈ ⊆*-carrier
    → (inj (m + n) (concat u v) , inj (m' + n') (concat u' v')) ∈ ⊆*-carrier
  lemma-⊆*-is-closed-under-concat zero n zero n' u v u' v' u-u' v-v' = v-v'
  lemma-⊆*-is-closed-under-concat (suc m) n m' n' u v u' v' u-u' v-v' with (suc m) ≟ m' | n ≟ n'
  lemma-⊆*-is-closed-under-concat (suc m) n .(suc m) .n u v u' v' u-u' v-v' | .true because ofʸ ≡refl | .true because ofʸ ≡refl with (suc m + n) ≟ (suc m + n)
  lemma-⊆*-is-closed-under-concat (suc m) n .(suc m) n u v u' v' u-u' v-v' | .true because ofʸ ≡refl | .true because ofʸ ≡refl | .true because ofʸ ≡refl =
    λ { zeroF → u-u' zeroF ; (sucF i) → proof i }
    where
      tu-tu' : (inj m (tailF u) , inj m (tailF u')) ∈ ⊆*-carrier
      tu-tu' with m ≟ m
      tu-tu' | .true because ofʸ ≡refl = λ i → u-u' (sucF i)
      tu-tu' | .false because ofⁿ ¬p = ¬p ≡refl

      v-v'-again : (inj n v , inj n v') ∈ ⊆*-carrier
      v-v'-again with n ≟ n
      v-v'-again | .true because ofʸ ≡refl = v-v'
      v-v'-again | .false because ofⁿ ¬p = ¬p ≡refl

      proof : ∀ i → ∀ a → concat u v (sucF i) a →ᵇ concat u' v' (sucF i) a
      proof i a with (m + n) ≟ proj₁ (inj (m + n) (concat (tailF u') v')) | lemma-⊆*-is-closed-under-concat m n m n (tailF u) v (tailF u') v' tu-tu' v-v'-again
      proof i a | .true because ofʸ ≡refl | ih = ih i a
      proof i a | .false because ofⁿ ¬p | ()
  lemma-⊆*-is-closed-under-concat (suc m) n .(suc m) n u v u' v' u-u' v-v' | .true because ofʸ ≡refl | .true because ofʸ ≡refl | .false because ofⁿ ¬p = ¬p ≡refl
  
  open ConditionOnQ PA
  ⊆*-is-closed-under-concat : [ ⊆* ]-is-closed-under-concat
  ⊆*-is-closed-under-concat ((m , u) , (m' , u')) u-u' ((n , v) , (n' , v')) v-v' =
    lemma-⊆*-is-closed-under-concat m n m' n' u v u' v' u-u' v-v'
 
module Sum≥ where
 
  sum : ∀ {n} → FinWord n ℤ → ℤ
  sum {zero} s = 0ℤ
  sum {suc n} s = s zeroF +ᶻ sum {n} (tailF s)

  sum-concat : ∀ {m n} → (u : FinWord m ℤ) → (v : FinWord n ℤ) → sum (concat u v) ≡ sum u +ᶻ sum v
  sum-concat {zero} {n} u v = begin
    sum (concat u v)
    ≡⟨⟩
    sum v
    ≡⟨ ≡sym (+ᶻ-identityˡ (sum v)) ⟩
    0ℤ +ᶻ sum v
    ≡⟨⟩
    sum u +ᶻ sum v
    ∎
  sum-concat {suc m} {n} u v = begin
    sum (concat u v)
    ≡⟨⟩
    u zeroF +ᶻ sum (concat (tailF u) v)
    ≡⟨ ≡cong (λ n → u zeroF +ᶻ n) (sum-concat (tailF u) v) ⟩
    u zeroF +ᶻ (sum (tailF u) +ᶻ sum v)
    ≡⟨ ≡sym (+ᶻ-assoc (u zeroF) (sum (tailF u)) (sum v)) ⟩
    u zeroF +ᶻ sum (tailF u) +ᶻ sum v
    ≡⟨⟩
    sum u +ᶻ sum v
    ∎
  
  ≥+-carrier : Pred' ((FINWord ℤ) × (FINWord ℤ))
  ≥+-carrier ((n , a) , (m , b)) = sum b ≤ᶻ sum a

  ≥+-refl : ∀ (w : FINWord ℤ) → ≥+-carrier (w , w)
  ≥+-refl (n , a) = ≤ᶻ-reflexive ≡refl

  ≥+-trans : ∀ (w w' w'' : FINWord ℤ)
    → ≥+-carrier (w , w')
    → ≥+-carrier (w' , w'')
    → ≥+-carrier (w , w'')
  ≥+-trans (l , a) (m , b) (n , c) p q = ≤ᶻ-trans q p

  ≥+ = aPreorder ≥+-carrier ≥+-refl ≥+-trans

  lemma-≥+-is-closed-under-concat : ∀ m n m' n'
    → (u  : FinWord m ℤ)
    → (v : FinWord n ℤ)
    → (u'  : FinWord m' ℤ)
    → (v' : FinWord n' ℤ)
    → (inj m u , inj m' u') ∈ ≥+-carrier
    → (inj n v , inj n' v') ∈ ≥+-carrier
    → (inj (m + n) (concat u v) , inj (m' + n') (concat u' v')) ∈ ≥+-carrier
  lemma-≥+-is-closed-under-concat m n m' n' u v u' v' u-u' v-v' =
    ≤ᶻ-trans (≤ᶻ-trans p a) q
    where
      a : sum u' +ᶻ sum v' ≤ᶻ sum u +ᶻ sum v
      a = +ᶻ-mono-≤ᶻ u-u' v-v'
      
      p : sum (concat u' v') ≤ᶻ sum u' +ᶻ sum v'
      p = ≤ᶻ-reflexive (sum-concat u' v')

      q : sum u +ᶻ sum v ≤ᶻ sum (concat u v)
      q = ≤ᶻ-reflexive (≡sym (sum-concat u v))

  open ConditionOnQ ℤ
  ≥+-is-closed-under-concat : [ ≥+ ]-is-closed-under-concat
  ≥+-is-closed-under-concat ((m , u) , (m' , u')) u-u' ((n , v) , (n' , v')) v-v' =
    lemma-≥+-is-closed-under-concat m n m' n' u v u' v' u-u' v-v'

module Total (A : Set) where

  total-carrier : Pred' ((FINWord A) × (FINWord A))
  total-carrier _ = ⊤

  total-refl : ∀ (w : FINWord A) → total-carrier (w , w)
  total-refl w = tt

  total-trans : ∀ (w w' w'' : FINWord A)
    → total-carrier (w , w')
    → total-carrier (w' , w'')
    → total-carrier (w , w'')
  total-trans w w' w'' _ _ = tt

  total = aPreorder total-carrier total-refl total-trans
