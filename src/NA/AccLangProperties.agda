module NA.AccLangProperties where
open import Level
  using (Level)
  renaming (zero to lzero; suc to lsuc)
open import Data.Nat
  using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Fin
  using (Fin; inject₁; inject≤; inject+; cast; toℕ; fromℕ; fromℕ<)
  renaming (zero to zeroF; suc to sucF)
open import Data.Fin.Patterns
open import Data.Product
  using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum
  using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)
  renaming (sym to ≡sym; cong to ≡cong; cong-app to ≡cong-app)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Relation.Unary
  using (_∈_; _⟨⊎⟩_; ∅; Satisfiable; Universal; Empty)
open import Function.Base
  using (id; case_of_)

open import Relation.Nullary using(¬_)
open import Relation.Nullary.Negation
  using (contradiction; contraposition; ¬∃⟶∀¬)
  
open import Data.Empty
  using (⊥; ⊥-elim)
open import Data.Unit.Base
  using (⊤; tt)

open import FinForWord
open import Base
open import Word
open import NA.Base

------------------------------------------------------------------
-- accepted languages of length 0, i.e. `FinAccLang _ _ 0`

-- L_A^0(x), as a predicate on A^0, is satisfiable
-- iff it is universal

FinAccLang0-∃⇔Π :
  {X A : Set} → (na : NA X A) → (x : X)
  → ∃⟨ FinAccLang na x 0 ⟩ ⇔ Π[ FinAccLang na x 0 ]

FinAccLang0-∃⇔Π na x = (pf⇒ , pf⇐)
  where
  pf⇒ : ∃⟨ FinAccLang na x 0 ⟩ → (∀ as → as ∈ FinAccLang na x 0)
  pf⇒ =
    -- given some `as' : FinWord 0 A` that satisfies
    -- `as' ∈ FinAccLang na x 0`,
    -- it comes with some sequence `xs : FinWord 1 X` s.t.:
    -- [1] it starts with `x`,
    -- [2] it is a run on `as'`,
    -- [3] it ends with an accepting state
    λ { (as' , xs , xs-head≡x , xs-run-on-as' , xs-last-acc ) →
      -- then for any `as : FinWord 0 A`,
      λ as →
        -- the sequence `xs` also witnesses acceptance of `as`;
        -- in particular, `xs` is a run on `as` too,
        -- because no transition is necessary
        (xs , xs-head≡x , (λ{ () }) , xs-last-acc)
    }
  pf⇐ : (∀ as → as ∈ FinAccLang na x 0) → ∃⟨ FinAccLang na x 0 ⟩
  pf⇐ assump =
    -- we can take `emptyF : FinWord 0 A` as an evidence
    (emptyF , assump emptyF)

-- for any state x,
-- L_A^0(x) is universal as a predicate on A^0
-- (which implies that the empty word is accepted from the state x),
-- iff the state x is an accepting state

FinAccLang0-Π⇔∈accept :
  {X A : Set} → (na : NA X A) → (x : X)
  → Π[ FinAccLang na x 0 ] ⇔ (x ∈ NA.accept na)
FinAccLang0-Π⇔∈accept na x = (pf⇒ , pf⇐)
  where
  pf⇒ : (∀ as → as ∈ FinAccLang na x 0) → (x ∈ NA.accept na)
  pf⇒ assump =
    -- by assumption, the empty word is accepted from `x`,
    -- i.e. there exists some sequence `xs : FinWord 1 X` such that:
    --      [1] it starts with `x`,
    --      [2] it is a run on `as`,
    --      [3] it ends with an accepting state
    let (xs , xs-head≡x , xs-run-on-as , xs-last-acc) =
          assump emptyF in
    -- since `xs` has length 1, it must end with `x`,
    -- which implies that `x` is an accepting state
    (NA.accept na) ⟨ xs-last-acc ⟩∋
    (begin (lastF xs) ≡⟨ xs-head≡x ⟩ x ∎)
  pf⇐ : (x ∈ NA.accept na) → (∀ as → as ∈ FinAccLang na x 0)
  pf⇐ x-acc =
    -- for any `as : FinWord 0 A`,
    λ as →
      -- `x` as a sequence witnesses acceptance of `as` from `x`,
      ((λ{ 0F → x })
      -- because [1] it starts with `x`
      , refl
      -- [2] it is trivially a run on `as`, involving no transition
      , (λ{ () })
      -- [3] it ends with `x`,
      --     which is an accepting state by assumption
      , x-acc)

-- L_A^0(x), as a predicate on A^0, is satisfiable
-- iff the state x is an accepting state

FinAccLang0-∃⇔∈accept :
  {X A : Set} → (na : NA X A) → (x : X)
  → ∃⟨ FinAccLang na x 0 ⟩ ⇔ (x ∈ NA.accept na)
FinAccLang0-∃⇔∈accept na x =
  (FinAccLang0-∃⇔Π na x) ⊙ (FinAccLang0-Π⇔∈accept na x)

------------------------------------------------------------------
-- empty finite/infinite accepted languages

-- for any state x of an NA,
-- its finite accepted language is empty
-- if the NA has no accepting state

FINAccLang-Empty-if-accept-Empty :
  {X A : Set} → (na : NA X A) → (x : X)
  → Empty (NA.accept na) → Empty (FINAccLang na x)
FINAccLang-Empty-if-accept-Empty na x accept-Empty =
  -- for any `as : FinWord n A`,
  λ { (inj n as) →
    -- if `as ∈ FinAccLang na x n`,
    -- i.e. if there exists some `xs : FinWord (suc n) X` s.t.
    --      [1] it starts with `x`,
    --      [2] it is a run on `as`,
    --      [3] it ends with an accepting state,
    λ { (xs , _ , _ , xs-last-acc ) →
      -- then there must exist an ending state, namely `lastF xs`,
      -- which is however not the case by assumption `accept-Empty`
      accept-Empty (lastF xs) xs-last-acc
    }
  }

-- for any state x of an NA,
-- its infinite accepted language is empty
-- if the NA has no transitions

INFAccLang-Empty-if-trans-Empty :
  {X A : Set} → (na : NA X A) → (x : X)
  → Empty (NA.trans na) → Empty (INFAccLang na x)
INFAccLang-Empty-if-trans-Empty na x trans-Empty =
  -- for any `as : INFWord A`,
  λ as →
  -- if `as ∈ INFAccLang na x`,
  -- i.e. if there exists some `xs : INFWord X` s.t.
  --      [1] it starts with `x`,
  --      [2] it is a run on `as`,
  λ { (xs , _ , xs-run-on-as) →
    -- then there must exist a transition,
    -- namely `(xs 0 , as 0 , xs 1)`, because `xs` is a run on `as`
    -- however this is not the case by assumption `trans-Empty`
    trans-Empty (xs 0 , as 0 , xs 1) (xs-run-on-as 0)
  }

------------------------------------------------------------------
-- acceptance and `tailF`, `tailI`
--
-- especially useful in inductive reasoning about `FinAccLang`

-- popping the head element from an accepted word

FinAccLang-pop :
  {X A : Set} → (na : NA X A)
  → {x : X} → ∀ {n : ℕ} → ∀ {as : FinWord (suc n) A}
  → (as∈FinAccLang[x] : as ∈ FinAccLang na x (suc n))
  → (tailF as) ∈ FinAccLang na ((proj₁ as∈FinAccLang[x]) 1F) n
FinAccLang-pop na =
  -- implicitly for any `as : FinWord (suc n) A`,
  -- if `as ∈ FinAccLang na x (suc n)`,
  -- i.e. if there exists some `xs : FinWord (suc (suc n)) X` s.t.:
  --      [1] it starts with `x`,
  --      [2] it is a run on `as`,
  --      [3] it ends with an accepting state,
  λ { (xs , xs-head≡x , xs-run-on-as , xs-last-acc) →
    -- then `tailF xs` witnesses acceptance of `tailF as`
    -- from the state `xs 1F`
    (tailF xs
    -- because [1] `tailF xs` starts with `xs 1F` indeed,
    , refl
    -- [2] `tailF xs` is a run on `tailF as`,
    , (λ{ i → xs-run-on-as (sucF i) })
    -- [3] `tailF xs` ends with an accepting state
    , xs-last-acc)
  }

INFAccLang-pop :
  {X A : Set} → (na : NA X A)
  → {x : X} → ∀ {as : INFWord A}
  → (as∈INFAccLang[x] : as ∈ INFAccLang na x)
  → (tailI as) ∈ INFAccLang na ((proj₁ as∈INFAccLang[x]) 1)
INFAccLang-pop na =
  -- implicitly for any `as : INFWord A`,
  -- if `as ∈ INFAccLang na x`,
  -- i.e. if there exists some `xs : INFWord X` s.t.:
  --      [1] it starts with `x`,
  --      [2] it is a run on `as`,
  λ { (xs , xs-head≡x , xs-run-on-as) →
    -- then `tailI xs` witnesses acceptance of `tailI as`
    -- from the state `xs 1`
    (tailI xs
    -- because [1] `tailI xs` starts with `xs 1` indeed,
    , refl
    -- [2] `tailI xs` is a run on `tailI as`
    , (λ{ k → xs-run-on-as (suc k) }))
  }

-- pushing back a popped element to an accepted word

FinAccLang-unpop :
  {X A : Set} → (na : NA X A)
  → ∀ {x x' : X} → ∀ {n : ℕ} → ∀ {as : FinWord (suc n) A}
  → (tailF as ∈ FinAccLang na x n)
  → (x' , headF as , x) ∈ (NA.trans na)
  → as ∈ FinAccLang na x' (suc n)
FinAccLang-unpop =
  -- implicitly for any `x' : X` and `as : FinWord (suc n) A`,
  λ na {x} {x'} {n} {as} →
  -- if `tailF as ∈ FinAccLang na x n`,
  -- i.e. if there exists some `xs : FinWord (suc n) X` s.t.:
  --      [1] it starts with `x`,
  --      [2] it is a run on `tailF as`,
  --      [3] it ends with an accepting state,
  λ { (xs , xs-head≡x , xs-run-on-as+ , xs-last-acc) →
    -- if `(x' , headF a , x) ∈ NA.trans na`,
    λ x'-as₀→x →
      -- then `x' ∷ᶠ xs` witnesses acceptance of `as`
      -- from the state `x'`
      (x' ∷ᶠ xs
      -- because [1] `x' ∷ᶠ xs` starts with `x'` indeed,
      , refl
      -- [2] `x' ∷ᶠ xs` is a run on `as`,
      , (λ{ 0F → (NA.trans na) ⟨ x'-as₀→x ⟩∋
                  (begin
                    (x' , headF as , x)
                  ≡˘⟨ ≡cong (x' ,_)
                            (≡cong (headF as ,_) xs-head≡x) ⟩
                    (x' , headF as , headF xs)
                  ∎);
            (sucF i) → xs-run-on-as+ i })
      -- [3] `x' ∷ᶠ xs` ends with an accepting state
      , xs-last-acc)
  }

INFAccLang-unpop :
  {X A : Set} → (na : NA X A)
  → ∀ {x x' : X} → ∀ {as : INFWord A}
  → (tailI as ∈ INFAccLang na x)
  → (x' , headI as , x) ∈ (NA.trans na)
  → as ∈ INFAccLang na x'
INFAccLang-unpop =
  -- implicitly for any `x' : X` and `as : INFWord A`,
  λ na {x} {x'} {as} →
  -- if `tailI as ∈ INFAccLang na x`,
  -- i.e. if there exists some `xs : INFWord X` s.t.:
  --      [1] it starts with `x`,
  --      [2] it is a run on `tailI as`,
  λ { (xs , xs-head≡x , xs-run-on-as+) →
    -- if `(x' , headI as , x) ∈ NA.trans na`,
    λ x'-as₀→x →
      -- then `x' ∷ⁱ xs` witnesses acceptance of `as`
      -- from the state `x'`
      (x' ∷ⁱ xs
      -- because [1] `x' ∷ⁱ xs` starts with `x'` indeed,
      , refl
      -- [2] `x' ∷ⁱ xs` is a run on `as`
      , (λ{ 0 → (NA.trans na) ⟨ x'-as₀→x ⟩∋
                 (begin
                   (x' , headI as , x)
                 ≡˘⟨ ≡cong (x' ,_)
                           (≡cong (headI as ,_) xs-head≡x) ⟩
                   (x' , headI as , headI xs)
                 ∎);
            (suc k) → xs-run-on-as+ k }))
  }

------------------------------------------------------------------
-- finite/infinite accepted languages in `[ na ]⊥`

-- finite language of `sink` is empty

FinAccLang[sink]-Empty :
  {X A : Set} → (na : NA X A) → ∀ (n : ℕ)
  → Empty (FinAccLang [ na ]⊥ (inj₂ sink) n)
-- the proof is by induction on the length `n`
-- base case: when the length is `0`
FinAccLang[sink]-Empty na 0 =
  -- accepted language of length `0` is empty,
  -- because the sink state is not an accepting state
  ¬∃⟶∀¬
  (contraposition
    (Equiv.⇒ (FinAccLang0-∃⇔∈accept [ na ]⊥ (inj₂ sink)))
    id)
-- inductive case: when the length is `suc n` for some `n : Nat`
FinAccLang[sink]-Empty na (suc n) =
  -- for any `as : FinWord (suc n) A`,
  λ as →
  -- if `as ∈ FinAccLang [ na ]⊥ (inj₂ sink) (suc n)`,
  -- i.e. if there exists some `xs : FinWord (suc (suc n)) (X ⊎ One)`
  --      s.t. [1] it starts with `inj₂ sink`,
  --           [2] it is a run on `as`,
  --           [3] it ends with an accepting state,
  λ { as∈FinAccLang[x]@(xs , xs-head≡sink , xs-run-on-as , _) →
    -- (1) `tailF as` is accepted from the state `xs 1F`
    let as+∈FinAccLang[xs₁] :
          (tailF as) ∈ FinAccLang [ na ]⊥ (xs 1F) n
        as+∈FinAccLang[xs₁] =
          FinAccLang-pop [ na ]⊥ as∈FinAccLang[x] in
    -- (2) `xs 1F` is actually the global sink state
    let xs₁≡sink : (xs 1F) ≡ (inj₂ sink)
        xs₁≡sink =
          -- the proof is by case analysis on `xs 1F`
          case inspect' (xs 1F) of
          λ {
            -- case 1: `xs 1F ≡ inj₁ x'` for some `x' : X`
            (inj₁ x' with≡ xs₁≡x') →
              -- (1:1) there is necessarily a transition
              --       `(inj₂ sink , as 0F , inj₁ x')` in `[ na ]⊥`
              let sink-as₀→x' :
                    (inj₂ sink , as 0F , inj₁ x') ∈ NA.trans [ na ]⊥
                  sink-as₀→x' =
                    (NA.trans [ na ]⊥) ⟨ xs-run-on-as 0F ⟩∋
                    (begin
                      (xs 0F , as 0F , xs 1F)
                    ≡⟨ ≡cong (_, as 0F , xs 1F) xs-head≡sink ⟩
                      (inj₂ sink , as 0F , xs 1F)
                    ≡⟨ ≡cong (inj₂ sink ,_)
                             (≡cong (as 0F ,_) xs₁≡x') ⟩
                      (inj₂ sink , as 0F , inj₁ x')
                    ∎) in
              -- (1:2) however, this transition is not possible,
              --       which means that
              --       this case `xs 1F ≡ inj₁ x'` never happens
              ⊥-elim sink-as₀→x';
            -- case 2: `xs 1F ≡ inj₂ sink`, where proof is trivial
            (inj₂ sink with≡ xs₁≡sink) → xs₁≡sink
          } in
    -- (3) by (1) and (2), `tailF as` is necessarily accepted
    --     from the global sink state
    let as+∈FinAccLang[sink] :
          (tailF as) ∈ FinAccLang [ na ]⊥ (inj₂ sink) n
        as+∈FinAccLang[sink] =
          (tailF as) ⟨ as+∈FinAccLang[xs₁] ⟩∈
          (begin
            FinAccLang [ na ]⊥ (xs 1F) n
          ≡⟨ ≡cong-app (≡cong (FinAccLang [ na ]⊥) xs₁≡sink) n ⟩
            FinAccLang [ na ]⊥ (inj₂ sink) n
          ∎) in
    -- (4) however, the acceptance of `tailF as` cannot
    --     actually be the case, because by I.H.,
    --     the sink state accepts no word of length `n`
    FinAccLang[sink]-Empty na n (tailF as) as+∈FinAccLang[sink]
  }

FINAccLang[sink]-Empty :
  {X A : Set} → (na : NA X A)
  → Empty (FINAccLang [ na ]⊥ (inj₂ sink))
FINAccLang[sink]-Empty na = ［ FinAccLang[sink]-Empty na ］'

-- infinite language of `sink`, as a predicate on infinite words,
-- is universal

INFAccLang[sink]-Π :
  {X A : Set} → (na : NA X A)
  → Π[ INFAccLang [ na ]⊥ (inj₂ sink) ]
INFAccLang[sink]-Π na =
  -- for any `as : INFWord A`,
  λ as →
    -- the infinite sequence of just `sink` witnesses acceptance
    -- of `as` from `sink`,
    ((λ{ _ → inj₂ sink })
    -- because [1] it starts with `sink`
    , refl
    -- [2] it is indeed a run on `as`,
    --     i.e. for any `k : Nat`, `("sink" , as k , "sink")` is a
    --     transition in `[ na ]⊥`
    , (λ{ _ → tt }))
