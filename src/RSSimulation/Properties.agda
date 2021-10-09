----------------------------------------------------------------------
-- properties of reachability-sensitive simulations

module RSSimulation.Properties where
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
  using (_∈_; _∉_; ∅; _⊆′_; U; ｛_｝)
open import Function.Base
  using (case_of_)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation
  using (contradiction)
open import Data.Empty
  using (⊥; ⊥-elim)
open import Data.Unit.Base
  using (⊤; tt)

open import Base
open import Word
open import NA
open import Simulation.Base
open import Simulation.Properties
open import RSSimulation.Base

------------------------------------------------------------------
-- soundness

-- soundness wrt. finite language of fixed length

RSSim-soundFin :
  {X₁ X₂ A : Set} → (na₁ : NA X₁ A) → (na₂ : NA X₂ A)
  → (R : RSSimulation na₁ na₂)
  → (x : X₁) → (y : X₂) → (x , y) ∈ (RSSimulation.𝑅 R)
  → (n : ℕ) → FinAccLang na₁ x n ⊆′ FinAccLang na₂ y n
-- the proof is by induction on the length
--              (in a similar way as `Simᴾ.soundFin`)
-- base case: when the length is `0`
RSSim-soundFin na₁ na₂ (aRSSim R R' R⊎R'-sim) x y xRy 0 =
  -- for any `as : FinWord 0 A`, if `as ∈ FinAccLang na₁ x 0`,
  λ as as∈FinAccLang[x] →
    -- (1) the existence of such `as` implies that
    --     the state `x` is an accepting state
    let x-acc = (Equiv.⇒ (FinAccLang0-∃⇔∈accept na₁ x))
                  (as , as∈FinAccLang[x]) in
    -- (2) by the acceptance condition of simulation,
    --     the state `y` is also an accepting state
    --     in `[ na₂ ]⊥`, and hence in `na₂`
    let y-acc =
          (IsSimulation.acceptance R⊎R'-sim) x (inj₁ y) xRy x-acc in
    -- (3) by (2), `as : FinWord 0 A` is also accepted
    --     in `na₂` from the state `y`
    (Equiv.⇐ (FinAccLang0-Π⇔∈accept na₂ y)) y-acc as
-- inductive case: when the length is `suc n`
RSSim-soundFin na₁ na₂ R⊎R'@(aRSSim R R' R⊎R'-sim) x y xRy (suc n) =
  -- for any `as : FinWord (suc n) A`,
  λ as →
  -- if `as ∈ FinAccLang na₁ x (suc n)`, with
  -- some witness `xs : FinWord (suc (suc n)) X₁` s.t.:
  -- [1] it starts with `x`,
  -- [2] it is a run on `as`,
  -- [3] it ends with an accepting state,
  λ { as∈FinAccLang[x]@(xs , xs-head≡x , xs-run-on-as , _) →
    -- (1) `tailF xs` witnesses acceptance of `tailF as`
    --     from the state `xs 1F`
    let as+∈FinAccLang[xs₁] : (tailF as) ∈ FinAccLang na₁ (xs 1F) n
        as+∈FinAccLang[xs₁] = FinAccLang-pop na₁ as∈FinAccLang[x] in
    -- (2) by the stap-match condition of simulation,
    --     `(x , y) ∈ R` (i.e. `(inj₁ x , y) ∈ "R ⊎ R'"`) and
    --     `(x , as 0F , xs 1F) ≡ (xs 0F , as 0F , xs 1F)
    --                          ∈ NA.trans na₁`
    --     imply existence of some state `z : X₂ ⊎ One` s.t.
    --     `(y , as 0F , z)` is a transition in `[ na₂ ]⊥`
    --     and `(xs 1F , z) ∈ "R ⊎ R'"`
    let (z , y-as₀→z , xs₁R⊎R'z) =
          (IsSimulation.step-match R⊎R'-sim) x (inj₁ y) xRy
            (as 0F) (xs 1F)
            ((NA.trans na₁) ⟨ xs-run-on-as 0F ⟩∋
             (begin
              (xs 0F , as 0F , xs 1F)
             ≡⟨ ≡cong (_, as 0F , xs 1F) xs-head≡x ⟩
              (x , as 0F , xs 1F)
             ∎)) in
    -- (3) by (2) and soundness of the ordinary simulation "R + R'",
    --     `tailF as` is also accepted in `[ na₂ ]⊥` from
    --     the state `z`
    let as+∈FinAccLang[z] : (tailF as) ∈ FinAccLang [ na₂ ]⊥ z n
        as+∈FinAccLang[z] =
          Sim-soundFin na₁ [ na₂ ]⊥ (aSim (R ⟨⊎⟩ʳ R') R⊎R'-sim)
                       (xs 1F) z xs₁R⊎R'z n
                       (tailF as) as+∈FinAccLang[xs₁] in
    -- (4) by case analisys on `z`, we can prove that
    --     `as` is also accepted in `na₂` from the state `y`
    case (inspect' z) of
    λ {
      -- case 1: `z ≡ inj₁ y'` for some `y' : X₂`
      (inj₁ y' with≡ z≡y') →
        -- (1:1) `(xs 1F , y') ∈ R` necessarily holds
        let xs₁Ry' : (xs 1F , y') ∈ R
            xs₁Ry' =
              (R ⟨⊎⟩ʳ R') ⟨ xs₁R⊎R'z ⟩∋
              (begin
                (xs 1F , z)
              ≡⟨ ≡cong (xs 1F ,_) z≡y' ⟩
                (xs 1F , inj₁ y')
              ∎) in
        -- (1:2) by I.H., `tailF as` is accepted in `na₂`
        --       from the state `y'`
        let as+∈FinAccLang[y'] : (tailF as) ∈ FinAccLang na₂ y' n
            as+∈FinAccLang[y'] =
              RSSim-soundFin na₁ na₂ R⊎R' (xs 1F) y' xs₁Ry' n
                             (tailF as) as+∈FinAccLang[xs₁] in
        -- (1:3) therefore, since `(y , as 0F , y')` is a transition
        --       in `na₂`,
        --       `as` is accepted in `na₂` from the state `y`
        FinAccLang-unpop na₂ as+∈FinAccLang[y']
          ((NA.trans [ na₂ ]⊥) ⟨ y-as₀→z ⟩∋
           (begin
             (inj₁ y , as 0F , z)
           ≡⟨ ≡cong (inj₁ y ,_)
                    (≡cong (as 0F ,_) z≡y') ⟩
             (inj₁ y , as 0F , inj₁ y')
           ∎));
      -- case 2: `z ≡ inj₂ sink`
      (inj₂ sink with≡ z≡sink) →
        -- (2:1) `tailF as` is necessarily accepted in `[ na₂ ]⊥`
        --       from the sink state
        let as+∈FinAccLang[sink] :
              (tailF as) ∈ FinAccLang [ na₂ ]⊥ (inj₂ sink) n
            as+∈FinAccLang[sink] =
              (tailF as) ⟨ as+∈FinAccLang[z] ⟩∈
              (begin
                FinAccLang [ na₂ ]⊥ z n
              ≡⟨ ≡cong-app (≡cong (FinAccLang [ na₂ ]⊥) z≡sink) n ⟩
                FinAccLang [ na₂ ]⊥ (inj₂ sink) n
              ∎) in
        -- (2:2) however, this acceptance is actually impossible
        --       because `[ na₂ ]⊥` accepts no word from `sink`,
        --       which means that
        --       this case `z ≡ inj₂ sink` never happens
        ⊥-elim (FinAccLang[sink]-Empty na₂ n (tailF as)
                                       as+∈FinAccLang[sink])
    }
  }

-- soundness wrt. finite language

RSSim-soundFIN :
  {X₁ X₂ A : Set} → (na₁ : NA X₁ A) → (na₂ : NA X₂ A)
  → (R⊎R' : RSSimulation na₁ na₂)
  → (x : X₁) → (y : X₂) → (x , y) ∈ (RSSimulation.𝑅 R⊎R')
  → FINAccLang na₁ x ⊆′ FINAccLang na₂ y
RSSim-soundFIN na₁ na₂ R⊎R' x y xRy =
  ［ RSSim-soundFin na₁ na₂ R⊎R' x y xRy ］'

-- _un_soundness wrt. infinite language

RSSim-¬soundINF :
  ¬ ({X₁ X₂ A : Set} → (na₁ : NA X₁ A) → (na₂ : NA X₂ A)
     → (R⊎R' : RSSimulation na₁ na₂)
     → (x : X₁) → (y : X₂) → (x , y) ∈ (RSSimulation.𝑅 R⊎R')
     → (INFAccLang na₁ x ⊆′ INFAccLang na₂ y))
RSSim-¬soundINF =
  -- if soundness holds,
  λ rssim-sound →
    -- (1) we take the following two NFA
    --     and a reachability-sensitive simulation between them
    -- (1-1) an NFA `nfa0⟲0 : NA (Fin 1) Nat`
    --       with a single non-accepting state `0F : Fin 1`
    --            and a single transition for `0 : Nat`
    let nfa0⟲0 : NA (Fin 1) ℕ
        nfa0⟲0 = record {
          trans  = ｛ (0F , 0 , 0F) ｝; -- transition for `0` only
          init   = U;                   -- `0F` is initial
          accept = ∅                    -- no accepting state
          } in
    -- (1-2) an NFA `nfa0 : NA (Fin 1) Nat`
    --       with a single non-accepting state `0F : Fin 1`
    --            and no transition
    let nfa0 : NA (Fin 1) ℕ
        nfa0 = record {
          trans  = ∅;         -- no transition
          init   = U;         -- `0F` is initial
          accept = ∅          -- no accepting state
          } in
    -- (1-3) a reachability-sensitive simulation between
    --       `nfa0⟲0` and `nfa0`, given by the universal relation
    let rssim:nfa0⟲0-nfa0 : RSSimulation nfa0⟲0 nfa0
        rssim:nfa0⟲0-nfa0 = record {
          𝑅 = U;              -- Fin 1 × Fin 1
          𝑅' = U;             -- Fin 1 × One
          isSimulation = record {
            acceptance =
              -- for all `x : Fin1`
              --         and `y : Fin 1`, if `(x , y) ∈ R`,
              λ x y _ →
              -- `x` is never accepted anyway
              λ ();
            step-match =
              -- for all `x : Fin 1` and `y : (Fin 1) ⊎ One`
              --         s.t. `(x , y) ∈ R`,
              -- and for all `a : Nat` and `x' : Fin 1`
              --         s.t. `(x , a , x') ∈ NA.trans nfa0⟲0`,
              -- `a` is necessarily `0`;
              λ {
                -- when `y ≡ inj₁ 0F`,
                x (inj₁ 0F) _ 0 x' _ →
                  -- we can take the sink state of `[ nfa0 ]⊥`,
                  -- so that:
                  -- [1] `(0F , 0 , sink) ∈ NA.trans [ nfa0 ]⊥`,
                  -- [2] `(x' , sink) ∈ R'`
                  (inj₂ sink , tt , tt);
                -- when `y ≡ inj₂ sink`,
                x (inj₂ sink) _ 0 x' _ →
                  -- we can again take the sink state of `[ nfa0 ]⊥`
                  -- so that:
                  -- [1] `(sink , 0 , sink) ∈ NA.trans [ nfa0 ]⊥`,
                  -- [2] `(x' , sink) ∈ R'`
                  (inj₂ sink , tt , tt)
              }
            }
          } in
    -- (2) by assumption, any infinite word accepted by `nfa0⟲0`
    --     (from its sole state `0F`) must be accepted by `nfa0` too
    --     (from its sole state `0F`)
    let INFAccLang-⊆ : INFAccLang nfa0⟲0 0F ⊆′ INFAccLang nfa0 0F
        INFAccLang-⊆ = rssim-sound {Fin 1} {Fin 1} {ℕ} nfa0⟲0 nfa0
                                   rssim:nfa0⟲0-nfa0 0F 0F tt in
    -- (3) an infinite word "0, 0, 0, ..." is accepted in `nfa0⟲0`,
    --     and therefore, it must be accepted in `nfa0` too
    let 𝟘 : INFWord ℕ
        𝟘 = λ{ _ → 0 }
        𝟘∈INFAccLang[nfa0⟲0] : 𝟘 ∈ INFAccLang nfa0⟲0 0F
        𝟘∈INFAccLang[nfa0⟲0] =
          -- `𝟘` is indeed accepted in `nfa0⟲0` from `0F`, because
          -- we can take the sequence "0F, 0F, ..." of states s.t.:
          ((λ{ _ → 0F })
          -- [1] it starts with `0F`
          , refl
          -- [2] it is a run on `𝟘`
          , (λ{ _ → refl }))
        𝟘∈INFAccLang[nfa0] : 𝟘 ∈ INFAccLang nfa0 0F
        𝟘∈INFAccLang[nfa0] = INFAccLang-⊆ 𝟘 𝟘∈INFAccLang[nfa0⟲0] in
    -- (3) however, the infinite word `𝟘` is not actually accepted
    --     in `nfa0`, which leads to a contradiction
    let 𝟘∉INFAccLang[nfa0] : 𝟘 ∉ INFAccLang nfa0 0F
        𝟘∉INFAccLang[nfa0] =
          -- if `𝟘` is accepted in `nfa0` from `0F`,
          -- which means existence of some `xs : INFWord (Fin 1)`
          -- s.t. [1] it starts with `0F`,
          --      [2] it is a run on `𝟘`,
          λ { (xs , xs-head≡0F , xs-run-on-𝟘) →
            -- there must be a transition `(xs 0 , 0 , xs 1)`
            -- in `nfa0`, but it is not a valid transition
            xs-run-on-𝟘 0
          } in
    contradiction 𝟘∈INFAccLang[nfa0] 𝟘∉INFAccLang[nfa0]
