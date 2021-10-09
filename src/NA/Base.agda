-- definition of nondeterministic automata and accepted language
module NA.Base where
open import Level
  using (Level)
  renaming (zero to lzero; suc to lsuc)
open import Data.Nat
  using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Fin
  using (Fin; inject₁; inject≤; inject+; cast; toℕ; fromℕ; fromℕ<)
  renaming (zero to 0F; suc to sucF)
open import Data.Product
  using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum
  using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong)
  renaming (sym to ≡sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Relation.Unary
  using (_∈_; _⟨⊎⟩_; ∅)
open import Data.Empty
  using (⊥)
open import Data.Unit.Base
  using (⊤)

open import Base.Pred
open import FinForWord
open import Word


------------------------------------------------------------------
-- the type of nondeterministic automata
-- with state space `X` and alphabet `A`
-- NB. `X` and `A` are parameters of the record type NA,
--     rather than fields of the record type,
--     so that these are visible from outside
--     (which is important to work with languages and simulations)
record NA (X A : Set) : Set₁ where
  constructor anNA
  field
    trans  : Pred' (X × A × X)       -- transition relation
    init   : Pred' X                 -- initial states
    accept : Pred' X                 -- accepting states

------------------------------------------------------------------
-- accepted languages

-- L_A^n(x), the _finite accepted language of length n_
-- of state x in automaton A

FinAccLang : {X A : Set} -> NA X A -> X
  -> (n : ℕ) -> Pred' (FinWord n A)
FinAccLang na x n =
  -- an input word `as : FinWord n A` is accepted iff:
  λ as ->
  -- there exists some sequence `xs : FinWord (suc n) X` such that:
  ∃ λ xs ->
    -- [1] `xs` starts with `x`
    (headF xs) ≡ x
    -- [2] `xs` is a run on the input word `as`,
    --     i.e. for all index `i : Fin n`,
    --          `("xs i" , as i , xs (sucF i))` is a transition
    --     NB. `inject₁` necessary for "xs i"
    × (∀ i -> (xs (inject₁ i) , as i , xs (sucF i)) ∈ (NA.trans na))
    -- [3] `xs` ends with an accepting state
    × (lastF xs) ∈ (NA.accept na)

FinWord-from[_]to[_] :
  {X A : Set} → X → X → NA X A
  → (n : ℕ) → Pred' (FinWord n A)
FinWord-from[ x ]to[ x' ] na n =
  -- an input word `as : FinWord n A` is a word from x to x' iff:
  λ as →
  -- there exists some sequence `xs : FinWord (suc n) X` such that:
  ∃ λ xs →
    -- [1] `xs` starts with `x`
    (headF xs) ≡ x
    -- [2] `xs` is a run on the input word `as`,
    × (∀ i → (xs (inject₁ i) , as i , xs (sucF i)) ∈ (NA.trans na))
    -- [3] `xs` ends with the accepting state `x'`
    × (lastF xs) ≡ x'

FinAccLang-from[_]to[_] :
  {X A : Set} → X → X → NA X A
  → (n : ℕ) → Pred' (FinWord n A)
FinAccLang-from[ x₀ ]to[ x ] na n =
  -- an input word `as : FinWord n A` is accepted iff:
  λ as →
    (as ∈ FinWord-from[ x₀ ]to[ x ] na n)
    × x ∈ (NA.accept na)

-- L_A^*(x), the _finite accepted language_
-- of state x in automaton A


FINAccLang : {X A : Set} -> NA X A -> X -> Pred' (FINWord A)
FINAccLang na x = ［ FinAccLang na x ］

FINWord-from[_]to[_] : {X A : Set} → X → X → NA X A → Pred' (FINWord A)
FINWord-from[ x ]to[ x' ] na = ［ FinWord-from[ x ]to[ x' ] na ］

FINAccLang-from[_]to[_] : {X A : Set} → X → X → NA X A → Pred' (FINWord A)
FINAccLang-from[ x₀ ]to[ x ] na = ［ FinAccLang-from[ x₀ ]to[ x ] na ］

[x⇝[w]x']and[x'∈F]⇒[w∈L[x]] : {X A : Set} →
  (na : NA X A) → (x x' : X) → (w : FINWord A) →
  w ∈ FINWord-from[ x ]to[ x' ] na →
  x' ∈ NA.accept na →
  w ∈ FINAccLang na x
[x⇝[w]x']and[x'∈F]⇒[w∈L[x]] {X} {A} na x x' w@(inj n ww)
  x⇝[w]x'@(xs , xs₀≡x , ∀i[] , xsₙ≡x') x'∈F =
  (xs , xs₀≡x , ∀i[] , step-∋ (NA.accept na) x'∈F (≡sym xsₙ≡x'))

-- L_A^ω(x), the _infinite acceped language_
-- of state x in automaton A

INFAccLang : {X A : Set} → NA X A → X → Pred' (INFWord A)
INFAccLang na x =
  -- an input word `as : INFWord A` is accepted iff:
  λ as ->
  -- there exists some sequence `xs : INFWord A` such that:
  ∃ λ xs ->
    -- [1] `xs` starts with `x`
    (headI xs) ≡ x
    -- [2] `xs` is a run on the input word `as`,
    --     i.e. for all index `k : Nat`,
    --          `(xs k , as k , xs (suc k))` is a transition
    × (∀ k -> (xs k , as k , xs (suc k)) ∈ (NA.trans na))

-- L_A^∞(x), the _accepted language_ of state x in automaton A

AccLang : {X A : Set} → NA X A → X → Pred' (Word A)
AccLang na x = (FINAccLang na x) ⟨⊎⟩ (INFAccLang na x)

------------------------------------------------------------------
-- adding a global sink state

data One : Set where
  sink : One

-- (_)⊥

add-global-sink : {X A : Set} → NA X A → NA (X ⊎ One) A
add-global-sink (anNA trans init accept) =
  record {
    -- transitions are given by:
    --   trans : X × A × X
    --   U     : (X ⊎ One) × A × One
    --   ∅     : One × A × X
    trans  = (λ{ (inj₁ x ,    a , inj₁ y)    -> trans (x , a , y);
                 (inj₁ x ,    a , inj₂ sink) -> ⊤;
                 (inj₂ sink , a , inj₂ sink) -> ⊤;
                 (inj₂ sink , a , inj₁ x)    -> ⊥ });
    -- initial/accepting states are the same as original
    init   = Data.Sum.[ init ,   ∅ ]; 
    accept = Data.Sum.[ accept , ∅ ]
  }

syntax add-global-sink na = [ na ]⊥
