module Simulation.Properties where
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
  using (_∈_; _⟨⊎⟩_; ∅; Satisfiable; Universal; Empty; Pred; _⊆′_)
open import Function.Base
  using (id; case_of_)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation
  using (contradiction; contraposition; ¬∃⟶∀¬)
  
open import Data.Empty
  using (⊥; ⊥-elim)
open import Data.Unit.Base
  using (⊤; tt)

open import Base
open import Word
open import NA
open import Simulation.Base

------------------------------------------------------------------
-- the empty relation ∅ is always a simulation between any NA

∅-sim : {X₁ X₂ A : Set} → (na₁ : NA X₁ A) → (na₂ : NA X₂ A)
        → IsSimulation na₁ na₂ ∅
∅-sim na₁ na₂ = record {
  acceptance =
    -- for all `x : X₁` and `y : X₂`, `(x , y) ∈ R` never holds
    λ x y → λ ();
  step-match =
    -- the same as above
    λ x y → λ ()
  }

------------------------------------------------------------------
-- soundness

-- soundness wrt. finite language of fixed length

Sim-soundFin :
  {a : Level} {X₁ X₂ A : Set} → (na₁ : NA X₁ A) → (na₂ : NA X₂ A)
  → (R : Simulation {a} na₁ na₂)
  → (x : X₁) → (y : X₂) → (x , y) ∈ (Simulation.𝑅 R)
  → (n : ℕ) → FinAccLang na₁ x n ⊆′ FinAccLang na₂ y n
-- the proof is by induction on the length
-- base case: when the length is `0`
Sim-soundFin na₁ na₂ (aSim R R-sim) x y xRy 0 =
  -- for any `as : FinWord 0 A`, if `as ∈ FinAccLang na₁ x 0`,
  λ as as∈FinAccLang[x] →
    -- (1) the existence of such `as` implies that
    --     the state `x` is an accepting state
    let x-acc = (Equiv.⇒ (FinAccLang0-∃⇔∈accept na₁ x))
                  (as , as∈FinAccLang[x]) in
    -- (2) by the acceptance condition of simulation,
    --     the state `y` is also an accepting state
    let y-acc = (IsSimulation.acceptance R-sim) x y xRy x-acc in
    -- (3) by (2), `as : FinWord 0 A` is also accepted
    --     in `na₂` from the state `y`
    (Equiv.⇐ (FinAccLang0-Π⇔∈accept na₂ y)) y-acc as
-- inductive case: when the length is `suc n`
Sim-soundFin na₁ na₂ (aSim R R-sim) x y xRy (suc n) =
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
    --     `(x , y) ∈ R` and
    --     `(x , as 0F , xs 1F) ≡ (xs 0F , as 0F , xs 1F)
    --                          ∈ NA.trans na₁`
    --     imply existence of some state `y' : X₂` s.t.
    --     `(y , as 0F , y')` is a transition in `na₂`
    --     and `(xs 1F , y') ∈ R`
    let (y' , y-as₀→y' , xs₁Ry') =
          (IsSimulation.step-match R-sim) x y xRy (as 0F) (xs 1F)
          ((NA.trans na₁) ⟨ xs-run-on-as 0F ⟩∋
           (begin
            (xs 0F , as 0F , xs 1F)
           ≡⟨ ≡cong (_, as 0F , xs 1F) xs-head≡x ⟩
            (x , as 0F , xs 1F)
           ∎)) in
    -- (4) by I.H., `tailF as` is also accepted in `na₂`
    --     from the state `y'`,
    let as+∈FinAccLang[y'] : (tailF as) ∈ (FinAccLang na₂ y' n)
        as+∈FinAccLang[y'] =
          Sim-soundFin na₁ na₂ (aSim R R-sim) (xs 1F) y' xs₁Ry'
                       n (tailF as) as+∈FinAccLang[xs₁] in
    -- (5) since `(y , as 0F , y')` is a transition in `na₂`,
    --     `as` is accepted in `na₂` from the state `y`
    FinAccLang-unpop na₂ as+∈FinAccLang[y'] y-as₀→y'
  }

-- soundness wrt. finite language

Sim-soundFIN :
  {a : Level} {X₁ X₂ A : Set} → (na₁ : NA X₁ A) → (na₂ : NA X₂ A)
  → (R : Simulation {a} na₁ na₂)
  → (x : X₁) → (y : X₂) → (x , y) ∈ (Simulation.𝑅 R)
  → FINAccLang na₁ x ⊆′ FINAccLang na₂ y
Sim-soundFIN na₁ na₂ R x y xRy =
  ［ Sim-soundFin na₁ na₂ R x y xRy ］'

-- soundness wrt. infinite language

Sim-soundINF :
  {a : Level} {X₁ X₂ A : Set} → (na₁ : NA X₁ A) → (na₂ : NA X₂ A)
  → (R : Simulation {a} na₁ na₂)
  → (x : X₁) → (y : X₂) → (x , y) ∈ (Simulation.𝑅 R)
  → INFAccLang na₁ x ⊆′ INFAccLang na₂ y
Sim-soundINF {a} {X₁} {X₂} {A} na₁ na₂ (aSim R R-sim) x y xRy
  -- for any `as : INFWord A`,
  as
  -- if `as ∈ INFAccLang na₂ x`, with some
  -- witness `xs : INFWord X₁` s.t.:
  -- [1] it starts with `x`,
  -- [2] it is a run on `as`,
  (xs , xs-head≡x , xs-run-on-as) =
    -- we will construct a sequence `ys : INFWord X₂` s.t.:
    -- [1] it starts with `y`,
    -- [2] it is a run on `as`,
    -- [3] at any point `k : Nat`, `(xs k , ys k) ∈ R`
    -- inductively below;
    -- the additional property [3] is crucial to get induction work
    (ys , refl , ys-run-on-as)
  where
  ys : INFWord X₂
  ys-run-on-as :
    ∀ (k : ℕ) → (ys k , as k , ys (suc k)) ∈ (NA.trans na₂)
  xsRys :
    ∀ (k : ℕ) → (xs k , ys k) ∈ R
  -- construction of the sequence `ys`: base case
  ys 0 =
    -- we take `y` as the head of `ys`
    y
  -- construction of the sequence `ys`: inductive case
  ys (suc n) =
    -- by I.H., we have `ys n : X₂` s.t. [3] 
    -- therefore, by the step-match condition of simulation,
    -- `(xs n , ys n) ∈ R` and
    -- `(xs n , as n , xs (suc n)) ∈ NA.trans na₁`
    -- imply existence of some state `y' : X₂` s.t.
    -- `(ys n , as n , y') ∈ NA.trans na₂`
    -- and `(xs (suc n) , y') ∈ R'
    let (y' , ys[n]-as[n]→y' , xs[n+1]Rys[n+1]) =
          (IsSimulation.step-match R-sim) (xs n) (ys n) (xsRys n)
          (as n) (xs (suc n)) (xs-run-on-as n) in
    -- we can take `y'` as `ys (suc n)`
    y'
  -- the property [1]: clear by the way `ys` is constructed
  ys-run-on-as n =
    let (y' , ys[n]-as[n]→y' , xs[n+1]Rys[n+1]) =
          (IsSimulation.step-match R-sim) (xs n) (ys n) (xsRys n)
          (as n) (xs (suc n)) (xs-run-on-as n) in
    ys[n]-as[n]→y'
  -- the property [3] at the head: consequence of assumptions
  xsRys 0 = R ⟨ xRy ⟩∋
            (begin
              (x , y)
            ≡˘⟨ ≡cong (_, y) xs-head≡x ⟩
              (headI xs , y)
            ∎)
  -- the property [3] at the tail:
  -- clear by the way `ys` is constructed
  xsRys (suc n) =
    let (y' , ys[n]-as[n]→y' , xs[n+1]Rys[n+1]) =
          (IsSimulation.step-match R-sim) (xs n) (ys n) (xsRys n)
          (as n) (xs (suc n)) (xs-run-on-as n) in
    xs[n+1]Rys[n+1]
