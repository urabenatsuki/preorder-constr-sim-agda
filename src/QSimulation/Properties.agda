module QSimulation.Properties where

open import Data.Product using (_×_; _,_)
open import Relation.Unary using (_⊆_)

open import Base
open import Word
open import NA
open import QSimulation.Base

-- monotonicity of Q-trace inclusion
Monotonicity-≤ : {A X X' : Set} {na : NA X A} {na' : NA X' A} →
  (Q Q' : Preorder {FINWord A}) →
  Preorder.carrier Q ⊆ Preorder.carrier Q' →
  ∀ ((x , y) : X × X') →
  x ≤[ na , na' , Q ] y →
  x ≤[ na , na' , Q' ] y
Monotonicity-≤ Q Q' Q⊆Q' (x , y) x≤[Q]y w w∈L*[x] with x≤[Q]y w w∈L*[x]
... | (w' , w'∈L*[y] , [w,w']∈Q) = (w' ,  w'∈L*[y] , Q⊆Q' [w,w']∈Q)

-- properties of M-bounded Q-constrained simulation
open import QSimulation.Bounded public

-- soundness
open import QSimulation.Soundness public
  using (soundness; soundness-of-bounded-simulation)

-- soundness of up-to version
open import QSimulation.SoundnessUpto public
  renaming (soundness to soundness-upto; soundness-of-bounded-simulation to soundness-of-bounded-simulation-upto)

-- completeness
open import QSimulation.Completeness public
  using (completeness)

open import QSimulation.Example public
