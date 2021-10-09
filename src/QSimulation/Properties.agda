module QSimulation.Properties where

-- soundness
open import QSimulation.Soundness public
  using (soundness)

-- soundness of up-to version
open import QSimulation.SoundnessUpto public
  renaming (soundness to soundness-upto)

-- completeness
open import QSimulation.Completeness public
  using (completeness)
