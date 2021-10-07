module QSimulation.Properties where

open import QSimulation.Soundness public
  using (soundness)

open import QSimulation.SoundnessUpto public
  renaming (soundness to soundness-upto)

open import QSimulation.Completeness public
  using (completeness)
