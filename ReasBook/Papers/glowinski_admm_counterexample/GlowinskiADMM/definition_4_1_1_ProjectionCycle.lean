/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.ProjectionCycle

@[expose] public section

universe u

/- The compatibility surface for finite cyclic ADMM configurations. -/
#check (ConsensusADMM.CycleConfig :
  (N : ℕ) → (E : Type u) → [AddCommGroup E] → [Module ℝ E] → Type u)
