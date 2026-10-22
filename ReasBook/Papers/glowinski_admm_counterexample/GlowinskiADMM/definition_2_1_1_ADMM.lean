/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Trajectory

@[expose] public section

/- Compatibility bridge for the shared two-block ADMM problem and trajectory API. -/
#check (ADMM.Trajectory : {n₁ n₂ m : ℕ} → ADMM.Problem n₁ n₂ m → ℝ → ℝ → Type)
