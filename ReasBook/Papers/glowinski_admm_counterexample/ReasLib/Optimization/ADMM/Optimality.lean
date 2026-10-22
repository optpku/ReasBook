/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Problem

@[expose] public section

namespace ADMM

namespace Problem

/-- A multiplier is optimal when it occurs in a KKT triple. -/
def IsOptimalMultiplier {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (multiplier : Fin m → ℝ) : Prop :=
  ∃ x y, P.IsKKT x y multiplier

/-- Characterization of an optimal multiplier by a KKT triple. -/
theorem isOptimalMultiplier_iff {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (multiplier : Fin m → ℝ) :
    P.IsOptimalMultiplier multiplier ↔ ∃ x y, P.IsKKT x y multiplier := by
  -- Unfolding the definition makes the two propositions identical.
  rfl

end Problem

end ADMM
