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
