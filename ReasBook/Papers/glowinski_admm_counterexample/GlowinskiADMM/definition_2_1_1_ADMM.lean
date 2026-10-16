module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Trajectory

@[expose] public section

/- Compatibility bridge for the shared two-block ADMM problem and trajectory API. -/
#check (ADMM.Trajectory : {n₁ n₂ m : ℕ} → ADMM.Problem n₁ n₂ m → ℝ → ℝ → Type)
