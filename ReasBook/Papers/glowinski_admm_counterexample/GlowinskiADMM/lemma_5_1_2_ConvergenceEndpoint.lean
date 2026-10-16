module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UniformConvergence
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Convergence

@[expose] public section

/- Compatibility checks for the shared uniform-convergence API. -/
#check (ADMM.Trajectory.Converges :
  ∀ {n₁ n₂ m : ℕ} {P : ADMM.Problem n₁ n₂ m} {β γ : ℝ},
    ADMM.Trajectory P β γ → Prop)

#check (ADMM.Trajectory.converges_iff :
  ∀ {n₁ n₂ m : ℕ} {P : ADMM.Problem n₁ n₂ m} {β γ : ℝ}
      {z : ADMM.Trajectory P β γ},
    z.Converges ↔
      Filter.Tendsto z.primalResidual Filter.atTop (nhds 0) ∧
        Filter.Tendsto z.secondIncrement Filter.atTop (nhds 0) ∧
        Filter.Tendsto z.objectiveValue Filter.atTop (nhds P.optimalValue) ∧
        ∃ multiplier, P.IsOptimalMultiplier multiplier ∧
          Filter.Tendsto z.multiplier Filter.atTop (nhds multiplier))

#check (ADMM.Trajectory.ConvergesToKKT :
  ∀ {n₁ n₂ m : ℕ} {P : ADMM.Problem n₁ n₂ m} {β γ : ℝ},
    ADMM.Trajectory P β γ → Prop)

#check (ADMM.Trajectory.convergesToKKT_iff :
  ∀ {n₁ n₂ m : ℕ} {P : ADMM.Problem n₁ n₂ m} {β γ : ℝ}
      {z : ADMM.Trajectory P β γ},
    z.ConvergesToKKT ↔
      ∃ xBar yBar multiplierBar, P.IsKKT xBar yBar multiplierBar ∧
        Filter.Tendsto (fun k ↦ (z.x k, z.y k, z.multiplier k)) Filter.atTop
          (nhds (xBar, yBar, multiplierBar)))

#check (ADMM.UniformConvergenceAt : ℝ → Prop)

#check (ADMM.uniformConvergenceAt_iff :
  ∀ {γ : ℝ}, ADMM.UniformConvergenceAt γ ↔
    ∀ (n₁ n₂ m : ℕ) (P : ADMM.Problem n₁ n₂ m),
      ADMM.IsClosedProperConvex P.f → ADMM.IsClosedProperConvex P.g →
      (∃ x y multiplier, P.IsKKT x y multiplier) →
      ∀ (β : ℝ), 0 < β → ∀ z : ADMM.Trajectory P β γ,
        z.Converges ∧
          (Function.Injective P.A.mulVec → Function.Injective P.B.mulVec →
            z.ConvergesToKKT))

#check (ADMM.uniformConvergenceEndpoint : ℝ)

#check (ADMM.uniformConvergenceEndpoint_def :
  ADMM.uniformConvergenceEndpoint =
    sSup {c : ℝ | 0 < c ∧ ∀ γ, 0 < γ → γ < c → ADMM.UniformConvergenceAt γ})
