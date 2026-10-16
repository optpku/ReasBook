module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Convergence

@[expose] public section

/- Theorem 2.1.2 (1): for an exact ADMM trajectory with closed proper convex
objectives, a KKT solution, `0 < β`, and `0 < γ ≤ 377 / 200`, the first
constraint images converge. -/
#check (ADMM.leftImage_tendsto :
  ∀ {n₁ n₂ m : ℕ} (P : ADMM.Problem n₁ n₂ m),
    ADMM.IsClosedProperConvex P.f → ADMM.IsClosedProperConvex P.g →
    (∃ x y multiplier, P.IsKKT x y multiplier) → ∀ {β γ : ℝ},
    0 < β → 0 < γ → γ ≤ (377 : ℝ) / 200 → ∀ z : ADMM.Trajectory P β γ,
    ∃ q : Fin m → ℝ,
      Filter.Tendsto (fun k ↦ P.A.mulVec (z.x k)) Filter.atTop (nhds q))

/- Theorem 2.1.2 (2): under the same hypotheses, the second constraint images
of the exact ADMM trajectory converge. -/
#check (ADMM.rightImage_tendsto :
  ∀ {n₁ n₂ m : ℕ} (P : ADMM.Problem n₁ n₂ m),
    ADMM.IsClosedProperConvex P.f → ADMM.IsClosedProperConvex P.g →
    (∃ x y multiplier, P.IsKKT x y multiplier) → ∀ {β γ : ℝ},
    0 < β → 0 < γ → γ ≤ (377 : ℝ) / 200 → ∀ z : ADMM.Trajectory P β γ,
    ∃ q : Fin m → ℝ,
      Filter.Tendsto (fun k ↦ P.B.mulVec (z.y k)) Filter.atTop (nhds q))

/- Theorem 2.1.2 (3): under the same hypotheses, the primal residuals of the
exact ADMM trajectory tend to zero. -/
#check (ADMM.primalResidual_tendsto_zero :
  ∀ {n₁ n₂ m : ℕ} (P : ADMM.Problem n₁ n₂ m),
    ADMM.IsClosedProperConvex P.f → ADMM.IsClosedProperConvex P.g →
    (∃ x y multiplier, P.IsKKT x y multiplier) → ∀ {β γ : ℝ},
    0 < β → 0 < γ → γ ≤ (377 : ℝ) / 200 → ∀ z : ADMM.Trajectory P β γ,
    Filter.Tendsto z.primalResidual Filter.atTop (nhds 0))

/- Theorem 2.1.2 (4): under the same hypotheses, the second-block image
increments of the exact ADMM trajectory tend to zero. -/
#check (ADMM.secondIncrement_tendsto_zero :
  ∀ {n₁ n₂ m : ℕ} (P : ADMM.Problem n₁ n₂ m),
    ADMM.IsClosedProperConvex P.f → ADMM.IsClosedProperConvex P.g →
    (∃ x y multiplier, P.IsKKT x y multiplier) → ∀ {β γ : ℝ},
    0 < β → 0 < γ → γ ≤ (377 : ℝ) / 200 → ∀ z : ADMM.Trajectory P β γ,
    Filter.Tendsto z.secondIncrement Filter.atTop (nhds 0))

/- Theorem 2.1.2 (5): under the same hypotheses, the objective values of the
exact ADMM trajectory tend to the constrained optimal value. -/
#check (ADMM.objective_tendsto :
  ∀ {n₁ n₂ m : ℕ} (P : ADMM.Problem n₁ n₂ m),
    ADMM.IsClosedProperConvex P.f → ADMM.IsClosedProperConvex P.g →
    (∃ x y multiplier, P.IsKKT x y multiplier) → ∀ {β γ : ℝ},
    0 < β → 0 < γ → γ ≤ (377 : ℝ) / 200 → ∀ z : ADMM.Trajectory P β γ,
    Filter.Tendsto z.objectiveValue Filter.atTop (nhds P.optimalValue))

/- Theorem 2.1.2 (6): under the same hypotheses, the multiplier sequence of
the exact ADMM trajectory converges to an optimal multiplier. -/
#check (ADMM.multiplier_tendsto_optimal :
  ∀ {n₁ n₂ m : ℕ} (P : ADMM.Problem n₁ n₂ m),
    ADMM.IsClosedProperConvex P.f → ADMM.IsClosedProperConvex P.g →
    (∃ x y multiplier, P.IsKKT x y multiplier) → ∀ {β γ : ℝ},
    0 < β → 0 < γ → γ ≤ (377 : ℝ) / 200 → ∀ z : ADMM.Trajectory P β γ,
    ∃ multiplier, P.IsOptimalMultiplier multiplier ∧
      Filter.Tendsto z.multiplier Filter.atTop (nhds multiplier))

/- Theorem 2.1.2 (7): if both constraint maps are injective, then under the
same hypotheses the complete primal-dual trajectory converges to a KKT triple. -/
#check (ADMM.trajectory_tendsto_kkt_of_injective :
  ∀ {n₁ n₂ m : ℕ} (P : ADMM.Problem n₁ n₂ m),
    ADMM.IsClosedProperConvex P.f → ADMM.IsClosedProperConvex P.g →
    (∃ x y multiplier, P.IsKKT x y multiplier) → ∀ {β γ : ℝ},
    0 < β → 0 < γ → γ ≤ (377 : ℝ) / 200 → ∀ z : ADMM.Trajectory P β γ,
    Function.Injective P.A.mulVec → Function.Injective P.B.mulVec →
    ∃ xBar yBar multiplierBar, P.IsKKT xBar yBar multiplierBar ∧
      Filter.Tendsto (fun k ↦ (z.x k, z.y k, z.multiplier k)) Filter.atTop
        (nhds (xBar, yBar, multiplierBar)))
