/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.ConvexFunction
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Optimality
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Trajectory

@[expose] public section

namespace ADMM

namespace Trajectory

/-- The four rank-free convergence conclusions for an exact ADMM trajectory. -/
def Converges {n₁ n₂ m : ℕ} {P : Problem n₁ n₂ m} {β γ : ℝ}
    (z : Trajectory P β γ) : Prop :=
  Filter.Tendsto z.primalResidual Filter.atTop (nhds 0) ∧
    Filter.Tendsto z.secondIncrement Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun k ↦ P.objective (z.x k) (z.y k)) Filter.atTop (nhds P.optimalValue) ∧
    ∃ multiplier, P.IsOptimalMultiplier multiplier ∧
      Filter.Tendsto z.multiplier Filter.atTop (nhds multiplier)

/-- Convergence consists of vanishing residuals, optimal objective values, and
convergence of the multiplier to an optimal multiplier. -/
theorem converges_iff {n₁ n₂ m : ℕ} {P : Problem n₁ n₂ m} {β γ : ℝ}
    {z : Trajectory P β γ} :
    z.Converges ↔
      Filter.Tendsto z.primalResidual Filter.atTop (nhds 0) ∧
        Filter.Tendsto z.secondIncrement Filter.atTop (nhds 0) ∧
        Filter.Tendsto (fun k ↦ P.objective (z.x k) (z.y k)) Filter.atTop (nhds P.optimalValue) ∧
        ∃ multiplier, P.IsOptimalMultiplier multiplier ∧
          Filter.Tendsto z.multiplier Filter.atTop (nhds multiplier) := by
  -- Unfolding `Converges` exposes exactly the displayed conjunction.
  rfl

/-- The entire primal-dual trajectory converges to a KKT triple. -/
def ConvergesToKKT {n₁ n₂ m : ℕ} {P : Problem n₁ n₂ m} {β γ : ℝ}
    (z : Trajectory P β γ) : Prop :=
  ∃ xBar yBar multiplierBar, P.IsKKT xBar yBar multiplierBar ∧
    Filter.Tendsto (fun k ↦ (z.x k, z.y k, z.multiplier k)) Filter.atTop
      (nhds (xBar, yBar, multiplierBar))

/-- Full trajectory convergence is convergence to some certified KKT triple. -/
theorem convergesToKKT_iff {n₁ n₂ m : ℕ} {P : Problem n₁ n₂ m} {β γ : ℝ}
    {z : Trajectory P β γ} :
    z.ConvergesToKKT ↔
      ∃ xBar yBar multiplierBar, P.IsKKT xBar yBar multiplierBar ∧
        Filter.Tendsto (fun k ↦ (z.x k, z.y k, z.multiplier k)) Filter.atTop
          (nhds (xBar, yBar, multiplierBar)) := by
  -- Unfolding `ConvergesToKKT` exposes exactly this certified limit statement.
  rfl

end Trajectory

/-- Uniform convergence at `γ` for every finite-dimensional Euclidean two-block
problem, positive penalty, and exact trajectory satisfying the standard convexity
and KKT assumptions. -/
def UniformConvergenceAt (γ : ℝ) : Prop :=
  ∀ (n₁ n₂ m : ℕ) (P : Problem n₁ n₂ m),
    IsClosedProperConvex P.f → IsClosedProperConvex P.g →
    (∃ x y multiplier, P.IsKKT x y multiplier) →
    ∀ (β : ℝ), 0 < β → ∀ z : Trajectory P β γ,
      z.Converges ∧
        (Function.Injective P.A.mulVec → Function.Injective P.B.mulVec → z.ConvergesToKKT)

/-- Uniform convergence expands to the rank-free conclusions for every exact
trajectory and full convergence whenever both constraint maps are injective. -/
theorem uniformConvergenceAt_iff {γ : ℝ} :
    UniformConvergenceAt γ ↔
      ∀ (n₁ n₂ m : ℕ) (P : Problem n₁ n₂ m),
        IsClosedProperConvex P.f → IsClosedProperConvex P.g →
        (∃ x y multiplier, P.IsKKT x y multiplier) →
        ∀ (β : ℝ), 0 < β → ∀ z : Trajectory P β γ,
          z.Converges ∧
            (Function.Injective P.A.mulVec → Function.Injective P.B.mulVec →
              z.ConvergesToKKT) := by
  -- Unfolding `UniformConvergenceAt` preserves the displayed binders and implications.
  rfl

/-- The endpoint of the initial interval of relaxation factors with uniform convergence. -/
noncomputable def uniformConvergenceEndpoint : ℝ :=
  sSup {c : ℝ | 0 < c ∧ ∀ γ, 0 < γ → γ < c → UniformConvergenceAt γ}

/-- The uniform-convergence endpoint is the supremum of positive valid initial prefixes. -/
theorem uniformConvergenceEndpoint_def :
    uniformConvergenceEndpoint =
      sSup {c : ℝ | 0 < c ∧ ∀ γ, 0 < γ → γ < c → UniformConvergenceAt γ} := by
  -- The endpoint definition reduces directly to this supremum expression.
  rfl

end ADMM
