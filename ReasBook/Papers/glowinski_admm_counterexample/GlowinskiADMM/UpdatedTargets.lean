/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.GlowinskiADMM.lemma_3_2_reduced
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.RefinedConstants
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UniformConvergence
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Convergence
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Symbol
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.CoercivityInterpolation
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.MomentRegrouping

@[expose] public section

/-!
# Full statements of the updated manuscript

These definitions freeze the full statements of the updated manuscript.
A definition of a proposition is not a theorem asserting that proposition.
Their proofs are supplied by the implementation modules imported by
`GlowinskiADMM.UpdatedPaper`; `GlowinskiADMM.UpdatedResults` exports the
unconditional convergence and endpoint theorems.
-/

namespace ADMM.UpdatedTargets

open Filter FiniteMemory UnitCircle

open scoped ComplexOrder

/-- All conclusions of the updated Theorem 2.1, including separate image limits. -/
def TrajectoryConclusions {n₁ n₂ m : ℕ} {P : Problem n₁ n₂ m} {β γ : ℝ}
    (z : Trajectory P β γ) : Prop :=
  (∃ qBar, Tendsto (fun k ↦ P.A.mulVec (z.x k)) atTop (nhds qBar)) ∧
  (∃ vBar, Tendsto (fun k ↦ P.B.mulVec (z.y k)) atTop (nhds vBar)) ∧
  z.Converges ∧
  (Function.Injective P.A.mulVec → Function.Injective P.B.mulVec → z.ConvergesToKKT)

/-- Updated Theorem 2.1. The old proof covers only `γ ≤ 377/200`. -/
def MainConvergenceClaim : Prop :=
  ∀ {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m),
    IsClosedProperConvex P.f → IsClosedProperConvex P.g →
    (∃ x y multiplier, P.IsKKT x y multiplier) → ∀ {β γ : ℝ},
    0 < β → 0 < γ → γ ≤ RefinedEndpoint.lower →
    ∀ z : Trajectory P β γ, TrajectoryConclusions z

/-- The retained proof supplies every updated conclusion on the old parameter range.
`UpdatedAssembly` combines this range with the unit-circle certificate to prove
the full range in `UpdatedResults`. -/
theorem retained_trajectory_conclusions {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (hf : IsClosedProperConvex P.f) (hg : IsClosedProperConvex P.g)
    (hKKT : ∃ x y multiplier, P.IsKKT x y multiplier) {β γ : ℝ}
    (hβ : 0 < β) (hγ : 0 < γ) (hOld : γ ≤ (377 : ℝ) / 200)
    (z : Trajectory P β γ) : TrajectoryConclusions z := by
  refine ⟨leftImage_tendsto P hf hg hKKT hβ hγ hOld z,
    rightImage_tendsto P hf hg hKKT hβ hγ hOld z, ?_, ?_⟩
  · exact ⟨primalResidual_tendsto_zero P hf hg hKKT hβ hγ hOld z,
      secondIncrement_tendsto_zero P hf hg hKKT hβ hγ hOld z,
      objective_tendsto P hf hg hKKT hβ hγ hOld z,
      multiplier_tendsto_optimal P hf hg hKKT hβ hγ hOld z⟩
  · intro hA hB
    exact trajectory_tendsto_kkt_of_injective P hf hg hKKT hβ hγ hOld z hA hB

/-- The complete reduced conclusion, retaining objective limits at domain boundaries. -/
def ReducedConclusions {m : ℕ} {f g : (Fin m → ℝ) → EReal} {γ : ℝ}
    (z : ReducedTrajectory f g γ) : Prop :=
  ∃ qBar vBar uBar, ReducedIsKKT f g qBar vBar uBar ∧
    Tendsto (fun k ↦ (z.q k, z.v k, z.u k)) atTop (nhds (qBar, vBar, uBar)) ∧
    Tendsto (fun k ↦ z.q k + z.v k) atTop (nhds 0) ∧
    Tendsto (fun k ↦ f (z.q k) - f qBar +
      ((dotProduct uBar (z.q k - qBar) : ℝ) : EReal)) atTop (nhds 0) ∧
    Tendsto (fun k ↦ g (z.v k) - g vBar +
      ((dotProduct uBar (z.v k - vBar) : ℝ) : EReal)) atTop (nhds 0)

/-- Equation (C.2), with a strictly positive uniform coercivity margin. -/
def CircleCoercive {ℓ : ℕ} (c : LagWeights ℓ) (γ : ℝ) : Prop :=
  ∃ κ : ℝ, 0 < κ ∧ HasCoercivityBound c γ κ

/-- The new analytic implication in Lemma C.1, for arbitrary initial states. -/
def UnitCircleConvergenceClaim : Prop :=
  ∀ (ℓ : ℕ) (c : LagWeights ℓ) {γ : ℝ},
    1 ≤ ℓ → 1 < γ → γ < 2 → BalancedMoments c → CircleCoercive c γ →
    ∀ {m : ℕ} (f g : (Fin m → ℝ) → EReal),
    IsClosedProperConvex f → IsClosedProperConvex g →
    (∃ q v u, ReducedIsKKT f g q v u) →
    ∀ z : ReducedTrajectory f g γ, ReducedConclusions z

/-- The concrete lower-certificate statement, including strict right continuation.
The fixed coefficients and margin are the exact pinned paper data. -/
def LowerCircleCertificateClaim : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ RefinedEndpoint.lower + δ < 2 ∧
    ∀ γ : ℝ, (377 : ℝ) / 200 ≤ γ → γ ≤ RefinedEndpoint.lower + δ →
      HasCoercivityBound paperWeights γ (RefinedEndpoint.Data.kappa : ℝ)

/-- The strict lower bound requires continuation beyond `L`, not just convergence at `L`. -/
def RefinedLowerBoundClaim : Prop := RefinedEndpoint.lower < uniformConvergenceEndpoint

/-- The strict upper bound supplied by the 1024-phase counterexample. -/
def RefinedUpperBoundClaim : Prop := uniformConvergenceEndpoint < RefinedEndpoint.upper

/-- Updated Corollary 2.3, including its exact enclosure width. -/
def EndpointBoundsClaim : Prop :=
  RefinedLowerBoundClaim ∧ RefinedUpperBoundClaim ∧
    RefinedEndpoint.upper - RefinedEndpoint.lower = (2171721 : ℝ) / 12500000000000

/-- Combine proofs of the two strict inequalities with the exact enclosure width. -/
theorem endpointBounds_of_two_bounds
    (hLower : RefinedLowerBoundClaim) (hUpper : RefinedUpperBoundClaim) :
    EndpointBoundsClaim :=
  ⟨hLower, hUpper, RefinedEndpoint.width⟩

end ADMM.UpdatedTargets
