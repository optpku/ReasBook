/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

noncomputable section

-- Semantic recall: no upstream mathlib owner surfaced for this rationally scaled trust-region
-- model. In Chapter 6, `ConicTrustRegionSubproblem` is the source-facing owner and
-- `CollinearScalingRewrite` is its bridge/view to the quadratic reformulation. As with the
-- nearby quadratic trust-region owner, the current iterate is ambient data for later translated
-- statements, not primitive step-space data of the subproblem owner.

section

variable {n : ℕ}

/-- Chapter06 Definition 6.2-extra-2 (1): a conic trust-region subproblem on `ℝ^n` records the
step-space model data: the scalar `f = f(x)` at the current approximation `x`, the gradient
`g = ∇ f(x)`, the Hessian approximation `A`, the horizontal vector `a`, the scaling matrix `D`,
and the trust-region radius `Δ` for the model
`ψ(s) = f + (gᵀ s) / (1 - aᵀ s) + (1 / 2) (sᵀ A s) / (1 - aᵀ s)^2`
under the constraint `‖D s‖ ≤ Δ`, with `0 ≤ Δ`. The iterate `x` itself is ambient bridge data
for later translated statements, not primitive data of this owner. -/
structure ConicTrustRegionSubproblem (n : ℕ) where
  fAtCenter : ℝ
  gradient : EuclideanSpace ℝ (Fin n)
  hessianApprox : Matrix (Fin n) (Fin n) ℝ
  horizontalVector : EuclideanSpace ℝ (Fin n)
  scalingMatrix : Matrix (Fin n) (Fin n) ℝ
  radius : ℝ
  radius_nonneg : 0 ≤ radius

local notation "Point" => EuclideanSpace ℝ (Fin n)

namespace ConicTrustRegionSubproblem

/-- The denominator `1 - aᵀ s` in the conic model. -/
def stepDenominator (P : ConicTrustRegionSubproblem n) (s : Point) : ℝ :=
  1 - dotProduct P.horizontalVector s

/-- Expanding `stepDenominator` gives the source denominator `1 - aᵀ s`. -/
theorem stepDenominator_eq (P : ConicTrustRegionSubproblem n) (s : Point) :
    P.stepDenominator s = 1 - dotProduct P.horizontalVector s :=
  rfl

/-- The weighted trust-region norm `‖D s‖`. -/
def weightedNorm (P : ConicTrustRegionSubproblem n) (s : Point) : ℝ :=
  ‖Matrix.toEuclideanLin P.scalingMatrix s‖

/-- Expanding `weightedNorm` gives the source quantity `‖D s‖`. -/
theorem weightedNorm_eq (P : ConicTrustRegionSubproblem n) (s : Point) :
    P.weightedNorm s = ‖Matrix.toEuclideanLin P.scalingMatrix s‖ :=
  rfl

/-- The displayed trust-region constraint set `‖D s‖ ≤ Δ`. -/
def trustRegionSet (P : ConicTrustRegionSubproblem n) : Set Point :=
  { s | P.weightedNorm s ≤ P.radius }

/-- Membership in `trustRegionSet` is exactly the inequality `‖D s‖ ≤ Δ`. -/
theorem mem_trustRegionSet_iff (P : ConicTrustRegionSubproblem n) (s : Point) :
    s ∈ P.trustRegionSet ↔ P.weightedNorm s ≤ P.radius :=
  Iff.rfl

/-- The admissible set of the conic model consists of trust-region steps with positive
denominator `1 - aᵀ s`. -/
def admissibleSet (P : ConicTrustRegionSubproblem n) : Set Point :=
  { s | s ∈ P.trustRegionSet ∧ 0 < P.stepDenominator s }

/-- Membership in `admissibleSet` is the trust-region constraint together with the side
condition `1 - aᵀ s > 0`. -/
theorem mem_admissibleSet_iff (P : ConicTrustRegionSubproblem n) (s : Point) :
    s ∈ P.admissibleSet ↔ s ∈ P.trustRegionSet ∧ 0 < P.stepDenominator s :=
  Iff.rfl

/-- The conic trust-region model
`ψ(s) = f + (gᵀ s) / (1 - aᵀ s) + (1 / 2) (sᵀ A s) / (1 - aᵀ s)^2`,
viewed on the admissible domain `P.admissibleSet`. -/
def objective (P : ConicTrustRegionSubproblem n) (s : P.admissibleSet) : ℝ :=
  P.fAtCenter +
    dotProduct P.gradient s / P.stepDenominator s +
      (((1 : ℝ) / 2) * dotProduct s (Matrix.toEuclideanLin P.hessianApprox s)) /
        (P.stepDenominator s) ^ (2 : ℕ)

/-- Expanding `objective` gives the source conic-model formula on admissible steps. -/
theorem objective_eq (P : ConicTrustRegionSubproblem n) (s : P.admissibleSet) :
    P.objective s =
      P.fAtCenter +
        dotProduct P.gradient s / P.stepDenominator s +
          (((1 : ℝ) / 2) * dotProduct s (Matrix.toEuclideanLin P.hessianApprox s)) /
            (P.stepDenominator s) ^ (2 : ℕ) :=
  rfl

/-- Evaluating `objective` on an admissible point `s` expands to the source conic-model
formula. -/
theorem objective_mk_eq (P : ConicTrustRegionSubproblem n) {s : Point}
    (hs : s ∈ P.admissibleSet) :
    P.objective ⟨s, hs⟩ =
      P.fAtCenter +
        dotProduct P.gradient s / P.stepDenominator s +
          (((1 : ℝ) / 2) * dotProduct s (Matrix.toEuclideanLin P.hessianApprox s)) /
            (P.stepDenominator s) ^ (2 : ℕ) :=
  rfl

/-- Chapter06 Definition 6.2-extra-2 (2): auxiliary data `J`, `h`, and `B` for rewriting a conic
trust-region subproblem `P` in collinear-scaling form. The rewritten step
`s = J w / (1 + hᵀ w)` sends every parameter with `0 < 1 + hᵀ w` into `P.admissibleSet`,
every admissible step of `P` is represented by such a parameter `w`, and the conic objective
agrees with the quadratic objective `f + gᵀ J w + (1 / 2) wᵀ B w`. -/
structure CollinearScalingRewrite (P : ConicTrustRegionSubproblem n) where
  stepMatrix : Matrix (Fin n) (Fin n) ℝ
  horizontalVector : Point
  quadraticMatrix : Matrix (Fin n) (Fin n) ℝ
  admissible_step (w : Point) (hw : 0 < 1 + dotProduct horizontalVector w) :
      (((1 + dotProduct horizontalVector w) : ℝ)⁻¹ •
        Matrix.toEuclideanLin stepMatrix w) ∈ P.admissibleSet
  admissible_step_surjective (s : Point) (hs : s ∈ P.admissibleSet) :
      ∃ w : Point,
        0 < 1 + dotProduct horizontalVector w ∧
          s = (((1 + dotProduct horizontalVector w) : ℝ)⁻¹ •
            Matrix.toEuclideanLin stepMatrix w)
  objective_eq (w : Point) (hw : 0 < 1 + dotProduct horizontalVector w) :
      P.objective
          ⟨(((1 + dotProduct horizontalVector w) : ℝ)⁻¹ •
              Matrix.toEuclideanLin stepMatrix w), admissible_step w hw⟩ =
        P.fAtCenter + dotProduct P.gradient (Matrix.toEuclideanLin stepMatrix w) +
          ((1 : ℝ) / 2) * dotProduct w (quadraticMatrix.mulVec w)

namespace CollinearScalingRewrite

/-- The denominator `1 + hᵀ w` in the rewritten step formula. -/
def stepDenominator {P : ConicTrustRegionSubproblem n} (R : P.CollinearScalingRewrite)
    (w : Point) : ℝ :=
  1 + dotProduct R.horizontalVector w

/-- Expanding `stepDenominator` gives the source denominator `1 + hᵀ w`. -/
theorem stepDenominator_eq {P : ConicTrustRegionSubproblem n} (R : P.CollinearScalingRewrite)
    (w : Point) :
    R.stepDenominator w = 1 + dotProduct R.horizontalVector w :=
  rfl

/-- The rewritten step `s = J w / (1 + hᵀ w)`. -/
def step {P : ConicTrustRegionSubproblem n} (R : P.CollinearScalingRewrite) (w : Point) : Point :=
  (R.stepDenominator w)⁻¹ • Matrix.toEuclideanLin R.stepMatrix w

/-- Expanding `step` gives the source relation `s = J w / (1 + hᵀ w)`. -/
theorem step_eq {P : ConicTrustRegionSubproblem n} (R : P.CollinearScalingRewrite) (w : Point) :
    R.step w = (R.stepDenominator w)⁻¹ • Matrix.toEuclideanLin R.stepMatrix w :=
  rfl

/-- Positive rewritten denominator forces the rewritten step into the original admissible set. -/
theorem step_mem_admissibleSet_of_pos {P : ConicTrustRegionSubproblem n}
    (R : P.CollinearScalingRewrite) (w : Point) (hpos : 0 < R.stepDenominator w) :
    R.step w ∈ P.admissibleSet := by
  simpa [step, stepDenominator] using
    R.admissible_step w (by simpa [stepDenominator] using hpos)

/-- Every admissible step of the conic problem is represented by a rewritten parameter `w`
with `0 < 1 + hᵀ w` and `s = J w / (1 + hᵀ w)`. -/
theorem exists_parameter_of_mem_admissibleSet {P : ConicTrustRegionSubproblem n}
    (R : P.CollinearScalingRewrite) (s : Point) (hs : s ∈ P.admissibleSet) :
    ∃ w : Point, 0 < R.stepDenominator w ∧ s = R.step w := by
  rcases R.admissible_step_surjective s hs with ⟨w, hw, hstep⟩
  exact ⟨w, by simpa [stepDenominator] using hw, by simpa [step, stepDenominator] using hstep⟩

/-- Positive rewritten denominator forces the rewritten step to satisfy the trust-region bound
`‖D s‖ ≤ Δ`. -/
theorem weightedNorm_le_radius_of_pos {P : ConicTrustRegionSubproblem n}
    (R : P.CollinearScalingRewrite) (w : Point) (hpos : 0 < R.stepDenominator w) :
    P.weightedNorm (R.step w) ≤ P.radius := by
  have hmem : R.step w ∈ P.admissibleSet := R.step_mem_admissibleSet_of_pos w hpos
  have htrust : R.step w ∈ P.trustRegionSet := (P.mem_admissibleSet_iff (R.step w)).1 hmem |>.1
  exact (P.mem_trustRegionSet_iff (R.step w)).1 htrust

/-- The rewritten quadratic objective `f + gᵀ J w + (1 / 2) wᵀ B w`. -/
def objective {P : ConicTrustRegionSubproblem n} (R : P.CollinearScalingRewrite) (w : Point) :
    ℝ :=
  P.fAtCenter + dotProduct P.gradient (Matrix.toEuclideanLin R.stepMatrix w) +
    ((1 : ℝ) / 2) * dotProduct w (R.quadraticMatrix.mulVec w)

/-- A collinear-scaling rewrite can be evaluated as its rewritten objective. -/
instance {P : ConicTrustRegionSubproblem n} :
    CoeFun (P.CollinearScalingRewrite) (fun _ ↦ Point → ℝ) where
  coe R := R.objective

/-- Evaluating a collinear-scaling rewrite as a function agrees with `objective`. -/
theorem coeFn_apply {P : ConicTrustRegionSubproblem n} (R : P.CollinearScalingRewrite)
    (w : Point) :
    R w = R.objective w :=
  rfl

/-- The rewritten feasible set consists of the parameters with positive denominator
`1 + hᵀ w > 0`; admissibility of the rewritten step is derived from the bridge certificate
`admissible_step`. -/
def feasibleSet {P : ConicTrustRegionSubproblem n} (R : P.CollinearScalingRewrite) : Set Point :=
  { w | 0 < R.stepDenominator w }

/-- Membership in the rewritten feasible set is exactly the positive denominator condition
`1 + hᵀ w > 0`. -/
theorem mem_feasibleSet_iff {P : ConicTrustRegionSubproblem n} (R : P.CollinearScalingRewrite)
    (w : Point) :
    w ∈ R.feasibleSet ↔ 0 < R.stepDenominator w :=
  Iff.rfl

/-- On points with positive denominator, the rewrite certificate identifies the original conic
objective with the rewritten quadratic objective. -/
theorem objective_eq_of_pos {P : ConicTrustRegionSubproblem n}
    (R : P.CollinearScalingRewrite) (w : Point) (hpos : 0 < R.stepDenominator w) :
    P.objective ⟨R.step w, R.step_mem_admissibleSet_of_pos w hpos⟩ = R.objective w := by
  simpa [objective, step, stepDenominator] using
    R.objective_eq w (by simpa [stepDenominator] using hpos)

/-- On rewritten feasible points, the conic objective equals the rewritten quadratic
objective. -/
theorem objective_eq_of_mem_feasibleSet {P : ConicTrustRegionSubproblem n}
    (R : P.CollinearScalingRewrite) (w : Point) (hw : w ∈ R.feasibleSet) :
    P.objective ⟨R.step w, R.step_mem_admissibleSet_of_pos w hw⟩ = R.objective w :=
  R.objective_eq_of_pos w hw

/-- A step of the original conic subproblem is admissible exactly when it is represented by a
rewritten feasible point `w` with `s = J w / (1 + hᵀ w)`. -/
theorem reformulatesSubproblem {P : ConicTrustRegionSubproblem n}
    (R : P.CollinearScalingRewrite) (s : Point) :
    s ∈ P.admissibleSet ↔ ∃ w : Point, w ∈ R.feasibleSet ∧ s = R.step w := by
  constructor
  · intro hs
    rcases R.exists_parameter_of_mem_admissibleSet s hs with ⟨w, hw, hstep⟩
    exact ⟨w, (R.mem_feasibleSet_iff w).2 hw, hstep⟩
  · rintro ⟨w, hw, hstep⟩
    simpa [hstep] using R.step_mem_admissibleSet_of_pos w ((R.mem_feasibleSet_iff w).1 hw)

end CollinearScalingRewrite
end ConicTrustRegionSubproblem
end
