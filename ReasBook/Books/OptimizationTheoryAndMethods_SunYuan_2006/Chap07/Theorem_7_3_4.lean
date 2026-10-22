/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Theorem_6_1_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap07.Algorithm_7_3_9
import OptimizationTheoryAndMethods_SunYuan_2006.Chap07.Definition_7_3_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap07.Theorem_7_3_4.Multiplier
import Mathlib
import Mathlib.Order.Filter.Extr

open Matrix

noncomputable section

-- Domain sampling for this refine pass:
-- * `trustRegionLevenbergMarquardtModel` in `Algorithm_7_3_9` already owns the
--   least-squares trust-region model, while the feasible set is the canonical closed ball
--   `Metric.closedBall 0 Δ`.
-- * `leastSquaresTrustRegionSubproblem` packages the same primitive data `J`, `r`, and `Δ`
--   inside the Chapter 6 trust-region owner.
-- Source/core/bridge triage:
-- * source-facing: the KKT multiplier characterization of the least-squares trust-region
--   subproblem.
-- * core/canonical: `TrustRegionSubproblem.isSolution_iff_exists_multiplier`.
-- This file therefore follows the source note literally by transporting the Chapter 7 statement
-- to the Chapter 6 owner and applying Theorem 6.1.2 directly.

section

variable {m n : ℕ}

-- Local declaration justification (source-local notation): this item fixes the Chapter 7
-- least-squares trust-region ambient spaces `EuclideanSpace ℝ (Fin n)` and
-- `EuclideanSpace ℝ (Fin m)`, and these short textbook names are only used to keep the local
-- KKT formulas readable without exporting item-specific aliases.
local notation "StepVector" => EuclideanSpace ℝ (Fin n)
-- Local declaration justification (source-local notation): this file uses the residual-space
-- alias only for the source-local LM formulas, so keeping it local avoids adding item-specific
-- ambient-space vocabulary to the public API.
local notation "ResidualVector" => EuclideanSpace ℝ (Fin m)
-- Local declaration justification (source-local notation): this abbreviation names the fixed
-- Hessian matrix ambient space used only by the source-local trust-region calculations.
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ
-- Local declaration justification (source-local notation): this alias is only the Jacobian
-- matrix ambient type for this theorem's local Chapter 7 formulas, not a reusable owner.
local notation "JacobianMatrix" => Matrix (Fin m) (Fin n) ℝ

/-- Helper for Chapter07 Theorem 7.3.4: the packaged Chapter 6 subproblem keeps the source
gradient `Jᵀ r` as its gradient field. -/
lemma least_squares_trust_region_subproblem_gradient
    (J : JacobianMatrix) (r : ResidualVector) (Δ : ℝ) (hΔ : 0 < Δ) :
    (leastSquaresTrustRegionSubproblem J r Δ hΔ).gradient = Jᵀ.mulVec r := by
  -- Expand the Euclidean matrix action so the packaged gradient becomes the usual matrix product.
  ext i
  simp [leastSquaresTrustRegionSubproblem, trustRegionLevenbergMarquardtGradient,
    Matrix.toEuclideanLin, Matrix.toLpLin_apply]

/-- Helper for Chapter07 Theorem 7.3.4: the owner residual vector
`Matrix.toEuclideanLin J s + r` is the Euclidean spelling of the coordinate residual
`J.mulVec s + r`. -/
lemma least_squares_residual_eq_coordinate
    (J : JacobianMatrix) (r : ResidualVector) (s : StepVector) :
    Matrix.toEuclideanLin J s + r = WithLp.toLp 2 (J.mulVec s.ofLp + r.ofLp) := by
  -- Rewrite the Euclidean matrix action into coordinates and combine the sum once.
  calc
    Matrix.toEuclideanLin J s + r
        = WithLp.toLp 2 (J.mulVec s.ofLp) + r := by
            rw [Matrix.toEuclideanLin_apply]
    _ = WithLp.toLp 2 (J.mulVec s.ofLp) + WithLp.toLp 2 r.ofLp := by
            simpa using
              congrArg
                (fun x : ResidualVector ↦ WithLp.toLp 2 (J.mulVec s.ofLp) + x)
                (WithLp.ofLp_toLp 2 r).symm
    _ = WithLp.toLp 2 (J.mulVec s.ofLp + r.ofLp) := by
            rw [← WithLp.toLp_add]

/-- Helper for Chapter07 Theorem 7.3.4: the packaged Chapter 6 owner residual already equals the
raw Chapter 7 surface residual `J.mulVec s + r`. -/
lemma least_squares_owner_residual_eq_surface_residual
    (J : JacobianMatrix) (r : ResidualVector) (s : StepVector) :
    Matrix.toEuclideanLin J s + r = J.mulVec s + r := by
  -- Compare both residual spellings coordinatewise after expanding the Euclidean matrix action.
  ext i
  simp [Matrix.toEuclideanLin_apply]

/-- Helper for Chapter07 Theorem 7.3.4: the Chapter 7 surface residual `J.mulVec s + r` has the
same Euclidean coordinate spelling `WithLp.toLp 2 (J.mulVec s.ofLp + r.ofLp)`. -/
lemma least_squares_surface_residual_eq_coordinate
    (J : JacobianMatrix) (r : ResidualVector) (s : StepVector) :
    WithLp.toLp 2 (J.mulVec s.ofLp) + r = WithLp.toLp 2 (J.mulVec s.ofLp + r.ofLp) := by
  -- Rewrite the surface residual so both summands use the same `WithLp.toLp` spelling.
  calc
    WithLp.toLp 2 (J.mulVec s.ofLp) + r
        = WithLp.toLp 2 (J.mulVec s.ofLp) + WithLp.toLp 2 r.ofLp := by
      simpa using
        congrArg
          (fun x : ResidualVector ↦ WithLp.toLp 2 (J.mulVec s.ofLp) + x)
          (WithLp.ofLp_toLp 2 r).symm
    _ = WithLp.toLp 2 (J.mulVec s.ofLp + r.ofLp) := by
      rw [← WithLp.toLp_add]

/-- Helper for Chapter07 Theorem 7.3.4: the Chapter 7 surface model is definitionally half the
squared norm of the raw residual `J.mulVec s + r`. -/
lemma trust_region_levenberg_marquardt_model_eq_surface_residual
    (J : JacobianMatrix) (r : ResidualVector) (s : StepVector) :
    trustRegionLevenbergMarquardtModel J r s =
      ((1 : ℝ) / 2) * ‖J.mulVec s + r‖ ^ (2 : ℕ) := by
  -- Unfold the model once so the Chapter 7 surface keeps its raw residual spelling.
  simpa [trustRegionLevenbergMarquardtModel]

/-- Helper for Chapter07 Theorem 7.3.4: the packaged Chapter 6 quadratic-model expansion
matches half the squared norm of the owner residual `Matrix.toEuclideanLin J s + r`. -/
lemma least_squares_model_expansion_eq_half_residual_norm_sq
    (J : JacobianMatrix) (r : ResidualVector) (s : StepVector) :
    ((1 : ℝ) / 2) * ‖r‖ ^ (2 : ℕ) + dotProduct (Jᵀ.mulVec r) s +
        ((1 : ℝ) / 2) * dotProduct s ((Jᵀ * J).mulVec s) =
      ((1 : ℝ) / 2) * ‖Matrix.toEuclideanLin J s + r‖ ^ (2 : ℕ) := by
  have hcross : dotProduct (Jᵀ.mulVec r) s = dotProduct (Matrix.toEuclideanLin J s) r := by
    -- Convert the transpose term into the residual-side dot product.
    calc
      dotProduct (Jᵀ.mulVec r) s = dotProduct s (Jᵀ.mulVec r) := by
        rw [dotProduct_comm]
      _ = dotProduct (J.mulVec s.ofLp) r.ofLp := by
        rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
      _ = dotProduct (Matrix.toEuclideanLin J s) r := by
        rw [Matrix.toEuclideanLin_apply]
  have hquad : dotProduct s ((Jᵀ * J).mulVec s) = ‖Matrix.toEuclideanLin J s‖ ^ (2 : ℕ) := by
    -- Collapse the Gram quadratic term to the squared norm of `J s`.
    calc
      dotProduct s ((Jᵀ * J).mulVec s)
          = dotProduct s (Jᵀ.mulVec (J.mulVec s.ofLp)) := by
              rw [Matrix.mulVec_mulVec]
      _ = dotProduct (J.mulVec s.ofLp) (J.mulVec s.ofLp) := by
            rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
      _ = ‖Matrix.toEuclideanLin J s‖ ^ (2 : ℕ) := by
            simpa [pow_two, dotProduct, Matrix.toEuclideanLin_apply] using
              (EuclideanSpace.real_norm_sq_eq (Matrix.toEuclideanLin J s)).symm
  -- Expand the residual norm once, then rewrite the cross and quadratic terms.
  rw [norm_add_sq_real, hquad]
  have hcross' : inner ℝ (Matrix.toEuclideanLin J s) r = dotProduct (Jᵀ.mulVec r) s := by
    simpa [PiLp.inner_apply, dotProduct, mul_comm] using hcross.symm
  rw [hcross']
  ring

/-- Helper for Chapter07 Theorem 7.3.4: evaluating the packaged Chapter 6 subproblem reproduces
the source Euclidean least-squares objective `s ↦ (1 / 2) * ‖J s + r‖₂²`. -/
lemma least_squares_trust_region_subproblem_apply
    (J : JacobianMatrix) (r : ResidualVector) (Δ : ℝ) (hΔ : 0 < Δ) (s : StepVector) :
    (leastSquaresTrustRegionSubproblem J r Δ hΔ : TrustRegionSubproblem n) s =
      ((1 : ℝ) / 2) * ‖Matrix.toEuclideanLin J s + r‖ ^ (2 : ℕ) := by
  -- Unfold the owner once and package its algebraic expansion into the residual squared norm.
  rw [TrustRegionSubproblem.quadraticModel_eq]
  simpa [leastSquaresTrustRegionSubproblem, trustRegionLevenbergMarquardtGradient,
    Matrix.toEuclideanLin_apply] using
    least_squares_model_expansion_eq_half_residual_norm_sq J r s

/-- Helper for Chapter07 Theorem 7.3.4: the packaged Chapter 6 quadratic-model field agrees
pointwise with the source Euclidean least-squares objective. -/
lemma least_squares_trust_region_subproblem_quadraticModel_eq
    (J : JacobianMatrix) (r : ResidualVector) (Δ : ℝ) (hΔ : 0 < Δ) (s : StepVector) :
    (leastSquaresTrustRegionSubproblem J r Δ hΔ).quadraticModel s =
      ((1 : ℝ) / 2) * ‖Matrix.toEuclideanLin J s + r‖ ^ (2 : ℕ) := by
  -- Switch from the owner field to evaluation of the owner as a function.
  simpa [TrustRegionSubproblem.coeFn_apply] using
    least_squares_trust_region_subproblem_apply J r Δ hΔ s

/-- Helper for Chapter07 Theorem 7.3.4: unpacking the packaged Chapter 6 solution predicate gives
the expected Chapter 7 feasible-ball statement `sk ∈ closedBall 0 Δ ∧ IsMinOn ...`. -/
lemma least_squares_trust_region_subproblem_isSolution_iff
    (J : JacobianMatrix) (r : ResidualVector) (Δ : ℝ) (hΔ : 0 < Δ) (sk : StepVector) :
    (leastSquaresTrustRegionSubproblem J r Δ hΔ).IsSolution sk ↔
      sk ∈ Metric.closedBall 0 Δ ∧
        IsMinOn
          (fun s : StepVector ↦ ((1 : ℝ) / 2) * ‖Matrix.toEuclideanLin J s + r‖ ^ (2 : ℕ))
          (Metric.closedBall 0 Δ) sk := by
  -- Rewrite the owner solution predicate into feasibility plus a pointwise minimizer statement.
  rw [TrustRegionSubproblem.isSolution_iff_mem_feasibleSet_and_isMinOn,
    TrustRegionSubproblem.feasibleSet, isMinOn_iff, isMinOn_iff]
  constructor
  · rintro ⟨hsk, hmin⟩
    refine ⟨by simpa [leastSquaresTrustRegionSubproblem] using hsk, ?_⟩
    intro s hs
    -- Transport each comparison value through the model-identification lemma.
    simpa [least_squares_trust_region_subproblem_quadraticModel_eq J r Δ hΔ sk,
      least_squares_trust_region_subproblem_quadraticModel_eq J r Δ hΔ s] using hmin s hs
  · rintro ⟨hsk, hmin⟩
    refine ⟨by simpa [leastSquaresTrustRegionSubproblem] using hsk, ?_⟩
    intro s hs
    -- The reverse direction uses the same pointwise identification of the quadratic model.
    simpa [least_squares_trust_region_subproblem_quadraticModel_eq J r Δ hΔ sk,
      least_squares_trust_region_subproblem_quadraticModel_eq J r Δ hΔ s] using hmin s hs

/-- Helper for Chapter07 Theorem 7.3.4: when `μ ≥ 0`, the shifted Hessian
`Jᵀ J + μ I` of the packaged least-squares trust-region subproblem is positive semidefinite. -/
lemma least_squares_shifted_hessian_pos_semidef
    (J : JacobianMatrix) (r : ResidualVector) (Δ : ℝ) (hΔ : 0 < Δ) {μ : ℝ} (hμ : 0 ≤ μ) :
    ((leastSquaresTrustRegionSubproblem J r Δ hΔ).shiftedHessian μ).PosSemidef := by
  -- Combine the Gram-matrix positivity with the positive semidefiniteness of `μ I`.
  have hgram : (Jᵀ * J : MatrixN).PosSemidef := by
    simpa using Matrix.posSemidef_conjTranspose_mul_self J
  have hone : (1 : MatrixN).PosSemidef := Matrix.PosSemidef.one
  have hidentity : (μ • (1 : MatrixN)).PosSemidef :=
    hone.smul hμ
  simpa [TrustRegionSubproblem.shiftedHessian, leastSquaresTrustRegionSubproblem, add_assoc]
    using hgram.add hidentity

/-- Helper for Chapter07 Theorem 7.3.4: the Chapter 7 multiplier packaging is equivalent to the
Chapter 6 KKT conjunction for the packaged least-squares trust-region subproblem. -/
lemma least_squares_multiplier_iff
    (J : JacobianMatrix) (r : ResidualVector) (Δ : ℝ) (hΔ : 0 < Δ) (sk : StepVector) :
    (∃ μ : ℝ, IsLevenbergMarquardtTrustRegionMultiplier J r Δ sk μ) ↔
      ∃ μ : ℝ,
        0 ≤ μ ∧
        ((leastSquaresTrustRegionSubproblem J r Δ hΔ).shiftedHessian μ).mulVec sk =
          -(leastSquaresTrustRegionSubproblem J r Δ hΔ).gradient ∧
        ‖sk‖ ≤ (leastSquaresTrustRegionSubproblem J r Δ hΔ).radius ∧
        μ * ((leastSquaresTrustRegionSubproblem J r Δ hΔ).radius - ‖sk‖) = 0 ∧
        ((leastSquaresTrustRegionSubproblem J r Δ hΔ).shiftedHessian μ).PosSemidef := by
  constructor
  · rintro ⟨μ, hμ⟩
    -- The source multiplier data already provides all Chapter 6 KKT clauses except PSD.
    have hstationarity :
        ((leastSquaresTrustRegionSubproblem J r Δ hΔ).shiftedHessian μ).mulVec sk =
          -(leastSquaresTrustRegionSubproblem J r Δ hΔ).gradient := by
      simpa [TrustRegionSubproblem.shiftedHessian, leastSquaresTrustRegionSubproblem,
        trustRegionLevenbergMarquardtGradient, Matrix.toEuclideanLin, Matrix.toLpLin_apply]
        using hμ.stationarity
    have hfeasible : ‖sk‖ ≤ (leastSquaresTrustRegionSubproblem J r Δ hΔ).radius := by
      simpa [leastSquaresTrustRegionSubproblem] using hμ.feasible
    have hcomplementary :
        μ * ((leastSquaresTrustRegionSubproblem J r Δ hΔ).radius - ‖sk‖) = 0 := by
      simpa [leastSquaresTrustRegionSubproblem] using hμ.complementarySlackness
    have hpsd :
        ((leastSquaresTrustRegionSubproblem J r Δ hΔ).shiftedHessian μ).PosSemidef :=
      least_squares_shifted_hessian_pos_semidef J r Δ hΔ hμ.nonneg
    exact ⟨μ, hμ.nonneg, hstationarity, hfeasible, hcomplementary, hpsd⟩
  · rintro ⟨μ, hμ_nonneg, hstationarity, hfeasible, hcomplementary, _hpsd⟩
    -- Conversely, the Chapter 6 KKT data specializes to the Chapter 7 multiplier class.
    have hstationarity' :
        solvesLevenbergMarquardtNormalEquation J (Jᵀ.mulVec r) μ sk := by
      simpa [TrustRegionSubproblem.shiftedHessian, leastSquaresTrustRegionSubproblem,
        trustRegionLevenbergMarquardtGradient, Matrix.toEuclideanLin, Matrix.toLpLin_apply]
        using hstationarity
    have hfeasible' : ‖sk‖ ≤ Δ := by
      simpa [leastSquaresTrustRegionSubproblem] using hfeasible
    have hcomplementary' : μ * (Δ - ‖sk‖) = 0 := by
      simpa [leastSquaresTrustRegionSubproblem] using hcomplementary
    exact
      ⟨μ,
        { nonneg := hμ_nonneg
          stationarity := hstationarity'
          complementarySlackness := hcomplementary'
          feasible := hfeasible' }⟩

/-- Helper for Chapter07 Theorem 7.3.4: the source-faithful least-squares trust-region statement
with explicit feasibility is exactly the Chapter 7 multiplier characterization. -/
lemma least_squares_solution_iff_exists_multiplier
    (J : JacobianMatrix) (r : ResidualVector) (Δ : ℝ) (hΔ : 0 < Δ) (sk : StepVector) :
    (sk ∈ Metric.closedBall 0 Δ ∧
        IsMinOn
          (fun s : StepVector ↦ ((1 : ℝ) / 2) * ‖Matrix.toEuclideanLin J s + r‖ ^ (2 : ℕ))
          (Metric.closedBall 0 Δ) sk) ↔
      ∃ μ : ℝ, IsLevenbergMarquardtTrustRegionMultiplier J r Δ sk μ := by
  -- Transport the Chapter 7 surface statement to the packaged Chapter 6 owner.
  calc
    (sk ∈ Metric.closedBall 0 Δ ∧
        IsMinOn
          (fun s : StepVector ↦ ((1 : ℝ) / 2) * ‖Matrix.toEuclideanLin J s + r‖ ^ (2 : ℕ))
          (Metric.closedBall 0 Δ) sk) ↔
        (leastSquaresTrustRegionSubproblem J r Δ hΔ).IsSolution sk := by
          simpa using
            (least_squares_trust_region_subproblem_isSolution_iff J r Δ hΔ sk).symm
    _ ↔ ∃ μ : ℝ,
        0 ≤ μ ∧
        ((leastSquaresTrustRegionSubproblem J r Δ hΔ).shiftedHessian μ).mulVec sk =
          -(leastSquaresTrustRegionSubproblem J r Δ hΔ).gradient ∧
        ‖sk‖ ≤ (leastSquaresTrustRegionSubproblem J r Δ hΔ).radius ∧
        μ * ((leastSquaresTrustRegionSubproblem J r Δ hΔ).radius - ‖sk‖) = 0 ∧
        ((leastSquaresTrustRegionSubproblem J r Δ hΔ).shiftedHessian μ).PosSemidef := by
          rw [TrustRegionSubproblem.isSolution_iff_exists_multiplier]
    _ ↔ ∃ μ : ℝ, IsLevenbergMarquardtTrustRegionMultiplier J r Δ sk μ := by
          simpa using (least_squares_multiplier_iff J r Δ hΔ sk).symm

/-- Chapter07 Theorem 7.3.4: the vector `sk` solves the constrained least-squares problem
`min (1 / 2) * ‖J s + r‖₂²` subject to `‖s‖ ≤ Δ`, formalized with the Euclidean residual
`Matrix.toEuclideanLin J s + r`. Then `sk` is feasible and minimizes that model on
`Metric.closedBall 0 Δ` if and only if there exists `μ ≥ 0` such that
`(Jᵀ * J + μ • 1).mulVec sk = -(Jᵀ.mulVec r)`, `μ * (Δ - ‖sk‖) = 0`, and `‖sk‖ ≤ Δ`. -/
theorem levenbergMarquardtTrustRegionSolution_iff_exists_multiplier
    (J : JacobianMatrix) (r : ResidualVector) (Δ : ℝ) (hΔ : 0 < Δ) (sk : StepVector) :
    (sk ∈ Metric.closedBall 0 Δ ∧
      IsMinOn
        (fun s : StepVector ↦ ((1 : ℝ) / 2) * ‖Matrix.toEuclideanLin J s + r‖ ^ (2 : ℕ))
        (Metric.closedBall 0 Δ) sk) ↔
      ∃ μ : ℝ, IsLevenbergMarquardtTrustRegionMultiplier J r Δ sk μ := by
  -- This is exactly the source-facing transport lemma established above.
  simpa using least_squares_solution_iff_exists_multiplier J r Δ hΔ sk

end
