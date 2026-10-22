/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Remark_1_2_2.Discrepancy
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Definition_7_4.Curve

public section

noncomputable section

namespace Tikhonov

universe u v

variable {m : Type u} {n : Type v}
variable [Fintype m] [DecidableEq m]
variable [Fintype n] [DecidableEq n]

/-- For Definition 7.4-extra-1 (1), the squared residual energy
`R(α) = ‖r_α‖^2` for the Tikhonov L-curve. -/
def lCurveResidualSq (K : Matrix m n ℝ) (d : EuclideanSpace ℝ m) : ℝ → ℝ :=
  fun α ↦ discrepancy K d α ^ 2

/-- The defining formula for `Tikhonov.lCurveResidualSq`. -/
theorem lCurveResidualSq_eq_discrepancy_sq
    (K : Matrix m n ℝ) (d : EuclideanSpace ℝ m) (α : ℝ) :
    lCurveResidualSq K d α = discrepancy K d α ^ 2 := by
  simp [lCurveResidualSq]

/-- For Definition 7.4-extra-1 (2), the logarithmic residual coordinate
`X(α) = log R(α)` for the Tikhonov L-curve. -/
def lCurveLogResidualSq (K : Matrix m n ℝ) (d : EuclideanSpace ℝ m) : ℝ → ℝ :=
  LCurve.logResidualSq (lCurveResidualSq K d)

/-- The defining formula for `Tikhonov.lCurveLogResidualSq`. -/
theorem lCurveLogResidualSq_eq
    (K : Matrix m n ℝ) (d : EuclideanSpace ℝ m) (α : ℝ) :
    lCurveLogResidualSq K d α = Real.log (lCurveResidualSq K d α) := by
  -- Unfold the owner wrapper once to expose the logarithmic residual coordinate.
  simpa [lCurveLogResidualSq] using LCurve.logResidualSq_def (lCurveResidualSq K d) α

/-- Helper for Definition 7.4-extra-1: the logarithmic residual coordinate is
the log of the squared discrepancy. -/
theorem lCurveLogResidualSq_eq_log_discrepancy_sq
    (K : Matrix m n ℝ) (d : EuclideanSpace ℝ m) (α : ℝ) :
    lCurveLogResidualSq K d α = Real.log (discrepancy K d α ^ 2) := by
  -- First rewrite to the residual-energy wrapper, then expose its defining square.
  rw [lCurveLogResidualSq_eq, lCurveResidualSq_eq_discrepancy_sq]

/-- For Definition 7.4-extra-1 (3), the squared solution energy
`S(α) = ‖f_α‖^2` for the Tikhonov L-curve. -/
def lCurveSolutionSq (K : Matrix m n ℝ) (d : EuclideanSpace ℝ m) : ℝ → ℝ :=
  fun α ↦ ‖reconstruction K α d‖ ^ 2

/-- The defining formula for `Tikhonov.lCurveSolutionSq`. -/
theorem lCurveSolutionSq_eq (K : Matrix m n ℝ) (d : EuclideanSpace ℝ m)
    (α : ℝ) :
    lCurveSolutionSq K d α = ‖reconstruction K α d‖ ^ 2 := by
  simp [lCurveSolutionSq]

/-- For Definition 7.4-extra-1 (4), the logarithmic solution coordinate
`Y(α) = log S(α)` for the Tikhonov L-curve. -/
def lCurveLogSolutionSq (K : Matrix m n ℝ) (d : EuclideanSpace ℝ m) : ℝ → ℝ :=
  LCurve.logSolutionSq (lCurveSolutionSq K d)

/-- The defining formula for `Tikhonov.lCurveLogSolutionSq`. -/
theorem lCurveLogSolutionSq_eq
    (K : Matrix m n ℝ) (d : EuclideanSpace ℝ m) (α : ℝ) :
    lCurveLogSolutionSq K d α = Real.log (lCurveSolutionSq K d α) := by
  -- Unfold the owner wrapper once to expose the logarithmic solution coordinate.
  simpa [lCurveLogSolutionSq] using LCurve.logSolutionSq_def (lCurveSolutionSq K d) α

/-- Helper for Definition 7.4-extra-1: the logarithmic solution coordinate is
the log of the squared reconstruction norm. -/
theorem lCurveLogSolutionSq_eq_log_reconstruction_norm_sq
    (K : Matrix m n ℝ) (d : EuclideanSpace ℝ m) (α : ℝ) :
    lCurveLogSolutionSq K d α = Real.log (‖reconstruction K α d‖ ^ 2) := by
  -- First rewrite to the solution-energy wrapper, then expose its defining norm square.
  rw [lCurveLogSolutionSq_eq, lCurveSolutionSq_eq]

/-- For Definition 7.4-extra-1 (5), the Tikhonov L-curve curvature
`κ(α)` given by the logarithmic curvature formula `(7.29)`. -/
def lCurveCurvature (K : Matrix m n ℝ) (d : EuclideanSpace ℝ m) : ℝ → ℝ :=
  LCurve.curvatureOfLogs (lCurveLogResidualSq K d) (lCurveLogSolutionSq K d)

/-- The defining formula for `Tikhonov.lCurveCurvature`. -/
theorem lCurveCurvature_eq (K : Matrix m n ℝ) (d : EuclideanSpace ℝ m)
    (α : ℝ) :
    lCurveCurvature K d α =
      LCurve.curvatureOfLogs (lCurveLogResidualSq K d) (lCurveLogSolutionSq K d) α := by
  simp [lCurveCurvature]

/-- For Definition 7.4-extra-1 (6), a positive parameter is an L-curve parameter
when it maximizes the Tikhonov L-curve curvature. -/
def IsLCurveParameter (K : Matrix m n ℝ) (d : EuclideanSpace ℝ m) (α : ℝ) :
    Prop :=
  LCurve.IsCornerParameter (lCurveCurvature K d) α

/-- def_7_4. Definition 7.4-extra-1. In the Tikhonov setting, the source
L-curve criterion selects a positive parameter exactly when it maximizes the
curvature `κ(α)` of the logarithmic coordinates
`X(α) = log (lCurveResidualSq K d α)` and
`Y(α) = log (lCurveSolutionSq K d α)`, matching `(7.27)`-(7.29). -/
theorem IsLCurveParameter_iff (K : Matrix m n ℝ) (d : EuclideanSpace ℝ m)
    (α : ℝ) :
    IsLCurveParameter K d α ↔
      IsMaxOn (lCurveCurvature K d) (Set.Ioi (0 : ℝ)) α := by
  simpa [IsLCurveParameter] using LCurve.IsCornerParameter_iff (lCurveCurvature K d) α

/-- Helper for Definition 7.4-extra-1: for a positive real `x`, the exponent
`3 / 2` on `x ^ 2` reduces to `x ^ 3`. -/
lemma squareRpow_threeHalves_of_pos {x : ℝ} (hx : 0 < x) :
    Real.rpow (x ^ 2) (3 / 2 : ℝ) = x ^ 3 := by
  have hx_sq_pos : 0 < x ^ 2 := by
    positivity
  -- Split the `3 / 2` exponent into `1 + 1 / 2`, then rewrite the square root.
  calc
    Real.rpow (x ^ 2) (3 / 2 : ℝ)
        = Real.rpow (x ^ 2) (1 : ℝ) * Real.rpow (x ^ 2) (1 / 2 : ℝ) := by
            simpa [show (3 / 2 : ℝ) = 1 + (1 / 2 : ℝ) by norm_num] using
              (Real.rpow_add hx_sq_pos (1 : ℝ) (1 / 2 : ℝ))
    _ = x ^ 2 * x := by
          have h_one : Real.rpow (x ^ 2) (1 : ℝ) = x ^ 2 := by
            simp
          have h_half : Real.rpow (x ^ 2) (1 / 2 : ℝ) = x := by
            simpa [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num] using
              (Real.pow_rpow_inv_natCast (x := x) (n := 2) (le_of_lt hx) (by norm_num))
          rw [h_one, h_half]
    _ = x ^ 3 := by
          ring

/-- Helper for Definition 7.4-extra-1: the second derivative of `Real.log ∘ F`
at a point with `F α > 0` can be written using `F`, `F'`, and `F''`. -/
lemma logSecondDeriv_eq_at {F : ℝ → ℝ} {α : ℝ}
    (hF : ContDiffAt ℝ 2 F α) (hF_pos : 0 < F α) :
    iteratedDeriv 2 (fun β ↦ Real.log (F β)) α =
      iteratedDeriv 2 F α / F α - (deriv F α) ^ 2 / (F α) ^ 2 := by
  have hlog : ContDiffAt ℝ 2 Real.log (F α) := (Real.contDiffAt_log).2 hF_pos.ne'
  -- Apply the second-derivative chain rule to `Real.log ∘ F`.
  change iteratedDeriv 2 (Real.log ∘ F) α =
    iteratedDeriv 2 F α / F α - (deriv F α) ^ 2 / (F α) ^ 2
  calc
    iteratedDeriv 2 (Real.log ∘ F) α
        = iteratedDeriv 2 Real.log (F α) * deriv F α ^ 2 +
            deriv Real.log (F α) * iteratedDeriv 2 F α := by
            simpa using iteratedDeriv_comp_two (g := Real.log) (f := F) hlog hF
    _ = (-(F α ^ 2)⁻¹) * deriv F α ^ 2 + (F α)⁻¹ * iteratedDeriv 2 F α := by
          rw [iteratedDeriv_succ, iteratedDeriv_one, Real.deriv_log]
          simp [deriv_inv]
    _ = iteratedDeriv 2 F α / F α - (deriv F α) ^ 2 / (F α) ^ 2 := by
          field_simp [hF_pos.ne']
          ring

/-- Definition 7.4-extra-1. Under the additional branch condition
`0 < deriv (lCurveSolutionSq K d) α`, the Tikhonov L-curve curvature rewrites
to the positive-orientation energy formula. -/
theorem lCurveCurvature_eq_curvatureFromEnergies_of_solutionDeriv_pos
    (K : Matrix m n ℝ) (d : EuclideanSpace ℝ m) (α : ℝ)
    (hR_smooth : ContDiffAt ℝ 2 (lCurveResidualSq K d) α)
    (hS_smooth : ContDiffAt ℝ 2 (lCurveSolutionSq K d) α)
    (hR_pos : 0 < lCurveResidualSq K d α)
    (hS_pos : 0 < lCurveSolutionSq K d α)
    (hS'_pos : 0 < deriv (lCurveSolutionSq K d) α)
    (hR' :
      deriv (lCurveResidualSq K d) α = -α * deriv (lCurveSolutionSq K d) α)
    (hR'' :
      iteratedDeriv 2 (lCurveResidualSq K d) α =
        -(deriv (lCurveSolutionSq K d) α +
          α * iteratedDeriv 2 (lCurveSolutionSq K d) α)) :
    lCurveCurvature K d α =
      LCurve.curvatureFromEnergies
        (lCurveResidualSq K d) (lCurveSolutionSq K d) α := by
  set R : ℝ → ℝ := lCurveResidualSq K d
  set S : ℝ → ℝ := lCurveSolutionSq K d
  have hR_smooth' : ContDiffAt ℝ 2 R α := by
    simpa [R] using hR_smooth
  have hS_smooth' : ContDiffAt ℝ 2 S α := by
    simpa [S] using hS_smooth
  have hR_pos' : 0 < R α := by
    simpa [R] using hR_pos
  have hS_pos' : 0 < S α := by
    simpa [S] using hS_pos
  have hS'_pos' : 0 < deriv S α := by
    simpa [S] using hS'_pos
  have hR' : deriv R α = -α * deriv S α := by
    simpa [R, S] using hR'
  have hR'' :
      iteratedDeriv 2 R α = -(deriv S α + α * iteratedDeriv 2 S α) := by
    simpa [R, S] using hR''
  have hR_diff : DifferentiableAt ℝ R α := by
    exact hR_smooth'.differentiableAt (by norm_num)
  have hS_diff : DifferentiableAt ℝ S α := by
    exact hS_smooth'.differentiableAt (by norm_num)
  have hX_def : lCurveLogResidualSq K d = fun β ↦ Real.log (R β) := by
    funext β
    simpa [R] using lCurveLogResidualSq_eq K d β
  have hY_def : lCurveLogSolutionSq K d = fun β ↦ Real.log (S β) := by
    funext β
    simpa [S] using lCurveLogSolutionSq_eq K d β
  have hX' : deriv (lCurveLogResidualSq K d) α = deriv R α / R α := by
    -- Expose the residual logarithm and differentiate the log-composition once.
    rw [hX_def]
    simpa using
      (deriv.log (f := R) hR_diff hR_pos'.ne')
  have hY' : deriv (lCurveLogSolutionSq K d) α = deriv S α / S α := by
    -- The solution logarithm is handled by the same one-step log derivative formula.
    rw [hY_def]
    simpa using
      (deriv.log (f := S) hS_diff hS_pos'.ne')
  have hX'' :
      iteratedDeriv 2 (lCurveLogResidualSq K d) α =
        iteratedDeriv 2 R α / R α - (deriv R α) ^ 2 / (R α) ^ 2 := by
    -- Apply the generic second-derivative formula for `Real.log ∘ R`.
    rw [hX_def]
    simpa using
      (logSecondDeriv_eq_at (F := R) (α := α) hR_smooth' hR_pos')
  have hY'' :
      iteratedDeriv 2 (lCurveLogSolutionSq K d) α =
        iteratedDeriv 2 S α / S α - (deriv S α) ^ 2 / (S α) ^ 2 := by
    -- Apply the same second-derivative formula to `Real.log ∘ S`.
    rw [hY_def]
    simpa using
      (logSecondDeriv_eq_at (F := S) (α := α) hS_smooth' hS_pos')
  have hCurvatureNumerator :
      iteratedDeriv 2 (lCurveLogResidualSq K d) α * deriv (lCurveLogSolutionSq K d) α -
          deriv (lCurveLogResidualSq K d) α * iteratedDeriv 2 (lCurveLogSolutionSq K d) α
        =
          -((deriv S α) ^ 2 *
              (R α * S α + α * R α * deriv S α + α ^ 2 * S α * deriv S α)) /
            (R α ^ 2 * S α ^ 2) := by
    -- Substitute the log-derivative identities and cancel the `S''` terms algebraically.
    rw [hX'', hY', hX', hY'', hR', hR'']
    field_simp [hR_pos'.ne', hS_pos'.ne']
    ring
  have hEnergyDenArg_pos : 0 < R α ^ 2 + α ^ 2 * S α ^ 2 := by
    have hR_sq_pos : 0 < R α ^ 2 := by
      positivity
    have hTail_nonneg : 0 ≤ α ^ 2 * S α ^ 2 := by
      positivity
    linarith
  have hCurvatureDenominator :
      Real.rpow
          (deriv (lCurveLogResidualSq K d) α ^ 2 +
            deriv (lCurveLogSolutionSq K d) α ^ 2)
          (3 / 2 : ℝ)
        =
          (deriv S α) ^ 3 *
              Real.rpow (R α ^ 2 + α ^ 2 * S α ^ 2) (3 / 2 : ℝ) /
            (R α ^ 3 * S α ^ 3) := by
    -- Normalize the denominator to the common energy form from `(7.32)`.
    rw [hX', hY', hR']
    calc
      Real.rpow (((-α * deriv S α) / R α) ^ 2 + (deriv S α / S α) ^ 2) (3 / 2 : ℝ)
          =
            Real.rpow
              (((deriv S α) ^ 2 * (R α ^ 2 + α ^ 2 * S α ^ 2)) / (R α ^ 2 * S α ^ 2))
              (3 / 2 : ℝ) := by
                congr 1
                field_simp [hR_pos'.ne', hS_pos'.ne']
                ring
      _ =
            Real.rpow ((deriv S α) ^ 2 * (R α ^ 2 + α ^ 2 * S α ^ 2)) (3 / 2 : ℝ) /
              Real.rpow (R α ^ 2 * S α ^ 2) (3 / 2 : ℝ) := by
                simpa using
                  (Real.div_rpow
                    (x := (deriv S α) ^ 2 * (R α ^ 2 + α ^ 2 * S α ^ 2))
                    (y := R α ^ 2 * S α ^ 2)
                    (by positivity) (by positivity) (3 / 2 : ℝ))
      _ =
            (Real.rpow ((deriv S α) ^ 2) (3 / 2 : ℝ) *
                Real.rpow (R α ^ 2 + α ^ 2 * S α ^ 2) (3 / 2 : ℝ)) /
              (Real.rpow (R α ^ 2) (3 / 2 : ℝ) * Real.rpow (S α ^ 2) (3 / 2 : ℝ)) := by
                rw [show
                    Real.rpow ((deriv S α) ^ 2 * (R α ^ 2 + α ^ 2 * S α ^ 2)) (3 / 2 : ℝ) =
                      Real.rpow ((deriv S α) ^ 2) (3 / 2 : ℝ) *
                        Real.rpow (R α ^ 2 + α ^ 2 * S α ^ 2) (3 / 2 : ℝ) by
                      simpa using
                        (Real.mul_rpow
                          (x := (deriv S α) ^ 2)
                          (y := R α ^ 2 + α ^ 2 * S α ^ 2)
                          (z := (3 / 2 : ℝ))
                          (by positivity) (le_of_lt hEnergyDenArg_pos)),
                  show
                    Real.rpow (R α ^ 2 * S α ^ 2) (3 / 2 : ℝ) =
                      Real.rpow (R α ^ 2) (3 / 2 : ℝ) *
                        Real.rpow (S α ^ 2) (3 / 2 : ℝ) by
                      simpa using
                        (Real.mul_rpow
                          (x := R α ^ 2)
                          (y := S α ^ 2)
                          (z := (3 / 2 : ℝ))
                          (by positivity) (by positivity))]
      _ =
            (deriv S α) ^ 3 * Real.rpow (R α ^ 2 + α ^ 2 * S α ^ 2) (3 / 2 : ℝ) /
              (R α ^ 3 * S α ^ 3) := by
                rw [squareRpow_threeHalves_of_pos hS'_pos',
                  squareRpow_threeHalves_of_pos hR_pos',
                  squareRpow_threeHalves_of_pos hS_pos']
  have hEnergyRpow_pos :
      0 < Real.rpow (R α ^ 2 + α ^ 2 * S α ^ 2) (3 / 2 : ℝ) := by
    exact Real.rpow_pos_of_pos hEnergyDenArg_pos _
  have hEnergyNormalForm :
      lCurveCurvature K d α =
        -(R α * S α * (α * R α + α ^ 2 * S α) + (R α * S α) ^ 2 / deriv S α) /
          Real.rpow (R α ^ 2 + α ^ 2 * S α ^ 2) (3 / 2 : ℝ) := by
    -- Route correction: normalize numerator and denominator first, then clear the scalar factors.
    rw [lCurveCurvature_eq, LCurve.curvatureOfLogs_def, hCurvatureNumerator, hCurvatureDenominator]
    field_simp [hR_pos'.ne', hS_pos'.ne', hS'_pos'.ne', hEnergyRpow_pos.ne']
    ring
  -- Finish by identifying the normalized scalar expression with the owner energy formula.
  calc
    lCurveCurvature K d α
        =
          -(R α * S α * (α * R α + α ^ 2 * S α) + (R α * S α) ^ 2 / deriv S α) /
            Real.rpow (R α ^ 2 + α ^ 2 * S α ^ 2) (3 / 2 : ℝ) :=
      hEnergyNormalForm
    _ = LCurve.curvatureFromEnergies R S α := by
          rw [LCurve.curvatureFromEnergies_def]
    _ = LCurve.curvatureFromEnergies
          (lCurveResidualSq K d) (lCurveSolutionSq K d) α := by
          simp [R, S]

end Tikhonov
