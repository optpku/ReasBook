module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import ReasLib.LinearAlgebra.Matrix.RealSymmetric2

public section

noncomputable section

open scoped Matrix

/-- A planar DFP control consists of its secant matrix and step ratio. -/
structure PlanarDFPControl where
  matrix : Matrix (Fin 2) (Fin 2) ℝ
  tau : ℝ

namespace TwoPhaseControls

/-- The canonical-state radius determined by the common control scale. -/
def radius (ε : ℝ) : ℝ :=
  ε ^ 2

/-- The radius is the square of the common control scale. -/
theorem radius_def (ε : ℝ) : radius ε = ε ^ 2 := by
  -- Unfolding the radius leaves the defining square on both sides.
  rfl

/-- The first planar control, with off-diagonal entry `ε` and ratio `2 / 3`. -/
def first (ε : ℝ) : PlanarDFPControl where
  matrix := RealSymmetric2.matrix 1 ε 1
  tau := 2 / 3

/-- The first control has matrix `!![1, ε; ε, 1]`. -/
theorem first_matrix (ε : ℝ) :
    (first ε).matrix = !![1, ε; ε, 1] := by
  -- The public symmetric-matrix equation exposes the stored entries.
  simpa only [first] using RealSymmetric2.matrix_eq 1 ε 1

/-- The first control has ratio `2 / 3`. -/
theorem first_tau (ε : ℝ) : (first ε).tau = 2 / 3 := by
  -- The ratio is the second field of the first control.
  rfl

/-- The second planar control, with off-diagonal entry `-2 * ε` and ratio `1 / 3`. -/
def second (ε : ℝ) : PlanarDFPControl where
  matrix := RealSymmetric2.matrix 1 (-2 * ε) 1
  tau := 1 / 3

/-- The second control has matrix `!![1, -2 * ε; -2 * ε, 1]`. -/
theorem second_matrix (ε : ℝ) :
    (second ε).matrix = !![1, -2 * ε; -2 * ε, 1] := by
  -- The public symmetric-matrix equation exposes the stored entries.
  simpa only [second] using RealSymmetric2.matrix_eq 1 (-2 * ε) 1

/-- The second control has ratio `1 / 3`. -/
theorem second_tau (ε : ℝ) : (second ε).tau = 1 / 3 := by
  -- The ratio is the second field of the second control.
  rfl

/-- The ordered two-phase family, whose two legs share the same scale `ε`. -/
def phase (ε : ℝ) : Fin 2 → PlanarDFPControl :=
  ![first ε, second ε]

/-- Phase zero is the first control. -/
theorem phase_zero (ε : ℝ) : phase ε 0 = first ε := by
  -- Evaluation at the first finite index selects the first control.
  rfl

/-- Phase one is the second control. -/
theorem phase_one (ε : ℝ) : phase ε 1 = second ε := by
  -- Evaluation at the second finite index selects the second control.
  rfl

/-- Every matrix in the two-phase family is Hermitian. -/
theorem matrix_isHermitian (ε : ℝ) (i : Fin 2) :
    ((phase ε i).matrix).IsHermitian := by
  -- Each phase reduces to an explicit real symmetric matrix.
  fin_cases i
  · exact RealSymmetric2.matrix_isHermitian 1 ε 1
  · exact RealSymmetric2.matrix_isHermitian 1 (-2 * ε) 1

/-- Under the prescribed scale restriction, every control matrix is positive definite. -/
theorem matrix_posDef (ε ε₀ : ℝ) (i : Fin 2) (hε : 0 < ε)
    (hε₀ : ε ≤ ε₀) (hε₀_lt : ε₀ < 1 / 4) :
    Matrix.PosDef (phase ε i).matrix := by
  -- The scale restriction makes both diagonal-dominance coefficients positive.
  have hε_lt : ε < 1 / 4 := lt_of_le_of_lt hε₀ hε₀_lt
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · rw [phase_zero]
    refine Matrix.PosDef.of_dotProduct_mulVec_pos
      (RealSymmetric2.matrix_isHermitian 1 ε 1) ?_
    intro x hx
    -- A nonzero planar vector has a strictly positive sum of coordinate squares.
    have hcoords : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra h
      apply hx
      funext k
      fin_cases k
      · exact not_ne_iff.mp (not_or.mp h).1
      · exact not_ne_iff.mp (not_or.mp h).2
    have hsquares : 0 < x 0 ^ 2 + x 1 ^ 2 := by
      rcases hcoords with hx₀ | hx₁
      · nlinarith [sq_pos_of_ne_zero hx₀]
      · nlinarith [sq_pos_of_ne_zero hx₁]
    -- The quadratic form is `(1 - ε) S + ε (x₀ + x₁)²`.
    rw [first_matrix]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    nlinarith [sq_nonneg (x 0 + x 1)]
  · rw [phase_one]
    refine Matrix.PosDef.of_dotProduct_mulVec_pos
      (RealSymmetric2.matrix_isHermitian 1 (-2 * ε) 1) ?_
    intro x hx
    -- A nonzero planar vector has a strictly positive sum of coordinate squares.
    have hcoords : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra h
      apply hx
      funext k
      fin_cases k
      · exact not_ne_iff.mp (not_or.mp h).1
      · exact not_ne_iff.mp (not_or.mp h).2
    have hsquares : 0 < x 0 ^ 2 + x 1 ^ 2 := by
      rcases hcoords with hx₀ | hx₁
      · nlinarith [sq_pos_of_ne_zero hx₀]
      · nlinarith [sq_pos_of_ne_zero hx₁]
    -- The quadratic form is `(1 - 2ε) S + 2ε (x₀ - x₁)²`.
    rw [second_matrix]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    nlinarith [sq_nonneg (x 0 - x 1)]

/-- Every step ratio in the ordered two-phase family is positive. -/
theorem tau_pos (ε : ℝ) (i : Fin 2) : 0 < (phase ε i).tau := by
  -- Both stored rational ratios are strictly positive.
  fin_cases i
  · norm_num [phase, first]
  · norm_num [phase, second]

/-- Under the prescribed scale restriction, every Hermitian eigenvalue of every
control matrix belongs to `[1 / 2, 3 / 2]`. -/
theorem spectrum_mem (ε ε₀ : ℝ) (i j : Fin 2) (hε : 0 < ε)
    (hε₀ : ε ≤ ε₀) (hε₀_lt : ε₀ < 1 / 4) :
    (matrix_isHermitian ε i).eigenvalues j ∈ Set.Icc (1 / 2) (3 / 2) := by
  -- Express the eigenvalue as the Rayleigh quotient of its unit eigenvector.
  let v : EuclideanSpace ℝ (Fin 2) :=
    (matrix_isHermitian ε i).eigenvectorBasis j
  have hvnorm : ‖v‖ = 1 := by
    exact (matrix_isHermitian ε i).eigenvectorBasis.norm_eq_one j
  have hsquares := EuclideanSpace.real_norm_sq_eq v
  rw [hvnorm, one_pow, Fin.sum_univ_two] at hsquares
  have heigen : (matrix_isHermitian ε i).eigenvalues j =
      dotProduct v ((phase ε i).matrix *ᵥ v) := by
    simpa [v] using (matrix_isHermitian ε i).eigenvalues_eq j
  rw [heigen]
  have hε_lt : ε < 1 / 4 := lt_of_le_of_lt hε₀ hε₀_lt
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · rw [phase_zero]
    -- The first Rayleigh quotient is `v₀² + 2εv₀v₁ + v₁²`.
    have hquadratic : dotProduct v ((first ε).matrix *ᵥ v) =
        v 0 ^ 2 + 2 * ε * v 0 * v 1 + v 1 ^ 2 := by
      rw [first_matrix]
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    rw [hquadratic]
    constructor
    · nlinarith [sq_nonneg (v 0 + v 1), sq_nonneg (v 0 - v 1)]
    · nlinarith [sq_nonneg (v 0 + v 1), sq_nonneg (v 0 - v 1)]
  · rw [phase_one]
    -- The second Rayleigh quotient is `v₀² - 4εv₀v₁ + v₁²`.
    have hquadratic : dotProduct v ((second ε).matrix *ᵥ v) =
        v 0 ^ 2 - 4 * ε * v 0 * v 1 + v 1 ^ 2 := by
      rw [second_matrix]
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    rw [hquadratic]
    constructor
    · nlinarith [sq_nonneg (v 0 + v 1), sq_nonneg (v 0 - v 1)]
    · nlinarith [sq_nonneg (v 0 + v 1), sq_nonneg (v 0 - v 1)]

end TwoPhaseControls
