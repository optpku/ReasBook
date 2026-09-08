module

public import ReasLib.Optimization.DFP.TwoPhaseControls.LineRatio

public section

noncomputable section

open scoped Matrix

namespace TwoPhaseControls

/-- The quadratic form of either two-phase control is uniformly comparable to
the Euclidean sum of squares on the prescribed scale interval. -/
theorem phase_quadraticForm_bounds (ε : ℝ) (i : Fin 2) (v : Fin 2 → ℝ)
    (hε : 0 < ε) (hε_lt : ε < 1 / 4) :
    (1 / 2 : ℝ) * dotProduct v v ≤
        dotProduct v ((phase ε i).matrix *ᵥ v) ∧
      dotProduct v ((phase ε i).matrix *ᵥ v) ≤
        (3 / 2 : ℝ) * dotProduct v v := by
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · rw [phase_zero, first_matrix]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    constructor <;>
      nlinarith [sq_nonneg (v 0 + v 1), sq_nonneg (v 0 - v 1)]
  · rw [phase_one, second_matrix]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    constructor <;>
      nlinarith [sq_nonneg (v 0 + v 1), sq_nonneg (v 0 - v 1)]

/-- The quadratic form of either phase differs from the Euclidean sum of
squares by at most `2 * |ε|` times that sum. -/
theorem abs_dotProduct_sub_phase_quadraticForm_le (ε : ℝ) (i : Fin 2)
    (v : Fin 2 → ℝ) :
    |dotProduct v v - dotProduct v ((phase ε i).matrix *ᵥ v)| ≤
      2 * |ε| * dotProduct v v := by
  have hxy : |v 0 * v 1| ≤ (v 0 ^ 2 + v 1 ^ 2) / 2 := by
    rw [abs_le]
    constructor <;>
      nlinarith [sq_nonneg (v 0 + v 1), sq_nonneg (v 0 - v 1)]
  rw [abs_mul] at hxy
  have hεabs : 0 ≤ |ε| := abs_nonneg ε
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · rw [phase_zero, first_matrix]
    simp only [Matrix.vec2_dotProduct, Fin.isValue, Matrix.cons_mulVec,
      Matrix.cons_dotProduct, one_mul, Matrix.dotProduct_of_isEmpty, add_zero,
      Matrix.empty_mulVec, Matrix.dotProduct_cons, Matrix.vecHead,
      Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, ge_iff_le]
    have hform : v 0 * v 0 + v 1 * v 1 -
        (v 0 * (v 0 + ε * v 1) + v 1 * (ε * v 0 + v 1)) =
        -2 * ε * (v 0 * v 1) := by ring
    rw [hform]
    norm_num [abs_mul]
    have hmul := mul_le_mul_of_nonneg_left hxy hεabs
    nlinarith [hmul, sq_nonneg (v 0), sq_nonneg (v 1)]
  · rw [phase_one, second_matrix]
    simp only [Matrix.vec2_dotProduct, Fin.isValue, neg_mul,
      Matrix.cons_mulVec, Matrix.cons_dotProduct, one_mul,
      Matrix.dotProduct_of_isEmpty, add_zero, Matrix.empty_mulVec,
      Matrix.dotProduct_cons, Matrix.vecHead, Matrix.vecTail,
      Function.comp_apply, Fin.succ_zero_eq_one, ge_iff_le]
    have hform : v 0 * v 0 + v 1 * v 1 -
        (v 0 * (v 0 + -(2 * ε * v 1)) +
          v 1 * (-(2 * ε * v 0) + v 1)) =
        4 * ε * (v 0 * v 1) := by ring
    rw [hform]
    norm_num [abs_mul]
    have hmul := mul_le_mul_of_nonneg_left hxy hεabs
    nlinarith [hmul, sq_nonneg (v 0), sq_nonneg (v 1)]

/-- If the phase curvature is `tau * q`, then `q` is nonnegative and uniformly
comparable to the Euclidean sum of squares. -/
theorem quotient_bounds_of_phase_curvature_eq_tau_mul
    (ε : ℝ) (i : Fin 2) (v : Fin 2 → ℝ) (q : ℝ)
    (hε : 0 < ε) (hε_lt : ε < 1 / 4)
    (hcurvature : dotProduct v ((phase ε i).matrix *ᵥ v) =
      (phase ε i).tau * q) :
    0 ≤ q ∧
      (3 / 4 : ℝ) * dotProduct v v ≤ q ∧
      q ≤ (9 / 2 : ℝ) * dotProduct v v := by
  have hbounds := phase_quadraticForm_bounds ε i v hε hε_lt
  have hsquares : 0 ≤ dotProduct v v := by
    simp only [dotProduct, Fin.sum_univ_two]
    nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  rcases phase_tau_mem ε i with htau | htau
  · rw [hcurvature, htau] at hbounds
    constructor
    · nlinarith
    constructor <;> nlinarith
  · rw [hcurvature, htau] at hbounds
    constructor
    · nlinarith
    constructor <;> nlinarith

/-- If a phase curvature equals `tau * q`, then `q` is uniformly comparable
to the squared Euclidean norm of the coordinate vector. -/
theorem phaseQuotient_mem_Icc_of_curvature
    (ε : ℝ) (i : Fin 2) (v : Fin 2 → ℝ) (q : ℝ)
    (hε : 0 < ε) (hε_lt : ε < 1 / 4)
    (hcurvature : dotProduct v ((phase ε i).matrix *ᵥ v) =
      (phase ε i).tau * q) :
    (3 / 4 : ℝ) * ‖WithLp.toLp 2 v‖ ^ 2 ≤ q ∧
      q ≤ (9 / 2 : ℝ) * ‖WithLp.toLp 2 v‖ ^ 2 := by
  have hq := quotient_bounds_of_phase_curvature_eq_tau_mul
    ε i v q hε hε_lt hcurvature
  have hnorm := EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 v)
  rw [Fin.sum_univ_two] at hnorm
  simp only [dotProduct, Fin.sum_univ_two] at hq
  constructor
  · nlinarith [hq.2.1, hq.2.2, hnorm]
  · nlinarith [hq.2.1, hq.2.2, hnorm]

end TwoPhaseControls
