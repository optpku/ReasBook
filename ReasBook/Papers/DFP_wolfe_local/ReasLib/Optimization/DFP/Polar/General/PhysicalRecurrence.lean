module

public import ReasLib.Optimization.DFP.Polar.General.Recurrence
public import ReasLib.Optimization.DFP.Polar.PhysicalRealization

public section

noncomputable section

open scoped Matrix Topology

namespace DFP.Polar.General.PhysicalRecurrence

/-- Helper for lem:polar-continuation: a normalized coordinate triple is a
canonical symmetric matrix. -/
def stateMatrix (x : ℝ × ℝ × ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  RealSymmetric2.matrix x.1 x.2.1 x.2.2

/-- Helper for lem:polar-continuation: the matrix represented by a normalized state. -/
theorem stateMatrix_def (x : ℝ × ℝ × ℝ) :
    stateMatrix x = RealSymmetric2.matrix x.1 x.2.1 x.2.2 := by
  rfl

/-- Helper for eq:polar-matrix-map: undoing the diagonal normalization gives
the physical local matrix. -/
def recoverMatrix (t : ℝ) (x : ℝ × ℝ × ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Normalized.invScaleMatrix t * stateMatrix x * Normalized.invScaleMatrix t

/-- Helper for eq:polar-matrix-map: the component formula for the recovered matrix. -/
theorem recoverMatrix_apply (t : ℝ) (x : ℝ × ℝ × ℝ) :
    recoverMatrix t x =
      !![t⁻¹ ^ 2 * x.1, t⁻¹ * x.2.1; t⁻¹ * x.2.1, x.2.2] := by
  rw [recoverMatrix, stateMatrix_def, RealSymmetric2.matrix_eq,
    Normalized.invScaleMatrix_def]
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals simp [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

/-- Helper for eq:polar-matrix-map: recovering a state preserves symmetry. -/
theorem recoverMatrix_isHermitian (t : ℝ) (x : ℝ × ℝ × ℝ) :
    (recoverMatrix t x).IsHermitian := by
  rw [recoverMatrix_apply, ← RealSymmetric2.matrix_eq]
  exact RealSymmetric2.matrix_isHermitian _ _ _

/-- Helper for lem:polar-continuation: diagonal scaling followed by its inverse
is the identity at every nonzero scale. -/
theorem scale_mul_invScale {t : ℝ} (ht : t ≠ 0) :
    Normalized.scaleMatrix t * Normalized.invScaleMatrix t = 1 := by
  rw [Normalized.scaleMatrix_def, Normalized.invScaleMatrix_def]
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals simp [Matrix.mul_apply, Fin.sum_univ_two, ht]

/-- Helper for lem:polar-continuation: inverse diagonal scaling also cancels
on the left. -/
theorem invScale_mul_scale {t : ℝ} (ht : t ≠ 0) :
    Normalized.invScaleMatrix t * Normalized.scaleMatrix t = 1 := by
  exact mul_eq_one_comm.mp (scale_mul_invScale ht)

/-- Helper for lem:polar-continuation: the coordinates of a recovered matrix
are the original state. -/
theorem coordinates_recoverMatrix {t : ℝ} (ht : t ≠ 0) (x : ℝ × ℝ × ℝ) :
    Normalized.coordinates t (recoverMatrix t x) = x := by
  rw [recoverMatrix_apply, Normalized.coordinates_apply]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  have hA : t ^ 2 * (t⁻¹ ^ 2 * x.1) = x.1 := by
    field_simp [ht]
  have hC : t * (t⁻¹ * x.2.1) = x.2.1 := by
    rw [← mul_assoc, mul_inv_cancel₀ ht, one_mul]
  rw [hA, hC]

/-- Helper for lem:polar-continuation: reconstructing the coordinates of a
Hermitian matrix gives the same matrix. -/
theorem stateMatrix_coordinates (t : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ)
    (hZ : Z.IsHermitian) :
    stateMatrix (Normalized.coordinates t Z) =
      Normalized.scaleMatrix t * Z * Normalized.scaleMatrix t := by
  rw [stateMatrix_def]
  exact Normalized.coordinates_eq_scaleMatrix_mul t Z hZ

/-- Helper for eq:polar-matrix-map: inverse normalization of the output
coordinate triple recovers the whole canceled stage matrix. -/
theorem stateMatrix_stage (a t : ℝ) (x : ℝ × ℝ × ℝ) (ζ η : ℝ) :
    stateMatrix (Normalized.stage a t x ζ η) = Normalized.stageMatrix a t x ζ η := by
  have hsymm : Normalized.stageMatrix a t x ζ η 1 0 =
      Normalized.stageMatrix a t x ζ η 0 1 := by
    simpa using (Normalized.stageMatrix_isHermitian a t x ζ η).apply 0 1
  rw [stateMatrix_def, RealSymmetric2.matrix_eq, Normalized.stage_apply]
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals simp [hsymm]

/-- Helper for eq:polar-matrix-map: a canceled normalized stage is exactly
the original raw polar matrix update after undoing its scale. -/
theorem recoverMatrix_stage (a : ℝ) {t : ℝ} (ht : 0 < t)
    (x : ℝ × ℝ × ℝ) (ζ η : ℝ) :
    recoverMatrix t (Normalized.stage a t x ζ η) =
      DFP.Polar.matrixStep (recoverMatrix t x) (Normalized.stageAngle a t) ζ η := by
  have hstage := Normalized.stageMatrix_eq_scaleMatrix_mul a t (recoverMatrix t x) ζ η
    (recoverMatrix_isHermitian t x) ht
  rw [coordinates_recoverMatrix ht.ne' x] at hstage
  rw [recoverMatrix, stateMatrix_stage, hstage]
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (Normalized.invScaleMatrix t)
    (Normalized.scaleMatrix t), invScale_mul_scale ht.ne', scale_mul_invScale ht.ne',
    Matrix.one_mul, Matrix.mul_one]

/-- Helper for lem:polar-continuation: recovering raw matrices commutes with
a positive change of diagonal normalization scale. -/
theorem recoverMatrix_rescale (β v : ℝ) {t : ℝ} (ht : t ≠ 0)
    (x : ℝ × ℝ × ℝ) :
    recoverMatrix (t * Normalized.scaleRatio β v) (Normalized.rescale β v x) =
      recoverMatrix t x := by
  have hρ : Normalized.scaleRatio β v ≠ 0 := by
    rw [Normalized.scaleRatio_def]
    exact (Real.exp_pos _).ne'
  rw [recoverMatrix_apply, recoverMatrix_apply, Normalized.rescale_apply]
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  all_goals field_simp [ht, hρ]


/-- Helper for lem:polar-continuation: a positive normalized matrix remains
positive definite after undoing a nonzero diagonal scale. -/
theorem recoverMatrix_posDef {t : ℝ} (ht : t ≠ 0) {x : ℝ × ℝ × ℝ}
    (hx : (stateMatrix x).PosDef) : (recoverMatrix t x).PosDef := by
  have hinjective : Function.Injective (Normalized.invScaleMatrix t).mulVec := by
    intro u v huv
    have h := congrArg (Normalized.scaleMatrix t *ᵥ ·) huv
    simpa only [Matrix.mulVec_mulVec, scale_mul_invScale ht, Matrix.one_mulVec] using h
  have htranspose : (Normalized.invScaleMatrix t)ᴴ = Normalized.invScaleMatrix t := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Normalized.invScaleMatrix_def]
    ext i j
    fin_cases i
    all_goals fin_cases j
    all_goals rfl
  simpa only [recoverMatrix, htranspose] using hx.conjTranspose_mul_mul_same hinjective

/-- Helper for lem:polar-continuation: the recovered off-diagonal entry has
the same positive sign as its normalized entry. -/
theorem recoverMatrix_offDiagonal_pos {t : ℝ} (ht : 0 < t)
    {x : ℝ × ℝ × ℝ} (hx : 0 < x.2.1) : 0 < recoverMatrix t x 0 1 := by
  rw [recoverMatrix_apply]
  simpa using mul_pos (inv_pos.mpr ht) hx

/-- Helper for eq:polar-step-data: the normalized slope is exactly the raw
slope with its scale factor removed. -/
theorem omega_recoverMatrix (t : ℝ) (x : ℝ × ℝ × ℝ) :
    DFP.Polar.omegaOf (recoverMatrix t x) = t * Normalized.slope x := by
  rw [DFP.Polar.omegaOf_def, recoverMatrix_apply, Normalized.slope_def]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

/-- Helper for eq:polar-step-data: the exact raw radius ratio has a canceled
formula in normalized coordinates. -/
theorem radiusRatio_recoverMatrix (a t : ℝ) (x : ℝ × ℝ × ℝ) :
    DFP.Polar.radiusRatioOf (recoverMatrix t x) (Normalized.stageAngle a t) =
      Real.cos (Normalized.stageAngle a t) +
        t * Normalized.slope x * Real.sin (Normalized.stageAngle a t) := by
  rw [DFP.Polar.radiusRatioOf_def, omega_recoverMatrix]

/-- Helper for lem:polar-continuation: normalizing a recovered matrix
preserves its secant scalar exactly. -/
theorem sigma_recoverMatrix (a : ℝ) {t : ℝ} (ht : 0 < t)
    (x : ℝ × ℝ × ℝ) (ζ η : ℝ) :
    DFP.Polar.sigmaOf (recoverMatrix t x) (Normalized.stageAngle a t) ζ η =
      Normalized.stageSigma a t x ζ η := by
  have h := Normalized.stageSigma_eq_sigmaOf a t (recoverMatrix t x) ζ η ht
  rw [coordinates_recoverMatrix ht.ne' x] at h
  exact h.symm

/-- Helper for lem:polar-continuation: on the positive logarithm branch,
the analytic source scale ratio is the exact successor power ratio. -/
theorem scaleRatio_eq_rpow (β : ℝ) {v : ℝ} (hv : 0 < 1 + v) :
    Normalized.scaleRatio β v = (1 + v) ^ (-1 / (1 + β)) := by
  rw [Normalized.scaleRatio_def, Real.rpow_def_of_pos hv]
  congr 1
  ring

end DFP.Polar.General.PhysicalRecurrence

namespace DFP.Polar.General.Parameters

/-- Helper for eq:polar-matrix-map: the concrete even raw matrix uses the
canonical inverse-normalization interface. -/
theorem evenMatrix_eq_recoverMatrix (p : Parameters) (j : ℕ) :
    p.evenMatrix j = PhysicalRecurrence.recoverMatrix (p.scale j) (p.normalizedEvenState j) := by
  rw [evenMatrix_apply, PhysicalRecurrence.recoverMatrix, PhysicalRecurrence.stateMatrix_def]

/-- Helper for eq:polar-matrix-map: the concrete intermediate raw matrix uses
the same inverse-normalization interface and boundary scale. -/
theorem oddMatrix_eq_recoverMatrix (p : Parameters) (j : ℕ) :
    p.oddMatrix j = PhysicalRecurrence.recoverMatrix (p.scale j) (p.normalizedOddState j) := by
  rw [oddMatrix_apply, PhysicalRecurrence.recoverMatrix, PhysicalRecurrence.stateMatrix_def]

/-- Helper for lem:polar-continuation: the actual successor scale equals
the analytic scale-change factor used by the canceled map. -/
theorem scale_succ (p : Parameters) (hstart : 0 < p.startIndex) (j : ℕ) :
    p.scale (j + 1) = p.scale j * Normalized.scaleRatio p.beta (p.inverseIndex j) := by
  have hbase : 0 < 1 + p.inverseIndex j := by
    rw [inverseIndex_def]
    positivity
  rw [PhysicalRecurrence.scaleRatio_eq_rpow p.beta hbase]
  simpa only [scale_def, inverseIndex_def] using General.scale_succ p.beta hstart j

/-- Helper for eq:polar-matrix-map: the first physical matrix update is the
original raw polar DFP recurrence, rather than a new assumed update law. -/
theorem oddMatrix_step (p : Parameters) (hβ : 0 < p.beta)
    (hstart : 0 < p.startIndex) (j : ℕ) :
    p.oddMatrix j = DFP.Polar.matrixStep (p.evenMatrix j)
      (p.angleIncrement (2 * j)) 1 (p.oddMultiplier j) := by
  have ht : 0 < p.scale j := by
    rw [scale_def]
    exact General.scale_pos p.beta hstart j
  rw [oddMatrix_eq_recoverMatrix, normalizedOddState_apply, Normalized.cycleStage_even,
    PhysicalRecurrence.recoverMatrix_stage _ ht, ← evenMatrix_eq_recoverMatrix,
    ← angleIncrement_even p hβ hstart j, ← oddMultiplier_def]

/-- Helper for eq:polar-matrix-map: after the second raw update, changing
the normalized scale leaves the physical matrix unchanged. -/
theorem evenMatrix_step (p : Parameters) (hβ : 0 < p.beta)
    (hstart : 0 < p.startIndex) (j : ℕ) :
    p.evenMatrix (j + 1) = DFP.Polar.matrixStep (p.oddMatrix j)
      (p.angleIncrement (2 * j + 1)) (p.oddMultiplier j) 1 := by
  have ht : 0 < p.scale j := by
    rw [scale_def]
    exact General.scale_pos p.beta hstart j
  rw [evenMatrix_eq_recoverMatrix, normalizedEvenState_succ, normalizedStep_apply,
    Normalized.map_apply, scale_succ p hstart j, PhysicalRecurrence.recoverMatrix_rescale
      p.beta (p.inverseIndex j) ht.ne', Normalized.twoStep_apply, Normalized.cycleStage_odd,
    ← normalizedOddState_apply, PhysicalRecurrence.recoverMatrix_stage _ ht,
    ← oddMatrix_eq_recoverMatrix, ← angleIncrement_odd p hβ hstart j, ← oddMultiplier_def]

/-- Helper for eq:polar-matrix-map: the entire concrete source trajectory
satisfies both original raw DFP stages at every index. -/
theorem matrix_step (p : Parameters) (hβ : 0 < p.beta) (hstart : 0 < p.startIndex) (k : ℕ) :
    p.matrix (k + 1) = DFP.Polar.matrixStep (p.matrix k) (p.angleIncrement k)
      (p.zeta k) (p.zeta (k + 1)) := by
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · rw [matrix_odd, matrix_even, zeta_even, zeta_odd]
    exact oddMatrix_step p hβ hstart j
  · have hindex : 2 * j + 1 + 1 = 2 * (j + 1) := by omega
    rw [hindex, matrix_even, matrix_odd, zeta_odd, zeta_even]
    exact evenMatrix_step p hβ hstart j


/-- Helper for lem:polar-continuation: normalized positive definiteness at
both phases implies positive definiteness of every concrete raw matrix. -/
theorem matrix_posDef_of_normalized (p : Parameters) (hstart : 0 < p.startIndex)
    (hEven : ∀ j, (PhysicalRecurrence.stateMatrix (p.normalizedEvenState j)).PosDef)
    (hOdd : ∀ j, (PhysicalRecurrence.stateMatrix (p.normalizedOddState j)).PosDef) (k : ℕ) :
    (p.matrix k).PosDef := by
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · rw [matrix_even, evenMatrix_eq_recoverMatrix]
    apply PhysicalRecurrence.recoverMatrix_posDef
    · rw [scale_def]
      exact (General.scale_pos p.beta hstart j).ne'
    · exact hEven j
  · rw [matrix_odd, oddMatrix_eq_recoverMatrix]
    apply PhysicalRecurrence.recoverMatrix_posDef
    · rw [scale_def]
      exact (General.scale_pos p.beta hstart j).ne'
    · exact hOdd j

/-- Helper for lem:polar-continuation: positive normalized off-diagonal entries
at both phases imply the raw off-diagonal sign at every index. -/
theorem matrix_offDiagonal_pos_of_normalized (p : Parameters) (hstart : 0 < p.startIndex)
    (hEven : ∀ j, 0 < (p.normalizedEvenState j).2.1)
    (hOdd : ∀ j, 0 < (p.normalizedOddState j).2.1) (k : ℕ) : 0 < p.matrix k 0 1 := by
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · rw [matrix_even, evenMatrix_eq_recoverMatrix]
    apply PhysicalRecurrence.recoverMatrix_offDiagonal_pos
    · rw [scale_def]
      exact General.scale_pos p.beta hstart j
    · exact hEven j
  · rw [matrix_odd, oddMatrix_eq_recoverMatrix]
    apply PhysicalRecurrence.recoverMatrix_offDiagonal_pos
    · rw [scale_def]
      exact General.scale_pos p.beta hstart j
    · exact hOdd j

/-- Helper for lem:polar-continuation: the raw even secant scalar is the
canceled stage scalar used in the continuation estimates. -/
theorem sigma_even_eq_normalized (p : Parameters) (hβ : 0 < p.beta)
    (hstart : 0 < p.startIndex) (j : ℕ) :
    DFP.Polar.sigmaOf (p.matrix (2 * j)) (p.angleIncrement (2 * j))
        (p.zeta (2 * j)) (p.zeta (2 * j + 1)) =
      Normalized.stageSigma (p.evenAngleFactor (p.inverseIndex j)) (p.scale j)
        (p.normalizedEvenState j) 1 (p.oddMultiplier j) := by
  have ht : 0 < p.scale j := by
    rw [scale_def]
    exact General.scale_pos p.beta hstart j
  rw [matrix_even, zeta_even, zeta_odd, evenMatrix_eq_recoverMatrix,
    angleIncrement_even p hβ hstart j, PhysicalRecurrence.sigma_recoverMatrix _ ht]

/-- Helper for lem:polar-continuation: the raw odd secant scalar retains the
shared feedback evaluated at the initial even state. -/
theorem sigma_odd_eq_normalized (p : Parameters) (hβ : 0 < p.beta)
    (hstart : 0 < p.startIndex) (j : ℕ) :
    DFP.Polar.sigmaOf (p.matrix (2 * j + 1)) (p.angleIncrement (2 * j + 1))
        (p.zeta (2 * j + 1)) (p.zeta (2 * j + 1 + 1)) =
      Normalized.stageSigma (p.oddAngleFactor (p.inverseIndex j)) (p.scale j)
        (p.normalizedOddState j) (p.oddMultiplier j) 1 := by
  have ht : 0 < p.scale j := by
    rw [scale_def]
    exact General.scale_pos p.beta hstart j
  have hindex : 2 * j + 1 + 1 = 2 * (j + 1) := by omega
  rw [hindex, matrix_odd, zeta_odd, zeta_even, oddMatrix_eq_recoverMatrix,
    angleIncrement_odd p hβ hstart j, PhysicalRecurrence.sigma_recoverMatrix _ ht]

/-- Helper for eq:polar-W-expansion: the concrete even radius factor has its
exact canceled trigonometric formula. -/
theorem radiusRatio_even_eq_normalized (p : Parameters) (hβ : 0 < p.beta)
    (hstart : 0 < p.startIndex) (j : ℕ) :
    p.radiusRatio (2 * j) =
      Real.cos (Normalized.stageAngle (p.evenAngleFactor (p.inverseIndex j)) (p.scale j)) +
        p.scale j * Normalized.slope (p.normalizedEvenState j) *
          Real.sin (Normalized.stageAngle (p.evenAngleFactor (p.inverseIndex j)) (p.scale j)) := by
  rw [radiusRatio_def, matrix_even, evenMatrix_eq_recoverMatrix,
    angleIncrement_even p hβ hstart j, PhysicalRecurrence.radiusRatio_recoverMatrix]

/-- Helper for eq:polar-W-expansion: the concrete odd radius factor has its
exact canceled formula using the intermediate normalized state. -/
theorem radiusRatio_odd_eq_normalized (p : Parameters) (hβ : 0 < p.beta)
    (hstart : 0 < p.startIndex) (j : ℕ) :
    p.radiusRatio (2 * j + 1) =
      Real.cos (Normalized.stageAngle (p.oddAngleFactor (p.inverseIndex j)) (p.scale j)) +
        p.scale j * Normalized.slope (p.normalizedOddState j) *
          Real.sin (Normalized.stageAngle (p.oddAngleFactor (p.inverseIndex j)) (p.scale j)) := by
  rw [radiusRatio_def, matrix_odd, oddMatrix_eq_recoverMatrix,
    angleIncrement_odd p hβ hstart j, PhysicalRecurrence.radiusRatio_recoverMatrix]

end DFP.Polar.General.Parameters
