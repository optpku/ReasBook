/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Optimization.DFP.Polar.General.PhysicalRecurrence
public import DFPWolfe.MP20251124.FixedCycle

public section
noncomputable section

open scoped Matrix

namespace DFPWolfe.MP20251124.FixedRecurrence

open DFP.Polar.General

/-- Helper for `eq:fixed-data`: the prescribed common angle in cycle `j`. -/
def tau (j0 j : ℕ) : ℝ := DFP.Polar.General.scale (1 / 2) j0 j

/-- Helper for `eq:fixed-data`: the independent inverse index of the cycle. -/
def inverseIndex (j0 j : ℕ) : ℝ := (((j0 + j : ℕ) : ℝ))⁻¹

/-- Helper for `eq:fixed-feedback`: the fixed manuscript feedback gain. -/
abbrev feedbackGain := FixedCycle.gain

/-- Helper for `eq:fixed-initial`: the prescribed initial polar Hessian matrix. -/
def initialMatrix (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![9 / (4 * t ^ 2), 3 / (2 * t); 3 / (2 * t), 2]

/-- Helper for `eq:fixed-initial`: the prescribed initial inverse Hessian. -/
def initialInverseHessian (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(8 / 9) * t ^ 2, -(2 / 3) * t; -(2 / 3) * t, 1]

/-- Helper for `eq:fixed-feedback`: feedback is evaluated on the even raw
matrix at the beginning of the cycle and is shared by both stages. -/
def multiplier (j0 j : ℕ) (Z : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  Normalized.feedback feedbackGain (inverseIndex j0 j) (tau j0 j ^ 2 * Z 0 0)

/-- Helper for `eq:fixed-update`: the two actual raw polar updates with equal
angles and the same intermediate gradient factor. -/
def cycleMatrix (j0 j : ℕ) (Z : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  DFP.Polar.matrixStep
    (DFP.Polar.matrixStep Z (tau j0 j) 1 (multiplier j0 j Z))
    (tau j0 j) (multiplier j0 j Z) 1

/-- Helper for `eq:fixed-update`: the fixed even matrices are defined by the
raw two-stage recurrence, without a feasibility or trajectory assumption. -/
def evenMatrix (j0 : ℕ) : ℕ → Matrix (Fin 2) (Fin 2) ℝ
  | 0 => initialMatrix (tau j0 0)
  | j + 1 => cycleMatrix j0 j (evenMatrix j0 j)

/-- Helper for `eq:fixed-update`: the intermediate matrix is the first raw stage. -/
def oddMatrix (j0 j : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  DFP.Polar.matrixStep (evenMatrix j0 j) (tau j0 j)
    1 (multiplier j0 j (evenMatrix j0 j))

/-- Helper for `eq:fixed-update`: interleaving the two phases gives all raw matrices. -/
def matrix (j0 : ℕ) : ℕ → Matrix (Fin 2) (Fin 2) ℝ :=
  DFP.twoStepSequence (evenMatrix j0) (oddMatrix j0)

/-- Helper for `eq:fixed-data`: both angles in cycle `j` equal `tau j0 j`. -/
def angleIncrement (j0 : ℕ) : ℕ → ℝ :=
  DFP.twoStepSequence (tau j0) (tau j0)

/-- Helper for `eq:fixed-data`: the unreduced angles start at zero and add
the prescribed fixed increments. -/
def angle (j0 : ℕ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => angle j0 k + angleIncrement j0 k

/-- Helper for `eq:fixed-feedback`: even gradients have factor one and odd
gradients have the exponential feedback of their even boundary. -/
def zeta (j0 : ℕ) : ℕ → ℝ :=
  DFP.twoStepSequence (fun _ ↦ 1) (fun j ↦ multiplier j0 j (evenMatrix j0 j))

/-- Helper for `lem:fixed-cycle`: diagonal normalization of the independently
constructed raw even matrices. -/
def normalizedState (j0 j : ℕ) : ℝ × ℝ × ℝ :=
  Normalized.coordinates (tau j0 j) (evenMatrix j0 j)

/-- Helper for `eq:fixed-feedback`: the public formula for the fixed gain. -/
theorem feedbackGain_formula (γ : ℝ) :
    feedbackGain γ = 3 / (4 * γ * Real.sqrt (1 - 2 / γ)) :=
  FixedCycle.gain_formula γ

/-- Helper for `eq:fixed-initial`: the four entries of the initial matrix. -/
theorem initialMatrix_apply (t : ℝ) :
    initialMatrix t = !![9 / (4 * t ^ 2), 3 / (2 * t); 3 / (2 * t), 2] := by
  rfl

/-- Helper for `eq:fixed-initial`: the four entries of the initial inverse. -/
theorem initialInverseHessian_apply (t : ℝ) :
    initialInverseHessian t = !![(8 / 9) * t ^ 2, -(2 / 3) * t; -(2 / 3) * t, 1] := by
  rfl

/-- Helper for `eq:fixed-initial`: the raw recurrence starts at the fixed matrix. -/
theorem evenMatrix_zero (j0 : ℕ) : evenMatrix j0 0 = initialMatrix (tau j0 0) := by
  rfl

/-- Helper for `eq:fixed-update`: the even boundary advances by the raw cycle. -/
theorem evenMatrix_succ (j0 j : ℕ) :
    evenMatrix j0 (j + 1) = cycleMatrix j0 j (evenMatrix j0 j) := by
  rfl

/-- Helper for `lem:fixed-cycle`: the actual even state uses the current
prescribed diagonal scale, so its first coordinate is the source γ. -/
theorem normalizedState_apply (j0 j : ℕ) :
    normalizedState j0 j =
      (tau j0 j ^ 2 * evenMatrix j0 j 0 0,
        tau j0 j * evenMatrix j0 j 0 1, evenMatrix j0 j 1 1) := by
  exact Normalized.coordinates_apply _ _

/-- Helper for `eq:fixed-update`: the two phases of the interleaved matrices. -/
theorem matrix_phases (j0 j : ℕ) :
    matrix j0 (2 * j) = evenMatrix j0 j ∧
      matrix j0 (2 * j + 1) = oddMatrix j0 j := by
  simp only [matrix, DFP.twoStepSequence_even, DFP.twoStepSequence_odd, and_self]

/-- Helper for `eq:fixed-feedback`: the fixed factors at both cycle phases. -/
theorem zeta_phases (j0 j : ℕ) :
    zeta j0 (2 * j) = 1 ∧
      zeta j0 (2 * j + 1) = multiplier j0 j (evenMatrix j0 j) := by
  simp only [zeta, DFP.twoStepSequence_even, DFP.twoStepSequence_odd, and_self]

/-- Helper for `eq:fixed-data`: the initial angle fixes the initial polar frame. -/
theorem angle_zero (j0 : ℕ) : angle j0 0 = 0 := by
  rfl

/-- Helper for `eq:fixed-data`: consecutive unreduced angles add the prescribed increment. -/
theorem angle_succ (j0 k : ℕ) :
    angle j0 (k + 1) = angle j0 k + angleIncrement j0 k := by
  rfl

/-- Helper for `eq:fixed-data`: the angular scale is exactly `N_j^(-2/3)`. -/
theorem tau_formula (j0 j : ℕ) :
    tau j0 j = (((j0 + j : ℕ) : ℝ)) ^ (-(2 / 3 : ℝ)) := by
  norm_num [tau, DFP.Polar.General.scale_def]

/-- Helper for `eq:fixed-data`: a positive starting index gives positive scales. -/
theorem tau_pos {j0 : ℕ} (hj0 : 0 < j0) (j : ℕ) : 0 < tau j0 j := by
  exact DFP.Polar.General.scale_pos (1 / 2) hj0 j

/-- Helper for `eq:fixed-data`: the change of scale is precisely the factor
used by the normalized map at exponent `1/2`. -/
theorem tau_succ {j0 : ℕ} (hj0 : 0 < j0) (j : ℕ) :
    tau j0 (j + 1) = tau j0 j * Normalized.scaleRatio (1 / 2) (inverseIndex j0 j) := by
  have hbase : 0 < 1 + inverseIndex j0 j := by
    unfold inverseIndex
    positivity
  rw [PhysicalRecurrence.scaleRatio_eq_rpow (1 / 2) hbase]
  exact DFP.Polar.General.scale_succ (1 / 2) hj0 j

/-- Helper for `eq:fixed-feedback`: the raw multiplier has the exact fixed
exponential formula and is strictly positive. -/
theorem multiplier_formula (j0 j : ℕ) (Z : Matrix (Fin 2) (Fin 2) ℝ) :
    multiplier j0 j Z = Real.exp
        (-feedbackGain (tau j0 j ^ 2 * Z 0 0) / (((j0 + j : ℕ) : ℝ))) ∧
      0 < multiplier j0 j Z := by
  constructor
  · simp only [multiplier, Normalized.feedback_def, inverseIndex, div_eq_mul_inv]
  · exact Normalized.feedback_pos _ _ _

/-- Helper for `eq:fixed-initial`: the displayed initial matrices are inverses
at every nonzero angular scale. -/
theorem initialMatrix_inverse {t : ℝ} (ht : t ≠ 0) :
    (initialMatrix t)⁻¹ = initialInverseHessian t := by
  apply Matrix.inv_eq_right_inv
  rw [initialMatrix, initialInverseHessian]
  ext i j
  fin_cases i
  · fin_cases j
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      field_simp
      ring
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      field_simp
      ring
  · fin_cases j
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      field_simp
      ring
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      field_simp
      ring

/-- Helper for `eq:fixed-initial`: the prescribed initial state is symmetric. -/
theorem initialMatrix_isHermitian (t : ℝ) : (initialMatrix t).IsHermitian := by
  rw [initialMatrix, ← RealSymmetric2.matrix_eq]
  exact RealSymmetric2.matrix_isHermitian _ _ _

/-- Helper for `eq:fixed-update`: every recursively constructed even matrix
is symmetric, independently of stage feasibility. -/
theorem evenMatrix_isHermitian (j0 j : ℕ) : (evenMatrix j0 j).IsHermitian := by
  induction j with
  | zero => exact initialMatrix_isHermitian _
  | succ j hj =>
    exact DFP.Polar.matrixStep_isHermitian _ _ _ _
      (DFP.Polar.matrixStep_isHermitian _ _ _ _ hj)

/-- Helper for `eq:fixed-initial`: at a positive starting index, the fixed
initial inverse and the normalized diagonal are exactly as prescribed. -/
theorem initialData {j0 : ℕ} (hj0 : 0 < j0) :
    (evenMatrix j0 0)⁻¹ = initialInverseHessian (tau j0 0) ∧
      normalizedState j0 0 = (9 / 4, 3 / 2, 2) := by
  have ht := (tau_pos hj0 0).ne'
  constructor
  · exact initialMatrix_inverse (tau_pos hj0 0).ne'
  · rw [normalizedState, evenMatrix, initialMatrix, Normalized.coordinates_apply]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    ext
    all_goals field_simp

/-- Helper for `lem:fixed-cycle`: inverse normalization recovers any symmetric
raw matrix at a nonzero scale. -/
theorem recoverCoordinates {t : ℝ} (ht : t ≠ 0)
    (Z : Matrix (Fin 2) (Fin 2) ℝ) (hZ : Z.IsHermitian) :
    PhysicalRecurrence.recoverMatrix t (Normalized.coordinates t Z) = Z := by
  have hsym : Z 1 0 = Z 0 1 := by
    simpa only [star_trivial] using hZ.apply 0 1
  rw [PhysicalRecurrence.recoverMatrix_apply, Normalized.coordinates_apply]
  ext i j
  fin_cases i
  · fin_cases j
    · simp [ht]
    · simp [ht]
  · fin_cases j
    · simp [ht, hsym]
    · simp

/-- Helper for `lem:fixed-cycle`: before changing scale, the normalized
fixed two-stage map recovers the actual raw two-stage update. -/
theorem recoverTwoStep {j0 : ℕ} (hj0 : 0 < j0) (j : ℕ)
    (Z : Matrix (Fin 2) (Fin 2) ℝ) (hZ : Z.IsHermitian) :
    PhysicalRecurrence.recoverMatrix (tau j0 j)
      (Normalized.twoStep (fun _ ↦ 1) (fun _ ↦ 1) feedbackGain
        (tau j0 j) (inverseIndex j0 j) (Normalized.coordinates (tau j0 j) Z)) =
      cycleMatrix j0 j Z := by
  rw [Normalized.twoStep_apply, Normalized.cycleStage_odd, Normalized.cycleStage_even,
    PhysicalRecurrence.recoverMatrix_stage _ (tau_pos hj0 j),
    PhysicalRecurrence.recoverMatrix_stage _ (tau_pos hj0 j),
    recoverCoordinates (tau_pos hj0 j).ne' Z hZ,
    Normalized.stageAngle_def, one_mul]
  simp only [cycleMatrix, multiplier, Normalized.coordinates_apply]

/-- Helper for `lem:fixed-cycle`: changing to the next prescribed scale makes
one actual fixed raw cycle exactly the normalized map with unit angle factors. -/
theorem normalizedCycle {j0 : ℕ} (hj0 : 0 < j0) (j : ℕ)
    (Z : Matrix (Fin 2) (Fin 2) ℝ) (hZ : Z.IsHermitian) :
    Normalized.coordinates (tau j0 (j + 1)) (cycleMatrix j0 j Z) =
      Normalized.map (1 / 2) (fun _ ↦ 1) (fun _ ↦ 1) feedbackGain
        (tau j0 j) (inverseIndex j0 j) (Normalized.coordinates (tau j0 j) Z) := by
  have hrecover : PhysicalRecurrence.recoverMatrix (tau j0 (j + 1))
      (Normalized.map (1 / 2) (fun _ ↦ 1) (fun _ ↦ 1) feedbackGain
        (tau j0 j) (inverseIndex j0 j) (Normalized.coordinates (tau j0 j) Z)) =
      cycleMatrix j0 j Z := by
    rw [Normalized.map_apply, tau_succ hj0 j,
      PhysicalRecurrence.recoverMatrix_rescale _ _ (tau_pos hj0 j).ne']
    exact recoverTwoStep hj0 j Z hZ
  have hcoordinates := congrArg (Normalized.coordinates (tau j0 (j + 1))) hrecover
  rw [PhysicalRecurrence.coordinates_recoverMatrix (tau_pos hj0 (j + 1)).ne'] at hcoordinates
  exact hcoordinates.symm

/-- Helper for `lem:fixed-cycle`: the normalized states of the actual raw
recurrence satisfy the exact manuscript two-parameter map at every cycle. -/
theorem normalizedState_succ {j0 : ℕ} (hj0 : 0 < j0) (j : ℕ) :
    normalizedState j0 (j + 1) =
      Normalized.map (1 / 2) (fun _ ↦ 1) (fun _ ↦ 1) feedbackGain
        (tau j0 j) (inverseIndex j0 j) (normalizedState j0 j) := by
  exact normalizedCycle hj0 j (evenMatrix j0 j) (evenMatrix_isHermitian j0 j)

/-- Helper for `eq:fixed-data`: the two prescribed angle increments are equal. -/
theorem angleIncrement_phases (j0 j : ℕ) :
    angleIncrement j0 (2 * j) = tau j0 j ∧
      angleIncrement j0 (2 * j + 1) = tau j0 j := by
  simp only [angleIncrement, DFP.twoStepSequence_even, DFP.twoStepSequence_odd, and_self]

/-- Helper for `eq:fixed-update`: all consecutive matrices satisfy the raw
polar DFP update with the actual fixed angles and feedback factors. -/
theorem matrix_step (j0 k : ℕ) :
    matrix j0 (k + 1) = DFP.Polar.matrixStep (matrix j0 k) (angleIncrement j0 k)
      (zeta j0 k) (zeta j0 (k + 1)) := by
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · simp only [matrix, angleIncrement, zeta,
      DFP.twoStepSequence_even, DFP.twoStepSequence_odd, oddMatrix]
  · have hindex : 2 * j + 1 + 1 = 2 * (j + 1) := by omega
    rw [hindex]
    simp only [matrix, angleIncrement, zeta,
      DFP.twoStepSequence_even, DFP.twoStepSequence_odd, evenMatrix, cycleMatrix, oddMatrix]

end DFPWolfe.MP20251124.FixedRecurrence
