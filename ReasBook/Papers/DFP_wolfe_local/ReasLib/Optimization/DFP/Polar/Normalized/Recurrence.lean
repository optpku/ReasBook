module

public import ReasLib.Optimization.DFP.Polar.Normalized.Dynamics

public section

noncomputable section

open scoped Matrix

namespace DFP.Polar.Normalized

/-- The analytic next-scale map advances the prescribed cubic scale sequence. -/
theorem nextScale_scale (p : DFP.Polar.Parameters) (j : ℕ)
    (hstart : 0 < p.startIndex) :
    nextScale (p.scale j) = p.scale (j + 1) := by
  -- The prescribed scale is positive, so the positive-branch continuation formula applies.
  have hN : 0 < ((p.startIndex + j : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_pos_left hstart j
  have ht : 0 < p.scale j := by
    rw [DFP.Polar.Parameters.scale_def]
    exact Real.rpow_pos_of_pos hN _
  have hpow :
      (((p.startIndex + j : ℕ) : ℝ) ^ (-(1 : ℝ) / 3)) ^ (3 : ℕ) =
        ((p.startIndex + j : ℕ) : ℝ)⁻¹ := by
    rw [← Real.rpow_mul_natCast hN.le]
    norm_num [Real.rpow_neg_one]
  have hcast :
      ((p.startIndex + (j + 1) : ℕ) : ℝ) =
        ((p.startIndex + j : ℕ) : ℝ) + 1 := by
    norm_num [Nat.cast_add]
    ring
  have hNplus_nonneg :
      0 ≤ ((p.startIndex + j : ℕ) : ℝ) + 1 := by positivity
  have hNplus_pos :
      0 < ((p.startIndex + j : ℕ) : ℝ) + 1 := by linarith
  rw [DFP.Polar.Normalized.nextScale_eq_rpow (p.scale j) ht]
  simp only [DFP.Polar.Parameters.scale_def]
  rw [hcast]
  rw [hpow]
  have hratio :
      1 + ((p.startIndex + j : ℕ) : ℝ)⁻¹ =
        (((p.startIndex + j : ℕ) : ℝ) + 1) /
          ((p.startIndex + j : ℕ) : ℝ) := by
    field_simp [hN.ne']
  rw [hratio, Real.div_rpow (x := ((p.startIndex + j : ℕ) : ℝ) + 1)
    (y := ((p.startIndex + j : ℕ) : ℝ)) hNplus_nonneg hN.le
    (-(1 : ℝ) / 3)]
  field_simp [Real.rpow_pos_of_pos hN _, Real.rpow_pos_of_pos hNplus_pos _]

/-- The prescribed even angle equals `2 * Real.pi / p.scale j`. -/
lemma evenAngleReciprocalScale (p : DFP.Polar.Parameters) (j : ℕ)
    (hstart : 0 < p.startIndex) :
    p.evenAngle j = 2 * Real.pi / p.scale j := by
  -- Rewrite both prescribed quantities to the same positive real power.
  have hN : 0 < ((p.startIndex + j : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_pos_left hstart j
  rw [DFP.Polar.Parameters.evenAngle_def,
    DFP.Polar.Parameters.scale_def]
  have hneg : (-(1 : ℝ) / 3) = -((1 : ℝ) / 3) := by ring
  rw [hneg, Real.rpow_neg hN.le]
  field_simp [Real.rpow_pos_of_pos hN _]

/-- The two analytic stage angles are the prescribed even and odd angular increments. -/
theorem stageAngle_scale (p : DFP.Polar.Parameters) (i : Fin 2) (j : ℕ)
    (hstart : 0 < p.startIndex) :
    stageAngle i (p.scale j) = p.angleIncrement (2 * j + (i : ℕ)) := by
  -- First identify the unweighted analytic increment with consecutive even angles.
  have hN : 0 < ((p.startIndex + j : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_pos_left hstart j
  have ht : 0 < p.scale j := by
    rw [DFP.Polar.Parameters.scale_def]
    exact Real.rpow_pos_of_pos hN _
  have hpow : (p.scale j) ^ (3 : ℕ) =
      ((p.startIndex + j : ℕ) : ℝ)⁻¹ := by
    rw [DFP.Polar.Parameters.scale_def, ← Real.rpow_mul_natCast hN.le]
    norm_num [Real.rpow_neg_one]
  have hcast :
      ((p.startIndex + (j + 1) : ℕ) : ℝ) =
        ((p.startIndex + j : ℕ) : ℝ) + 1 := by
    norm_num [Nat.cast_add]
    ring
  have hratio :
      1 + ((p.startIndex + j : ℕ) : ℝ)⁻¹ =
        (((p.startIndex + j : ℕ) : ℝ) + 1) /
          ((p.startIndex + j : ℕ) : ℝ) := by
    field_simp [hN.ne']
  have hNplus_nonneg :
      0 ≤ ((p.startIndex + j : ℕ) : ℝ) + 1 := by positivity
  have hunweighted :
      (9 * DFP.Polar.baseAngle / p.scale j) *
          ((1 + (p.scale j) ^ (3 : ℕ)) ^ ((1 : ℝ) / 3) - 1) =
        p.evenAngle (j + 1) - p.evenAngle j := by
    rw [hpow, DFP.Polar.Parameters.scale_def, hratio]
    rw [Real.div_rpow (x := ((p.startIndex + j : ℕ) : ℝ) + 1)
      (y := ((p.startIndex + j : ℕ) : ℝ)) hNplus_nonneg hN.le
      ((1 : ℝ) / 3)]
    have hneg : (-(1 : ℝ) / 3) = -((1 : ℝ) / 3) := by ring
    rw [hneg, Real.rpow_neg hN.le]
    have hroot :
        ((p.startIndex + j : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≠ 0 :=
      (Real.rpow_pos_of_pos hN _).ne'
    field_simp [hN.ne', hroot]
    rw [DFP.Polar.Parameters.evenAngle_def,
      DFP.Polar.Parameters.evenAngle_def, hcast,
      DFP.Polar.baseAngle_def]
    ring
  -- The two finite phases simply weight this common increment by 2/3 and 1/3.
  rw [stageAngle_eq_rpow i (p.scale j) ht, hunweighted]
  fin_cases i
  · change stageWeight (0 : Fin 2) *
        (p.evenAngle (j + 1) - p.evenAngle j) =
      p.angleIncrement (2 * j + 0)
    rw [stageWeight_zero, DFP.Polar.Parameters.angleIncrement_def]
    have hzero : 2 * j + 0 = 2 * j := by omega
    rw [hzero]
    rw [DFP.Polar.Parameters.angle_odd, DFP.Polar.Parameters.angle_even,
      DFP.Polar.Parameters.oddAngle_def]
    ring
  · change stageWeight (1 : Fin 2) *
        (p.evenAngle (j + 1) - p.evenAngle j) =
      p.angleIncrement (2 * j + 1)
    rw [stageWeight_one, DFP.Polar.Parameters.angleIncrement_def]
    have hnext : 2 * j + 1 + 1 = 2 * (j + 1) := by omega
    rw [hnext]
    rw [DFP.Polar.Parameters.angle_even, DFP.Polar.Parameters.angle_odd,
      DFP.Polar.Parameters.oddAngle_def]
    ring

/-- Normalized coordinates intertwine one normalized stage with the polar matrix update. -/
lemma stageCoordinates (i : Fin 2) (t : ℝ)
    (Z : Matrix (Fin 2) (Fin 2) ℝ) (ζ ζNext : ℝ)
    (hZ : Z.IsHermitian) (ht : 0 < t) :
    stage i t (coordinates t Z) ζ ζNext =
      coordinates t (DFP.Polar.matrixStep Z (stageAngle i t) ζ ζNext) := by
  -- The matrix transport theorem is projected onto the three coordinate entries.
  have hstage := stageMatrix_eq_scaleMatrix_mul i t Z ζ ζNext hZ ht
  rw [stage_apply]
  simp only [coordinates_apply]
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ ↦ M 0 0) hstage
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ ↦ M 0 1) hstage
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ ↦ M 1 1) hstage
  rw [coordinates_apply] at h00 h01 h11
  apply Prod.ext
  · convert h00 using 1
    simp [scaleMatrix_def, Matrix.mul_apply, Matrix.vecMul,
      Matrix.of_apply, Fin.sum_univ_two, Matrix.cons_dotProduct, Matrix.vecHead,
      Matrix.vecTail, Function.comp_apply, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val', Matrix.cons_val_fin_one,
      Fin.succ_zero_eq_one, Matrix.cons_val_one, zero_mul, add_zero]
    ring
  · apply Prod.ext
    · simpa [scaleMatrix_def, Matrix.mul_apply, Matrix.vecMul, Matrix.mulVec, Matrix.of_apply,
        Fin.sum_univ_two, Matrix.cons_dotProduct_cons, Matrix.dotProduct_cons,
        Matrix.cons_dotProduct, Matrix.vecHead, Matrix.vecTail,
        Function.comp_apply, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
        Matrix.cons_val', Matrix.cons_val_fin_one, Fin.succ_zero_eq_one,
        Matrix.cons_val_one, zero_mul, add_zero] using h01
    · simpa [scaleMatrix_def, Matrix.mul_apply, Matrix.vecMul, Matrix.mulVec, Matrix.of_apply,
        Fin.sum_univ_two, Matrix.cons_dotProduct_cons, Matrix.dotProduct_cons,
        Matrix.cons_dotProduct, Matrix.vecHead, Matrix.vecTail,
        Function.comp_apply, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
        Matrix.cons_val', Matrix.cons_val_fin_one, Fin.succ_zero_eq_one,
        Matrix.cons_val_one, zero_mul, add_zero] using h11

/-- Rescaling normalized coordinates changes their scale from `t` to `nextScale t`. -/
lemma rescaleCoordinates (t : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ)
    (ht : 0 < t) :
    rescale t (coordinates t Z) = coordinates (nextScale t) Z := by
  -- Replace the analytic factor by the squared scale ratio and cancel powers of t.
  rw [rescale_apply]
  simp only [coordinates_apply]
  rw [rescaleFactor_eq_div_sq t ht]
  apply Prod.ext
  · field_simp [ht.ne']
  · apply Prod.ext
    · field_simp [ht.ne']
    · rfl

end DFP.Polar.Normalized

namespace DFP.Polar.Parameters

/-- The normalized even-boundary state in coordinates at the prescribed scale. -/
def normalizedEvenState (p : Parameters) (j : ℕ) : ℝ × ℝ × ℝ :=
  Normalized.coordinates (p.scale j) (p.evenMatrix j)

/-- The coordinate formula defining `normalizedEvenState`. -/
theorem normalizedEvenState_apply (p : Parameters) (j : ℕ) :
    p.normalizedEvenState j =
      (p.scale j ^ 4 * p.evenMatrix j 0 0,
        p.scale j ^ 2 * p.evenMatrix j 0 1,
        p.evenMatrix j 1 1) := by
  -- The boundary state is exactly the coordinate constructor at the prescribed scale.
  unfold normalizedEvenState
  rw [Normalized.coordinates_apply]

/-- The prescribed normalized state reconstructs as the scaled even matrix. -/
theorem normalizedEvenState_matrix (p : Parameters) (j : ℕ) :
    RealSymmetric2.matrix (p.normalizedEvenState j).1
        (p.normalizedEvenState j).2.1 (p.normalizedEvenState j).2.2 =
      Normalized.scaleMatrix (p.scale j) * p.evenMatrix j *
        Normalized.scaleMatrix (p.scale j) := by
  -- The reconstruction identity is the existing Hermitian coordinate interface.
  simpa only [normalizedEvenState] using
    (Normalized.coordinates_eq_scaleMatrix_mul (p.scale j) (p.evenMatrix j)
      (DFP.Polar.Parameters.evenMatrix_isHermitian p j))

/-- Two normalized stages reproduce the prescribed two-stage polar matrix recurrence. -/
lemma twoStepCoordinates (p : Parameters) (j : ℕ)
    (Z : Matrix (Fin 2) (Fin 2) ℝ) (hZ : Z.IsHermitian)
    (hstart : 0 < p.startIndex) :
    Normalized.twoStep p.feedbackRate p.kStar (p.scale j)
        (Normalized.coordinates (p.scale j) Z) =
      Normalized.coordinates (p.scale j) (p.nextEvenMatrix j Z) := by
  -- The normalized feedback at the boundary is exactly the prescribed odd multiplier.
  have hfeedback :
      Normalized.feedback p.feedbackRate p.kStar (p.scale j)
          (Normalized.coordinates (p.scale j) Z) = p.oddMultiplierOf j Z := by
    rw [Normalized.feedback_def, DFP.Polar.Parameters.oddMultiplierOf_def,
      DFP.Polar.Parameters.amplitudeOf_def, Normalized.coordinates_apply]
  have ht : 0 < p.scale j := by
    have hN : 0 < ((p.startIndex + j : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_pos_left hstart j
    rw [DFP.Polar.Parameters.scale_def]
    exact Real.rpow_pos_of_pos hN _
  have hangle0 :
      Normalized.stageAngle 0 (p.scale j) =
        p.oddAngle j - p.evenAngle j := by
    rw [Normalized.stageAngle_scale p 0 j hstart,
      DFP.Polar.Parameters.angleIncrement_def]
    have hzero : 2 * j + ((0 : Fin 2) : ℕ) = 2 * j := by norm_num
    rw [hzero, DFP.Polar.Parameters.angle_odd,
      DFP.Polar.Parameters.angle_even]
  have hangle1 :
      Normalized.stageAngle 1 (p.scale j) =
        p.evenAngle (j + 1) - p.oddAngle j := by
    rw [Normalized.stageAngle_scale p 1 j hstart,
      DFP.Polar.Parameters.angleIncrement_def]
    have hnext : 2 * j + ((1 : Fin 2) : ℕ) + 1 = 2 * (j + 1) := by
      norm_num
      omega
    rw [hnext, DFP.Polar.Parameters.angle_even]
    have hone : ((1 : Fin 2) : ℕ) = 1 := by norm_num
    rw [hone, DFP.Polar.Parameters.angle_odd]
  have hZodd :
      (DFP.Polar.matrixStep Z (p.oddAngle j - p.evenAngle j) 1
        (p.oddMultiplierOf j Z)).IsHermitian := by
    exact DFP.Polar.matrixStep_isHermitian _ _ _ _ hZ
  have hcycle0 :
      Normalized.cycleStage p.feedbackRate p.kStar 0 (p.scale j)
          (Normalized.coordinates (p.scale j) Z)
          (Normalized.coordinates (p.scale j) Z) =
        Normalized.coordinates (p.scale j)
          (DFP.Polar.matrixStep Z (p.oddAngle j - p.evenAngle j) 1
            (p.oddMultiplierOf j Z)) := by
    rw [Normalized.cycleStage_apply, hfeedback]
    simpa [hangle0] using
      (Normalized.stageCoordinates 0 (p.scale j) Z 1
        (p.oddMultiplierOf j Z) hZ ht)
  have hcycle1 :
      Normalized.cycleStage p.feedbackRate p.kStar 1 (p.scale j)
          (Normalized.coordinates (p.scale j) Z)
          (Normalized.coordinates (p.scale j)
            (DFP.Polar.matrixStep Z (p.oddAngle j - p.evenAngle j) 1
              (p.oddMultiplierOf j Z))) =
        Normalized.coordinates (p.scale j)
          (DFP.Polar.matrixStep
            (DFP.Polar.matrixStep Z (p.oddAngle j - p.evenAngle j) 1
              (p.oddMultiplierOf j Z))
            (p.evenAngle (j + 1) - p.oddAngle j)
            (p.oddMultiplierOf j Z) 1) := by
    rw [Normalized.cycleStage_apply, hfeedback]
    simpa [hangle1] using
      (Normalized.stageCoordinates 1 (p.scale j)
        (DFP.Polar.matrixStep Z (p.oddAngle j - p.evenAngle j) 1
          (p.oddMultiplierOf j Z))
        (p.oddMultiplierOf j Z) 1 hZodd ht)
  calc
    Normalized.twoStep p.feedbackRate p.kStar (p.scale j)
          (Normalized.coordinates (p.scale j) Z) =
        Normalized.cycleStage p.feedbackRate p.kStar 1 (p.scale j)
          (Normalized.coordinates (p.scale j) Z)
          (Normalized.cycleStage p.feedbackRate p.kStar 0 (p.scale j)
            (Normalized.coordinates (p.scale j) Z)
            (Normalized.coordinates (p.scale j) Z)) := by
      rw [Normalized.twoStep_def]
    _ = Normalized.cycleStage p.feedbackRate p.kStar 1 (p.scale j)
          (Normalized.coordinates (p.scale j) Z)
          (Normalized.coordinates (p.scale j)
            (DFP.Polar.matrixStep Z (p.oddAngle j - p.evenAngle j) 1
              (p.oddMultiplierOf j Z))) := by rw [hcycle0]
    _ = Normalized.coordinates (p.scale j)
          (DFP.Polar.matrixStep
            (DFP.Polar.matrixStep Z (p.oddAngle j - p.evenAngle j) 1
              (p.oddMultiplierOf j Z))
            (p.evenAngle (j + 1) - p.oddAngle j)
            (p.oddMultiplierOf j Z) 1) := hcycle1
    _ = Normalized.coordinates (p.scale j) (p.nextEvenMatrix j Z) := by
      rw [DFP.Polar.Parameters.nextEvenMatrix_def]

/-- The prescribed normalized even states follow the canonical normalized map. -/
theorem normalizedEvenState_succ (p : Parameters) (j : ℕ)
    (hstart : 0 < p.startIndex) :
    p.normalizedEvenState (j + 1) =
      Normalized.map p.feedbackRate p.kStar (p.scale j) (p.normalizedEvenState j) := by
  -- The successor boundary is obtained by the raw two-stage recurrence first.
  have ht : 0 < p.scale j := by
    have hN : 0 < ((p.startIndex + j : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_pos_left hstart j
    rw [DFP.Polar.Parameters.scale_def]
    exact Real.rpow_pos_of_pos hN _
  have hscale := Normalized.nextScale_scale p j hstart
  have htwo := twoStepCoordinates p j (p.evenMatrix j)
    (DFP.Polar.Parameters.evenMatrix_isHermitian p j) hstart
  have hrescale := Normalized.rescaleCoordinates (p.scale j)
    (p.nextEvenMatrix j (p.evenMatrix j)) ht
  calc
    p.normalizedEvenState (j + 1) =
        Normalized.coordinates (p.scale (j + 1)) (p.evenMatrix (j + 1)) := by
      rfl
    _ = Normalized.coordinates (Normalized.nextScale (p.scale j))
          (p.nextEvenMatrix j (p.evenMatrix j)) := by
      rw [DFP.Polar.Parameters.evenMatrix_succ, hscale]
    _ = Normalized.rescale (p.scale j)
          (Normalized.coordinates (p.scale j)
            (p.nextEvenMatrix j (p.evenMatrix j))) := by
      exact hrescale.symm
    _ = Normalized.rescale (p.scale j)
          (Normalized.twoStep p.feedbackRate p.kStar (p.scale j)
            (Normalized.coordinates (p.scale j) (p.evenMatrix j))) := by
      rw [htwo]
    _ = Normalized.map p.feedbackRate p.kStar (p.scale j)
          (p.normalizedEvenState j) := by
      rw [Normalized.map_def]
      rfl

end DFP.Polar.Parameters
