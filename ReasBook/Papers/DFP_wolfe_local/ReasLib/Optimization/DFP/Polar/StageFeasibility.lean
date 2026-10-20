module

public import ReasLib.Optimization.DFP.Polar.FastRemainder
public import ReasLib.Optimization.DFP.Polar.Normalized.Recurrence
public import ReasLib.Optimization.DFP.Polar.ScaleTails
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

public section

noncomputable section

open Filter
open scoped Matrix Topology

namespace DFP.Polar.StageFeasibility

open Normalized

/-- Helper for lem:polar-continuation: the symmetric matrix represented by
the original normalized coordinates `(A,C,V)`. -/
def stateMatrix (x : ℝ × ℝ × ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  RealSymmetric2.matrix x.1 x.2.1 x.2.2

/-- Helper for lem:polar-continuation: the coordinate reconstruction formula. -/
theorem stateMatrix_def (x : ℝ × ℝ × ℝ) :
    stateMatrix x = RealSymmetric2.matrix x.1 x.2.1 x.2.2 := by
  rfl

/-- Helper for lem:polar-continuation: the normalized determinant is `AV-C²`. -/
theorem stateMatrix_det (x : ℝ × ℝ × ℝ) :
    (stateMatrix x).det = x.1 * x.2.2 - x.2.1 ^ 2 := by
  rw [stateMatrix_def, RealSymmetric2.matrix_eq, Matrix.det_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  ring

/-- Helper for lem:polar-continuation: the natural positive two-by-two
criterion gives positive definiteness of a normalized state. -/
theorem stateMatrix_posDef (x : ℝ × ℝ × ℝ) (hA : 0 < x.1)
    (hdet : 0 < x.1 * x.2.2 - x.2.1 ^ 2) : (stateMatrix x).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · exact RealSymmetric2.matrix_isHermitian _ _ _
  · intro u hu
    have hform : star u ⬝ᵥ (stateMatrix x *ᵥ u) =
        x.1 * (u 0 + x.2.1 / x.1 * u 1) ^ 2 +
          (x.1 * x.2.2 - x.2.1 ^ 2) / x.1 * (u 1) ^ 2 := by
      simp only [stateMatrix_def, RealSymmetric2.matrix_eq, Matrix.mulVec,
        dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.star_apply, star_trivial]
      field_simp [hA.ne']
      ring
    rw [hform]
    by_cases hu1 : u 1 = 0
    · have hu0 : u 0 ≠ 0 := by
        intro hzero
        apply hu
        ext i
        fin_cases i
        · exact hzero
        · exact hu1
      simpa [hu1] using mul_pos hA (sq_pos_of_ne_zero hu0)
    · exact add_pos_of_nonneg_of_pos (mul_nonneg hA.le (sq_nonneg _))
        (mul_pos (div_pos hdet hA) (sq_pos_of_ne_zero hu1))

/-- Helper for lem:polar-continuation: positivity of the state matrix and
off-diagonal entry is controlled by the three strict scalar inequalities. -/
def regularState (x : ℝ × ℝ × ℝ) : Prop :=
  0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.1 * x.2.2 - x.2.1 ^ 2

/-- Helper for lem:polar-continuation: the scalar regularity criterion. -/
theorem regularState_def (x : ℝ × ℝ × ℝ) :
    regularState x ↔ 0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.1 * x.2.2 - x.2.1 ^ 2 := by
  rfl

/-- Helper for lem:polar-continuation: regular states represent positive
definite matrices with positive off-diagonal entries. -/
theorem regularState_posDef (x : ℝ × ℝ × ℝ) (hx : regularState x) :
    (stateMatrix x).PosDef ∧ 0 < x.2.1 := by
  exact ⟨stateMatrix_posDef x hx.1 hx.2.2, hx.2.1⟩

/-- Helper for lem:polar-continuation: the original even cycle is a regular
state throughout the selected normalization interval. -/
theorem regularState_evenState (A : ℝ) (hA : A ∈ TwoCycle.normalizationSet) :
    regularState (TwoCycle.evenState A) := by
  have hpos := TwoCycle.evenState_mapsTo_positive hA
  have hfirst : 0 < A := by
    simpa only [Set.mem_Ioi, TwoCycle.evenState_firstDiagonal] using hpos.1
  have hdet : 0 < (TwoCycle.evenState A).1 * (TwoCycle.evenState A).2.2 -
      (TwoCycle.evenState A).2.1 ^ 2 := by
    rw [← stateMatrix_det, stateMatrix_def, TwoCycle.evenState_det A hA]
    exact hfirst
  exact ⟨Set.mem_Ioi.mp hpos.1, Set.mem_Ioi.mp hpos.2.1, hdet⟩

/-- Helper for lem:polar-continuation: the original odd cycle is a regular
state throughout the same selected normalization interval. -/
theorem regularState_oddState (A : ℝ) (hA : A ∈ TwoCycle.normalizationSet) :
    regularState (TwoCycle.oddState A) := by
  have hpos := TwoCycle.oddState_mapsTo_positive hA
  have hfirst : 0 < A := by
    simpa only [Set.mem_Ioi, TwoCycle.oddState_firstDiagonal] using hpos.1
  have hdet : 0 < (TwoCycle.oddState A).1 * (TwoCycle.oddState A).2.2 -
      (TwoCycle.oddState A).2.1 ^ 2 := by
    rw [← stateMatrix_det, stateMatrix_def, TwoCycle.oddState_det A hA]
    exact hfirst
  exact ⟨Set.mem_Ioi.mp hpos.1, Set.mem_Ioi.mp hpos.2.1, hdet⟩

/-- Helper for lem:polar-continuation: scaling and inverse scaling are
mutually inverse at every nonzero scale. -/
theorem scaleMatrix_mul_invScaleMatrix (t : ℝ) (ht : t ≠ 0) :
    scaleMatrix t * invScaleMatrix t = 1 := by
  rw [scaleMatrix_def, invScaleMatrix_def]
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals simp [Matrix.mul_apply, Fin.sum_univ_two, ht]

/-- Helper for lem:polar-continuation: inverse scaling cancels scaling. -/
theorem invScaleMatrix_mul_scaleMatrix (t : ℝ) (ht : t ≠ 0) :
    invScaleMatrix t * scaleMatrix t = 1 := by
  exact mul_eq_one_comm.mp (scaleMatrix_mul_invScaleMatrix t ht)

/-- Helper for lem:polar-continuation: the normalization matrix is
self-adjoint over the real scalars. -/
theorem scaleMatrix_conjTranspose (t : ℝ) : (scaleMatrix t)ᴴ = scaleMatrix t := by
  rw [scaleMatrix_def]
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals simp

/-- Helper for lem:polar-continuation: inverse normalization is symmetric. -/
theorem invScaleMatrix_transpose (t : ℝ) : (invScaleMatrix t).transpose = invScaleMatrix t := by
  rw [invScaleMatrix_def]
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals rfl

/-- Helper for lem:polar-continuation: nonzero scaling is an invertible
matrix change of coordinates. -/
theorem scaleMatrix_isUnit (t : ℝ) (ht : t ≠ 0) : IsUnit (scaleMatrix t) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [scaleMatrix_def, Matrix.det_fin_two]
  simp [isUnit_iff_ne_zero, ht]

/-- Helper for lem:polar-continuation: normalization preserves and reflects
positive definiteness of the actual Hermitian local matrix. -/
theorem normalized_posDef_iff (t : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ)
    (hZ : Z.IsHermitian) (ht : 0 < t) :
    (stateMatrix (coordinates t Z)).PosDef ↔ Z.PosDef := by
  rw [stateMatrix_def, coordinates_eq_scaleMatrix_mul t Z hZ]
  simpa only [Matrix.star_eq_conjTranspose, scaleMatrix_conjTranspose] using
    Matrix.IsUnit.posDef_star_left_conjugate_iff (x := Z) (scaleMatrix_isUnit t ht.ne')

/-- Helper for lem:polar-continuation: the physical local matrix is exactly
the inverse-scale congruence of its normalized reconstruction. -/
theorem invScaleMatrix_reconstruction (t : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ)
    (hZ : Z.IsHermitian) (ht : 0 < t) :
    invScaleMatrix t * stateMatrix (coordinates t Z) * invScaleMatrix t = Z := by
  rw [stateMatrix_def, coordinates_eq_scaleMatrix_mul t Z hZ]
  calc
    invScaleMatrix t * (scaleMatrix t * Z * scaleMatrix t) * invScaleMatrix t =
        (invScaleMatrix t * scaleMatrix t) * Z * (scaleMatrix t * invScaleMatrix t) := by
      simp only [Matrix.mul_assoc]
    _ = Z := by
      rw [invScaleMatrix_mul_scaleMatrix t ht.ne', scaleMatrix_mul_invScaleMatrix t ht.ne',
        Matrix.one_mul, Matrix.mul_one]

/-- Helper for lem:polar-continuation: positive normalization does not change
the sign of the actual off-diagonal matrix entry. -/
theorem normalized_offDiagonal_pos_iff (t : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ)
    (ht : 0 < t) : 0 < (coordinates t Z).2.1 ↔ 0 < Z 0 1 := by
  rw [coordinates_apply]
  exact mul_pos_iff_of_pos_left (sq_pos_of_pos ht)

/-- Helper for lem:polar-continuation: the actual normalized radius factor. -/
def normalizedRadiusFactor (i : Fin 2) (t : ℝ) (x : ℝ × ℝ × ℝ) : ℝ :=
  Real.cos (stageAngle i t) + t ^ 2 * slope x * Real.sin (stageAngle i t)

/-- Helper for lem:polar-continuation: the explicit source radius formula. -/
theorem normalizedRadiusFactor_def (i : Fin 2) (t : ℝ) (x : ℝ × ℝ × ℝ) :
    normalizedRadiusFactor i t x =
      Real.cos (stageAngle i t) + t ^ 2 * slope x * Real.sin (stageAngle i t) := by
  rfl

/-- Helper for lem:polar-continuation: every zero-scale radius factor is one. -/
theorem normalizedRadiusFactor_zero (i : Fin 2) (x : ℝ × ℝ × ℝ) :
    normalizedRadiusFactor i 0 x = 1 := by
  simp [normalizedRadiusFactor_def, stageAngle_def]

/-- Helper for lem:polar-continuation: the normalized slope and physical
slope differ by the prescribed squared scale. -/
theorem scale_sq_mul_slope_coordinates (t : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ)
    (ht : 0 < t) : t ^ 2 * slope (coordinates t Z) = omegaOf Z := by
  rw [slope_def, coordinates_apply, omegaOf_def]
  simp only [div_eq_mul_inv, mul_inv_rev]
  field_simp [ht.ne']

/-- Helper for lem:polar-continuation: the named normalized radius factor
is the actual raw recurrence's radius ratio. -/
theorem normalizedRadiusFactor_eq_radiusRatioOf (i : Fin 2) (t : ℝ)
    (Z : Matrix (Fin 2) (Fin 2) ℝ) (ht : 0 < t) :
    normalizedRadiusFactor i t (coordinates t Z) = radiusRatioOf Z (stageAngle i t) := by
  rw [normalizedRadiusFactor_def, scale_sq_mul_slope_coordinates t Z ht, radiusRatioOf_def]

/-- Helper for lem:polar-continuation: reciprocal scaling of the displacement
and gradient change preserves the actual secant scalar. -/
theorem stageSigma_eq_sigmaOf (i : Fin 2) (t : ℝ)
    (Z : Matrix (Fin 2) (Fin 2) ℝ) (ζ η : ℝ) (ht : 0 < t) :
    stageSigma i t (coordinates t Z) ζ η = sigmaOf Z (stageAngle i t) ζ η := by
  rw [stageSigma_def, stepV_eq_invScaleMatrix_mulVec t Z ht,
    stepW_eq_scaleMatrix_mulVec i t Z ζ η ht, Matrix.dotProduct_mulVec,
    Matrix.vecMul_mulVec, invScaleMatrix_transpose,
    invScaleMatrix_mul_scaleMatrix t ht.ne', Matrix.vecMul_one, sigmaOf_def]

/-- Helper for lem:polar-continuation: the actual normalized even matrix
is positive definite exactly when its physical even matrix is. -/
theorem normalizedEvenState_posDef_iff (p : Parameters) (j : ℕ)
    (hstart : 0 < p.startIndex) :
    (stateMatrix (p.normalizedEvenState j)).PosDef ↔ (p.evenMatrix j).PosDef := by
  rw [stateMatrix_def, Parameters.normalizedEvenState_matrix]
  simpa only [Matrix.star_eq_conjTranspose, scaleMatrix_conjTranspose] using
    Matrix.IsUnit.posDef_star_left_conjugate_iff (x := p.evenMatrix j)
      (scaleMatrix_isUnit (p.scale j) (ScaleTails.scale_pos p hstart j).ne')

/-- Helper for lem:polar-continuation and eq:polar-initial-matrix: the exact
initial matrix normalizes to the genuine even cycle at `p.kStar`. -/
theorem normalizedEvenState_zero (p : Parameters) (hstart : 0 < p.startIndex)
    (hν : p.cycleParameter ∈ TwoCycle.parameterSet) :
    p.normalizedEvenState 0 = TwoCycle.evenState p.kStar := by
  have ht := ScaleTails.scale_pos p hstart 0
  have hinverse : TwoCycle.inverseParameter p.kStar = p.cycleParameter := by
    rw [Parameters.kStar_def]
    exact TwoCycle.inverseParameter_invOn.1 hν
  rw [Parameters.normalizedEvenState_apply, Parameters.evenMatrix_zero,
    Parameters.initialMatrix_def, TwoCycle.evenState_apply, hinverse,
    ← Parameters.wStar_def p]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  apply Prod.ext
  · field_simp [ht.ne']
  · apply Prod.ext
    · field_simp [ht.ne']
    · rfl

/-- Helper for lem:polar-continuation: symmetric coordinate reconstruction
is a continuous function of the three state entries. -/
theorem continuous_stateMatrix : Continuous stateMatrix := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i
  all_goals fin_cases j
  all_goals simp only [stateMatrix_def, RealSymmetric2.matrix_eq, Matrix.of_apply,
    Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  all_goals fun_prop

/-- Helper for lem:polar-continuation: the original slope varies continuously
along any state path whose limiting off-diagonal entry is nonzero. -/
theorem slopeAlong_continuousAt {E : Type*} [TopologicalSpace E]
    {X : E → ℝ × ℝ × ℝ} {z : E} (hX : ContinuousAt X z) (hC : (X z).2.1 ≠ 0) :
    ContinuousAt (fun y ↦ slope (X y)) z := by
  have hCV : ContinuousAt (fun y ↦ (X y).2) z :=
    continuousAt_snd.comp_of_eq hX rfl
  have hC' : ContinuousAt (fun y ↦ (X y).2.1) z :=
    continuousAt_fst.comp_of_eq hCV rfl
  have hV : ContinuousAt (fun y ↦ (X y).2.2) z :=
    continuousAt_snd.comp_of_eq hCV rfl
  simp only [slope_def]
  fun_prop (disch := assumption)

/-- Helper for lem:polar-continuation: the normalized secant scalar in scalar
coordinates, preserving the exact stage gradient change. -/
theorem stageSigma_scalar (i : Fin 2) (t : ℝ) (x : ℝ × ℝ × ℝ) (ζ η : ℝ) :
    stageSigma i t x ζ η =
      -slope x * ((η - ζ) * cotFactor i t - ζ * t ^ 4 * slope x) + η := by
  simp [stageSigma_def, stepV_def, stepW_def]

/-- Helper for lem:polar-continuation: regular scale, slope, and multiplier
germs give a continuous secant scalar at zero scale. -/
theorem stageSigmaAlong_continuousAt {E : Type*} [TopologicalSpace E]
    (i : Fin 2) {τ : E → ℝ} {X : E → ℝ × ℝ × ℝ} {ζ η : E → ℝ} {z : E}
    (hτ : ContinuousAt τ z) (hSlope : ContinuousAt (fun y ↦ slope (X y)) z)
    (hζ : ContinuousAt ζ z) (hη : ContinuousAt η z) (hτ0 : τ z = 0) :
    ContinuousAt (fun y ↦ stageSigma i (τ y) (X y) (ζ y) (η y)) z := by
  have hCot := (cotFactor_analyticAt i).continuousAt.comp_of_eq hτ hτ0
  simp only [stageSigma_scalar]
  fun_prop

/-- Helper for lem:polar-continuation: unit multipliers give the positive
limiting secant scalar one at every zero-scale state. -/
theorem stageSigma_zero_unit (i : Fin 2) (x : ℝ × ℝ × ℝ) :
    stageSigma i 0 x 1 1 = 1 := by
  simp [stageSigma_scalar]

/-- Helper for lem:polar-continuation: the original normalized radius factor
is continuous along regular state and scale germs at zero scale. -/
theorem normalizedRadiusFactorAlong_continuousAt {E : Type*} [TopologicalSpace E]
    (i : Fin 2) {τ : E → ℝ} {X : E → ℝ × ℝ × ℝ} {z : E}
    (hτ : ContinuousAt τ z) (hX : ContinuousAt X z) (hτ0 : τ z = 0)
    (hC : (X z).2.1 ≠ 0) :
    ContinuousAt (fun y ↦ normalizedRadiusFactor i (τ y) (X y)) z := by
  have hAngle := (stageAngle_analyticAt i).continuousAt.comp_of_eq hτ hτ0
  have hSlope := slopeAlong_continuousAt hX hC
  simp only [normalizedRadiusFactor_def]
  fun_prop

/-- Helper for lem:polar-continuation: the exact normalized stage matrix
preserves continuous regular scale, state, and multiplier germs. -/
theorem stageMatrixAlong_continuousAt {E : Type*} [TopologicalSpace E]
    (i : Fin 2) {τ : E → ℝ} {X : E → ℝ × ℝ × ℝ} {ζ η : E → ℝ} {z : E}
    (hτ : ContinuousAt τ z) (hX : ContinuousAt X z)
    (hζ : ContinuousAt ζ z) (hη : ContinuousAt η z) (hτ0 : τ z = 0)
    (hC : (X z).2.1 ≠ 0) (hσ : stageSigma i (τ z) (X z) (ζ z) (η z) ≠ 0) :
    ContinuousAt (fun y ↦ stageMatrix i (τ y) (X y) (ζ y) (η y)) z := by
  have hSlope := slopeAlong_continuousAt hX hC
  have hAngle := (stageAngle_analyticAt i).continuousAt.comp_of_eq hτ hτ0
  have hSin := (sinFactor_analyticAt i).continuousAt.comp_of_eq hτ hτ0
  have hCot := (cotFactor_analyticAt i).continuousAt.comp_of_eq hτ hτ0
  have hv : ContinuousAt (fun y ↦ stepV (X y)) z := by
    apply continuousAt_pi.mpr
    intro j
    fin_cases j
    · simp only [stepV_def, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      exact hSlope.neg
    · simp only [stepV_def, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      exact continuousAt_const
  have hw : ContinuousAt (fun y ↦ stepW i (τ y) (X y) (ζ y) (η y)) z := by
    apply continuousAt_pi.mpr
    intro j
    fin_cases j
    · simp only [stepW_def, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      fun_prop
    · simpa only [stepW_def, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] using hη
  have hR : ContinuousAt (fun y ↦ rotation i (τ y)) z := by
    apply continuousAt_pi.mpr
    intro r
    apply continuousAt_pi.mpr
    intro c
    fin_cases r
    all_goals fin_cases c
    all_goals simp only [rotation_def, Matrix.of_apply, Fin.zero_eta, Fin.mk_one,
      Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    all_goals fun_prop
  have hSecant := stageSigmaAlong_continuousAt i hτ hSlope hζ hη hτ0
  have hSecantInv : ContinuousAt
      (fun y ↦ (stageSigma i (τ y) (X y) (ζ y) (η y))⁻¹) z := by
    fun_prop (disch := assumption)
  have hM := continuous_stateMatrix.continuousAt.comp_of_eq hX rfl
  have houter : Continuous (fun d : (Fin 2 → ℝ) × (Fin 2 → ℝ) ↦
      Matrix.vecMulVec d.1 d.2) := continuous_fst.matrix_vecMulVec continuous_snd
  have hwv := houter.continuousAt.comp_of_eq (hw.prodMk hv) rfl
  have hvw := houter.continuousAt.comp_of_eq (hv.prodMk hw) rfl
  have hww := houter.continuousAt.comp_of_eq (hw.prodMk hw) rfl
  have htranspose : Continuous
      (fun R : Matrix (Fin 2) (Fin 2) ℝ ↦ R.transpose) := continuous_id.matrix_transpose
  have hRT := htranspose.continuousAt.comp_of_eq hR rfl
  have hbracket : ContinuousAt
      (fun y ↦
        (1 - (stageSigma i (τ y) (X y) (ζ y) (η y))⁻¹ •
            Matrix.vecMulVec (stepW i (τ y) (X y) (ζ y) (η y)) (stepV (X y))) *
          stateMatrix (X y) *
            (1 - (stageSigma i (τ y) (X y) (ζ y) (η y))⁻¹ •
              Matrix.vecMulVec (stepV (X y)) (stepW i (τ y) (X y) (ζ y) (η y))) +
          (stageSigma i (τ y) (X y) (ζ y) (η y))⁻¹ •
            Matrix.vecMulVec (stepW i (τ y) (X y) (ζ y) (η y))
              (stepW i (τ y) (X y) (ζ y) (η y))) z := by
    fun_prop
  have hmatrix := (hR.fun_mul hbracket).fun_mul hRT
  simpa only [stageMatrix_def, stateMatrix_def, Function.comp_def] using hmatrix

/-- Helper for lem:polar-continuation: the selected three coordinates of the
exact stage preserve the same continuous regular germs. -/
theorem stageAlong_continuousAt {E : Type*} [TopologicalSpace E]
    (i : Fin 2) {τ : E → ℝ} {X : E → ℝ × ℝ × ℝ} {ζ η : E → ℝ} {z : E}
    (hτ : ContinuousAt τ z) (hX : ContinuousAt X z)
    (hζ : ContinuousAt ζ z) (hη : ContinuousAt η z) (hτ0 : τ z = 0)
    (hC : (X z).2.1 ≠ 0) (hσ : stageSigma i (τ z) (X z) (ζ z) (η z) ≠ 0) :
    ContinuousAt (fun y ↦ stage i (τ y) (X y) (ζ y) (η y)) z := by
  have hM := stageMatrixAlong_continuousAt i hτ hX hζ hη hτ0 hC hσ
  have h00 := continuousAt_pi.mp (continuousAt_pi.mp hM 0) 0
  have h01 := continuousAt_pi.mp (continuousAt_pi.mp hM 0) 1
  have h11 := continuousAt_pi.mp (continuousAt_pi.mp hM 1) 1
  simpa only [stage_apply] using h00.prodMk (h01.prodMk h11)

/-- Helper for lem:polar-continuation: the actual boundary feedback is
continuous along zero-scale state germs with nonzero boundary amplitude. -/
theorem feedbackAlong_continuousAt {E : Type*} [TopologicalSpace E]
    (L κ : ℝ) {τ : E → ℝ} {X₀ : E → ℝ × ℝ × ℝ} {z : E}
    (hτ : ContinuousAt τ z) (hX₀ : ContinuousAt X₀ z) (hA : (X₀ z).1 ≠ 0) :
    ContinuousAt (fun y ↦ feedback L κ (τ y) (X₀ y)) z := by
  have hfirst := continuousAt_fst.comp_of_eq hX₀ rfl
  simp only [feedback_def]
  fun_prop (disch := assumption)

/-- Helper for lem:polar-continuation: each actual cycle stage varies
continuously in scale, boundary state, and the state being updated. -/
theorem cycleStageAlong_continuousAt {E : Type*} [TopologicalSpace E]
    (L κ : ℝ) (i : Fin 2) {τ : E → ℝ} {X₀ X : E → ℝ × ℝ × ℝ} {z : E}
    (hτ : ContinuousAt τ z) (hX₀ : ContinuousAt X₀ z) (hX : ContinuousAt X z)
    (hτ0 : τ z = 0) (hA : (X₀ z).1 ≠ 0) (hC : (X z).2.1 ≠ 0) :
    ContinuousAt (fun y ↦ cycleStage L κ i (τ y) (X₀ y) (X y)) z := by
  have hfb := feedbackAlong_continuousAt L κ hτ hX₀ hA
  have hfb0 : feedback L κ (τ z) (X₀ z) = 1 := by
    rw [hτ0]
    simp [feedback_def]
  fin_cases i
  · have hσ : stageSigma 0 (τ z) (X z) 1 (feedback L κ (τ z) (X₀ z)) ≠ 0 := by
      rw [hfb0, hτ0, stageSigma_zero_unit]
      exact one_ne_zero
    simpa only [cycleStage_apply, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero] using
      stageAlong_continuousAt 0 hτ hX continuousAt_const hfb hτ0 hC hσ
  · have hσ : stageSigma 1 (τ z) (X z) (feedback L κ (τ z) (X₀ z)) 1 ≠ 0 := by
      rw [hfb0, hτ0, stageSigma_zero_unit]
      exact one_ne_zero
    simpa only [cycleStage_apply, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] using
      stageAlong_continuousAt 1 hτ hX hfb continuousAt_const hτ0 hC hσ

/-- Helper for lem:polar-continuation: the actual input to each phase of a
cycle, with the odd phase using the computed first-stage output. -/
def cycleInput (L κ : ℝ) (i : Fin 2) (t : ℝ) (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (![x, cycleStage L κ 0 t x x] : Fin 2 → ℝ × ℝ × ℝ) i

/-- Helper for lem:polar-continuation: the source phase-selection formula
for the actual stage input. -/
theorem cycleInput_def (L κ : ℝ) (i : Fin 2) (t : ℝ) (x : ℝ × ℝ × ℝ) :
    cycleInput L κ i t x = (![x, cycleStage L κ 0 t x x] : Fin 2 → ℝ × ℝ × ℝ) i := by
  rfl

/-- Helper for lem:polar-continuation: the even phase starts at the boundary state. -/
theorem cycleInput_zero (L κ t : ℝ) (x : ℝ × ℝ × ℝ) : cycleInput L κ 0 t x = x := by
  rfl

/-- Helper for lem:polar-continuation: the odd phase starts at the actual
first-stage output with feedback from the original boundary state. -/
theorem cycleInput_one (L κ t : ℝ) (x : ℝ × ℝ × ℝ) :
    cycleInput L κ 1 t x = cycleStage L κ 0 t x x := by
  rfl

/-- Helper for lem:polar-continuation: the actual secant scalar of either
phase, using the one shared original boundary feedback. -/
def cycleSecant (L κ : ℝ) (i : Fin 2) (t : ℝ) (x : ℝ × ℝ × ℝ) : ℝ :=
  stageSigma i t (cycleInput L κ i t x)
    (![1, feedback L κ t x] i) (![feedback L κ t x, 1] i)

/-- Helper for lem:polar-continuation: the actual stage secant in terms of
its phase input and shared boundary feedback. -/
theorem cycleSecant_def (L κ : ℝ) (i : Fin 2) (t : ℝ) (x : ℝ × ℝ × ℝ) :
    cycleSecant L κ i t x = stageSigma i t (cycleInput L κ i t x)
      (![1, feedback L κ t x] i) (![feedback L κ t x, 1] i) := by
  rfl

/-- Helper for lem:polar-continuation: the even phase secant scalar. -/
theorem cycleSecant_zero (L κ t : ℝ) (x : ℝ × ℝ × ℝ) :
    cycleSecant L κ 0 t x = stageSigma 0 t x 1 (feedback L κ t x) := by
  rfl

/-- Helper for lem:polar-continuation: the odd phase secant scalar uses the
computed odd state, while keeping the original cycle feedback. -/
theorem cycleSecant_one (L κ t : ℝ) (x : ℝ × ℝ × ℝ) :
    cycleSecant L κ 1 t x =
      stageSigma 1 t (cycleStage L κ 0 t x x) (feedback L κ t x) 1 := by
  rfl

/-- Helper for lem:polar-continuation: the secant scalar in either limiting
stage is one, so its eventual sign is positive. -/
theorem cycleSecant_at_zero (L κ : ℝ) (i : Fin 2) (x : ℝ × ℝ × ℝ) :
    cycleSecant L κ i 0 x = 1 := by
  have hfb : feedback L κ 0 x = 1 := by simp [feedback_def]
  have hone : (![1, 1] : Fin 2 → ℝ) = fun _ ↦ 1 := by
    ext j
    fin_cases j
    all_goals rfl
  simp only [cycleSecant, hfb, hone]
  exact stageSigma_zero_unit i _

/-- Helper for lem:polar-continuation: the actual first cycle stage is
jointly continuous in scale and boundary state on its regular zero-scale domain. -/
theorem firstStage_continuousAt (L κ : ℝ) (x : ℝ × ℝ × ℝ)
    (hA : x.1 ≠ 0) (hC : x.2.1 ≠ 0) :
    ContinuousAt (fun z : ℝ × (ℝ × ℝ × ℝ) ↦ cycleStage L κ 0 z.1 z.2 z.2) (0, x) := by
  exact cycleStageAlong_continuousAt L κ 0 continuousAt_fst continuousAt_snd
    continuousAt_snd rfl hA hC

/-- Helper for lem:polar-continuation: the actual input state of either
phase is continuous at a regular zero-scale boundary. -/
theorem cycleInput_continuousAt (L κ : ℝ) (i : Fin 2) (x : ℝ × ℝ × ℝ)
    (hA : x.1 ≠ 0) (hC : x.2.1 ≠ 0) :
    ContinuousAt (fun z : ℝ × (ℝ × ℝ × ℝ) ↦ cycleInput L κ i z.1 z.2) (0, x) := by
  fin_cases i
  · simpa only [Fin.zero_eta, Fin.isValue, cycleInput_zero] using
      (continuousAt_snd : ContinuousAt (fun z : ℝ × (ℝ × ℝ × ℝ) ↦ z.2) (0, x))
  · simpa only [Fin.mk_one, Fin.isValue, cycleInput_one] using
      firstStage_continuousAt L κ x hA hC

/-- Helper for lem:polar-continuation: both actual stages are jointly
continuous when the limiting input to each stage has nonzero off-diagonal entry. -/
theorem twoStep_continuousAt (L κ : ℝ) (x : ℝ × ℝ × ℝ)
    (hA : x.1 ≠ 0) (hC : x.2.1 ≠ 0)
    (hCNext : (leadingStage (limitAngle 0) x).2.1 ≠ 0) :
    ContinuousAt (fun z : ℝ × (ℝ × ℝ × ℝ) ↦ twoStep L κ z.1 z.2) (0, x) := by
  have hfirst := firstStage_continuousAt L κ x hA hC
  have hfirstC : (cycleStage L κ 0 0 x x).2.1 ≠ 0 := by
    rw [cycleStage_zero]
    exact hCNext
  simpa only [twoStep_def] using cycleStageAlong_continuousAt L κ 1
    continuousAt_fst continuousAt_snd hfirst rfl hA hfirstC

/-- Helper for lem:polar-continuation: the actual even and odd secant
scalars vary continuously along the full two-stage cycle. -/
theorem cycleSecant_continuousAt (L κ : ℝ) (i : Fin 2) (x : ℝ × ℝ × ℝ)
    (hA : x.1 ≠ 0) (hC : x.2.1 ≠ 0)
    (hCNext : (leadingStage (limitAngle 0) x).2.1 ≠ 0) :
    ContinuousAt (fun z : ℝ × (ℝ × ℝ × ℝ) ↦ cycleSecant L κ i z.1 z.2) (0, x) := by
  have hX : ContinuousAt (fun z : ℝ × (ℝ × ℝ × ℝ) ↦ z.2) (0, x) := continuousAt_snd
  have hτ : ContinuousAt (fun z : ℝ × (ℝ × ℝ × ℝ) ↦ z.1) (0, x) := continuousAt_fst
  have hfb := feedbackAlong_continuousAt L κ hτ hX hA
  have hSlope := slopeAlong_continuousAt hX hC
  have hfirst := firstStage_continuousAt L κ x hA hC
  have hfirstC : (cycleStage L κ 0 0 x x).2.1 ≠ 0 := by
    rw [cycleStage_zero]
    exact hCNext
  have hSlopeNext := slopeAlong_continuousAt hfirst hfirstC
  fin_cases i
  · simpa only [Fin.zero_eta, Fin.isValue, cycleSecant_zero] using
      stageSigmaAlong_continuousAt 0 hτ hSlope continuousAt_const hfb rfl
  · simpa only [Fin.mk_one, Fin.isValue, cycleSecant_one] using
      stageSigmaAlong_continuousAt 1 hτ hSlopeNext hfb continuousAt_const rfl

/-- Helper for lem:polar-continuation: both actual radius factors vary
continuously along the cycle, including the computed odd input state. -/
theorem cycleRadius_continuousAt (L κ : ℝ) (i : Fin 2) (x : ℝ × ℝ × ℝ)
    (hA : x.1 ≠ 0) (hC : x.2.1 ≠ 0)
    (hCNext : (leadingStage (limitAngle 0) x).2.1 ≠ 0) :
    ContinuousAt (fun z : ℝ × (ℝ × ℝ × ℝ) ↦
      normalizedRadiusFactor i z.1 (cycleInput L κ i z.1 z.2)) (0, x) := by
  have hinput := cycleInput_continuousAt L κ i x hA hC
  have hinputC : (cycleInput L κ i 0 x).2.1 ≠ 0 := by
    fin_cases i
    · simpa only [Fin.zero_eta, Fin.isValue, cycleInput_zero] using hC
    · simpa only [Fin.mk_one, Fin.isValue, cycleInput_one, cycleStage_zero] using hCNext
  exact normalizedRadiusFactorAlong_continuousAt i continuousAt_fst hinput rfl hinputC

/-- Helper for lem:polar-continuation: strict scalar regularity is preserved
on a neighborhood along every continuous normalized state germ. -/
theorem eventually_regularState {E : Type*} [TopologicalSpace E]
    {X : E → ℝ × ℝ × ℝ} {z : E} (hX : ContinuousAt X z) (hx : regularState (X z)) :
    ∀ᶠ y in 𝓝 z, regularState (X y) := by
  have hA : ContinuousAt (fun y ↦ (X y).1) z := continuousAt_fst.comp_of_eq hX rfl
  have hCV : ContinuousAt (fun y ↦ (X y).2) z := continuousAt_snd.comp_of_eq hX rfl
  have hC : ContinuousAt (fun y ↦ (X y).2.1) z := continuousAt_fst.comp_of_eq hCV rfl
  have hV : ContinuousAt (fun y ↦ (X y).2.2) z := continuousAt_snd.comp_of_eq hCV rfl
  have hdet : ContinuousAt (fun y ↦ (X y).1 * (X y).2.2 - (X y).2.1 ^ 2) z := by
    fun_prop
  filter_upwards [hA.eventually (Ioi_mem_nhds hx.1),
    hC.eventually (Ioi_mem_nhds hx.2.1), hdet.eventually (Ioi_mem_nhds hx.2.2)] with
    y hyA hyC hydet
  exact ⟨hyA, hyC, hydet⟩

/-- Helper for lem:polar-continuation: the original first limiting stage
carries the even cycle to the odd cycle. -/
theorem firstStage_zero_evenState (L κ A : ℝ) (hA : A ∈ TwoCycle.normalizationSet) :
    cycleStage L κ 0 0 (TwoCycle.evenState A) (TwoCycle.evenState A) =
      TwoCycle.oddState A := by
  rw [cycleStage_zero, limitAngle_zero, TwoCycle.evenToOdd A hA]

/-- Helper for lem:polar-continuation: both original limiting stages return
the even cycle to itself. -/
theorem twoStep_zero_evenState (L κ A : ℝ) (hA : A ∈ TwoCycle.normalizationSet) :
    twoStep L κ 0 (TwoCycle.evenState A) = TwoCycle.evenState A := by
  rw [twoStep_def, firstStage_zero_evenState L κ A hA, cycleStage_zero,
    limitAngle_one, TwoCycle.oddToEven A hA]

/-- Helper for lem:polar-continuation: near a genuine even cycle all three
actual states are regular and both secant and radius factors have the fixed
positive lower bound `1/2`. -/
theorem eventually_regularCycle (L κ A : ℝ) (hA : A ∈ TwoCycle.normalizationSet) :
    ∀ᶠ z : ℝ × (ℝ × ℝ × ℝ) in 𝓝 (0, TwoCycle.evenState A),
      regularState z.2 ∧ regularState (cycleStage L κ 0 z.1 z.2 z.2) ∧
        regularState (twoStep L κ z.1 z.2) ∧
          (∀ i : Fin 2, (1 / 2 : ℝ) ≤ cycleSecant L κ i z.1 z.2) ∧
            ∀ i : Fin 2, (1 / 2 : ℝ) ≤
              normalizedRadiusFactor i z.1 (cycleInput L κ i z.1 z.2) := by
  have hE := regularState_evenState A hA
  have hO := regularState_oddState A hA
  have hCNext : (leadingStage (limitAngle 0) (TwoCycle.evenState A)).2.1 ≠ 0 := by
    rw [limitAngle_zero, TwoCycle.evenToOdd A hA]
    exact hO.2.1.ne'
  have hfirst := firstStage_continuousAt L κ (TwoCycle.evenState A) hE.1.ne' hE.2.1.ne'
  have htwo := twoStep_continuousAt L κ (TwoCycle.evenState A)
    hE.1.ne' hE.2.1.ne' hCNext
  have hfirstRegular : regularState
      (cycleStage L κ 0 0 (TwoCycle.evenState A) (TwoCycle.evenState A)) := by
    rw [firstStage_zero_evenState L κ A hA]
    exact hO
  have htwoRegular : regularState (twoStep L κ 0 (TwoCycle.evenState A)) := by
    rw [twoStep_zero_evenState L κ A hA]
    exact hE
  have hsecants : ∀ᶠ z : ℝ × (ℝ × ℝ × ℝ) in 𝓝 (0, TwoCycle.evenState A),
      ∀ i : Fin 2, (1 / 2 : ℝ) ≤ cycleSecant L κ i z.1 z.2 := by
    apply Filter.eventually_all.mpr
    intro i
    have hlim : (1 / 2 : ℝ) < cycleSecant L κ i 0 (TwoCycle.evenState A) := by
      rw [cycleSecant_at_zero]
      norm_num
    exact ((cycleSecant_continuousAt L κ i (TwoCycle.evenState A)
      hE.1.ne' hE.2.1.ne' hCNext).eventually (Ioi_mem_nhds hlim)).mono fun _ hz ↦ hz.le
  have hradii : ∀ᶠ z : ℝ × (ℝ × ℝ × ℝ) in 𝓝 (0, TwoCycle.evenState A),
      ∀ i : Fin 2, (1 / 2 : ℝ) ≤
        normalizedRadiusFactor i z.1 (cycleInput L κ i z.1 z.2) := by
    apply Filter.eventually_all.mpr
    intro i
    have hlim : (1 / 2 : ℝ) < normalizedRadiusFactor i 0
        (cycleInput L κ i 0 (TwoCycle.evenState A)) := by
      rw [normalizedRadiusFactor_zero]
      norm_num
    exact ((cycleRadius_continuousAt L κ i (TwoCycle.evenState A)
      hE.1.ne' hE.2.1.ne' hCNext).eventually (Ioi_mem_nhds hlim)).mono fun _ hz ↦ hz.le
  filter_upwards [eventually_regularState
    (continuousAt_snd : ContinuousAt (fun z : ℝ × (ℝ × ℝ × ℝ) ↦ z.2)
      (0, TwoCycle.evenState A)) hE,
    eventually_regularState hfirst hfirstRegular, eventually_regularState htwo htwoRegular,
    hsecants, hradii] with z hx hy hz hsec hradius
  exact ⟨hx, hy, hz, hsec, hradius⟩

/-- Helper for lem:polar-continuation: one fixed compact even-state ball and
one scale threshold give actual two-stage regularity, with positive secants
and radius factors uniformly bounded below independently of `j₀`. -/
theorem exists_uniform_regularCycle (L κ A : ℝ) (hA : A ∈ TwoCycle.normalizationSet) :
    ∃ r > 0, ∃ δ > 0, ∀ t ∈ Set.Icc (-δ) δ,
      ∀ x ∈ Metric.closedBall (TwoCycle.evenState A) r,
        regularState x ∧ regularState (cycleStage L κ 0 t x x) ∧
          regularState (twoStep L κ t x) ∧
            (∀ i : Fin 2, (1 / 2 : ℝ) ≤ cycleSecant L κ i t x) ∧
              ∀ i : Fin 2, (1 / 2 : ℝ) ≤
                normalizedRadiusFactor i t (cycleInput L κ i t x) := by
  obtain ⟨ε, hε, hbound⟩ := Metric.eventually_nhds_iff.mp (eventually_regularCycle L κ A hA)
  refine ⟨ε / 2, half_pos hε, ε / 2, half_pos hε, ?_⟩
  intro t ht x hx
  have htAbs : |t| ≤ ε / 2 := abs_le.mpr ht
  have hxDist := Metric.mem_closedBall.mp hx
  apply hbound (y := (t, x))
  rw [Prod.dist_eq, max_lt_iff]
  constructor
  · simpa only [dist_zero_right, Real.norm_eq_abs] using
      htAbs.trans_lt (half_lt_self hε)
  · exact hxDist.trans_lt (half_lt_self hε)

/-- Helper for lem:polar-continuation: reconstruction of the selected stage
coordinates recovers the exact Hermitian normalized stage matrix. -/
theorem stateMatrix_stage (i : Fin 2) (t : ℝ) (x : ℝ × ℝ × ℝ) (ζ η : ℝ) :
    stateMatrix (stage i t x ζ η) = stageMatrix i t x ζ η := by
  have hsymm : stageMatrix i t x ζ η 1 0 = stageMatrix i t x ζ η 0 1 := by
    simpa only [star_trivial] using (stageMatrix_isHermitian i t x ζ η).apply 0 1
  rw [stateMatrix_def, stage_apply, RealSymmetric2.matrix_eq]
  ext r c
  fin_cases r
  · fin_cases c
    · rfl
    · rfl
  · fin_cases c
    · exact hsymm.symm
    · rfl

/-- Helper for lem:polar-continuation: the explicit even phase of the
source cycle uses unit even multiplier and the original boundary feedback. -/
theorem cycleStage_even_apply (L κ t : ℝ) (x₀ x : ℝ × ℝ × ℝ) :
    cycleStage L κ 0 t x₀ x = stage 0 t x 1 (feedback L κ t x₀) := by
  rw [cycleStage_apply]
  rfl

/-- Helper for lem:polar-continuation: the explicit odd phase uses the
same original boundary feedback and the unit next even multiplier. -/
theorem cycleStage_odd_apply (L κ t : ℝ) (x₀ x : ℝ × ℝ × ℝ) :
    cycleStage L κ 1 t x₀ x = stage 1 t x (feedback L κ t x₀) 1 := by
  rw [cycleStage_apply]
  rfl

/-- Helper for lem:polar-continuation: the exact boundary change of scale
preserves positive determinants and positive off-diagonal entries. -/
theorem regularState_rescale (t : ℝ) (x : ℝ × ℝ × ℝ) (hx : regularState x) :
    regularState (rescale t x) := by
  have hρ : 0 < rescaleFactor t := by
    rw [rescaleFactor_def, unitRoot_def]
    positivity
  rw [regularState_def, rescale_apply]
  refine ⟨mul_pos (sq_pos_of_pos hρ) hx.1, mul_pos hρ hx.2.1, ?_⟩
  calc
    0 < rescaleFactor t ^ 2 * (x.1 * x.2.2 - x.2.1 ^ 2) :=
      mul_pos (sq_pos_of_pos hρ) hx.2.2
    _ = (rescaleFactor t ^ 2 * x.1) * x.2.2 - (rescaleFactor t * x.2.1) ^ 2 := by
      ring

/-- lem:polar-continuation, actual stage feasibility: one fixed compact
even-state neighborhood and scale threshold make the input, both computed
stage outputs, and the rescaled output positive definite with positive
off-diagonal entries. Secants and radius factors are uniformly positive,
and all original normalized denominators are bounded away from zero. -/
theorem exists_uniform_stageFeasibility (L κ A : ℝ) (hA : A ∈ TwoCycle.normalizationSet) :
    ∃ r > 0, ∃ δ > 0, ∃ d > 0, ∀ t ∈ Set.Icc (-δ) δ,
      ∀ x ∈ Metric.closedBall (TwoCycle.evenState A) r,
        (stateMatrix x).PosDef ∧ 0 < x.2.1 ∧
          (stageMatrix 0 t x 1 (feedback L κ t x)).PosDef ∧
            0 < (cycleStage L κ 0 t x x).2.1 ∧
              (stageMatrix 1 t (cycleStage L κ 0 t x x) (feedback L κ t x) 1).PosDef ∧
                0 < (twoStep L κ t x).2.1 ∧
                  (stateMatrix (Normalized.map L κ t x)).PosDef ∧
                    0 < (Normalized.map L κ t x).2.1 ∧
                      (∀ i : Fin 2, (1 / 2 : ℝ) ≤ cycleSecant L κ i t x) ∧
                        (∀ i : Fin 2, (1 / 2 : ℝ) ≤
                          normalizedRadiusFactor i t (cycleInput L κ i t x)) ∧
                            ∀ i : Fin 9, d ≤ |denominators L κ t x i| := by
  obtain ⟨r, hr, δ₀, hδ₀, hregular⟩ := exists_uniform_regularCycle L κ A hA
  have hzero : (0 : ℝ) ∈ Set.Icc (-δ₀) δ₀ := ⟨neg_nonpos.mpr hδ₀.le, hδ₀.le⟩
  have hfirst : ∀ x ∈ Metric.closedBall (TwoCycle.evenState A) r,
      0 < x.1 := fun x hx ↦ (hregular 0 hzero x hx).1.1
  have hoff : ∀ x ∈ Metric.closedBall (TwoCycle.evenState A) r,
      0 < x.2.1 := fun x hx ↦ (hregular 0 hzero x hx).1.2.1
  have hnext : ∀ x ∈ Metric.closedBall (TwoCycle.evenState A) r,
      0 < (leadingStage (limitAngle 0) x).2.1 := by
    intro x hx
    have h := (hregular 0 hzero x hx).2.1.2.1
    simpa only [cycleStage_zero] using h
  obtain ⟨ε, hε, d, hd, hdenom⟩ := denominators_uniformOn L κ
    (Metric.closedBall (TwoCycle.evenState A) r) (isCompact_closedBall _ _)
    hfirst hoff hnext
  refine ⟨r, hr, min δ₀ ε, lt_min hδ₀ hε, d, hd, ?_⟩
  intro t ht x hx
  have htAbs : |t| ≤ min δ₀ ε := abs_le.mpr (Set.mem_Icc.mp ht)
  have ht₀ : t ∈ Set.Icc (-δ₀) δ₀ := by
    exact Set.mem_Icc.mpr (abs_le.mp (htAbs.trans (min_le_left _ _)))
  have htε : t ∈ Set.Icc (-ε) ε := by
    exact Set.mem_Icc.mpr (abs_le.mp (htAbs.trans (min_le_right _ _)))
  have hgood := hregular t ht₀ x hx
  have hxPD := (regularState_posDef x hgood.1).1
  have hfirstPD := (regularState_posDef _ hgood.2.1).1
  rw [cycleStage_even_apply, stateMatrix_stage] at hfirstPD
  have hsecondPD := (regularState_posDef _ hgood.2.2.1).1
  rw [twoStep_def, cycleStage_odd_apply, stateMatrix_stage] at hsecondPD
  have hmap : regularState (Normalized.map L κ t x) := by
    rw [Normalized.map_def]
    exact regularState_rescale t _ hgood.2.2.1
  exact ⟨hxPD, hgood.1.2.1, hfirstPD, hgood.2.1.2.1,
    hsecondPD, hgood.2.2.1.2.1, (regularState_posDef _ hmap).1, hmap.2.1,
    hgood.2.2.2.1, hgood.2.2.2.2, hdenom t htε x hx⟩

/-- Helper for lem:polar-continuation and eq:polar-initial-matrix: the chosen
`p.kStar` belongs to the original normalization family. -/
theorem kStar_mem_normalizationSet (p : Parameters)
    (hν : p.cycleParameter ∈ TwoCycle.parameterSet) : p.kStar ∈ TwoCycle.normalizationSet := by
  rw [Parameters.kStar_def]
  exact TwoCycle.cycleK_bijOn_parameterSet.mapsTo hν

/-- Helper for lem:polar-continuation: normalization preserves the sign of
the actual even matrix's off-diagonal entry at every prescribed cycle. -/
theorem normalizedEvenState_offDiagonal_pos_iff (p : Parameters) (j : ℕ)
    (hstart : 0 < p.startIndex) :
    0 < (p.normalizedEvenState j).2.1 ↔ 0 < p.evenMatrix j 0 1 := by
  rw [Parameters.normalizedEvenState_apply]
  exact mul_pos_iff_of_pos_left (sq_pos_of_pos (ScaleTails.scale_pos p hstart j))

/-- Helper for lem:polar-continuation and eq:polar-initial-matrix: the actual
initial local matrix is positive definite, without an extra positivity assumption. -/
theorem initialMatrix_posDef (p : Parameters) (hstart : 0 < p.startIndex)
    (hν : p.cycleParameter ∈ TwoCycle.parameterSet) : p.initialMatrix.PosDef := by
  have hnorm : (stateMatrix (p.normalizedEvenState 0)).PosDef := by
    rw [normalizedEvenState_zero p hstart hν]
    exact (regularState_posDef _ (regularState_evenState _
      (kStar_mem_normalizationSet p hν))).1
  simpa only [Parameters.evenMatrix_zero] using
    (normalizedEvenState_posDef_iff p 0 hstart).mp hnorm

/-- Helper for lem:polar-continuation and eq:polar-initial-matrix: the actual
initial off-diagonal matrix entry is positive. -/
theorem initialMatrix_offDiagonal_pos (p : Parameters) (hstart : 0 < p.startIndex)
    (hν : p.cycleParameter ∈ TwoCycle.parameterSet) : 0 < p.initialMatrix 0 1 := by
  have hnorm : 0 < (p.normalizedEvenState 0).2.1 := by
    rw [normalizedEvenState_zero p hstart hν]
    exact (regularState_evenState _ (kStar_mem_normalizationSet p hν)).2.1
  simpa only [Parameters.evenMatrix_zero] using
    (normalizedEvenState_offDiagonal_pos_iff p 0 hstart).mp hnorm

/-- Helper for lem:polar-continuation and eq:polar-initial-matrix: the source
initial slow and fast displacements both vanish exactly. -/
theorem initial_errors_zero (p : Parameters) (hstart : 0 < p.startIndex)
    (hν : p.cycleParameter ∈ TwoCycle.parameterSet) :
    (p.normalizedEvenState 0).1 - p.kStar = 0 ∧
      FastContraction.fastError (p.normalizedEvenState 0) = 0 := by
  rw [normalizedEvenState_zero p hstart hν, TwoCycle.evenState_firstDiagonal,
    sub_self, FastContraction.fastError_def, TwoCycle.evenState_firstDiagonal, sub_self]
  exact ⟨rfl, rfl⟩

/-- Helper for lem:polar-continuation: the actual raw stage is positive
definite exactly when its normalized stage matrix is positive definite. -/
theorem stageMatrix_posDef_iff (i : Fin 2) (t : ℝ)
    (Z : Matrix (Fin 2) (Fin 2) ℝ) (ζ η : ℝ) (hZ : Z.IsHermitian) (ht : 0 < t) :
    (stageMatrix i t (coordinates t Z) ζ η).PosDef ↔
      (matrixStep Z (stageAngle i t) ζ η).PosDef := by
  rw [stageMatrix_eq_scaleMatrix_mul i t Z ζ η hZ ht]
  simpa only [Matrix.star_eq_conjTranspose, scaleMatrix_conjTranspose] using
    Matrix.IsUnit.posDef_star_left_conjugate_iff
      (x := matrixStep Z (stageAngle i t) ζ η) (scaleMatrix_isUnit t ht.ne')

/-- Helper for lem:polar-continuation: the actual first physical matrix
update, with feedback computed from its original normalized even input. -/
def rawFirstStage (L κ t : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  matrixStep Z (stageAngle 0 t) 1 (feedback L κ t (coordinates t Z))

/-- Helper for lem:polar-continuation: the source formula for the first
physical stage. -/
theorem rawFirstStage_def (L κ t : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) :
    rawFirstStage L κ t Z =
      matrixStep Z (stageAngle 0 t) 1 (feedback L κ t (coordinates t Z)) := by
  rfl

/-- Helper for lem:polar-continuation: the second physical matrix update
uses the computed first matrix and the same original cycle feedback. -/
def rawSecondStage (L κ t : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  matrixStep (rawFirstStage L κ t Z) (stageAngle 1 t)
    (feedback L κ t (coordinates t Z)) 1

/-- Helper for lem:polar-continuation: the source formula for the second
physical stage. -/
theorem rawSecondStage_def (L κ t : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ) :
    rawSecondStage L κ t Z = matrixStep (rawFirstStage L κ t Z) (stageAngle 1 t)
      (feedback L κ t (coordinates t Z)) 1 := by
  rfl

/-- Helper for lem:polar-continuation: the computed first physical stage
preserves Hermitian symmetry. -/
theorem rawFirstStage_isHermitian (L κ t : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ)
    (hZ : Z.IsHermitian) : (rawFirstStage L κ t Z).IsHermitian := by
  rw [rawFirstStage_def]
  exact matrixStep_isHermitian _ _ _ _ hZ

/-- Helper for lem:polar-continuation: the computed second physical stage
preserves Hermitian symmetry. -/
theorem rawSecondStage_isHermitian (L κ t : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ)
    (hZ : Z.IsHermitian) : (rawSecondStage L κ t Z).IsHermitian := by
  rw [rawSecondStage_def]
  exact matrixStep_isHermitian _ _ _ _ (rawFirstStage_isHermitian L κ t Z hZ)

/-- Helper for lem:polar-continuation: the actual normalized odd-phase input
is the coordinate image of the computed first physical matrix. -/
theorem cycleInput_one_coordinates (L κ t : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ)
    (hZ : Z.IsHermitian) (ht : 0 < t) :
    cycleInput L κ 1 t (coordinates t Z) = coordinates t (rawFirstStage L κ t Z) := by
  rw [cycleInput_one, cycleStage_even_apply, rawFirstStage_def]
  exact stageCoordinates 0 t Z 1 (feedback L κ t (coordinates t Z)) hZ ht

/-- Helper for lem:polar-continuation: the exact two-stage normalized output
is the coordinate image of the computed second physical matrix. -/
theorem twoStep_coordinates (L κ t : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ)
    (hZ : Z.IsHermitian) (ht : 0 < t) :
    twoStep L κ t (coordinates t Z) = coordinates t (rawSecondStage L κ t Z) := by
  have hfirst := cycleInput_one_coordinates L κ t Z hZ ht
  rw [cycleInput_one] at hfirst
  rw [twoStep_def, hfirst, cycleStage_odd_apply, rawSecondStage_def]
  exact stageCoordinates 1 t (rawFirstStage L κ t Z)
    (feedback L κ t (coordinates t Z)) 1 (rawFirstStage_isHermitian L κ t Z hZ) ht

/-- Helper for lem:polar-continuation: the actual normalized even secant
scalar equals the raw first-stage secant scalar. -/
theorem cycleSecant_zero_eq_sigmaOf (L κ t : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ)
    (ht : 0 < t) :
    cycleSecant L κ 0 t (coordinates t Z) =
      sigmaOf Z (stageAngle 0 t) 1 (feedback L κ t (coordinates t Z)) := by
  rw [cycleSecant_zero]
  exact stageSigma_eq_sigmaOf 0 t Z 1 (feedback L κ t (coordinates t Z)) ht

/-- Helper for lem:polar-continuation: the actual normalized odd secant
scalar equals the raw secant scalar at the computed first physical matrix. -/
theorem cycleSecant_one_eq_sigmaOf (L κ t : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ)
    (hZ : Z.IsHermitian) (ht : 0 < t) :
    cycleSecant L κ 1 t (coordinates t Z) =
      sigmaOf (rawFirstStage L κ t Z) (stageAngle 1 t)
        (feedback L κ t (coordinates t Z)) 1 := by
  have hfirst := cycleInput_one_coordinates L κ t Z hZ ht
  rw [cycleInput_one] at hfirst
  rw [cycleSecant_one, hfirst]
  exact stageSigma_eq_sigmaOf 1 t (rawFirstStage L κ t Z)
    (feedback L κ t (coordinates t Z)) 1 ht

/-- Helper for lem:polar-continuation: the actual even normalized radius
factor equals the first physical radius ratio. -/
theorem cycleRadius_zero_eq_radiusRatioOf (L κ t : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ)
    (ht : 0 < t) :
    normalizedRadiusFactor 0 t (cycleInput L κ 0 t (coordinates t Z)) =
      radiusRatioOf Z (stageAngle 0 t) := by
  rw [cycleInput_zero, normalizedRadiusFactor_eq_radiusRatioOf 0 t Z ht]

/-- Helper for lem:polar-continuation: the actual odd normalized radius
factor equals the radius ratio at the computed first physical matrix. -/
theorem cycleRadius_one_eq_radiusRatioOf (L κ t : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℝ)
    (hZ : Z.IsHermitian) (ht : 0 < t) :
    normalizedRadiusFactor 1 t (cycleInput L κ 1 t (coordinates t Z)) =
      radiusRatioOf (rawFirstStage L κ t Z) (stageAngle 1 t) := by
  rw [cycleInput_one_coordinates L κ t Z hZ ht,
    normalizedRadiusFactor_eq_radiusRatioOf 1 t (rawFirstStage L κ t Z) ht]

/-- Helper for lem:polar-continuation: one fixed normalized neighborhood
makes the actual first and second physical updates positive definite, with
positive off-diagonal entries, positive secant scalars, and positive radius
ratios uniformly bounded below, independently of `j₀`. -/
theorem exists_uniform_rawCycleFeasibility (L κ A : ℝ)
    (hA : A ∈ TwoCycle.normalizationSet) :
    ∃ r > 0, ∃ δ > 0, ∃ d > 0, ∀ t ∈ Set.Ioc (0 : ℝ) δ,
      ∀ Z : Matrix (Fin 2) (Fin 2) ℝ, Z.IsHermitian →
        coordinates t Z ∈ Metric.closedBall (TwoCycle.evenState A) r →
          Z.PosDef ∧ 0 < Z 0 1 ∧
            (rawFirstStage L κ t Z).PosDef ∧ 0 < rawFirstStage L κ t Z 0 1 ∧
              (rawSecondStage L κ t Z).PosDef ∧ 0 < rawSecondStage L κ t Z 0 1 ∧
                (1 / 2 : ℝ) ≤ sigmaOf Z (stageAngle 0 t) 1
                  (feedback L κ t (coordinates t Z)) ∧
                  (1 / 2 : ℝ) ≤ sigmaOf (rawFirstStage L κ t Z) (stageAngle 1 t)
                    (feedback L κ t (coordinates t Z)) 1 ∧
                    (1 / 2 : ℝ) ≤ radiusRatioOf Z (stageAngle 0 t) ∧
                      (1 / 2 : ℝ) ≤ radiusRatioOf (rawFirstStage L κ t Z) (stageAngle 1 t) ∧
                        ∀ i : Fin 9, d ≤ |denominators L κ t (coordinates t Z) i| := by
  obtain ⟨r, hr, δ, hδ, d, hd, hfeasible⟩ := exists_uniform_stageFeasibility L κ A hA
  refine ⟨r, hr, δ, hδ, d, hd, ?_⟩
  intro t ht Z hZ hx
  have htBoth : t ∈ Set.Icc (-δ) δ := by
    constructor
    · linarith [ht.1]
    · exact ht.2
  rcases hfeasible t htBoth (coordinates t Z) hx with
    ⟨hxPD, hxC, hfirstPD, hfirstC, hsecondPD, hsecondC, _, _, hsec, hrad, hden⟩
  have hfirstCoordinates := cycleInput_one_coordinates L κ t Z hZ ht.1
  rw [cycleInput_one] at hfirstCoordinates
  have htwoCoordinates := twoStep_coordinates L κ t Z hZ ht.1
  have hZFirst := rawFirstStage_isHermitian L κ t Z hZ
  rw [hfirstCoordinates] at hfirstC hsecondPD
  rw [htwoCoordinates] at hsecondC
  have hrawFirstPD : (rawFirstStage L κ t Z).PosDef := by
    rw [rawFirstStage_def]
    exact (stageMatrix_posDef_iff 0 t Z 1 (feedback L κ t (coordinates t Z)) hZ ht.1).mp hfirstPD
  have hrawSecondPD : (rawSecondStage L κ t Z).PosDef := by
    rw [rawSecondStage_def]
    exact (stageMatrix_posDef_iff 1 t (rawFirstStage L κ t Z)
      (feedback L κ t (coordinates t Z)) 1 hZFirst ht.1).mp hsecondPD
  have hsecEven := hsec 0
  have hsecOdd := hsec 1
  have hradEven := hrad 0
  have hradOdd := hrad 1
  rw [cycleSecant_zero_eq_sigmaOf L κ t Z ht.1] at hsecEven
  rw [cycleSecant_one_eq_sigmaOf L κ t Z hZ ht.1] at hsecOdd
  rw [cycleRadius_zero_eq_radiusRatioOf L κ t Z ht.1] at hradEven
  rw [cycleRadius_one_eq_radiusRatioOf L κ t Z hZ ht.1] at hradOdd
  exact ⟨(normalized_posDef_iff t Z hZ ht.1).mp hxPD,
    (normalized_offDiagonal_pos_iff t Z ht.1).mp hxC, hrawFirstPD,
    (normalized_offDiagonal_pos_iff t _ ht.1).mp hfirstC, hrawSecondPD,
    (normalized_offDiagonal_pos_iff t _ ht.1).mp hsecondC,
    hsecEven, hsecOdd, hradEven, hradOdd, hden⟩

/-- Helper for lem:polar-continuation: the prescribed even normalized state
is exactly the coordinate image of its actual even physical matrix. -/
theorem normalizedEvenState_eq_coordinates (p : Parameters) (j : ℕ) :
    p.normalizedEvenState j = coordinates (p.scale j) (p.evenMatrix j) := by
  rw [Parameters.normalizedEvenState_apply, coordinates_apply]

/-- Helper for lem:polar-continuation: the shared normalized feedback at a
prescribed scale equals the original raw recurrence's odd multiplier. -/
theorem feedback_coordinates_prescribed (p : Parameters) (j : ℕ)
    (Z : Matrix (Fin 2) (Fin 2) ℝ) :
    feedback p.feedbackRate p.kStar (p.scale j) (coordinates (p.scale j) Z) =
      p.oddMultiplierOf j Z := by
  rw [feedback_def, Parameters.oddMultiplierOf_def, Parameters.amplitudeOf_def,
    coordinates_apply]

/-- Helper for lem:polar-continuation: the even stage angle at the
prescribed scale is the original first angle increment of the cycle. -/
theorem stageAngle_even_prescribed (p : Parameters) (j : ℕ) (hstart : 0 < p.startIndex) :
    stageAngle 0 (p.scale j) = p.oddAngle j - p.evenAngle j := by
  have hangle := stageAngle_scale p 0 j hstart
  simpa only [Fin.val_zero, Nat.add_zero, Parameters.angleIncrement_def,
    Parameters.angle_odd, Parameters.angle_even] using hangle

/-- Helper for lem:polar-continuation: the odd stage angle at the
prescribed scale is the original second angle increment of the cycle. -/
theorem stageAngle_odd_prescribed (p : Parameters) (j : ℕ) (hstart : 0 < p.startIndex) :
    stageAngle 1 (p.scale j) = p.evenAngle (j + 1) - p.oddAngle j := by
  have hangle := stageAngle_scale p 1 j hstart
  norm_num only [Fin.val_one] at hangle
  rw [Parameters.angleIncrement_def] at hangle
  have hnext : 2 * j + 1 + 1 = 2 * (j + 1) := by omega
  rw [hnext, Parameters.angle_even, Parameters.angle_odd] at hangle
  exact hangle

/-- Helper for lem:polar-continuation: the first physical stage used by the
local feasibility theorem is exactly the original prescribed first matrix stage. -/
theorem rawFirstStage_prescribed (p : Parameters) (j : ℕ)
    (Z : Matrix (Fin 2) (Fin 2) ℝ) (hstart : 0 < p.startIndex) :
    rawFirstStage p.feedbackRate p.kStar (p.scale j) Z = p.firstStageMatrix j Z := by
  rw [rawFirstStage_def, feedback_coordinates_prescribed,
    stageAngle_even_prescribed p j hstart, Parameters.firstStageMatrix_def]

/-- Helper for lem:polar-continuation: the second physical stage used by
the local feasibility theorem is exactly the original prescribed next even matrix. -/
theorem rawSecondStage_prescribed (p : Parameters) (j : ℕ)
    (Z : Matrix (Fin 2) (Fin 2) ℝ) (hstart : 0 < p.startIndex) :
    rawSecondStage p.feedbackRate p.kStar (p.scale j) Z = p.nextEvenMatrix j Z := by
  rw [rawSecondStage_def, rawFirstStage_prescribed p j Z hstart,
    stageAngle_odd_prescribed p j hstart, feedback_coordinates_prescribed,
    Parameters.nextEvenMatrix_def, Parameters.firstStageMatrix_def]

/-- Helper for lem:polar-continuation: the normalized odd input in the
actual recurrence is the coordinate image of `p.oddMatrix j`. -/
theorem cycleInput_one_evenMatrix (p : Parameters) (j : ℕ) (hstart : 0 < p.startIndex) :
    cycleInput p.feedbackRate p.kStar 1 (p.scale j) (p.normalizedEvenState j) =
      coordinates (p.scale j) (p.oddMatrix j) := by
  rw [normalizedEvenState_eq_coordinates,
    cycleInput_one_coordinates p.feedbackRate p.kStar (p.scale j) (p.evenMatrix j)
      (Parameters.evenMatrix_isHermitian p j) (ScaleTails.scale_pos p hstart j),
    rawFirstStage_prescribed p j (p.evenMatrix j) hstart, Parameters.oddMatrix_def]

/-- Helper for lem:polar-continuation and eq:polar-initial-matrix: the exact
initial physical matrix is the inverse-scale congruence of the genuine even cycle. -/
theorem initialMatrix_eq_invScaleMatrix_mul (p : Parameters) (hstart : 0 < p.startIndex)
    (hν : p.cycleParameter ∈ TwoCycle.parameterSet) :
    p.initialMatrix = invScaleMatrix (p.scale 0) * stateMatrix (TwoCycle.evenState p.kStar) *
      invScaleMatrix (p.scale 0) := by
  have h := invScaleMatrix_reconstruction (p.scale 0) (p.evenMatrix 0)
    (Parameters.evenMatrix_isHermitian p 0) (ScaleTails.scale_pos p hstart 0)
  rw [← normalizedEvenState_eq_coordinates p 0, normalizedEvenState_zero p hstart hν,
    Parameters.evenMatrix_zero] at h
  exact h.symm

/-- Helper for lem:polar-continuation: the actual even-stage normalized
secant scalar is the prescribed full recurrence scalar `σ₂ⱼ`. -/
theorem cycleSecant_even_prescribed (p : Parameters) (j : ℕ) (hstart : 0 < p.startIndex) :
    cycleSecant p.feedbackRate p.kStar 0 (p.scale j) (p.normalizedEvenState j) =
      p.sigma (2 * j) := by
  rw [normalizedEvenState_eq_coordinates,
    cycleSecant_zero_eq_sigmaOf p.feedbackRate p.kStar (p.scale j) (p.evenMatrix j)
      (ScaleTails.scale_pos p hstart j), feedback_coordinates_prescribed,
    Parameters.sigma_def, Parameters.matrix_even, Parameters.zeta_even, Parameters.zeta_odd]
  simpa only [Fin.val_zero, Nat.add_zero] using
    congrArg (fun θ ↦ sigmaOf (p.evenMatrix j) θ 1 (p.oddMultiplierOf j (p.evenMatrix j)))
      (stageAngle_scale p 0 j hstart)

/-- Helper for lem:polar-continuation: the actual odd-stage normalized
secant scalar is the prescribed full recurrence scalar `σ₂ⱼ₊₁`. -/
theorem cycleSecant_odd_prescribed (p : Parameters) (j : ℕ) (hstart : 0 < p.startIndex) :
    cycleSecant p.feedbackRate p.kStar 1 (p.scale j) (p.normalizedEvenState j) =
      p.sigma (2 * j + 1) := by
  rw [normalizedEvenState_eq_coordinates,
    cycleSecant_one_eq_sigmaOf p.feedbackRate p.kStar (p.scale j) (p.evenMatrix j)
      (Parameters.evenMatrix_isHermitian p j) (ScaleTails.scale_pos p hstart j),
    rawFirstStage_prescribed p j (p.evenMatrix j) hstart, ← Parameters.oddMatrix_def p j,
    feedback_coordinates_prescribed, Parameters.sigma_def, Parameters.matrix_odd,
    Parameters.zeta_odd]
  have hnext : 2 * j + 1 + 1 = 2 * (j + 1) := by omega
  rw [hnext, Parameters.zeta_even]
  simpa only [Fin.val_one] using
    congrArg (fun θ ↦ sigmaOf (p.oddMatrix j) θ (p.oddMultiplierOf j (p.evenMatrix j)) 1)
      (stageAngle_scale p 1 j hstart)

/-- Helper for lem:polar-continuation: the actual even normalized radius
factor is the prescribed full recurrence factor `W₂ⱼ`. -/
theorem cycleRadius_even_prescribed (p : Parameters) (j : ℕ) (hstart : 0 < p.startIndex) :
    normalizedRadiusFactor 0 (p.scale j)
        (cycleInput p.feedbackRate p.kStar 0 (p.scale j) (p.normalizedEvenState j)) =
      p.radiusRatio (2 * j) := by
  rw [normalizedEvenState_eq_coordinates,
    cycleRadius_zero_eq_radiusRatioOf p.feedbackRate p.kStar (p.scale j) (p.evenMatrix j)
      (ScaleTails.scale_pos p hstart j), Parameters.radiusRatio_def, Parameters.matrix_even]
  simpa only [Fin.val_zero, Nat.add_zero] using
    congrArg (radiusRatioOf (p.evenMatrix j)) (stageAngle_scale p 0 j hstart)

/-- Helper for lem:polar-continuation: the actual odd normalized radius
factor is the prescribed full recurrence factor `W₂ⱼ₊₁`. -/
theorem cycleRadius_odd_prescribed (p : Parameters) (j : ℕ) (hstart : 0 < p.startIndex) :
    normalizedRadiusFactor 1 (p.scale j)
        (cycleInput p.feedbackRate p.kStar 1 (p.scale j) (p.normalizedEvenState j)) =
      p.radiusRatio (2 * j + 1) := by
  rw [normalizedEvenState_eq_coordinates,
    cycleRadius_one_eq_radiusRatioOf p.feedbackRate p.kStar (p.scale j) (p.evenMatrix j)
      (Parameters.evenMatrix_isHermitian p j) (ScaleTails.scale_pos p hstart j),
    rawFirstStage_prescribed p j (p.evenMatrix j) hstart, ← Parameters.oddMatrix_def p j,
    Parameters.radiusRatio_def, Parameters.matrix_odd]
  simpa only [Fin.val_one] using
    congrArg (radiusRatioOf (p.oddMatrix j)) (stageAngle_scale p 1 j hstart)

end DFP.Polar.StageFeasibility
