/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/DFP_wolfe_local/README.md (Contributors).
-/

module

public import Mathlib.Analysis.Matrix.PosDef
public import ReasLib.Optimization.DFP.Polar.AngularGeometry
public import ReasLib.Optimization.DFP.Polar.Continuation
public import ReasLib.Optimization.DFP.Polar.Realization
public import ReasLib.Optimization.DFP.Polar.RadiusProducts
public import ReasLib.Optimization.DFP.InverseUpdate.OrthogonalTransport
public import ReasLib.Optimization.DFP.InverseUpdate.Scaling

public section

noncomputable section

open scoped Matrix

namespace DFP.Polar.PhysicalRealization

/-- Helper for eq:polar-physical-step: real polar rotations are orthogonal. -/
theorem rotation_orthogonal (θ : ℝ) :
    rotationMatrix θ ∈ Matrix.orthogonalGroup (Fin 2) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff, rotationMatrix_def]
  ext i j
  fin_cases i
  · fin_cases j
    · simpa [Matrix.mul_apply, Fin.sum_univ_two, pow_two] using Real.cos_sq_add_sin_sq θ
    · simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
  · fin_cases j
    · simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
    · simpa [Matrix.mul_apply, Fin.sum_univ_two, pow_two] using Real.sin_sq_add_cos_sq θ

/-- Helper for eq:polar-physical-step: successive unreduced polar frames compose. -/
theorem rotation_add (θ δ : ℝ) :
    rotationMatrix (θ + δ) = rotationMatrix θ * rotationMatrix δ := by
  rw [rotationMatrix_def, rotationMatrix_def, rotationMatrix_def]
  ext i j
  fin_cases i
  · fin_cases j
    · simp [Matrix.mul_apply, Fin.sum_univ_two, Real.cos_add, sub_eq_add_neg]
    · simp [Matrix.mul_apply, Fin.sum_univ_two, Real.sin_add]
  · fin_cases j
    · simp [Matrix.mul_apply, Fin.sum_univ_two, Real.sin_add]
    · simp [Matrix.mul_apply, Fin.sum_univ_two, Real.cos_add, sub_eq_add_neg]
      ring

/-- Helper for eq:polar-physical-step: the exact radial recurrence gives the
physical chord with the common factor `rNext * sin δ`. -/
theorem chord_eq (Z : Matrix (Fin 2) (Fin 2) ℝ) (θ δ r rNext : ℝ)
    (hr : rNext * radiusRatioOf Z δ = r) :
    WithLp.ofLp (rNext • polarUnit (θ + δ) - r • polarUnit θ) =
      rotationMatrix θ *ᵥ ((rNext * Real.sin δ) • stepVOf Z) := by
  rw [← hr, radiusRatioOf_def, rotationMatrix_def, stepVOf_def]
  ext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Real.cos_add]
    ring
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Real.sin_add]
    ring

/-- Helper for eq:polar-physical-step: the exact radial recurrence gives the
physical secant with the same common factor as the chord. -/
theorem secant_eq (Z : Matrix (Fin 2) (Fin 2) ℝ) (θ δ r rNext ζ ζNext : ℝ)
    (hr : rNext * radiusRatioOf Z δ = r) (hsin : Real.sin δ ≠ 0) :
    WithLp.ofLp (ζNext • (rNext • polarUnit (θ + δ)) -
      ζ • (r • polarUnit θ)) =
        rotationMatrix θ *ᵥ ((rNext * Real.sin δ) • stepWOf Z δ ζ ζNext) := by
  rw [← hr, radiusRatioOf_def, rotationMatrix_def, stepWOf_def]
  ext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Real.cos_add,
      Real.cot_eq_cos_div_sin]
    field_simp [hsin]
    ring
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Real.sin_add,
      Real.cot_eq_cos_div_sin]
    field_simp [hsin]
    ring

/-- Helper for eq:polar-physical-step: the source chord identity in the radial
and tangential coordinates at the current point. -/
theorem chord_in_frame (Z : Matrix (Fin 2) (Fin 2) ℝ) (θ δ r rNext : ℝ)
    (hr : rNext * radiusRatioOf Z δ = r) :
    (rotationMatrix θ).transpose *ᵥ
      WithLp.ofLp (rNext • polarUnit (θ + δ) - r • polarUnit θ) =
        (rNext * Real.sin δ) • stepVOf Z := by
  rw [chord_eq Z θ δ r rNext hr, Matrix.mulVec_mulVec,
    (Matrix.mem_orthogonalGroup_iff' _ _).mp (rotation_orthogonal θ), Matrix.one_mulVec]

/-- Helper for eq:polar-physical-step: the source secant identity in the radial
and tangential coordinates at the current point. -/
theorem secant_in_frame (Z : Matrix (Fin 2) (Fin 2) ℝ) (θ δ r rNext ζ ζNext : ℝ)
    (hr : rNext * radiusRatioOf Z δ = r) (hsin : Real.sin δ ≠ 0) :
    (rotationMatrix θ).transpose *ᵥ
      WithLp.ofLp (ζNext • (rNext • polarUnit (θ + δ)) -
        ζ • (r • polarUnit θ)) =
          (rNext * Real.sin δ) • stepWOf Z δ ζ ζNext := by
  rw [secant_eq Z θ δ r rNext ζ ζNext hr hsin, Matrix.mulVec_mulVec,
    (Matrix.mem_orthogonalGroup_iff' _ _).mp (rotation_orthogonal θ), Matrix.one_mulVec]

/-- Helper for eq:polar-physical-step: multiplication of the source step vector
by its symmetric local matrix is purely radial. -/
theorem matrix_mul_stepV (Z : Matrix (Fin 2) (Fin 2) ℝ)
    (hZ : Z.IsHermitian) (hC : Z 0 1 ≠ 0) :
    Z *ᵥ stepVOf Z = (-(Z.det / Z 0 1)) • ![1, 0] := by
  have hsym : Z 1 0 = Z 0 1 := by
    simpa only [star_trivial] using hZ.apply 0 1
  rw [stepVOf_def, omegaOf_def, Matrix.det_fin_two]
  ext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hsym]
    field_simp
    ring
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hsym]
    field_simp
    ring

/-- Helper for eq:polar-physical-step: the inverse local matrix sends the
radial unit vector to the prescribed step direction. -/
theorem inverse_mul_radial (Z : Matrix (Fin 2) (Fin 2) ℝ)
    (hZ : Z.IsHermitian) (hC : Z 0 1 ≠ 0) (hdet : Z.det ≠ 0) :
    Z⁻¹ *ᵥ ![1, 0] = (-(Z 0 1 / Z.det)) • stepVOf Z := by
  have hunit : IsUnit Z.det := isUnit_iff_ne_zero.mpr hdet
  have hscalar : -(Z 0 1 / Z.det) * -(Z.det / Z 0 1) = 1 := by
    field_simp
  have hforward : Z *ᵥ ((-(Z 0 1 / Z.det)) • stepVOf Z) = ![1, 0] := by
    rw [Matrix.mulVec_smul, matrix_mul_stepV Z hZ hC, smul_smul, hscalar, one_smul]
  calc
    Z⁻¹ *ᵥ ![1, 0] = Z⁻¹ *ᵥ (Z *ᵥ ((-(Z 0 1 / Z.det)) • stepVOf Z)) := by
      rw [hforward]
    _ = (-(Z 0 1 / Z.det)) • stepVOf Z := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul Z hunit, Matrix.one_mulVec]

/-- Helper for eq:polar-physical-step: a radial vector is expressed in the
unreduced polar frame without changing its scale. -/
theorem radial_eq (θ r : ℝ) :
    WithLp.ofLp (r • polarUnit θ) = rotationMatrix θ *ᵥ (r • ![1, 0]) := by
  rw [rotationMatrix_def]
  ext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]

/-- Helper for eq:polar-physical-step: the original rotated inverse Hessian
sends a radial gradient to the exact negative chord direction. -/
theorem inverseHessian_mul_gradient (Z : Matrix (Fin 2) (Fin 2) ℝ)
    (θ r ζ : ℝ) (hZ : Z.IsHermitian) (hC : Z 0 1 ≠ 0) (hdet : Z.det ≠ 0) :
    (rotationMatrix θ * Z⁻¹ * (rotationMatrix θ).transpose) *ᵥ
      WithLp.ofLp (ζ • (r • polarUnit θ)) =
        (-(ζ * r * Z 0 1 / Z.det)) • (rotationMatrix θ *ᵥ stepVOf Z) := by
  rw [smul_smul, radial_eq,
    Matrix.conjugate_mulVec_of_mem_orthogonalGroup _ _ (rotation_orthogonal θ),
    Matrix.mulVec_smul, inverse_mul_radial Z hZ hC hdet]
  simp only [Matrix.mulVec_smul, smul_smul]
  congr 1
  ring

/-- Helper for eq:polar-physical-step: the explicit source step length is
positive under the local feasibility inequalities. -/
theorem stepLength_pos (Z : Matrix (Fin 2) (Fin 2) ℝ) (δ ζ : ℝ)
    (hZ : Z.PosDef) (hC : 0 < Z 0 1) (hζ : 0 < ζ)
    (hsin : 0 < Real.sin δ) (hW : 0 < radiusRatioOf Z δ) :
    0 < Z.det * Real.sin δ / (ζ * Z 0 1 * radiusRatioOf Z δ) := by
  exact div_pos (mul_pos hZ.det_pos hsin) (mul_pos (mul_pos hζ hC) hW)

/-- Helper for eq:polar-physical-step: the explicit source step length gives
the exact inverse-Hessian search step. -/
theorem search_step (Z : Matrix (Fin 2) (Fin 2) ℝ) (θ δ r rNext ζ : ℝ)
    (hr : rNext * radiusRatioOf Z δ = r) (hZ : Z.IsHermitian)
    (hC : Z 0 1 ≠ 0) (hdet : Z.det ≠ 0) (hζ : ζ ≠ 0)
    (hW : radiusRatioOf Z δ ≠ 0) :
    WithLp.ofLp (rNext • polarUnit (θ + δ) - r • polarUnit θ) =
      (-(Z.det * Real.sin δ / (ζ * Z 0 1 * radiusRatioOf Z δ))) •
        ((rotationMatrix θ * Z⁻¹ * (rotationMatrix θ).transpose) *ᵥ
          WithLp.ofLp (ζ • (r • polarUnit θ))) := by
  rw [chord_eq Z θ δ r rNext hr,
    inverseHessian_mul_gradient Z θ r ζ hZ hC hdet, Matrix.mulVec_smul, smul_smul]
  congr 1
  rw [← hr]
  field_simp

/-- Helper for eq:polar-physical-step: the physical secant pairing is the
square of the common chord/secant factor times the original scalar `σ`. -/
theorem secant_pairing (Z : Matrix (Fin 2) (Fin 2) ℝ) (θ δ r rNext ζ ζNext : ℝ)
    (hr : rNext * radiusRatioOf Z δ = r) (hsin : Real.sin δ ≠ 0) :
    WithLp.ofLp (rNext • polarUnit (θ + δ) - r • polarUnit θ) ⬝ᵥ
      WithLp.ofLp (ζNext • (rNext • polarUnit (θ + δ)) - ζ • (r • polarUnit θ)) =
        (rNext * Real.sin δ) ^ 2 * sigmaOf Z δ ζ ζNext := by
  rw [chord_eq Z θ δ r rNext hr, secant_eq Z θ δ r rNext ζ ζNext hr hsin,
    Matrix.dotProduct_mulVec_eq_of_mem_orthogonalGroup _ (rotation_orthogonal θ),
    Matrix.inverseDFPUpdate_secant_denominator_smul, sigmaOf_def]

/-- Helper for eq:polar-physical-step: positive radius, sine, and local secant
scalar give strictly positive physical curvature. -/
theorem secant_pairing_pos (Z : Matrix (Fin 2) (Fin 2) ℝ)
    (θ δ r rNext ζ ζNext : ℝ) (hr : rNext * radiusRatioOf Z δ = r)
    (hrNext : 0 < rNext) (hsin : 0 < Real.sin δ) (hσ : 0 < sigmaOf Z δ ζ ζNext) :
    0 < WithLp.ofLp (rNext • polarUnit (θ + δ) - r • polarUnit θ) ⬝ᵥ
      WithLp.ofLp (ζNext • (rNext • polarUnit (θ + δ)) - ζ • (r • polarUnit θ)) := by
  rw [secant_pairing Z θ δ r rNext ζ ζNext hr (ne_of_gt hsin)]
  exact mul_pos (sq_pos_of_pos (mul_pos hrNext hsin)) hσ

/-- Helper for eq:polar-physical-step: the factored Hessian rank update
whose inverse is the inverse-form DFP update. -/
def factoredHessianStep {n : Type*} [Fintype n] [DecidableEq n]
    (Z : Matrix n n ℝ) (s y : n → ℝ) : Matrix n n ℝ :=
  (1 - (s ⬝ᵥ y)⁻¹ • Matrix.vecMulVec y s) * Z *
    (1 - (s ⬝ᵥ y)⁻¹ • Matrix.vecMulVec s y) +
      (s ⬝ᵥ y)⁻¹ • Matrix.vecMulVec y y

/-- Helper for eq:polar-physical-step: the small public interface of the
factored Hessian rank update. -/
theorem factoredHessianStep_def {n : Type*} [Fintype n] [DecidableEq n]
    (Z : Matrix n n ℝ) (s y : n → ℝ) :
    factoredHessianStep Z s y =
      (1 - (s ⬝ᵥ y)⁻¹ • Matrix.vecMulVec y s) * Z *
        (1 - (s ⬝ᵥ y)⁻¹ • Matrix.vecMulVec s y) +
          (s ⬝ᵥ y)⁻¹ • Matrix.vecMulVec y y := by
  rfl

/-- Helper for eq:polar-physical-step: removing the secant projection from
DFP leaves exactly its metric rank correction. -/
theorem inverseDFPUpdate_remove_secant {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℝ) (s y : n → ℝ)
    (hq : y ⬝ᵥ (H *ᵥ y) ≠ 0) (hr : s ⬝ᵥ y ≠ 0) :
    Matrix.inverseDFPUpdate H s y * (1 - (s ⬝ᵥ y)⁻¹ • Matrix.vecMulVec y s) =
      H - (y ⬝ᵥ (H *ᵥ y))⁻¹ • Matrix.vecMulVec (H *ᵥ y) (y ᵥ* H) := by
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_vecMulVec,
    Matrix.inverseDFPUpdate_mulVec_secant hq hr, Matrix.inverseDFPUpdate_def]
  abel

/-- Helper for eq:polar-physical-step: complementary rank projections
cancel using only the nonzero secant pairing. -/
theorem complementaryProjection_product {n : Type*} [Fintype n] [DecidableEq n]
    (s y h : n → ℝ) (q : ℝ) (hr : s ⬝ᵥ y ≠ 0) :
    (1 - q • Matrix.vecMulVec h y) *
        (1 - (s ⬝ᵥ y)⁻¹ • Matrix.vecMulVec s y) +
      (s ⬝ᵥ y)⁻¹ • Matrix.vecMulVec s y = 1 := by
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.vecMulVec_mul_vecMulVec,
    Matrix.vecMulVec_smul, smul_smul, dotProduct_comm y s]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- Helper for eq:polar-physical-step: the inverse of the source factored
Hessian update is exactly DFP, obtained from the canonical secant identity. -/
theorem factoredHessianStep_inv {n : Type*} [Fintype n] [DecidableEq n]
    (Z H : Matrix n n ℝ) (s y : n → ℝ) (hHZ : H * Z = 1)
    (hq : y ⬝ᵥ (H *ᵥ y) ≠ 0) (hr : s ⬝ᵥ y ≠ 0) :
    (factoredHessianStep Z s y)⁻¹ = Matrix.inverseDFPUpdate H s y := by
  have hrow : (y ᵥ* H) ᵥ* Z = y := by
    rw [Matrix.vecMul_vecMul, hHZ, Matrix.vecMul_one]
  have hmetric :
      (H - (y ⬝ᵥ (H *ᵥ y))⁻¹ • Matrix.vecMulVec (H *ᵥ y) (y ᵥ* H)) * Z =
        1 - (y ⬝ᵥ (H *ᵥ y))⁻¹ • Matrix.vecMulVec (H *ᵥ y) y := by
    rw [Matrix.sub_mul, hHZ, Matrix.smul_mul, Matrix.vecMulVec_mul, hrow]
  apply Matrix.inv_eq_left_inv
  rw [factoredHessianStep_def, Matrix.mul_add, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, inverseDFPUpdate_remove_secant H s y hq hr, hmetric,
    Matrix.mul_smul, Matrix.mul_vecMulVec, Matrix.inverseDFPUpdate_mulVec_secant hq hr]
  exact complementaryProjection_product s y (H *ᵥ y) (y ⬝ᵥ (H *ᵥ y))⁻¹ hr

/-- Helper for eq:polar-physical-step: the original raw polar matrix step is
the rotated factored Hessian update, with its exact original vectors. -/
theorem matrixStep_eq_factored (Z : Matrix (Fin 2) (Fin 2) ℝ) (δ ζ ζNext : ℝ) :
    matrixStep Z δ ζ ζNext =
      (rotationMatrix δ).transpose *
        factoredHessianStep Z (stepVOf Z) (stepWOf Z δ ζ ζNext) * rotationMatrix δ := by
  rw [matrixStep_def, factoredHessianStep_def, sigmaOf_def]

/-- Helper for eq:polar-physical-step: a common nonzero scale cancels in a
secant-normalized rank-one term, including zero-curvature junk values. -/
theorem secantRankTerm_smul {n : Type*} [Fintype n]
    (s y v w : n → ℝ) {c : ℝ} (hc : c ≠ 0) :
    ((c • s) ⬝ᵥ (c • y))⁻¹ • Matrix.vecMulVec (c • v) (c • w) =
      (s ⬝ᵥ y)⁻¹ • Matrix.vecMulVec v w := by
  rw [Matrix.inverseDFPUpdate_secant_denominator_smul]
  by_cases hr : s ⬝ᵥ y = 0
  · simp [hr]
  · ext i j
    simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
    field_simp

/-- Helper for eq:polar-physical-step: the common chord/secant factor cancels
in the original factored Hessian update. -/
theorem factoredHessianStep_smul_pair {n : Type*} [Fintype n] [DecidableEq n]
    (Z : Matrix n n ℝ) (s y : n → ℝ) {c : ℝ} (hc : c ≠ 0) :
    factoredHessianStep Z (c • s) (c • y) = factoredHessianStep Z s y := by
  rw [factoredHessianStep_def, factoredHessianStep_def,
    secantRankTerm_smul s y y s hc, secantRankTerm_smul s y s y hc,
    secantRankTerm_smul s y y y hc]

/-- Helper for eq:polar-physical-step: rotations transport a mixed outer
product by the same coordinate change on both vectors. -/
theorem conjugate_outer {n : Type*} [Fintype n]
    (R : Matrix n n ℝ) (v w : n → ℝ) :
    R * Matrix.vecMulVec v w * R.transpose =
      Matrix.vecMulVec (R *ᵥ v) (R *ᵥ w) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]

/-- Helper for eq:polar-physical-step: the factored Hessian update commutes
with an orthogonal change of coordinates. -/
theorem factoredHessianStep_conjugate {n : Type*} [Fintype n] [DecidableEq n]
    (R Z : Matrix n n ℝ) (s y : n → ℝ)
    (hR : R ∈ Matrix.orthogonalGroup n ℝ) :
    R * factoredHessianStep Z s y * R.transpose =
      factoredHessianStep (R * Z * R.transpose) (R *ᵥ s) (R *ᵥ y) := by
  have hRRT := (Matrix.mem_orthogonalGroup_iff _ _).mp hR
  have hRTR := (Matrix.mem_orthogonalGroup_iff' _ _).mp hR
  have houter (v w : n → ℝ) :
      Matrix.vecMulVec (R *ᵥ v) (R *ᵥ w) =
        R * Matrix.vecMulVec v w * R.transpose := (conjugate_outer R v w).symm
  have hfactor (v w : n → ℝ) :
      1 - (s ⬝ᵥ y)⁻¹ • Matrix.vecMulVec (R *ᵥ v) (R *ᵥ w) =
        R * (1 - (s ⬝ᵥ y)⁻¹ • Matrix.vecMulVec v w) * R.transpose := by
    rw [houter]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul, hRRT]
  rw [factoredHessianStep_def, factoredHessianStep_def,
    Matrix.dotProduct_mulVec_eq_of_mem_orthogonalGroup R hR s y, hfactor, hfactor, houter]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc R.transpose R, hRTR,
    Matrix.one_mul]

/-- Helper for eq:polar-physical-step: inversion commutes with orthogonal
conjugation, including the canonical inverse at singular matrices. -/
theorem conjugate_inv {n : Type*} [Fintype n] [DecidableEq n]
    (R Z : Matrix n n ℝ) (hR : R ∈ Matrix.orthogonalGroup n ℝ) :
    (R * Z * R.transpose)⁻¹ = R * Z⁻¹ * R.transpose := by
  have hRinv : R⁻¹ = R.transpose :=
    Matrix.inv_eq_right_inv ((Matrix.mem_orthogonalGroup_iff _ _).mp hR)
  have hRTinv : R.transpose⁻¹ = R :=
    Matrix.inv_eq_right_inv ((Matrix.mem_orthogonalGroup_iff' _ _).mp hR)
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hRTinv, hRinv, Matrix.mul_assoc]

/-- Helper for eq:polar-physical-step: rotating the original raw stage by
the next frame cancels its outer rotations exactly. -/
theorem rotated_matrixStep (Z : Matrix (Fin 2) (Fin 2) ℝ) (θ δ ζ ζNext : ℝ) :
    rotationMatrix (θ + δ) * matrixStep Z δ ζ ζNext *
        (rotationMatrix (θ + δ)).transpose =
      factoredHessianStep (rotationMatrix θ * Z * (rotationMatrix θ).transpose)
        (rotationMatrix θ *ᵥ stepVOf Z) (rotationMatrix θ *ᵥ stepWOf Z δ ζ ζNext) := by
  have hRR := (Matrix.mem_orthogonalGroup_iff _ _).mp (rotation_orthogonal δ)
  rw [rotation_add, matrixStep_eq_factored, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc,
    ← Matrix.mul_assoc (rotationMatrix δ) (rotationMatrix δ).transpose,
    hRR, Matrix.one_mul]
  simpa only [Matrix.mul_assoc] using
    factoredHessianStep_conjugate _ _ _ _ (rotation_orthogonal θ)

/-- Helper for eq:polar-physical-step: the original rotated raw recurrence
is the factored physical Hessian recurrence after common-factor cancellation. -/
theorem physicalHessian_step (Z : Matrix (Fin 2) (Fin 2) ℝ)
    (θ δ r rNext ζ ζNext : ℝ) (hr : rNext * radiusRatioOf Z δ = r)
    (hrNext : rNext ≠ 0) (hsin : Real.sin δ ≠ 0) :
    rotationMatrix (θ + δ) * matrixStep Z δ ζ ζNext *
        (rotationMatrix (θ + δ)).transpose =
      factoredHessianStep (rotationMatrix θ * Z * (rotationMatrix θ).transpose)
        (WithLp.ofLp (rNext • polarUnit (θ + δ) - r • polarUnit θ))
        (WithLp.ofLp (ζNext • (rNext • polarUnit (θ + δ)) - ζ • (r • polarUnit θ))) := by
  rw [chord_eq Z θ δ r rNext hr, secant_eq Z θ δ r rNext ζ ζNext hr hsin,
    Matrix.mulVec_smul, Matrix.mulVec_smul,
    factoredHessianStep_smul_pair _ _ _ (mul_ne_zero hrNext hsin)]
  exact rotated_matrixStep Z θ δ ζ ζNext

/-- Helper for eq:polar-physical-step: multiplication of conjugated matrices
cancels the intermediate orthogonal frame. -/
theorem conjugate_mul {n : Type*} [Fintype n] [DecidableEq n]
    (R A B : Matrix n n ℝ) (hR : R ∈ Matrix.orthogonalGroup n ℝ) :
    (R * A * R.transpose) * (R * B * R.transpose) = R * (A * B) * R.transpose := by
  have hRTR := (Matrix.mem_orthogonalGroup_iff' _ _).mp hR
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc R.transpose R, hRTR, Matrix.one_mul]

/-- Helper for eq:polar-physical-step: rotating a positive definite matrix
preserves positive definiteness. -/
theorem conjugate_posDef {n : Type*} [Fintype n] [DecidableEq n]
    (R Z : Matrix n n ℝ) (hR : R ∈ Matrix.orthogonalGroup n ℝ) (hZ : Z.PosDef) :
    (R * Z * R.transpose).PosDef := by
  have hRRT := (Matrix.mem_orthogonalGroup_iff _ _).mp hR
  have hinjective : Function.Injective R.transpose.mulVec := by
    intro x y hxy
    have h := congrArg R.mulVec hxy
    simpa only [Matrix.mulVec_mulVec, hRRT, Matrix.one_mulVec] using h
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] using
    hZ.conjTranspose_mul_mul_same hinjective

/-- Helper for eq:polar-physical-step: inverting the actual rotated raw stage
produces the inverse DFP update for the physical chord and secant. -/
theorem physicalInverseHessian_step (Z : Matrix (Fin 2) (Fin 2) ℝ)
    (θ δ r rNext ζ ζNext : ℝ) (hr : rNext * radiusRatioOf Z δ = r)
    (hZ : Z.PosDef) (hrNext : 0 < rNext) (hsin : 0 < Real.sin δ)
    (hσ : 0 < sigmaOf Z δ ζ ζNext) :
    rotationMatrix (θ + δ) * (matrixStep Z δ ζ ζNext)⁻¹ *
        (rotationMatrix (θ + δ)).transpose =
      Matrix.inverseDFPUpdate
        (rotationMatrix θ * Z⁻¹ * (rotationMatrix θ).transpose)
        (WithLp.ofLp (rNext • polarUnit (θ + δ) - r • polarUnit θ))
        (WithLp.ofLp (ζNext • (rNext • polarUnit (θ + δ)) - ζ • (r • polarUnit θ))) := by
  have hunit : IsUnit Z.det := isUnit_iff_ne_zero.mpr (ne_of_gt hZ.det_pos)
  have hHZ :
      (rotationMatrix θ * Z⁻¹ * (rotationMatrix θ).transpose) *
        (rotationMatrix θ * Z * (rotationMatrix θ).transpose) = 1 := by
    rw [conjugate_mul _ _ _ (rotation_orthogonal θ), Matrix.nonsing_inv_mul Z hunit,
      Matrix.mul_one]
    exact (Matrix.mem_orthogonalGroup_iff _ _).mp (rotation_orthogonal θ)
  have hcurvature := secant_pairing_pos Z θ δ r rNext ζ ζNext hr hrNext hsin hσ
  have hH := conjugate_posDef _ _ (rotation_orthogonal θ) hZ.inv
  have hq := hH.inverseDFPUpdate_denominator_pos hcurvature
  rw [← conjugate_inv _ _ (rotation_orthogonal (θ + δ)),
    physicalHessian_step Z θ δ r rNext ζ ζNext hr (ne_of_gt hrNext) (ne_of_gt hsin)]
  exact factoredHessianStep_inv _ _ _ _ hHZ (ne_of_gt hq) (ne_of_gt hcurvature)

/-- Helper for eq:polar-physical-step: every actual prescribed increment is
less than `π` for every positive initial index. -/
theorem angleIncrement_lt_pi (p : Parameters) (hstart : 0 < p.startIndex) (k : ℕ) :
    p.angleIncrement k < Real.pi := by
  have hnonneg := ScaleTails.scale_nonneg p (k / 2)
  have hone := ScaleTails.scale_le_one p hstart (k / 2)
  have hsq : p.scale (k / 2) ^ 2 ≤ 1 := by
    nlinarith
  have hupper := (AngularGeometry.angleIncrement_bounds p hstart k).2
  have hcoefficient := AngularGeometry.baseAngle_pos
  have hbound := mul_le_mul_of_nonneg_left hsq (mul_nonneg (zero_le_two) hcoefficient.le)
  rw [baseAngle_def] at hupper hbound
  nlinarith [Real.pi_pos]

/-- Helper for eq:polar-physical-step: the sine of every actual increment is
strictly positive without discarding an initialized segment. -/
theorem angleIncrement_sin_pos (p : Parameters) (hstart : 0 < p.startIndex) (k : ℕ) :
    0 < Real.sin (p.angleIncrement k) := by
  exact Real.sin_pos_of_pos_of_lt_pi (AngularGeometry.angleIncrement_pos p hstart k)
    (angleIncrement_lt_pi p hstart k)

/-- Helper for eq:polar-physical-step: every original radial gradient
multiplier is strictly positive, including both phases of each cycle. -/
theorem zeta_pos (p : Parameters) (k : ℕ) : 0 < p.zeta k := by
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · rw [Parameters.zeta_even]
    exact zero_lt_one
  · rw [Parameters.zeta_odd, Parameters.oddMultiplierOf_def]
    exact Real.exp_pos _

/-- Helper for eq:polar-physical-step: the physical chord of the original
prescribed point sequence, in fixed standard coordinates. -/
def chord (p : Parameters) (k : ℕ) : Fin 2 → ℝ :=
  WithLp.ofLp (p.point (k + 1) - p.point k)

/-- Helper for eq:polar-physical-step: the public difference formula for the
physical chord of the original point sequence. -/
theorem chord_def (p : Parameters) (k : ℕ) :
    chord p k = WithLp.ofLp (p.point (k + 1) - p.point k) := by
  rfl

/-- Helper for eq:polar-physical-step: the physical secant of the original
prescribed gradient sequence, in fixed standard coordinates. -/
def secant (p : Parameters) (k : ℕ) : Fin 2 → ℝ :=
  WithLp.ofLp (p.gradient (k + 1) - p.gradient k)

/-- Helper for eq:polar-physical-step: the public difference formula for the
physical secant of the original gradient sequence. -/
theorem secant_def (p : Parameters) (k : ℕ) :
    secant p k = WithLp.ofLp (p.gradient (k + 1) - p.gradient k) := by
  rfl

/-- Helper for eq:polar-physical-step: the explicit source step length for
the original prescribed matrix and multiplier sequences. -/
def prescribedStepLength (p : Parameters) (k : ℕ) : ℝ :=
  (p.matrix k).det * Real.sin (p.angleIncrement k) /
    (p.zeta k * p.matrix k 0 1 * p.radiusRatio k)

/-- Helper for eq:polar-physical-step: the public scalar formula for the
explicit prescribed step length. -/
theorem prescribedStepLength_def (p : Parameters) (k : ℕ) :
    prescribedStepLength p k = (p.matrix k).det * Real.sin (p.angleIncrement k) /
      (p.zeta k * p.matrix k 0 1 * p.radiusRatio k) := by
  rfl

/-- Helper for eq:polar-physical-step: the next unreduced angle is the
current angle plus its original prescribed increment. -/
theorem angle_succ (p : Parameters) (k : ℕ) :
    p.angle (k + 1) = p.angle k + p.angleIncrement k := by
  rw [Parameters.angleIncrement_def]
  ring

/-- Helper for eq:polar-physical-step: the physical chord retains the exact
original radii and unreduced angles. -/
theorem chord_polar (p : Parameters) (k : ℕ) :
    chord p k = WithLp.ofLp
      (p.radius (k + 1) • polarUnit (p.angle k + p.angleIncrement k) -
        p.radius k • polarUnit (p.angle k)) := by
  rw [chord_def, Parameters.point_def, Parameters.point_def, angle_succ]

/-- Helper for eq:polar-physical-step: the physical secant retains the exact
original multipliers, radii, and unreduced angles. -/
theorem secant_polar (p : Parameters) (k : ℕ) :
    secant p k = WithLp.ofLp
      (p.zeta (k + 1) • (p.radius (k + 1) • polarUnit (p.angle k + p.angleIncrement k)) -
        p.zeta k • (p.radius k • polarUnit (p.angle k))) := by
  rw [secant_def, Parameters.gradient_def, Parameters.gradient_def,
    Parameters.point_def, Parameters.point_def, angle_succ]

/-- Helper for eq:polar-physical-step: the exact original radius recurrence
gives the multiplicative balance used by the source chord and secant algebra. -/
theorem radius_balance (p : Parameters) (k : ℕ)
    (hr : p.radius (k + 1) = p.radius k / p.radiusRatio k)
    (hW : p.radiusRatio k ≠ 0) :
    p.radius (k + 1) * radiusRatioOf (p.matrix k) (p.angleIncrement k) = p.radius k := by
  rw [← Parameters.radiusRatio_def, hr, div_mul_cancel₀ _ hW]

/-- Helper for eq:polar-physical-step: the source radial/tangential chord
identity for the actual prescribed point sequence. -/
theorem prescribed_chord_in_frame (p : Parameters) (k : ℕ)
    (hr : p.radius (k + 1) = p.radius k / p.radiusRatio k) (hW : p.radiusRatio k ≠ 0) :
    (rotationMatrix (p.angle k)).transpose *ᵥ chord p k =
      (p.radius (k + 1) * Real.sin (p.angleIncrement k)) • p.stepV k := by
  rw [chord_polar, Parameters.stepV_def]
  exact chord_in_frame _ _ _ _ _ (radius_balance p k hr hW)

/-- Helper for eq:polar-physical-step: the source radial/tangential secant
identity for the actual prescribed gradient sequence. -/
theorem prescribed_secant_in_frame (p : Parameters) (k : ℕ)
    (hstart : 0 < p.startIndex)
    (hr : p.radius (k + 1) = p.radius k / p.radiusRatio k) (hW : p.radiusRatio k ≠ 0) :
    (rotationMatrix (p.angle k)).transpose *ᵥ secant p k =
      (p.radius (k + 1) * Real.sin (p.angleIncrement k)) • p.stepW k := by
  rw [secant_polar, Parameters.stepW_def]
  exact secant_in_frame _ _ _ _ _ _ _ (radius_balance p k hr hW)
    (ne_of_gt (angleIncrement_sin_pos p hstart k))

/-- Helper for eq:polar-physical-step: the actual inverse Hessian is positive
definite whenever its original local matrix is positive definite. -/
theorem prescribed_inverseHessian_posDef (p : Parameters) (k : ℕ)
    (hZ : (p.matrix k).PosDef) : (p.inverseHessian k).PosDef := by
  rw [Parameters.inverseHessian_def]
  exact conjugate_posDef _ _ (rotation_orthogonal _) hZ.inv

/-- Helper for eq:polar-physical-step: the explicit original step length is
positive under the previously established matrix and radius-factor feasibility. -/
theorem prescribedStepLength_pos (p : Parameters) (k : ℕ) (hstart : 0 < p.startIndex)
    (hZ : (p.matrix k).PosDef) (hC : 0 < p.matrix k 0 1) (hW : 0 < p.radiusRatio k) :
    0 < prescribedStepLength p k := by
  rw [prescribedStepLength_def, Parameters.radiusRatio_def]
  rw [Parameters.radiusRatio_def] at hW
  exact stepLength_pos _ _ _ hZ hC (zeta_pos p k) (angleIncrement_sin_pos p hstart k) hW

/-- Helper for eq:polar-physical-step: the original inverse Hessian and
explicit step length generate the exact original chord. -/
theorem prescribed_search_step (p : Parameters) (k : ℕ)
    (hZ : (p.matrix k).PosDef) (hC : 0 < p.matrix k 0 1) (hW : 0 < p.radiusRatio k)
    (hr : p.radius (k + 1) = p.radius k / p.radiusRatio k) :
    chord p k = (-prescribedStepLength p k) •
      (p.inverseHessian k *ᵥ WithLp.ofLp (p.gradient k)) := by
  have hWof : 0 < radiusRatioOf (p.matrix k) (p.angleIncrement k) := by
    simpa only [Parameters.radiusRatio_def] using hW
  rw [chord_polar, prescribedStepLength_def, Parameters.inverseHessian_def,
    Parameters.gradient_def, Parameters.point_def, Parameters.radiusRatio_def]
  exact search_step _ _ _ _ _ _ (radius_balance p k hr (ne_of_gt hW)) hZ.isHermitian
    (ne_of_gt hC) (ne_of_gt hZ.det_pos) (ne_of_gt (zeta_pos p k)) (ne_of_gt hWof)

/-- Helper for eq:polar-physical-step: the exact physical pairing formula
uses the original prescribed local secant scalar. -/
theorem prescribed_secant_pairing (p : Parameters) (k : ℕ) (hstart : 0 < p.startIndex)
    (hr : p.radius (k + 1) = p.radius k / p.radiusRatio k) (hW : p.radiusRatio k ≠ 0) :
    chord p k ⬝ᵥ secant p k =
      (p.radius (k + 1) * Real.sin (p.angleIncrement k)) ^ 2 * p.sigma k := by
  rw [chord_polar, secant_polar, Parameters.sigma_def]
  exact secant_pairing _ _ _ _ _ _ _ (radius_balance p k hr hW)
    (ne_of_gt (angleIncrement_sin_pos p hstart k))

/-- Helper for eq:polar-physical-step: the original physical secant curvature
is strictly positive under source radius and local feasibility. -/
theorem prescribed_secant_pairing_pos (p : Parameters) (k : ℕ) (hstart : 0 < p.startIndex)
    (hr : p.radius (k + 1) = p.radius k / p.radiusRatio k) (hW : 0 < p.radiusRatio k)
    (hrNext : 0 < p.radius (k + 1)) (hσ : 0 < p.sigma k) :
    0 < chord p k ⬝ᵥ secant p k := by
  rw [prescribed_secant_pairing p k hstart hr (ne_of_gt hW)]
  exact mul_pos (sq_pos_of_pos (mul_pos hrNext (angleIncrement_sin_pos p hstart k))) hσ

/-- Helper for eq:polar-physical-step: the exact original matrix recurrence,
points, gradients, and radii satisfy the physical inverse DFP update. -/
theorem prescribed_inverseDFPUpdate (p : Parameters) (k : ℕ) (hstart : 0 < p.startIndex)
    (hr : p.radius (k + 1) = p.radius k / p.radiusRatio k)
    (hZ : (p.matrix k).PosDef) (hW : 0 < p.radiusRatio k)
    (hrNext : 0 < p.radius (k + 1)) (hσ : 0 < p.sigma k) :
    p.inverseHessian (k + 1) = Matrix.inverseDFPUpdate (p.inverseHessian k) (chord p k)
      (secant p k) := by
  have hσof : 0 < sigmaOf (p.matrix k) (p.angleIncrement k) (p.zeta k) (p.zeta (k + 1)) := by
    simpa only [Parameters.sigma_def] using hσ
  rw [Parameters.inverseHessian_def, Parameters.matrix_succ, angle_succ,
    Parameters.inverseHessian_def, chord_polar, secant_polar]
  exact physicalInverseHessian_step _ _ _ _ _ _ _ (radius_balance p k hr (ne_of_gt hW))
    hZ hrNext (angleIncrement_sin_pos p hstart k) hσof

/-- Helper for eq:polar-physical-step: the exact physical inverse-Hessian
search direction for the original prescribed gradient. -/
theorem prescribed_inverseHessian_mul_gradient (p : Parameters) (k : ℕ)
    (hZ : (p.matrix k).PosDef) (hC : 0 < p.matrix k 0 1) :
    p.inverseHessian k *ᵥ WithLp.ofLp (p.gradient k) =
      (-(p.zeta k * p.radius k * p.matrix k 0 1 / (p.matrix k).det)) •
        (rotationMatrix (p.angle k) *ᵥ p.stepV k) := by
  rw [Parameters.inverseHessian_def, Parameters.gradient_def, Parameters.point_def,
    Parameters.stepV_def]
  exact inverseHessian_mul_gradient _ _ _ _ hZ.isHermitian (ne_of_gt hC) (ne_of_gt hZ.det_pos)

/-- Helper for eq:polar-physical-step: the original data realize one positive
inverse-DFP search step, with the explicit source step length. -/
structure RealizesStep (p : Parameters) (k : ℕ) : Prop where
  /-- Helper for eq:polar-physical-step: the inverse Hessian is positive definite. -/
  inverseHessian_posDef : (p.inverseHessian k).PosDef
  /-- Helper for eq:polar-physical-step: the explicit step length is positive. -/
  stepLength_pos : 0 < prescribedStepLength p k
  /-- Helper for eq:polar-physical-step: the physical chord is the search step. -/
  search : chord p k = (-prescribedStepLength p k) •
    (p.inverseHessian k *ᵥ WithLp.ofLp (p.gradient k))
  /-- Helper for eq:polar-physical-step: the physical secant has positive curvature. -/
  curvature_pos : 0 < chord p k ⬝ᵥ secant p k
  /-- Helper for eq:polar-physical-step: the next original inverse Hessian is the DFP update. -/
  inverseDFPUpdate : p.inverseHessian (k + 1) =
    Matrix.inverseDFPUpdate (p.inverseHessian k) (chord p k) (secant p k)

/-- Helper for eq:polar-physical-step: previously established local feasibility
and the exact original radius recurrence imply physical realization at one step. -/
theorem realizesStep_of_radiusRecurrence (p : Parameters) (k : ℕ)
    (hstart : 0 < p.startIndex) (hZ : (p.matrix k).PosDef)
    (hC : 0 < p.matrix k 0 1) (hσ : 0 < p.sigma k) (hW : 0 < p.radiusRatio k)
    (hrNext : 0 < p.radius (k + 1))
    (hr : p.radius (k + 1) = p.radius k / p.radiusRatio k) : RealizesStep p k := by
  constructor
  · exact prescribed_inverseHessian_posDef p k hZ
  · exact prescribedStepLength_pos p k hstart hZ hC hW
  · exact prescribed_search_step p k hZ hC hW hr
  · exact prescribed_secant_pairing_pos p k hstart hr hW hrNext hσ
  · exact prescribed_inverseDFPUpdate p k hstart hr hZ hW hrNext hσ

/-- Helper for eq:polar-physical-step: Continuation supplies all matrix and
angle hypotheses uniformly before the choice of starting index; only the
separate original-radius interface remains in this integration adapter. -/
theorem uniformRealization_of_radiusRecurrence :
    ∃ η > 0, ∀ νStar ∈ Set.Ioo baseAngle (baseAngle + η),
      ∃ J : ℕ, 0 < J ∧ ∀ j₀ ≥ J,
        (∀ k, 0 < (Parameters.of j₀ νStar).radius k) →
        (∀ k, (Parameters.of j₀ νStar).radius (k + 1) =
          (Parameters.of j₀ νStar).radius k / (Parameters.of j₀ νStar).radiusRatio k) →
        ∀ k, RealizesStep (Parameters.of j₀ νStar) k := by
  obtain ⟨η, hη, hcontinuation⟩ := Continuation.polarContinuation
  refine ⟨η, hη, ?_⟩
  intro νStar hνStar
  obtain ⟨_, N, _, M, _, J, hJ, htrajectory⟩ := hcontinuation νStar hνStar
  refine ⟨J, hJ, ?_⟩
  intro j₀ hj₀ hrPos hrSucc k
  have hstart : 0 < (Parameters.of j₀ νStar).startIndex := by
    simpa only [Parameters.of_startIndex] using hJ.trans_le hj₀
  obtain ⟨hZ, hC, hσ, hW⟩ := (htrajectory j₀ hj₀).2 k
  exact realizesStep_of_radiusRecurrence _ k hstart hZ hC hσ hW (hrPos (k + 1)) (hrSucc k)

/-- Helper for eq:polar-physical-step: the prescribed even gradients have
zero correction relative to the quadratic gradient. -/
theorem gradient_correction_even (p : Parameters) (j : ℕ) :
    p.gradient (2 * j) - p.point (2 * j) = 0 := by
  rw [Parameters.gradient_def, Parameters.zeta_even, one_smul, sub_self]

/-- Helper for eq:polar-physical-step: the prescribed odd gradient correction
is exactly the radial multiplier error times the original point. -/
theorem gradient_correction_odd (p : Parameters) (j : ℕ) :
    p.gradient (2 * j + 1) - p.point (2 * j + 1) =
      (p.zeta (2 * j + 1) - 1) • p.point (2 * j + 1) := by
  rw [Parameters.gradient_def, sub_smul, one_smul]

/-- Helper for eq:polar-physical-step: the original unreduced polar vector
has Euclidean norm exactly one. -/
theorem polarUnit_norm (θ : ℝ) : ‖polarUnit θ‖ = 1 := by
  have hnorm := EuclideanSpace.real_norm_sq_eq (polarUnit θ)
  simp only [Fin.sum_univ_two, polarUnit_apply_zero, polarUnit_apply_one,
    Real.cos_sq_add_sin_sq] at hnorm
  nlinarith [norm_nonneg (polarUnit θ)]

/-- Helper for eq:polar-physical-step: the original point norm is its
positive radius, without changing the tail-product construction. -/
theorem point_norm (p : Parameters) (k : ℕ) (hr : 0 ≤ p.radius k) :
    ‖p.point k‖ = p.radius k := by
  rw [Parameters.point_def, norm_smul, polarUnit_norm, Real.norm_eq_abs, abs_of_nonneg hr,
    mul_one]

/-- Helper for eq:polar-physical-step: the original radial gradient norm is
exactly its positive multiplier times its radius. -/
theorem gradient_norm (p : Parameters) (k : ℕ) (hr : 0 ≤ p.radius k) :
    ‖p.gradient k‖ = p.zeta k * p.radius k := by
  rw [Parameters.gradient_def, norm_smul, point_norm p k hr, Real.norm_eq_abs,
    abs_of_pos (zeta_pos p k)]

/-- Helper for eq:polar-physical-step: a positive original radius gives a
nonzero physical gradient in standard coordinates. -/
theorem gradient_ne_zero (p : Parameters) (k : ℕ) (hr : 0 < p.radius k) :
    WithLp.ofLp (p.gradient k) ≠ 0 := by
  have hnorm : 0 < ‖p.gradient k‖ := by
    rw [gradient_norm p k hr.le]
    exact mul_pos (zeta_pos p k) hr
  intro hzero
  have hg : p.gradient k = 0 := (WithLp.ofLp_injective 2) hzero
  exact (norm_pos_iff.mp hnorm) hg

/-- Helper for eq:polar-physical-step: a realized physical step satisfies
the exact physical secant equation. -/
theorem RealizesStep.secant_equation (p : Parameters) (k : ℕ) (h : RealizesStep p k) :
    p.inverseHessian (k + 1) *ᵥ secant p k = chord p k := by
  have hq := h.inverseHessian_posDef.inverseDFPUpdate_denominator_pos h.curvature_pos
  rw [h.inverseDFPUpdate]
  exact Matrix.inverseDFPUpdate_mulVec_secant (ne_of_gt hq) (ne_of_gt h.curvature_pos)

/-- Helper for eq:polar-physical-step: the realized search step is a strict
descent direction for its nonzero original radial gradient. -/
theorem RealizesStep.descent (p : Parameters) (k : ℕ) (h : RealizesStep p k)
    (hr : 0 < p.radius k) :
    WithLp.ofLp (p.gradient k) ⬝ᵥ chord p k < 0 := by
  have hq := h.inverseHessian_posDef.dotProduct_mulVec_pos (gradient_ne_zero p k hr)
  rw [h.search, dotProduct_smul]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos h.stepLength_pos) hq

/-- Helper for eq:polar-physical-step: rotating the actual original matrix
recurrence gives the factored physical Hessian update before inversion. -/
theorem prescribed_hessian_step (p : Parameters) (k : ℕ) (hstart : 0 < p.startIndex)
    (hr : p.radius (k + 1) = p.radius k / p.radiusRatio k)
    (hW : p.radiusRatio k ≠ 0) (hrNext : p.radius (k + 1) ≠ 0) :
    rotationMatrix (p.angle (k + 1)) * p.matrix (k + 1) *
        (rotationMatrix (p.angle (k + 1))).transpose =
      factoredHessianStep
        (rotationMatrix (p.angle k) * p.matrix k * (rotationMatrix (p.angle k)).transpose)
        (chord p k) (secant p k) := by
  rw [Parameters.matrix_succ, angle_succ, chord_polar, secant_polar]
  exact physicalHessian_step _ _ _ _ _ _ _ (radius_balance p k hr hW) hrNext
    (ne_of_gt (angleIncrement_sin_pos p hstart k))

/-- Helper for eq:polar-physical-step: positive consecutive original radii
and their exact quotient recurrence force the original radius factor to be positive. -/
theorem radiusRatio_pos_of_radiusRecurrence (p : Parameters) (k : ℕ)
    (hrCurrent : 0 < p.radius k) (hrNext : 0 < p.radius (k + 1))
    (hr : p.radius (k + 1) = p.radius k / p.radiusRatio k) : 0 < p.radiusRatio k := by
  apply (div_pos_iff_of_pos_left hrCurrent).mp
  rw [← hr]
  exact hrNext

/-- Helper for eq:polar-physical-step: the complete physical frame and
curvature identities require only positive consecutive original radii and
their exact source recurrence. -/
theorem physicalIdentities_of_radiusRecurrence (p : Parameters) (k : ℕ)
    (hstart : 0 < p.startIndex) (hrCurrent : 0 < p.radius k)
    (hrNext : 0 < p.radius (k + 1))
    (hr : p.radius (k + 1) = p.radius k / p.radiusRatio k) :
    (rotationMatrix (p.angle k)).transpose *ᵥ chord p k =
        (p.radius (k + 1) * Real.sin (p.angleIncrement k)) • p.stepV k ∧
      (rotationMatrix (p.angle k)).transpose *ᵥ secant p k =
        (p.radius (k + 1) * Real.sin (p.angleIncrement k)) • p.stepW k ∧
      chord p k ⬝ᵥ secant p k =
        (p.radius (k + 1) * Real.sin (p.angleIncrement k)) ^ 2 * p.sigma k := by
  have hW := radiusRatio_pos_of_radiusRecurrence p k hrCurrent hrNext hr
  exact ⟨prescribed_chord_in_frame p k hr (ne_of_gt hW),
    prescribed_secant_in_frame p k hstart hr (ne_of_gt hW),
    prescribed_secant_pairing p k hstart hr (ne_of_gt hW)⟩

/-- eq:polar-physical-step and physical DFP realization: for the original
prescribed point, gradient, radius, and inverse-Hessian sequences, every step
is a positive inverse-DFP search step and satisfies both exact source frame
identities and the exact physical curvature formula. The parameter interval
and natural threshold precede every subsequent initialized starting index. -/
theorem polarPhysicalRealization :
    ∃ η > 0, ∀ νStar ∈ Set.Ioo baseAngle (baseAngle + η),
      ∃ J : ℕ, 0 < J ∧ ∀ j₀ ≥ J,
        let p := Parameters.of j₀ νStar
        ∀ k, RealizesStep p k ∧
          (rotationMatrix (p.angle k)).transpose *ᵥ chord p k =
            (p.radius (k + 1) * Real.sin (p.angleIncrement k)) • p.stepV k ∧
          (rotationMatrix (p.angle k)).transpose *ᵥ secant p k =
            (p.radius (k + 1) * Real.sin (p.angleIncrement k)) • p.stepW k ∧
          chord p k ⬝ᵥ secant p k =
            (p.radius (k + 1) * Real.sin (p.angleIncrement k)) ^ 2 * p.sigma k := by
  obtain ⟨ηs, hηs, hsteps⟩ := uniformRealization_of_radiusRecurrence
  obtain ⟨ηr, hηr, hradii⟩ := RadiusProducts.polarRadiusProducts
  refine ⟨min ηs ηr, lt_min hηs hηr, ?_⟩
  intro νStar hnear
  have hnearSteps : νStar ∈ Set.Ioo baseAngle (baseAngle + ηs) :=
    ⟨hnear.1, hnear.2.trans_le (add_le_add le_rfl (min_le_left ηs ηr))⟩
  have hnearRadii : νStar ∈ Set.Ioo baseAngle (baseAngle + ηr) :=
    ⟨hnear.1, hnear.2.trans_le (add_le_add le_rfl (min_le_right ηs ηr))⟩
  obtain ⟨Js, hJs, hstep⟩ := hsteps νStar hnearSteps
  obtain ⟨_, K, _, c, _, B, _, Jr, hJr, hradius⟩ := hradii νStar hnearRadii
  refine ⟨max Js Jr, hJs.trans_le (le_max_left _ _), ?_⟩
  intro j₀ hj₀
  dsimp only
  let p := Parameters.of j₀ νStar
  have hjSteps : Js ≤ j₀ := (le_max_left Js Jr).trans hj₀
  have hjRadii : Jr ≤ j₀ := (le_max_right Js Jr).trans hj₀
  have hstart : 0 < p.startIndex := by
    simpa only [p, Parameters.of_startIndex] using hJs.trans_le hjSteps
  have hR := hradius j₀ hjRadii
  have hrPos : ∀ k, 0 < p.radius k := fun k ↦ zero_lt_one.trans (hR.above_one k)
  have hrealizes := hstep j₀ hjSteps hrPos hR.recurrence
  intro k
  exact ⟨hrealizes k, physicalIdentities_of_radiusRecurrence p k hstart
    (hrPos k) (hrPos (k + 1)) (hR.recurrence k)⟩

end DFP.Polar.PhysicalRealization
