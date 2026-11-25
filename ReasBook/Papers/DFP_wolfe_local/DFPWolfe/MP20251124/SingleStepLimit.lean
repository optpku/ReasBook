/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Optimization.DFP.Polar.General.Normalized

public section
noncomputable section

open Filter
open scoped Matrix Topology

namespace DFPWolfe.MP20251124.SingleStepLimit

open DFP.Polar.General

/-- Helper for lem:fixed-single-limit: the symmetric matrix represented by a coordinate triple. -/
def stateMatrix (x : ℝ × ℝ × ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  RealSymmetric2.matrix x.1 x.2.1 x.2.2

/-- Helper for lem:fixed-single-limit: undoing the diagonal scaling of a fixed matrix. -/
def rawMatrix (x : ℝ × ℝ × ℝ) (τ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  RealSymmetric2.matrix (x.1 / τ ^ 2) (x.2.1 / τ) x.2.2

/-- Helper for lem:fixed-single-limit: the raw matrix is exactly the inverse-scale congruence. -/
theorem rawMatrix_eq_congruence (x : ℝ × ℝ × ℝ) (τ : ℝ) :
    rawMatrix x τ = Normalized.invScaleMatrix τ * stateMatrix x *
      Normalized.invScaleMatrix τ := by
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals simp [rawMatrix, stateMatrix, RealSymmetric2.matrix_eq,
    Normalized.invScaleMatrix_def, Matrix.mul_apply, Fin.sum_univ_two, div_eq_mul_inv]
  all_goals ring

/-- Helper for lem:fixed-single-limit: positive-scale normalization recovers the fixed input. -/
theorem coordinates_rawMatrix (x : ℝ × ℝ × ℝ) {τ : ℝ} (hτ : 0 < τ) :
    Normalized.coordinates τ (rawMatrix x τ) = x := by
  simp only [Normalized.coordinates_apply, rawMatrix, RealSymmetric2.matrix_eq,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [mul_div_cancel₀ _ (pow_ne_zero 2 hτ.ne'), mul_div_cancel₀ _ hτ.ne']

/-- Helper for lem:fixed-single-limit: the normalized secant scalar has value one at the base. -/
theorem stageSigma_zero (a : ℝ) (x : ℝ × ℝ × ℝ) :
    Normalized.stageSigma a 0 x 1 1 = 1 := by
  simp [Normalized.stageSigma_def, Normalized.stepV_def, Normalized.stepW_def,
    dotProduct, Fin.sum_univ_two]

/-- Helper for lem:fixed-single-limit: joint analyticity is used only for the stage map,
not for the subsequently supplied multiplier paths. -/
theorem stage_joint_analyticAt (a : ℝ) (x : ℝ × ℝ × ℝ)
    (ha : a ≠ 0) (hC : x.2.1 ≠ 0) :
    AnalyticAt ℝ (fun z : ℝ × ℝ × ℝ ↦ Normalized.stage a z.1 x z.2.1 z.2.2)
      (0, 1, 1) := by
  have hσ : Normalized.stageSigma a 0 x 1 1 ≠ 0 := (stageSigma_zero a x).trans_ne one_ne_zero
  exact Normalized.stageAlong_analyticAt analyticAt_const analyticAt_fst
    analyticAt_const (analyticAt_fst.comp analyticAt_snd)
    (analyticAt_snd.comp analyticAt_snd) ha rfl hC hσ

/-- Helper for lem:fixed-single-limit: arbitrary convergent multiplier paths give the
coordinate limit, without derivative or rate assumptions on those paths. -/
theorem stage_tendsto (a : ℝ) (x : ℝ × ℝ × ℝ) (ha : a ≠ 0)
    (hC : x.2.1 ≠ 0) {ζ η : ℝ → ℝ}
    (hζ : Tendsto ζ (𝓝[>] 0) (𝓝 1)) (hη : Tendsto η (𝓝[>] 0) (𝓝 1)) :
    Tendsto (fun τ ↦ Normalized.stage a τ x (ζ τ) (η τ)) (𝓝[>] 0)
      (𝓝 (Normalized.leadingStage a x)) := by
  have hinput : Tendsto (fun τ : ℝ ↦ τ) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hpath : Tendsto (fun τ : ℝ ↦ (τ, ζ τ, η τ)) (𝓝[>] 0) (𝓝 (0, 1, 1)) :=
    hinput.prodMk_nhds (hζ.prodMk_nhds hη)
  simpa only [Function.comp_def, Normalized.stage_zero] using
    (stage_joint_analyticAt a x ha hC).continuousAt.tendsto.comp hpath

/-- Helper for lem:fixed-single-limit: the canceled cotangent factor tends to `1 / a`. -/
theorem cotFactor_tendsto (a : ℝ) (ha : a ≠ 0) :
    Tendsto (fun τ ↦ Normalized.cotFactor a τ) (𝓝[>] 0) (𝓝 (1 / a)) := by
  have ht : Tendsto (fun τ : ℝ ↦ τ) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hang : Tendsto (fun τ : ℝ ↦ a * τ) (𝓝[>] 0) (𝓝 0) := by
    simpa using tendsto_const_nhds.mul ht
  have hsinc := Normalized.analyticAt_sinc_zero.continuousAt.tendsto.comp hang
  have hcos := Real.continuous_cos.continuousAt.tendsto.comp hang
  have hsin : Tendsto (fun τ ↦ Normalized.sinFactor a τ) (𝓝[>] 0) (𝓝 a) := by
    simp only [Normalized.sinFactor_def, Normalized.stageAngle_def]
    simpa using hsinc.const_mul a
  simp only [Normalized.cotFactor_def, Normalized.stageAngle_def]
  simpa only [Function.comp_def, Pi.div_def, Real.cos_zero] using hcos.div hsin ha

/-- Helper for lem:fixed-single-limit: the secant scalar tends to one along arbitrary
multiplier paths tending to one. -/
theorem stageSigma_tendsto (a : ℝ) (x : ℝ × ℝ × ℝ) (ha : a ≠ 0)
    {ζ η : ℝ → ℝ} (hζ : Tendsto ζ (𝓝[>] 0) (𝓝 1))
    (hη : Tendsto η (𝓝[>] 0) (𝓝 1)) :
    Tendsto (fun τ ↦ Normalized.stageSigma a τ x (ζ τ) (η τ))
      (𝓝[>] 0) (𝓝 1) := by
  have ht : Tendsto (fun τ : ℝ ↦ τ) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hfirst := ((hη.sub hζ).mul (cotFactor_tendsto a ha)).sub
    ((hζ.mul (ht.pow 2)).mul_const (Normalized.slope x))
  have hscalar := (hfirst.const_mul (-Normalized.slope x)).add hη
  simpa [Normalized.stageSigma_def, Normalized.stepV_def, Normalized.stepW_def,
    dotProduct, Fin.sum_univ_two] using hscalar

/-- Helper for lem:fixed-single-limit: a symmetric stage is recovered from its three entries. -/
theorem stageMatrix_eq_stateMatrix (a τ : ℝ) (x : ℝ × ℝ × ℝ) (ζ η : ℝ) :
    Normalized.stageMatrix a τ x ζ η = stateMatrix (Normalized.stage a τ x ζ η) := by
  have h := Normalized.stageMatrix_isHermitian a τ x ζ η
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals simp [stateMatrix, Normalized.stage_apply, RealSymmetric2.matrix_eq]
  simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ ↦ M 0 1) h

/-- Helper for lem:fixed-single-limit: reconstruction of symmetric matrices is continuous. -/
theorem continuous_stateMatrix : Continuous stateMatrix := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i
  all_goals fin_cases j
  all_goals simp only [stateMatrix, RealSymmetric2.matrix_eq]
  · exact continuous_fst
  · exact continuous_fst.comp continuous_snd
  · exact continuous_fst.comp continuous_snd
  · exact continuous_snd.comp continuous_snd

/-- Helper for lem:fixed-single-limit: the canceled stage equals the scaled raw DFP update. -/
theorem scaledRawUpdate_eq_stageMatrix (a : ℝ) (x : ℝ × ℝ × ℝ)
    {τ : ℝ} (hτ : 0 < τ) (ζ η : ℝ) :
    Normalized.scaleMatrix τ * DFP.Polar.matrixStep (rawMatrix x τ) (a * τ) ζ η *
        Normalized.scaleMatrix τ = Normalized.stageMatrix a τ x ζ η := by
  have hraw := RealSymmetric2.matrix_isHermitian (x.1 / τ ^ 2) (x.2.1 / τ) x.2.2
  have h := Normalized.stageMatrix_eq_scaleMatrix_mul a τ (rawMatrix x τ) ζ η hraw hτ
  rw [coordinates_rawMatrix x hτ, Normalized.stageAngle_def] at h
  exact h.symm

/-- Helper for lem:fixed-single-limit: the limiting matrix has determinant equal to
its preserved first diagonal entry. -/
theorem limitMatrix_det (A q : ℝ) :
    (RealSymmetric2.matrix A (A * q) (1 + A * q ^ 2)).det = A := by
  simp [RealSymmetric2.matrix_eq, Matrix.det_fin_two]
  ring

/-- Helper for lem:fixed-single-limit: the limiting quadratic form is a sum of squares. -/
theorem limitMatrix_quadratic (A q : ℝ) (v : Fin 2 → ℝ) :
    star v ⬝ᵥ (RealSymmetric2.matrix A (A * q) (1 + A * q ^ 2) *ᵥ v) =
      A * (v 0 + q * v 1) ^ 2 + (v 1) ^ 2 := by
  simp [RealSymmetric2.matrix_eq, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

/-- Helper for lem:fixed-single-limit: a positive first diagonal entry makes the
limiting matrix positive definite. -/
theorem limitMatrix_posDef {A : ℝ} (hA : 0 < A) (q : ℝ) :
    (RealSymmetric2.matrix A (A * q) (1 + A * q ^ 2)).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨RealSymmetric2.matrix_isHermitian _ _ _, ?_⟩
  intro v hv
  rw [limitMatrix_quadratic]
  by_cases h1 : v 1 = 0
  · have h0 : v 0 ≠ 0 := by
      intro hz
      apply hv
      ext i
      fin_cases i
      · exact hz
      · exact h1
    simpa [h1] using
      mul_pos hA (sq_pos_of_ne_zero h0)
  · exact add_pos_of_nonneg_of_pos (mul_nonneg hA.le (sq_nonneg _))
      (sq_pos_of_ne_zero h1)

/-- Helper for lem:fixed-single-limit: for every positive definite symmetric input with positive
off-diagonal entry and every positive angular coefficient, arbitrary multiplier paths
tending to one have an eventually positive raw secant scalar and the stated scaled
raw-update limit. The limiting matrix is positive definite and has determinant `x.1`. -/
theorem singleStepLimit (a : ℝ) (x : ℝ × ℝ × ℝ) (ha : 0 < a)
    (hX : (stateMatrix x).PosDef) (hC : 0 < x.2.1) {ζ η : ℝ → ℝ}
    (hζ : Tendsto ζ (𝓝[>] 0) (𝓝 1)) (hη : Tendsto η (𝓝[>] 0) (𝓝 1)) :
    (∀ᶠ τ in 𝓝[>] 0,
      0 < DFP.Polar.sigmaOf (rawMatrix x τ) (a * τ) (ζ τ) (η τ)) ∧
    Tendsto (fun τ ↦ Normalized.scaleMatrix τ *
      DFP.Polar.matrixStep (rawMatrix x τ) (a * τ) (ζ τ) (η τ) *
        Normalized.scaleMatrix τ) (𝓝[>] 0)
      (𝓝 (RealSymmetric2.matrix x.1 (x.1 * (x.2.2 / x.2.1 - a))
        (1 + x.1 * (x.2.2 / x.2.1 - a) ^ 2))) ∧
    (RealSymmetric2.matrix x.1 (x.1 * (x.2.2 / x.2.1 - a))
      (1 + x.1 * (x.2.2 / x.2.1 - a) ^ 2)).PosDef ∧
    (RealSymmetric2.matrix x.1 (x.1 * (x.2.2 / x.2.1 - a))
      (1 + x.1 * (x.2.2 / x.2.1 - a) ^ 2)).det = x.1 := by
  have hpositive := (stageSigma_tendsto a x ha.ne' hζ hη).eventually
    (eventually_gt_nhds zero_lt_one)
  have hrawPositive : ∀ᶠ τ in 𝓝[>] 0,
      0 < DFP.Polar.sigmaOf (rawMatrix x τ) (a * τ) (ζ τ) (η τ) := by
    filter_upwards [self_mem_nhdsWithin, hpositive] with τ hτ hσ
    have hid := Normalized.stageSigma_eq_sigmaOf a τ (rawMatrix x τ) (ζ τ) (η τ) hτ
    rw [coordinates_rawMatrix x hτ, Normalized.stageAngle_def] at hid
    rwa [← hid]
  have hmatrix := continuous_stateMatrix.continuousAt.tendsto.comp
    (stage_tendsto a x ha.ne' hC.ne' hζ hη)
  have heq : (fun τ ↦ Normalized.scaleMatrix τ *
      DFP.Polar.matrixStep (rawMatrix x τ) (a * τ) (ζ τ) (η τ) *
        Normalized.scaleMatrix τ) =ᶠ[𝓝[>] 0]
      (fun τ ↦ stateMatrix (Normalized.stage a τ x (ζ τ) (η τ))) := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    rw [scaledRawUpdate_eq_stageMatrix a x hτ, stageMatrix_eq_stateMatrix]
  have hlimit := hmatrix.congr' heq.symm
  have hA : 0 < x.1 := by
    simpa [stateMatrix, RealSymmetric2.matrix_eq] using hX.diag_pos (i := 0)
  have hpd := limitMatrix_posDef hA (x.2.2 / x.2.1 - a)
  have hdet := limitMatrix_det x.1 (x.2.2 / x.2.1 - a)
  refine ⟨hrawPositive, ?_, hpd, hdet⟩
  simpa only [Function.comp_def, stateMatrix, Normalized.leadingStage_apply] using hlimit

/-- Helper for lem:fixed-single-limit: the three coordinates represent every real
Hermitian two-by-two matrix, so the coordinate theorem loses no inputs. -/
theorem stateMatrix_entries (X : Matrix (Fin 2) (Fin 2) ℝ) (hX : X.IsHermitian) :
    stateMatrix (X 0 0, X 0 1, X 1 1) = X := by
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals simp [stateMatrix, RealSymmetric2.matrix_eq]
  simpa using (congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ ↦ M 0 1) hX).symm

/-- lem:fixed-single-limit. For an arbitrary positive definite matrix `X` with
`X₀₁ > 0`, the exact raw update of `Sτ⁻¹ X Sτ⁻¹` has eventually positive
secant scalar and converges after scaling to the displayed matrix. Only the right
limits `ζ → 1` and `η → 1` are required; the limit is positive definite with
determinant `X₀₀`. -/
theorem singleStepLimitMatrix (a : ℝ) (X : Matrix (Fin 2) (Fin 2) ℝ)
    (ha : 0 < a) (hX : X.PosDef) (hC : 0 < X 0 1) {ζ η : ℝ → ℝ}
    (hζ : Tendsto ζ (𝓝[>] 0) (𝓝 1)) (hη : Tendsto η (𝓝[>] 0) (𝓝 1)) :
    (∀ᶠ τ in 𝓝[>] 0,
      0 < DFP.Polar.sigmaOf
        (Normalized.invScaleMatrix τ * X * Normalized.invScaleMatrix τ)
        (a * τ) (ζ τ) (η τ)) ∧
    Tendsto (fun τ ↦ Normalized.scaleMatrix τ *
      DFP.Polar.matrixStep
        (Normalized.invScaleMatrix τ * X * Normalized.invScaleMatrix τ)
        (a * τ) (ζ τ) (η τ) * Normalized.scaleMatrix τ) (𝓝[>] 0)
      (𝓝 (RealSymmetric2.matrix (X 0 0) (X 0 0 * (X 1 1 / X 0 1 - a))
        (1 + X 0 0 * (X 1 1 / X 0 1 - a) ^ 2))) ∧
    (RealSymmetric2.matrix (X 0 0) (X 0 0 * (X 1 1 / X 0 1 - a))
      (1 + X 0 0 * (X 1 1 / X 0 1 - a) ^ 2)).PosDef ∧
    (RealSymmetric2.matrix (X 0 0) (X 0 0 * (X 1 1 / X 0 1 - a))
      (1 + X 0 0 * (X 1 1 / X 0 1 - a) ^ 2)).det = X 0 0 := by
  have hcoordinates : (stateMatrix (X 0 0, X 0 1, X 1 1)).PosDef := by
    rw [stateMatrix_entries X hX.isHermitian]
    exact hX
  have h := singleStepLimit a (X 0 0, X 0 1, X 1 1) ha hcoordinates hC hζ hη
  simpa only [rawMatrix_eq_congruence, stateMatrix_entries X hX.isHermitian] using h

end DFPWolfe.MP20251124.SingleStepLimit
