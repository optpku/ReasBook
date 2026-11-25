/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f0dee1064101ffc85a871f8c7f3a997668f5a83b:ReasBook/Papers/DFP_wolfe_local/README.md (Contributors).
-/

module

public import DFPWolfe.V21.CenterManifold
-- The regular coordinate definitions are opaque across this module boundary;
-- their algebraic projection identities are needed for spectral reconstruction.
import all DFPWolfe.V21.CenterManifold

public section

noncomputable section

open scoped Matrix
open DFPWolfe.V21.CenterManifold

namespace DFPWolfe.Latest.CenterDesignRecovery

/-- Helper for cm-alternating-data: the recovered shape and radius reproduce
the removable lower eigenvalue of a general regular step. -/
theorem regularStepLowIdentity (p h r μ τ : ℝ)
    (hL : (regularSpectrum p h r μ).1 ≠ 0)
    (hH : (regularSpectrum p h r μ).2 ≠ 0)
    (hX : (regularRotatedData p h r μ τ).1.1 ≠ 0)
    (hY : (regularRotatedData p h r μ τ).1.2 ≠ 0) :
    (regularStep p h r μ τ).2.2.1 * (regularStep p h r μ τ).2.1 *
        (r * (regularStep p h r μ τ).1) ^ 2 =
      r ^ 2 * (regularSpectrum p h r μ).1 := by
  dsimp only [regularStep]
  field_simp [hL, hH, hX, hY]

/-- Helper for cm-alternating-data: the general recovered gradient coordinates
agree with the rotated gradient numerators. -/
theorem regularStepGradientCoordinates (p h r μ τ : ℝ)
    (hL : (regularSpectrum p h r μ).1 ≠ 0)
    (hH : (regularSpectrum p h r μ).2 ≠ 0)
    (hX : (regularRotatedData p h r μ τ).1.1 ≠ 0)
    (hY : (regularRotatedData p h r μ τ).1.2 ≠ 0) :
    (regularStep p h r μ τ).2.2.2 •
        ![(1 : ℝ), (regularStep p h r μ τ).2.1 *
          (r * (regularStep p h r μ τ).1)] =
      ![(regularRotatedData p h r μ τ).1.1 / (regularRotatedData p h r μ τ).2,
        r * (regularRotatedData p h r μ τ).1.2 /
          (regularRotatedData p h r μ τ).2] := by
  ext i
  fin_cases i
  · simp [regularStep]
  · simp [regularStep]
    field_simp [hL, hH, hX, hY]

/-- Helper for cm-alternating-data: the actual regular metric in its updated
eigenframe is the canonical metric of the recovered shape and radius. -/
theorem regularFrameMetricRecovery (p h r μ τ : ℝ)
    (hD : regularDenominator r μ ≠ 0) (hE : regularEnergy p r μ ≠ 0)
    (hL : (regularSpectrum p h r μ).1 ≠ 0)
    (hH : (regularSpectrum p h r μ).2 ≠ 0)
    (hX : (regularRotatedData p h r μ τ).1.1 ≠ 0)
    (hY : (regularRotatedData p h r μ τ).1.2 ≠ 0)
    (hN : (regularRotatedData p h r μ τ).2 ≠ 0) :
    (regularFrame p h r μ τ).transpose * regularMetric p h r μ *
        regularFrame p h r μ τ =
      Matrix.diagonal ![(regularStep p h r μ τ).2.2.1 *
        (regularStep p h r μ τ).2.1 * (r * (regularStep p h r μ τ).1) ^ 2,
        (regularStep p h r μ τ).2.2.1] := by
  have hhigh : RealSymmetric2.high (regularEntries p h r μ).1
      (r * (regularEntries p h r μ).2.1) (regularEntries p h r μ).2.2 ≠ 0 := hH
  have hden := hN
  rw [regularNormalizer_eq_lowDenom p h r μ τ hD hE hhigh] at hden
  have hmetric : regularMetric p h r μ =
      RealSymmetric2.matrix (regularEntries p h r μ).1
        (r * (regularEntries p h r μ).2.1) (regularEntries p h r μ).2.2 := by
    rw [RealSymmetric2.matrix_eq]
    rfl
  rw [regularFrame_eq_lowEigenframe p h r μ τ hD hE hhigh, hmetric,
    RealSymmetric2.frame_diagonalizes_of_lowDenom_ne_zero _ _ _ hden,
    regularStepLowIdentity p h r μ τ hL hH hX hY,
    regularSpectrum_low p h r μ hD hE hhigh]
  rfl

/-- Helper for cm-alternating-data: the actual regular gradient in its updated
eigenframe has the recovered shape, radius, and amplitude multiplier. -/
theorem regularFrameGradientRecovery (p h r μ τ : ℝ)
    (hL : (regularSpectrum p h r μ).1 ≠ 0)
    (hH : (regularSpectrum p h r μ).2 ≠ 0)
    (hX : (regularRotatedData p h r μ τ).1.1 ≠ 0)
    (hY : (regularRotatedData p h r μ τ).1.2 ≠ 0) :
    (regularFrame p h r μ τ).transpose *ᵥ regularGradient p r μ τ =
      (regularStep p h r μ τ).2.2.2 •
        ![(1 : ℝ), (regularStep p h r μ τ).2.1 *
          (r * (regularStep p h r μ τ).1)] := by
  rw [regularFrame_gradient, regularStepGradientCoordinates p h r μ τ hL hH hX hY]

/-- Helper for cm-alternating-data: an actual DFP step has the recovered
canonical metric in the updated eigenbasis, with no assumed recovery identity. -/
theorem spectralMetricRecovery (z : DFP.AbstractSecantStep (Fin 2))
    (p h r μ G : ℝ)
    (hmetric : z.inverseHessian = Matrix.diagonal ![h * p * r ^ 2, h])
    (hgradient : z.gradient = G • ![(1 : ℝ), p * r])
    (hcontrol : z.secantMatrix = !![1, μ; μ, 1])
    (hD : regularDenominator r μ ≠ 0) (hE : regularEnergy p r μ ≠ 0)
    (hL : (regularSpectrum p h r μ).1 ≠ 0)
    (hH : (regularSpectrum p h r μ).2 ≠ 0)
    (hX : (regularRotatedData p h r μ z.tau).1.1 ≠ 0)
    (hY : (regularRotatedData p h r μ z.tau).1.2 ≠ 0)
    (hN : (regularRotatedData p h r μ z.tau).2 ≠ 0) :
    (regularFrame p h r μ z.tau).transpose * z.nextInverseHessian *
        regularFrame p h r μ z.tau =
      Matrix.diagonal ![(regularStep p h r μ z.tau).2.2.1 *
        (regularStep p h r μ z.tau).2.1 * (r * (regularStep p h r μ z.tau).1) ^ 2,
        (regularStep p h r μ z.tau).2.2.1] := by
  rw [spectralMetricUpdate z p h r μ G hmetric hgradient hcontrol]
  exact regularFrameMetricRecovery p h r μ z.tau hD hE hL hH hX hY hN

/-- Helper for cm-alternating-data: an actual DFP step has the recovered
canonical gradient in the updated eigenbasis and its actual amplitude. -/
theorem spectralGradientRecovery (z : DFP.AbstractSecantStep (Fin 2))
    (p h r μ G : ℝ)
    (hmetric : z.inverseHessian = Matrix.diagonal ![h * p * r ^ 2, h])
    (hgradient : z.gradient = G • ![(1 : ℝ), p * r])
    (hcontrol : z.secantMatrix = !![1, μ; μ, 1])
    (hL : (regularSpectrum p h r μ).1 ≠ 0)
    (hH : (regularSpectrum p h r μ).2 ≠ 0)
    (hX : (regularRotatedData p h r μ z.tau).1.1 ≠ 0)
    (hY : (regularRotatedData p h r μ z.tau).1.2 ≠ 0) :
    (regularFrame p h r μ z.tau).transpose *ᵥ z.nextGradient =
      (G * (regularStep p h r μ z.tau).2.2.2) •
        ![(1 : ℝ), (regularStep p h r μ z.tau).2.1 *
          (r * (regularStep p h r μ z.tau).1)] := by
  rw [spectralGradientUpdate z p h r μ G hmetric hgradient hcontrol,
    Matrix.mulVec_smul, regularFrameGradientRecovery p h r μ z.tau hL hH hX hY,
    smul_smul]

/-- Helper for cm-alternating-data: a symmetric unit-diagonal control is
positive definite when its off-diagonal coefficient has absolute value below one. -/
theorem unitControlPosDef (μ : ℝ) (hμ : |μ| < 1) :
    (!![1, μ; μ, 1] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
  have hsym : (!![1, μ; μ, 1] : Matrix (Fin 2) (Fin 2) ℝ).IsHermitian := by
    rw [← RealSymmetric2.matrix_eq]
    exact RealSymmetric2.matrix_isHermitian 1 μ 1
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hsym
  intro x hx
  have hgap : 0 < 1 - μ ^ 2 := by
    nlinarith [abs_lt.mp hμ, sq_abs μ]
  have hpositive : 0 < (x 0 + μ * x 1) ^ 2 + (1 - μ ^ 2) * (x 1) ^ 2 := by
    by_cases hsecond : x 1 = 0
    · have hfirst : x 0 ≠ 0 := by
        intro hzero
        apply hx
        ext i
        fin_cases i
        · simpa using hzero
        · simpa using hsecond
      simpa [hsecond] using sq_pos_of_ne_zero hfirst
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos hgap (sq_pos_of_ne_zero hsecond))
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at ⊢
  simp at ⊢
  nlinarith

/-- Helper for cm-alternating-data: positive spectral parameters give a
positive definite canonical diagonal metric. -/
theorem canonicalMetricPosDef (p h r : ℝ) (hp : 0 < p) (hh : 0 < h) (hr : 0 < r) :
    (Matrix.diagonal ![h * p * r ^ 2, h] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
  apply Matrix.PosDef.diagonal
  intro i
  fin_cases i
  · dsimp
    exact mul_pos (mul_pos hh hp) (pow_pos hr 2)
  · dsimp
    exact hh

/-- Helper for cm-alternating-data: a canonical gradient with positive
amplitude is nonzero regardless of its shape and radius. -/
theorem canonicalGradientNeZero (p r G : ℝ) (hG : 0 < G) :
    G • ![(1 : ℝ), p * r] ≠ (0 : Fin 2 → ℝ) := by
  apply smul_ne_zero hG.ne'
  intro hz
  have hc := congrArg (fun v : Fin 2 → ℝ ↦ v 0) hz
  norm_num at hc

/-- Helper for cm-alternating-data: the general canonical spectral data define
an actual abstract DFP step with the prescribed control and ratio. -/
def canonicalSpectralStep (p h r μ τ G : ℝ)
    (hp : 0 < p) (hh : 0 < h) (hr : 0 < r) (hG : 0 < G)
    (hμ : |μ| < 1) (hτ : 0 < τ) : DFP.AbstractSecantStep (Fin 2) where
  inverseHessian := Matrix.diagonal ![h * p * r ^ 2, h]
  gradient := G • ![(1 : ℝ), p * r]
  secantMatrix := !![1, μ; μ, 1]
  tau := τ
  inverseHessian_posDef := canonicalMetricPosDef p h r hp hh hr
  secantMatrix_posDef := unitControlPosDef μ hμ
  tau_pos := hτ
  gradient_ne_zero := canonicalGradientNeZero p r G hG

/-- Helper for cm-alternating-data: positive removable first-step factors
produce two actual DFP steps whose intermediate data agree in the updated eigenbasis. -/
theorem existsActualSpectralCycle (p h r μ₁ μ₂ τ₁ τ₂ G : ℝ)
    (hp : 0 < p) (hh : 0 < h) (hr : 0 < r) (hG : 0 < G)
    (hτ₁ : 0 < τ₁) (hτ₂ : 0 < τ₂) (hμ₁ : |μ₁| < 1) (hμ₂ : |μ₂| < 1)
    (hL : 0 < (regularSpectrum p h r μ₁).1)
    (hH : 0 < (regularSpectrum p h r μ₁).2)
    (hX : 0 < (regularRotatedData p h r μ₁ τ₁).1.1)
    (hY : 0 < (regularRotatedData p h r μ₁ τ₁).1.2)
    (hN : 0 < (regularRotatedData p h r μ₁ τ₁).2) :
    ∃ first second : DFP.AbstractSecantStep (Fin 2),
      first.inverseHessian = Matrix.diagonal ![h * p * r ^ 2, h] ∧
      first.gradient = G • ![(1 : ℝ), p * r] ∧
      first.secantMatrix = !![1, μ₁; μ₁, 1] ∧ first.tau = τ₁ ∧
      second.inverseHessian = (regularFrame p h r μ₁ τ₁).transpose *
        first.nextInverseHessian * regularFrame p h r μ₁ τ₁ ∧
      second.gradient = (regularFrame p h r μ₁ τ₁).transpose *ᵥ first.nextGradient ∧
      second.secantMatrix = !![1, μ₂; μ₂, 1] ∧ second.tau = τ₂ := by
  have hD := (regularDenominator_pos r μ₁ hμ₁).ne'
  have hE := (regularEnergy_pos p r μ₁ hp hμ₁).ne'
  have hnextR : 0 < r * (regularStep p h r μ₁ τ₁).1 :=
    mul_pos hr (div_pos (mul_pos hL hX) (mul_pos hH hY))
  have hnextP : 0 < (regularStep p h r μ₁ τ₁).2.1 :=
    div_pos (mul_pos hH (pow_pos hY 2)) (mul_pos hL (pow_pos hX 2))
  have hnextG : 0 < G * (regularStep p h r μ₁ τ₁).2.2.2 :=
    mul_pos hG (div_pos hX hN)
  let first := canonicalSpectralStep p h r μ₁ τ₁ G hp hh hr hG hμ₁ hτ₁
  let second := canonicalSpectralStep (regularStep p h r μ₁ τ₁).2.1
    (regularStep p h r μ₁ τ₁).2.2.1 (r * (regularStep p h r μ₁ τ₁).1) μ₂ τ₂
    (G * (regularStep p h r μ₁ τ₁).2.2.2) hnextP hH hnextR hnextG hμ₂ hτ₂
  have hmetric := spectralMetricRecovery first p h r μ₁ G rfl rfl rfl
    hD hE hL.ne' hH.ne' hX.ne' hY.ne' hN.ne'
  have hgradient := spectralGradientRecovery first p h r μ₁ G rfl rfl rfl
    hL.ne' hH.ne' hX.ne' hY.ne'
  exact ⟨first, second, rfl, rfl, rfl, rfl, hmetric.symm, hgradient.symm, rfl, rfl⟩

end DFPWolfe.Latest.CenterDesignRecovery
