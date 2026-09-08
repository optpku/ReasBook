module

public import ReasLib.Algebra.GroupWithZero.PowerCancellation
public import ReasLib.Optimization.DFP.AbstractSecantStep.Eigenframe
public import ReasLib.Optimization.DFP.InverseUpdate.Determinant
public import ReasLib.Optimization.DFP.SpectralRecovery
public import ReasLib.Optimization.DFP.TwoPhaseControls
public import ReasLib.LinearAlgebra.Matrix.RealSymmetric2.Eigenframe
public import ReasLib.Geometry.Euclidean.Plane.Rotation
import all ReasLib.Geometry.Euclidean.Plane.Rotation
public import ReasLib.Optimization.DFP.SpectralRecovery
import all ReasLib.Optimization.DFP.SpectralRecovery
public import ReasLib.LinearAlgebra.Matrix.RealSymmetric2
import all ReasLib.LinearAlgebra.Matrix.RealSymmetric2

public section

noncomputable section

open Filter
open scoped Matrix Topology

namespace DFP.FirstLeg

/-- The first DFP metric after canceling every common power of `ε` in the entrywise
one-step formulas for the canonical input with radius `ε ^ 2`. -/
def outputMetric (ε p h : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let B := 1 + 2 * ε ^ 3 + ε ^ 4
  let C := (1 + ε ^ 3) ^ 2 + p * ε ^ 6 * (1 + ε) ^ 2
  let a := h * p - h * p ^ 2 * ε ^ 6 * (1 + ε) ^ 2 / C + 1 / B
  let b := 1 / B - h * p * ε ^ 3 * (1 + ε) * (1 + ε ^ 3) / C
  let d := h - h * (1 + ε ^ 3) ^ 2 / C + 1 / B
  !![ε ^ 4 * a, ε ^ 2 * b; ε ^ 2 * b, d]

/-- The canceled first-leg metric is the symmetric matrix determined by its
three independent entries. -/
theorem outputMetric_eq_symmetricMatrix (ε p h : ℝ) :
    outputMetric ε p h =
      RealSymmetric2.matrix (outputMetric ε p h 0 0)
        (outputMetric ε p h 0 1) (outputMetric ε p h 1 1) := by
  unfold outputMetric RealSymmetric2.matrix
  rfl

/-- The first updated gradient divided by its incoming amplitude, with the removable
factor `ε ^ 2` retained explicitly in its second incoming-frame coordinate. -/
def outputGradient (ε p h : ℝ) : Fin 2 → ℝ :=
  let _ := h
  let B := 1 + 2 * ε ^ 3 + ε ^ 4
  let q := 1 - 2 * (p + 1) * ε ^ 3 * (1 + ε) / (3 * B)
  let v := p - 2 * (p + 1) * (1 + ε ^ 3) / (3 * B)
  ![q, ε ^ 2 * v]

/-- Evaluation formula for the normalized gradient after the first DFP leg. -/
theorem outputGradient_apply (ε p h : ℝ) :
    outputGradient ε p h =
      let _ := h
      let B := 1 + 2 * ε ^ 3 + ε ^ 4
      let q := 1 - 2 * (p + 1) * ε ^ 3 * (1 + ε) / (3 * B)
      let v := p - 2 * (p + 1) * (1 + ε ^ 3) / (3 * B)
      ![q, ε ^ 2 * v] := by
  rfl

/-- The fixed analytic, positively oriented eigenframe of the first updated metric. -/
def frame (ε p h : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let H := outputMetric ε p h
  EuclideanPlane.frame (RealSymmetric2.lowVector (H 0 0) (H 0 1) (H 1 1))

/-- The first-leg frame is the canonical low-eigenvector frame of the physical
output metric. -/
theorem frame_eq_lowEigenframe (ε p h : ℝ) :
    frame ε p h =
      EuclideanPlane.frame
        (RealSymmetric2.lowVector (outputMetric ε p h 0 0)
          (outputMetric ε p h 0 1) (outputMetric ε p h 1 1)) := by
  rfl

/-- The low and high eigenvalues of the first updated metric in the fixed analytic branch. -/
def eigenvalues (ε p h : ℝ) : ℝ × ℝ :=
  let H := outputMetric ε p h
  (RealSymmetric2.low (H 0 0) (H 0 1) (H 1 1),
    RealSymmetric2.high (H 0 0) (H 0 1) (H 1 1))

/-- The first-leg eigenvalue pair is the explicit low/high spectrum of the
physical output metric. -/
theorem eigenvalues_eq_lowHigh (ε p h : ℝ) :
    eigenvalues ε p h =
      (RealSymmetric2.low (outputMetric ε p h 0 0)
          (outputMetric ε p h 0 1) (outputMetric ε p h 1 1),
        RealSymmetric2.high (outputMetric ε p h 0 0)
          (outputMetric ε p h 0 1) (outputMetric ε p h 1 1)) := by
  rfl

/-- The fixed-frame coordinates of the normalized first updated gradient. -/
def coordinates (ε p h : ℝ) : ℝ × ℝ :=
  let g := (frame ε p h).transpose *ᵥ outputGradient ε p h
  (g 0, g 1)

/-- The removable low-eigenvalue factor `L₁` and the high eigenvalue `ℋ₁`. -/
def spectralFactors (ε p h : ℝ) : ℝ × ℝ :=
  let B := 1 + 2 * ε ^ 3 + ε ^ 4
  let C := (1 + ε ^ 3) ^ 2 + p * ε ^ 6 * (1 + ε) ^ 2
  let a := h * p - h * p ^ 2 * ε ^ 6 * (1 + ε) ^ 2 / C + 1 / B
  let b := 1 / B - h * p * ε ^ 3 * (1 + ε) * (1 + ε ^ 3) / C
  let d := h - h * (1 + ε ^ 3) ^ 2 / C + 1 / B
  let high := RealSymmetric2.high (ε ^ 4 * a) (ε ^ 2 * b) d
  ((a * d - b ^ 2) / high, high)

/-- Evaluation formula for the removable spectral factors of the first leg. -/
theorem spectralFactors_apply (ε p h : ℝ) :
    spectralFactors ε p h =
      let B := 1 + 2 * ε ^ 3 + ε ^ 4
      let C := (1 + ε ^ 3) ^ 2 + p * ε ^ 6 * (1 + ε) ^ 2
      let a := h * p - h * p ^ 2 * ε ^ 6 * (1 + ε) ^ 2 / C + 1 / B
      let b := 1 / B - h * p * ε ^ 3 * (1 + ε) * (1 + ε ^ 3) / C
      let d := h - h * (1 + ε ^ 3) ^ 2 / C + 1 / B
      let high := RealSymmetric2.high (ε ^ 4 * a) (ε ^ 2 * b) d
      ((a * d - b ^ 2) / high, high) := by
  rfl

/-- The removable oriented-gradient factors `𝒢₁` and `U₁`, obtained by canceling
the factor `ε ^ 2` from the high-frame coordinate before evaluating at `ε = 0`. -/
def gradientFactors (ε p h : ℝ) : ℝ × ℝ :=
  let B := 1 + 2 * ε ^ 3 + ε ^ 4
  let C := (1 + ε ^ 3) ^ 2 + p * ε ^ 6 * (1 + ε) ^ 2
  let a := h * p - h * p ^ 2 * ε ^ 6 * (1 + ε) ^ 2 / C + 1 / B
  let b := 1 / B - h * p * ε ^ 3 * (1 + ε) * (1 + ε ^ 3) / C
  let d := h - h * (1 + ε ^ 3) ^ 2 / C + 1 / B
  let q := 1 - 2 * (p + 1) * ε ^ 3 * (1 + ε) / (3 * B)
  let v := p - 2 * (p + 1) * (1 + ε ^ 3) / (3 * B)
  let low := RealSymmetric2.low (ε ^ 4 * a) (ε ^ 2 * b) d
  let denom := RealSymmetric2.lowDenom (ε ^ 4 * a) (ε ^ 2 * b) d
  (((d - low) * q - ε ^ 4 * b * v) / denom,
    (b * q + (d - low) * v) / denom)

/-- Evaluation formula for the removable oriented-gradient factors of the first leg. -/
theorem gradientFactors_apply (ε p h : ℝ) :
    gradientFactors ε p h =
      let B := 1 + 2 * ε ^ 3 + ε ^ 4
      let C := (1 + ε ^ 3) ^ 2 + p * ε ^ 6 * (1 + ε) ^ 2
      let a := h * p - h * p ^ 2 * ε ^ 6 * (1 + ε) ^ 2 / C + 1 / B
      let b := 1 / B - h * p * ε ^ 3 * (1 + ε) * (1 + ε ^ 3) / C
      let d := h - h * (1 + ε ^ 3) ^ 2 / C + 1 / B
      let q := 1 - 2 * (p + 1) * ε ^ 3 * (1 + ε) / (3 * B)
      let v := p - 2 * (p + 1) * (1 + ε ^ 3) / (3 * B)
      let low := RealSymmetric2.low (ε ^ 4 * a) (ε ^ 2 * b) d
      let denom := RealSymmetric2.lowDenom (ε ^ 4 * a) (ε ^ 2 * b) d
      (((d - low) * q - ε ^ 4 * b * v) / denom,
        (b * q + (d - low) * v) / denom) := by
  rfl

/-- The canonical radius factor `ℛ₁` and recovered shape `p₁` formed from the
removable spectral and gradient factors. -/
def canonicalFactors (ε p h : ℝ) : ℝ × ℝ :=
  let spectral := spectralFactors ε p h
  let gradient := gradientFactors ε p h
  (spectral.1 * gradient.1 / (spectral.2 * gradient.2),
    spectral.2 * gradient.2 ^ 2 / (spectral.1 * gradient.1 ^ 2))

/-- The radius and shape recovered from the actual first-leg spectral and oriented-gradient
coordinates. -/
def recovered (ε p h : ℝ) : ℝ × ℝ :=
  let eigen := eigenvalues ε p h
  let gradient := coordinates ε p h
  (CycleBoundaryState.recoveryRadius eigen.1 eigen.2 gradient.1 gradient.2,
    CycleBoundaryState.recoveryShape eigen.1 eigen.2 gradient.1 gradient.2)

/-- The three pairs of removable first-leg factors: spectral, gradient, and canonical. -/
def factors (ε p h : ℝ) : (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ) :=
  (spectralFactors ε p h, gradientFactors ε p h, canonicalFactors ε p h)

/-- The combined first-leg factor package exposes its spectral, gradient, and
canonical components. -/
theorem factors_apply (ε p h : ℝ) :
    factors ε p h =
      (spectralFactors ε p h, gradientFactors ε p h, canonicalFactors ε p h) := by
  rfl

/-- The preconditioned-gradient energy for the canonical first control has the
displayed residual factor. -/
private lemma preconditionedEnergyFirstControl
    (z : DFP.AbstractSecantStep (Fin 2)) (ε p h G : ℝ)
    (hH : z.inverseHessian = Matrix.diagonal ![h * p * ε ^ 4, h])
    (hg : z.gradient = G • ![(1 : ℝ), p * ε ^ 2])
    (hA : z.secantMatrix = (TwoPhaseControls.first ε).matrix) :
    z.preconditionedGradient ⬝ᵥ
        (z.secantMatrix *ᵥ z.preconditionedGradient) =
      h ^ 2 * p ^ 2 * G ^ 2 * ε ^ 4 * (1 + 2 * ε ^ 3 + ε ^ 4) := by
  -- Expose the two matrix-vector products in the canonical incoming frame.
  rw [z.preconditionedGradient_def, hH, hg, hA, TwoPhaseControls.first_matrix]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  -- The remaining scalar polynomial is the required factored energy.
  ring

/-- The inverse-Hessian energy of the first-control secant image has the
displayed residual factor. -/
private lemma secantImageEnergyFirstControl
    (z : DFP.AbstractSecantStep (Fin 2)) (ε p h G : ℝ)
    (hH : z.inverseHessian = Matrix.diagonal ![h * p * ε ^ 4, h])
    (hg : z.gradient = G • ![(1 : ℝ), p * ε ^ 2])
    (hA : z.secantMatrix = (TwoPhaseControls.first ε).matrix) :
    (z.secantMatrix *ᵥ z.preconditionedGradient) ⬝ᵥ
        (z.inverseHessian *ᵥ
          (z.secantMatrix *ᵥ z.preconditionedGradient)) =
      h ^ 3 * p ^ 2 * G ^ 2 * ε ^ 4 *
        ((1 + ε ^ 3) ^ 2 + p * ε ^ 6 * (1 + ε) ^ 2) := by
  -- Expand the secant image and the final diagonal matrix action coordinatewise.
  rw [z.preconditionedGradient_def, hH, hg, hA, TwoPhaseControls.first_matrix]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  -- Polynomial normalization isolates the second canonical residual.
  ring

/-- Both residual denominators in the canonical first-control formulas are nonzero. -/
private lemma firstControlResiduals_ne_zero
    (z : DFP.AbstractSecantStep (Fin 2)) (ε p h G : ℝ)
    (hH : z.inverseHessian = Matrix.diagonal ![h * p * ε ^ 4, h])
    (hg : z.gradient = G • ![(1 : ℝ), p * ε ^ 2])
    (hA : z.secantMatrix = (TwoPhaseControls.first ε).matrix) :
    1 + 2 * ε ^ 3 + ε ^ 4 ≠ 0 ∧
      (1 + ε ^ 3) ^ 2 + p * ε ^ 6 * (1 + ε) ^ 2 ≠ 0 := by
  -- Positivity of each abstract energy makes its fully factored value nonzero.
  have hβ : h ^ 2 * p ^ 2 * G ^ 2 * ε ^ 4 * (1 + 2 * ε ^ 3 + ε ^ 4) ≠ 0 := by
    rw [← preconditionedEnergyFirstControl z ε p h G hH hg hA]
    exact z.stepLengthDenominator_ne_zero
  have hγ : h ^ 3 * p ^ 2 * G ^ 2 * ε ^ 4 *
      ((1 + ε ^ 3) ^ 2 + p * ε ^ 6 * (1 + ε) ^ 2) ≠ 0 := by
    rw [← secantImageEnergyFirstControl z ε p h G hH hg hA]
    exact ne_of_gt z.secantImageEnergy_pos
  -- Cancel only the outer product, retaining the residual factors used below.
  exact ⟨right_ne_zero_of_mul hβ, right_ne_zero_of_mul hγ⟩

/-- The canceled outputs agree with the established abstract DFP step on the canonical
input with radius `ε ^ 2`, first control, and amplitude `G`. -/
theorem outputEqStep (z : DFP.AbstractSecantStep (Fin 2)) (ε p h G : ℝ)
    (hH : z.inverseHessian = Matrix.diagonal ![h * p * ε ^ 4, h])
    (hg : z.gradient = G • ![(1 : ℝ), p * ε ^ 2])
    (hA : z.secantMatrix = (TwoPhaseControls.first ε).matrix)
    (hτ : z.tau = (TwoPhaseControls.first ε).tau) :
    (z.nextInverseHessian, z.nextGradient) =
      (outputMetric ε p h, G • outputGradient ε p h) := by
  -- Put the scaled gradient and first control into the explicit eigenframe spelling.
  have hg' : z.gradient = ![G, G * (p * ε ^ 2)] := by
    rw [hg]
    ext i
    fin_cases i
    · simp
    · simp
  have hA' : z.secantMatrix = !![1, ε; ε, 1] := by
    simpa only [TwoPhaseControls.first_matrix] using hA
  have hτ' : z.tau = 2 / 3 := by
    simpa only [TwoPhaseControls.first_tau] using hτ
  have hresiduals := firstControlResiduals_ne_zero z ε p h G hH hg hA
  have hβne :
      h ^ 2 * p ^ 2 * G ^ 2 * ε ^ 4 * (1 + 2 * ε ^ 3 + ε ^ 4) ≠ 0 := by
    rw [← preconditionedEnergyFirstControl z ε p h G hH hg hA]
    exact z.stepLengthDenominator_ne_zero
  have hγne :
      h ^ 3 * p ^ 2 * G ^ 2 * ε ^ 4 *
        ((1 + ε ^ 3) ^ 2 + p * ε ^ 6 * (1 + ε) ^ 2) ≠ 0 := by
    rw [← secantImageEnergyFirstControl z ε p h G hH hg hA]
    exact ne_of_gt z.secantImageEnergy_pos
  have hh : h ≠ 0 := by
    intro hh
    apply hβne
    simp [hh]
  have hp : p ≠ 0 := by
    intro hp
    apply hβne
    simp [hp]
  have hG : G ≠ 0 := by
    intro hG
    apply hβne
    simp [hG]
  have hε : ε ≠ 0 := by
    intro hε
    apply hβne
    simp [hε]
  -- Normalize the coordinate energies used by both eigenframe update formulas.
  have hβ :
      (h * p * ε ^ 4 * G) *
          (1 * (h * p * ε ^ 4 * G) + ε * (h * (G * (p * ε ^ 2)))) +
        (h * (G * (p * ε ^ 2))) *
          (ε * (h * p * ε ^ 4 * G) + 1 * (h * (G * (p * ε ^ 2)))) =
        h ^ 2 * p ^ 2 * G ^ 2 * ε ^ 4 * (1 + 2 * ε ^ 3 + ε ^ 4) := by
    ring
  have hγ :
      (h * p * ε ^ 4) *
          (1 * (h * p * ε ^ 4 * G) + ε * (h * (G * (p * ε ^ 2)))) ^ 2 +
        h * (ε * (h * p * ε ^ 4 * G) + 1 * (h * (G * (p * ε ^ 2)))) ^ 2 =
        h ^ 3 * p ^ 2 * G ^ 2 * ε ^ 4 *
          ((1 + ε ^ 3) ^ 2 + p * ε ^ 6 * (1 + ε) ^ 2) := by
    ring
  apply Prod.ext
  · -- The rank-two formula reduces the matrix equality to four scalar identities.
    rw [z.nextInverseHessian_eigenframe (h * p * ε ^ 4) h G
      (G * (p * ε ^ 2)) 1 ε 1 hH hg' hA']
    rw [hβ, hγ]
    unfold outputMetric
    ext i j
    fin_cases i
    · fin_cases j
      · simp
        field_simp [hh, hp, hG, hε, hβne, hγne, hresiduals.1, hresiduals.2]
        ring
      · simp
        field_simp [hh, hp, hG, hε, hβne, hγne, hresiduals.1, hresiduals.2]
        ring
    · fin_cases j
      · simp
        field_simp [hh, hp, hG, hε, hβne, hγne, hresiduals.1, hresiduals.2]
        ring
      · simp
        field_simp [hh, hp, hG, hε, hβne, hγne, hresiduals.1, hresiduals.2]
        ring
  · -- The exact gradient formula uses the same `β` normalization in two coordinates.
    rw [z.nextGradient_eigenframe (h * p * ε ^ 4) h G
      (G * (p * ε ^ 2)) 1 ε 1 hH hg' hA', hτ']
    rw [hβ]
    unfold outputGradient
    ext i
    fin_cases i
    · simp
      field_simp [hh, hp, hG, hε, hβne, hresiduals.1]
      ring
    · simp
      field_simp [hh, hp, hG, hε, hβne, hresiduals.1]
      ring

/-- Each entry of the canceled first updated metric is analytic at the base parameters. -/
private lemma analyticAt_outputMetricEntry (i j : Fin 2) : AnalyticAt ℝ
    (fun x : ℝ × ℝ × ℝ ↦ outputMetric x.1 x.2.1 x.2.2 i j) (0, 2, 1) := by
  have hε : AnalyticAt ℝ (fun x : ℝ × ℝ × ℝ ↦ x.1) (0, 2, 1) := analyticAt_fst
  have hp : AnalyticAt ℝ (fun x : ℝ × ℝ × ℝ ↦ x.2.1) (0, 2, 1) :=
    analyticAt_fst.comp analyticAt_snd
  have hh : AnalyticAt ℝ (fun x : ℝ × ℝ × ℝ ↦ x.2.2) (0, 2, 1) :=
    analyticAt_snd.comp analyticAt_snd
  -- Coordinatewise expansion exposes only polynomial operations and nonvanishing quotients.
  fin_cases i
  · fin_cases j
    · unfold outputMetric
      dsimp
      fun_prop (disch := norm_num) [Prod.fst, Prod.snd]
    · unfold outputMetric
      dsimp
      fun_prop (disch := norm_num) [Prod.fst, Prod.snd]
  · fin_cases j
    · unfold outputMetric
      dsimp
      fun_prop (disch := norm_num) [Prod.fst, Prod.snd]
    · unfold outputMetric
      dsimp
      fun_prop (disch := norm_num) [Prod.fst, Prod.snd]

/-- Each coordinate of the canceled first updated gradient is analytic at the base parameters. -/
private lemma analyticAt_outputGradientEntry (i : Fin 2) : AnalyticAt ℝ
    (fun x : ℝ × ℝ × ℝ ↦ outputGradient x.1 x.2.1 x.2.2 i) (0, 2, 1) := by
  have hε : AnalyticAt ℝ (fun x : ℝ × ℝ × ℝ ↦ x.1) (0, 2, 1) := analyticAt_fst
  have hp : AnalyticAt ℝ (fun x : ℝ × ℝ × ℝ ↦ x.2.1) (0, 2, 1) :=
    analyticAt_fst.comp analyticAt_snd
  -- The two coordinates are rational functions with unit residual denominator at the base.
  fin_cases i
  · unfold outputGradient
    dsimp
    fun_prop (disch := norm_num) [Prod.fst, Prod.snd]
  · unfold outputGradient
    dsimp
    fun_prop (disch := norm_num) [Prod.fst, Prod.snd]

/-- The three independent entries of the canceled first updated metric. -/
private def metricEntryTriple (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (outputMetric x.1 x.2.1 x.2.2 0 0,
    outputMetric x.1 x.2.1 x.2.2 0 1,
    outputMetric x.1 x.2.1 x.2.2 1 1)

/-- The metric-entry triple is analytic at the base parameters. -/
private lemma analyticAt_metricEntryTriple : AnalyticAt ℝ metricEntryTriple (0, 2, 1) := by
  -- Assemble the three previously established entrywise analytic functions.
  exact (analyticAt_outputMetricEntry 0 0).prod
    ((analyticAt_outputMetricEntry 0 1).prod (analyticAt_outputMetricEntry 1 1))

/-- At the base parameters, the metric-entry triple is the reference diagonal triple. -/
private lemma metricEntryTriple_base :
    metricEntryTriple (0, 2, 1) = ((0, 0, 1) : ℝ × ℝ × ℝ) := by
  norm_num [metricEntryTriple, outputMetric]

/-- The fixed frame depends on the metric only through its three independent entries. -/
private lemma frame_eq_frameOfMetricEntries (x : ℝ × ℝ × ℝ) :
    frame x.1 x.2.1 x.2.2 = EuclideanPlane.frame
      (RealSymmetric2.lowVector (metricEntryTriple x).1
        (metricEntryTriple x).2.1 (metricEntryTriple x).2.2) := by
  rfl

/-- Each entry of the fixed first-leg eigenframe is analytic at the base parameters. -/
private lemma analyticAt_frameEntry (i j : Fin 2) : AnalyticAt ℝ
    (fun x : ℝ × ℝ × ℝ ↦ frame x.1 x.2.1 x.2.2 i j) (0, 2, 1) := by
  have houter := RealSymmetric2.analyticOnNhd_frame i j
    ((0, 0, 1) : ℝ × ℝ × ℝ) RealSymmetric2.diag_mem_lowChart
  rw [← metricEntryTriple_base] at houter
  have hframe := houter.comp analyticAt_metricEntryTriple
  apply hframe.congr
  filter_upwards [] with x
  exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ ↦ M i j)
    (frame_eq_frameOfMetricEntries x).symm

/-- Near the base point, the fixed analytic low eigenvector is already oriented toward
the first updated gradient. -/
theorem frameOriented :
    ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ), 0 < (coordinates x.1 x.2.1 x.2.2).1 := by
  -- Continuity preserves the positive low-frame coordinate at the diagonal base point.
  have hcoordinate : ContinuousAt
      (fun x : ℝ × ℝ × ℝ ↦ (coordinates x.1 x.2.1 x.2.2).1) (0, 2, 1) := by
    have htop : (instTopologicalSpaceProd : TopologicalSpace (ℝ × ℝ × ℝ)) =
        PseudoMetricSpace.toUniformSpace.toTopologicalSpace := by
      with_reducible_and_instances rfl
    rw [htop]
    have hsum := ((analyticAt_frameEntry 0 0).continuousAt.mul
        (analyticAt_outputGradientEntry 0).continuousAt).add
        ((analyticAt_frameEntry 1 0).continuousAt.mul
          (analyticAt_outputGradientEntry 1).continuousAt)
    have hsum' : ContinuousAt (fun x : ℝ × ℝ × ℝ ↦
        frame x.1 x.2.1 x.2.2 0 0 * outputGradient x.1 x.2.1 x.2.2 0 +
          frame x.1 x.2.1 x.2.2 1 0 * outputGradient x.1 x.2.1 x.2.2 1) (0, 2, 1) := by
      apply hsum.congr
      filter_upwards [] with x
      rfl
    simpa [coordinates, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hsum'
  apply hcoordinate.eventually
  apply Ioi_mem_nhds
  simp [coordinates, frame, outputMetric, outputGradient, RealSymmetric2.frame_diag,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The high eigenvalue of the first updated metric is analytic at the base parameters. -/
private lemma analyticAt_highEigenvalue : AnalyticAt ℝ
    (fun x : ℝ × ℝ × ℝ ↦ RealSymmetric2.high (metricEntryTriple x).1
      (metricEntryTriple x).2.1 (metricEntryTriple x).2.2) (0, 2, 1) := by
  have houter := RealSymmetric2.analyticOnNhd_high
    ((0, 0, 1) : ℝ × ℝ × ℝ) RealSymmetric2.diag_mem_lowChart
  rw [← metricEntryTriple_base] at houter
  exact houter.comp analyticAt_metricEntryTriple

/-- The high eigenvalue of the first updated metric stays nonzero near the base parameters. -/
private lemma eventually_highEigenvalue_ne_zero :
    ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      RealSymmetric2.high (metricEntryTriple x).1
        (metricEntryTriple x).2.1 (metricEntryTriple x).2.2 ≠ 0 := by
  have htop : (instTopologicalSpaceProd : TopologicalSpace (ℝ × ℝ × ℝ)) =
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace := by
    with_reducible_and_instances rfl
  rw [htop]
  apply analyticAt_highEigenvalue.continuousAt.eventually_ne
  rw [metricEntryTriple_base]
  have hsum := RealSymmetric2.low_add_high 0 0 1
  have hprod := RealSymmetric2.low_mul_high 0 0 1
  have hle := RealSymmetric2.low_le_high 0 0 1
  nlinarith

/-- Scaling the first row and column extracts the fourth power from the low eigenvalue. -/
private lemma low_scaledFactorization (ε a b d : ℝ)
    (hhigh : RealSymmetric2.high (ε ^ 4 * a) (ε ^ 2 * b) d ≠ 0) :
    RealSymmetric2.low (ε ^ 4 * a) (ε ^ 2 * b) d =
      ε ^ 4 * ((a * d - b ^ 2) /
        RealSymmetric2.high (ε ^ 4 * a) (ε ^ 2 * b) d) := by
  -- Divide the low-high determinant identity by the nonzero high eigenvalue.
  rw [← mul_div_assoc]
  apply (eq_div_iff hhigh).2
  rw [RealSymmetric2.low_mul_high]
  ring

/-- A nonzero high spectral factor exposes the pointwise removable
factorization of the first-leg eigenvalues. -/
theorem spectrumFactorization_of_high_ne_zero (ε p h : ℝ)
    (hhigh : (spectralFactors ε p h).2 ≠ 0) :
    eigenvalues ε p h =
      (ε ^ 4 * (spectralFactors ε p h).1, (spectralFactors ε p h).2) := by
  unfold spectralFactors at hhigh
  dsimp at hhigh
  unfold eigenvalues spectralFactors outputMetric
  dsimp
  apply Prod.ext
  · rw [RealSymmetric2.low_eq_det_div_high_of_ne _ _ _ hhigh]
    ring
  · rfl

/-- Locally at `(0, 2, 1)`, the first updated low and high eigenvalues factor as
`ε ^ 4 * L₁` and `ℋ₁`. -/
theorem spectrumFactorization :
    ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      eigenvalues x.1 x.2.1 x.2.2 =
        (x.1 ^ 4 * (spectralFactors x.1 x.2.1 x.2.2).1,
          (spectralFactors x.1 x.2.1 x.2.2).2) := by
  filter_upwards [eventually_highEigenvalue_ne_zero] with x hx
  -- The determinant identity cancels the displayed `ε ^ 4` from the low eigenvalue.
  unfold metricEntryTriple at hx
  unfold eigenvalues spectralFactors
  dsimp at hx ⊢
  apply Prod.ext
  · exact low_scaledFactorization _ _ _ _ hx
  · rfl

/-- The first updated metric remains in the fixed low-eigenvector chart near the base. -/
private lemma eventually_metricEntryTriple_mem_lowChart :
    ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      (metricEntryTriple x).1 < (metricEntryTriple x).2.2 := by
  have ha : AnalyticAt ℝ (fun x : ℝ × ℝ × ℝ ↦ (metricEntryTriple x).1) (0, 2, 1) :=
    analyticAt_fst.comp analyticAt_metricEntryTriple
  have hd : AnalyticAt ℝ (fun x : ℝ × ℝ × ℝ ↦ (metricEntryTriple x).2.2) (0, 2, 1) :=
    (analyticAt_snd.comp analyticAt_snd).comp analyticAt_metricEntryTriple
  have htop : (instTopologicalSpaceProd : TopologicalSpace (ℝ × ℝ × ℝ)) =
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace := by
    with_reducible_and_instances rfl
  rw [htop]
  have hdiffRaw := (hd.sub ha).continuousAt
  have hdiff : ContinuousAt
      (fun x : ℝ × ℝ × ℝ ↦ (metricEntryTriple x).2.2 - (metricEntryTriple x).1)
      (0, 2, 1) := by
    apply hdiffRaw.congr
    filter_upwards [] with x
    rfl
  have hpos : ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      0 < (metricEntryTriple x).2.2 - (metricEntryTriple x).1 := by
    apply hdiff.eventually
    have hbaseDiff :
        ((fun x : ℝ × ℝ × ℝ ↦ (metricEntryTriple x).2.2 - (metricEntryTriple x).1)
          (0, 2, 1)) = 1 := by
      dsimp
      rw [metricEntryTriple_base]
      norm_num
    rw [hbaseDiff]
    have hone_pos : 0 < (1 : ℝ) := by
      norm_num
    exact Ioi_mem_nhds hone_pos
  simpa only [sub_pos] using hpos

/-- Locally at `(0, 2, 1)`, the first-leg eigenframe diagonalizes the updated metric
with diagonal entries `ε ^ 4 * L₁` and `ℋ₁`. -/
theorem frameDiagonalization :
    ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      (frame x.1 x.2.1 x.2.2).transpose * outputMetric x.1 x.2.1 x.2.2 *
          frame x.1 x.2.1 x.2.2 =
        Matrix.diagonal
          ![x.1 ^ 4 * (spectralFactors x.1 x.2.1 x.2.2).1,
            (spectralFactors x.1 x.2.1 x.2.2).2] := by
  -- Work where the metric is in the low-eigenvector chart and its spectrum is factored.
  filter_upwards [eventually_metricEntryTriple_mem_lowChart, spectrumFactorization]
    with x hchart hspectrum
  -- Project the factored spectral pair to rewrite both diagonal entries separately.
  have hlow := congrArg Prod.fst hspectrum
  have hhigh := congrArg Prod.snd hspectrum
  simp only at hlow hhigh
  rw [← hlow, ← hhigh]
  -- The established eigenframe theorem applies to the three metric entries on the chart.
  simpa [frame, eigenvalues, metricEntryTriple, outputMetric, RealSymmetric2.matrix] using
    RealSymmetric2.frame_diagonalizes (metricEntryTriple x).1
      (metricEntryTriple x).2.1 (metricEntryTriple x).2.2 hchart

/-- In the oriented first-leg eigenframe, the updated gradient has the exact
factored coordinates `G • ![𝒢₁, ε ^ 2 * U₁]` for every parameter triple
and amplitude. -/
theorem frame_transpose_mulVec_outputGradient (ε p h G : ℝ) :
    (frame ε p h).transpose *ᵥ (G • outputGradient ε p h) =
      G • ![(gradientFactors ε p h).1,
        ε ^ 2 * (gradientFactors ε p h).2] := by
  -- Expanding the two frame columns exposes exactly the two canceled numerators.
  unfold gradientFactors frame outputMetric outputGradient
  ext i
  fin_cases i
  · simp [EuclideanPlane.frame, EuclideanPlane.perp_apply, RealSymmetric2.lowVector,
      RealSymmetric2.lowRaw, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  · simp [EuclideanPlane.frame, EuclideanPlane.perp_apply, RealSymmetric2.lowVector,
      RealSymmetric2.lowRaw, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring

/-- A nonzero low gradient factor forces the normalization denominator of the
fixed first-leg low eigenvector to be nonzero. -/
theorem lowDenom_ne_zero_of_gradientFactor_ne_zero (ε p h : ℝ)
    (hlow : (gradientFactors ε p h).1 ≠ 0) :
    RealSymmetric2.lowDenom (outputMetric ε p h 0 0)
      (outputMetric ε p h 0 1) (outputMetric ε p h 1 1) ≠ 0 := by
  let H := outputMetric ε p h
  change RealSymmetric2.lowDenom (H 0 0) (H 0 1) (H 1 1) ≠ 0
  intro hzero
  have hframeZero : frame ε p h = 0 := by
    simp only [frame, H, RealSymmetric2.lowVector, hzero, inv_zero, zero_smul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [EuclideanPlane.frame, EuclideanPlane.perp_apply]
  have hfactor := frame_transpose_mulVec_outputGradient ε p h 1
  rw [hframeZero] at hfactor
  have hcoordinate := congrArg (fun v : Fin 2 → ℝ ↦ v 0) hfactor
  have hfactorZero : (gradientFactors ε p h).1 = 0 := by
    simpa using hcoordinate.symm
  exact hlow hfactorZero

/-- If the low gradient coordinate is nonzero, the fixed first-leg eigenframe
is a positively oriented orthogonal frame. -/
theorem frame_mem_specialOrthogonalGroup (ε p h : ℝ)
    (hlow : (gradientFactors ε p h).1 ≠ 0) :
    frame ε p h ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
  let H := outputMetric ε p h
  have hdenom : RealSymmetric2.lowDenom (H 0 0) (H 0 1) (H 1 1) ≠ 0 := by
    simpa only [H] using
      lowDenom_ne_zero_of_gradientFactor_ne_zero ε p h hlow
  change EuclideanPlane.frame
      (RealSymmetric2.lowVector (H 0 0) (H 0 1) (H 1 1)) ∈
    Matrix.specialOrthogonalGroup (Fin 2) ℝ
  exact RealSymmetric2.frame_mem_specialOrthogonalGroup_of_lowDenom_ne_zero
    (H 0 0) (H 0 1) (H 1 1) hdenom

/-- Locally at `(0, 2, 1)`, the oriented first updated gradient coordinates factor as
`G • ![𝒢₁, ε ^ 2 * U₁]` for every amplitude `G`. -/
theorem gradientFactorization :
    ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ), ∀ G : ℝ,
      (frame x.1 x.2.1 x.2.2).transpose *ᵥ
          (G • outputGradient x.1 x.2.1 x.2.2) =
        G • ![(gradientFactors x.1 x.2.1 x.2.2).1,
          x.1 ^ 2 * (gradientFactors x.1 x.2.1 x.2.2).2] := by
  filter_upwards [] with x
  exact frame_transpose_mulVec_outputGradient x.1 x.2.1 x.2.2

/-- The three unscaled residual entries underlying the first updated metric. -/
private def metricResiduals (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  let ε := x.1
  let p := x.2.1
  let h := x.2.2
  let B := 1 + 2 * ε ^ 3 + ε ^ 4
  let C := (1 + ε ^ 3) ^ 2 + p * ε ^ 6 * (1 + ε) ^ 2
  let a := h * p - h * p ^ 2 * ε ^ 6 * (1 + ε) ^ 2 / C + 1 / B
  let b := 1 / B - h * p * ε ^ 3 * (1 + ε) * (1 + ε ^ 3) / C
  let d := h - h * (1 + ε ^ 3) ^ 2 / C + 1 / B
  (a, b, d)

/-- The two unscaled residual coordinates underlying the first updated gradient. -/
private def gradientResiduals (x : ℝ × ℝ × ℝ) : ℝ × ℝ :=
  let ε := x.1
  let p := x.2.1
  let B := 1 + 2 * ε ^ 3 + ε ^ 4
  let q := 1 - 2 * (p + 1) * ε ^ 3 * (1 + ε) / (3 * B)
  let v := p - 2 * (p + 1) * (1 + ε ^ 3) / (3 * B)
  (q, v)

/-- The unscaled metric residuals are analytic at the base parameters. -/
private lemma analyticAt_metricResiduals : AnalyticAt ℝ metricResiduals (0, 2, 1) := by
  have hε : AnalyticAt ℝ (fun x : ℝ × ℝ × ℝ ↦ x.1) (0, 2, 1) := analyticAt_fst
  have hp : AnalyticAt ℝ (fun x : ℝ × ℝ × ℝ ↦ x.2.1) (0, 2, 1) :=
    analyticAt_fst.comp analyticAt_snd
  have hh : AnalyticAt ℝ (fun x : ℝ × ℝ × ℝ ↦ x.2.2) (0, 2, 1) :=
    analyticAt_snd.comp analyticAt_snd
  unfold metricResiduals
  dsimp
  fun_prop (disch := norm_num) [Prod.fst, Prod.snd]

/-- The unscaled gradient residuals are analytic at the base parameters. -/
private lemma analyticAt_gradientResiduals : AnalyticAt ℝ gradientResiduals (0, 2, 1) := by
  have hε : AnalyticAt ℝ (fun x : ℝ × ℝ × ℝ ↦ x.1) (0, 2, 1) := analyticAt_fst
  have hp : AnalyticAt ℝ (fun x : ℝ × ℝ × ℝ ↦ x.2.1) (0, 2, 1) :=
    analyticAt_fst.comp analyticAt_snd
  unfold gradientResiduals
  dsimp
  fun_prop (disch := norm_num) [Prod.fst, Prod.snd]

/-- The low eigenvalue of the first updated metric is analytic at the base parameters. -/
private lemma analyticAt_lowEigenvalue : AnalyticAt ℝ
    (fun x : ℝ × ℝ × ℝ ↦ RealSymmetric2.low (metricEntryTriple x).1
      (metricEntryTriple x).2.1 (metricEntryTriple x).2.2) (0, 2, 1) := by
  have houter := RealSymmetric2.analyticOnNhd_low
    ((0, 0, 1) : ℝ × ℝ × ℝ) RealSymmetric2.diag_mem_lowChart
  rw [← metricEntryTriple_base] at houter
  exact houter.comp analyticAt_metricEntryTriple

/-- The low eigenvalue of the base metric is zero. -/
private lemma lowEigenvalue_base : RealSymmetric2.low (metricEntryTriple (0, 2, 1)).1
    (metricEntryTriple (0, 2, 1)).2.1 (metricEntryTriple (0, 2, 1)).2.2 = 0 := by
  rw [metricEntryTriple_base]
  have hsum := RealSymmetric2.low_add_high 0 0 1
  have hprod := RealSymmetric2.low_mul_high 0 0 1
  have hle := RealSymmetric2.low_le_high 0 0 1
  nlinarith

/-- The high eigenvalue of the base metric is one. -/
private lemma highEigenvalue_base : RealSymmetric2.high (metricEntryTriple (0, 2, 1)).1
    (metricEntryTriple (0, 2, 1)).2.1 (metricEntryTriple (0, 2, 1)).2.2 = 1 := by
  rw [metricEntryTriple_base]
  have hsum := RealSymmetric2.low_add_high 0 0 1
  have hprod := RealSymmetric2.low_mul_high 0 0 1
  have hle := RealSymmetric2.low_le_high 0 0 1
  nlinarith

/-- The squared norm used to normalize the fixed low eigenvector. -/
private def lowDenomRadicand (x : ℝ × ℝ × ℝ) : ℝ :=
  ((metricEntryTriple x).2.2 -
      RealSymmetric2.low (metricEntryTriple x).1
        (metricEntryTriple x).2.1 (metricEntryTriple x).2.2) ^ 2 +
    (metricEntryTriple x).2.1 ^ 2

/-- The low-eigenvector normalization radicand is analytic at the base parameters. -/
private lemma analyticAt_lowDenomRadicand : AnalyticAt ℝ lowDenomRadicand (0, 2, 1) := by
  have hb : AnalyticAt ℝ (fun x : ℝ × ℝ × ℝ ↦ (metricEntryTriple x).2.1) (0, 2, 1) :=
    (analyticAt_fst.comp analyticAt_snd).comp analyticAt_metricEntryTriple
  have hd : AnalyticAt ℝ (fun x : ℝ × ℝ × ℝ ↦ (metricEntryTriple x).2.2) (0, 2, 1) :=
    (analyticAt_snd.comp analyticAt_snd).comp analyticAt_metricEntryTriple
  have hradicand := ((hd.sub analyticAt_lowEigenvalue).pow 2).add (hb.pow 2)
  apply hradicand.congr
  filter_upwards [] with x
  rfl

/-- The low-eigenvector normalization denominator is analytic at the base parameters. -/
private lemma analyticAt_lowDenom : AnalyticAt ℝ
    (fun x : ℝ × ℝ × ℝ ↦ RealSymmetric2.lowDenom (metricEntryTriple x).1
      (metricEntryTriple x).2.1 (metricEntryTriple x).2.2) (0, 2, 1) := by
  have hradicand_pos : 0 < lowDenomRadicand (0, 2, 1) := by
    unfold lowDenomRadicand
    rw [metricEntryTriple_base]
    norm_num [RealSymmetric2.low, RealSymmetric2.gap]
  have hsqrtAt : AnalyticAt ℝ Real.sqrt (lowDenomRadicand (0, 2, 1)) := by
    have hformula : AnalyticAt ℝ
        (fun y : ℝ ↦ NormedSpace.exp (Real.log y * (1 / 2 : ℝ)))
        (lowDenomRadicand (0, 2, 1)) :=
      (NormedSpace.exp_analytic _).comp
        ((analyticAt_log hradicand_pos).mul analyticAt_const)
    apply hformula.congr
    filter_upwards [eventually_gt_nhds hradicand_pos] with y hy
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hy, Real.exp_eq_exp_ℝ]
  have hsqrt := hsqrtAt.comp (f := lowDenomRadicand) analyticAt_lowDenomRadicand
  apply hsqrt.congr
  filter_upwards [] with x
  rfl

/-- The removable spectral factors equal their residual determinant formula. -/
private lemma spectralFactors_eq_residualFormula (x : ℝ × ℝ × ℝ) :
    spectralFactors x.1 x.2.1 x.2.2 =
      (((metricResiduals x).1 * (metricResiduals x).2.2 - (metricResiduals x).2.1 ^ 2) /
          RealSymmetric2.high (metricEntryTriple x).1
            (metricEntryTriple x).2.1 (metricEntryTriple x).2.2,
        RealSymmetric2.high (metricEntryTriple x).1
          (metricEntryTriple x).2.1 (metricEntryTriple x).2.2) := by
  rfl

/-- The removable spectral factors are analytic at the base parameters. -/
private lemma analyticAt_spectralFactors : AnalyticAt ℝ
    (fun x : ℝ × ℝ × ℝ ↦ spectralFactors x.1 x.2.1 x.2.2) (0, 2, 1) := by
  have ha := analyticAt_fst.comp analyticAt_metricResiduals
  have hb := (analyticAt_fst.comp analyticAt_snd).comp analyticAt_metricResiduals
  have hd := (analyticAt_snd.comp analyticAt_snd).comp analyticAt_metricResiduals
  have hhigh_ne : RealSymmetric2.high (metricEntryTriple (0, 2, 1)).1
      (metricEntryTriple (0, 2, 1)).2.1 (metricEntryTriple (0, 2, 1)).2.2 ≠ 0 := by
    rw [highEigenvalue_base]
    norm_num
  have hlowFactor := ((ha.mul hd).sub (hb.pow 2)).div analyticAt_highEigenvalue
    hhigh_ne
  have hpairs := hlowFactor.prod analyticAt_highEigenvalue
  apply hpairs.congr
  filter_upwards [] with x
  exact (spectralFactors_eq_residualFormula x).symm

/-- The removable gradient factors equal their residual eigenvector-coordinate formula. -/
private lemma gradientFactors_eq_residualFormula (x : ℝ × ℝ × ℝ) :
    gradientFactors x.1 x.2.1 x.2.2 =
      ((((metricResiduals x).2.2 -
            RealSymmetric2.low (metricEntryTriple x).1
              (metricEntryTriple x).2.1 (metricEntryTriple x).2.2) *
          (gradientResiduals x).1 - x.1 ^ 4 * (metricResiduals x).2.1 *
            (gradientResiduals x).2) /
          RealSymmetric2.lowDenom (metricEntryTriple x).1
            (metricEntryTriple x).2.1 (metricEntryTriple x).2.2,
        ((metricResiduals x).2.1 * (gradientResiduals x).1 +
            ((metricResiduals x).2.2 -
              RealSymmetric2.low (metricEntryTriple x).1
                (metricEntryTriple x).2.1 (metricEntryTriple x).2.2) *
              (gradientResiduals x).2) /
          RealSymmetric2.lowDenom (metricEntryTriple x).1
            (metricEntryTriple x).2.1 (metricEntryTriple x).2.2) := by
  rfl

/-- The removable gradient factors are analytic at the base parameters. -/
private lemma analyticAt_gradientFactors : AnalyticAt ℝ
    (fun x : ℝ × ℝ × ℝ ↦ gradientFactors x.1 x.2.1 x.2.2) (0, 2, 1) := by
  have hε : AnalyticAt ℝ (fun x : ℝ × ℝ × ℝ ↦ x.1) (0, 2, 1) := analyticAt_fst
  have hb := (analyticAt_fst.comp analyticAt_snd).comp analyticAt_metricResiduals
  have hd := (analyticAt_snd.comp analyticAt_snd).comp analyticAt_metricResiduals
  have hq := analyticAt_fst.comp analyticAt_gradientResiduals
  have hv := analyticAt_snd.comp analyticAt_gradientResiduals
  have hdenom_ne : RealSymmetric2.lowDenom (metricEntryTriple (0, 2, 1)).1
      (metricEntryTriple (0, 2, 1)).2.1 (metricEntryTriple (0, 2, 1)).2.2 ≠ 0 := by
    rw [RealSymmetric2.lowDenom, metricEntryTriple_base]
    norm_num [RealSymmetric2.low, RealSymmetric2.gap]
  have hlowFactor := (((hd.sub analyticAt_lowEigenvalue).mul hq).sub
    (((hε.pow 4).mul hb).mul hv)).div analyticAt_lowDenom hdenom_ne
  have hhighFactor := ((hb.mul hq).add
    ((hd.sub analyticAt_lowEigenvalue).mul hv)).div analyticAt_lowDenom hdenom_ne
  have hpairs := hlowFactor.prod hhighFactor
  apply hpairs.congr
  filter_upwards [] with x
  exact (gradientFactors_eq_residualFormula x).symm

/-- The spectral removable factors have their reference values at the base parameters. -/
private lemma spectralFactors_base : spectralFactors 0 2 1 = (2, 1) := by
  norm_num [spectralFactors, RealSymmetric2.low, RealSymmetric2.high,
    RealSymmetric2.gap]

/-- The gradient removable factors have their reference values at the base parameters. -/
private lemma gradientFactors_base : gradientFactors 0 2 1 = (1, 1) := by
  norm_num [gradientFactors, RealSymmetric2.low, RealSymmetric2.gap,
    RealSymmetric2.lowDenom]

/-- The removable canonical factors equal the recovery quotients of the spectral and
gradient factors. -/
private lemma canonicalFactors_eq_factorFormula (x : ℝ × ℝ × ℝ) :
    canonicalFactors x.1 x.2.1 x.2.2 =
      ((spectralFactors x.1 x.2.1 x.2.2).1 *
          (gradientFactors x.1 x.2.1 x.2.2).1 /
        ((spectralFactors x.1 x.2.1 x.2.2).2 *
          (gradientFactors x.1 x.2.1 x.2.2).2),
        (spectralFactors x.1 x.2.1 x.2.2).2 *
            (gradientFactors x.1 x.2.1 x.2.2).2 ^ 2 /
          ((spectralFactors x.1 x.2.1 x.2.2).1 *
            (gradientFactors x.1 x.2.1 x.2.2).1 ^ 2)) := by
  rfl

/-- The removable canonical factors are analytic at the base parameters. -/
private lemma analyticAt_canonicalFactors : AnalyticAt ℝ
    (fun x : ℝ × ℝ × ℝ ↦ canonicalFactors x.1 x.2.1 x.2.2) (0, 2, 1) := by
  have hL := analyticAt_fst.comp analyticAt_spectralFactors
  have hH := analyticAt_snd.comp analyticAt_spectralFactors
  have hQ := analyticAt_fst.comp analyticAt_gradientFactors
  have hU := analyticAt_snd.comp analyticAt_gradientFactors
  have hhighDenom_ne :
      (spectralFactors 0 2 1).2 * (gradientFactors 0 2 1).2 ≠ 0 := by
    rw [spectralFactors_base, gradientFactors_base]
    norm_num
  have hlowDenom_ne :
      (spectralFactors 0 2 1).1 * (gradientFactors 0 2 1).1 ^ 2 ≠ 0 := by
    rw [spectralFactors_base, gradientFactors_base]
    norm_num
  have hradius := (hL.mul hQ).div (hH.mul hU) hhighDenom_ne
  have hshape := (hH.mul (hU.pow 2)).div (hL.mul (hQ.pow 2)) hlowDenom_ne
  have hpairs := hradius.prod hshape
  apply hpairs.congr
  filter_upwards [] with x
  exact (canonicalFactors_eq_factorFormula x).symm

/-- All six removable first-leg factors are jointly real analytic at `(0, 2, 1)`. -/
theorem factorsAnalytic :
    AnalyticAt ℝ
      (fun x : ℝ × ℝ × ℝ ↦ factors x.1 x.2.1 x.2.2)
      (0, 2, 1) := by
  -- Assemble the spectral, gradient, and canonical analytic pairs.
  exact analyticAt_spectralFactors.prod
    (analyticAt_gradientFactors.prod analyticAt_canonicalFactors)

/-- The first-leg spectral, gradient, radius, and shape factors have base values
`(2, 1, 1, 1, 2, 1 / 2)`. -/
theorem factorsBase :
    factors 0 2 1 = ((2, 1), (1, 1), (2, 1 / 2)) := by
  -- At the diagonal base metric, all residual denominators and spectral radicals are one.
  norm_num [factors, spectralFactors, gradientFactors, canonicalFactors,
    RealSymmetric2.low, RealSymmetric2.high, RealSymmetric2.gap,
    RealSymmetric2.lowDenom]

/-- Canonical recovery cancels the prescribed fourth- and second-power coordinate factors. -/
private lemma recovered_scaledFactorization (ε L H Q U : ℝ) (hε : ε ≠ 0) :
    (CycleBoundaryState.recoveryRadius (ε ^ 4 * L) H Q (ε ^ 2 * U),
      CycleBoundaryState.recoveryShape (ε ^ 4 * L) H Q (ε ^ 2 * U)) =
        (ε ^ 2 * (L * Q / (H * U)), H * U ^ 2 / (L * Q ^ 2)) := by
  unfold CycleBoundaryState.recoveryRadius CycleBoundaryState.recoveryShape
  apply Prod.ext
  · dsimp
    by_cases hH : H = 0
    · simp [hH]
    by_cases hU : U = 0
    · simp [hU]
    field_simp [hε, hH, hU]
  · dsimp
    by_cases hL : L = 0
    · simp [hL]
    by_cases hQ : Q = 0
    · simp [hQ]
    field_simp [hε, hL, hQ]

/-- Locally at `(0, 2, 1)` away from `ε = 0`, canonical recovery yields radius
`ε ^ 2 * ℛ₁` and shape `p₁`. -/
theorem canonicalFactorization :
    ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ), x.1 ≠ 0 →
      recovered x.1 x.2.1 x.2.2 =
        (x.1 ^ 2 * (canonicalFactors x.1 x.2.1 x.2.2).1,
          (canonicalFactors x.1 x.2.1 x.2.2).2) := by
  filter_upwards [spectrumFactorization, gradientFactorization] with x hspectrum hgradient
  intro hε
  have hvector := hgradient 1
  simp only [one_smul] at hvector
  have hcoordinates : coordinates x.1 x.2.1 x.2.2 =
      ((gradientFactors x.1 x.2.1 x.2.2).1,
        x.1 ^ 2 * (gradientFactors x.1 x.2.1 x.2.2).2) := by
    unfold coordinates
    apply Prod.ext
    · exact congrArg (fun v : Fin 2 → ℝ ↦ v 0) hvector
    · exact congrArg (fun v : Fin 2 → ℝ ↦ v 1) hvector
  -- Substitute the factored spectrum and coordinates before canceling the powers of `ε`.
  unfold recovered
  dsimp
  rw [hspectrum, hcoordinates]
  unfold canonicalFactors
  dsimp
  exact recovered_scaledFactorization _ _ _ _ _ hε

end DFP.FirstLeg
