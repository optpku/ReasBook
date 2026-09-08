module

public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.RawFrameCertificateAdapter
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterBracketRegularityAdapter
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterResidualKernelFromBracket
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterResidualSourceFromKernel
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.RawFrameAngleGermAdapter
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CanonicalFrameSlopeGerm
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.RawFrameCertificateAdapter
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterBracketRegularityAdapter
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterResidualKernelFromBracket
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterResidualSourceFromKernel
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.RawFrameAngleGermAdapter
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CanonicalFrameSlopeGerm

public section

noncomputable section

namespace DFP.TwoLeg.Mixed

/-!
This module exposes the source normal-form identity for the mixed center bracket.
The parent evaluator keeps the same calculation private; downstream source
certificates can consume the public equality without unfolding the observable.
-/

/-!
The frame-slope part of the source proof is kept separate from the center-bracket
certificate. The two projections below mirror the frames used by the public
raw-angle normal form, giving later source files a stable place to state signed
frame facts.
-/

/-- Infrastructure I.16a: the first oriented frame in the public raw-angle normal
form, expressed as a state projection rather than a large evaluator term. -/
def mixedIndependentRawFirstFrame
    (b r p h : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  CenterRaw.firstFrame b (r, p, h)

/-- Infrastructure I.16a: the second oriented frame in the public raw-angle normal
form, expressed as a state projection rather than a large evaluator term. -/
def mixedIndependentRawSecondFrame
    (b r p h : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let step := CenterRaw.secondStep b (r, p, h)
  OrientedEigenframe.frame (step.1 0 0) (step.1 0 1) (step.1 1 1)
    (WithLp.toLp 2 step.2.1)

/-- Infrastructure I.16a: the public raw relative-frame matrix is the product of
the two named frame projections. -/
theorem mixedIndependentRawFrameAngleMatrix_eq_frameProduct
    (b r p h : ℝ) :
    mixedIndependentRawFrameAngleMatrix b r p h =
      mixedIndependentRawFirstFrame b r p h *
        mixedIndependentRawSecondFrame b r p h := by
  unfold mixedIndependentRawFrameAngleMatrix mixedIndependentRawFirstFrame
    mixedIndependentRawSecondFrame CenterRaw.secondStep CenterRaw.secondMetric
    CenterRaw.secondGradient CenterRaw.firstFrame CenterRaw.firstStep
    CenterRaw.initialMetric CenterRaw.initialGradient
  rfl

/-- Infrastructure I.16a: the canonical second low-eigenvector frame used by the
relative-frame slope has a reusable projection name. -/
def canonicalSecondFrame
    (θ : ℝ × ℝ × ℝ) (r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  EuclideanPlane.frame
    (RealSymmetric2.lowVector
      (independentRadiusSecondMetricTriple (θ, r)).1
      (independentRadiusSecondMetricTriple (θ, r)).2.1
      (independentRadiusSecondMetricTriple (θ, r)).2.2)

/- The zero-radius branch is kept as a separate rewrite so a punctured frame
   certificate never has to manufacture a low-denominator hypothesis at `r = 0`. -/

/-- Infrastructure I.16a: the canonical relative-frame slope vanishes at zero radius. -/
theorem canonicalFrameSlope_zero (θ : ℝ × ℝ × ℝ) :
    canonicalFrameSlope θ 0 = 0 := by
  simp [canonicalFrameSlope, canonicalFrameSlopeFirstE,
    canonicalFrameSlopeFirstX, canonicalFrameSlopeSecondE,
    canonicalFrameSlopeSecondX, independentRadiusFirstMetricTriple_zero,
    independentRadiusSecondMetricTriple_zero,
    independentRadiusFirstSpectral_zero, independentRadiusSecondSpectral_zero]

/-- Infrastructure I.16a: the raw and canonical relative-frame slopes agree on
the zero-radius branch, before any punctured denominator certificate is used. -/
theorem mixedIndependentRawFrameAngleSlopeAlongInput_zero_eq_canonicalFrameSlope
    (θ : ℝ × ℝ × ℝ) :
    mixedIndependentRawFrameAngleSlopeAlongInput θ 0 = canonicalFrameSlope θ 0 := by
  rw [mixedIndependentRawFrameAngleSlopeAlongInput_zero, canonicalFrameSlope_zero]

/-- Infrastructure I.16a: multiplying a planar matrix by a nonzero scalar does
not change its lower-left/upper-left entry ratio, including a zero denominator. -/
theorem matrixEntryRatio_eq_of_smul
    (σ : ℝ) (hσ : σ ≠ 0) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    (σ • M) 1 0 / (σ • M) 0 0 = M 1 0 / M 0 0 := by
  by_cases hM : M 0 0 = 0
  · simp [hM]
  · simp only [smul_eq_mul, Matrix.smul_apply]
    field_simp [hσ, hM]

/-- Infrastructure I.16a: signed choices of the two oriented frames preserve
the relative-frame entry ratio. -/
theorem matrixProductEntryRatio_eq_of_signedFrames
    {R₁ R₂ F₁ F₂ : Matrix (Fin 2) (Fin 2) ℝ}
    (h₁ : R₁ = F₁ ∨ R₁ = -F₁)
    (h₂ : R₂ = F₂ ∨ R₂ = -F₂) :
    (R₁ * R₂) 1 0 / (R₁ * R₂) 0 0 =
      (F₁ * F₂) 1 0 / (F₁ * F₂) 0 0 := by
  rcases h₁ with h₁ | h₁
  · rcases h₂ with h₂ | h₂
    · rw [h₁, h₂]
    · rw [h₁, h₂]
      have hprod : F₁ * -F₂ = (-1 : ℝ) • (F₁ * F₂) := by
        ext i j
        simp [Matrix.smul_apply]
      rw [hprod]
      have hneg : (-1 : ℝ) ≠ 0 := by norm_num
      exact matrixEntryRatio_eq_of_smul (-1) hneg (F₁ * F₂)
  · rcases h₂ with h₂ | h₂
    · rw [h₁, h₂]
      have hprod : -F₁ * F₂ = (-1 : ℝ) • (F₁ * F₂) := by
        ext i j
        simp [Matrix.smul_apply]
      rw [hprod]
      have hneg : (-1 : ℝ) ≠ 0 := by norm_num
      exact matrixEntryRatio_eq_of_smul (-1) hneg (F₁ * F₂)
    · rw [h₁, h₂]
      simp only [Matrix.neg_mul, Matrix.mul_neg]
      simp

/-- Infrastructure I.16a: the fixed low-vector frame product has the explicit
entry-ratio formula used by the canonical slope quotient. -/
theorem lowFrameProduct_entryRatio
    {a₁ b₁ d₁ a₂ b₂ d₂ : ℝ}
    (h₁ : RealSymmetric2.lowDenom a₁ b₁ d₁ ≠ 0)
    (h₂ : RealSymmetric2.lowDenom a₂ b₂ d₂ ≠ 0) :
    (EuclideanPlane.frame (RealSymmetric2.lowVector a₁ b₁ d₁) *
        EuclideanPlane.frame (RealSymmetric2.lowVector a₂ b₂ d₂)) 1 0 /
      (EuclideanPlane.frame (RealSymmetric2.lowVector a₁ b₁ d₁) *
        EuclideanPlane.frame (RealSymmetric2.lowVector a₂ b₂ d₂)) 0 0 =
      (-(b₁ * (d₂ - RealSymmetric2.low a₂ b₂ d₂) +
          (d₁ - RealSymmetric2.low a₁ b₁ d₁) * b₂) /
        ((d₁ - RealSymmetric2.low a₁ b₁ d₁) *
            (d₂ - RealSymmetric2.low a₂ b₂ d₂) - b₁ * b₂)) := by
  unfold EuclideanPlane.frame
  simp only [Matrix.mul_apply, Fin.sum_univ_two, EuclideanPlane.perp_apply,
    RealSymmetric2.lowVector, RealSymmetric2.lowRaw, PiLp.smul_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul]
  field_simp [h₁, h₂]
  ring

/-- Infrastructure I.16a: after the physical low eigenvalues are normalized by
their radius factors, the canonical frame product realizes `canonicalFrameSlope`. -/
theorem canonicalFrameProduct_entryRatio_eq_canonicalFrameSlope
    (θ : ℝ × ℝ × ℝ) (r : ℝ)
    (h₁ : RealSymmetric2.lowDenom
      (independentRadiusFirstMetricTriple (θ, r)).1
      (independentRadiusFirstMetricTriple (θ, r)).2.1
      (independentRadiusFirstMetricTriple (θ, r)).2.2 ≠ 0)
    (h₂ : RealSymmetric2.lowDenom
      (independentRadiusSecondMetricTriple (θ, r)).1
      (independentRadiusSecondMetricTriple (θ, r)).2.1
      (independentRadiusSecondMetricTriple (θ, r)).2.2 ≠ 0)
    (hlow₁ : RealSymmetric2.low
      (independentRadiusFirstMetricTriple (θ, r)).1
      (independentRadiusFirstMetricTriple (θ, r)).2.1
      (independentRadiusFirstMetricTriple (θ, r)).2.2 =
        r ^ 2 * (independentRadiusFirstSpectral (θ, r)).1)
    (hlow₂ : RealSymmetric2.low
      (independentRadiusSecondMetricTriple (θ, r)).1
      (independentRadiusSecondMetricTriple (θ, r)).2.1
      (independentRadiusSecondMetricTriple (θ, r)).2.2 =
        r ^ 2 * (independentRadiusSecondSpectral (θ, r)).1) :
    (canonicalFirstFrame θ r * canonicalSecondFrame θ r) 1 0 /
      (canonicalFirstFrame θ r * canonicalSecondFrame θ r) 0 0 =
        canonicalFrameSlope θ r := by
  have hratio := lowFrameProduct_entryRatio
    (a₁ := (independentRadiusFirstMetricTriple (θ, r)).1)
    (b₁ := (independentRadiusFirstMetricTriple (θ, r)).2.1)
    (d₁ := (independentRadiusFirstMetricTriple (θ, r)).2.2)
    (a₂ := (independentRadiusSecondMetricTriple (θ, r)).1)
    (b₂ := (independentRadiusSecondMetricTriple (θ, r)).2.1)
    (d₂ := (independentRadiusSecondMetricTriple (θ, r)).2.2) h₁ h₂
  rw [hlow₁, hlow₂] at hratio
  simpa only [canonicalFirstFrame, canonicalSecondFrame,
    canonicalFrameSlope, canonicalFrameSlopeFirstE,
    canonicalFrameSlopeFirstX, canonicalFrameSlopeSecondE,
    canonicalFrameSlopeSecondX] using hratio

/-- Infrastructure I.16a: a signed raw-frame certificate transports the raw
relative-frame slope to the canonical frame-coordinate quotient. The frame and
low-eigenvalue hypotheses are explicit so a source proof can discharge them
without hiding a chart singularity behind a global definition. -/
theorem mixedIndependentRawFrameAngleSlope_eq_canonicalFrameSlope_of_signedFrameData
    (θ : ℝ × ℝ × ℝ) (r : ℝ)
    (hfirst :
      mixedIndependentRawFirstFrame θ.1 r
          (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r) =
          canonicalFirstFrame θ r ∨
      mixedIndependentRawFirstFrame θ.1 r
          (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r) =
          -canonicalFirstFrame θ r)
    (hsecond :
      mixedIndependentRawSecondFrame θ.1 r
          (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r) =
          canonicalSecondFrame θ r ∨
      mixedIndependentRawSecondFrame θ.1 r
          (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r) =
          -canonicalSecondFrame θ r)
    (h₁ : RealSymmetric2.lowDenom
      (independentRadiusFirstMetricTriple (θ, r)).1
      (independentRadiusFirstMetricTriple (θ, r)).2.1
      (independentRadiusFirstMetricTriple (θ, r)).2.2 ≠ 0)
    (h₂ : RealSymmetric2.lowDenom
      (independentRadiusSecondMetricTriple (θ, r)).1
      (independentRadiusSecondMetricTriple (θ, r)).2.1
      (independentRadiusSecondMetricTriple (θ, r)).2.2 ≠ 0)
    (hlow₁ : RealSymmetric2.low
      (independentRadiusFirstMetricTriple (θ, r)).1
      (independentRadiusFirstMetricTriple (θ, r)).2.1
      (independentRadiusFirstMetricTriple (θ, r)).2.2 =
        r ^ 2 * (independentRadiusFirstSpectral (θ, r)).1)
    (hlow₂ : RealSymmetric2.low
      (independentRadiusSecondMetricTriple (θ, r)).1
      (independentRadiusSecondMetricTriple (θ, r)).2.1
      (independentRadiusSecondMetricTriple (θ, r)).2.2 =
        r ^ 2 * (independentRadiusSecondSpectral (θ, r)).1) :
    mixedIndependentRawFrameAngleSlopeAlongInput θ r =
      canonicalFrameSlope θ r := by
  have hmatrix := mixedIndependentRawFrameAngleMatrix_eq_frameProduct
    θ.1 r (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r)
  unfold mixedIndependentRawFrameAngleSlopeAlongInput
    mixedIndependentRawFrameAngleSlope
  rw [hmatrix]
  have hratio := matrixProductEntryRatio_eq_of_signedFrames hfirst hsecond
  rw [hratio]
  exact canonicalFrameProduct_entryRatio_eq_canonicalFrameSlope
    θ r h₁ h₂ hlow₁ hlow₂

/-- Infrastructure I.16a: the mixed center bracket agrees pointwise with the
canonical weighted center-bracket normal form. -/
theorem mixedCenterBracket_eq_canonicalCenterBracket
    (θ : ℝ × ℝ × ℝ) (r : ℝ) :
    mixedCenterBracket θ r = canonicalCenterBracket θ r := by
  unfold mixedCenterBracket canonicalCenterBracket canonicalFirstFrame
    canonicalFirstNormalizedDisplacement canonicalSecondNormalizedDisplacement
    centerSecondDisplacementLow centerSecondDisplacementHigh
    centerSecondDisplacementGradientLow centerSecondDisplacementGradientHigh
  rw [WeightedCenterBracket.coord_zero_apply]
  simp [CenterRaw.firstNormalizedDisplacement,
    CenterRaw.secondNormalizedDisplacement, input]

/-- Infrastructure I.16a: the joint mixed center-bracket evaluator is equal
to the joint canonical normal form, with the product coordinates preserved. -/
theorem mixedCenterBracket_uncurry_eq_canonicalCenterBracket :
    Function.uncurry mixedCenterBracket =
      Function.uncurry canonicalCenterBracket := by
  funext z
  exact mixedCenterBracket_eq_canonicalCenterBracket z.1 z.2

/-- Infrastructure I.16a: the canonical quadratic germ transports to the
mixed center bracket without changing either radius coefficient. -/
theorem mixedCenterBracket_quadraticGerm
    (θ : ℝ × ℝ × ℝ) :
    HasQuadraticGerm (mixedCenterBracket θ) 0
      (centerBracketCoefficient θ)
      (canonicalCenterBracketQuadraticCoeff θ
        (centerSecondDisplacementScaleLinearCoeff θ)
        (centerSecondDisplacementScaleQuadraticCoeff θ)) := by
  have hbracket : mixedCenterBracket θ = canonicalCenterBracket θ := by
    funext r
    exact mixedCenterBracket_eq_canonicalCenterBracket θ r
  rw [hbracket]
  exact canonicalCenterBracket_quadraticGerm_of_centerScale θ

/-- Infrastructure I.16a: joint `C³` regularity of the canonical bracket
transfers to the mixed bracket through the public normal-form equality. -/
theorem mixedCenterBracket_contDiffAt_of_canonical
    {z₀ : (ℝ × ℝ × ℝ) × ℝ}
    (hregular : ContDiffAt ℝ 3
      (Function.uncurry canonicalCenterBracket) z₀) :
    ContDiffAt ℝ 3 (Function.uncurry mixedCenterBracket) z₀ := by
  rw [mixedCenterBracket_uncurry_eq_canonicalCenterBracket]
  exact hregular

/-- Helper for Infrastructure I.16a: the explicit independent-radius normal form is
`C³` at every parameter-radius base `(θ, 0)`, exposing the source regularity needed
by compact quadratic-remainder transport. -/
theorem mixedCenterBracket_contDiffAt_of_independentRadius
    (θ : ℝ × ℝ × ℝ) :
    ContDiffAt ℝ 3 (Function.uncurry mixedCenterBracket) (θ, 0) := by
  have hm := independentRadiusFirstMetricTriple_analyticAt θ
  have hframe (i j : Fin 2) : AnalyticAt ℝ
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
        (EuclideanPlane.frame
          (RealSymmetric2.lowVector
            (independentRadiusFirstMetricTriple z).1
            (independentRadiusFirstMetricTriple z).2.1
            (independentRadiusFirstMetricTriple z).2.2)) i j) (θ, 0) := by
    have houter := RealSymmetric2.analyticOnNhd_frame i j
      ((0, 0, 1) : ℝ × ℝ × ℝ) RealSymmetric2.diag_mem_lowChart
    rw [← independentRadiusFirstMetricTriple_zero θ] at houter
    have hcomp := houter.comp hm
    apply hcomp.congr
    filter_upwards [] with z
    rfl
  have hF00 := hframe 0 0
  have hF01 := hframe 0 1
  have hb : AnalyticAt ℝ
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ z.1.1) (θ, 0) :=
    analyticAt_fst.comp analyticAt_fst
  have hr : AnalyticAt ℝ
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ z.2) (θ, 0) := analyticAt_snd
  have hp : AnalyticAt ℝ
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ (input z.1 z.2).2.1) (θ, 0) := by
    change AnalyticAt ℝ
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
        2 + z.1.2.1 * z.1.1 * z.2) (θ, 0)
    have hp' : AnalyticAt ℝ
        (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ z.1.2.1) (θ, 0) :=
      analyticAt_fst.comp (analyticAt_snd.comp analyticAt_fst)
    have hb' : AnalyticAt ℝ
        (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ z.1.1) (θ, 0) :=
      analyticAt_fst.comp analyticAt_fst
    have hpoly : AnalyticAt ℝ
        (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
          2 + z.1.2.1 * z.1.1 * z.2) (θ, 0) := by
      have hconst : AnalyticAt ℝ
          (fun _ : (ℝ × ℝ × ℝ) × ℝ ↦ (2 : ℝ)) (θ, 0) := analyticAt_const
      have h := hconst.add ((hp'.mul hb').mul analyticAt_snd)
      apply h.congr
      filter_upwards [] with z
      rfl
    exact hpoly
  have hL : AnalyticAt ℝ
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
        (independentRadiusFirstSpectral z).1) (θ, 0) :=
    analyticAt_fst.comp (independentRadiusFirstSpectral_analyticAt θ)
  have hH : AnalyticAt ℝ
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
        (independentRadiusFirstSpectral z).2) (θ, 0) :=
    analyticAt_snd.comp (independentRadiusFirstSpectral_analyticAt θ)
  have hQ : AnalyticAt ℝ
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
        (independentRadiusFirstGradient z).1) (θ, 0) :=
    analyticAt_fst.comp (independentRadiusFirstGradient_analyticAt θ)
  have hU : AnalyticAt ℝ
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
        (independentRadiusFirstGradient z).2) (θ, 0) :=
    analyticAt_snd.comp (independentRadiusFirstGradient_analyticAt θ)
  let den : ((ℝ × ℝ × ℝ) × ℝ) → ℝ := fun z ↦
    1 + 2 * z.1.1 * z.2 + z.2 ^ 2
  let beta' : ((ℝ × ℝ × ℝ) × ℝ) → ℝ := fun z ↦
    z.2 * (independentRadiusFirstSpectral z).1 *
        (independentRadiusFirstGradient z).1 *
        (z.2 * (independentRadiusFirstSpectral z).1 *
            (independentRadiusFirstGradient z).1 -
          2 * z.1.1 * (independentRadiusFirstSpectral z).2 *
            (independentRadiusFirstGradient z).2) +
      (independentRadiusFirstSpectral z).2 *
        (independentRadiusFirstGradient z).2 *
        ((independentRadiusFirstSpectral z).2 *
            (independentRadiusFirstGradient z).2 -
          2 * z.1.1 * z.2 * (independentRadiusFirstSpectral z).1 *
            (independentRadiusFirstGradient z).1)
  have hden : AnalyticAt ℝ den (θ, 0) := by
    dsimp [den]
    fun_prop
  have hbeta : AnalyticAt ℝ beta' (θ, 0) := by
    dsimp [beta']
    fun_prop
  have hden0 : den (θ, 0) ≠ 0 := by
    simp [den]
  have hbeta0 : beta' (θ, 0) ≠ 0 := by
    simp [beta', independentRadiusFirstSpectral_zero θ,
      independentRadiusFirstGradient_zero θ]
  let alpha : ((ℝ × ℝ × ℝ) × ℝ) → ℝ := fun z ↦
    (-(1 / 3 : ℝ)) *
      ((independentRadiusFirstSpectral z).1 *
          (independentRadiusFirstGradient z).1 ^ 2 +
        (independentRadiusFirstSpectral z).2 *
          (independentRadiusFirstGradient z).2 ^ 2) / beta' z
  have halpha : AnalyticAt ℝ alpha (θ, 0) := by
    dsimp [alpha]
    have hnum := (hL.mul (hQ.pow 2)).add (hH.mul (hU.pow 2))
    exact (analyticAt_const.mul hnum).div hbeta hbeta0
  let u0 : ((ℝ × ℝ × ℝ) × ℝ) → ℝ := fun z ↦
    (-(2 / 3 : ℝ) * ((input z.1 z.2).2.1 + 1)) / den z
  have hu0 : AnalyticAt ℝ u0 (θ, 0) := by
    dsimp [u0]
    have hplus : AnalyticAt ℝ
        (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ (input z.1 z.2).2.1 + 1) (θ, 0) :=
      hp.add analyticAt_const
    have hscale : AnalyticAt ℝ
        (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
          (-(2 / 3 : ℝ)) * ((input z.1 z.2).2.1 + 1)) (θ, 0) := by
      have hconst : AnalyticAt ℝ
          (fun _ : (ℝ × ℝ × ℝ) × ℝ ↦ (-(2 / 3 : ℝ))) (θ, 0) :=
        analyticAt_const
      exact hconst.mul hplus
    exact hscale.div hden hden0
  let u10 : ((ℝ × ℝ × ℝ) × ℝ) → ℝ := fun z ↦
    alpha z * (z.2 * (independentRadiusFirstSpectral z).1 *
      (independentRadiusFirstGradient z).1)
  let u11 : ((ℝ × ℝ × ℝ) × ℝ) → ℝ := fun z ↦
    alpha z * ((independentRadiusFirstSpectral z).2 *
      (independentRadiusFirstGradient z).2)
  have hu10 : AnalyticAt ℝ u10 (θ, 0) := by
    dsimp [u10]
    exact halpha.mul (((hr.mul hL).mul hQ))
  have hu11 : AnalyticAt ℝ u11 (θ, 0) := by
    dsimp [u11]
    exact halpha.mul (hH.mul hU)
  have hsum := (hF00.mul hu11).add (hF01.mul hu10)
  have hscaled : AnalyticAt ℝ
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
        2 * ((EuclideanPlane.frame
          (RealSymmetric2.lowVector
            (independentRadiusFirstMetricTriple z).1
            (independentRadiusFirstMetricTriple z).2.1
            (independentRadiusFirstMetricTriple z).2.2)) 0 0 * u11 z +
          (EuclideanPlane.frame
            (RealSymmetric2.lowVector
              (independentRadiusFirstMetricTriple z).1
              (independentRadiusFirstMetricTriple z).2.1
              (independentRadiusFirstMetricTriple z).2.2)) 0 1 * u10 z)) (θ, 0) := by
    exact analyticAt_const.mul hsum
  have hbracket := hu0.neg.add hscaled
  have hbracket' : AnalyticAt ℝ
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ mixedCenterBracket z.1 z.2) (θ, 0) := by
    apply hbracket.congr
    filter_upwards [] with z
    simp [u0, u10, u11, mixedCenterBracket, input]
    ring
  exact hbracket'.contDiffAt (n := 3)

/-- Infrastructure I.16a: signed raw-frame data transport the coordinate-zero
full center displacement to the mixed bracket name used by the source. -/
theorem CenterRaw.fullCenterDisplacement_coord_zero_eq_mixedCenterBracket_of_signedFrameData
    {θ : ℝ × ℝ × ℝ} {r : ℝ}
    (horth :
      canonicalFirstFrame θ r * (canonicalFirstFrame θ r).transpose = 1)
    (hbranch :
      (CenterRaw.firstFrame θ.1 (input θ r) = canonicalFirstFrame θ r ∧
        (CenterRaw.secondStep θ.1 (input θ r)).2.2 =
          r • canonicalSecondNormalizedDisplacement θ r) ∨
      (CenterRaw.firstFrame θ.1 (input θ r) = -canonicalFirstFrame θ r ∧
        (CenterRaw.secondStep θ.1 (input θ r)).2.2 =
          r • (-canonicalSecondNormalizedDisplacement θ r)))
    (hfirst :
      (CenterRaw.firstStep θ.1 (input θ r)).2.2 =
        r • canonicalFirstNormalizedDisplacement θ r) :
    (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 =
      (θ.1 * r) * mixedCenterBracket θ r := by
  have hcanonical :=
    CenterRaw.fullCenterDisplacement_coord_zero_eq_canonicalBracket_of_signedFrameData
      horth hbranch hfirst
  rw [mixedCenterBracket_eq_canonicalCenterBracket]
  exact hcanonical

/-- Infrastructure I.16a: signed raw-frame data transport the physical center
residual to the mixed bracket residual before denominator clearing. -/
theorem centerResidual_eq_controlRadius_mul_mixedCenterBracketResidual_of_signedFrameData
    {θ : ℝ × ℝ × ℝ} {r : ℝ}
    (horth :
      canonicalFirstFrame θ r * (canonicalFirstFrame θ r).transpose = 1)
    (hbranch :
      (CenterRaw.firstFrame θ.1 (input θ r) = canonicalFirstFrame θ r ∧
        (CenterRaw.secondStep θ.1 (input θ r)).2.2 =
          r • canonicalSecondNormalizedDisplacement θ r) ∨
      (CenterRaw.firstFrame θ.1 (input θ r) = -canonicalFirstFrame θ r ∧
        (CenterRaw.secondStep θ.1 (input θ r)).2.2 =
          r • (-canonicalSecondNormalizedDisplacement θ r)))
    (hfirst :
      (CenterRaw.firstStep θ.1 (input θ r)).2.2 =
        r • canonicalFirstNormalizedDisplacement θ r) :
    physicalCenterResidual θ r =
      (θ.1 * r) * (mixedCenterBracket θ r - centerBracketCoefficient θ * r) := by
  have hcanonical :=
    centerResidual_eq_controlRadius_mul_canonicalBracketResidual_of_signedFrameData
      horth hbranch hfirst
  rw [mixedCenterBracket_eq_canonicalCenterBracket]
  exact hcanonical

namespace MixedRaw

/-- Infrastructure I.16a: the second-leg denominator is strictly positive on
the mixed raw projection domain. -/
theorem secondDenominator_pos
    {θ : ℝ × ℝ × ℝ} {r : ℝ}
    (hdomain : mixedRawProjectionDomain θ r) :
    0 < r * (independentRadiusFirstSpectral (θ, r)).1 *
          (independentRadiusFirstGradient (θ, r)).1 *
          (r * (independentRadiusFirstSpectral (θ, r)).1 *
              (independentRadiusFirstGradient (θ, r)).1 -
            2 * θ.1 * (independentRadiusFirstSpectral (θ, r)).2 *
              (independentRadiusFirstGradient (θ, r)).2) +
        (independentRadiusFirstSpectral (θ, r)).2 *
          (independentRadiusFirstGradient (θ, r)).2 *
          ((independentRadiusFirstSpectral (θ, r)).2 *
              (independentRadiusFirstGradient (θ, r)).2 -
            2 * θ.1 * r * (independentRadiusFirstSpectral (θ, r)).1 *
              (independentRadiusFirstGradient (θ, r)).1) := by
  rcases hdomain with ⟨hr, hθ, hp, hh, hL, hH, hQ⟩
  let L := (independentRadiusFirstSpectral (θ, r)).1
  let H := (independentRadiusFirstSpectral (θ, r)).2
  let Q := (independentRadiusFirstGradient (θ, r)).1
  let U := (independentRadiusFirstGradient (θ, r)).2
  have hdiag : (Matrix.diagonal ![r ^ 2 * L, H] :
      Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i
    · exact mul_pos (sq_pos_of_ne_zero hr) hL
    · exact hH
  have hg : (![Q, r * U] : Fin 2 → ℝ) ≠ 0 := by
    intro hz
    have hz0 := congrArg (fun v : Fin 2 → ℝ ↦ v 0) hz
    have hQzero : Q = 0 := by
      simpa [Q] using hz0
    exact hQ hQzero
  have hcontrols := independentRadiusControlMatricesPosDef θ.1 hθ
  let z := DFP.AbstractSecantStep.ofMatrices
    (Matrix.diagonal ![r ^ 2 * L, H]) (![Q, r * U] : Fin 2 → ℝ)
    (TwoPhaseControls.second θ.1).matrix (TwoPhaseControls.second θ.1).tau
    hdiag hcontrols.2 (TwoPhaseControls.tau_pos θ.1 1) hg
  have henergy := z.preconditionedEnergy_pos
  have hidentity :
      z.preconditionedGradient ⬝ᵥ
          (Matrix.mulVec z.secantMatrix z.preconditionedGradient) =
        r ^ 2 * (r * L * Q * (r * L * Q - 2 * θ.1 * H * U) +
          H * U * (H * U - 2 * θ.1 * r * L * Q)) := by
    rw [z.preconditionedGradient_def]
    simp [z, DFP.AbstractSecantStep.ofMatrices, TwoPhaseControls.second_matrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  have hβ : 0 < r * L * Q * (r * L * Q - 2 * θ.1 * H * U) +
      H * U * (H * U - 2 * θ.1 * r * L * Q) := by
    rw [hidentity] at henergy
    exact pos_of_mul_pos_right henergy (sq_nonneg r)
  dsimp [L, H, Q, U] at hβ ⊢
  exact hβ

end MixedRaw

/-- Infrastructure I.16a: on the punctured projection domain, the raw first
frame is orthogonal after transporting the independent-radius step through
the oriented eigenframe. -/
theorem mixedRawFirstFrame_mul_transpose_of_projectionDomain
    (θ : ℝ × ℝ × ℝ) (r : ℝ) (hdomain : mixedRawProjectionDomain θ r) :
    let H₀ : Matrix (Fin 2) (Fin 2) ℝ :=
      Matrix.diagonal ![(input θ r).2.2 * (input θ r).2.1 * r ^ 2,
        (input θ r).2.2]
    let g₀ : Fin 2 → ℝ := ![(1 : ℝ), (input θ r).2.1 * r]
    let firstStep := rawObservableStep H₀ g₀ (TwoPhaseControls.first θ.1)
    let firstFrame := OrientedEigenframe.frame
      (firstStep.1 0 0) (firstStep.1 0 1) (firstStep.1 1 1)
      (WithLp.toLp 2 firstStep.2.1)
    firstFrame * firstFrame.transpose = 1 := by
  rcases hdomain with ⟨hr, hθ, hp, hh, hL, hH, hQ⟩
  let p : ℝ := (input θ r).2.1
  let h : ℝ := (input θ r).2.2
  let H₀ : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![h * p * r ^ 2, h]
  let g₀ : Fin 2 → ℝ := ![(1 : ℝ), p * r]
  have hinitial : H₀.PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i
    · exact mul_pos (mul_pos hh hp) (sq_pos_of_ne_zero hr)
    · exact hh
  have hcontrols := independentRadiusControlMatricesPosDef θ.1 hθ
  have hgradient : g₀ ≠ 0 := by
    intro hzero
    have hzeroFirst := congrArg (fun v : Fin 2 → ℝ ↦ v 0) hzero
    norm_num [g₀] at hzeroFirst
  have hfirstRaw := independentRawStep_first_eq θ.1 r p h hinitial hcontrols.1
    (TwoPhaseControls.tau_pos θ.1 0) hgradient hr
  let t₁ := independentFirstResiduals θ.1 r p h
  let M₁ := independentFirstMetric θ.1 r p h
  let v₁ := independentFirstGradient θ.1 r p
  let F₁ := EuclideanPlane.frame
    (RealSymmetric2.lowVector (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2)
  have hgradientFactors : independentRadiusFirstGradient (θ, r) =
      independentFirstGradientFactors θ.1 r p h := by
    rfl
  have hdenom : RealSymmetric2.lowDenom
      (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2 ≠ 0 := by
    intro hzero
    apply hQ
    rw [hgradientFactors]
    unfold independentFirstGradientFactors
    dsimp only
    rw [hzero]
    simp
  have hspecial : F₁ ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
    exact RealSymmetric2.frame_mem_specialOrthogonalGroup_of_lowDenom_ne_zero
      (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2 hdenom
  have hfixedOrth : F₁ * F₁.transpose = 1 :=
    (Matrix.mem_orthogonalGroup_iff (Fin 2) ℝ).mp
      (Matrix.mem_specialOrthogonalGroup_iff.mp hspecial).1
  have hmetric : (rawObservableStep H₀ g₀ (TwoPhaseControls.first θ.1)).1 = M₁ := by
    calc
      (rawObservableStep H₀ g₀ (TwoPhaseControls.first θ.1)).1 =
          (independentRawStep H₀ g₀ (TwoPhaseControls.first θ.1)).1 :=
        mixedRawObservableStep_metric_eq H₀ g₀ (TwoPhaseControls.first θ.1)
      _ = M₁ := congrArg Prod.fst hfirstRaw
  have hupdatedGradient :
      (rawObservableStep H₀ g₀ (TwoPhaseControls.first θ.1)).2.1 = v₁ := by
    calc
      (rawObservableStep H₀ g₀ (TwoPhaseControls.first θ.1)).2.1 =
          (independentRawStep H₀ g₀ (TwoPhaseControls.first θ.1)).2 :=
        mixedRawObservableStep_gradient_eq H₀ g₀ (TwoPhaseControls.first θ.1)
      _ = v₁ := congrArg Prod.snd hfirstRaw
  have hframe :
      OrientedEigenframe.frame (M₁ 0 0) (M₁ 0 1) (M₁ 1 1)
          (WithLp.toLp 2 v₁) = F₁ ∨
        OrientedEigenframe.frame (M₁ 0 0) (M₁ 0 1) (M₁ 1 1)
          (WithLp.toLp 2 v₁) = -F₁ := by
    rcases orientedEigenframe_eq_fixed_or_neg (M₁ 0 0) (M₁ 0 1) (M₁ 1 1)
      (WithLp.toLp 2 v₁) with hframe | hframe
    · left
      simpa [F₁, M₁, independentFirstMetric, t₁] using hframe
    · right
      simpa [F₁, M₁, independentFirstMetric, t₁] using hframe
  dsimp only
  change
    let firstStep := rawObservableStep H₀ g₀ (TwoPhaseControls.first θ.1)
    let firstFrame := OrientedEigenframe.frame
      (firstStep.1 0 0) (firstStep.1 0 1) (firstStep.1 1 1)
      (WithLp.toLp 2 firstStep.2.1)
    firstFrame * firstFrame.transpose = 1
  dsimp only
  rw [hmetric, hupdatedGradient]
  rcases hframe with hframe | hframe
  · rwa [hframe]
  · rw [hframe]
    simpa only [Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg] using
      hfixedOrth

/-- Infrastructure I.16a: the raw first step has the canonical diagonal metric
and gradient coordinates, with the same global orientation sign as its frame. -/
theorem mixedRawFirstCanonicalFrameData
    (θ : ℝ × ℝ × ℝ) (r : ℝ)
    (hdomain : mixedRawProjectionDomain θ r) :
    let L := (independentRadiusFirstSpectral (θ, r)).1
    let H := (independentRadiusFirstSpectral (θ, r)).2
    let Q := (independentRadiusFirstGradient (θ, r)).1
    let U := (independentRadiusFirstGradient (θ, r)).2
    let F := EuclideanPlane.frame
      (RealSymmetric2.lowVector
        (independentRadiusFirstMetricTriple (θ, r)).1
        (independentRadiusFirstMetricTriple (θ, r)).2.1
        (independentRadiusFirstMetricTriple (θ, r)).2.2)
    (CenterRaw.firstFrame θ.1 (input θ r) = F ∧
        F.transpose * (CenterRaw.firstStep θ.1 (input θ r)).1 * F =
          Matrix.diagonal ![r ^ 2 * L, H] ∧
        F.transpose.mulVec (CenterRaw.firstStep θ.1 (input θ r)).2.1 =
          ![Q, r * U]) ∨
      (CenterRaw.firstFrame θ.1 (input θ r) = -F ∧
        (-F).transpose * (CenterRaw.firstStep θ.1 (input θ r)).1 * (-F) =
          Matrix.diagonal ![r ^ 2 * L, H] ∧
        (-F).transpose.mulVec (CenterRaw.firstStep θ.1 (input θ r)).2.1 =
          -![Q, r * U]) := by
  rcases hdomain with ⟨hr, hθ, hp, hh, hL, hH, hQ⟩
  let p : ℝ := (input θ r).2.1
  let h : ℝ := (input θ r).2.2
  let H₀ : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![h * p * r ^ 2, h]
  let g₀ : Fin 2 → ℝ := ![(1 : ℝ), p * r]
  let t₁ := independentFirstResiduals θ.1 r p h
  let M₁ := independentFirstMetric θ.1 r p h
  let v₁ := independentFirstGradient θ.1 r p
  let F₁ := EuclideanPlane.frame
    (RealSymmetric2.lowVector (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2)
  have hinitial : H₀.PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i
    · exact mul_pos (mul_pos hh hp) (sq_pos_of_ne_zero hr)
    · exact hh
  have hcontrols := independentRadiusControlMatricesPosDef θ.1 hθ
  have hgradient : g₀ ≠ 0 := by
    intro hz
    have hz0 := congrArg (fun v : Fin 2 → ℝ ↦ v 0) hz
    norm_num [g₀] at hz0
  have hfirstRaw := independentRawStep_first_eq θ.1 r p h hinitial hcontrols.1
    (TwoPhaseControls.tau_pos θ.1 0) hgradient hr
  have hmetric : (CenterRaw.firstStep θ.1 (input θ r)).1 = M₁ := by
    calc
      (CenterRaw.firstStep θ.1 (input θ r)).1 =
          (independentRawStep H₀ g₀ (TwoPhaseControls.first θ.1)).1 := by
        rfl
      _ = M₁ := by simpa [M₁] using congrArg Prod.fst hfirstRaw
  have hupdatedGradient :
      (CenterRaw.firstStep θ.1 (input θ r)).2.1 = v₁ := by
    calc
      (CenterRaw.firstStep θ.1 (input θ r)).2.1 =
          (independentRawStep H₀ g₀ (TwoPhaseControls.first θ.1)).2 := by
        rfl
      _ = v₁ := by simpa [v₁] using congrArg Prod.snd hfirstRaw
  have hspectral : independentRadiusFirstSpectral (θ, r) =
      independentFirstSpectralFactors θ.1 r p h := by
    rfl
  have hgradientFactors : independentRadiusFirstGradient (θ, r) =
      independentFirstGradientFactors θ.1 r p h := by
    rfl
  have hdenom : RealSymmetric2.lowDenom
      (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2 ≠ 0 := by
    intro hz
    apply hQ
    rw [hgradientFactors]
    unfold independentFirstGradientFactors
    dsimp only
    rw [hz]
    simp
  have hhigh : RealSymmetric2.high
      (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2 ≠ 0 := by
    have hpos : 0 < RealSymmetric2.high
        (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2 := by
      simpa [hH, hspectral, independentFirstSpectralFactors, t₁] using hH
    exact ne_of_gt hpos
  have hlow : RealSymmetric2.low
      (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2 =
      r ^ 2 * (independentRadiusFirstSpectral (θ, r)).1 := by
    rw [low_eq_radiusSq_mul_detFactor r t₁.1 t₁.2.1 t₁.2.2 hhigh]
    simp [hspectral, independentFirstSpectralFactors, t₁]
  have hdiag : F₁.transpose * M₁ * F₁ =
      Matrix.diagonal ![r ^ 2 * (independentRadiusFirstSpectral (θ, r)).1,
        (independentRadiusFirstSpectral (θ, r)).2] := by
    have hmetric' : M₁ = RealSymmetric2.matrix
        (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2 := by
      ext i j
      fin_cases i
      · fin_cases j
        · rfl
        · rfl
      · fin_cases j
        · rfl
        · rfl
    rw [hmetric', RealSymmetric2.frame_diagonalizes_of_lowDenom_ne_zero
      (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2 hdenom]
    simp [hspectral, independentFirstSpectralFactors, t₁, hlow]
  have hF₁ : F₁ = EuclideanPlane.frame
      (RealSymmetric2.lowVector
        (independentRadiusFirstMetricTriple (θ, r)).1
        (independentRadiusFirstMetricTriple (θ, r)).2.1
        (independentRadiusFirstMetricTriple (θ, r)).2.2) := by
    rfl
  have hcoords : F₁.transpose.mulVec v₁ =
      ![(independentRadiusFirstGradient (θ, r)).1,
        r * (independentRadiusFirstGradient (θ, r)).2] := by
    have hraw := lowFrame_transpose_mulVec
      (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2
      (independentFirstGradientResiduals θ.1 r p).1
      (r * (independentFirstGradientResiduals θ.1 r p).2)
    have hshape : F₁.transpose.mulVec v₁ =
        (EuclideanPlane.frame (RealSymmetric2.lowVector
          (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2)).transpose.mulVec
          ![(independentFirstGradientResiduals θ.1 r p).1,
            r * (independentFirstGradientResiduals θ.1 r p).2] := by
      rfl
    rw [hshape, hraw]
    ext i
    fin_cases i
    · simp [hgradientFactors, independentFirstGradientFactors, t₁]
      ring
    · simp [hgradientFactors, independentFirstGradientFactors, t₁]
      ring
  have hframe :
      OrientedEigenframe.frame (M₁ 0 0) (M₁ 0 1) (M₁ 1 1) (WithLp.toLp 2 v₁) = F₁ ∨
      OrientedEigenframe.frame (M₁ 0 0) (M₁ 0 1) (M₁ 1 1) (WithLp.toLp 2 v₁) = -F₁ := by
    rcases orientedEigenframe_eq_fixed_or_neg (M₁ 0 0) (M₁ 0 1) (M₁ 1 1)
      (WithLp.toLp 2 v₁) with hframe | hframe
    · left
      simpa [F₁, M₁, independentFirstMetric, t₁] using hframe
    · right
      simpa [F₁, M₁, independentFirstMetric, t₁] using hframe
  dsimp only
  have hframe' := hframe
  rw [← hmetric, ← hupdatedGradient] at hframe'
  have hframe'' :
      CenterRaw.firstFrame θ.1 (input θ r) = F₁ ∨
        CenterRaw.firstFrame θ.1 (input θ r) = -F₁ := by
    simpa [CenterRaw.firstFrame, CenterRaw.firstStep] using hframe'
  have hdiag' : F₁.transpose *
      (CenterRaw.firstStep θ.1 (input θ r)).1 * F₁ =
      Matrix.diagonal ![r ^ 2 * (independentRadiusFirstSpectral (θ, r)).1,
        (independentRadiusFirstSpectral (θ, r)).2] := by
    simpa [hmetric] using hdiag
  have hcoords' : F₁.transpose.mulVec
      (CenterRaw.firstStep θ.1 (input θ r)).2.1 =
      ![(independentRadiusFirstGradient (θ, r)).1,
        r * (independentRadiusFirstGradient (θ, r)).2] := by
    simpa [hupdatedGradient] using hcoords
  rcases hframe'' with hframe | hframe
  · left
    refine ⟨hframe, ?_, ?_⟩
    · rw [← hF₁]
      exact hdiag'
    · rw [← hF₁]
      exact hcoords'
  · right
    refine ⟨hframe, ?_, ?_⟩
    · rw [← hF₁]
      simpa only [Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg] using hdiag'
    · have hcoordsCanonical := hcoords'
      rw [hF₁] at hcoordsCanonical
      rw [Matrix.transpose_neg, Matrix.neg_mulVec, hcoordsCanonical]

/-- Infrastructure I.16a: the raw second displacement is the canonical
radius-normalized displacement, with the first-frame orientation deciding the
common sign. -/
theorem mixedRawSecondDisplacement_eq_signedCanonical
    (θ : ℝ × ℝ × ℝ) (r : ℝ)
    (hdomain : mixedRawProjectionDomain θ r) :
    let L := (independentRadiusFirstSpectral (θ, r)).1
    let H := (independentRadiusFirstSpectral (θ, r)).2
    let Q := (independentRadiusFirstGradient (θ, r)).1
    let U := (independentRadiusFirstGradient (θ, r)).2
    let F := EuclideanPlane.frame
      (RealSymmetric2.lowVector
        (independentRadiusFirstMetricTriple (θ, r)).1
        (independentRadiusFirstMetricTriple (θ, r)).2.1
        (independentRadiusFirstMetricTriple (θ, r)).2.2)
    (CenterRaw.firstFrame θ.1 (input θ r) = F ∧
        (CenterRaw.secondStep θ.1 (input θ r)).2.2 =
          r • CenterRaw.secondNormalizedDisplacement θ.1 r L H Q U) ∨
      (CenterRaw.firstFrame θ.1 (input θ r) = -F ∧
        (CenterRaw.secondStep θ.1 (input θ r)).2.2 =
          r • (-CenterRaw.secondNormalizedDisplacement θ.1 r L H Q U)) := by
  have hfirst := mixedRawFirstCanonicalFrameData θ r hdomain
  dsimp only at hfirst ⊢
  rcases hdomain with ⟨hr, hθ, hp, hh, hL, hH, hQ⟩
  rcases hfirst with ⟨hframe, hdiag, hgrad⟩ | ⟨hframe, hdiag, hgrad⟩
  · have hβpos := MixedRaw.secondDenominator_pos
      (θ := θ) (r := r) ⟨hr, hθ, hp, hh, hL, hH, hQ⟩
    have hβne :
        r * (independentRadiusFirstSpectral (θ, r)).1 *
              (independentRadiusFirstGradient (θ, r)).1 *
              (r * (independentRadiusFirstSpectral (θ, r)).1 *
                  (independentRadiusFirstGradient (θ, r)).1 -
                2 * θ.1 * (independentRadiusFirstSpectral (θ, r)).2 *
                  (independentRadiusFirstGradient (θ, r)).2) +
            (independentRadiusFirstSpectral (θ, r)).2 *
              (independentRadiusFirstGradient (θ, r)).2 *
              ((independentRadiusFirstSpectral (θ, r)).2 *
                  (independentRadiusFirstGradient (θ, r)).2 -
                2 * θ.1 * r * (independentRadiusFirstSpectral (θ, r)).1 *
                  (independentRadiusFirstGradient (θ, r)).1) ≠ 0 :=
      ne_of_gt hβpos
    have hone : (1 : ℝ) ≠ 0 := by norm_num
    have hden : (1 : ℝ) ^ 2 * r ^ 2 *
        (r * (independentRadiusFirstSpectral (θ, r)).1 *
              (independentRadiusFirstGradient (θ, r)).1 *
              (r * (independentRadiusFirstSpectral (θ, r)).1 *
                  (independentRadiusFirstGradient (θ, r)).1 -
                2 * θ.1 * (independentRadiusFirstSpectral (θ, r)).2 *
                  (independentRadiusFirstGradient (θ, r)).2) +
            (independentRadiusFirstSpectral (θ, r)).2 *
              (independentRadiusFirstGradient (θ, r)).2 *
              ((independentRadiusFirstSpectral (θ, r)).2 *
                  (independentRadiusFirstGradient (θ, r)).2 -
                2 * θ.1 * r * (independentRadiusFirstSpectral (θ, r)).1 *
                  (independentRadiusFirstGradient (θ, r)).1)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hone) (pow_ne_zero 2 hr)) hβne
    have hmetricSecond : CenterRaw.secondMetric θ.1 (input θ r) =
        Matrix.diagonal ![r ^ 2 * (independentRadiusFirstSpectral (θ, r)).1,
          (independentRadiusFirstSpectral (θ, r)).2] := by
      simpa [CenterRaw.secondMetric, hframe] using hdiag
    have hgradientSecond : CenterRaw.secondGradient θ.1 (input θ r) =
        (1 : ℝ) • ![(independentRadiusFirstGradient (θ, r)).1,
          r * (independentRadiusFirstGradient (θ, r)).2] := by
      simpa [CenterRaw.secondGradient, hframe] using hgrad
    have hdisp := CenterRaw.secondStep_displacement_eq_radius_smul
      θ.1 r (independentRadiusFirstSpectral (θ, r)).1
      (independentRadiusFirstSpectral (θ, r)).2
      (independentRadiusFirstGradient (θ, r)).1
      (independentRadiusFirstGradient (θ, r)).2 1 (input θ r)
      hmetricSecond hgradientSecond hden
    have hdisplacement :
        (CenterRaw.secondStep θ.1 (input θ r)).2.2 =
          r • CenterRaw.secondNormalizedDisplacement θ.1 r
            (independentRadiusFirstSpectral (θ, r)).1
            (independentRadiusFirstSpectral (θ, r)).2
            (independentRadiusFirstGradient (θ, r)).1
            (independentRadiusFirstGradient (θ, r)).2 := by
      simpa only [one_smul] using hdisp
    exact Or.inl ⟨hframe, hdisplacement⟩
  · have hβpos := MixedRaw.secondDenominator_pos
      (θ := θ) (r := r) ⟨hr, hθ, hp, hh, hL, hH, hQ⟩
    have hβne :
        r * (independentRadiusFirstSpectral (θ, r)).1 *
              (independentRadiusFirstGradient (θ, r)).1 *
              (r * (independentRadiusFirstSpectral (θ, r)).1 *
                  (independentRadiusFirstGradient (θ, r)).1 -
                2 * θ.1 * (independentRadiusFirstSpectral (θ, r)).2 *
                  (independentRadiusFirstGradient (θ, r)).2) +
            (independentRadiusFirstSpectral (θ, r)).2 *
              (independentRadiusFirstGradient (θ, r)).2 *
              ((independentRadiusFirstSpectral (θ, r)).2 *
                  (independentRadiusFirstGradient (θ, r)).2 -
                2 * θ.1 * r * (independentRadiusFirstSpectral (θ, r)).1 *
                  (independentRadiusFirstGradient (θ, r)).1) ≠ 0 :=
      ne_of_gt hβpos
    have hminusOneSq : (-1 : ℝ) ^ 2 = 1 := by norm_num
    have hden : (-1 : ℝ) ^ 2 * r ^ 2 *
        (r * (independentRadiusFirstSpectral (θ, r)).1 *
              (independentRadiusFirstGradient (θ, r)).1 *
              (r * (independentRadiusFirstSpectral (θ, r)).1 *
                  (independentRadiusFirstGradient (θ, r)).1 -
                2 * θ.1 * (independentRadiusFirstSpectral (θ, r)).2 *
                  (independentRadiusFirstGradient (θ, r)).2) +
            (independentRadiusFirstSpectral (θ, r)).2 *
              (independentRadiusFirstGradient (θ, r)).2 *
              ((independentRadiusFirstSpectral (θ, r)).2 *
                  (independentRadiusFirstGradient (θ, r)).2 -
                2 * θ.1 * r * (independentRadiusFirstSpectral (θ, r)).1 *
                  (independentRadiusFirstGradient (θ, r)).1)) ≠ 0 := by
      rw [hminusOneSq]
      simpa only [one_mul] using
        (mul_ne_zero (pow_ne_zero 2 hr) hβne)
    have hmetricSecond : CenterRaw.secondMetric θ.1 (input θ r) =
        Matrix.diagonal ![r ^ 2 * (independentRadiusFirstSpectral (θ, r)).1,
          (independentRadiusFirstSpectral (θ, r)).2] := by
      simpa [CenterRaw.secondMetric, hframe] using hdiag
    have hgradientSecond : CenterRaw.secondGradient θ.1 (input θ r) =
        (-1 : ℝ) • ![(independentRadiusFirstGradient (θ, r)).1,
          r * (independentRadiusFirstGradient (θ, r)).2] := by
      simpa [CenterRaw.secondGradient, hframe, neg_smul] using hgrad
    have hdisp := CenterRaw.secondStep_displacement_eq_radius_smul
      θ.1 r (independentRadiusFirstSpectral (θ, r)).1
      (independentRadiusFirstSpectral (θ, r)).2
      (independentRadiusFirstGradient (θ, r)).1
      (independentRadiusFirstGradient (θ, r)).2 (-1) (input θ r)
      hmetricSecond hgradientSecond hden
    have hdisplacement :
        (CenterRaw.secondStep θ.1 (input θ r)).2.2 =
          r • (-CenterRaw.secondNormalizedDisplacement θ.1 r
            (independentRadiusFirstSpectral (θ, r)).1
            (independentRadiusFirstSpectral (θ, r)).2
            (independentRadiusFirstGradient (θ, r)).1
            (independentRadiusFirstGradient (θ, r)).2) := by
      calc
        (CenterRaw.secondStep θ.1 (input θ r)).2.2 =
            (-1 : ℝ) • (r •
              CenterRaw.secondNormalizedDisplacement θ.1 r
                (independentRadiusFirstSpectral (θ, r)).1
                (independentRadiusFirstSpectral (θ, r)).2
                (independentRadiusFirstGradient (θ, r)).1
                (independentRadiusFirstGradient (θ, r)).2) := hdisp
        _ = r • (-CenterRaw.secondNormalizedDisplacement θ.1 r
                (independentRadiusFirstSpectral (θ, r)).1
                (independentRadiusFirstSpectral (θ, r)).2
                (independentRadiusFirstGradient (θ, r)).1
                (independentRadiusFirstGradient (θ, r)).2) := by
          rw [smul_smul]
          simp
    exact Or.inr ⟨hframe, hdisplacement⟩

/-- Infrastructure I.16a: a zero-radius or punctured projection point yields a
raw bracket certificate whose scalar bracket is the mixed canonical bracket. -/
theorem mixedRawBracketCertificate_of_projectionTube
    (θ : ℝ × ℝ × ℝ) (r : ℝ)
    (hbranch : r = 0 ∨ mixedRawProjectionDomain θ r) :
    ∃ certificate : CenterRaw.BracketCertificate θ.1 r (input θ r),
      certificate.bracket 0 = mixedCenterBracket θ r := by
  rcases hbranch with rfl | hdomain
  · let u₀ : Fin 2 → ℝ := CenterRaw.firstNormalizedDisplacement θ.1 0 2
    let u₁ : Fin 2 → ℝ := CenterRaw.secondNormalizedDisplacement θ.1 0 2 1 1 1
    have hinput : input θ 0 = (0, 2, 1) := by
      simp [input]
    have hframe : CenterRaw.firstFrame θ.1 (input θ 0) = 1 := by
      simpa [CenterRaw.firstFrame, CenterRaw.firstStep,
        CenterRaw.initialMetric, CenterRaw.initialGradient, hinput] using
        (rawObservableStep_zeroRadius_frame (TwoPhaseControls.first θ.1))
    have horth : CenterRaw.firstFrame θ.1 (input θ 0) *
        (CenterRaw.firstFrame θ.1 (input θ 0)).transpose = 1 := by
      rw [hframe]
      simp
    have hfirst : (CenterRaw.firstStep θ.1 (input θ 0)).2.2 = (0 : ℝ) • u₀ := by
      simp [u₀, CenterRaw.firstStep, CenterRaw.initialMetric,
        CenterRaw.initialGradient, hinput, rawObservableStep_zeroRadius_base]
    have hstep₁ := rawObservableStep_zeroRadius_scaled (1 * 2) 1 2
      (TwoPhaseControls.first θ.1)
    have hframe₁ := rawObservableStep_zeroRadius_scaled_frame (1 * 2) 2
      (TwoPhaseControls.first θ.1)
    have hsecond : (CenterRaw.secondStep θ.1 (input θ 0)).2.2 = (0 : ℝ) • u₁ := by
      rw [hinput]
      simp only [CenterRaw.secondStep, CenterRaw.secondMetric,
        CenterRaw.secondGradient, CenterRaw.firstFrame, CenterRaw.firstStep,
        CenterRaw.initialMetric, CenterRaw.initialGradient]
      rw [hframe₁, hstep₁]
      simp [u₁, rawObservableStep_zeroRadius_base]
    let certificate : CenterRaw.BracketCertificate θ.1 0 (input θ 0) :=
      { firstNormalized := u₀
        secondNormalized := u₁
        frame_orthogonal := horth
        first_displacement := hfirst
        second_displacement := hsecond }
    refine ⟨certificate, ?_⟩
    have hbracket : certificate.bracket 0 = 0 := by
      simp [certificate, CenterRaw.BracketCertificate.bracket, hframe, u₀, u₁,
        weightedCenterBracket, CenterRaw.firstNormalizedDisplacement,
        CenterRaw.secondNormalizedDisplacement]
      norm_num [div_eq_mul_inv]
    rw [hbracket]
    exact (mixedCenterBracket_zero θ).symm
  · rcases hdomain with ⟨hr, hθ, hp, hh, hL, hH, hQ⟩
    have hdomain' : mixedRawProjectionDomain θ r :=
      ⟨hr, hθ, hp, hh, hL, hH, hQ⟩
    let p : ℝ := (input θ r).2.1
    let h : ℝ := (input θ r).2.2
    let u₀ : Fin 2 → ℝ := CenterRaw.firstNormalizedDisplacement θ.1 r p
    let u₁ : Fin 2 → ℝ := CenterRaw.secondNormalizedDisplacement θ.1 r
      (independentRadiusFirstSpectral (θ, r)).1
      (independentRadiusFirstSpectral (θ, r)).2
      (independentRadiusFirstGradient (θ, r)).1
      (independentRadiusFirstGradient (θ, r)).2
    have hdenom : 0 < 1 + 2 * θ.1 * r + r ^ 2 :=
      mixedFirstDisplacement_denominator_pos hdomain'
    have hden : h ^ 2 * p ^ 2 * r ^ 2 *
        (1 + 2 * θ.1 * r + r ^ 2) ≠ 0 := by
      exact mul_ne_zero
        (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (ne_of_gt hh))
          (pow_ne_zero 2 (ne_of_gt hp))) (pow_ne_zero 2 hr))
        (ne_of_gt hdenom)
    have horth : CenterRaw.firstFrame θ.1 (input θ r) *
        (CenterRaw.firstFrame θ.1 (input θ r)).transpose = 1 :=
      mixedRawFirstFrame_mul_transpose_of_projectionDomain θ r hdomain'
    have hfirst : (CenterRaw.firstStep θ.1 (input θ r)).2.2 = r • u₀ := by
        simpa [u₀, p, h, input, CenterRaw.firstStep, CenterRaw.initialMetric,
        CenterRaw.initialGradient] using
        CenterRaw.firstStep_displacement_eq_radius_smul θ.1 r p h hden
    rcases mixedRawSecondDisplacement_eq_signedCanonical θ r hdomain' with
      hplus | hminus
    · have hsecond : (CenterRaw.secondStep θ.1 (input θ r)).2.2 = r • u₁ := by
        simpa [u₁] using hplus.2
      let certificate : CenterRaw.BracketCertificate θ.1 r (input θ r) :=
        { firstNormalized := u₀
          secondNormalized := u₁
          frame_orthogonal := horth
          first_displacement := hfirst
          second_displacement := hsecond }
      refine ⟨certificate, ?_⟩
      have hbracket : certificate.bracket 0 = mixedCenterBracket θ r := by
        simp only [certificate, CenterRaw.BracketCertificate.bracket]
        rw [hplus.1]
        simp [u₀, u₁, p, mixedCenterBracket,
          CenterRaw.firstNormalizedDisplacement,
          CenterRaw.secondNormalizedDisplacement, weightedCenterBracket,
          Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        ring
      exact hbracket
    · have hsecond : (CenterRaw.secondStep θ.1 (input θ r)).2.2 = r • (-u₁) := by
        simpa [u₁] using hminus.2
      let certificate : CenterRaw.BracketCertificate θ.1 r (input θ r) :=
        { firstNormalized := u₀
          secondNormalized := -u₁
          frame_orthogonal := horth
          first_displacement := hfirst
          second_displacement := hsecond }
      refine ⟨certificate, ?_⟩
      have hcanonical : weightedCenterBracket
            (EuclideanPlane.frame
              (RealSymmetric2.lowVector
                (independentRadiusFirstMetricTriple (θ, r)).1
                (independentRadiusFirstMetricTriple (θ, r)).2.1
                (independentRadiusFirstMetricTriple (θ, r)).2.2)) u₀ u₁ 0 =
          mixedCenterBracket θ r := by
        simp [u₀, u₁, p, mixedCenterBracket,
          CenterRaw.firstNormalizedDisplacement,
          CenterRaw.secondNormalizedDisplacement, weightedCenterBracket,
          Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        ring
      rw [CenterRaw.BracketCertificate.bracket, hminus.1]
      rw [weightedCenterBracket_neg_neg]
      exact hcanonical

/-- Helper for Infrastructure I.16a: the punctured raw projection tube exposes the
coordinate-zero full-center displacement in the mixed canonical bracket
coordinates without retaining an existential certificate. -/
theorem mixedRaw_fullCenterDisplacement_coord_zero_eq_mixedCenterBracket
    (θ : ℝ × ℝ × ℝ) (r : ℝ)
    (hdomain : mixedRawProjectionDomain θ r) :
    (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 =
      (θ.1 * r) * mixedCenterBracket θ r := by
  obtain ⟨certificate, hcertificate⟩ :=
    mixedRawBracketCertificate_of_projectionTube θ r (Or.inr hdomain)
  have hraw := certificate.fullCenterDisplacement_coord_zero_eq_mul_bracket
  rw [hcertificate] at hraw
  exact hraw

/-- Helper for Infrastructure I.16a: the punctured raw projection tube transports the
physical center residual to the mixed canonical bracket remainder. -/
theorem mixedRaw_centerResidual_eq_mixedCenterBracketResidual
    (θ : ℝ × ℝ × ℝ) (r : ℝ)
    (hdomain : mixedRawProjectionDomain θ r) :
    physicalCenterResidual θ r =
      (θ.1 * r) * (mixedCenterBracket θ r - centerBracketCoefficient θ * r) := by
  obtain ⟨certificate, hcertificate⟩ :=
    mixedRawBracketCertificate_of_projectionTube θ r (Or.inr hdomain)
  have hres := certificate.centerResidual_eq_controlRadius_mul_bracketResidual
  rw [hcertificate] at hres
  simpa only [physicalCenterResidual] using hres

/-- Helper for Infrastructure I.16a: a punctured mixed bracket kernel identity gives the
denominator-cleared physical center residual in cubic form. -/
theorem mixedRaw_centerResidual_eq_cubicKernel
    {K : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    (θ : ℝ × ℝ × ℝ) (r : ℝ)
    (hdomain : mixedRawProjectionDomain θ r)
    (hkernel : mixedCenterBracket θ r - centerBracketCoefficient θ * r =
      r ^ 2 * K θ r) :
    physicalCenterResidual θ r = (θ.1 * r ^ 3) • K θ r := by
  obtain ⟨certificate, hcertificate⟩ :=
    mixedRawBracketCertificate_of_projectionTube θ r (Or.inr hdomain)
  have hkernel' : certificate.bracket 0 - centerBracketCoefficient θ * r =
      r ^ 2 * K θ r := by
    rw [hcertificate]
    exact hkernel
  exact certificate.centerResidual_eq_cubicKernel hkernel'

/-- Helper for Infrastructure I.16a: a parameter-set projection tube and a mixed bracket
kernel identity transport the center residual through both removable branches. -/
theorem centerResidual_eq_cubicKernel_of_projectionTube
    {β B radius : ℝ}
    {K : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    (hscale : ∀ θ r, θ.1 = 0 → physicalCenterResidual θ r = 0)
    (hcover : ∀ θ, θ ∈ parameterSet β B → ∀ r : ℝ, |r| < radius →
      r = 0 ∨ mixedRawProjectionDomain θ r)
    (hkernel : ∀ θ r, θ ∈ parameterSet β B → |r| < radius →
      mixedCenterBracket θ r - centerBracketCoefficient θ * r = r ^ 2 * K θ r)
    {θ : ℝ × ℝ × ℝ} {r : ℝ}
    (hθ : θ ∈ parameterSet β B) (hr : |r| < radius) :
    physicalCenterResidual θ r = physicalCenterCubicWeight θ r • K θ r := by
  let P : (ℝ × ℝ × ℝ) → ℝ → Prop :=
    fun η s ↦ η ∈ parameterSet β B ∧ |s| < radius
  have hcover' : ∀ η s, P η s →
      η.1 = 0 ∨ s = 0 ∨
        ∃ certificate : CenterRaw.BracketCertificate η.1 s (input η s),
          certificate.bracket 0 = mixedCenterBracket η s := by
    intro η s hP
    rcases hP with ⟨hη, hs⟩
    by_cases hηzero : η.1 = 0
    · exact Or.inl hηzero
    by_cases hszero : s = 0
    · exact Or.inr (Or.inl hszero)
    rcases hcover η hη s hs with hszero' | hdomain
    · exact Or.inr (Or.inl hszero')
    · obtain ⟨certificate, hcertificate⟩ :=
        mixedRawBracketCertificate_of_projectionTube η s (Or.inr hdomain)
      exact Or.inr (Or.inr ⟨certificate, hcertificate⟩)
  have hkernel' : ∀ η s, P η s → η.1 ≠ 0 → s ≠ 0 →
      mixedCenterBracket η s - centerBracketCoefficient η * s = s ^ 2 * K η s := by
    intro η s hP hη hs
    exact hkernel η s hP.1 hP.2
  exact centerResidual_eq_cubicKernel_of_bracketCertificateCover
    (fun η s _ hη ↦ hscale η s hη) hcover' hkernel' ⟨hθ, hr⟩

/-- Infrastructure I.16a: a canonical center-frame certificate packages the
orthogonality, signed second-displacement branch, and first displacement data
needed by the raw evaluator bridge. -/
structure CanonicalCenterFrameData
    (θ : ℝ × ℝ × ℝ) (r : ℝ) : Prop where
  orthogonal :
    canonicalFirstFrame θ r * (canonicalFirstFrame θ r).transpose = 1
  branch :
    (CenterRaw.firstFrame θ.1 (input θ r) = canonicalFirstFrame θ r ∧
      (CenterRaw.secondStep θ.1 (input θ r)).2.2 =
        r • canonicalSecondNormalizedDisplacement θ r) ∨
    (CenterRaw.firstFrame θ.1 (input θ r) = -canonicalFirstFrame θ r ∧
      (CenterRaw.secondStep θ.1 (input θ r)).2.2 =
        r • (-canonicalSecondNormalizedDisplacement θ r))
  firstDisplacement :
    (CenterRaw.firstStep θ.1 (input θ r)).2.2 =
      r • canonicalFirstNormalizedDisplacement θ r

/-- Infrastructure I.16a: a canonical `FrameKernelDataOn` point specializes to
the pointwise frame certificate without exposing its kernel fields. -/
theorem CanonicalCenterFrameData.ofFrameKernelData
    {K : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {D : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (data : FrameKernelDataOn canonicalFrameKernelSpec K D)
    {θ : ℝ × ℝ × ℝ} {r : ℝ} (hD : D θ r) :
    CanonicalCenterFrameData θ r := by
  exact
    { orthogonal := data.orthogonal θ r hD
      branch := data.branch θ r hD
      firstDisplacement := data.firstDisplacement θ r hD }

namespace CanonicalCenterFrameData

/-- Infrastructure I.16a: a canonical center-frame certificate produces the
raw bracket certificate whose scalar coordinate is `mixedCenterBracket`. -/
theorem bracketCertificate
    {θ : ℝ × ℝ × ℝ} {r : ℝ}
    (data : CanonicalCenterFrameData θ r) :
    ∃ certificate : CenterRaw.BracketCertificate θ.1 r (input θ r),
      certificate.bracket 0 = mixedCenterBracket θ r := by
  have hbracket :
      (weightedCenterBracket (canonicalFirstFrame θ r)
        (canonicalFirstNormalizedDisplacement θ r)
        (canonicalSecondNormalizedDisplacement θ r)) 0 =
        canonicalCenterBracket θ r := by
    rfl
  obtain ⟨certificate, hcertificate⟩ :=
    CenterRaw.bracketCertificate_of_signedFrameData
      (F := canonicalFirstFrame θ r)
      (u₀ := canonicalFirstNormalizedDisplacement θ r)
      (u₁ := canonicalSecondNormalizedDisplacement θ r)
      (W := canonicalCenterBracket θ r)
      data.orthogonal data.branch data.firstDisplacement hbracket
  refine ⟨certificate, ?_⟩
  rw [hcertificate, mixedCenterBracket_eq_canonicalCenterBracket]

/-- Infrastructure I.16a: the packaged frame certificate gives the raw
coordinate-zero full-center displacement in mixed-bracket form. -/
theorem fullCenterDisplacement_coord_zero
    {θ : ℝ × ℝ × ℝ} {r : ℝ}
    (data : CanonicalCenterFrameData θ r) :
    (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 =
      (θ.1 * r) * mixedCenterBracket θ r := by
  exact CenterRaw.fullCenterDisplacement_coord_zero_eq_mixedCenterBracket_of_signedFrameData
    data.orthogonal data.branch data.firstDisplacement

/-- Infrastructure I.16a: the packaged frame certificate gives the physical
center residual as the mixed bracket residual. -/
theorem centerResidual
    {θ : ℝ × ℝ × ℝ} {r : ℝ}
    (data : CanonicalCenterFrameData θ r) :
    physicalCenterResidual θ r =
      (θ.1 * r) * (mixedCenterBracket θ r - centerBracketCoefficient θ * r) := by
  exact centerResidual_eq_controlRadius_mul_mixedCenterBracketResidual_of_signedFrameData
    data.orthogonal data.branch data.firstDisplacement

/-- Infrastructure I.16a: a packaged frame certificate and a quadratic
bracket remainder produce the denominator-cleared cubic residual identity. -/
theorem centerResidual_eq_cubicKernel
    {θ : ℝ × ℝ × ℝ} {r K : ℝ}
    (data : CanonicalCenterFrameData θ r)
    (hkernel : mixedCenterBracket θ r - centerBracketCoefficient θ * r = r ^ 2 * K) :
    physicalCenterResidual θ r = physicalCenterCubicWeight θ r • K := by
  have hres := data.centerResidual
  rw [hres, hkernel]
  simp only [physicalCenterCubicWeight, smul_eq_mul]
  ring

end CanonicalCenterFrameData

/-- Infrastructure I.16a: canonical joint regularity and the transported
quadratic germ produce the truncated mixed bracket germ on a compact set. -/
theorem mixedCenterBracket_truncatedGerm_of_canonicalRegularity
    {K : Set (ℝ × ℝ × ℝ)}
    (hregular : ∀ θ, θ ∈ K →
      ContDiffAt ℝ 3 (Function.uncurry canonicalCenterBracket) (θ, 0)) :
    IndependentRadiusTruncatedGerm mixedCenterBracket K 2
      (fun n θ ↦ (![0, centerBracketCoefficient θ] : Fin 2 → ℝ) n) := by
  apply WeightedCenterBracket.truncatedGerm_of_coordZero_quadraticGerm
    (W := mixedCenterBracket)
  · intro θ hθ
    exact mixedCenterBracket_contDiffAt_of_canonical (hregular θ hθ)
  · intro θ hθ
    exact mixedCenterBracket_quadraticGerm θ

/-- Infrastructure I.16a: punctured canonical frame data expose the raw
coordinate-zero displacement directly in the mixed source bracket. -/
theorem CanonicalFrameKernelData.fullCenterDisplacement_coord_zero_eq_mixedCenterBracket
    {K : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    (data : CanonicalFrameKernelData K)
    {θ : ℝ × ℝ × ℝ} {r : ℝ}
    (hθ : θ.1 ≠ 0) (hr : r ≠ 0) :
    (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 =
      (θ.1 * r) * mixedCenterBracket θ r := by
  have hcanonical :=
    data.fullCenterDisplacement_coord_zero_eq_canonicalBracket hθ hr
  rw [mixedCenterBracket_eq_canonicalCenterBracket]
  exact hcanonical

/-- Infrastructure I.16a: a domain-indexed canonical frame cover extends the
raw mixed-bracket displacement identity across the zero-scale and zero-radius branches. -/
theorem CanonicalFrameKernelDataOn.fullCenterDisplacement_coord_zero_eq_mixedCenterBracket_of_cover
    {K : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {D P : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (data : CanonicalFrameKernelDataOn K D)
    (hscale : ∀ θ r, P θ r → θ.1 = 0 → physicalCenterResidual θ r = 0)
    (hcover : ∀ θ r, P θ r →
      θ.1 = 0 ∨ r = 0 ∨ D θ r)
    {θ : ℝ × ℝ × ℝ} {r : ℝ} (hP : P θ r) :
    (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 =
      (θ.1 * r) * mixedCenterBracket θ r := by
  have hcanonical :=
    FrameKernelDataOn.fullCenterDisplacement_coord_zero_eq_specBracket_of_cover
      data hscale hcover hP
  rw [mixedCenterBracket_eq_canonicalCenterBracket]
  simpa only [canonicalFrameKernelSpec] using hcanonical

namespace CanonicalFrameKernelDataOn

/-- Infrastructure I.16a: a covered canonical frame transports the physical
center residual to the mixed bracket remainder without dividing by either
the scale or the radius. -/
theorem centerResidual_eq_controlRadius_mul_mixedCenterBracketResidual_of_cover
    {K : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {D P : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (data : CanonicalFrameKernelDataOn K D)
    (hscale : ∀ θ r, P θ r → θ.1 = 0 → physicalCenterResidual θ r = 0)
    (hcover : ∀ θ r, P θ r →
      θ.1 = 0 ∨ r = 0 ∨ D θ r)
    {θ : ℝ × ℝ × ℝ} {r : ℝ} (hP : P θ r) :
    physicalCenterResidual θ r =
      (θ.1 * r) * (mixedCenterBracket θ r - centerBracketCoefficient θ * r) := by
  have hraw :=
    data.fullCenterDisplacement_coord_zero_eq_mixedCenterBracket_of_cover
      hscale hcover hP
  unfold physicalCenterResidual
  rw [hraw, centerDriftCoefficient_eq_control_mul_centerBracketCoefficient]
  ring

end CanonicalFrameKernelDataOn

namespace CanonicalFrameKernelDataOn

/-- Infrastructure I.16a: a frame-kernel certificate gives the punctured
center residual in mixed-bracket cubic-kernel form without a global cover. -/
theorem centerResidual_eq_mixedBracketCubicKernel
    {K : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {D : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (data : CanonicalFrameKernelDataOn K D)
    {θ : ℝ × ℝ × ℝ} {r : ℝ}
    (hkernel : D θ r →
      mixedCenterBracket θ r - centerBracketCoefficient θ * r = r ^ 2 * K θ r)
    (hD : D θ r) :
    physicalCenterResidual θ r = physicalCenterCubicWeight θ r • K θ r := by
  have hkernel' :
      canonicalCenterBracket θ r - centerBracketCoefficient θ * r = r ^ 2 * K θ r := by
    rw [← mixedCenterBracket_eq_canonicalCenterBracket]
    exact hkernel hD
  have hres :=
    FrameKernelDataOn.centerResidual_eq_controlRadius_mul_specBracketResidual
      (spec := canonicalFrameKernelSpec) data hD
  rw [hres]
  simp only [canonicalFrameKernelSpec]
  rw [hkernel']
  simp only [physicalCenterCubicWeight, smul_eq_mul]
  ring

/-- Infrastructure I.16a: the pointwise raw evaluator is the quadratic drift
plus a mixed-bracket cubic kernel on a certified punctured frame chart. -/
theorem fullCenterDisplacement_coord_zero_eq_drift_add_mixedBracketCubicKernel
    {K : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {D : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (data : CanonicalFrameKernelDataOn K D)
    {θ : ℝ × ℝ × ℝ} {r : ℝ}
    (hkernel : D θ r →
      mixedCenterBracket θ r - centerBracketCoefficient θ * r = r ^ 2 * K θ r)
    (hD : D θ r) :
    (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 =
      centerDriftCoefficient θ * r ^ 2 +
        physicalCenterCubicWeight θ r • K θ r := by
  have hres := data.centerResidual_eq_mixedBracketCubicKernel hkernel hD
  unfold physicalCenterResidual at hres
  linarith

/-- Infrastructure I.16a: the punctured zero-filled quotient is exactly the
mixed-bracket kernel, with no assumptions on removable branches. -/
theorem centerResidual_zeroFilledQuotient_eq_kernel
    {K : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {D : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (data : CanonicalFrameKernelDataOn K D)
    {θ : ℝ × ℝ × ℝ} {r : ℝ}
    (hkernel : D θ r →
      mixedCenterBracket θ r - centerBracketCoefficient θ * r = r ^ 2 * K θ r)
    (hD : D θ r)
    (hθ : θ.1 ≠ 0) (hr : r ≠ 0) :
    centerBracketZeroFilledQuotient physicalCenterResidual θ r = K θ r := by
  have hres := data.centerResidual_eq_mixedBracketCubicKernel hkernel hD
  have hweight : θ.1 * r ^ (3 : ℕ) ≠ 0 :=
    mul_ne_zero hθ (pow_ne_zero 3 hr)
  simp only [centerBracketZeroFilledQuotient, hweight, if_false,
    physicalCenterCubicWeight, hres, smul_eq_mul]
  field_simp [hweight]

/-- Infrastructure I.16a: a covered canonical frame and a mixed-bracket quadratic
remainder assemble the full denominator-cleared cubic center residual. -/
theorem centerResidual_eq_mixedBracketCubicKernel_of_cover
    {K : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {D P : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (data : CanonicalFrameKernelDataOn K D)
    (hscale : ∀ θ r, P θ r → θ.1 = 0 → physicalCenterResidual θ r = 0)
    (hcover : ∀ θ r, P θ r →
      θ.1 = 0 ∨ r = 0 ∨ D θ r)
    (hkernel : ∀ θ r, P θ r →
      D θ r →
        mixedCenterBracket θ r - centerBracketCoefficient θ * r = r ^ 2 * K θ r)
    {θ : ℝ × ℝ × ℝ} {r : ℝ} (hP : P θ r) :
    physicalCenterResidual θ r = physicalCenterCubicWeight θ r • K θ r := by
  rcases hcover θ r hP with hθ | hr | hD
  · have hres := hscale θ r hP hθ
    rw [hres, physicalCenterCubicWeight, hθ]
    simp
  · subst r
    have hres : physicalCenterResidual θ 0 = 0 := by
      simpa only [physicalCenterResidual] using centerResidual_zeroRadius θ
    rw [hres, physicalCenterCubicWeight]
    simp
  · exact data.centerResidual_eq_mixedBracketCubicKernel
      (hkernel θ r hP) hD

/-- Infrastructure I.16a: the covered raw evaluator is the quadratic drift plus
the mixed-bracket cubic kernel, including both removable branches. -/
theorem fullCenterDisplacement_coord_zero_eq_drift_add_mixedBracketCubicKernel_of_cover
    {K : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {D P : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (data : CanonicalFrameKernelDataOn K D)
    (hscale : ∀ θ r, P θ r → θ.1 = 0 → physicalCenterResidual θ r = 0)
    (hcover : ∀ θ r, P θ r →
      θ.1 = 0 ∨ r = 0 ∨ D θ r)
    (hkernel : ∀ θ r, P θ r →
      D θ r →
        mixedCenterBracket θ r - centerBracketCoefficient θ * r = r ^ 2 * K θ r)
    {θ : ℝ × ℝ × ℝ} {r : ℝ} (hP : P θ r) :
    (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 =
      centerDriftCoefficient θ * r ^ 2 +
        physicalCenterCubicWeight θ r • K θ r := by
  have hres := data.centerResidual_eq_mixedBracketCubicKernel_of_cover
    hscale hcover hkernel hP
  unfold physicalCenterResidual at hres
  linarith

/-- Infrastructure I.16a: on the punctured covered branch, the parent
zero-filled residual quotient is exactly the supplied mixed-bracket kernel. -/
theorem centerResidual_zeroFilledQuotient_eq_kernel_of_cover
    {K : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {D P : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (data : CanonicalFrameKernelDataOn K D)
    (hcover : ∀ θ r, P θ r →
      θ.1 = 0 ∨ r = 0 ∨ D θ r)
    (hkernel : ∀ θ r, P θ r →
      D θ r →
        mixedCenterBracket θ r - centerBracketCoefficient θ * r = r ^ 2 * K θ r)
    {θ : ℝ × ℝ × ℝ} {r : ℝ} (hP : P θ r)
    (hθ : θ.1 ≠ 0) (hr : r ≠ 0) :
    centerBracketZeroFilledQuotient physicalCenterResidual θ r = K θ r := by
  have hD : D θ r := by
    rcases hcover θ r hP with hθzero | hrzero | hD
    · exact (hθ hθzero).elim
    · exact (hr hrzero).elim
    · exact hD
  exact data.centerResidual_zeroFilledQuotient_eq_kernel
    (hkernel θ r hP) hD hθ hr

end CanonicalFrameKernelDataOn

/-- Infrastructure I.16a: the local-cover quotient fills only the removable
branches with the supplied kernel, while retaining the raw residual quotient
on the punctured branch. -/
def centerResidualKernelFilledQuotient
    (K : (ℝ × ℝ × ℝ) → ℝ → ℝ)
    (θ : ℝ × ℝ × ℝ) (r : ℝ) : ℝ :=
  if physicalCenterCubicWeight θ r = 0 then K θ r
  else centerBracketZeroFilledQuotient physicalCenterResidual θ r

/-! The next two declarations are the source-facing boundary for a local raw
    projection tube.  The kernel is only required to describe the bracket on
    the tube; outside it, the filled quotient supplies the harmless extension
    needed by the global certificate type. -/

/-- Infrastructure I.16a: a local raw projection tube identifies the filled
quotient with a supplied continuous mixed-bracket kernel. -/
theorem centerResidualKernelFilledQuotient_eq_kernel_of_projectionTube
    {β B radius : ℝ}
    {K : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    (hscale : ∀ θ r, θ.1 = 0 → physicalCenterResidual θ r = 0)
    (hcover : ∀ θ, θ ∈ parameterSet β B → ∀ r : ℝ, |r| < radius →
      r = 0 ∨ mixedRawProjectionDomain θ r)
    (hkernel : ∀ θ r, θ ∈ parameterSet β B → |r| < radius →
      mixedCenterBracket θ r - centerBracketCoefficient θ * r = r ^ 2 * K θ r)
    {θ : ℝ × ℝ × ℝ} (hθ : θ ∈ parameterSet β B)
    {r : ℝ} (hr : |r| < radius) :
    centerResidualKernelFilledQuotient K θ r = K θ r := by
  let P : (ℝ × ℝ × ℝ) → ℝ → Prop :=
    fun η s ↦ η ∈ parameterSet β B ∧ |s| < radius
  have hcover' : ∀ η s, P η s →
      η.1 = 0 ∨ s = 0 ∨
        ∃ certificate : CenterRaw.BracketCertificate η.1 s (input η s),
          certificate.bracket 0 = mixedCenterBracket η s := by
    intro η s hP
    rcases hP with ⟨hη, hs⟩
    by_cases hηzero : η.1 = 0
    · exact Or.inl hηzero
    by_cases hszero : s = 0
    · exact Or.inr (Or.inl hszero)
    rcases hcover η hη s hs with hszero' | hdomain
    · exact Or.inr (Or.inl hszero')
    · obtain ⟨certificate, hcertificate⟩ :=
        mixedRawBracketCertificate_of_projectionTube η s (Or.inr hdomain)
      exact Or.inr (Or.inr ⟨certificate, hcertificate⟩)
  have hkernel' : ∀ η s, P η s → η.1 ≠ 0 → s ≠ 0 →
      mixedCenterBracket η s - centerBracketCoefficient η * s = s ^ 2 * K η s := by
    intro η s hP hη hs
    exact hkernel η s hP.1 hP.2
  have hP : P θ r := ⟨hθ, hr⟩
  by_cases hweight : physicalCenterCubicWeight θ r = 0
  · simp only [centerResidualKernelFilledQuotient, hweight, if_pos]
  · have hres := centerResidual_eq_cubicKernel_of_bracketCertificateCover
      (fun η s _ hη ↦ hscale η s hη) hcover' hkernel' hP
    have hweight' : θ.1 * r ^ (3 : ℕ) ≠ 0 := by
      simpa only [physicalCenterCubicWeight] using hweight
    have hθne : θ.1 ≠ 0 := by
      intro hθzero
      apply hweight'
      simp only [hθzero, zero_mul]
    have hrne : r ≠ 0 := by
      intro hrzero
      apply hweight
      simp [physicalCenterCubicWeight, hrzero]
    have hden : θ.1 * r ≠ 0 := mul_ne_zero hθne hrne
    have hquotient : centerBracketZeroFilledQuotient physicalCenterResidual θ r = K θ r := by
      simp only [centerBracketZeroFilledQuotient, hweight', if_false,
        physicalCenterCubicWeight, hres, smul_eq_mul]
      field_simp [hden]
    simp only [centerResidualKernelFilledQuotient, hweight, if_false]
    exact hquotient

/-- Infrastructure I.16a: a global scale-zero identity factors the physical
residual through the local-cover filled quotient on every branch. -/
theorem centerResidual_eq_cubicWeight_smul_kernelFilledQuotient_of_scaleZero
    (K : (ℝ × ℝ × ℝ) → ℝ → ℝ)
    (hscale : ∀ θ r, θ.1 = 0 → physicalCenterResidual θ r = 0) :
    ∀ θ r,
      physicalCenterResidual θ r =
        physicalCenterCubicWeight θ r •
          centerResidualKernelFilledQuotient K θ r := by
  intro θ r
  have hzero :=
    centerResidual_eq_cubicWeight_smul_zeroFilledQuotient_of_scaleZero hscale θ r
  by_cases hweight : physicalCenterCubicWeight θ r = 0
  · have hres : physicalCenterResidual θ r = 0 := by
      simpa only [hweight, zero_smul] using hzero
    simp only [centerResidualKernelFilledQuotient, hweight, if_pos,
      hres, zero_smul]
  · simpa only [centerResidualKernelFilledQuotient, hweight, if_false] using hzero

/-- Infrastructure I.16a: the same factorization in source notation supplies
the all-branch identity required by `CenterResidualSourceCertificate`. -/
theorem centerResidual_source_factorization_of_scaleZero
    (K : (ℝ × ℝ × ℝ) → ℝ → ℝ)
    (hscale : ∀ θ r, θ.1 = 0 → physicalCenterResidual θ r = 0) :
    ∀ θ r,
      (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
          centerDriftCoefficient θ * r ^ (2 : ℕ) =
        physicalCenterCubicWeight θ r •
          centerResidualKernelFilledQuotient K θ r := by
  intro θ r
  simpa only [physicalCenterResidual] using
    centerResidual_eq_cubicWeight_smul_kernelFilledQuotient_of_scaleZero K hscale θ r

/-- Infrastructure I.16a: a physical scale-zero residual identity is the
source-facing removable branch after expanding `physicalCenterResidual`. -/
theorem centerResidual_source_scale_zero_of_scaleZero
    (hscale : ∀ θ r, θ.1 = 0 → physicalCenterResidual θ r = 0) :
    ∀ θ r, θ.1 = 0 →
      (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
          centerDriftCoefficient θ * r ^ (2 : ℕ) = 0 := by
  intro θ r hθ
  simpa only [physicalCenterResidual] using hscale θ r hθ

/-- Infrastructure I.16a: the all-branch filled factorization restricts to
the punctured source branch required by the certificate interface. -/
theorem centerResidual_source_punctured_factorization_of_scaleZero
    (K : (ℝ × ℝ × ℝ) → ℝ → ℝ)
    (hscale : ∀ θ r, θ.1 = 0 → physicalCenterResidual θ r = 0) :
    ∀ θ r, θ.1 ≠ 0 → r ≠ 0 →
      (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
          centerDriftCoefficient θ * r ^ (2 : ℕ) =
        (θ.1 * r ^ (3 : ℕ)) •
          centerResidualKernelFilledQuotient K θ r := by
  intro θ r hθ hr
  simpa only [physicalCenterCubicWeight] using
    centerResidual_source_factorization_of_scaleZero K hscale θ r

/-- Helper for Infrastructure I.16a: a local raw projection tube packages directly as a
source certificate, with the outside-tube quotient hidden in the filled kernel. -/
noncomputable def CenterResidualSourceCertificate.of_projectionTube
    {β B radius : ℝ}
    (K : (ℝ × ℝ × ℝ) → ℝ → ℝ)
    (hradius : 0 < radius)
    (hscale : ∀ θ r, θ.1 = 0 → physicalCenterResidual θ r = 0)
    (hcover : ∀ θ, θ ∈ parameterSet β B → ∀ r : ℝ, |r| < radius →
      r = 0 ∨ mixedRawProjectionDomain θ r)
    (hkernel : ∀ θ r, θ ∈ parameterSet β B → |r| < radius →
      mixedCenterBracket θ r - centerBracketCoefficient θ * r = r ^ 2 * K θ r)
    (hK : ContinuousOn
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ K z.1 z.2)
      (parameterSet β B ×ˢ Set.Icc (-radius) radius)) :
    CenterResidualSourceCertificate β B
      (centerResidualKernelFilledQuotient K) :=
  { kernel := K
    radius := radius
    radius_pos := hradius
    scale_zero := centerResidual_source_scale_zero_of_scaleZero hscale
    punctured_factorization :=
      centerResidual_source_punctured_factorization_of_scaleZero K hscale
    kernel_continuous := hK
    quotient_eq_kernel :=
      fun _θ hθ _r hr ↦ centerResidualKernelFilledQuotient_eq_kernel_of_projectionTube
        hscale hcover hkernel hθ hr }

namespace CanonicalFrameKernelDataOn

/-- Infrastructure I.16a: a canonical frame cover on a compact source tube
identifies the filled residual quotient with the continuous supplied kernel. -/
theorem kernelFilledQuotient_eq_kernel_of_localCover
    {β B : ℝ}
    {K : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {D : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (data : CanonicalFrameKernelDataOn K D)
    (radius : ℝ)
    (hcover : ∀ θ, θ ∈ parameterSet β B → ∀ r : ℝ, |r| < radius →
      θ.1 ≠ 0 → r ≠ 0 → D θ r)
    {θ : ℝ × ℝ × ℝ} (hθ : θ ∈ parameterSet β B)
    {r : ℝ} (hr : |r| < radius) :
    centerResidualKernelFilledQuotient K θ r = K θ r := by
  by_cases hweight : physicalCenterCubicWeight θ r = 0
  · simp only [centerResidualKernelFilledQuotient, hweight, if_pos]
  · have hθne : θ.1 ≠ 0 := by
      intro hθzero
      apply hweight
      simp only [physicalCenterCubicWeight, hθzero, zero_mul]
    have hrne : r ≠ 0 := by
      intro hrzero
      apply hweight
      rw [physicalCenterCubicWeight, hrzero]
      simp
    have hD : D θ r := hcover θ hθ r hr hθne hrne
    have hkernel : D θ r →
        mixedCenterBracket θ r - centerBracketCoefficient θ * r = r ^ 2 * K θ r := by
      intro hD'
      rw [mixedCenterBracket_eq_canonicalCenterBracket]
      exact data.bracketKernel θ r hD'
    have hquot := data.centerResidual_zeroFilledQuotient_eq_kernel
      hkernel hD hθne hrne
    simp only [centerResidualKernelFilledQuotient, hweight, if_false]
    exact hquot

/-- Infrastructure I.16a: a local canonical frame cover promotes to a source
certificate without pretending that the raw chart exists outside its tube. -/
noncomputable def toLocalSourceCertificate
    {β B : ℝ}
    {K : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {D : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (data : CanonicalFrameKernelDataOn K D)
    (radius : ℝ)
    (hradius : 0 < radius)
    (hscale : ∀ θ r, θ.1 = 0 → physicalCenterResidual θ r = 0)
    (hcover : ∀ θ, θ ∈ parameterSet β B → ∀ r : ℝ, |r| < radius →
      θ.1 ≠ 0 → r ≠ 0 → D θ r)
    (hK : ContinuousOn
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ K z.1 z.2)
      (parameterSet β B ×ˢ Set.Icc (-radius) radius)) :
    CenterResidualSourceCertificate β B
      (centerResidualKernelFilledQuotient K) :=
  { kernel := K
    radius := radius
    radius_pos := hradius
    scale_zero := centerResidual_source_scale_zero_of_scaleZero hscale
    punctured_factorization :=
      centerResidual_source_punctured_factorization_of_scaleZero K hscale
    kernel_continuous := hK
    quotient_eq_kernel :=
      fun _ hθ _ hr ↦ data.kernelFilledQuotient_eq_kernel_of_localCover
        radius hcover hθ hr }

end CanonicalFrameKernelDataOn

/-- Infrastructure I.16a: a local frame-kernel cover identifies the filled residual
quotient with its continuous kernel on the parameter-radius tube. -/
theorem FrameKernelDataOn.localFilledQuotient_eq_kernel
    {β B radius : ℝ}
    {spec : FrameKernelSpec}
    {K : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {D : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (data : FrameKernelDataOn spec K D)
    (hcover : ∀ θ, θ ∈ parameterSet β B → ∀ r : ℝ, |r| < radius →
      θ.1 ≠ 0 → r ≠ 0 → D θ r)
    {θ : ℝ × ℝ × ℝ} (hθ : θ ∈ parameterSet β B)
    {r : ℝ} (hr : |r| < radius) :
    centerResidualKernelFilledQuotient K θ r = K θ r := by
  by_cases hweight : physicalCenterCubicWeight θ r = 0
  · simp only [centerResidualKernelFilledQuotient, hweight, if_pos]
  · have hθne : θ.1 ≠ 0 := by
      intro hθzero
      apply hweight
      simp only [physicalCenterCubicWeight, hθzero, zero_mul]
    have hrne : r ≠ 0 := by
      intro hrzero
      apply hweight
      simp [physicalCenterCubicWeight, hrzero]
    have hD : D θ r := hcover θ hθ r hr hθne hrne
    have hres := data.centerResidual_eq_cubicKernel hD
    have hweight' : θ.1 * r ^ (3 : ℕ) ≠ 0 := by
      simpa only [physicalCenterCubicWeight] using hweight
    have hquot :
        centerBracketZeroFilledQuotient physicalCenterResidual θ r = K θ r := by
      simp only [centerBracketZeroFilledQuotient, hweight', if_false, hres,
        smul_eq_mul]
      field_simp [hweight']
    simp only [centerResidualKernelFilledQuotient, hweight, if_false]
    exact hquot

/-- Infrastructure I.16a: a removable-branch cover specializes to the punctured
cover required by the denominator-cleared frame-kernel identity. -/
theorem FrameKernelDataOn.puncturedCover_of_removableCover
    {β B radius : ℝ}
    {D : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (hcover : ∀ θ, θ ∈ parameterSet β B → ∀ r : ℝ, |r| < radius →
      θ.1 = 0 ∨ r = 0 ∨ D θ r) :
    ∀ θ, θ ∈ parameterSet β B → ∀ r : ℝ, |r| < radius →
      θ.1 ≠ 0 → r ≠ 0 → D θ r := by
  intro θ hθ r hr hθne hrne
  rcases hcover θ hθ r hr with hθzero | hrzero | hD
  · exact (hθne hθzero).elim
  · exact (hrne hrzero).elim
  · exact hD

/-- Infrastructure I.16a: a domain-indexed frame-kernel package promotes to a
source certificate using only a local parameter-radius cover. -/
noncomputable def FrameKernelDataOn.toLocalSourceCertificate
    {β B radius : ℝ}
    {spec : FrameKernelSpec}
    {K : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {D : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (data : FrameKernelDataOn spec K D)
    (hradius : 0 < radius)
    (hscale : ∀ θ r, θ.1 = 0 → physicalCenterResidual θ r = 0)
    (hcover : ∀ θ, θ ∈ parameterSet β B → ∀ r : ℝ, |r| < radius →
      θ.1 ≠ 0 → r ≠ 0 → D θ r)
    (hK : ContinuousOn
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ K z.1 z.2)
      (parameterSet β B ×ˢ Set.Icc (-radius) radius)) :
    CenterResidualSourceCertificate β B
      (centerResidualKernelFilledQuotient K) :=
  { kernel := K
    radius := radius
    radius_pos := hradius
    scale_zero := centerResidual_source_scale_zero_of_scaleZero hscale
    punctured_factorization :=
      centerResidual_source_punctured_factorization_of_scaleZero K hscale
    kernel_continuous := hK
    quotient_eq_kernel :=
      fun _ hθ _ hr ↦ data.localFilledQuotient_eq_kernel hcover hθ hr }

/-- Infrastructure I.16a: a domain-indexed frame-kernel package promotes from
the natural removable-branch cover used by local source calculations. -/
noncomputable def FrameKernelDataOn.toLocalSourceCertificate_of_removableCover
    {β B radius : ℝ}
    {spec : FrameKernelSpec}
    {K : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {D : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (data : FrameKernelDataOn spec K D)
    (hradius : 0 < radius)
    (hscale : ∀ θ r, θ.1 = 0 → physicalCenterResidual θ r = 0)
    (hcover : ∀ θ, θ ∈ parameterSet β B → ∀ r : ℝ, |r| < radius →
      θ.1 = 0 ∨ r = 0 ∨ D θ r)
    (hK : ContinuousOn
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ K z.1 z.2)
      (parameterSet β B ×ˢ Set.Icc (-radius) radius)) :
    CenterResidualSourceCertificate β B
      (centerResidualKernelFilledQuotient K) :=
  data.toLocalSourceCertificate hradius hscale
    (FrameKernelDataOn.puncturedCover_of_removableCover hcover) hK

/-- Infrastructure I.16a: a domain-indexed frame-kernel package is promoted to
the source-facing certificate without exposing the intermediate quotient proof. -/
noncomputable def FrameKernelDataOn.toSourceCertificate
    {β B : ℝ}
    {spec : FrameKernelSpec}
    {K : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {D : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (data : FrameKernelDataOn spec K D)
    (radius : ℝ)
    (hradius : 0 < radius)
    (hscale : ∀ θ r, θ.1 = 0 → physicalCenterResidual θ r = 0)
    (hcover : ∀ θ r, θ.1 ≠ 0 → r ≠ 0 → D θ r)
    (hK : ContinuousOn
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ K z.1 z.2)
      (parameterSet β B ×ˢ Set.Icc (-radius) radius)) :
    CenterResidualSourceCertificate β B
      (kernelFilledCubicQuotient
        (data.toKernelCertificate radius hradius hscale hcover hK)) :=
  (data.toKernelCertificate radius hradius hscale hcover hK).toSourceCertificate

/-- Infrastructure I.16a: the source-facing promotion preserves the raw
punctured factorization in the full-center-displacement notation. -/
theorem FrameKernelDataOn.source_punctured_factorization
    {β B : ℝ}
    {spec : FrameKernelSpec}
    {K : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {D : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (data : FrameKernelDataOn spec K D)
    (radius : ℝ)
    (hradius : 0 < radius)
    (hscale : ∀ θ r, θ.1 = 0 → physicalCenterResidual θ r = 0)
    (hcover : ∀ θ r, θ.1 ≠ 0 → r ≠ 0 → D θ r)
    (hK : ContinuousOn
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ K z.1 z.2)
      (parameterSet β B ×ˢ Set.Icc (-radius) radius)) :
    ∀ θ r, θ.1 ≠ 0 → r ≠ 0 →
      (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
          centerDriftCoefficient θ * r ^ (2 : ℕ) =
        (θ.1 * r ^ (3 : ℕ)) •
          kernelFilledCubicQuotient
            (data.toKernelCertificate radius hradius hscale hcover hK) θ r := by
  exact (data.toSourceCertificate radius hradius hscale hcover hK).punctured_factorization

/-- Infrastructure I.16a: the source-facing promotion identifies its filled
quotient with the continuous frame kernel on the whole parameter tube. -/
theorem FrameKernelDataOn.source_quotient_eq_kernel
    {β B : ℝ}
    {spec : FrameKernelSpec}
    {K : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {D : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (data : FrameKernelDataOn spec K D)
    (radius : ℝ)
    (hradius : 0 < radius)
    (hscale : ∀ θ r, θ.1 = 0 → physicalCenterResidual θ r = 0)
    (hcover : ∀ θ r, θ.1 ≠ 0 → r ≠ 0 → D θ r)
    (hK : ContinuousOn
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ K z.1 z.2)
      (parameterSet β B ×ˢ Set.Icc (-radius) radius)) :
    ∀ θ ∈ parameterSet β B, ∀ r : ℝ, |r| < radius →
      kernelFilledCubicQuotient
          (data.toKernelCertificate radius hradius hscale hcover hK) θ r =
        K θ r := by
  exact (data.toSourceCertificate radius hradius hscale hcover hK).quotient_eq_kernel

/-- Helper for Infrastructure I.16a: the explicit independent-radius regularity supplies the
compact-set truncated bracket germ used by the zero-filled quotient transport. -/
theorem mixedCenterBracket_truncatedGerm_of_independentRadius
    {K : Set (ℝ × ℝ × ℝ)} :
    IndependentRadiusTruncatedGerm mixedCenterBracket K 2
      (fun n θ ↦ (![0, centerBracketCoefficient θ] : Fin 2 → ℝ) n) := by
  apply mixedCenterBracket_truncatedGerm_of_canonicalRegularity
  intro θ hθ
  have hmixed := mixedCenterBracket_contDiffAt_of_independentRadius θ
  rw [mixedCenterBracket_uncurry_eq_canonicalCenterBracket] at hmixed
  exact hmixed

/-- Helper for Infrastructure I.16a: a uniform projection tube supplies raw bracket
certificates on the whole compact parameter-radius neighborhood. -/
theorem mixedRawBracketCertificate_of_uniformProjectionTube
    (β B : ℝ) (hβ_small : β < 1 / 4) (hB : 0 ≤ B) :
    ∃ δ₀ > 0, ∀ θ ∈ parameterSet β B, ∀ r : ℝ, |r| < δ₀ →
      ∃ certificate : CenterRaw.BracketCertificate θ.1 r (input θ r),
        certificate.bracket 0 = mixedCenterBracket θ r := by
  obtain ⟨δ₀, hδ₀, htube⟩ :=
    mixedRawProjectionDomain_uniformTube β B hβ_small hB
  refine ⟨δ₀, hδ₀, ?_⟩
  intro θ hθ r hr
  exact mixedRawBracketCertificate_of_projectionTube θ r (htube θ hθ r hr)

/-- Infrastructure I.16a: on the uniform projection tube, the zero-control-scale
branch of the physical center residual vanishes, with the radius-zero case included. -/
theorem mixedCenterResidual_zeroScale_of_uniformProjectionTube
    (β B : ℝ) (hβ_small : β < 1 / 4) (hB : 0 ≤ B) :
    ∃ δ₀ > 0, ∀ θ ∈ parameterSet β B, ∀ r : ℝ, |r| < δ₀ →
      θ.1 = 0 → physicalCenterResidual θ r = 0 := by
  obtain ⟨δ₀, hδ₀, htube⟩ :=
    mixedRawProjectionDomain_uniformTube β B hβ_small hB
  refine ⟨δ₀, hδ₀, ?_⟩
  intro θ hθ r hr hscale
  by_cases hrzero : r = 0
  · subst r
    exact physicalCenterResidual_zeroRadius θ
  · have hbranch := htube θ hθ r hr
    rcases hbranch with hrzero' | hdomain
    · exact (hrzero hrzero').elim
    · obtain ⟨certificate, _hcertificate⟩ :=
        mixedRawBracketCertificate_of_projectionTube θ r (Or.inr hdomain)
      have hdisplacement :=
        certificate.fullCenterDisplacement_coord_zero_eq_mul_bracket
      simpa [physicalCenterResidual, centerDriftCoefficient, hscale]
        using hdisplacement

/- The public source-facing quotient theorem deliberately stops at the compact
   germ interface: it does not require a separately chosen continuous divided
   difference kernel. -/

/-- Infrastructure I.16a: the independent-radius mixed bracket germ and the uniform
projection tube together give the zero-filled physical center-residual quotient bound. -/
theorem mixedCenterResidual_zeroFilledQuotient_uniformBound
    (β B : ℝ) (hβ_small : β < 1 / 4) (hB : 0 ≤ B) :
    ∃ δ > 0, ∃ C > 0, ∀ θ ∈ parameterSet β B, ∀ r : ℝ, |r| < δ →
      ‖centerBracketZeroFilledQuotient physicalCenterResidual θ r‖ ≤ C := by
  have hK : IsCompact (parameterSet β B) := parameterSet_isCompact β B
  have hW := mixedCenterBracket_truncatedGerm_of_independentRadius
    (K := parameterSet β B)
  obtain ⟨δ₀, hδ₀, hcertificate⟩ :=
    mixedRawBracketCertificate_of_uniformProjectionTube β B hβ_small hB
  obtain ⟨C, hC, δ, hδ, hbound⟩ :=
    centerResidual_zeroFilledQuotient_uniformBound_of_bracketGerm
      hK hW δ₀ hδ₀ hcertificate
  exact ⟨δ, hδ, C, hC, hbound⟩

/-- Helper for Infrastructure I.16a: a scale-zero certificate restricted to a
radius tube gives the zero-filled cubic factorization on that same tube.  The
radius restriction avoids imposing a global removable-branch identity. -/
theorem centerResidual_eq_cubicWeight_smul_zeroFilledQuotient_on_radius
    (S : Set (ℝ × ℝ × ℝ)) (radius : ℝ)
    (hscale : ∀ θ ∈ S, ∀ r : ℝ, |r| < radius →
      θ.1 = 0 → physicalCenterResidual θ r = 0) :
    ∀ θ ∈ S, ∀ r : ℝ, |r| < radius →
      physicalCenterResidual θ r =
        physicalCenterCubicWeight θ r •
          centerBracketZeroFilledQuotient physicalCenterResidual θ r := by
  intro θ hθS r hradius
  by_cases hweight : physicalCenterCubicWeight θ r = 0
  · have hweight' : θ.1 * r ^ (3 : ℕ) = 0 := by
      simpa only [physicalCenterCubicWeight] using hweight
    have hres : physicalCenterResidual θ r = 0 := by
      rcases mul_eq_zero.mp hweight' with hθ | hrpow
      · exact hscale θ hθS r hradius hθ
      · have hr : r = 0 := by
          exact eq_zero_of_pow_eq_zero hrpow
        rw [hr]
        simpa only [physicalCenterResidual] using centerResidual_zeroRadius θ
    have hquot_zero :
        centerBracketZeroFilledQuotient physicalCenterResidual θ r = 0 := by
      simp only [centerBracketZeroFilledQuotient, hweight', if_pos]
    rw [hres, hquot_zero]
    simp [hweight]
  · have hweight' : θ.1 * r ^ (3 : ℕ) ≠ 0 := by
      intro hzero
      apply hweight
      simpa only [physicalCenterCubicWeight] using hzero
    have hquot :
        centerBracketZeroFilledQuotient physicalCenterResidual θ r =
          physicalCenterResidual θ r / (θ.1 * r ^ (3 : ℕ)) := by
      simp only [centerBracketZeroFilledQuotient, hweight', if_false]
    rw [hquot, smul_eq_mul]
    exact (mul_div_cancel₀ (physicalCenterResidual θ r) hweight').symm

/-- Infrastructure I.16a: the uniform projection tube supplies both removable
branches, so the full mixed-variable cubic center-residual estimate needs no
global scale-zero hypothesis. -/
theorem mixedCenterResidual_uniformBound_of_uniformProjectionTube_zeroScale
    (β B : ℝ) (hβ_small : β < 1 / 4) (hB : 0 ≤ B) :
    ∃ C > 0, ∃ δ > 0, ∀ θ ∈ parameterSet β B, ∀ r : ℝ, |r| < δ →
      ‖(observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
        centerDriftCoefficient θ * r ^ (2 : ℕ)‖ ≤
      C * |θ.1| * |r| ^ (3 : ℝ) := by
  obtain ⟨δ₀, hδ₀, hscale⟩ :=
    mixedCenterResidual_zeroScale_of_uniformProjectionTube β B hβ_small hB
  obtain ⟨δ, hδ, C, hC, hQ⟩ :=
    mixedCenterResidual_zeroFilledQuotient_uniformBound β B hβ_small hB
  refine ⟨C, hC, min δ δ₀, lt_min hδ hδ₀, ?_⟩
  intro θ hθ r hr
  have hrδ : |r| < δ := (lt_min_iff.mp hr).1
  have hrδ₀ : |r| < δ₀ := (lt_min_iff.mp hr).2
  have hfactor :=
    centerResidual_eq_cubicWeight_smul_zeroFilledQuotient_on_radius
      (parameterSet β B) δ₀
      (fun η hη s hs hηzero ↦ hscale η hη s hs hηzero)
      θ hθ r hrδ₀
  have hfactor' :
      (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
          centerDriftCoefficient θ * r ^ (2 : ℕ) =
        (θ.1 * r ^ (3 : ℕ)) •
          centerBracketZeroFilledQuotient physicalCenterResidual θ r := by
    simpa only [physicalCenterResidual, physicalCenterCubicWeight] using hfactor
  rw [hfactor', norm_smul, Real.norm_eq_abs, abs_mul, abs_pow]
  have hnonneg : 0 ≤ |θ.1| * |r| ^ (3 : ℕ) := by positivity
  calc
    (|θ.1| * |r| ^ (3 : ℕ)) *
        ‖centerBracketZeroFilledQuotient physicalCenterResidual θ r‖ ≤
        (|θ.1| * |r| ^ (3 : ℕ)) * C :=
      mul_le_mul_of_nonneg_left (hQ θ hθ r hrδ) hnonneg
    _ = C * |θ.1| * |r| ^ (3 : ℕ) := by ring
    _ = C * |θ.1| * |r| ^ (3 : ℝ) := by
      have hpow : |r| ^ (3 : ℝ) = |r| ^ (3 : ℕ) := by
        norm_num [Real.rpow_natCast]
      rw [hpow]

/-- Infrastructure I.16a: adding the explicit zero-scale evaluator certificate upgrades
    the quotient bound to the full mixed-variable cubic center-residual estimate. -/
theorem mixedCenterResidual_uniformBound_of_uniformProjectionTube
    (β B : ℝ) (hβ_small : β < 1 / 4) (hB : 0 ≤ B)
    (hscale : ∀ θ r, θ.1 = 0 → physicalCenterResidual θ r = 0) :
    ∃ C > 0, ∃ δ > 0, ∀ θ ∈ parameterSet β B, ∀ r : ℝ, |r| < δ →
      ‖(observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
        centerDriftCoefficient θ * r ^ (2 : ℕ)‖ ≤
      C * |θ.1| * |r| ^ (3 : ℝ) := by
  let Q : (ℝ × ℝ × ℝ) → ℝ → ℝ :=
    centerBracketZeroFilledQuotient physicalCenterResidual
  have hfactor : ∀ θ r,
      physicalCenterResidual θ r =
        physicalCenterCubicWeight θ r • Q θ r := by
    intro θ r
    exact centerResidual_eq_cubicWeight_smul_zeroFilledQuotient_of_scaleZero
      hscale θ r
  obtain ⟨δ, hδ, C, hC, hQ⟩ :=
    mixedCenterResidual_zeroFilledQuotient_uniformBound β B hβ_small hB
  have hQ' : ∃ C > 0, ∃ δ > 0, ∀ θ ∈ parameterSet β B, ∀ r : ℝ,
      |r| < δ → ‖Q θ r‖ ≤ C := by
    exact ⟨C, hC, δ, hδ, hQ⟩
  have hbound := centerResidual_uniformBound_of_cubicFactorization
    (K := parameterSet β B) (Q := Q) hfactor hQ'
  simpa only [Q, physicalCenterResidual] using hbound

end DFP.TwoLeg.Mixed
