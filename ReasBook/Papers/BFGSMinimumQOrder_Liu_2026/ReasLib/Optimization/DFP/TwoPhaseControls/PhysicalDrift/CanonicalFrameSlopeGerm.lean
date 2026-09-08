module

public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.RawFrameSlopeCoefficientBridge
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusSecondFactorGerm
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.RawFrameSlopeCoefficientBridge
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusSecondFactorGerm

public section

noncomputable section

namespace DFP.TwoLeg.Mixed

/-!
This file instantiates the raw-frame quotient boundary with the public
independent-radius normal form.  No oriented raw evaluator is imported here;
the source-facing bridge is the pointwise identification supplied by the
physical-drift owner.
-/

/-- Helper for Infrastructure I.16a: the first canonical frame's off-diagonal
entry along an independent-radius slice. -/
def canonicalFrameSlopeFirstE (θ : ℝ × ℝ × ℝ) (r : ℝ) : ℝ :=
  (independentRadiusFirstMetricTriple (θ, r)).2.1

/-- Helper for Infrastructure I.16a: the first canonical frame's diagonal gap
after removing its explicit quadratic radius factor. -/
def canonicalFrameSlopeFirstX (θ : ℝ × ℝ × ℝ) (r : ℝ) : ℝ :=
  (independentRadiusFirstMetricTriple (θ, r)).2.2 -
    r ^ 2 * (independentRadiusFirstSpectral (θ, r)).1

/-- Helper for Infrastructure I.16a: the second canonical frame's off-diagonal
entry along an independent-radius slice. -/
def canonicalFrameSlopeSecondE (θ : ℝ × ℝ × ℝ) (r : ℝ) : ℝ :=
  (independentRadiusSecondMetricTriple (θ, r)).2.1

/-- Helper for Infrastructure I.16a: the second canonical frame's diagonal gap
after removing its explicit quadratic radius factor. -/
def canonicalFrameSlopeSecondX (θ : ℝ × ℝ × ℝ) (r : ℝ) : ℝ :=
  (independentRadiusSecondMetricTriple (θ, r)).2.2 -
    r ^ 2 * (independentRadiusSecondSpectral (θ, r)).1

/-- Infrastructure I.16a: the canonical relative-frame slope obtained from the
two low-vector entry pairs. -/
def canonicalFrameSlope (θ : ℝ × ℝ × ℝ) (r : ℝ) : ℝ :=
  -(canonicalFrameSlopeFirstE θ r * canonicalFrameSlopeSecondX θ r +
      canonicalFrameSlopeFirstX θ r * canonicalFrameSlopeSecondE θ r) /
    (canonicalFrameSlopeFirstX θ r * canonicalFrameSlopeSecondX θ r -
      canonicalFrameSlopeFirstE θ r * canonicalFrameSlopeSecondE θ r)

/-
  This theorem is the stable rewrite interface for ordinary module imports:
  the definition itself is intentionally opaque outside this file.
-/
/-- Helper for Infrastructure I.16a: the canonical slope evaluates to its
entry-wise quotient formula. -/
theorem canonicalFrameSlope_apply (θ : ℝ × ℝ × ℝ) (r : ℝ) :
    canonicalFrameSlope θ r =
      -(canonicalFrameSlopeFirstE θ r * canonicalFrameSlopeSecondX θ r +
          canonicalFrameSlopeFirstX θ r * canonicalFrameSlopeSecondE θ r) /
        (canonicalFrameSlopeFirstX θ r * canonicalFrameSlopeSecondX θ r -
          canonicalFrameSlopeFirstE θ r * canonicalFrameSlopeSecondE θ r) := by
  rfl

/-- Helper for Infrastructure I.16a: the canonical slope is equal as a path to
its entry-wise quotient formula, which remains rewriteable across modules. -/
theorem canonicalFrameSlope_eq_entryQuotient (θ : ℝ × ℝ × ℝ) :
    canonicalFrameSlope θ =
      (fun r ↦
        -(canonicalFrameSlopeFirstE θ r * canonicalFrameSlopeSecondX θ r +
            canonicalFrameSlopeFirstX θ r * canonicalFrameSlopeSecondE θ r) /
          (canonicalFrameSlopeFirstX θ r * canonicalFrameSlopeSecondX θ r -
            canonicalFrameSlopeFirstE θ r * canonicalFrameSlopeSecondE θ r)) := by
  funext r
  exact canonicalFrameSlope_apply θ r

/-- Helper for Infrastructure I.16a: the uncurried canonical slope has an
explicit entry quotient normal form for joint analytic arguments. -/
theorem canonicalFrameSlope_uncurry_eq_entryQuotient :
    Function.uncurry canonicalFrameSlope =
      (fun z : ((ℝ × ℝ × ℝ) × ℝ) ↦
        -(canonicalFrameSlopeFirstE z.1 z.2 *
              canonicalFrameSlopeSecondX z.1 z.2 +
            canonicalFrameSlopeFirstX z.1 z.2 *
              canonicalFrameSlopeSecondE z.1 z.2) /
          (canonicalFrameSlopeFirstX z.1 z.2 *
              canonicalFrameSlopeSecondX z.1 z.2 -
            canonicalFrameSlopeFirstE z.1 z.2 *
              canonicalFrameSlopeSecondE z.1 z.2)) := by
  funext z
  exact canonicalFrameSlope_apply z.1 z.2

/-- Helper for Infrastructure I.16a: the joint canonical slope is analytic at
each base point, with the removable denominator normalized at radius zero. -/
theorem canonicalFrameSlope_analyticAt (θ : ℝ × ℝ × ℝ) :
    AnalyticAt ℝ (Function.uncurry canonicalFrameSlope) (θ, 0) := by
  have hfirstMetric := independentRadiusFirstMetricTriple_analyticAt θ
  have hfirstMetricE : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ × ℝ) × ℝ) ↦
        (independentRadiusFirstMetricTriple z).2.1) (θ, 0) :=
    analyticAt_fst.comp (analyticAt_snd.comp hfirstMetric)
  have hfirstMetricD : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ × ℝ) × ℝ) ↦
        (independentRadiusFirstMetricTriple z).2.2) (θ, 0) :=
    analyticAt_snd.comp (analyticAt_snd.comp hfirstMetric)
  have hfirstSpectral := independentRadiusFirstSpectral_analyticAt θ
  have hfirstSpectralLow : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ × ℝ) × ℝ) ↦
        (independentRadiusFirstSpectral z).1) (θ, 0) :=
    analyticAt_fst.comp hfirstSpectral
  have hsecondMetric := independentRadiusSecondMetricTriple_analyticAt θ
  have hsecondMetricE : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ × ℝ) × ℝ) ↦
        (independentRadiusSecondMetricTriple z).2.1) (θ, 0) :=
    analyticAt_fst.comp (analyticAt_snd.comp hsecondMetric)
  have hsecondMetricD : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ × ℝ) × ℝ) ↦
        (independentRadiusSecondMetricTriple z).2.2) (θ, 0) :=
    analyticAt_snd.comp (analyticAt_snd.comp hsecondMetric)
  have hsecondSpectral := independentRadiusSecondSpectral_analyticAt θ
  have hsecondSpectralLow : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ × ℝ) × ℝ) ↦
        (independentRadiusSecondSpectral z).1) (θ, 0) :=
    analyticAt_fst.comp hsecondSpectral
  have hradius : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ × ℝ) × ℝ) ↦ z.2) (θ, 0) := analyticAt_snd
  have hfirstE : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ × ℝ) × ℝ) ↦
        canonicalFrameSlopeFirstE z.1 z.2) (θ, 0) := by
    simpa only [canonicalFrameSlopeFirstE] using hfirstMetricE
  have hfirstX : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ × ℝ) × ℝ) ↦
        canonicalFrameSlopeFirstX z.1 z.2) (θ, 0) := by
    have hsub := hfirstMetricD.sub ((hradius.pow 2).mul hfirstSpectralLow)
    have hpath :
        (fun z : ((ℝ × ℝ × ℝ) × ℝ) ↦
          canonicalFrameSlopeFirstX z.1 z.2) =
          (fun z ↦ (independentRadiusFirstMetricTriple z).2.2 -
            z.2 ^ 2 * (independentRadiusFirstSpectral z).1) := by
      funext z
      rfl
    rw [hpath]
    exact hsub
  have hsecondE : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ × ℝ) × ℝ) ↦
        canonicalFrameSlopeSecondE z.1 z.2) (θ, 0) := by
    simpa only [canonicalFrameSlopeSecondE] using hsecondMetricE
  have hsecondX : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ × ℝ) × ℝ) ↦
        canonicalFrameSlopeSecondX z.1 z.2) (θ, 0) := by
    have hsub := hsecondMetricD.sub ((hradius.pow 2).mul hsecondSpectralLow)
    have hpath :
        (fun z : ((ℝ × ℝ × ℝ) × ℝ) ↦
          canonicalFrameSlopeSecondX z.1 z.2) =
          (fun z ↦ (independentRadiusSecondMetricTriple z).2.2 -
            z.2 ^ 2 * (independentRadiusSecondSpectral z).1) := by
      funext z
      rfl
    rw [hpath]
    exact hsub
  have hnum : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ × ℝ) × ℝ) ↦
        -(canonicalFrameSlopeFirstE z.1 z.2 *
              canonicalFrameSlopeSecondX z.1 z.2 +
            canonicalFrameSlopeFirstX z.1 z.2 *
              canonicalFrameSlopeSecondE z.1 z.2)) (θ, 0) := by
    exact (hfirstE.mul hsecondX).add (hfirstX.mul hsecondE) |>.neg
  have hden : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ × ℝ) × ℝ) ↦
        canonicalFrameSlopeFirstX z.1 z.2 *
              canonicalFrameSlopeSecondX z.1 z.2 -
            canonicalFrameSlopeFirstE z.1 z.2 *
              canonicalFrameSlopeSecondE z.1 z.2) (θ, 0) := by
    exact (hfirstX.mul hsecondX).sub (hfirstE.mul hsecondE)
  have hden0 :
      canonicalFrameSlopeFirstX θ 0 * canonicalFrameSlopeSecondX θ 0 -
        canonicalFrameSlopeFirstE θ 0 * canonicalFrameSlopeSecondE θ 0 ≠ 0 := by
    simp [canonicalFrameSlopeFirstE, canonicalFrameSlopeFirstX,
      canonicalFrameSlopeSecondE, canonicalFrameSlopeSecondX,
      independentRadiusFirstMetricTriple_zero,
      independentRadiusSecondMetricTriple_zero]
  have hquot := hnum.div hden hden0
  rw [canonicalFrameSlope_uncurry_eq_entryQuotient]
  exact hquot

/-- Infrastructure I.16a: the four public normal-form entry paths carry the
quadratic coefficients required by the raw-frame quotient. -/
theorem canonicalFrameSlope_entryGerms (θ : ℝ × ℝ × ℝ) :
    HasQuadraticGerm (canonicalFrameSlopeFirstE θ) 0 1 (-4 * θ.1) ∧
    HasQuadraticGerm (canonicalFrameSlopeFirstX θ) 1 (-2 * θ.1)
      (6 * θ.1 ^ 2 - 3) ∧
    HasQuadraticGerm (canonicalFrameSlopeSecondE θ) 0 2
      (θ.1 * (6 * θ.2.2 + θ.2.1 + 84) / 3) ∧
    HasQuadraticGerm (canonicalFrameSlopeSecondX θ) 1 (8 * θ.1)
      (4 * (6 * θ.2.2 * θ.1 ^ 2 + θ.2.1 * θ.1 ^ 2 +
        78 * θ.1 ^ 2 - 3) / 3 - 2) := by
  let b : ℝ := θ.1
  let P : ℝ := θ.2.1
  let J : ℝ := θ.2.2
  let radius : ℝ → ℝ := fun r ↦ r
  let firstC : ℝ → ℝ := fun r ↦
    (independentFirstResiduals b r (2 + P * b * r) (1 + J * b * r)).2.1
  let firstD : ℝ → ℝ := fun r ↦
    (independentFirstResiduals b r (2 + P * b * r) (1 + J * b * r)).2.2
  let firstL : ℝ → ℝ := fun r ↦
    (independentRadiusFirstSpectral (θ, r)).1
  let secondC : ℝ → ℝ := fun r ↦
    (independentSecondResiduals b r
      (independentRadiusFirstSpectral (θ, r)).1
      (independentRadiusFirstSpectral (θ, r)).2
      (independentRadiusFirstGradient (θ, r)).1
      (independentRadiusFirstGradient (θ, r)).2).2.1
  let secondD : ℝ → ℝ := fun r ↦
    (independentSecondResiduals b r
      (independentRadiusFirstSpectral (θ, r)).1
      (independentRadiusFirstSpectral (θ, r)).2
      (independentRadiusFirstGradient (θ, r)).1
      (independentRadiusFirstGradient (θ, r)).2).2.2
  let secondL : ℝ → ℝ := fun r ↦
    (independentRadiusSecondSpectral (θ, r)).1
  obtain ⟨_, hfirstC, hfirstD, _, _⟩ :=
    independentFirstResidualQuadraticGerms b P J
  obtain ⟨_, hsecondC, hsecondD, _, _⟩ :=
    independentRadiusSecondComponentQuadraticGerms θ
  obtain ⟨hfirstL, _, _, _⟩ := independentRadiusFirstFactorQuadraticGerms θ
  obtain ⟨hsecondL, _, _, _⟩ := independentRadiusSecondFactorQuadraticGerms θ
  have hfirstC' : HasQuadraticGerm firstC 1 (-4 * b)
      (-2 * J * b ^ 2 - P * b ^ 2 + 6 * b ^ 2 - 3) := by
    simpa only [firstC, b, P, J] using hfirstC
  have hfirstD' : HasQuadraticGerm firstD 1 (-2 * b) (6 * b ^ 2 - 1) := by
    simpa only [firstD, b, P, J] using hfirstD
  have hfirstL' : HasQuadraticGerm firstL 2
      (θ.1 * (2 * θ.2.2 + θ.2.1 + 4))
      (θ.2.1 * θ.2.2 * θ.1 ^ 2 + 4 * θ.2.2 * θ.1 ^ 2 +
        2 * θ.2.1 * θ.1 ^ 2 - 10 * θ.1 ^ 2 + 2) := by
    simpa only [firstL] using hfirstL
  have hsecondC' : HasQuadraticGerm secondC 2
      (θ.1 * (6 * θ.2.2 + θ.2.1 + 84) / 3)
      ((3 * θ.2.1 * θ.2.2 * θ.1 ^ 2 + 432 * θ.2.2 * θ.1 ^ 2 -
        θ.2.1 ^ 2 * θ.1 ^ 2 + 72 * θ.2.1 * θ.1 ^ 2 +
        2538 * θ.1 ^ 2 - 126) / 9) := by
    simpa only [secondC, b] using hsecondC
  have hsecondD' : HasQuadraticGerm secondD 1 (8 * θ.1)
      (4 * (6 * θ.2.2 * θ.1 ^ 2 + θ.2.1 * θ.1 ^ 2 +
        78 * θ.1 ^ 2 - 3) / 3) := by
    simpa only [secondD, b] using hsecondD
  have hsecondL' : HasQuadraticGerm secondL 2
      (θ.1 * (2 * θ.2.2 + θ.2.1 - 12))
      ((3 * θ.2.1 * θ.2.2 * θ.1 ^ 2 - 84 * θ.2.2 * θ.1 ^ 2 -
        26 * θ.2.1 * θ.1 ^ 2 - 510 * θ.1 ^ 2 + 30) / 3) := by
    simpa only [secondL] using hsecondL
  have hRadius : HasQuadraticGerm radius 0 1 0 := by
    apply (HasQuadraticGerm.model 0 1 0).congrFunction
    intro r
    simp [radius, quadraticModel]
  have hfirstERaw := hRadius.mul hfirstC'
  have hfirstEPath : ∀ r : ℝ,
      canonicalFrameSlopeFirstE θ r = radius r * firstC r := by
    intro r
    simp [canonicalFrameSlopeFirstE, independentRadiusFirstMetricTriple,
      independentRadiusFirstResiduals, radius, firstC, b, P, J]
  have hfirstE : HasQuadraticGerm (canonicalFrameSlopeFirstE θ) 0 1
      (-4 * θ.1) := by
    have hraw : HasQuadraticGerm (fun r ↦ radius r * firstC r) 0 1
        (-4 * b) := by
      apply hfirstERaw.congrCoefficients
      · ring
      · ring
      · ring
    apply hraw.congrFunction
    intro r
    exact hfirstEPath r
  have hfirstRadiusSquare : HasQuadraticGerm
      (fun r : ℝ ↦ radius r ^ 2) 0 0 1 := by
    have hraw := hRadius.mul hRadius
    have hcoeff : HasQuadraticGerm
        (fun r ↦ radius r * radius r) 0 0 1 := by
      apply hraw.congrCoefficients
      · ring
      · ring
      · ring
    apply hcoeff.congrFunction
    intro r
    simp [pow_two]
  have hfirstSquareLRaw := hfirstRadiusSquare.mul hfirstL'
  have hfirstSquareL : HasQuadraticGerm
      (fun r : ℝ ↦ radius r ^ 2 * firstL r) 0 0 2 := by
    apply hfirstSquareLRaw.congrCoefficients
    · ring
    · ring
    · ring
  have hfirstXRaw := hfirstD'.sub hfirstSquareL
  have hfirstXPath : ∀ r : ℝ,
      canonicalFrameSlopeFirstX θ r = firstD r - radius r ^ 2 * firstL r := by
    intro r
    simp [canonicalFrameSlopeFirstX, independentRadiusFirstMetricTriple,
      independentRadiusFirstResiduals, radius, firstD, firstL, b, P, J]
  have hfirstX : HasQuadraticGerm (canonicalFrameSlopeFirstX θ) 1 (-2 * θ.1)
      (6 * θ.1 ^ 2 - 3) := by
    have hraw : HasQuadraticGerm
        (fun r ↦ firstD r - radius r ^ 2 * firstL r) 1 (-2 * b)
          (6 * b ^ 2 - 3) := by
      apply hfirstXRaw.congrCoefficients
      · ring
      · ring
      · ring
    apply hraw.congrFunction
    intro r
    exact hfirstXPath r
  have hsecondERaw := hRadius.mul hsecondC'
  have hsecondEPath : ∀ r : ℝ,
      canonicalFrameSlopeSecondE θ r = radius r * secondC r := by
    intro r
    simp [canonicalFrameSlopeSecondE, independentRadiusSecondMetricTriple,
      independentSecondResiduals, radius, secondC, b]
  have hsecondE : HasQuadraticGerm (canonicalFrameSlopeSecondE θ) 0 2
      (θ.1 * (6 * θ.2.2 + θ.2.1 + 84) / 3) := by
    have hraw : HasQuadraticGerm (fun r ↦ radius r * secondC r) 0 2
        (θ.1 * (6 * θ.2.2 + θ.2.1 + 84) / 3) := by
      apply hsecondERaw.congrCoefficients
      · ring
      · ring
      · ring
    apply hraw.congrFunction
    intro r
    exact hsecondEPath r
  have hsecondSquareLRaw := hfirstRadiusSquare.mul hsecondL'
  have hsecondSquareL : HasQuadraticGerm
      (fun r : ℝ ↦ radius r ^ 2 * secondL r) 0 0 2 := by
    apply hsecondSquareLRaw.congrCoefficients
    · ring
    · ring
    · ring
  have hsecondXRaw := hsecondD'.sub hsecondSquareL
  have hsecondXPath : ∀ r : ℝ,
      canonicalFrameSlopeSecondX θ r = secondD r - radius r ^ 2 * secondL r := by
    intro r
    simp [canonicalFrameSlopeSecondX, independentRadiusSecondMetricTriple,
      independentSecondResiduals, radius, secondD, secondL, b]
  have hsecondX : HasQuadraticGerm (canonicalFrameSlopeSecondX θ) 1 (8 * θ.1)
      (4 * (6 * θ.2.2 * θ.1 ^ 2 + θ.2.1 * θ.1 ^ 2 +
        78 * θ.1 ^ 2 - 3) / 3 - 2) := by
    have hraw : HasQuadraticGerm
        (fun r ↦ secondD r - radius r ^ 2 * secondL r) 1 (8 * b)
          (4 * (6 * J * b ^ 2 + P * b ^ 2 + 78 * b ^ 2 - 3) / 3 - 2) := by
      apply hsecondXRaw.congrCoefficients
      · ring
      · ring
      · ring
    apply hraw.congrFunction
    intro r
    exact hsecondXPath r
  exact ⟨hfirstE, hfirstX, hsecondE, hsecondX⟩

/-- Helper for Infrastructure I.16a: `C²` certificates for the four canonical
entry paths complete the canonical slope's regularity and first-order law. -/
theorem canonicalFrameSlope_contDiffAt_and_deriv_of_entryRegularity
    (θ : ℝ × ℝ × ℝ)
    (hfirstERegular : ContDiffAt ℝ 2 (canonicalFrameSlopeFirstE θ) 0)
    (hfirstXRegular : ContDiffAt ℝ 2 (canonicalFrameSlopeFirstX θ) 0)
    (hsecondERegular : ContDiffAt ℝ 2 (canonicalFrameSlopeSecondE θ) 0)
    (hsecondXRegular : ContDiffAt ℝ 2 (canonicalFrameSlopeSecondX θ) 0) :
    ContDiffAt ℝ 2 (canonicalFrameSlope θ) 0 ∧
      deriv (canonicalFrameSlope θ) 0 = -3 := by
  obtain ⟨hfirstE, hfirstX, hsecondE, hsecondX⟩ :=
    canonicalFrameSlope_entryGerms θ
  have hden :
      canonicalFrameSlopeFirstX θ 0 * canonicalFrameSlopeSecondX θ 0 -
        canonicalFrameSlopeFirstE θ 0 * canonicalFrameSlopeSecondE θ 0 ≠ 0 := by
    simp [canonicalFrameSlopeFirstE, canonicalFrameSlopeFirstX,
      canonicalFrameSlopeSecondE, canonicalFrameSlopeSecondX,
      independentRadiusFirstMetricTriple_zero,
      independentRadiusSecondMetricTriple_zero]
  have hlinear : (1 : ℝ) + 2 = 3 := by
    norm_num
  have hresult := mixedRawFrameSlope_contDiffAt_and_deriv_of_entryCertificates
    hfirstERegular hfirstXRegular hsecondERegular hsecondXRegular
    hfirstE hfirstX hsecondE hsecondX hden hlinear
  have hcanonical : canonicalFrameSlope θ =
      (fun r ↦ -(canonicalFrameSlopeFirstE θ r * canonicalFrameSlopeSecondX θ r +
        canonicalFrameSlopeFirstX θ r * canonicalFrameSlopeSecondE θ r) /
        (canonicalFrameSlopeFirstX θ r * canonicalFrameSlopeSecondX θ r -
          canonicalFrameSlopeFirstE θ r * canonicalFrameSlopeSecondE θ r)) := by
    funext r
    rfl
  rw [hcanonical]
  exact hresult

/-- Helper for Infrastructure I.16a: an analytic function on the independent
radius parameter space restricts to a `C²` fixed-parameter radius slice. -/
theorem contDiffAt_radiusSlice_of_analyticAt
    {F : ((ℝ × ℝ × ℝ) × ℝ) → ℝ}
    (θ : ℝ × ℝ × ℝ)
    (hF : AnalyticAt ℝ F (θ, 0)) :
    ContDiffAt ℝ 2 (fun r : ℝ ↦ F (θ, r)) 0 := by
  have hpath : AnalyticAt ℝ
      (fun r : ℝ ↦ (θ, r)) 0 := by
    fun_prop
  exact (hF.comp hpath).contDiffAt (n := 2)

/-- Infrastructure I.16a: the public independent-radius metric and spectral
paths provide `C²` regularity for all four canonical quotient entries. -/
theorem canonicalFrameSlope_entryRegularity (θ : ℝ × ℝ × ℝ) :
    ContDiffAt ℝ 2 (canonicalFrameSlopeFirstE θ) 0 ∧
    ContDiffAt ℝ 2 (canonicalFrameSlopeFirstX θ) 0 ∧
    ContDiffAt ℝ 2 (canonicalFrameSlopeSecondE θ) 0 ∧
    ContDiffAt ℝ 2 (canonicalFrameSlopeSecondX θ) 0 := by
  have hfirstMetric := independentRadiusFirstMetricTriple_analyticAt θ
  have hfirstMetricE : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ × ℝ) × ℝ) ↦
        (independentRadiusFirstMetricTriple z).2.1) (θ, 0) :=
    analyticAt_fst.comp (analyticAt_snd.comp hfirstMetric)
  have hfirstMetricX : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ × ℝ) × ℝ) ↦
        (independentRadiusFirstMetricTriple z).2.2) (θ, 0) :=
    analyticAt_snd.comp (analyticAt_snd.comp hfirstMetric)
  have hfirstSpectral := independentRadiusFirstSpectral_analyticAt θ
  have hfirstSpectralLow : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ × ℝ) × ℝ) ↦
        (independentRadiusFirstSpectral z).1) (θ, 0) :=
    analyticAt_fst.comp hfirstSpectral
  have hsecondMetric := independentRadiusSecondMetricTriple_analyticAt θ
  have hsecondMetricE : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ × ℝ) × ℝ) ↦
        (independentRadiusSecondMetricTriple z).2.1) (θ, 0) :=
    analyticAt_fst.comp (analyticAt_snd.comp hsecondMetric)
  have hsecondMetricX : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ × ℝ) × ℝ) ↦
        (independentRadiusSecondMetricTriple z).2.2) (θ, 0) :=
    analyticAt_snd.comp (analyticAt_snd.comp hsecondMetric)
  have hsecondSpectral := independentRadiusSecondSpectral_analyticAt θ
  have hsecondSpectralLow : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ × ℝ) × ℝ) ↦
        (independentRadiusSecondSpectral z).1) (θ, 0) :=
    analyticAt_fst.comp hsecondSpectral
  have hfirstE := contDiffAt_radiusSlice_of_analyticAt θ hfirstMetricE
  have hfirstD := contDiffAt_radiusSlice_of_analyticAt θ hfirstMetricX
  have hfirstL := contDiffAt_radiusSlice_of_analyticAt θ hfirstSpectralLow
  have hsecondE := contDiffAt_radiusSlice_of_analyticAt θ hsecondMetricE
  have hsecondD := contDiffAt_radiusSlice_of_analyticAt θ hsecondMetricX
  have hsecondL := contDiffAt_radiusSlice_of_analyticAt θ hsecondSpectralLow
  have hfirstE' : ContDiffAt ℝ 2 (canonicalFrameSlopeFirstE θ) 0 := by
    have hpath : canonicalFrameSlopeFirstE θ =
        (fun r : ℝ ↦ (independentRadiusFirstMetricTriple (θ, r)).2.1) := by
      funext r
      rfl
    rw [hpath]
    exact hfirstE
  have hfirstX' : ContDiffAt ℝ 2 (canonicalFrameSlopeFirstX θ) 0 := by
    have hpow : ContDiffAt ℝ 2 (fun r : ℝ ↦ r ^ 2) 0 := by fun_prop
    have hprod := hpow.mul hfirstL
    have hsub := hfirstD.sub hprod
    have hpath : canonicalFrameSlopeFirstX θ =
        (fun r : ℝ ↦ (independentRadiusFirstMetricTriple (θ, r)).2.2 -
          r ^ 2 * (independentRadiusFirstSpectral (θ, r)).1) := by
      funext r
      rfl
    rw [hpath]
    exact hsub
  have hsecondE' : ContDiffAt ℝ 2 (canonicalFrameSlopeSecondE θ) 0 := by
    have hpath : canonicalFrameSlopeSecondE θ =
        (fun r : ℝ ↦ (independentRadiusSecondMetricTriple (θ, r)).2.1) := by
      funext r
      rfl
    rw [hpath]
    exact hsecondE
  have hsecondX' : ContDiffAt ℝ 2 (canonicalFrameSlopeSecondX θ) 0 := by
    have hpow : ContDiffAt ℝ 2 (fun r : ℝ ↦ r ^ 2) 0 := by fun_prop
    have hprod := hpow.mul hsecondL
    have hsub := hsecondD.sub hprod
    have hpath : canonicalFrameSlopeSecondX θ =
        (fun r : ℝ ↦ (independentRadiusSecondMetricTriple (θ, r)).2.2 -
          r ^ 2 * (independentRadiusSecondSpectral (θ, r)).1) := by
      funext r
      rfl
    rw [hpath]
    exact hsub
  exact ⟨hfirstE', hfirstX', hsecondE', hsecondX'⟩

/-- Helper for Infrastructure I.16a: the canonical independent-radius slope is
`C²` at the base radius and has linear coefficient `-3`. -/
theorem canonicalFrameSlope_contDiffAt_and_deriv
    (θ : ℝ × ℝ × ℝ) :
    ContDiffAt ℝ 2 (canonicalFrameSlope θ) 0 ∧
      deriv (canonicalFrameSlope θ) 0 = -3 := by
  obtain ⟨hfirstE, hfirstX, hsecondE, hsecondX⟩ :=
    canonicalFrameSlope_entryRegularity θ
  exact canonicalFrameSlope_contDiffAt_and_deriv_of_entryRegularity θ
    hfirstE hfirstX hsecondE hsecondX

end DFP.TwoLeg.Mixed
