module

public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusNormalForm
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusNormalForm

public section

noncomputable section

open Filter
open scoped Matrix Topology

namespace DFP.TwoLeg.Mixed

/-!
This file gives the denominator-cleared interface for the second normalized gradient.
The raw map and its oriented-frame branch remain outside this file; the interface only
uses the already-proved analytic normal form and is therefore safe to consume from the
independent-radius cancellation proof.
-/

/-- The normalized second-leg metric entries along an
independent-radius path, written as a single scalar triple. -/
def independentRadiusSecondMetricTriple
    (z : (ℝ × ℝ × ℝ) × ℝ) : ℝ × ℝ × ℝ :=
  (z.2 ^ 2 * (independentSecondResiduals z.1.1 z.2
      (independentRadiusFirstSpectral z).1
      (independentRadiusFirstSpectral z).2
      (independentRadiusFirstGradient z).1
      (independentRadiusFirstGradient z).2).1,
    z.2 * (independentSecondResiduals z.1.1 z.2
      (independentRadiusFirstSpectral z).1
      (independentRadiusFirstSpectral z).2
      (independentRadiusFirstGradient z).1
      (independentRadiusFirstGradient z).2).2.1,
    (independentSecondResiduals z.1.1 z.2
      (independentRadiusFirstSpectral z).1
      (independentRadiusFirstSpectral z).2
      (independentRadiusFirstGradient z).1
      (independentRadiusFirstGradient z).2).2.2)

/-- The low-eigenvector normalization denominator of the
second-leg metric triple. -/
def independentRadiusSecondGradientDenominator
    (z : (ℝ × ℝ × ℝ) × ℝ) : ℝ :=
  let m := independentRadiusSecondMetricTriple z
  RealSymmetric2.lowDenom m.1 m.2.1 m.2.2

/-- The second-leg gradient numerator obtained by clearing
the low-eigenvector normalization denominator. -/
def independentRadiusSecondGradientNumerator
    (z : (ℝ × ℝ × ℝ) × ℝ) : ℝ × ℝ :=
  let d := independentRadiusSecondGradientDenominator z
  let g := independentRadiusSecondGradient z
  (d * g.1, d * g.2)

/-- The named metric triple is definitionally the triple used by the normal-form metric
analyticity theorem. -/
lemma independentRadiusSecondMetricTriple_eq (z : (ℝ × ℝ × ℝ) × ℝ) :
    independentRadiusSecondMetricTriple z =
      (z.2 ^ 2 * (independentSecondResiduals z.1.1 z.2
        (independentRadiusFirstSpectral z).1
        (independentRadiusFirstSpectral z).2
        (independentRadiusFirstGradient z).1
        (independentRadiusFirstGradient z).2).1,
       z.2 * (independentSecondResiduals z.1.1 z.2
        (independentRadiusFirstSpectral z).1
        (independentRadiusFirstSpectral z).2
        (independentRadiusFirstGradient z).1
        (independentRadiusFirstGradient z).2).2.1,
       (independentSecondResiduals z.1.1 z.2
        (independentRadiusFirstSpectral z).1
        (independentRadiusFirstSpectral z).2
        (independentRadiusFirstGradient z).1
        (independentRadiusFirstGradient z).2).2.2) := by
  rfl

/-- The named second-leg metric triple is analytic at every zero-radius base point. -/
lemma independentRadiusSecondMetricTriple_analyticAt (θ : ℝ × ℝ × ℝ) :
    AnalyticAt ℝ independentRadiusSecondMetricTriple (θ, 0) := by
  unfold independentRadiusSecondMetricTriple
  exact independentRadiusSecondMetric_analyticAt θ

/-- The named second-leg metric triple has diagonal base value `(0, 0, 1)`. -/
lemma independentRadiusSecondMetricTriple_zero (θ : ℝ × ℝ × ℝ) :
    independentRadiusSecondMetricTriple (θ, 0) = (0, 0, 1) := by
  unfold independentRadiusSecondMetricTriple
  simp only [independentRadiusFirstSpectral_zero θ,
    independentRadiusFirstGradient_zero θ]
  exact independentRadiusSecondMetric_zero θ

/-- The cleared-gradient denominator is analytic at every zero-radius base point. -/
lemma independentRadiusSecondGradientDenominator_analyticAt (θ : ℝ × ℝ × ℝ) :
    AnalyticAt ℝ independentRadiusSecondGradientDenominator (θ, 0) := by
  have hm := independentRadiusSecondMetricTriple_analyticAt θ
  have hm0 := independentRadiusSecondMetricTriple_zero θ
  have hden := analyticAt_lowDenom_of_analyticAt_metric hm hm0
  unfold independentRadiusSecondGradientDenominator
  exact hden

/-- The cleared-gradient denominator equals one at the zero-radius base point. -/
lemma independentRadiusSecondGradientDenominator_zero (θ : ℝ × ℝ × ℝ) :
    independentRadiusSecondGradientDenominator (θ, 0) = 1 := by
  rw [independentRadiusSecondGradientDenominator,
    independentRadiusSecondMetricTriple_zero]
  norm_num [RealSymmetric2.lowDenom, RealSymmetric2.low, RealSymmetric2.gap]

/-- The cleared-gradient denominator is nonzero on a neighborhood of each base point. -/
lemma eventually_independentRadiusSecondGradientDenominator_ne (θ : ℝ × ℝ × ℝ) :
    ∀ᶠ z in 𝓝 (θ, 0), independentRadiusSecondGradientDenominator z ≠ 0 := by
  have hcont := (independentRadiusSecondGradientDenominator_analyticAt θ).continuousAt
  have hlim : Tendsto independentRadiusSecondGradientDenominator
      (𝓝 (θ, 0)) (𝓝 (1 : ℝ)) := by
    simpa only [ContinuousAt, independentRadiusSecondGradientDenominator_zero θ] using hcont
  exact hlim.eventually (eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num))

/-- The denominator-cleared gradient numerator is analytic at every zero-radius base point. -/
lemma independentRadiusSecondGradientNumerator_analyticAt (θ : ℝ × ℝ × ℝ) :
    AnalyticAt ℝ independentRadiusSecondGradientNumerator (θ, 0) := by
  have hd := independentRadiusSecondGradientDenominator_analyticAt θ
  have hg := independentRadiusSecondGradient_analyticAt θ
  have hfirst := hd.mul (analyticAt_fst.comp hg)
  have hsecond := hd.mul (analyticAt_snd.comp hg)
  have hpair := hfirst.prod hsecond
  unfold independentRadiusSecondGradientNumerator
  dsimp
  apply hpair.congr
  filter_upwards [] with z
  rfl

/-- On the nonzero-denominator neighborhood, division of the cleared numerator recovers the
original second-leg gradient factors. -/
lemma independentRadiusSecondGradientNumerator_div_eq_eventually
    (θ : ℝ × ℝ × ℝ) :
    ∀ᶠ z in 𝓝 (θ, 0),
      (independentRadiusSecondGradientNumerator z).1 /
          independentRadiusSecondGradientDenominator z =
        (independentRadiusSecondGradient z).1 ∧
      (independentRadiusSecondGradientNumerator z).2 /
          independentRadiusSecondGradientDenominator z =
        (independentRadiusSecondGradient z).2 := by
  filter_upwards [eventually_independentRadiusSecondGradientDenominator_ne θ] with z hz
  constructor
  · unfold independentRadiusSecondGradientNumerator
    dsimp
    exact mul_div_cancel_left₀ _ hz
  · unfold independentRadiusSecondGradientNumerator
    dsimp
    exact mul_div_cancel_left₀ _ hz

end DFP.TwoLeg.Mixed
