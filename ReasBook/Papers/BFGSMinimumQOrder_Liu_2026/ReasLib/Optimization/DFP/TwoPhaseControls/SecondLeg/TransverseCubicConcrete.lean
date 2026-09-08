module

public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.Analyticity

public section

noncomputable section

open Filter
open scoped Matrix Topology

namespace DFP.SecondLeg

/-- Helper for `lowGradientFactorTransverseFDeriv_norm_bound`: the unnormalized low-frame
coordinate of the second-leg output gradient. -/
def lowGradientTransverseNumerator (x : ℝ × ℝ × ℝ) : ℝ :=
  let metric := outputMetric x.1 x.2.1 x.2.2
  let gradient := outputGradient x.1 x.2.1 x.2.2
  (metric 1 1 - RealSymmetric2.low (metric 0 0) (metric 0 1) (metric 1 1)) *
      gradient 0 - metric 0 1 * gradient 1

/-- Helper for `lowGradientFactorTransverseFDeriv_norm_bound`: the normalization of the
fixed low eigenvector used by the second-leg gradient factor. -/
def lowGradientTransverseDenominator (x : ℝ × ℝ × ℝ) : ℝ :=
  let metric := outputMetric x.1 x.2.1 x.2.2
  RealSymmetric2.lowDenom (metric 0 0) (metric 0 1) (metric 1 1)

/-- Lemma 4.15 adapter: frame-entry formulas and the normalized coordinate identity recover
the low-gradient factor as the explicit transverse quotient. -/
theorem gradientFactors_low_eq_transverseQuotient_of_frame
    (x : ℝ × ℝ × ℝ)
    (hcoordinate :
      (frame x.1 x.2.1 x.2.2).transpose *ᵥ
          outputGradient x.1 x.2.1 x.2.2 =
        ![(gradientFactors x.1 x.2.1 x.2.2).1,
          x.1 ^ 2 * (gradientFactors x.1 x.2.1 x.2.2).2])
    (hframe0 :
      frame x.1 x.2.1 x.2.2 0 0 =
        (outputMetric x.1 x.2.1 x.2.2 1 1 -
          RealSymmetric2.low (outputMetric x.1 x.2.1 x.2.2 0 0)
            (outputMetric x.1 x.2.1 x.2.2 0 1)
            (outputMetric x.1 x.2.1 x.2.2 1 1)) /
          lowGradientTransverseDenominator x)
    (hframe1 :
      frame x.1 x.2.1 x.2.2 1 0 =
        -outputMetric x.1 x.2.1 x.2.2 0 1 /
          lowGradientTransverseDenominator x) :
    (gradientFactors x.1 x.2.1 x.2.2).1 =
      lowGradientTransverseNumerator x / lowGradientTransverseDenominator x := by
  have hlow := congrArg (fun v : Fin 2 → ℝ ↦ v 0) hcoordinate
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.transpose_apply] at hlow
  have hlow' :
      frame x.1 x.2.1 x.2.2 0 0 * outputGradient x.1 x.2.1 x.2.2 0 +
          frame x.1 x.2.1 x.2.2 1 0 * outputGradient x.1 x.2.1 x.2.2 1 =
        (gradientFactors x.1 x.2.1 x.2.2).1 := by
    simpa using hlow
  rw [← hlow', lowGradientTransverseNumerator]
  dsimp [lowGradientTransverseNumerator, lowGradientTransverseDenominator]
  dsimp [lowGradientTransverseDenominator] at hframe0 hframe1 ⊢
  rw [hframe0, hframe1]
  field_simp
  ring_nf

end DFP.SecondLeg
