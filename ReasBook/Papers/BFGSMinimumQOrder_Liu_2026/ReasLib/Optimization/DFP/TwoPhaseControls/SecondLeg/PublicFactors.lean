module

public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg

public section

noncomputable section

open scoped Topology

namespace DFP.SecondLeg

/-!
The main SecondLeg file keeps the residual-coordinate construction private.  These projection
lemmas expose the small, stable interface needed by the transverse derivative estimates without
unfolding the full eigenframe construction in downstream proofs.
-/

/-- Helper for Lemma 4.15: the gradient-factor pair is analytic at the canceled base point. -/
theorem gradientFactors_analyticAt_base :
    AnalyticAt ℝ
      (fun x : ℝ × ℝ × ℝ ↦ gradientFactors x.1 x.2.1 x.2.2)
      (0, 2, 1) := by
  have hFactors := factorsAnalytic
  have hGradient : AnalyticAt ℝ
      (fun x : ℝ × ℝ × ℝ ↦
        (factors x.1 x.2.1 x.2.2).2.1) (0, 2, 1) := by
    exact analyticAt_fst.comp (analyticAt_snd.comp hFactors)
  apply hGradient.congr
  filter_upwards [] with x
  rfl

/-- Helper for Lemma 4.15: analyticity of the gradient factors yields their base continuity. -/
theorem gradientFactors_continuousAt_base :
    ContinuousAt
      (fun x : ℝ × ℝ × ℝ ↦ gradientFactors x.1 x.2.1 x.2.2)
      (0, 2, 1) := by
  exact gradientFactors_analyticAt_base.continuousAt

/-- Helper for Lemma 4.15: the normalized gradient factors take the canonical base value. -/
theorem gradientFactors_base : gradientFactors 0 2 1 = (1, 2) := by
  exact congrArg (fun t ↦ t.2.1) factorsBase

/-- Helper for Lemma 4.15: the low gradient factor is nonzero on a neighborhood of the
    canceled base point. -/
theorem eventually_gradientFactors_low_ne_zero :
    ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      (gradientFactors x.1 x.2.1 x.2.2).1 ≠ 0 := by
  have hcont := gradientFactors_continuousAt_base
  have hlow : ContinuousAt
      (fun x : ℝ × ℝ × ℝ ↦ (gradientFactors x.1 x.2.1 x.2.2).1)
      (0, 2, 1) := continuousAt_fst.comp hcont
  have hbase :
      (gradientFactors (0 : ℝ) (2 : ℝ) (1 : ℝ)).1 ≠ 0 := by
    rw [gradientFactors_base]
    norm_num
  exact hlow.eventually_ne hbase

end DFP.SecondLeg
