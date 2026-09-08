module

public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.FixedSectionDerivativeBridge

public section

open Filter
open scoped Topology

universe u

namespace LocalCutoff.GraphTransform

variable {Y : Type u} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- A translated first-order remainder that is little-o of its scalar increment
determines the corresponding derivative at every base point. -/
theorem predecessorHasDerivAt_of_rawDefectLittleO
    (f d : ℝ → Y)
    (hraw : ∀ u : ℝ,
      (fun h : ℝ => f (u + h) - f u - h • d u) =o[𝓝 0] (fun h : ℝ => h)) :
    ∀ u : ℝ, HasDerivAt f (d u) u := by
  intro u
  -- The scalar remainder is the Fréchet remainder for the span-singleton map.
  have hspan :
      (fun h : ℝ => f (u + h) - f u -
        (ContinuousLinearMap.toSpanSingleton ℝ (d u)) h) =o[𝓝 0]
        (fun h : ℝ => h) := by
    simpa only [ContinuousLinearMap.toSpanSingleton_apply] using hraw u
  -- Apply the standard translated little-o bridge, then expose its scalar derivative.
  have hfrechet := hasFDerivAt_of_isLittleO_shift_bridge f u
    (ContinuousLinearMap.toSpanSingleton ℝ (d u)) hspan
  simpa only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] using hfrechet.hasDerivAt

end LocalCutoff.GraphTransform
