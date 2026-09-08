module

public import ReasLib.Analysis.Asymptotics.UniformRemainder.Diagonal
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.LeadingTransverse.Basic
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedMap.Basic

public section

/-!
# Conditional asymptotics for the leading transverse map

This companion isolates the bookkeeping that turns uniform shape and scale remainder
bounds into the normalized transverse little-o estimate.  The two analytic expansion
certificates remain explicit hypotheses.
-/

open Filter
open scoped Topology

namespace DFP.TwoLeg.Mixed

noncomputable section

/-- The error in the linear shape expansion of the mixed map. -/
def shapeRemainder (θ : ℝ × ℝ × ℝ) (r : ℝ) : ℝ :=
  let y := map θ.1 (input θ r)
  y.2.1 - 2 - (θ.1 * (6 * θ.2.2 - θ.2.1 + 348) / 9) * r

/-- The error in the linear high-scale expansion of the mixed map. -/
def scaleRemainder (θ : ℝ × ℝ × ℝ) (r : ℝ) : ℝ :=
  let y := map θ.1 (input θ r)
  y.2.2 - 1 - 8 * θ.1 * r

/-- Away from `ε = 0`, the normalized transverse error is exactly the pair of
normalized shape and scale remainders. -/
theorem normalized_transverseIncrement_sub_eq_remainders
    (ε P J : ℝ) (hε : ε ≠ 0) :
    (ε ^ 3)⁻¹ • transverseIncrement ε (P, J) - leadingTransverse (P, J) =
      ((ε ^ 3)⁻¹ • shapeRemainder (ε, P, J) (ε ^ 2),
        (ε ^ 3)⁻¹ • scaleRemainder (ε, P, J) (ε ^ 2)) := by
  rw [transverseIncrement_eq, leadingTransverse_eq]
  ext <;> simp [shapeRemainder, scaleRemainder]
  · field_simp [hε]
  · field_simp [hε]

/-- A fixed coefficient pair lies in the mixed parameter set for all sufficiently
small signed controls. -/
theorem eventually_mem_parameterSet {β B P J : ℝ}
    (hβ : 0 < β) (hz : dist (P, J) (0, 0) ≤ B) :
    ∀ᶠ ε in 𝓝[≠] (0 : ℝ), (ε, P, J) ∈ parameterSet β B := by
  have habs_tendsto : Tendsto (fun ε : ℝ => |ε|) (𝓝 0) (𝓝 0) := by
    have hcont : ContinuousAt (fun ε : ℝ => |ε|) 0 :=
      continuous_abs.continuousAt
    simpa [ContinuousAt] using hcont
  have hsmall : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), |ε| < β :=
    (habs_tendsto.eventually (Iio_mem_nhds hβ)).filter_mono inf_le_left
  filter_upwards [hsmall] with ε hε
  rw [mem_parameterSet_iff]
  refine ⟨abs_le.mp hε.le, ?_⟩
  exact hz

/-- Uniform quadratic shape and scale expansions imply the normalized transverse
little-o estimate along `b = ε`, `r = ε²`. -/
theorem transverseIncrement_asymptotic_of_uniformRemainders
    {β B Cshape Cscale P J : ℝ}
    (hβ : 0 < β) (hz : dist (P, J) (0, 0) ≤ B)
    (hshape : Asymptotics.IsUniformRemainderOn
      shapeRemainder (parameterSet β B) Cshape 2)
    (hscale : Asymptotics.IsUniformRemainderOn
      scaleRemainder (parameterSet β B) Cscale 2) :
    (fun ε ↦
      (ε ^ 3)⁻¹ • transverseIncrement ε (P, J) - leadingTransverse (P, J))
      =o[𝓝[≠] 0] (fun _ ↦ (1 : ℝ)) := by
  have hθ : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), (ε, P, J) ∈ parameterSet β B :=
    eventually_mem_parameterSet hβ hz
  have hshape_o :=
    Asymptotics.IsUniformRemainderOn.inv_cube_smul_comp_square_isLittleO_one
      hshape hθ
  have hscale_o :=
    Asymptotics.IsUniformRemainderOn.inv_cube_smul_comp_square_isLittleO_one
      hscale hθ
  have hpair := hshape_o.prod_left hscale_o
  refine hpair.congr' ?_ (Filter.Eventually.of_forall fun _ => rfl)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hεne : ε ≠ 0 := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hε
  exact (normalized_transverseIncrement_sub_eq_remainders ε P J hεne).symm

end

end DFP.TwoLeg.Mixed
