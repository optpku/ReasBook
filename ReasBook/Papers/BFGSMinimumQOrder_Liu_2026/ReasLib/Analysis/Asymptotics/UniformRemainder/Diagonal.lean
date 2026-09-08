module

public import ReasLib.Analysis.Asymptotics.UniformRemainder
import all ReasLib.Analysis.Asymptotics.UniformRemainder

public section

open Filter
open scoped Topology

namespace Asymptotics.IsUniformRemainderOn

universe u v

variable {Θ : Type u} {E : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A uniform quadratic remainder stays `o(1)` after restriction to the parabolic
diagonal `r = ε²` and normalization by `ε³`. -/
theorem inv_cube_smul_comp_square_isLittleO_one
    {R : Θ → ℝ → E} {s : Set Θ} {C : ℝ} {θ : ℝ → Θ}
    (hR : Asymptotics.IsUniformRemainderOn R s C 2)
    (hθ : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), θ ε ∈ s) :
    (fun ε : ℝ => (ε ^ 3)⁻¹ • R (θ ε) (ε ^ 2))
      =o[𝓝[≠] 0] (fun _ => (1 : ℝ)) := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hbound⟩ := hR
  have hsquare_tendsto :
      Tendsto (fun ε : ℝ => |ε ^ 2|) (𝓝 0) (𝓝 0) := by
    have hcont : ContinuousAt (fun ε : ℝ => |ε ^ 2|) 0 :=
      (continuousAt_id.pow 2).abs
    simpa [ContinuousAt] using hcont
  have hsquare :
      ∀ᶠ ε in 𝓝[≠] (0 : ℝ), |ε ^ 2| < δ :=
    (hsquare_tendsto.eventually (Iio_mem_nhds hδ)).filter_mono inf_le_left
  have hcoef_tendsto :
      Tendsto (fun ε : ℝ => |C| * |ε|) (𝓝 0) (𝓝 0) := by
    have hconst : ContinuousAt (fun _ : ℝ => |C|) 0 :=
      continuousAt_const
    have habs : ContinuousAt (fun ε : ℝ => |ε|) 0 :=
      continuous_abs.continuousAt
    have hcont : ContinuousAt (fun ε : ℝ => |C| * |ε|) 0 :=
      hconst.mul habs
    simpa [ContinuousAt] using hcont
  have hsmall :
      ∀ᶠ ε in 𝓝[≠] (0 : ℝ), |C| * |ε| < c :=
    (hcoef_tendsto.eventually (Iio_mem_nhds hc)).filter_mono inf_le_left
  filter_upwards [hθ, hsquare, hsmall, self_mem_nhdsWithin] with
      ε hθε hεδ hεsmall hεne
  have hne : ε ≠ 0 := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hεne
  have hb := hbound (θ ε) hθε (ε ^ 2) hεδ
  have hb' :
      ‖R (θ ε) (ε ^ 2)‖ ≤ |C| * |ε ^ 2| ^ (2 : ℝ) :=
    hb.trans (mul_le_mul_of_nonneg_right (le_abs_self C)
      (Real.rpow_nonneg (abs_nonneg _) _))
  calc
    ‖(ε ^ 3)⁻¹ • R (θ ε) (ε ^ 2)‖ =
        |(ε ^ 3)⁻¹| * ‖R (θ ε) (ε ^ 2)‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ |(ε ^ 3)⁻¹| * (|C| * |ε ^ 2| ^ (2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hb' (abs_nonneg _)
    _ = |C| * |ε| := by
      rw [abs_inv, abs_pow, Real.rpow_two, abs_pow]
      field_simp [abs_ne_zero.mpr hne]
    _ ≤ c := hεsmall.le
    _ = c * ‖(1 : ℝ)‖ := by norm_num

end Asymptotics.IsUniformRemainderOn
