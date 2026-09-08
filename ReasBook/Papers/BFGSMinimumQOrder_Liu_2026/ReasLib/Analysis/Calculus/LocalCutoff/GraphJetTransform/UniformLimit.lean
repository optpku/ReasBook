module

public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Defs

public section

open Filter
open scoped Topology

universe u v

namespace LocalCutoff.GraphTransform

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Infrastructure I.16: a locally uniform limit of differentiable iterates is one
order smoother when the limiting derivative field already has the lower regularity. -/
theorem contDiffAt_succ_of_tendstoLocallyUniformlyOn
    {ι : Type*} {l : Filter ι} [NeBot l]
    (n : ℕ) {s : Set E} {x : E}
    (hs : IsOpen s) (hx : x ∈ s)
    {f : ι → E → F} {g : E → F}
    {g' : E → E →L[ℝ] F}
    (hf : ∀ i, DifferentiableOn ℝ (f i) s)
    (hderiv : TendstoLocallyUniformlyOn (fderiv ℝ ∘ f) g' l s)
    (hvalue : ∀ y ∈ s, Tendsto (fun i ↦ f i y) l (𝓝 (g y)))
    (hg' : ContDiffAt ℝ n g' x) :
    ContDiffAt ℝ (n + 1) g x := by
  apply contDiffAt_succ_iff_hasFDerivAt.mpr
  refine ⟨g', ?_, hg'⟩
  refine ⟨s, hs.mem_nhds hx, ?_⟩
  intro y hy
  exact hasFDerivAt_of_tendsto_locally_uniformly_on' hs hderiv hf hvalue hy

/- Helper for Infrastructure I.16: a locally uniform limit remains one order smoother
when each approximant supplies an explicit derivative field. -/
theorem contDiffAt_succ_of_tendstoLocallyUniformlyOn_hasFDeriv
    {ι : Type*} {l : Filter ι} [NeBot l]
    (n : ℕ) {s : Set E} {x : E}
    (hs : IsOpen s) (hx : x ∈ s)
    {f : ι → E → F} {g : E → F}
    {f' : ι → E → E →L[ℝ] F} {g' : E → E →L[ℝ] F}
    (hf : ∀ i y, y ∈ s → HasFDerivAt (f i) (f' i y) y)
    (hderiv : TendstoLocallyUniformlyOn f' g' l s)
    (hvalue : ∀ y ∈ s, Tendsto (fun i ↦ f i y) l (𝓝 (g y)))
    (hg' : ContDiffAt ℝ n g' x) :
    ContDiffAt ℝ (n + 1) g x := by
  apply contDiffAt_succ_iff_hasFDerivAt.mpr
  refine ⟨g', ?_, hg'⟩
  refine ⟨s, hs.mem_nhds hx, ?_⟩
  intro y hy
  exact hasFDerivAt_of_tendstoLocallyUniformlyOn hs hderiv hf hvalue hy

end LocalCutoff.GraphTransform
