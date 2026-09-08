module

public import ReasLib.Analysis.Calculus.ContDiff.ZeroExtensionJets

public section

open Filter Set Topology

universe u v

namespace HasFDerivAt

/-- At a point in the complement of a closed set, extending a function by zero across the
set preserves its certified Frechet derivative. -/
theorem indicator_compl_of_mem
    {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {Gamma : Set E} (hGamma : IsClosed Gamma)
    {f : E → F} {f' : E →L[ℝ] F} {x : E} (hx : x ∈ Gammaᶜ)
    (h : HasFDerivAt f f' x) :
    HasFDerivAt (Gammaᶜ.indicator f) f' x := by
  have hxnot : x ∉ Gamma := by
    simpa only [mem_compl_iff] using hx
  have hlocal : Gammaᶜ.indicator f =ᶠ[𝓝 x] f :=
    Filter.eventuallyEq_of_mem (hGamma.compl_mem_nhds hxnot)
      (fun y hy ↦ indicator_of_mem hy f)
  exact h.congr_of_eventuallyEq hlocal

end HasFDerivAt

namespace HasGradientAt

/-- At a point in the complement of a closed set, extending a scalar function by zero
across the set preserves its certified gradient. -/
theorem indicator_compl_of_mem
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {Gamma : Set E} (hGamma : IsClosed Gamma) {f : E → ℝ} {g x : E}
    (hx : x ∈ Gammaᶜ) (h : HasGradientAt f g x) :
    HasGradientAt (Gammaᶜ.indicator f) g x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  exact h.hasFDerivAt.indicator_compl_of_mem hGamma hx

end HasGradientAt
