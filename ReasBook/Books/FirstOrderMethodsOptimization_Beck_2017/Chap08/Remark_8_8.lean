/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_2
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_6
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Topology

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Remark 8.8: if `f` is convex and the feasible set `C` lies in the interior of `dom(f)`, then
`f` is subdifferentiable at every point of `C`, equivalently `C ⊆ dom(∂ f)`. -/
-- Proof sketch: for each `x ∈ C`, the inclusion `C ⊆ interior (effective_domain f)` gives
-- `x ∈ interior (effective_domain f)`. Apply the interior-point subdifferentiability theorem
-- `subdifferential_nonempty_at_interior_point` and rewrite the conclusion using
-- `mem_subdifferential_domain`.
theorem subset_subdifferential_domain_of_subset_interior_effective_domain
    (f : E → EReal) (C : Set E) (hf_convex : is_convex_function f)
    (hC : C ⊆ interior (effective_domain f)) :
    C ⊆ subdifferential_domain f := by
  intro x hxC
  -- Move from the feasible-set inclusion to interior membership at the chosen point.
  rw [mem_subdifferential_domain]
  -- The interior-point theorem supplies a nonempty subdifferential.
  exact subdifferential_nonempty_at_interior_point f x hf_convex (hC hxC)

/-- If `C` is closed and `f` is closed, then the feasible lower level set
`C ∩ {x | f x ≤ fOpt}` is closed. -/
-- Proof sketch: use `lowerSemicontinuous_iff_isClosed_real_sublevelSets` to show that the real
-- sublevel set `f ⁻¹' Iic (fOpt : EReal)` is closed, then intersect it with the closed feasible
-- set `C`.
theorem isClosed_inter_real_sublevelSet
    (f : E → EReal) (C : Set E) (fOpt : ℝ)
    (hC_closed : IsClosed C) (hf_closed : LowerSemicontinuous f) :
    IsClosed (C ∩ f ⁻¹' Set.Iic (fOpt : EReal)) := by
  -- Closedness of `f` gives closedness of each real sublevel set.
  have hsublevel_closed : IsClosed (f ⁻¹' Set.Iic (fOpt : EReal)) :=
    (lowerSemicontinuous_iff_isClosed_real_sublevelSets f).mp hf_closed fOpt
  -- Intersect the closed feasible set with the closed sublevel set.
  exact hC_closed.inter hsublevel_closed

/-- If the feasible lower level set `C ∩ {x | f x ≤ fOpt}` is nonempty, then every point outside
that set has strictly positive distance to it. -/
-- Proof sketch: first obtain closedness of `C ∩ f ⁻¹' Iic (fOpt : EReal)` from
-- `isClosed_inter_real_sublevelSet`. Then apply the metric-space characterization
-- `IsClosed.notMem_iff_infDist_pos` for nonempty closed sets.
theorem infDist_pos_of_not_mem_inter_real_sublevelSet
    (f : E → EReal) (C : Set E) (fOpt : ℝ)
    (hC_closed : IsClosed C) (hf_closed : LowerSemicontinuous f)
    (hX_nonempty : (C ∩ f ⁻¹' Set.Iic (fOpt : EReal)).Nonempty)
    {x : E} (hx : x ∉ C ∩ f ⁻¹' Set.Iic (fOpt : EReal)) :
    0 < Metric.infDist x (C ∩ f ⁻¹' Set.Iic (fOpt : EReal)) := by
  -- First recover the closedness of the feasible optimal set.
  have hX_closed : IsClosed (C ∩ f ⁻¹' Set.Iic (fOpt : EReal)) :=
    isClosed_inter_real_sublevelSet f C fOpt hC_closed hf_closed
  -- For a nonempty closed set, nonmembership is equivalent to strictly positive distance.
  exact (hX_closed.notMem_iff_infDist_pos hX_nonempty).mp hx

end
