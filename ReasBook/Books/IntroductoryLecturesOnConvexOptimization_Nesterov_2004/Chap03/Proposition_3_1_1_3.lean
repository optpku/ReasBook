/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped WithTopConvexAnalysis

variable {X : Type u} [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X]

/-- Proposition 3.1.1.3, generalized from the textbook `ℝⁿ` setting: a continuous convex
real-valued function on a real topological module is a closed convex function; equivalently, after
coercing `f` to `WithTop ℝ`, its epigraph is a closed convex subset of `X × ℝ`. -/
-- Proof sketch: for the `WithTop ℝ`-valued coercion of `f`, the effective domain is all of `X`,
-- so `ClosedConvexFunction` reduces to closedness and convexity of the usual epigraph.
-- Convexity is exactly `hf_convex.convex_epigraph`, and closedness follows from
-- `IsClosed.epigraph isClosed_univ hf_cont.continuousOn`.
theorem closedConvexFunction_coe_of_convexOn_continuous
    {f : X → ℝ}
    (hf_convex : ConvexOn ℝ Set.univ f) (hf_cont : Continuous f) :
    ClosedConvexFunction (fun x ↦ (f x : WithTop ℝ)) := by
  let g : X → WithTop ℝ := fun x ↦ (f x : WithTop ℝ)
  have hconstrained :
      constrainedEpigraph (dom g) g =
        {p : X × ℝ | p.1 ∈ dom g ∧ withTopRealPart g p.1 ≤ p.2} :=
    constrainedEpigraph_eq_epigraph_withTopRealPart (subset_rfl : dom g ⊆ dom g)
  refine ⟨subset_rfl, ?_, ?_⟩
  · rw [hconstrained]
    simpa [withTopEffectiveDomain, withTopRealPart, g] using
      IsClosed.epigraph isClosed_univ hf_cont.continuousOn
  · rw [hconstrained]
    simpa [withTopEffectiveDomain, withTopRealPart, g] using hf_convex.convex_epigraph
