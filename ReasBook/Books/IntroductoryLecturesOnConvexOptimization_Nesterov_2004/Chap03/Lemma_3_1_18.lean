/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Pointwise

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-
Lemma 3.1.18 is a source-facing item in the chapter's tangent-cone domain.

Primary domain:
- tangent cones of convex subsets of real normed spaces.

Relevant owner-style declarations sampled before refinement:
- `posTangentConeAt`
- `mem_posTangentConeAt_of_segment_subset`
- `PointedCone.hull`
- `Set.vsub_singleton`

Best owner abstraction:
- `posTangentConeAt Q xBar`

Primitive data:
- the feasible set `Q`
- the base point `xBar`

Derived API:
- the displacement set `Q -ᵥ ({xBar} : Set E)`
- the pointed conical hull `PointedCone.hull ℝ (Q -ᵥ ({xBar} : Set E))`

Source/core/bridge triage:
- source-facing: the textbook feasible-direction cone at `xBar`
- core/canonical: `posTangentConeAt Q xBar`
- bridge/view: the displacement-set realization and its pointed cone hull

Mathlib's field-valued `tangentConeAt ℝ Q xBar` is a different owner abstraction from the textbook
positive cone of feasible directions; at boundary points it can be strictly larger. This source
item therefore uses the chapter's canonical owner `posTangentConeAt`. The textbook `ℝⁿ` statement
is a specialization of this real normed-space theorem.
-/

/-- Lemma 3.1.18, owner-level equality form: for a convex set `Q` in a real normed space and a
point `xBar ∈ Q`, the positive tangent cone at `xBar` is the closure of the canonical pointed cone
hull of the feasible displacements `Q - xBar`. The textbook `ℝⁿ` closed boundary-point case is the
specialization `IsClosed Q` and `xBar ∈ frontier Q`. -/
-- Proof sketch: the tangent cone is the positive-direction owner `posTangentConeAt Q xBar`, while
-- the feasible-direction model is `PointedCone.hull ℝ (Q -ᵥ ({xBar} : Set E))`. Convexity turns
-- small feasible increments into segments from `xBar`, and the tangent-cone closure description
-- identifies the resulting cone with the closure of this pointed hull.
theorem posTangentConeAt_eq_closure_pointedConeHull_vsub_singleton
    (Q : Set E) (hQ_convex : Convex ℝ Q) (xBar : E) (hxBar : xBar ∈ Q) :
    posTangentConeAt Q xBar =
      closure (PointedCone.hull ℝ (Q -ᵥ ({xBar} : Set E))) := by
  let S : Set E := Q -ᵥ ({xBar} : Set E)
  -- The displacement set remains convex after translating `Q` by `-xBar`.
  have hS_convex : Convex ℝ S := by
    simpa [S, Set.vsub_singleton, vsub_eq_sub] using hQ_convex.sub (convex_singleton xBar)
  have hxBar_mem_singleton : xBar ∈ ({xBar} : Set E) := by
    simp
  have hxBar_vsub_self : xBar -ᵥ xBar = (0 : E) := by
    simp [vsub_eq_sub]
  -- The zero displacement is feasible because the base point itself lies in `Q`.
  have hS_zero : (0 : E) ∈ S := by
    exact ⟨xBar, hxBar, xBar, hxBar_mem_singleton, hxBar_vsub_self⟩
  -- Every feasible displacement comes from a segment starting at `xBar`, so it is tangent.
  have hS_subset : S ⊆ posTangentConeAt Q xBar := by
    intro v hv
    have hv' : v ∈ (· -ᵥ xBar) '' Q := by
      simpa [S, Set.vsub_singleton] using hv
    rcases hv' with ⟨x, hx, rfl⟩
    simpa [vsub_eq_sub] using
      sub_mem_posTangentConeAt_of_segment_subset (hQ_convex.segment_subset hxBar hx)
  have hsmul_mem :
      ∀ {r : ℝ} {v : E}, 0 ≤ r → v ∈ posTangentConeAt Q xBar → r • v ∈ posTangentConeAt Q xBar := by
    intro r v hr hv
    rcases exists_fun_of_mem_tangentConeAt hv with ⟨α, l, hl, c, d, hd₀, hds, hcd⟩
    let rr : NNReal := ⟨r, hr⟩
    refine mem_tangentConeAt_of_seq l (fun n ↦ rr * c n) d hd₀ hds ?_
    simpa [rr, mul_smul] using (tendsto_const_nhds.smul hcd)
  have hconvexHull_pointed : (ConvexCone.hull ℝ S).Pointed :=
    ConvexCone.subset_hull hS_zero
  have hpointedHull_eq_convexHull : (PointedCone.hull ℝ S : Set E) = ConvexCone.hull ℝ S := by
    ext v
    constructor
    · intro hv
      let C : PointedCone ℝ E := (ConvexCone.hull ℝ S).toPointedCone hconvexHull_pointed
      have hspan : PointedCone.hull ℝ S ≤ C := by
        refine Submodule.span_le.2 ?_
        intro x hx
        exact ConvexCone.subset_hull hx
      exact hspan hv
    · intro hv
      have hconvexHull_le : ConvexCone.hull ℝ S ≤ (PointedCone.hull ℝ S : ConvexCone ℝ E) := by
        exact ConvexCone.hull_min (fun x hx ↦ PointedCone.subset_hull hx)
      exact hconvexHull_le hv
  have hmem_pointedHull {v : E} :
      v ∈ (PointedCone.hull ℝ S : Set E) ↔ ∃ r : ℝ, 0 < r ∧ v ∈ r • S := by
    rw [hpointedHull_eq_convexHull]
    simpa using (ConvexCone.mem_hull_of_convex hS_convex : v ∈ ConvexCone.hull ℝ S ↔ _)
  have hpointedHull_subset : (PointedCone.hull ℝ S : Set E) ⊆ posTangentConeAt Q xBar := by
    intro v hv
    rcases hmem_pointedHull.mp hv with ⟨r, hr, y, hy, rfl⟩
    exact hsmul_mem hr.le (hS_subset hy)
  have hclosed : IsClosed (posTangentConeAt Q xBar) := by
    rw [posTangentConeAt, tangentConeAt_def]
    exact isClosed_setOf_clusterPt
  apply Set.Subset.antisymm
  · intro v hv
    -- Tangent-cone witnesses provide scaled feasible increments converging to `v`.
    rcases exists_fun_of_mem_tangentConeAt hv with ⟨α, l, hl, c, d, hd₀, hds, hcd⟩
    have hdS : ∀ᶠ n in l, d n ∈ S := by
      filter_upwards [hds] with n hn
      have hn' : d n ∈ (· -ᵥ xBar) '' Q := by
        refine ⟨xBar + d n, hn, ?_⟩
        simp [vsub_eq_sub]
      simpa [S, Set.vsub_singleton] using hn'
    have hcdHull : ∀ᶠ n in l, c n • d n ∈ (PointedCone.hull ℝ S : Set E) := by
      filter_upwards [hdS] with n hn
      simpa [NNReal.smul_def] using
        (PointedCone.hull ℝ S).smul_mem (show 0 ≤ (c n : ℝ) from (c n).2)
          (PointedCone.subset_hull hn)
    exact mem_closure_of_tendsto hcd hcdHull
  -- Closedness upgrades the pointed-hull inclusion to an inclusion of its closure.
  · exact hclosed.closure_subset_iff.2 hpointedHull_subset

end
