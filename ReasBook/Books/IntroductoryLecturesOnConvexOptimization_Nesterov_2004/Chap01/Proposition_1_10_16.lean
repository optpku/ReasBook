/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_18

-- Declarations for this item will be appended below by the statement pipeline.

open Filter Set Topology

universe u

variable {α : Type u} [TopologicalSpace α]

namespace IsBarrierFunctionOn

/-
Source/core/bridge triage for Proposition 1.10.16:
- source-facing: the sum of two barrier functions is again a barrier on the common interior;
- core/canonical owner: the continuous maps `C(interior 𝓕, ℝ)`;
- bridge/view: restrict each owner map along `ContinuousMap.inclusion (interior_mono ...)` and add
  the resulting continuous maps on `interior (𝓕₁ ∩ 𝓕₂)`.

The restricted sum is derived entirely from the owner `ContinuousMap` API, so this file keeps the
source-facing proposition and instance at the intrinsic topological level and does not introduce a
parallel public wrapper definition specialized to Euclidean coordinates.
-/
variable {𝓕₁ 𝓕₂ : Set α}
variable (F₁ : C(interior 𝓕₁, ℝ)) (F₂ : C(interior 𝓕₂, ℝ))

/-- Restrict both summands to `interior (𝓕₁ ∩ 𝓕₂)` and add them there. -/
private abbrev interAdd : C(interior (𝓕₁ ∩ 𝓕₂), ℝ) :=
  F₁.comp (ContinuousMap.inclusion (interior_mono inter_subset_left)) +
    F₂.comp (ContinuousMap.inclusion (interior_mono inter_subset_right))

/-- Helper for Proposition 1.10.16: a point in the closure of a closed set lies either in its
interior or on its frontier. -/
private lemma mem_interior_or_frontier_of_mem_closure_of_closed
    {s : Set α} (hs : IsClosed s) {x : α} (hx : x ∈ closure s) :
    x ∈ interior s ∨ x ∈ frontier s := by
  have hx' : x ∈ s := by
    simpa [hs.closure_eq] using hx
  -- Closedness lets us turn the closure statement into the standard interior/frontier dichotomy.
  by_cases hfront : x ∈ frontier s
  · exact Or.inr hfront
  · exact Or.inl ((mem_interior_iff_notMem_frontier hx').2 hfront)

/-- Helper for Proposition 1.10.16: if a sequence in a smaller interior converges to a point that
is still interior to the larger set, continuity gives a finite limit for the restricted summand. -/
private lemma tendsto_restricted_summand_of_mem_interior
    {s 𝓕 : Set α} (F : C(interior 𝓕, ℝ)) (hsub : interior s ⊆ interior 𝓕)
    (x : ℕ → interior s) {xBar : α}
    (hx : Tendsto (fun k ↦ (x k : α)) atTop (nhds xBar))
    (hxBar : xBar ∈ interior 𝓕) :
    Tendsto (fun k ↦ F ⟨x k, hsub (x k).property⟩)
      atTop (nhds (F ⟨xBar, hxBar⟩)) := by
  let xF : ℕ → interior 𝓕 := fun k ↦ ⟨x k, hsub (x k).property⟩
  have hxF : Tendsto xF atTop (nhds ⟨xBar, hxBar⟩) := by
    -- Passing to the subtype keeps exactly the same ambient convergence.
    apply tendsto_subtype_rng.mpr
    simpa [xF] using hx
  -- Continuity of the owner map transports the convergence to a finite real limit.
  exact F.continuous.continuousAt.tendsto.comp hxF

/-- The pointwise sum of two barrier functions, restricted to `interior (𝓕₁ ∩ 𝓕₂)`, diverges to
`+∞` along sequences in that interior converging to a boundary point of `𝓕₁ ∩ 𝓕₂`. -/
-- Proof sketch: use `frontier_inter_subset` to reduce a boundary point of `𝓕₁ ∩ 𝓕₂` to the
-- boundary of one factor or the other, apply the corresponding barrier property there, and combine
-- it with continuity of the remaining summand using the standard `atTop` addition lemmas.
private theorem add_inter_tendsTo_atTop_of_tendsto_frontier
    (h₁ : IsBarrierFunctionOn 𝓕₁ F₁)
    (h₂ : IsBarrierFunctionOn 𝓕₂ F₂)
    (x : ℕ → interior (𝓕₁ ∩ 𝓕₂)) {xBar : α}
    (hx : Tendsto (fun k ↦ (x k : α)) atTop (nhds xBar))
    (hxBar : xBar ∈ frontier (𝓕₁ ∩ 𝓕₂)) :
    Tendsto
      (fun k : ℕ ↦ interAdd F₁ F₂ (x k))
      atTop (atTop : Filter ℝ) := by
  let x₁ : ℕ → interior 𝓕₁ := fun k ↦ ⟨x k, interior_mono inter_subset_left (x k).property⟩
  let x₂ : ℕ → interior 𝓕₂ := fun k ↦ ⟨x k, interior_mono inter_subset_right (x k).property⟩
  have hx₁ : Tendsto (fun k ↦ (x₁ k : α)) atTop (nhds xBar) := by
    simpa [x₁] using hx
  have hx₂ : Tendsto (fun k ↦ (x₂ k : α)) atTop (nhds xBar) := by
    simpa [x₂] using hx
  have hxCases :
      xBar ∈ frontier 𝓕₁ ∩ closure 𝓕₂ ∪ closure 𝓕₁ ∩ frontier 𝓕₂ :=
    (frontier_inter_subset 𝓕₁ 𝓕₂) hxBar
  -- Restrict the common-interior sequence to each factor so the two barrier hypotheses apply.
  rcases hxCases with hxLeft | hxRight
  · rcases hxLeft with ⟨hxBar₁, hxBar₂Closure⟩
    have hF₁ :
        Tendsto (fun k ↦ F₁ (x₁ k)) atTop (atTop : Filter ℝ) :=
      h₁.tendsTo_atTop_of_tendsto_frontier x₁ hx₁ hxBar₁
    -- In the first textbook branch, the left summand blows up and the right summand is either
    -- still finite by continuity or also blows up on its own frontier.
    rcases mem_interior_or_frontier_of_mem_closure_of_closed h₂.isClosed hxBar₂Closure with
      hxBar₂ | hxBar₂
    · have hF₂ :
          Tendsto (fun k ↦ F₂ (x₂ k)) atTop (nhds (F₂ ⟨xBar, hxBar₂⟩)) := by
        simpa [x₂] using
          tendsto_restricted_summand_of_mem_interior F₂
            (interior_mono inter_subset_right) x hx hxBar₂
      have hsum :
          Tendsto (fun k ↦ F₁ (x₁ k) + F₂ (x₂ k)) atTop (atTop : Filter ℝ) :=
        hF₁.atTop_add hF₂
      simpa [interAdd, x₁, x₂] using hsum
    · have hF₂ :
          Tendsto (fun k ↦ F₂ (x₂ k)) atTop (atTop : Filter ℝ) :=
        h₂.tendsTo_atTop_of_tendsto_frontier x₂ hx₂ hxBar₂
      have hle : (fun k ↦ F₁ (x₁ k)) ≤ᶠ[atTop] fun k ↦ F₁ (x₁ k) + F₂ (x₂ k) := by
        filter_upwards [hF₂.eventually (eventually_ge_atTop 0)] with k hk
        exact le_add_of_nonneg_right hk
      have hsum :
          Tendsto (fun k ↦ F₁ (x₁ k) + F₂ (x₂ k)) atTop (atTop : Filter ℝ) :=
        tendsto_atTop_mono' atTop hle hF₁
      simpa [interAdd, x₁, x₂] using hsum
  · rcases hxRight with ⟨hxBar₁Closure, hxBar₂⟩
    have hF₂ :
        Tendsto (fun k ↦ F₂ (x₂ k)) atTop (atTop : Filter ℝ) :=
      h₂.tendsTo_atTop_of_tendsto_frontier x₂ hx₂ hxBar₂
    -- The symmetric branch interchanges the roles of the two factors.
    rcases mem_interior_or_frontier_of_mem_closure_of_closed h₁.isClosed hxBar₁Closure with
      hxBar₁ | hxBar₁
    · have hF₁ :
          Tendsto (fun k ↦ F₁ (x₁ k)) atTop (nhds (F₁ ⟨xBar, hxBar₁⟩)) := by
        simpa [x₁] using
          tendsto_restricted_summand_of_mem_interior F₁
            (interior_mono inter_subset_left) x hx hxBar₁
      have hsum :
          Tendsto (fun k ↦ F₁ (x₁ k) + F₂ (x₂ k)) atTop (atTop : Filter ℝ) :=
        hF₁.add_atTop hF₂
      simpa [interAdd, x₁, x₂] using hsum
    · have hF₁ :
          Tendsto (fun k ↦ F₁ (x₁ k)) atTop (atTop : Filter ℝ) :=
        h₁.tendsTo_atTop_of_tendsto_frontier x₁ hx₁ hxBar₁
      have hle : (fun k ↦ F₂ (x₂ k)) ≤ᶠ[atTop] fun k ↦ F₁ (x₁ k) + F₂ (x₂ k) := by
        filter_upwards [hF₁.eventually (eventually_ge_atTop 0)] with k hk
        exact le_add_of_nonneg_left hk
      have hsum :
          Tendsto (fun k ↦ F₁ (x₁ k) + F₂ (x₂ k)) atTop (atTop : Filter ℝ) :=
        tendsto_atTop_mono' atTop hle hF₂
      simpa [interAdd, x₁, x₂] using hsum

/-- Proposition 1.10.16: if `F₁` and `F₂` are barrier functions for `𝓕₁` and `𝓕₂` and
`interior (𝓕₁ ∩ 𝓕₂)` is nonempty, then their pointwise sum, restricted to the common interior,
is a barrier function for `𝓕₁ ∩ 𝓕₂`. -/
theorem add_inter
    (h₁ : IsBarrierFunctionOn 𝓕₁ F₁)
    (h₂ : IsBarrierFunctionOn 𝓕₂ F₂)
    (hinter : (interior (𝓕₁ ∩ 𝓕₂)).Nonempty) :
    IsBarrierFunctionOn (𝓕₁ ∩ 𝓕₂)
      (F₁.comp (ContinuousMap.inclusion (interior_mono inter_subset_left)) +
        F₂.comp (ContinuousMap.inclusion (interior_mono inter_subset_right))) := by
  change IsBarrierFunctionOn (𝓕₁ ∩ 𝓕₂) (interAdd F₁ F₂)
  let _ : Fact (IsClosed (𝓕₁ ∩ 𝓕₂)) := ⟨h₁.isClosed.inter h₂.isClosed⟩
  -- The wrapper only packages the repaired frontier-growth proof for the restricted sum.
  refine
    { interior_nonempty := hinter
      tendsTo_atTop_of_tendsto_frontier := ?_ }
  intro x xBar hx hxBar
  exact add_inter_tendsTo_atTop_of_tendsto_frontier F₁ F₂ h₁ h₂ x hx hxBar

instance
    [h₁ : IsBarrierFunctionOn 𝓕₁ F₁]
    [h₂ : IsBarrierFunctionOn 𝓕₂ F₂]
    [Fact ((interior (𝓕₁ ∩ 𝓕₂)).Nonempty)] :
    IsBarrierFunctionOn (𝓕₁ ∩ 𝓕₂)
      (F₁.comp (ContinuousMap.inclusion (interior_mono inter_subset_left)) +
        F₂.comp (ContinuousMap.inclusion (interior_mono inter_subset_right))) :=
  add_inter F₁ F₂ h₁ h₂ Fact.out

end IsBarrierFunctionOn
