/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_24

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Theorem 6.41 is `source-facing`: the textbook object is the projection point of a convex set,
and the chapter's canonical owner for that object is the set-valued projection mapping `P[C]`
used throughout Chapter 6. Domain sampling for this item uses the local owner
`projection_mapping`, the companion membership lemma `mem_projection_mapping_iff`, the first-order
criterion `norm_eq_iInf_iff_real_inner_le_zero` from mathlib's Hilbert projection API, and the
owner-level convex uniqueness theorem `projection_mapping_subsingleton` from Theorem 6.24. These
show that the primitive data are only the convex set `C`, the base point `x`, and the candidate
projection point `u ∈ C`; closure, nonemptiness, and finite-dimensional completeness are not part
of the core variational statement. The owner-level derived API here is the variational
characterization of membership in `P[C] x`; the textbook singleton identity `P[C] x = {u}` is then
a thin source-facing wrapper over that characterization together with the owner uniqueness theorem,
rather than a new point-valued projection wrapper. -/

/-- Helper for Theorem 6.41: for a convex set `C`, a point `u ∈ C` belongs to the projection set
`P[C] x` exactly when it satisfies the Hilbert-space variational inequality against every point of
`C`. -/
theorem mem_projection_mapping_iff_inner_le_zero
    (C : Set E) (hC_convex : Convex ℝ C) (x : E) {u : E} (hu : u ∈ C) :
    u ∈ P[C] x ↔ ∀ y ∈ C, inner ℝ (x - u) (y - u) ≤ 0 := by
  constructor
  · intro hu_proj
    -- Convert projection membership into the canonical infimum characterization, then apply the
    -- Hilbert-space first-order criterion.
    exact (norm_eq_iInf_iff_real_inner_le_zero hC_convex hu).1
      (norm_eq_iInf_of_mem_projection_mapping hu_proj)
  · intro hu_inner
    -- The variational inequality recovers the infimum formula for `‖x - u‖`.
    have hu_eq_iInf : ‖x - u‖ = ⨅ z : C, ‖x - z‖ :=
      (norm_eq_iInf_iff_real_inner_le_zero hC_convex hu).2 hu_inner
    rw [mem_projection_mapping_iff, isMinOn_iff]
    constructor
    · exact hu
    · intro y hy
      -- The infimum over `C` is bounded below by `0`, so it is below each sampled distance.
      have h_bdd : BddBelow (Set.range fun z : C ↦ ‖x - z‖) := by
        refine ⟨0, ?_⟩
        rintro _ ⟨z, rfl⟩
        exact norm_nonneg _
      have h_inf_le : (⨅ z : C, ‖x - z‖) ≤ ‖x - y‖ := by
        simpa using ciInf_le h_bdd ⟨y, hy⟩
      simpa [norm_sub_rev] using le_trans hu_eq_iInf.le h_inf_le

-- Proof sketch: first rewrite the variational condition as membership in `P[C] x` via
-- `mem_projection_mapping_iff_inner_le_zero`. Since `C` is convex, the owner theorem
-- `projection_mapping_subsingleton` shows that `P[C] x` is a subsingleton, so membership of `u`
-- upgrades immediately to the singleton identity `P[C] x = {u}`.
/-- Theorem 6.41: second projection theorem. For a convex set `C` and a point `u ∈ C`, the
equality `P[C] x = {u}` holds if and only if `inner ℝ (x - u) (y - u) ≤ 0` for every `y ∈ C`.
The usual nonempty and closed hypotheses are unnecessary for this variational characterization
once a candidate point `u ∈ C` is fixed. -/
theorem projection_mapping_eq_singleton_iff_inner_le_zero
    (C : Set E) (hC_convex : Convex ℝ C) (x : E) {u : E} (hu : u ∈ C) :
    P[C] x = {u} ↔ ∀ y ∈ C, inner ℝ (x - u) (y - u) ≤ 0 := by
  constructor
  · intro h
    -- Read the singleton identity as projection membership, then use the variational criterion.
    exact (mem_projection_mapping_iff_inner_le_zero C hC_convex x hu).1 (by simp [h])
  · intro hu_inner
    -- Recover projection membership from the variational inequality, then use uniqueness.
    have hu_proj : u ∈ P[C] x :=
      (mem_projection_mapping_iff_inner_le_zero C hC_convex x hu).2 hu_inner
    exact (projection_mapping_subsingleton C hC_convex x).eq_singleton_of_mem hu_proj

end
