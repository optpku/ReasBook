/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Filter ERealFunction

variable {X : Type u} [TopologicalSpace X]

private lemma seq_lower_semicontinuous_implies_real_epigraph_seq_closed
    (f : X → EReal)
    (hseq : ∀ ⦃u : ℕ → X⦄ ⦃x : X⦄, Tendsto u atTop (nhds x) →
      f x ≤ liminf (fun n ↦ f (u n)) atTop) :
    IsSeqClosed (epigraph f) := by
  intro u p hu_mem hu_tendsto
  have hfst : Tendsto (fun n ↦ (u n).1) atTop (nhds p.1) := by
    simpa using (continuous_fst.tendsto p).comp hu_tendsto
  have hsnd : Tendsto (fun n ↦ (u n).2) atTop (nhds p.2) := by
    simpa using (continuous_snd.tendsto p).comp hu_tendsto
  have hsnd_ereal : Tendsto (fun n ↦ ((u n).2 : EReal)) atTop (nhds (p.2 : EReal)) := by
    exact (continuous_coe_real_ereal.tendsto p.2).comp hsnd
  have hlimsnd : liminf (fun n ↦ ((u n).2 : EReal)) atTop = (p.2 : EReal) := by
    simpa using Filter.Tendsto.liminf_eq hsnd_ereal
  have hlim_le :
      liminf (fun n ↦ f ((u n).1)) atTop ≤ liminf (fun n ↦ ((u n).2 : EReal)) atTop := by
    refine Filter.liminf_le_liminf <| Filter.Eventually.of_forall fun n ↦ ?_
    simpa using hu_mem n
  calc
    f p.1 ≤ liminf (fun n ↦ f ((u n).1)) atTop := hseq hfst
    _ ≤ liminf (fun n ↦ ((u n).2 : EReal)) atTop := hlim_le
    _ = (p.2 : EReal) := hlimsnd

private lemma real_epigraph_seq_closed_implies_lower_level_set_seq_closed
    (f : X → EReal)
    (hEpi : IsSeqClosed (epigraph f)) :
    ∀ ξ : ℝ, IsSeqClosed (lowerLevelSet f ξ) := by
  intro ξ u x hu_mem hu_tendsto
  have hprod_mem : ∀ n, (u n, ξ) ∈ epigraph f := by
    intro n
    simpa using hu_mem n
  have hprod_tendsto : Tendsto (fun n ↦ (u n, ξ)) atTop (nhds (x, ξ)) := by
    exact Filter.Tendsto.prodMk_nhds hu_tendsto tendsto_const_nhds
  simpa using hEpi hprod_mem hprod_tendsto

private lemma subseq_mem_lower_level_set_of_liminf_lt
    (f : X → EReal) {u : ℕ → X} {x : X} {ξ : ℝ}
    (hu : Tendsto u atTop (nhds x))
    (hξ : liminf (fun n ↦ f (u n)) atTop < (ξ : EReal)) :
    ∃ ns : ℕ → ℕ, Tendsto (fun n ↦ u (ns n)) atTop (nhds x) ∧
      ∀ n, f (u (ns n)) ≤ (ξ : EReal) := by
  let p : X → Prop := fun y ↦ f y < (ξ : EReal)
  have hfreq : ∃ᶠ n in atTop, p (u n) := by
    exact Filter.frequently_lt_of_liminf_lt (by isBoundedDefault) hξ
  obtain ⟨ns, hns_tendsto, hns_mem⟩ := Filter.subseq_forall_of_frequently hu hfreq
  exact ⟨ns, hns_tendsto, fun n ↦ le_of_lt (hns_mem n)⟩

private lemma lower_level_set_seq_closed_implies_seq_lower_semicontinuous
    (f : X → EReal)
    (hLevel : ∀ ξ : ℝ, IsSeqClosed (lowerLevelSet f ξ)) :
    ∀ ⦃u : ℕ → X⦄ ⦃x : X⦄, Tendsto u atTop (nhds x) →
      f x ≤ liminf (fun n ↦ f (u n)) atTop := by
  intro u x hu
  by_contra hnot
  have hlt : liminf (fun n ↦ f (u n)) atTop < f x := lt_of_not_ge hnot
  obtain ⟨ξ, hξ_left, hξ_right⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
  obtain ⟨ns, hns_tendsto, hns_mem⟩ :=
    subseq_mem_lower_level_set_of_liminf_lt f hu hξ_left
  have hx_mem : f x ≤ (ξ : EReal) := by
    exact hLevel ξ hns_mem hns_tendsto
  exact (not_le_of_gt hξ_right) hx_mem

/-- Lemma 1.36: for an extended-real-valued function on a topological space, sequential lower
semicontinuity, sequential closedness of the real-height epigraph, and sequential closedness of
every real lower level set are equivalent. -/
theorem sequentialLowerSemicontinuous_real_epigraph_seqClosed_lowerLevelSet_seqClosed_tfae
    (f : X → EReal) :
    List.TFAE [
      ∀ ⦃u : ℕ → X⦄ ⦃x : X⦄, Tendsto u atTop (nhds x) →
        f x ≤ liminf (fun n ↦ f (u n)) atTop,
      IsSeqClosed (epigraph f),
      ∀ ξ : ℝ, IsSeqClosed (lowerLevelSet f ξ)
    ] := by
  tfae_have 1 → 2 := seq_lower_semicontinuous_implies_real_epigraph_seq_closed f
  tfae_have 2 → 3 := real_epigraph_seq_closed_implies_lower_level_set_seq_closed f
  tfae_have 3 → 1 := lower_level_set_seq_closed_implies_seq_lower_semicontinuous f
  tfae_finish
