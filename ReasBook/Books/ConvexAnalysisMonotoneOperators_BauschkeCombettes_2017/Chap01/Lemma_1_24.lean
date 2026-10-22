/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {X : Type u}

private lemma epigraph_eq_preimage_erealEpigraph (f : X → EReal) :
    epigraph f =
      (fun p : X × ℝ ↦ (p.1, (p.2 : EReal))) ⁻¹' {q : X × EReal | f q.1 ≤ q.2} := by
  rfl

private lemma lowerLevelSet_eq_preimage_epigraph (f : X → EReal) (ξ : ℝ) :
    lowerLevelSet f ξ = (fun x : X ↦ (x, ξ)) ⁻¹' epigraph f := by
  rfl

private lemma preimage_Ioi_eq_iUnion_compl_lowerLevelSet_rat (f : X → EReal) (α : EReal) :
    f ⁻¹' Set.Ioi α =
      ⋃ q : {q : ℚ // α < (((q : ℚ) : ℝ) : EReal)}, (lowerLevelSet f ((q : ℚ) : ℝ))ᶜ := by
  ext x
  constructor
  · intro hx
    rcases EReal.exists_rat_btwn_of_lt hx with ⟨q, hαq, hqf⟩
    refine Set.mem_iUnion.2 ⟨⟨q, hαq⟩, ?_⟩
    simpa [lowerLevelSet, Set.mem_compl, Set.mem_preimage, not_le] using hqf
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨q, hxq⟩
    have hαq : α < (((q : ℚ) : ℝ) : EReal) := q.2
    have hqf : ((((q : ℚ) : ℝ) : EReal) < f x) := by
      simpa [lowerLevelSet, Set.mem_compl, Set.mem_preimage, not_le] using hxq
    exact hαq.trans hqf

variable [TopologicalSpace X]

/-- Lemma 1.24: an extended-real-valued function on a topological space is lower semicontinuous if
and only if each of its real lower level sets is closed. -/
theorem lowerSemicontinuous_iff_isClosed_lowerLevelSet (f : X → EReal) :
    LowerSemicontinuous f ↔ ∀ ξ : ℝ, IsClosed (lowerLevelSet f ξ) := by
  constructor
  · intro hf ξ
    simpa [lowerLevelSet] using hf.isClosed_preimage ((ξ : ℝ) : EReal)
  · intro hLevel
    rw [lowerSemicontinuous_iff_isOpen_preimage]
    intro α
    rw [preimage_Ioi_eq_iUnion_compl_lowerLevelSet_rat]
    exact isOpen_iUnion fun q ↦ (hLevel ((q : ℚ) : ℝ)).isOpen_compl

/-- Lemma 1.24: an extended-real-valued function on a topological space is lower semicontinuous if
and only if its real-height epigraph is closed. -/
theorem lowerSemicontinuous_iff_isClosed_epigraph (f : X → EReal) :
    LowerSemicontinuous f ↔ IsClosed (epigraph f) := by
  constructor
  · intro hf
    rw [epigraph_eq_preimage_erealEpigraph]
    exact hf.isClosed_epigraph.preimage
      (continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd))
  · intro hEpi
    have hLevel : ∀ ξ : ℝ, IsClosed (lowerLevelSet f ξ) := by
      intro ξ
      rw [lowerLevelSet_eq_preimage_epigraph]
      exact hEpi.preimage (Continuous.prodMk continuous_id continuous_const)
    exact (lowerSemicontinuous_iff_isClosed_lowerLevelSet f).2 hLevel

/-- Textbook presentation of Lemma 1.24: lower semicontinuity, closedness of the real-height
epigraph, and closedness of all real lower level sets are equivalent assertions. -/
theorem lowerSemicontinuous_real_epigraph_closed_lowerLevelSet_closed_tfae (f : X → EReal) :
    List.TFAE [LowerSemicontinuous f, IsClosed (epigraph f), ∀ ξ : ℝ, IsClosed (lowerLevelSet f ξ)] := by
  tfae_have 1 → 2 := fun hf ↦
    (lowerSemicontinuous_iff_isClosed_epigraph f).1 hf
  tfae_have 2 → 3 := fun hEpi ↦
    (lowerSemicontinuous_iff_isClosed_lowerLevelSet f).1
      ((lowerSemicontinuous_iff_isClosed_epigraph f).2 hEpi)
  tfae_have 3 → 1 := fun hLevel ↦
    (lowerSemicontinuous_iff_isClosed_lowerLevelSet f).2 hLevel
  tfae_finish

end ERealFunction
