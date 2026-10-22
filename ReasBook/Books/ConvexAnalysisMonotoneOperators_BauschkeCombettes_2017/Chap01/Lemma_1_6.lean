/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4

-- Declarations for this item will be appended below by the statement pipeline.

open Set

universe u v

namespace ERealFunction

-- Proof sketch: extensionality on pairs `(x, ξ)` reduces the claim to the order fact
-- `iSup_le_iff`, which says `⨆ i, f i x ≤ ξ` iff `∀ i, f i x ≤ ξ`.
/-- Lemma 1.6 (1): the epigraph of the pointwise supremum of a family of extended-real-valued
functions is the intersection of the epigraphs of the family members. -/
theorem epigraph_iSup {X : Type u} {I : Type v} (f : I → X → EReal) :
    epigraph (⨆ i, f i) = ⋂ i, epigraph (f i) := by
  ext p
  rcases p with ⟨x, ξ⟩
  -- Membership on both sides is an upper-bound condition at `(x, ξ)`.
  simp [iSup_le_iff]

-- Proof sketch: extensionality on `(x, ξ)` reduces the statement to the finite complete-lattice
-- identity `iInf_le_iff`, which under `[Finite I]` rewrites `⨅ i, f i x ≤ ξ` as
-- `∃ i, f i x ≤ ξ`.
/-- Lemma 1.6 (2): if the index type is finite, then the epigraph of the pointwise minimum is the
union of the epigraphs of the family members. -/
theorem epigraph_iInf_of_finite {X : Type u} {I : Type v} [Finite I] (f : I → X → EReal) :
    epigraph (⨅ i, f i) = ⋃ i, epigraph (f i) := by
  classical
  let _ : Fintype I := Fintype.ofFinite I
  have hinf (x : X) (ξ : ℝ) :
      Finset.univ.inf (fun i : I ↦ f i x) ≤ (ξ : EReal) ↔
        ∃ i, f i x ≤ (ξ : EReal) := by
    have h :
        Finset.univ.inf (fun i : I ↦ f i x) ≤ (ξ : EReal) ↔
          ∃ i, i ∈ (Finset.univ : Finset I) ∧ f i x ≤ (ξ : EReal) :=
      Finset.inf_le_iff (EReal.coe_lt_top ξ)
    simp only [Finset.mem_univ, true_and] at h
    exact h
  ext p
  rcases p with ⟨x, ξ⟩
  constructor
  · intro hp
    rw [mem_epigraph_iff] at hp
    have hpx : (⨅ i, f i x) ≤ (ξ : EReal) := by
      simpa using hp
    rw [← Finset.inf_univ_eq_iInf (fun i : I ↦ f i x), hinf] at hpx
    rcases hpx with ⟨i, hi⟩
    exact Set.mem_iUnion.2 ⟨i, by simpa [mem_epigraph_iff] using hi⟩
  · intro hp
    rcases Set.mem_iUnion.1 hp with ⟨i, hi⟩
    rw [mem_epigraph_iff] at hi
    rw [mem_epigraph_iff]
    have hpx : (⨅ i, f i x) ≤ (ξ : EReal) := by
      rw [← Finset.inf_univ_eq_iInf (fun i : I ↦ f i x), hinf]
      exact ⟨i, hi⟩
    simpa using hpx

end ERealFunction
