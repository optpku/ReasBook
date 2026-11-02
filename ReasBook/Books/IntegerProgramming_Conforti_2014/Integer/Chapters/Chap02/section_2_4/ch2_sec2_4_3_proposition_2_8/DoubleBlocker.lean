module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_3_definition_2_16.Blocker
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Order.Preorder.Finite

public section

namespace Clutter

universe u

variable {α : Type u} [DecidableEq α]

/-- Every member of a clutter is a transversal of its blocker. -/
lemma isTransversal_blocker_of_mem
    (E : Finset α) (S : Set (Finset α)) (hS : IsClutterOn E S)
    {s : Finset α} (hs : s ∈ S) :
    IsTransversal E (blocker E S) s := by
  refine IsTransversal.ofSubsetGroundAndHits (hS.subset_ground s hs) ?_
  intro t ht
  simpa [Finset.inter_comm] using (mem_blocker_iff.mp ht).prop.hits s hs

/-- Every transversal contains a blocker member. -/
lemma exists_blocker_subset_of_transversal
    (E : Finset α) (S : Set (Finset α)) {t : Finset α}
    (ht : IsTransversal E S t) :
    ∃ u : Finset α, u ∈ blocker E S ∧ u ⊆ t := by
  classical
  let candidates : Set (Finset α) := {u | u ⊆ t ∧ IsTransversal E S u}
  have ht_mem : t ∈ candidates := ⟨fun _ hx ↦ hx, ht⟩
  have hCandidatesFinite : candidates.Finite := by
    refine t.powerset.finite_toSet.subset ?_
    intro u hu
    exact Finset.mem_powerset.mpr hu.1
  obtain ⟨u, _, hu_min⟩ := hCandidatesFinite.exists_le_minimal ht_mem
  have hu_trans : IsTransversal E S u := hu_min.prop.2
  have hu_subset_t : u ⊆ t := hu_min.prop.1
  refine ⟨u, mem_blocker_iff.mpr ?_, hu_subset_t⟩
  refine ⟨hu_trans, ?_⟩
  intro v hv hvu
  exact hu_min.2 ⟨fun x hx ↦ hu_subset_t (hvu hx), hv⟩ hvu

/-- Every member of the double blocker contains a member of the original clutter. -/
lemma exists_mem_subset_of_mem_blocker_blocker
    (E : Finset α) (S : Set (Finset α)) (hS : IsClutterOn E S)
    {q : Finset α} (hq : q ∈ blocker E (blocker E S)) :
    ∃ s : Finset α, s ∈ S ∧ s ⊆ q := by
  classical
  by_contra hNo
  have hNo' : ∀ s ∈ S, ¬ s ⊆ q := by
    intro s hs hsq
    exact hNo ⟨s, hs, hsq⟩
  have hCompl : IsTransversal E S (E \ q) := by
    refine IsTransversal.ofSubsetGroundAndHits Finset.sdiff_subset ?_
    intro s hs
    obtain ⟨x, hxS, hxQ⟩ := Finset.not_subset.mp (hNo' s hs)
    have hxE : x ∈ E := hS.subset_ground s hs hxS
    exact ⟨x, by
      rw [Finset.mem_inter, Finset.mem_sdiff]
      exact ⟨hxS, hxE, hxQ⟩⟩
  obtain ⟨t, ht, ht_subset⟩ := exists_blocker_subset_of_transversal E S hCompl
  have hhit : (t ∩ q).Nonempty := (mem_blocker_iff.mp hq).prop.hits t ht
  obtain ⟨x, hx⟩ := hhit
  have hxT : x ∈ t := Finset.mem_of_mem_inter_left hx
  have hxQ : x ∈ q := Finset.mem_of_mem_inter_right hx
  have hxNotQ : x ∉ q := (Finset.mem_sdiff.mp (ht_subset hxT)).2
  exact hxNotQ hxQ

/-- Proposition 2.8: the blocker of the blocker of a clutter is the original clutter. -/
theorem blocker_blocker_eq
    (E : Finset α) (S : Set (Finset α)) (hS : IsClutterOn E S) :
    blocker E (blocker E S) = S := by
  have hDoubleSubset : blocker E (blocker E S) ⊆ S := by
    intro q hq
    obtain ⟨s, hs, hsq⟩ := exists_mem_subset_of_mem_blocker_blocker E S hS hq
    have hs_eq_q :
        s = q :=
      Minimal.eq_of_le
        (mem_blocker_iff.mp hq)
        (isTransversal_blocker_of_mem E S hS hs)
        hsq
    simpa [hs_eq_q] using hs
  have hSubsetDouble : S ⊆ blocker E (blocker E S) := by
    intro s hs
    obtain ⟨q, hq, hqs⟩ :=
      exists_blocker_subset_of_transversal E (blocker E S)
        (isTransversal_blocker_of_mem E S hS hs)
    have hqS : q ∈ S := hDoubleSubset hq
    by_cases hEq : q = s
    · simpa [hEq] using hq
    exfalso
    exact hS.antichain hqS hs hEq hqs
  ext q
  constructor
  · intro hq
    exact hDoubleSubset hq
  · intro hq
    exact hSubsetDouble hq

end Clutter
