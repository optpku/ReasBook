module

public import stacks_project.Chap05.Definition_5_28_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Set TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

/-
Domain-style sampling for indexed stratifications:
- primary domain: indexed partitions of a topological space with locally closed pieces and a
  closure-order condition
- inspected canonical declarations:
  `IndexedPartition`,
  `IndexedPartition.disjoint`,
  `IndexedPartition.iUnion`,
  `LocallyClosedPartition`,
  `Set.PairwiseDisjoint.isPartition_of_exists_of_ne_empty`
- best owner abstraction for the partition datum: `IndexedPartition strata`

Layer triage:
- `source-facing`: `IsStratification`
- `core/canonical`: the indexed partition owner `IndexedPartition strata`
- `bridge/view`: `toLocallyClosedPartition`

Primitive data are the source-facing nonempty pairwise disjoint cover by locally closed subsets
together with the closure-order condition. The canonical `IndexedPartition strata` owner is then
derived from that primitive data, rather than stored as auxiliary chosen public data.
-/

/-- Definition 5.28.3: an indexed stratification of a topological space is a nonempty pairwise
disjoint cover `X = ⨿ i, strata i` by locally closed subsets such that the closure of each stratum
is contained in the union of the strata indexed by smaller elements. The subsets `strata i` are
the strata. -/
class IsStratification {I : Type v} [PartialOrder I] (strata : I → Set X) : Prop where
  /-- Distinct strata are disjoint. -/
  disjoint : Pairwise fun i j ↦ Disjoint (strata i) (strata j)
  /-- Each stratum is nonempty. -/
  nonempty : ∀ i, (strata i).Nonempty
  /-- The strata cover the ambient space. -/
  cover : (⋃ i, strata i) = univ
  /-- Each stratum is locally closed. -/
  locallyClosed : ∀ i, IsLocallyClosed (strata i)
  /-- The closure of a stratum is contained in the union of the lower strata. -/
  closure_subset : ∀ j, closure (strata j) ⊆ ⋃ i ∈ Set.Iic j, strata i

namespace IsStratification

variable {I : Type v} [PartialOrder I] {strata : I → Set X}

/-- The canonical indexed-partition owner attached to an indexed stratification. -/
noncomputable def toIndexedPartition (h : IsStratification strata) : IndexedPartition strata :=
  IndexedPartition.mk' strata h.disjoint h.nonempty fun x ↦ by
    have hx : x ∈ ⋃ i, strata i := by
      simp [h.cover]
    simpa [Set.mem_iUnion] using hx

/-- If one stratum meets the closure of another, then its index is smaller. -/
theorem le_of_inter_closure_nonempty (h : IsStratification strata) {i j : I}
    (hij : ((strata i) ∩ closure (strata j)).Nonempty) : i ≤ j := by
  rcases hij with ⟨x, hxi, hxj⟩
  rcases Set.mem_iUnion.1 (h.closure_subset j hxj) with ⟨k, hxk⟩
  rcases Set.mem_iUnion.1 hxk with ⟨hkj, hxk⟩
  simpa [h.toIndexedPartition.eq_of_mem hxi hxk] using hkj

-- Proof sketch: coverage gives existence of a stratum containing any point, pairwise disjointness
-- gives uniqueness of that stratum, and nonemptiness rules out the empty set from the range.
/-- The set of strata of an indexed stratification is a partition of the ambient space. -/
def toLocallyClosedPartition (h : IsStratification strata) : LocallyClosedPartition X where
  toPartitions := ⟨Set.range strata, by
    refine Set.PairwiseDisjoint.isPartition_of_exists_of_ne_empty ?_ ?_ ?_
    · rintro s ⟨i, rfl⟩ t ⟨j, rfl⟩ hst
      exact h.toIndexedPartition.disjoint fun hij ↦ hst (congrArg strata hij)
    · intro x
      rcases h.toIndexedPartition.exists_mem x with ⟨i, hxi⟩
      exact ⟨strata i, ⟨i, rfl⟩, hxi⟩
    · intro hEmpty
      rcases hEmpty with ⟨i, hi⟩
      exact (h.nonempty i).ne_empty hi⟩
  locallyClosed := by
    rintro ⟨_, ⟨i, rfl⟩⟩
    exact h.locallyClosed i

end IsStratification

/-- The one-stratum decomposition of a nonempty topological space is a stratification. -/
instance oneStratum_isStratification [Nonempty X] :
    IsStratification (fun _ : Fin 1 ↦ (univ : Set X)) where
  disjoint := by
    intro s t hst
    exact (hst <| Subsingleton.elim _ _).elim
  nonempty _ := Set.univ_nonempty
  cover := by
    ext x
    constructor
    · intro _
      trivial
    · intro _
      exact Set.mem_iUnion.2 ⟨0, mem_univ x⟩
  locallyClosed _ := isOpen_univ.isLocallyClosed
  closure_subset _ := by
    intro x _
    refine Set.mem_iUnion.2 ⟨0, ?_⟩
    refine Set.mem_iUnion.2 ⟨by simp, mem_univ x⟩
