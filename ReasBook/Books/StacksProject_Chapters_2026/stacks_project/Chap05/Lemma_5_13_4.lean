module

public import Mathlib.Topology.Sets.OpenCover
public import Mathlib.Topology.Separation.Regular
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.ShrinkingLemma

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open Set TopologicalSpace

universe u v

section

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [NormalSpace X]

/- Domain-style sampling for shrinking open covers in compact normal spaces:
- source-facing owner for the primitive open-cover data: `TopologicalSpace.IsOpenCover`
- core shrinking owner: `exists_iUnion_eq_closure_subset`
- compactness reduction API: `IsCompact.elim_finite_subcover`
- same-domain declarations inspected:
  `TopologicalSpace.IsOpenCover.of_sets`,
  `TopologicalSpace.IsOpenCover.iSup_set_eq_univ`,
  `exists_iUnion_eq_closure_subset`,
  `IsCompact.elim_finite_subcover`

Layer triage:
- `source-facing`: the same-index open-cover shrinking statement from Stacks
- `core/canonical`: the `TopologicalSpace.IsOpenCover` owner together with mathlib's shrinking
  lemma for point-finite open covers in normal spaces
- `bridge/view`: replace the original cover by a finite-support cover indexed by the same type,
  then apply the owner theorem

Primitive data are only the indexed open family `U : ι → Opens X` and its `IsOpenCover`
structure. The point-finiteness needed by the owner theorem is derived from compactness after
passing to a finite subcover, so it should remain internal rather than becoming part of the public
statement. The owner theorem itself only needs `NormalSpace`, so `T2Space` is not primitive data
for this file.

Since the source statement is exactly an open-cover theorem, the main declaration should live on
the owner `TopologicalSpace.IsOpenCover` rather than as a parallel global wrapper.
-/

variable {ι : Type v}

namespace TopologicalSpace.IsOpenCover

-- Proof sketch: extract a finite subcover from the given open cover, replace the unused indices by
-- `⊥`, and apply the point-finite shrinking lemma to this finite-support cover. The resulting
-- shrinking is still indexed by the original type, and outside the finite subcover the shrunken
-- members are empty.
/-- Lemma 5.13.4: a compact normal space admits a shrinking of any open cover, indexed by the same
family, such that the closure of each shrunken open set is contained in the corresponding original
open set. This is the source compact-Hausdorff shrinking statement, formalized over the weaker
canonical normality hypothesis used by the owner theorem. -/
theorem exists_shrinking {U : ι → Opens X} (hU : IsOpenCover U) :
    ∃ V : ι → Opens X, IsOpenCover V ∧ ∀ i, closure (V i : Set X) ⊆ U i := by
  obtain ⟨t, ht⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set X)).elim_finite_subcover
      (fun i ↦ (U i : Set X)) (fun i ↦ (U i).isOpen) hU.iSup_set_eq_univ.ge
  classical
  let U' : ι → Opens X := fun i ↦ if i ∈ t then U i else ⊥
  have hU'_finite : ∀ x, { i | x ∈ U' i }.Finite := by
    intro x
    refine (t.finite_toSet).subset ?_
    intro i hi
    by_cases hit : i ∈ t
    · exact hit
    · exact (hit <| by simpa [U', hit] using hi).elim
  have hU'_cover_set : (⋃ i, (U' i : Set X)) = (Set.univ : Set X) := by
    refine subset_antisymm (subset_univ _) ?_
    intro x hx
    rcases mem_iUnion₂.1 (ht hx) with ⟨i, hi, hxi⟩
    exact mem_iUnion.2 ⟨i, by simpa [U', hi] using hxi⟩
  have hU'_cover : IsOpenCover U' := by
    simpa using (of_sets (fun i ↦ (U' i).isOpen) hU'_cover_set)
  obtain ⟨V, hV_cover, hV_open, hV_closure⟩ :=
    exists_iUnion_eq_closure_subset (fun i ↦ (U' i).isOpen) hU'_finite hU'_cover.iSup_set_eq_univ
  let V' : ι → Opens X := fun i ↦ ⟨V i, hV_open i⟩
  refine ⟨V', ?_, fun i ↦ ?_⟩
  · simpa [V'] using of_sets hV_open hV_cover
  · exact (hV_closure i).trans <| by
      by_cases hi : i ∈ t <;> simp [U', hi]

end TopologicalSpace.IsOpenCover

end
