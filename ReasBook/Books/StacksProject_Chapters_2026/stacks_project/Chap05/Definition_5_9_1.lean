module

public import Mathlib.Topology.NoetherianSpace
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/-
Domain-style sampling for locally Noetherian spaces:
- primary domain: topological Noetherianity and its local open-subspace form
- same-domain declarations inspected:
  `TopologicalSpace.NoetherianSpace`,
  `TopologicalSpace.NoetherianSpace.set`,
  `TopologicalSpace.noetherianSpace_set_iff`,
  `WeaklyLocallyCompactSpace.exists_compact_mem_nhds`

Owner-abstraction choice:
- `source-facing`: `TopologicalSpace.LocallyNoetherianSpace`
- `core/canonical`: `TopologicalSpace.NoetherianSpace` for each open subspace
- `bridge/view`: the derived neighborhood-filter reformulation of the owner field

Primitive data versus derived API:
- primitive data: for each `x : X`, an open neighborhood whose induced topology is Noetherian
- derived API: the neighborhood-filter restatement used by later files
-/

variable {X : Type u} [TopologicalSpace X]

open Topology

namespace TopologicalSpace

/- Companion recall: the textbook notion that a topological space is Noetherian is the canonical
mathlib predicate `TopologicalSpace.NoetherianSpace`, and the descending chain condition on closed
subsets is one of its equivalent formulations via `TopologicalSpace.noetherianSpace_TFAE`. -/
recall TopologicalSpace.NoetherianSpace

/-- Definition 5.9.1: a topological space is locally Noetherian if every point has an open
neighbourhood whose induced topology is Noetherian. The owner field stores this source-facing open
formulation directly, while the neighborhood-filter formulation is derived API built from the
canonical predicate `TopologicalSpace.NoetherianSpace`. -/
class LocallyNoetherianSpace (X : Type u) [TopologicalSpace X] : Prop where
  exists_open (x : X) : ∃ U : Opens X, x ∈ U ∧ NoetherianSpace U

private theorem noetherianSpace_inter_opens (U : Opens X) [NoetherianSpace U] (s : Set X) :
    NoetherianSpace (((U : Set X) ∩ s : Set X)) := by
  let hU : NoetherianSpace (U : Set X) := inferInstance
  exact
    (noetherianSpace_set_iff ((U : Set X) ∩ s)).2 fun t ht ↦
      (noetherianSpace_set_iff (U : Set X)).1 hU t <|
        Set.Subset.trans ht Set.inter_subset_left

/-- Derived neighborhood-filter bridge: every neighborhood contains a Noetherian neighborhood. -/
theorem LocallyNoetherianSpace.exists_mem_nhds_subset [LocallyNoetherianSpace X] (x : X)
    {s : Set X} (hs : s ∈ 𝓝 x) :
    ∃ t : Set X, t ∈ 𝓝 x ∧ t ⊆ s ∧ NoetherianSpace t := by
  rcases LocallyNoetherianSpace.exists_open x with ⟨U, hxU, hU⟩
  refine ⟨((U : Set X) ∩ s : Set X), Filter.inter_mem (U.2.mem_nhds hxU) hs,
    Set.inter_subset_right, ?_⟩
  letI : NoetherianSpace U := hU
  simpa using noetherianSpace_inter_opens U s

/-- Derived neighborhood-filter bridge: a point admits a Noetherian neighborhood in its
neighborhood filter. -/
theorem LocallyNoetherianSpace.exists_mem_nhds [LocallyNoetherianSpace X] (x : X) :
    ∃ s : Set X, s ∈ 𝓝 x ∧ NoetherianSpace s := by
  have h_univ : (Set.univ : Set X) ∈ 𝓝 x := Filter.univ_mem
  rcases LocallyNoetherianSpace.exists_mem_nhds_subset x h_univ with
    ⟨s, hs_nhds, _, hs_noeth⟩
  exact ⟨s, hs_nhds, hs_noeth⟩

/-- Every Noetherian topological space is locally Noetherian. -/
instance [NoetherianSpace X] : LocallyNoetherianSpace X where
  exists_open _ := ⟨⊤, by simp, noetherian_univ_iff.2 inferInstance⟩

end TopologicalSpace
