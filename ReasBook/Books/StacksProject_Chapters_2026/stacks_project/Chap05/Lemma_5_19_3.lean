module

public import Mathlib.Topology.Sets.Closeds
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for specialization-stable subsets:
- owner declaration: `stableUnderSpecialization_iff_exists_sUnion_eq`
- same-domain declarations inspected:
  `StableUnderSpecialization`,
  `IsClosed.stableUnderSpecialization`,
  `stableUnderSpecialization_sUnion`,
  `TopologicalSpace.Closeds`
- target layers here:
  - `core/canonical`: `stableUnderSpecialization_iff_exists_sUnion_eq`
  - `bridge/view`: the directed bundled-closed strengthening below

Primitive data is only the subset `T` together with the owner predicate
`StableUnderSpecialization T`. The closed family witnessing the union is derived API, and mathlib
already packages closed subsets canonically as `Closeds X`. A plain rebundling of the owner
theorem into `Set (Closeds X)` would add no new mathematics, so this file keeps the owner theorem
as a direct `recall` and exposes only the genuinely new directed strengthening. That
strengthening uses the canonical directed family of all bundled closed subsets contained in `T`,
rather than an arbitrary chosen family repaired by finite unions.
-/

/- Lemma 5.19.3: the canonical owner theorem is
`stableUnderSpecialization_iff_exists_sUnion_eq`, which expresses specialization-stable subsets as
unions of closed subsets. -/
recall stableUnderSpecialization_iff_exists_sUnion_eq

/-- Lemma 5.19.3, parenthetical strengthening: the family of bundled closed subsets can be chosen
directed under inclusion. -/
theorem stableUnderSpecialization_iff_exists_directed_closeds_sUnion_eq {T : Set X} :
    StableUnderSpecialization T ↔
      ∃ S : Set (Closeds X), DirectedOn (· ≤ ·) S ∧ ⋃₀ ((↑) '' S) = T := by
  constructor
  · intro hT
    refine ⟨{Z : Closeds X | (Z : Set X) ⊆ T}, ?_, ?_⟩
    · intro A hA B hB
      refine ⟨A ⊔ B, ?_, le_sup_left, le_sup_right⟩
      simpa using union_subset hA hB
    · ext x
      constructor
      · intro hx
        rcases mem_sUnion.mp hx with ⟨U, hU, hxU⟩
        rcases hU with ⟨Z, hZ, rfl⟩
        exact hZ hxU
      · intro hx
        refine mem_sUnion.mpr ⟨closure ({x} : Set X), ?_, subset_closure (by simp)⟩
        refine ⟨Closeds.closure {x}, ?_, rfl⟩
        intro y hy
        exact hT (specializes_iff_mem_closure.mpr hy) hx
  · rintro ⟨S, _, hT⟩
    rw [← hT]
    refine stableUnderSpecialization_sUnion _ ?_
    rintro U ⟨Z, hZ, rfl⟩
    exact Z.isClosed.stableUnderSpecialization
