module

public import stacks_project.Chap05.Definition_5_9_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Topology

namespace TopologicalSpace

section

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [LocallyNoetherianSpace X]

/-
Domain-style sampling for Lemma 5.12.14:
- primary domain: Noetherianity of quasi-compact locally Noetherian spaces
- sampled owner declarations:
  `TopologicalSpace.LocallyNoetherianSpace.exists_open`,
  `TopologicalSpace.NoetherianSpace.iUnion`,
  `TopologicalSpace.NoetherianSpace.compactSpace`,
  `AlgebraicGeometry.IsNoetherian.noetherianSpace`
- best owner abstraction: the ambient owners are the typeclasses
  `TopologicalSpace.LocallyNoetherianSpace` and `TopologicalSpace.NoetherianSpace`
- primitive data: an open Noetherian neighborhood around each point, supplied by
  `LocallyNoetherianSpace.exists_open`
- derived API: the finite-subcover step `CompactSpace.elim_nhds_subcover` and the finite-union
  theorem `NoetherianSpace.iUnion`

Layer triage:
- `source-facing`: Lemma 5.12.14, asserting that a quasi-compact locally Noetherian space is
  Noetherian
- `core/canonical`: `TopologicalSpace.NoetherianSpace`
- `bridge/view`: the finite-cover argument upgrading local Noetherian neighborhoods to a global
  `NoetherianSpace` instance

There is no upstream theorem in the chapter or in mathlib with this exact
`CompactSpace X` + `LocallyNoetherianSpace X` interface, so this file keeps the source-facing
bridge theorem and rewrites it to the canonical owner API instead of introducing a parallel local
wrapper.
-/

-- Proof sketch: use local Noetherianity to cover `X` by Noetherian neighbourhoods, extract a
-- finite subcover from quasi-compactness, and then apply the canonical finite-union theorem
-- `TopologicalSpace.NoetherianSpace.iUnion`.
/-- Lemma 5.12.14: a quasi-compact locally Noetherian topological space is Noetherian. -/
theorem LocallyNoetherianSpace.noetherianSpace :
    NoetherianSpace X := by
  classical
  -- Choose a Noetherian neighbourhood around each point from local Noetherianity.
  choose U hU_nhds hU_noeth using fun x : X ↦ LocallyNoetherianSpace.exists_mem_nhds x
  -- Quasi-compactness turns the neighbourhood cover into a finite subcover.
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover U hU_nhds
  -- Rewrite the subcover statement into an equality with `univ`.
  have hcover : (⋃ x : t, (U x : Set X)) = Set.univ := by
    simpa [Set.iUnion_subtype] using ht
  -- Reduce global Noetherianity to the finite union of the chosen Noetherian pieces.
  rw [← noetherian_univ_iff, ← hcover]
  letI : ∀ x : t, NoetherianSpace (U x) := fun x ↦ hU_noeth x
  exact NoetherianSpace.iUnion fun x : t ↦ U x

attribute [instance 100] LocallyNoetherianSpace.noetherianSpace

end

end TopologicalSpace
