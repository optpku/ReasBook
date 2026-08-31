module

public import stacks_project.Chap05.Definition_5_9_1
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Noetherianity under continuous/open maps:
- owner abstractions: `TopologicalSpace.NoetherianSpace` and the chapter owner
  `TopologicalSpace.LocallyNoetherianSpace`
- same-domain declarations inspected:
  `TopologicalSpace.NoetherianSpace.range`,
  `TopologicalSpace.noetherianSpace_of_surjective`,
  `TopologicalSpace.LocallyNoetherianSpace.exists_open`,
  `IsOpenMap.isOpen_range`

Layer triage:
- `core/canonical`: `TopologicalSpace.NoetherianSpace.range`
- `source-facing`: local Noetherianity of the range under an open map
- `bridge/view`: the restricted map `U → Set.range f`

Primitive data for clause `(2)` is the owner class `LocallyNoetherianSpace`; the textbook bridge
`LocallyNoetherianSpace.exists_open` and the range neighborhood lemmas for open maps are
derived API. So this file should recall the canonical range theorem for clause `(1)` and keep only
the source-facing permanence theorem for clause `(2)`. -/

open Set Topology

universe u v

namespace TopologicalSpace

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

/- Companion recall for clause (1): the image of a Noetherian topological space under a continuous
map is Noetherian for the induced topology. -/
recall NoetherianSpace.range

-- Proof sketch: for a point `y` of `Set.range f`, choose a preimage `x : X`. By local
-- Noetherianity, `x` has an open Noetherian neighbourhood `U`. Restricting `f` to `U` gives an
-- open continuous map `U → Set.range f`, so its range is an open neighbourhood of `y` in
-- `Set.range f`; clause `(1)` shows that this range is Noetherian.
/-- Lemma 5.9.3: if every point of `X` has an open Noetherian neighbourhood and `f` is open, then
the image `f(X)` is locally Noetherian for the induced topology. -/
theorem LocallyNoetherianSpace.range [LocallyNoetherianSpace X]
    (hcont : Continuous f) (hopen : IsOpenMap f) :
    LocallyNoetherianSpace (Set.range f) := by
  refine ⟨fun y ↦ ?_⟩
  rcases y with ⟨_, ⟨x, rfl⟩⟩
  rcases LocallyNoetherianSpace.exists_open x with ⟨U, hUx, hU⟩
  let g : U → Set.range f := fun z ↦ ⟨f z, ⟨z, rfl⟩⟩
  let xU : U := ⟨x, hUx⟩
  have hg : Continuous g := by
    simpa [g] using (hcont.comp continuous_subtype_val).subtype_mk fun z ↦ ⟨z, rfl⟩
  have hgOpen : IsOpenMap g := by
    simpa [g] using (hopen.comp U.2.isOpenMap_subtype_val).subtype_mk fun z ↦ ⟨z, rfl⟩
  refine ⟨⟨Set.range g, hgOpen.isOpen_range⟩, mem_range_self xU, ?_⟩
  · simpa using NoetherianSpace.range g hg

end

end TopologicalSpace
