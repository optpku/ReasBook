module

import Mathlib.Tactic.Recall
public import Mathlib.Topology.Bases

@[expose] public section

open FiniteInter

namespace TopologicalSpace

universe u

variable {X : Type u}

/- Domain-style sampling for subbases:
- owner abstraction: `TopologicalSpace.generateFrom`
- same-domain declarations inspected:
  `TopologicalSpace.isTopologicalBasis_of_subbasis`,
  `TopologicalSpace.isTopologicalBasis_of_subbasis_of_finiteInter`,
  `TopologicalSpace.IsTopologicalBasis.eq_generateFrom`,
  `FiniteInter.finiteInterClosure_finiteInter`

Layer triage:
- `source-facing`: a collection of subsets is a subbasis for the topology exactly when the
  topology is `generateFrom` that collection
- `core/canonical`: `TopologicalSpace.generateFrom`
- `bridge/view`: `eq_generateFrom_iff_isTopologicalBasis_finiteInterClosure`

Primitive data is only the family `B : Set (Set X)` and the generated topology `generateFrom B`.
The finite-intersection basis is derived API coming from `finiteInterClosure B`, so this file
should recall `generateFrom` as the main declaration and keep the basis criterion as a companion
bridge theorem rather than introducing a parallel wrapper notion.
-/

/- Definition 5.5.4: a collection of subsets of `X` is a subbasis for the topology on `X`
exactly when the topology is `generateFrom` that collection. -/
recall generateFrom

private theorem generateFrom_finiteInterClosure (B : Set (Set X)) :
    generateFrom (finiteInterClosure B) = generateFrom B := by
  refine le_antisymm (generateFrom_anti ?_) (le_generateFrom ?_)
  · intro U hU
    exact finiteInterClosure.basic hU
  · letI : TopologicalSpace X := generateFrom B
    intro U hU
    induction hU with
    | basic hU => exact GenerateOpen.basic _ hU
    | univ => simp
    | inter _ _ hU hV => exact hU.inter hV

section

variable [t : TopologicalSpace X]

/-- A collection generates the topology exactly when the finite intersections of its members form
a topological basis. -/
theorem eq_generateFrom_iff_isTopologicalBasis_finiteInterClosure {B : Set (Set X)} :
    t = generateFrom B ↔ IsTopologicalBasis (finiteInterClosure B) := by
  constructor
  · intro hB
    have hfinite : t = generateFrom (finiteInterClosure B) := by
      simpa [generateFrom_finiteInterClosure B] using hB
    exact isTopologicalBasis_of_subbasis_of_finiteInter hfinite
      (finiteInterClosure_finiteInter B)
  · intro hB
    simpa [generateFrom_finiteInterClosure B] using hB.eq_generateFrom

end

end TopologicalSpace
