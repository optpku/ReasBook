module

public import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Baire.LocallyCompactRegular

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology

universe u v

/- Domain-style sampling for the Baire category theorem:
- primary domain: Baire spaces and countable intersections of dense open subsets
- owner declarations inspected: `BaireSpace`, `dense_iInter_of_isOpen`,
  `BaireSpace.of_t2Space_locallyCompactSpace`, `dense_biInter_of_isOpen`
- best owner abstraction: `BaireSpace`

Layer triage:
- `source-facing`: the locally quasi-compact Hausdorff specialization in the Stacks statement
- `core/canonical`: `BaireSpace` together with `dense_iInter_of_isOpen`
- `bridge/view`: the instance `BaireSpace.of_t2Space_locallyCompactSpace` turning the source
  hypotheses into the owner abstraction

Primitive data is the family `U : ι → Set X` together with the proofs that each `U i` is open and
dense. The Baire-space structure and the dense-intersection theorem are derived API from the owner
abstraction, so this file should keep only the source-facing specialization and reuse the canonical
mathlib declarations directly. -/

variable {X : Type u} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
variable {ι : Sort v} [Countable ι] {U : ι → Set X}

/-- Lemma 5.13.3 (Baire category theorem): in a locally quasi-compact Hausdorff space, a
countable intersection of dense open subsets is dense. -/
-- Proof sketch: the source assumptions give the canonical `BaireSpace X` instance, so the result
-- is the owner theorem `dense_iInter_of_isOpen` specialized to `U`.
theorem dense_iInter_dense_open_of_locallyCompact_t2
    (hU_open : ∀ i, IsOpen (U i)) (hU_dense : ∀ i, Dense (U i)) : Dense (⋂ i, U i) := by
  simpa using dense_iInter_of_isOpen hU_open hU_dense
