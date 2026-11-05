module

public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for local quasi-compactness around Lemma 5.13.2:
- owner abstractions: `LocallyCompactSpace`, `WeaklyLocallyCompactSpace`
- same-domain declarations inspected:
  `compact_basis_nhds`,
  `LocallyCompactSpace.of_hasBasis`,
  `T2Space.r1Space`,
  `(priority := 100) [LocallyCompactSpace X] : WeaklyLocallyCompactSpace X`,
  `WeaklyLocallyCompactSpace.locallyCompactSpace`

Layer triage:
- `source-facing`: the equivalence between the two local quasi-compactness formulations used by
  the Stacks text in the Hausdorff case
- `core/canonical`: the owner classes `LocallyCompactSpace` and `WeaklyLocallyCompactSpace`
- `bridge/view`: the `T2Space.r1Space` and `WeaklyLocallyCompactSpace.locallyCompactSpace`
  instance bridges

Primitive data already lives in the owner classes. The chapter has already chosen
`LocallyCompactSpace` as the canonical source-facing owner in `Definition_5_13_1`, and the
Hausdorff specialization factors canonically through `T2Space.r1Space`, while the stronger `R₁`
converse is the canonical mathlib instance
`WeaklyLocallyCompactSpace.locallyCompactSpace`. This file should therefore remain a thin bridge
rather than introducing any parallel wrapper API. The numbered Stacks lemma stays Hausdorff-facing;
the more general `R₁` equivalence belongs only as a companion bridge.
-/

/-- The `R₁`-space version of the local compactness equivalence uses the canonical bridge between
`WeaklyLocallyCompactSpace` and `LocallyCompactSpace`. -/
-- Proof sketch: one direction is the canonical instance
-- `[LocallyCompactSpace X] → [WeaklyLocallyCompactSpace X]`, and the other is the canonical
-- instance `[WeaklyLocallyCompactSpace X] [R1Space X] → [LocallyCompactSpace X]`.
theorem locallyCompactSpace_iff_weaklyLocallyCompactSpace_of_r1 [R1Space X] :
    LocallyCompactSpace X ↔ WeaklyLocallyCompactSpace X := by
  constructor
  · intro h
    -- Promote the forward hypothesis to the canonical weak local compactness instance.
    letI := h
    infer_instance
  · intro h
    -- In an `R₁` space, weak local compactness upgrades back to local compactness.
    letI := h
    infer_instance

/- The Hausdorff-space specialization compares the canonical mathlib classes
`LocallyCompactSpace X` and `WeaklyLocallyCompactSpace X`. -/
-- Proof sketch: combine `T2Space.r1Space` with the `R₁` companion equivalence above.
/-- Lemma 5.13.2: for a Hausdorff space, local quasi-compactness is equivalent to every point
having a quasi-compact neighborhood. Mathlib expresses these two conditions by
`LocallyCompactSpace X` and `WeaklyLocallyCompactSpace X`. -/
theorem locallyCompactSpace_iff_weaklyLocallyCompactSpace [T2Space X] :
    LocallyCompactSpace X ↔ WeaklyLocallyCompactSpace X := by
  -- Specialize the `R₁` equivalence through the canonical Hausdorff-to-`R₁` instance.
  simpa using (locallyCompactSpace_iff_weaklyLocallyCompactSpace_of_r1 (X := X))

end
