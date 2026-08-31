module

import Mathlib.Topology.Category.TopCommRingCat
import Mathlib.Tactic.Recall
public import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Quiver.Basic

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Domain-style sampling for topological rings:
- primary domain: topological algebra of rings and the bundled category of topological
  commutative rings
- sampled mathlib owner declarations:
  `IsTopologicalRing`,
  `ContinuousAdd`,
  `ContinuousMul`,
  `TopCommRingCat.of`
- sampled neighboring project declarations:
  `Lemma_5_30_8.topologicalRingCat_hasLimits_and_forget_preservesLimits`,
  `Definition_5_30_10`,
  `Definition_15_36_1_Topological_rings`
- best owner abstraction: `IsTopologicalRing` for the unbundled notion, with `TopCommRingCat` as
  the bundled owner for morphisms

Layer triage:
- `source-facing`: the Stacks restatement that, for commutative rings, the topological-ring
  condition is
  equivalent to continuity of addition and multiplication
- `core/canonical`: `IsTopologicalRing` and `TopCommRingCat`
- `bridge/view`: the iff theorem below, which explicitly unfolds the primitive continuity data of
  the canonical owner without introducing any parallel wrapper

Primitive data for the owner `IsTopologicalRing` is exactly `ContinuousAdd` and `ContinuousMul`,
while continuity of negation is derived in the ring setting. The hom type in part (2) is derived
categorical API from the bundled owner `TopCommRingCat`.
-/

/-
Clause (1): in the Stacks convention, rings are commutative with `1`, and the canonical
mathlib notion of a topological ring is the typeclass `IsTopologicalRing`. For commutative
rings, this is the same as requiring addition and multiplication to be continuous, since
continuity of negation follows automatically. -/
recall IsTopologicalRing

/- Primitive data for the canonical owner `IsTopologicalRing`: continuity of addition. -/
recall ContinuousAdd

/- Primitive data for the canonical owner `IsTopologicalRing`: continuity of multiplication. -/
recall ContinuousMul

/- Companion recall: topological commutative rings form the canonical bundled category
`TopCommRingCat`. -/
recall TopCommRingCat

/- The canonical constructor for bundling an unbundled topological commutative ring is
`TopCommRingCat.of`. -/
recall TopCommRingCat.of

section

variable {R : Type u} [CommRing R] [TopologicalSpace R]

/-- Definition 5.30.7 (1): a topological ring is exactly a ring with a topology for which
addition and multiplication are continuous. -/
theorem isTopologicalRing_iff_continuousAdd_continuousMul :
    IsTopologicalRing R ↔ ContinuousAdd R ∧ ContinuousMul R := by
  constructor
  · intro _
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hAdd, hMul⟩
    let _ : IsTopologicalSemiring R := { toContinuousAdd := hAdd, toContinuousMul := hMul }
    exact IsTopologicalSemiring.toIsTopologicalRing inferInstance

end

section

variable {R S : Type u} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
variable [IsTopologicalRing R] [IsTopologicalRing S]

/- Definition 5.30.7 (2): a homomorphism of topological rings from `R` to `S` is a morphism in
the canonical category `TopCommRingCat`, whose hom type is realized in mathlib by continuous ring
homomorphisms. -/
#check (TopCommRingCat.of R ⟶ TopCommRingCat.of S)

end
