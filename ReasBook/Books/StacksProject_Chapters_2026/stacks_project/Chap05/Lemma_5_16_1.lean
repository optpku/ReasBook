module

public import stacks_project.Chap05.FiniteUnionOfLocallyClosed
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import stacks_project.Chap05.Lemma_5_12_13
import stacks_project.Chap05.Lemma_5_15_13

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set Topology TopologicalSpace

section

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for constructible subsets in Noetherian spaces:
- primary domain: constructible, locally closed, and Noetherian topological subsets
- inspected declarations:
  `Topology.IsConstructible.isFiniteUnionOfLocallyClosed`,
  `IsLocallyClosed.isConstructible_of_isCompact_of_retrocompact_compl`,
  `Topology.IsConstructible.sUnion`,
  `TopologicalSpace.NoetherianSpace.isCompact`,
  `isRetrocompact_of_noetherianSpace`
- best owner abstraction: `Topology.IsConstructible`

Layer triage:
- `source-facing`: the equivalence between constructibility and finite unions of locally closed
  subsets in a Noetherian space
- `core/canonical`: the owner predicate `Topology.IsConstructible`
- `bridge/view`: the chapter predicate `IsFiniteUnionOfLocallyClosed`

Primitive data is only the ambient `NoetherianSpace` instance together with the locally closed
pieces in a finite union. The finite-union predicate is a bridge/view API, so the reverse
direction should unpack it and rebuild constructibility from the owner-level operations on
`IsConstructible`, reusing the earlier locally closed-to-constructible bridge rather than
reintroducing a parallel proof of the same conversion.
-/

-- Proof sketch: the forward implication is the existing owner-level bridge
-- `IsConstructible.isFiniteUnionOfLocallyClosed`. For the converse, unpack the finite union and
-- apply the earlier theorem that a locally closed compact subset with retrocompact complement is
-- constructible; in a Noetherian space those compactness and retrocompactness hypotheses are
-- automatic for every subset.
/-- Lemma 5.16.1: in a Noetherian topological space, the constructible subsets are exactly the
finite unions of locally closed subsets. -/
theorem isConstructible_iff_isFiniteUnionOfLocallyClosed_of_noetherian
    [NoetherianSpace X] {s : Set X} :
    IsConstructible s ↔ IsFiniteUnionOfLocallyClosed s := by
  constructor
  · exact IsConstructible.isFiniteUnionOfLocallyClosed
  · rintro ⟨S, hSfinite, hS, rfl⟩
    refine IsConstructible.sUnion hSfinite fun Z hZ ↦ ?_
    exact (hS Z hZ).isConstructible_of_isCompact_of_retrocompact_compl
      (NoetherianSpace.isCompact Z) (isRetrocompact_of_noetherianSpace Zᶜ)

end
