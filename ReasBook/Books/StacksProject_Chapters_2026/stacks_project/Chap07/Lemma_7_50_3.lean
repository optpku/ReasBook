module

public import Mathlib.CategoryTheory.Sites.Closed
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap04.Definition_4_3_3
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory.GrothendieckTopology

section

variable {C : Type u} [Category.{v} C] {J J' : GrothendieckTopology C}

/- Domain-style sampling for Lemma 7.50.3:
- primary domain: comparison of Grothendieck topologies through their sheaf predicates
- sampled owner API:
  `Presheaf.IsSheaf.of_le`,
  `le_topology_of_closedSieves_isSheaf`,
  `isSheaf_iff_isSheaf_of_type`
- source/core/bridge triage:
  `source-facing`: the textbook formulation using set-valued sheaves
  `core/canonical`: topology inclusion together with
    `le_topology_of_closedSieves_isSheaf`
  `bridge/view`: `isSheaf_iff_isSheaf_of_type`

Primitive data are only the two Grothendieck topologies `J` and `J'`. The forward implication is
the canonical monotonicity of the sheaf predicate on the chapter owner `Presheaf C`, while the
converse is recovered from the closed sieve classifier, so no extra local wrapper object is
warranted here.
-/

-- Proof sketch: the forward implication is `Presheaf.IsSheaf.of_le`. For the converse, apply the
-- hypothesis to the presheaf of `J'`-closed sieves and then use
-- `le_topology_of_closedSieves_isSheaf`.
/-- Lemma 7.50.3: `J` is contained in `J'` if and only if every set-valued sheaf for the topology
`J'` is also a sheaf for the topology `J`. -/
theorem le_iff_sheaf_inclusion :
    J ≤ J' ↔
      ∀ P : Presheaf.{max u v} C, Presheaf.IsSheaf J' P → Presheaf.IsSheaf J P := by
  constructor
  · intro hJ P
    exact Presheaf.IsSheaf.of_le hJ
  · intro h
    apply le_topology_of_closedSieves_isSheaf
    rw [← isSheaf_iff_isSheaf_of_type]
    exact h _ ((isSheaf_iff_isSheaf_of_type _ _).2 (classifier_isSheaf J'))

end

end CategoryTheory.GrothendieckTopology
