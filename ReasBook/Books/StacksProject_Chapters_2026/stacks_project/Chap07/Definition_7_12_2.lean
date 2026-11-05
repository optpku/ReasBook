module

public import Mathlib.CategoryTheory.Sites.Canonical
import Mathlib.Tactic.Recall
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory.GrothendieckTopology

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Definition 7.12.2:
- primary domain: subcanonical Grothendieck topologies and representable sheaves;
- sampled owner API:
  `GrothendieckTopology.Subcanonical`,
  `GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj`,
  `GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable`,
  `GrothendieckTopology.le_canonical`;
- source/core/bridge triage:
  `source-facing`: the Stacks criterion that a topology is subcanonical exactly when every
  representable presheaf is a sheaf;
  `core/canonical`: `J.Subcanonical`;
  `bridge/view`: the two direction theorems
  `Subcanonical.of_isSheaf_yoneda_obj` and `Subcanonical.isSheaf_of_isRepresentable`, together
  with the order-theoretic consequence `le_canonical`.

Primitive data are only the Grothendieck topology `J`. The representable-sheaf criterion and the
comparison `J ≤ canonicalTopology C` are derived API from the owner class `Subcanonical`, so this
file should recall that owner directly and keep only the thin source-facing equivalence as a
companion theorem.
-/
/- Definition 7.12.2: a subcanonical topology on a site is the canonical mathlib class
`GrothendieckTopology.Subcanonical` on a Grothendieck topology. -/
recall Subcanonical

-- Proof sketch: `Subcanonical.isSheaf_of_isRepresentable` gives the forward implication, and
-- `Subcanonical.of_isSheaf_yoneda_obj` reconstructs
-- subcanonicality from the sheaf condition on every representable presheaf.
/-- Definition 7.12.2, source-facing form: a Grothendieck topology is subcanonical exactly when
every representable presheaf is a sheaf for it. -/
theorem subcanonical_iff_forall_isSheaf_yoneda_obj (J : GrothendieckTopology C) :
    J.Subcanonical ↔ ∀ X : C, Presieve.IsSheaf J (CategoryTheory.yoneda.obj X) := by
  constructor
  · intro hJ X
    letI : J.Subcanonical := hJ
    simpa using Subcanonical.isSheaf_of_isRepresentable (CategoryTheory.yoneda.obj X)
  · exact Subcanonical.of_isSheaf_yoneda_obj J

/- Companion recall: the order-theoretic formulation that a subcanonical topology is weaker than
the canonical topology is the theorem `GrothendieckTopology.le_canonical`. -/
recall le_canonical

end CategoryTheory.GrothendieckTopology
