module

public import Mathlib.CategoryTheory.Sites.Canonical
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

/- Domain-style sampling for Definition 7.47.12:
- primary domain: canonical and subcanonical Grothendieck topologies on a category;
- sampled owner API:
  `Sheaf.canonicalTopology`,
  `Sheaf.finestTopology`,
  `Sheaf.isSheaf_yoneda_obj`,
  `GrothendieckTopology.Subcanonical`;
- source/core/bridge triage:
  `source-facing`: the Stacks definition of the canonical topology as the finest topology for
  which every representable presheaf is a sheaf;
  `core/canonical`: `Sheaf.canonicalTopology`;
  `bridge/view`: the representable-sheaf consequence `Sheaf.isSheaf_yoneda_obj` and the
  subcanonical comparison packaged by `GrothendieckTopology.Subcanonical`.

Primitive data are only the category `C`; the "finest topology" and "representables are sheaves"
clauses are derived API from the owner `Sheaf.canonicalTopology`, via
`Sheaf.finestTopology (Set.range yoneda.obj)`. This item is therefore a direct owner recall, not a
new wrapper or bridge.
-/

/- Definition 7.47.12: the canonical topology on a category `\mathcal C` is the canonical
mathlib Grothendieck topology `Sheaf.canonicalTopology C`, i.e. the finest topology
for which every representable presheaf is a sheaf. -/
recall Sheaf.canonicalTopology
