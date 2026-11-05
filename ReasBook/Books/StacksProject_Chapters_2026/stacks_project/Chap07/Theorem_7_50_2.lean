module

public import Mathlib.CategoryTheory.Sites.Closed
public import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Tactic.Recall

@[expose] public section

open CategoryTheory

/- Domain-style sampling for Theorem 7.50.2:
- primary domain: Grothendieck topologies and their set-valued sheaf categories;
- sampled owner API:
  `topology_eq_iff_same_sheaves`,
  `Presheaf.IsSheaf`,
  `isSheaf_iff_isSheaf_of_type`;
- source/core/bridge triage:
  `source-facing`: the textbook formulation using set-valued sheaves;
  `core/canonical`: `topology_eq_iff_same_sheaves`;
  `bridge/view`: `isSheaf_iff_isSheaf_of_type`.

Primitive data are only the two Grothendieck topologies. Equality of topologies is governed by the
canonical owner theorem `topology_eq_iff_same_sheaves`, while the passage from the
presieve-valued sheaf predicate to the chapter's set-valued `Presheaf.IsSheaf` language is derived
API via `isSheaf_iff_isSheaf_of_type`. The previous local theorem was only a shell around these
two canonical declarations, so this file should recall them directly instead of
keeping a parallel wrapper.
-/

/- Theorem 7.50.2, core/canonical recall: two Grothendieck topologies are equal exactly when they
define the same sheaf predicate on set-valued presheaves, expressed canonically via the
presieve-valued owner theorem. -/
recall topology_eq_iff_same_sheaves

/- Bridge recall: for set-valued presheaves, the chapter's `Presheaf.IsSheaf` predicate is
canonically equivalent to the owner predicate `Presieve.IsSheaf`. -/
recall isSheaf_iff_isSheaf_of_type
