module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open TopCat

universe u

section

/- Domain-style sampling for Lemma 6.17.1:
- primary domain: sheafification of set-valued presheaves on a topological space;
- sampled owner API:
  `TopCat.Presheaf.sheafify`,
  `TopCat.Presheaf.sheafifyStalkIso`,
  `TopCat.Presheaf.IsSheaf`,
  `GrothendieckTopology.sheafify_isSheaf`;
- source/core/bridge triage:
  `source-facing`: the textbook assertion that the associated presheaf `ℱ^#` is a sheaf;
  `core/canonical`: the bundled sheafification owner `TopCat.Presheaf.sheafify`;
  `bridge/view`: the underlying-presheaf sheaf predicate `ℱ.sheafify.presheaf.IsSheaf`.

Primitive data are only the topological space `X` and the presheaf `ℱ`. The sheaf-condition proof
is not primitive data here: it is already carried by the bundled owner `ℱ.sheafify`. Therefore the
file should expose the owner directly and treat the unbundled `IsSheaf` statement as a companion
view, rather than keeping a duplicate local theorem wrapper around `.property`.
-/

recall TopCat.Presheaf.sheafify

variable {X : TopCat.{u}} (ℱ : X.Presheaf (Type u))

/- Lemma 6.17.1: for a set-valued presheaf `ℱ` on `X`, the associated presheaf `ℱ^#`,
formalized by the underlying presheaf of `ℱ.sheafify`, is a sheaf. This is the sheaf-condition
proof carried by the canonical owner `TopCat.Presheaf.sheafify`. -/
#check (ℱ.sheafify.property : ℱ.sheafify.presheaf.IsSheaf)

end
