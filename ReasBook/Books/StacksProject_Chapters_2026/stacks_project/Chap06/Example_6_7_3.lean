module

public import Mathlib.Topology.Sheaves.LocalPredicate
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open TopCat

universe u

section

variable (X Y : TopCat.{u})

/- Domain-style sampling for Example 6.7.3:
- primary domain: set-valued sheaves on a topological space, specifically the sheaf of continuous
  maps into a fixed target space;
- sampled owner declarations:
  `presheafToTop`,
  `presheafToTop_obj`,
  `sheafToTop`,
  `TopCat.Presheaf.IsSheaf`;
- best owner abstraction: the bundled sheaf owner `sheafToTop Y`, whose underlying presheaf is the
  canonical `presheafToTop X Y`;
- primitive data: only the target space `Y` together with the canonical presheaf of continuous
  maps, already supplied upstream by `presheafToTop`;
- derived API: the sheaf condition on that presheaf, carried by `(sheafToTop Y).property`.

Source/core/bridge triage:
- `source-facing`: the presheaf on `X` sending `U` to the continuous maps `U ⟶ Y`;
- `core/canonical`: the bundled owner `sheafToTop Y`;
- `bridge/view`: the unbundled predicate `(presheafToTop X Y).IsSheaf`.

Since this example only recalls that the canonical presheaf of continuous maps is a sheaf, the file
should stay in direct recall/check form rather than introduce any local wrapper around either
`presheafToTop` or `sheafToTop`.
-/

/- Canonical recall: the sheaf of continuous maps from opens of `X` into `Y` is
`sheafToTop Y`. -/
recall sheafToTop

/- Companion recall: the underlying rule `U ↦ {f : U → Y | Continuous f}` with restriction by
precomposition is the canonical presheaf `presheafToTop X Y`. -/
recall presheafToTop

/- Example 6.7.3: for topological spaces `X` and `Y`, the presheaf sending an open set `U ⊆ X`
to the set of continuous maps `U → Y`, with the obvious restriction maps, satisfies the sheaf
condition. This is the `.property` field of the canonical owner `sheafToTop Y`. -/
#check (show (presheafToTop X Y).IsSheaf from (sheafToTop Y).property)

end
