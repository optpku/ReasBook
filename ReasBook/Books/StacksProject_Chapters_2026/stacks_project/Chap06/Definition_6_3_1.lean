module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory

namespace TopCat

scoped notation "PSh(" X ")" => TopCat.Presheaf (Type _) X

end TopCat

open scoped TopCat

variable (X : TopCat.{u})

/- Domain-style sampling for Definition 6.3.1:
- primary domain: set-valued presheaves on a topological space;
- sampled owner API:
  `TopCat.Presheaf`,
  `TopCat.Presheaf.IsSheaf`,
  `TopCat.Presheaf.sheafify`,
  `TopCat.Sheaf.forget`;
- best owner abstraction: the canonical presheaf owner `X.Presheaf (Type v)`, with source-facing
  Stacks notation `PSh(X)`;
- primitive data: only the functor `(TopologicalSpace.Opens X)ᵒᵖ ⥤ Type v`;
- derived API: morphisms as natural transformations, hence compatibility with restriction maps by
  naturality.

Source/core/bridge triage:
- `source-facing`: the Stacks category `PSh(X)` of set-valued presheaves on `X`;
- `core/canonical`: `TopCat.Presheaf`;
- `bridge/view`: the naturality identities for morphisms of presheaves.

This item adds no extra source-facing mathematics beyond the canonical owner, so the main entry
should be a direct recall of `TopCat.Presheaf` together with the chapter notation `PSh(X)`,
rather than a duplicate local wrapper. -/

/- Definition 6.3.1 (1) and (3): the category of presheaves of sets on a topological space `X`,
denoted `PSh(X)` in the Stacks Project, is the canonical owner `X.Presheaf (Type v)`. -/
recall TopCat.Presheaf
#check (PSh(X))
#check (X.Presheaf (Type v))

section

variable {X}
variable {F G : PSh(X)} (φ : F ⟶ G)

/- Morphisms of presheaves are natural transformations, so compatibility with restriction maps is
the canonical naturality identity `φ.naturality`. -/
#check φ.naturality

end
