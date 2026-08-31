module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory TopCat

namespace TopCat

scoped notation "Sh(" X ")" => TopCat.Sheaf (Type _) X

end TopCat

open scoped TopCat

variable (X : TopCat.{u})

/- Domain-style sampling for Definition 6.7.1:
- primary domain: sheaves of sets on a topological space and their morphisms as a full
  subcategory of presheaves;
- sampled owner declarations:
  `TopCat.Sheaf`,
  `TopCat.Presheaf.IsSheaf`,
  `TopCat.Sheaf.forget`,
  `CategoryTheory.Sheaf.homEquiv`;
- best owner abstraction: the canonical sheaf owner `X.Sheaf (Type v)`, with source-facing
  Stacks notation `Sh(X)`;
- primitive data: none beyond the canonical owner `X.Sheaf (Type v)` and the sheaf predicate on a
  `Type`-valued presheaf;
- derived API: the underlying presheaf, the forgetful functor to presheaves, and the equivalence
  between morphisms of sheaves and morphisms of the underlying presheaves.

Source/core/bridge triage:
- `source-facing`: the Stacks notation `Sh(X)` together with the description of its morphisms;
- `core/canonical`: `TopCat.Sheaf` and `TopCat.Presheaf.IsSheaf`;
- `bridge/view`: `TopCat.Sheaf.forget` and `Sheaf.homEquiv`, which expose the underlying
  presheaf-level view without introducing a parallel local owner.

Since Definition 6.7.1 only recalls the canonical category of sheaves of sets and its morphisms,
this file should stay in direct recall/check form rather than define any wrapper around the sheaf
owner or around sheaf morphisms. -/

/- Definition 6.7.1 (1) and (3): the category of sheaves of sets on a topological space `X`,
denoted `Sh(X)` in the Stacks Project, is the canonical project-facing owner `Sh(X)`
of set-valued presheaves satisfying the sheaf condition. -/
recall TopCat.Sheaf
#check (Sh(X))

/- The sheaf condition on a set-valued presheaf on `X` is the canonical predicate
`TopCat.Presheaf.IsSheaf`, expressing existence and uniqueness of gluing for compatible local
sections over open covers. -/
#check (Presheaf.IsSheaf : X.Presheaf (Type v) → Prop)

section

variable {X}
variable (ℱ 𝒢 : Sh(X))

/- Definition 6.7.1 (2): morphisms in `Sh(X)` are exactly morphisms of the underlying presheaves,
via the canonical fully faithful inclusion of sheaves into presheaves. -/
#check (Sheaf.homEquiv : (ℱ ⟶ 𝒢) ≃ (ℱ.presheaf ⟶ 𝒢.presheaf))

/- The same identification is implemented by the canonical forgetful functor from sheaves to
presheaves. -/
#check (Sheaf.forget (Type v) X : Sh(X) ⥤ X.Presheaf (Type v))

end
