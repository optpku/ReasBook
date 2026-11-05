module

public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open TopCat

universe u

namespace TopCat

scoped notation "PAb(" X ")" => Presheaf AddCommGrpCat X

end TopCat

open scoped TopCat

variable (X : TopCat.{u})

/- Domain-style sampling for Definition 6.4.4:
- primary domain: presheaves on topological spaces valued in the concrete algebraic category
  `AddCommGrpCat`;
- sampled owner declarations:
  `TopCat.Presheaf`,
  `TopCat.Presheaf.restrict`,
  `TopCat.Presheaf.restrict_sum`;
- best owner abstraction: the canonical presheaf owner specialized to abelian groups,
  with source-facing project notation `PAb(X)` and underlying owner `X.Presheaf AddCommGrpCat`.

Primitive-vs-derived split:
- primitive data: none beyond the existing owner `X.Presheaf AddCommGrpCat`;
- derived API: objectwise additive commutative group structures on sections and additivity of
  restriction maps come from the concrete-category structure on `AddCommGrpCat`, so they should be
  reused rather than restated as separate data.

Source/core/bridge triage:
- `source-facing`: the Stacks notation `PAb(X)` for the category of abelian presheaves on `X`;
- `core/canonical`: `X.Presheaf AddCommGrpCat`;
- `bridge/view`: none needed here, since the source notion is exactly a canonical specialization of
  the owner. -/

/- Definition 6.4.4: the category of abelian presheaves on `X`, denoted `PAb(X)` in the Stacks
Project, is the canonical presheaf owner specialized to `AddCommGrpCat`. -/
recall TopCat.Presheaf
#check (PAb(X))
#check (X.Presheaf AddCommGrpCat)
