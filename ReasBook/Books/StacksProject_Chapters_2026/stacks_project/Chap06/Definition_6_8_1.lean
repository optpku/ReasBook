module

public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopCat

universe u v

namespace TopCat

scoped notation "Ab(" X ")" => TopCat.Sheaf AddCommGrpCat X

end TopCat

open scoped TopCat

variable (X : TopCat.{u})

/- Domain-style sampling for Definition 6.8.1:
- primary domain: sheaves on a topological space valued in `AddCommGrpCat`;
- sampled owner declarations:
  `TopCat.Sheaf`,
  `TopCat.Sheaf.presheaf`,
  `TopCat.Sheaf.forget`,
  `TopCat.Presheaf.isSheaf_iff_isSheaf_comp`;
- best owner abstraction: the canonical sheaf owner specialized to abelian groups, with
  source-facing chapter notation `Ab(X)` and underlying owner `X.Sheaf AddCommGrpCat`.

Primitive-vs-derived split:
- primitive data: none beyond the existing owner `X.Sheaf AddCommGrpCat`;
- derived API: for an abelian presheaf `F : X.Presheaf AddCommGrpCat`, the underlying set-valued
  sheaf condition is identified by
  `TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat)`.

Source/core/bridge triage:
- `source-facing`: an abelian sheaf on `X` is an abelian presheaf whose underlying set-valued
  presheaf is a sheaf;
- `core/canonical`: `X.Sheaf AddCommGrpCat`;
- `bridge/view`: the comparison theorem
  `TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat)`.
-/

/- Definition 6.8.1: the category of abelian sheaves on `X`, denoted `Ab(X)` in the Stacks
Project, is the canonical sheaf owner specialized to `AddCommGrpCat`. -/
recall TopCat.Sheaf
#check (Ab(X))
#check (X.Sheaf AddCommGrpCat)

variable {X : TopCat.{u}}

/- The source wording "an abelian sheaf is an abelian presheaf whose underlying presheaf of sets
is a sheaf" is the canonical sheaf condition on `AddCommGrpCat`-valued presheaves, compared with
the underlying `Type`-valued sheaf condition by
`TopCat.Presheaf.isSheaf_iff_isSheaf_comp`. -/
#check
  (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat) :
    ∀ F : X.Presheaf AddCommGrpCat,
      F.IsSheaf ↔ TopCat.Presheaf.IsSheaf (F ⋙ forget AddCommGrpCat))
