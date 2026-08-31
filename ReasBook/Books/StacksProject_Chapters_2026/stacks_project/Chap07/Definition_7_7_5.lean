module

public import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/- Domain-style sampling for Definition 7.7.5:
- primary domain: categories of sheaves on a Grothendieck site;
- sampled canonical declarations:
  `Sheaf`,
  `Presheaf.IsSheaf`,
  `sheafToPresheaf`,
  `isSheaf_iff_isSheaf_of_type`,
- best owner abstraction: `Sheaf`, whose defining predicate is `Presheaf.IsSheaf`.

Source/core/bridge triage:
- `source-facing`: the Stacks category of sheaves of sets on `(C, J)`;
- `core/canonical`: `Sheaf`;
- `bridge/view`: specialize the value category to `Type (max u v)`; the underlying set-valued
  presheaf is recovered by `sheafToPresheaf J (Type (max u v))`, and the defining predicate on that
  presheaf is canonically `Presheaf.IsSheaf J`, equivalent to the original set-valued sheaf
  condition by `isSheaf_iff_isSheaf_of_type`.

Primitive data are only a set-valued presheaf together with the predicate `Presheaf.IsSheaf J`.
The category structure and forgetful view to presheaves are derived automatically from the owner
`Sheaf J (Type (max u v))`, so no local wrapper or duplicate owner should survive here.
-/
/- Definition 7.7.5: the category of sheaves of sets on `(C, J)` is
`Sheaf J (Type (max u v))`, i.e. the full subcategory of set-valued presheaves satisfying the
canonical predicate `Presheaf.IsSheaf J`. -/
#check (Sheaf J (Type (max u v)))
