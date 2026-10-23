module

public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopologicalSpace TopCat

universe u v

namespace TopCat

set_option quotPrecheck false in
scoped notation:max A " ₚ " X =>
  (Functor.const (Opens X)ᵒᵖ).obj A

end TopCat

open scoped TopCat

variable (X : TopCat.{u}) (A : Type v)

/- Domain-style sampling for Definition 6.3.2:
- primary domain: set-valued presheaves on a topological space, viewed as a functor category;
- sampled owner API:
  `TopCat.Presheaf`,
  `Functor.const`,
  `CategoryTheory.Functor.obj`,
  `TopCat.Presheaf.Γgerm`;
- best owner abstraction: the constant-functor owner
  `Functor.const (Opens X)ᵒᵖ : Type v ⥤ X.Presheaf (Type v)`;
- source/core/bridge triage:
  `source-facing`: the Stacks constant-presheaf notation `A ₚ X`;
  `core/canonical`: the generic constant-functor owner in the functor category;
  `bridge/view`: the notation `A ₚ X` realizing the specialization of that owner at `A`.

Primitive data are the index category `(Opens X)ᵒᵖ` and the value `A`. The object-level constant
presheaf is derived from the owner abstraction by `.obj A`; the only extra surface needed in this
owner file is the chapter-facing notation `A ₚ X`, not a parallel wrapper definition.
-/
/- Definition 6.3.2: the constant presheaf construction on `X` is the canonical constant-functor
owner, exposed on the chapter surface by the notation `A ₚ X`. -/
recall Functor.const
#check (Functor.const (Opens X)ᵒᵖ : Type v ⥤ X.Presheaf (Type v))

/- Definition 6.3.2 source-facing object: `A ₚ X` is the constant presheaf on `X` with value
`A`. -/
#check (A ₚ X : X.Presheaf (Type v))
