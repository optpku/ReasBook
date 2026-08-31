module

public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (P : Cᵒᵖ ⥤ Type (max u v))

/- Source/core/bridge triage for Definition 7.10.11:
- source-facing content: the associated sheaf `P^#` of a set-valued presheaf `P` on `(C, J)`;
- core/canonical owner: `presheafToSheaf J (Type (max u v))`;
- derived API: the underlying sheafification `J.sheafify P` and the unit `J.toSheafify P`.

The source item only recalls the canonical sheafification owner, so this file keeps the public
surface at that owner and records the underlying presheaf and unit map only as companion views.
-/
/- Definition 7.10.11: the associated sheaf `P^#` of a set-valued presheaf `P` on the site
`(C, J)` is the image of `P` under the canonical sheafification functor
`presheafToSheaf J (Type (max u v))`. -/
recall presheafToSheaf

/- Source-facing specialization: `P^#` is the bundled sheaf obtained by applying the
sheafification functor to `P`. -/
#check (presheafToSheaf J (Type (max u v))).obj P

/- Companion recall: the underlying-presheaf owner is `GrothendieckTopology.sheafify`. -/
recall GrothendieckTopology.sheafify

/- Companion recall: the underlying presheaf of `P^#` is the canonical sheafification
`J.sheafify P`, implemented in mathlib by the usual plus-plus construction. -/
#check J.sheafify P

/- Companion recall: the unit owner is `GrothendieckTopology.toSheafify`. -/
recall GrothendieckTopology.toSheafify

/- Companion recall: the canonical map from `P` to the underlying presheaf of `P^#` is the
sheafification unit `J.toSheafify P : P ⟶ J.sheafify P`. -/
#check J.toSheafify P
