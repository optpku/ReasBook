module

public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Mathlib.Tactic.Recall
public import stacks_project.Chap07.Definition_7_10_11

@[expose] public section

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (P : Cᵒᵖ ⥤ Type (max u v))

/- Domain-style sampling for Definition 7.49.4:
- primary domain: sheafification of set-valued presheaves on a Grothendieck site;
- sampled owner API:
  `presheafToSheaf`,
  `GrothendieckTopology.sheafify`,
  `GrothendieckTopology.toSheafify`,
  `sheafificationAdjunction`;
- source-facing layer: the repeated textbook item defining the associated sheaf `P^#` of a
  presheaf `P`;
- core/canonical owner: `presheafToSheaf J (Type (max u v))`;
- bridge/view: the underlying presheaf `J.sheafify P` and the unit `J.toSheafify P`, already
  recorded in `Definition_7_10_11`.

Primitive data are only the site `(C, J)` and the presheaf `P`. The associated sheaf, its
underlying presheaf, and its unit map are derived from the owner sheafification functor, so this
repeated item should expose only that owner directly. The derived bridge/view API is reused from
the earlier chapter owner file rather than recopied here.
-/

/- Definition 7.49.4: the associated sheaf `P^#` of a set-valued presheaf `P` on `(C, J)` is
again the bundled sheaf obtained by applying the canonical sheafification functor
`presheafToSheaf J (Type (max u v))` to `P`. This repeats Definition 7.10.11, so this file keeps
only the source-facing recall of that owner and leaves the companion views upstream. -/
recall presheafToSheaf

/- Source-facing specialization: `P^#` is the bundled sheaf obtained by sheafifying `P`. -/
#check (presheafToSheaf J (Type (max u v))).obj P
