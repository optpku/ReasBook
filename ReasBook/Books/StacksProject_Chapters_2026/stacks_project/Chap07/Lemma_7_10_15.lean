module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)

/- Domain-style sampling for Lemma 7.10.15:
- primary domain: exactness of set-valued sheafification on a Grothendieck site;
- sampled owner API:
  `presheafToSheaf`,
  `PreservesFiniteLimits (presheafToSheaf J (Type (max u v)))`,
  `Sheaf.isColimitSheafifyCocone`,
  `ExactFunctor.of`;
- best owner abstraction: `ExactFunctor.of (presheafToSheaf J (Type (max u v)))`;
- primitive data: the Grothendieck topology `J`;
- derived API: the underlying sheafification functor obtained by forgetting the exact structure.

Source/core/bridge triage:
- source-facing: the sheafification functor on set-valued presheaves is exact;
- core/canonical: `ExactFunctor.of (presheafToSheaf J (Type (max u v)))`;
- bridge/view: forgetting the bundled exact structure recovers the usual sheafification functor.
-/

/- Lemma 7.10.15 recalls the owner sheafification functor used to build the exact functor. -/
recall presheafToSheaf

/- Lemma 7.10.15: the sheafification functor from set-valued presheaves on `(C, J)` to sheaves of
sets on `(C, J)` is exact. The canonical bundled exact-functor owner is `ExactFunctor.of`. -/
recall ExactFunctor.of

/- Source-facing specialization: the exact sheafification functor for set-valued presheaves. -/
#check
  (ExactFunctor.of (presheafToSheaf J (Type (max u v))) :
    (Cᵒᵖ ⥤ Type (max u v)) ⥤ₑ Sheaf J (Type (max u v)))
