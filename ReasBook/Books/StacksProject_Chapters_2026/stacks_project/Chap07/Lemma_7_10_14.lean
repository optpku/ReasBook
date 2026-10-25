module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Sheaf

universe w v u

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable (I : Type w) [Category I] [Small.{max u v} I]
variable [HasWeakSheafify J (Type (max u v))]
variable (F : I ⥤ Sheaf J (Type (max u v)))

/- Source/core/bridge triage for Lemma 7.10.14:
- source-facing content: colimits of set-valued sheaves are obtained by sheafifying a colimit
  cocone of the underlying presheaf diagram
- core/canonical owner: `CategoryTheory.Sheaf.isColimitSheafifyCocone`
- bridge/view: the `Type`-specialization to the canonical cocone
  `colimit.cocone (F ⋙ sheafToPresheaf J (Type (max u v)))`
- primitive data: the diagram `F`
- derived API: the colimit cocone in sheaves, obtained by sheafifying the underlying presheaf
  colimit cocone
-/
/- Lemma 7.10.14: for a small diagram `F` of sheaves of sets on the site `(C, J)`, the colimit
of `F` is obtained by sheafifying the colimit cocone of the underlying diagram of presheaves.
This is exactly the canonical sheaf-colimit statement `Sheaf.isColimitSheafifyCocone`. -/
recall Sheaf.isColimitSheafifyCocone

/- Source-facing specialization: the set-valued sheaf colimit cocone attached to `F` is the
sheafification of the presheaf colimit cocone. -/
#check
  (isColimitSheafifyCocone
    (colimit.cocone (F ⋙ sheafToPresheaf J (Type (max u v))))
    (colimit.isColimit (F ⋙ sheafToPresheaf J (Type (max u v)))))
