module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Tactic.Recall
public import stacks_project.Chap07.Lemma_7_25_4

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.GrothendieckTopology
open scoped SheafifiedRepresentable

universe u v

noncomputable section

namespace CategoryTheory.GrothendieckTopology

attribute [local instance] Types.instConcreteCategory
attribute [local instance] Types.instFunLike

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (U : C)

/- Lemma 7.30.5: if `ℱ = h_U^#`, then the localization morphism
`Sh(C, J)/ℱ ⥤ Sh(C, J)` from Lemma 7.30.1 agrees, via the equivalence
`Sh(C/U, J.over U) ≌ Sh(C, J)/h_U^#` of Lemma 7.25.4, with the localization morphism
`j_U : Sh(C/U, J.over U) ⥤ Sh(C, J)`. Equivalently, after identifying sheaves on `C/U` with
sheaves over `h_U^#`, the forgetful functor to `Sh(C, J)` is exactly `j_{U!}`.

This is the owner-level companion theorem
`GrothendieckTopology.representableLocalizationComparison_forget` attached to the comparison
functor of Lemma 7.25.4. -/
recall representableLocalizationComparison_forget

end CategoryTheory.GrothendieckTopology
