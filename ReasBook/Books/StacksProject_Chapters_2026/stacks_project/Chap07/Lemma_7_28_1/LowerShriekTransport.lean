module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Lemma_7_12_4
public import stacks_project.Chap07.Definition_7_14_1
public import stacks_project.Chap07.Lemma_7_25_2
public import stacks_project.Chap07.Lemma_7_25_9
public import stacks_project.Chap07.Lemma_7_25_8
public import stacks_project.Chap07.Remark_7_25_10
public import stacks_project.Chap07.Lemma_7_28_1.SliceStructuredArrow

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology
open Opposite

universe w u₁ u₂ v₁ v₂ v₃

noncomputable section

namespace CategoryTheory

attribute [local instance] Types.instConcreteCategory
attribute [local instance] Types.instFunLike

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}

/-- Helper for Lemma 7.28.1: any ambient sheaf on `(C, JC)` remains a sheaf after first pulling
back along `u` and then restricting to the slice over `V`. -/
theorem overPost_ambient_restriction_isSheaf
    (u : D ⥤ C) [u.IsContinuous JD JC] (V : D)
    (F : Sheaf JC (Type (max u₁ u₂ v₁ v₂))) :
    Presieve.IsSheaf (JD.over V) (((Over.forget V).op ⋙ u.op) ⋙ F.obj) := by
  -- First use continuity of `u`, then continuity of the localized forgetful functor.
  exact
    (Over.forget V).op_comp_isSheaf_of_types (JD.over V) JD
      ⟨u.op ⋙ F.obj, (isSheaf_iff_isSheaf_of_type JD (u.op ⋙ F.obj)).2
        (u.op_comp_isSheaf_of_types JD JC F)⟩

/-- Helper for Lemma 7.28.1: the ambient lower-shriek sheaf `j_{u(V)!} ℋ` attached to a localized
sheaf `ℋ` on `(C/u(V), JC.over u(V))`. -/
abbrev overPost_lowerShriek_obj
    (u : D ⥤ C) (V : D)
    (ℋ : Sheaf (JC.over (u.obj V)) (Type (max u₁ u₂ v₁ v₂))) :
    Sheaf JC (Type (max u₁ u₂ v₁ v₂)) :=
  ((Over.forget (u.obj V)).sheafPullback (Type (max u₁ u₂ v₁ v₂))
    (JC.over (u.obj V)) JC).obj ℋ

/-- Helper for Lemma 7.28.1: after localizing `ℋ` to the ambient site by `j_{u(V)!}`, the
restriction of the resulting sheaf along `Over.forget V ⋙ u` is already a sheaf on `(D/V,
JD.over V)`. -/
theorem overPost_lowerShriek_isSheaf_on_slice
    (u : D ⥤ C) [u.IsContinuous JD JC] (V : D)
    (ℋ : Sheaf (JC.over (u.obj V)) (Type (max u₁ u₂ v₁ v₂))) :
    Presieve.IsSheaf (JD.over V)
      (((Over.forget V).op ⋙ u.op) ⋙ (overPost_lowerShriek_obj (u := u) (V := V) ℋ).obj) := by
  -- This is exactly the ambient sheaf argument applied to `j_{u(V)!} ℋ`.
  exact overPost_ambient_restriction_isSheaf
    (u := u) (V := V) (F := overPost_lowerShriek_obj (u := u) (V := V) ℋ)

end

end CategoryTheory
