module

public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Subsheaf


@[expose] public section

open CategoryTheory
open CategoryTheory.GrothendieckTopology
open Opposite

universe u v w

noncomputable section

namespace CategoryTheory

attribute [local instance] Types.instConcreteCategory
attribute [local instance] Types.instFunLike

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

/-- Helper for Lemma 7.28.1: restriction preserves the defining equation for the fibre over a
chosen section of a morphism of type-valued sheaves. -/
theorem sectionFiberSubfunctor_map_mem
    {E B : Sheaf J (Type w)} (π : E ⟶ B) {U : C}
    (b : B.obj.obj (op U)) {X Y : (Over U)ᵒᵖ} (f : X ⟶ Y)
    {s : E.obj.obj (op X.unop.left)}
    (hs : π.hom.app (op X.unop.left) s = B.obj.map X.unop.hom.op b) :
    π.hom.app (op Y.unop.left) (E.obj.map f.unop.left.op s) =
      B.obj.map Y.unop.hom.op b := by
  -- Naturality moves the structure map past restriction from `X` to `Y`.
  have hnat := congrFun (π.hom.naturality f.unop.left.op) s
  dsimp at hnat
  rw [hs] at hnat
  -- The chosen base section restricts along the triangle in the over-category.
  refine hnat.trans ?_
  calc
    B.obj.map f.unop.left.op (B.obj.map X.unop.hom.op b) =
        B.obj.map (X.unop.hom.op ≫ f.unop.left.op) b := by
          exact (FunctorToTypes.map_comp_apply B.obj X.unop.hom.op f.unop.left.op b).symm
    _ = B.obj.map Y.unop.hom.op b := by
          exact congrArg (fun m ↦ B.obj.map m b) <|
            by simpa only [op_comp] using congrArg Quiver.Hom.op (Over.w f.unop)

/-- Helper for Lemma 7.28.1: the subpresheaf of sections of `E` mapping to the restriction of a
fixed section of `B`. -/
def sectionFiberSubfunctor
    {E B : Sheaf J (Type w)} (π : E ⟶ B) {U : C}
    (b : B.obj.obj (op U)) :
    Subfunctor ((Over.forget U).op ⋙ E.obj) where
  obj X := { s | π.hom.app (op X.unop.left) s = B.obj.map X.unop.hom.op b }
  map := fun f _ hs ↦ sectionFiberSubfunctor_map_mem π b f hs

/-- Helper for Lemma 7.28.1: the presheaf on `C/U` whose sections are fibres of a morphism of
sheaves over a fixed section. -/
abbrev sectionFiberPresheaf
    {E B : Sheaf J (Type w)} (π : E ⟶ B) {U : C}
    (b : B.obj.obj (op U)) :
    (Over U)ᵒᵖ ⥤ Type w :=
  (sectionFiberSubfunctor π b).toFunctor

/-- Helper for Lemma 7.28.1: a section fibre of a morphism of type-valued sheaves is a sheaf on
the localized site. -/
theorem sectionFiberPresheaf_isSheaf
    {E B : Sheaf J (Type w)} (π : E ⟶ B) {U : C}
    (b : B.obj.obj (op U)) :
    Presieve.IsSheaf (J.over U) (sectionFiberPresheaf π b) := by
  let G := sectionFiberSubfunctor π b
  -- The ambient source sheaf remains a sheaf after restriction to the localized site.
  have hbase : Presieve.IsSheaf (J.over U) ((Over.forget U).op ⋙ E.obj) :=
    (Over.forget U).op_comp_isSheaf_of_types (J.over U) J E
  -- A locally fibre-valued section is globally fibre-valued because the target sheaf is separated.
  rw [sectionFiberPresheaf, Subfunctor.isSheaf_iff G hbase]
  intro X s hs
  have htarget : Presieve.IsSheaf (J.over U) ((Over.forget U).op ⋙ B.obj) :=
    (Over.forget U).op_comp_isSheaf_of_types (J.over U) J B
  -- It remains to prove that the two target sections agree; separatedness of `B` reduces this to
  -- checking the equality after every arrow in the covering sieve attached to `s`.
  refine (htarget (G.sieveOfSection s) hs).isSeparatedFor.ext ?_
  intro Y f hf
  -- Restrict both candidate target sections along a cover arrow and use the local fibre equation.
  have hnat := congrFun (π.hom.naturality f.left.op) s
  dsimp at hnat
  have hbaseSection :
      B.obj.map f.left.op (B.obj.map X.unop.hom.op b) =
        B.obj.map Y.hom.op b := by
    calc
      B.obj.map f.left.op (B.obj.map X.unop.hom.op b) =
          B.obj.map (X.unop.hom.op ≫ f.left.op) b := by
            exact (FunctorToTypes.map_comp_apply B.obj X.unop.hom.op f.left.op b).symm
      _ = B.obj.map Y.hom.op b := by
            exact congrArg (fun m ↦ B.obj.map m b) <|
              by simpa only [op_comp] using congrArg Quiver.Hom.op (Over.w f)
  have hfiber :
      π.hom.app (op Y.left) (E.obj.map f.left.op s) =
        B.obj.map Y.hom.op b := by
    simpa [Subfunctor.sieveOfSection, G, sectionFiberSubfunctor] using hf
  -- Naturality and the local fibre equation identify the two restrictions required for
  -- separatedness.
  exact hnat.symm.trans (hfiber.trans hbaseSection.symm)

/-- Helper for Lemma 7.28.1: bundle the section-fibre presheaf as a sheaf on the localized site.
-/
abbrev sectionFiberSheaf
    {E B : Sheaf J (Type w)} (π : E ⟶ B) {U : C}
    (b : B.obj.obj (op U)) :
    Sheaf (J.over U) (Type w) :=
  ⟨sectionFiberPresheaf π b,
    (isSheaf_iff_isSheaf_of_type (J.over U) (sectionFiberPresheaf π b)).2
      (sectionFiberPresheaf_isSheaf π b)⟩

end

end CategoryTheory
