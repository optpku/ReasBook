module

public import Mathlib.CategoryTheory.EqToHom
public import stacks_project.Chap04.Lemma_4_31_6
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits
open CategoricalPullback
open scoped CategoricalPullback

namespace CategoryTheory.Limits

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]
variable {D : Type u₄} [Category.{v₄} D]
variable {E : Type u₅} [Category.{v₅} E]
variable {F : Type u₆} [Category.{v₆} F]

/-
Domain-style sampling for Lemma 4.31.9:
- primary domain: categorical pullbacks of functors and induced functors between pullback
  categories;
- sampled owner API:
  `CategoricalPullback`,
  `CatCommSq`,
  `CategoricalPullback.catCommSq`,
  `two_fibre_product_map`,
  `Functor.leftUnitor`;
- core/canonical owner abstraction: the chapter owner `two_fibre_product_map` from Lemma `4.31.6`
  is the induced functor on categorical pullbacks; this file only needs its source-facing
  specialization to the projection from an iterated pullback; the only extra derived datum is the
  nontrivial left comparison isomorphism, while the right comparison is the canonical unitor;
- primitive-vs-derived split: the primitive data are the pullback square `catCommSq AB CB` and the
  strict commutativity hypothesis `hcomm : CB ⋙ BF = CD ⋙ DF`; the projection functor `pr_{02}` is
  derived API.

Source/core/bridge triage:
- `source-facing`: the canonical projection
  `two_fibre_product_pr02 : (A ×[B] C) ×[D] E ⥤ A ×[F] E`;
- `core/canonical`: `CategoricalPullback`, `CategoricalPullback.catCommSq`, and the chapter owner
  `two_fibre_product_map`;
- `bridge/view`: the two comparison isomorphisms needed to specialize
  `two_fibre_product_map` to the cospan `A ⥤ B ⥤ F`, `C ⥤ B`, `C ⥤ D ⥤ F`, `E ⥤ D`. -/

section

variable (AB : A ⥤ B) (CB : C ⥤ B) (CD : C ⥤ D) (ED : E ⥤ D) (BF : B ⥤ F) (DF : D ⥤ F)
variable (hcomm : CB ⋙ BF = CD ⋙ DF)

local notation "LeftAssoc" => ((π₂ AB CB) ⋙ CD) ⊡ ED
local notation "OuterPullback" => (AB ⋙ BF) ⊡ (ED ⋙ DF)

/-- The comparison isomorphism sending the iterated pullback cospan
`π₂ AB CB ⋙ CD ⋙ DF` to the outer cospan `π₁ AB CB ⋙ AB ⋙ BF`. -/
abbrev pr02BaseIso :
    π₂ AB CB ⋙ CD ⋙ DF ≅ π₁ AB CB ⋙ AB ⋙ BF :=
  Functor.associator (π₂ AB CB) CD DF ≪≫
    Functor.isoWhiskerLeft (π₂ AB CB) (eqToIso hcomm.symm) ≪≫
    (Functor.associator (π₂ AB CB) CB BF).symm ≪≫
    Functor.isoWhiskerRight (catCommSq AB CB).iso.symm BF ≪≫
    Functor.associator (π₁ AB CB) AB BF

/-- Lemma 4.31.9: a strictly commutative diagram
`A ⥤ B ⥤ F`, `C ⥤ B`, `C ⥤ D ⥤ F`, and `E ⥤ D` induces the canonical projection functor
`pr_{02} : (A ×[B] C) ×[D] E ⥤ A ×[F] E`. -/
abbrev two_fibre_product_pr02 :
    LeftAssoc ⥤ OuterPullback :=
  two_fibre_product_map (Functor.leftUnitor (ED ⋙ DF)) (pr02BaseIso AB CB CD BF DF hcomm)

/-- The projection functor `pr_{02}` is the pullback comparison functor specialized using the
canonical left unitor on `ED ⋙ DF` and the comparison isomorphism `pr02BaseIso`. -/
theorem two_fibre_product_pr02_def :
    two_fibre_product_pr02 AB CB CD ED BF DF hcomm =
      two_fibre_product_map (Functor.leftUnitor (ED ⋙ DF)) (pr02BaseIso AB CB CD BF DF hcomm) :=
  rfl

/-- The projection functor `pr_{02}` sends an object of the iterated pullback to its `A`-component. -/
@[simp] theorem two_fibre_product_pr02_obj_fst (P : LeftAssoc) :
    ((two_fibre_product_pr02 AB CB CD ED BF DF hcomm).obj P).fst = P.fst.fst :=
  rfl

/-- The projection functor `pr_{02}` sends an object of the iterated pullback to its `E`-component. -/
@[simp] theorem two_fibre_product_pr02_obj_snd (P : LeftAssoc) :
    ((two_fibre_product_pr02 AB CB CD ED BF DF hcomm).obj P).snd = P.snd :=
  rfl

/-- On the first component, `pr_{02}` maps morphisms by the `A`-part of the iterated pullback
morphism. -/
@[simp] theorem two_fibre_product_pr02_map_fst {P Q : LeftAssoc} (f : P ⟶ Q) :
    ((two_fibre_product_pr02 AB CB CD ED BF DF hcomm).map f).fst = f.fst.fst :=
  rfl

/-- On the second component, `pr_{02}` maps morphisms by the `E`-part of the iterated pullback
morphism. -/
@[simp] theorem two_fibre_product_pr02_map_snd {P Q : LeftAssoc} (f : P ⟶ Q) :
    ((two_fibre_product_pr02 AB CB CD ED BF DF hcomm).map f).snd = f.snd :=
  rfl

end

end CategoryTheory.Limits
