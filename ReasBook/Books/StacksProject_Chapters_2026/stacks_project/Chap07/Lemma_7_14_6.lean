module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import stacks_project.Chap07.Definition_7_14_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe w u₁ u₂ v₁ v₂

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-
Domain-style sampling for Lemma 7.14.6:
- primary domain: morphisms of sites built from continuous functors and filtered structured-arrow
  categories;
- sampled owner API:
  `RepresentablyFlat`,
  `RepresentablyFlat.cofiltered`,
  `isMorphismOfSites_of_isContinuous_representablyFlat`,
  `isMorphismOfSites_sheafPullback_exact`;
- source/core/bridge triage:
  `source-facing`: the textbook hypothesis that `(StructuredArrow V u)ᵒᵖ` is filtered for every
  `V : D`;
  `core/canonical`: `RepresentablyFlat u`;
  `bridge/view`: the induced site-morphism and sheaf-exactness statements below.

Primitive data here are only the continuity hypothesis and the filteredness of the opposite
structured-arrow categories. `RepresentablyFlat u` is the owner abstraction for that data, while
`IsMorphismOfSites J K u` and exactness of `u.sheafPullback` are derived API.
-/

/-- Helper for Lemma 7.14.6: the textbook hypothesis that every opposite structured-arrow category
`(StructuredArrow V u)ᵒᵖ` is filtered is exactly the source-facing form of the canonical owner
datum `RepresentablyFlat u`. -/
theorem representablyFlat_of_structuredArrow_op_isFiltered
    (u : C ⥤ D) (hfiltered : ∀ V : D, IsFiltered (StructuredArrow V u)ᵒᵖ) :
    RepresentablyFlat u where
  cofiltered V := by
    -- Convert the filteredness of the opposite structured-arrow category into the owner field.
    let _ : IsFiltered (StructuredArrow V u)ᵒᵖ := hfiltered V
    exact isCofiltered_of_isFiltered_op (StructuredArrow V u)

-- Proof sketch: build the canonical `RepresentablyFlat u` instance from the textbook hypothesis
-- and then reuse the owner instance from Definition `7.14.1`.
/-- Lemma 7.14.6: if `u : \mathcal C \to \mathcal D` is continuous and each opposite
structured-arrow category `(StructuredArrow V u)ᵒᵖ`, i.e. `(𝓘_V^u)ᵒᵖ`, is filtered, then `u`
defines a morphism of sites `(\mathcal D, K) ⟶ (\mathcal C, J)`. -/
theorem isMorphismOfSites_of_filtered_op_structuredArrow
    (u : C ⥤ D) [u.IsContinuous J K]
    (hfiltered : ∀ V : D, IsFiltered (StructuredArrow V u)ᵒᵖ) :
    IsMorphismOfSites J K u := by
  let _ : RepresentablyFlat u := representablyFlat_of_structuredArrow_op_isFiltered u hfiltered
  exact isMorphismOfSites_of_isContinuous_representablyFlat J K u

-- Proof sketch: the bridge theorem supplies `IsMorphismOfSites J K u`, and exactness is then the
-- existing canonical consequence `isMorphismOfSites_sheafPullback_exact`.
/-- The inverse-image functor on set-valued sheaves attached to Lemma 7.14.6 is exact. -/
theorem sheafPullback_exact_of_filtered_op_structuredArrow
    (u : C ⥤ D) [u.IsContinuous J K]
    (hfiltered : ∀ V : D, IsFiltered (StructuredArrow V u)ᵒᵖ)
    [HasSheafify J (Type w)] [HasSheafify K (Type w)]
    [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension P]
    [PreservesFiniteLimits (u.op.lan : (Cᵒᵖ ⥤ Type w) ⥤ Dᵒᵖ ⥤ Type w)] :
    exactFunctor (Sheaf J (Type w)) (Sheaf K (Type w))
      (u.sheafPullback (Type w) J K) := by
  let _ : IsMorphismOfSites J K u :=
    isMorphismOfSites_of_filtered_op_structuredArrow u hfiltered
  exact isMorphismOfSites_sheafPullback_exact u

end
