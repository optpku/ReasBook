module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Lemma_7_12_4

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe u v

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J (Type (max u v))]

/- Domain-style sampling for Lemma 7.12.6:
- primary domain: density-style colimit presentations of sheaves by sheafified representables;
- sampled owner declarations:
  `Presheaf.functorToRepresentables`,
  `Presheaf.coconeOfRepresentable`,
  `Presheaf.colimitOfRepresentable`,
  `sheafificationNatIso`,
  `GrothendieckTopology.sheafifiedRepresentableFunctor`;
- best owner abstraction: map the canonical presheaf density presentation of the underlying
  presheaf of `ℱ` through the left adjoint `presheafToSheaf J (Type (max u v))`, then transport
  the target along `sheafificationNatIso`;
- primitive data: the underlying presheaf `ℱ.obj` and its category-of-elements projection
  `CategoryOfElements.π ℱ.obj`;
- derived API: the resulting `ColimitPresentation` in `Sheaf J (Type (max u v))` whose diagram is
  `U ⋙ J.sheafifiedRepresentableFunctor`.

Source/core/bridge triage:
- `source-facing`: existence of a colimit presentation of `ℱ` by sheafified representables;
- `core/canonical`: `ColimitPresentation`, `Presheaf.colimitOfRepresentable`, and
  `sheafificationNatIso`;
- `bridge/view`: applying the sheafification left adjoint to the presheaf density presentation.

This item should stay `source-facing`, but it should reuse the canonical density owner instead of
keeping a chapter-local helper that repackages a coequalizer presentation into a colimit
presentation.
-/

-- Proof sketch: present the underlying presheaf of `ℱ` as a colimit of representables via its
-- category of elements, map that colimit presentation through sheafification, and then identify
-- the sheafification of `ℱ.obj` with `ℱ` by the canonical reflective isomorphism
-- `sheafificationNatIso`.
/-- Lemma 7.12.6: every sheaf of sets on a site is a colimit of sheafified representables
`h_U^#`. -/
theorem exists_colimit_presentation_by_sheafifiedRepresentables
    (ℱ : Sheaf J (Type (max u v))) :
    ∃ (I : Type (max u v)) (_ : SmallCategory I) (U : I ⥤ C)
      (pres : ColimitPresentation I ℱ),
      pres.diag = U ⋙ J.sheafifiedRepresentableFunctor := by
  -- Use the category of elements of the underlying presheaf to realize the textbook indexing
  -- category of pairs `(U, s)`.
  let I : Type (max u v) := ShrinkHoms (ℱ.obj.Elementsᵒᵖ)
  let U : I ⥤ C :=
    (ShrinkHoms.equivalence (ℱ.obj.Elementsᵒᵖ)).inverse ⋙ (CategoryOfElements.π ℱ.obj).leftOp
  -- The underlying presheaf is the canonical colimit of representables over its category of
  -- elements.
  let presheafPresentation : ColimitPresentation (ℱ.obj.Elementsᵒᵖ) ℱ.obj :=
    { diag := Presheaf.functorToRepresentables.{max u v} ℱ.obj
      ι := (Presheaf.coconeOfRepresentable.{max u v} ℱ.obj).ι
      isColimit := Presheaf.colimitOfRepresentable.{max u v} ℱ.obj }
  let reindexedPresheafPresentation : ColimitPresentation I ℱ.obj :=
    presheafPresentation.reindex (ShrinkHoms.equivalence (ℱ.obj.Elementsᵒᵖ)).inverse
  -- Sheafification preserves this colimit presentation, and the resulting sheafification of
  -- `ℱ.obj` is canonically isomorphic to `ℱ`.
  let pres :=
    (reindexedPresheafPresentation.map (presheafToSheaf J (Type (max u v)))).ofIso
      (((sheafificationNatIso J (Type (max u v))).app ℱ).symm)
  refine ⟨I, inferInstance, U, pres, ?_⟩
  -- The diagram after sheafification is definitionally the sheafified representable functor.
  change (reindexedPresheafPresentation.map (presheafToSheaf J (Type (max u v)))).diag =
      U ⋙ J.sheafifiedRepresentableFunctor
  simp only [U, reindexedPresheafPresentation, presheafPresentation,
    GrothendieckTopology.sheafifiedRepresentableFunctor,
    GrothendieckTopology.uliftSheafifiedRepresentableFunctor,
    CategoryTheory.Presheaf.functorToRepresentables]
  rfl

end CategoryTheory.GrothendieckTopology
