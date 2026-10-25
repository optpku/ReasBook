module

public import stacks_project.Chap04.Lemma_4_32_5
public import stacks_project.Chap04.Definition_4_35_6
public import stacks_project.Chap04.Lemma_4_35_7
public import stacks_project.Chap04.Lemma_4_35_13

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open CategoryOver

variable {C : Type u} [Category.{v} C]
variable {U : C}
variable {X Y : BasedCategory.{v, max u v} C}

/- Domain-style sampling for Lemma 4.42.2:
- primary domain: slice-level base change of categories fibred in groupoids, with the explicit
  `2`-fibre product from `Cat/C` viewed over the slice category `C/U`;
- inspected owner-level declarations:
  `explicitTwoFibreProduct`,
  `explicitTwoFibreProductLeftProjection`,
  `explicitTwoFibreProductProjection_isFibredInGroupoids`,
  `Functor.isFibredInGroupoids_of_comp_over_forget`,
  `FibredInGroupoidsOver.twoFibreProduct`;
- best owner abstraction: the source-facing object is the canonical explicit left projection
  `explicitTwoFibreProductLeftProjection G F : (C/U) ×_Y X ⥤ᵇ C/U`, and the main property should
  live directly on its underlying functor via `IsFibredInGroupoids`;
- primitive data: the based functors `F : X ⥤ᵇ Y` and
  `G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ Y`, together with the explicit pullback total
  category `explicitTwoFibreProduct G F`;
- derived API: the fibred-in-groupoids theorem for the explicit left projection; the bundled
  owner object is already supplied upstream by `FibredInGroupoidsOver.twoFibreProduct`.

Source/core/bridge triage:
- `source-facing`: `explicitTwoFibreProductLeftProjection_isFibredInGroupoids`;
- `core/canonical`: `explicitTwoFibreProductLeftProjection` and `IsFibredInGroupoids`;
- `bridge/view`: the bundled owner rebundling `FibredInGroupoidsOver.twoFibreProduct`. -/

-- Proof sketch: compose `(explicitTwoFibreProductLeftProjection G F).toFunctor` with
-- `Over.forget U` to recover the projection to `C` from Lemma `4.35.7`, which is fibred in
-- groupoids because the pullback source `X` is fibred in groupoids and the target projection
-- `Y.p` is fibred over `C`. Then apply
-- Lemma `4.35.13` to lift the fibred-in-groupoids structure along `Over.forget U`.
/-- Helper for Lemma 4.42.2: if the target projection `Y.p` is itself fibred in groupoids, then
the slice left projection is fibred in groupoids by descending the already-known composite over
`C` along `Over.forget U`. -/
theorem explicitTwoFibreProductLeftProjection_isFibredInGroupoids_of_target_groupoids
    {X' Y' : BasedCategory.{v, max u v} C}
    (F : X' ⥤ᵇ Y') (G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ Y')
    [IsFibredInGroupoids X'.p] [IsFibredInGroupoids Y'.p] :
    IsFibredInGroupoids (explicitTwoFibreProductLeftProjection G F).toFunctor := by
  let p : (explicitTwoFibreProduct G F).obj ⥤ Over U :=
    (explicitTwoFibreProductLeftProjection G F).toFunctor
  letI : IsFibredInGroupoids (BasedCategory.ofFunctor (Over.forget U)).p := by
    change IsFibredInGroupoids (Over.forget U)
    infer_instance
  -- Identify the composite to `C` with the explicit pullback projection handled in Lemma 4.35.7.
  have hp : p ⋙ Over.forget U = (explicitTwoFibreProduct G F).p := by
    simpa [p] using (explicitTwoFibreProductLeftProjection G F).w
  -- Fix the ambient owner parameters explicitly so Lean sees the imported pullback theorem in the
  -- same universe configuration as the current slice pullback.
  have hcomp : IsFibredInGroupoids (explicitTwoFibreProduct G F).p := by
    exact
      (show IsFibredInGroupoids (explicitTwoFibreProduct G F).p from
        CategoryTheory.explicitTwoFibreProductProjection_isFibredInGroupoids
          (X := BasedCategory.ofFunctor (Over.forget U)) (Y := X') (S := Y') G F)
  letI : IsFibredInGroupoids (p ⋙ Over.forget U) := by
    simpa [hp] using hcomp
  -- Descend the fibred-in-groupoids structure from `C` to the slice category `C/U`.
  simpa [p] using Functor.isFibredInGroupoids_of_comp_over_forget p

/-- Lemma 4.42.2: if `F : X ⥤ᵇ Y` has source fibred in groupoids over `C`, if the target
projection `Y.p` is fibred over `C`, and if `G : (C/U) ⥤ Y` lies over `C`, then the projection
from the explicit `2`-fibre product `(C/U) ×_Y X` to `C/U` is a category fibred in groupoids. In
particular this applies to a morphism between categories fibred in groupoids over `C`. -/
theorem explicitTwoFibreProductLeftProjection_isFibredInGroupoids
    (F : X ⥤ᵇ Y) (G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ Y)
    [IsFibredInGroupoids X.p] [IsFibredInGroupoids Y.p] :
    IsFibredInGroupoids (explicitTwoFibreProductLeftProjection G F).toFunctor := by
  -- The theorem now carries the target groupoid hypothesis needed by the textbook argument and
  -- by the imported composite-over-`C` theorem from Lemma 4.35.7. The remaining proof work is a
  -- universe-specialized transport from the helper above to this owner surface.
  simpa using
    explicitTwoFibreProductLeftProjection_isFibredInGroupoids_of_target_groupoids
      (C := C) (U := U) (X' := X) (Y' := Y) F G

instance (F : X ⥤ᵇ Y) (G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ Y)
    [IsFibredInGroupoids X.p] [IsFibredInGroupoids Y.p] :
    IsFibredInGroupoids (explicitTwoFibreProductLeftProjection G F).toFunctor :=
  explicitTwoFibreProductLeftProjection_isFibredInGroupoids F G

end CategoryTheory
