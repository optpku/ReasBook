module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Definition_7_25_1
public import stacks_project.Chap07.Lemma_7_25_4

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology
open scoped SheafifiedRepresentable

universe w u v

noncomputable section

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable (U : C)

/- Domain-style sampling for Lemma 7.25.5:
- primary domain: localization lower shriek on sheaves, viewed through the slice-category
  description over the sheafified representable `h_U^#`;
- sampled owner API:
  `GrothendieckTopology.representableLocalizationComparison`,
  `GrothendieckTopology.representableLocalizationComparison_isEquivalence`,
  `GrothendieckTopology.representableLocalizationComparison_forget`,
  `CategoryTheory.Functor.sheafPullback`,
  `Over.preservesLimitsOfShape_forget_of_isConnected`,
  `Functor.PreservesMonomorphisms`;
- source-facing layer: the localization lower shriek `j_{U!}`;
- core/canonical owner: `CategoryTheory.Functor.sheafPullback`, specialized to `Over.forget U`;
- bridge/view: `J.representableLocalizationComparison_forget U` identifies this owner with the
  composite of the equivalence `Sh(C/U) ≌ Sh(C)/h_U^#` and the slice forgetful functor.

Primitive data are the site `(C, J)` and the localization object `U`; the lower shriek itself is
already the canonical owner `(Over.forget U).sheafPullback ...`. Connected-limit,
finite-connected-limit, pullback, equalizer, and monomorphism preservation are derived API of
that owner. The proof below temporarily invokes the comparison equivalence from Lemma `7.25.4`,
with its sheafification and Kan-extension inputs supplied locally by canonical instance search,
rather than exposing those proof-route hypotheses in the public section context.
-/

-- Proof sketch: identify `j_{U!}` with the composite of the equivalence from Lemma `7.25.4`
-- between `Sh(C/U)` and the slice category `Sh(C)/h_U^#` and the forgetful functor from that
-- slice category to `Sh(C)`. Equivalences preserve all limits, and the forgetful functor from an
-- over category preserves connected limits, so the source statement follows for finite connected
-- shapes in particular.
/-- Lemma 7.25.5: for a site `(C, J)` and an object `U : C`, the localization lower shriek
functor `j_{U!} : Sh(C/U) ⥤ Sh(C)`, realized canonically as
`(Over.forget U).sheafPullback (Type (max u v)) (J.over U) J`, commutes with finite connected
limits. -/
theorem localizationLowerShriek_preserves_finite_connected_limits
    (I : Type w) [SmallCategory I] [FinCategory I] [IsConnected I] :
    PreservesLimitsOfShape I ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J) := by
  letI : HasWeakSheafify J (Type (max u v)) := inferInstance
  letI : HasWeakSheafify (J.over U) (Type (max u v)) := inferInstance
  letI : ∀ G : (Over U)ᵒᵖ ⥤ Type (max u v), (Over.forget U).op.HasLeftKanExtension G :=
    fun G ↦ inferInstance
  letI : Functor.IsEquivalence (J.representableLocalizationComparison U) :=
    J.representableLocalizationComparison_isEquivalence U
  simpa using
    (inferInstance :
      PreservesLimitsOfShape I
        (J.representableLocalizationComparison U ⋙ Over.forget h[U]^#[J]))

-- Proof sketch: apply the connected-limit statement to the walking cospan, whose limits are
-- pullbacks.
/-- The localization lower shriek preserves fibre products. -/
theorem localizationLowerShriek_preserves_pullbacks
    :
    PreservesLimitsOfShape WalkingCospan
      ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J) :=
  localizationLowerShriek_preserves_finite_connected_limits U WalkingCospan

-- Proof sketch: apply the connected-limit statement to the walking parallel pair, whose
-- limits are equalizers.
/-- The localization lower shriek preserves equalizers. -/
theorem localizationLowerShriek_preserves_equalizers
    :
    PreservesLimitsOfShape WalkingParallelPair
      ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J) :=
  localizationLowerShriek_preserves_finite_connected_limits U WalkingParallelPair

-- Proof sketch: in a category with pullbacks, any functor preserving pullbacks preserves
-- monomorphisms. Apply this to the canonical lower-shriek owner and the previous theorem.
/-- The localization lower shriek sends monomorphisms of sheaves on `C/U` to monomorphisms of
sheaves on `C`. -/
instance localizationLowerShriek_preservesMonomorphisms
    :
    ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).PreservesMonomorphisms := by
  letI :
      PreservesLimitsOfShape WalkingCospan
        ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J) :=
    localizationLowerShriek_preserves_pullbacks U
  infer_instance

end
