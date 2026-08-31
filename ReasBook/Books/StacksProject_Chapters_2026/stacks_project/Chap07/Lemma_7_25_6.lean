module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Lemma_7_25_4

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.GrothendieckTopology
open scoped SheafifiedRepresentable

universe u v

noncomputable section

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable (U : C)
variable [∀ G : (Over U)ᵒᵖ ⥤ Type (max u v), (Over.forget U).op.HasLeftKanExtension G]
variable [HasWeakSheafify J (Type (max u v))]

/- Domain-style sampling for Lemma 7.25.6:
- primary domain: localization lower shriek on sheaves, compared with the slice category over the
  sheafified representable `h_U^#`;
- sampled owner API:
  `GrothendieckTopology.representableLocalizationComparison`,
  `GrothendieckTopology.representableLocalizationComparison_isEquivalence`,
  `CategoryTheory.Functor.ReflectsMonomorphisms`,
  `CategoryTheory.Functor.ReflectsEpimorphisms`;
- source-facing layer: the localization lower shriek `j_{U!}`, realized canonically as
  `(Over.forget U).sheafPullback (Type (max u v)) (J.over U) J`;
- core/canonical owner: the equivalence `J.representableLocalizationComparison U` from sheaves on
  `(C/U, J.over U)` to the slice category `Sh(C, J) / h_U^#`;
- bridge/view: composing that equivalence with the slice forgetful functor recovers `j_{U!}`,
  so reflection of monomorphisms and epimorphisms is derived API of the owner comparison rather
  than primitive data of a separate localization wrapper.

Primitive data are the site `(C, J)`, the localization object `U`, and the canonical lower-shriek
functor already owned by `Functor.sheafPullback`. Reflection of injections and surjections is
derived from the owner-level equivalence together with the standard slice forgetful functor, so
this file should reuse that comparison directly instead of introducing parallel local copies.
-/

-- Proof sketch: by Lemma `7.25.4`, `j_{U!}` identifies with the composite of the comparison
-- equivalence `Sh(C/U) ≌ Sh(C)/h_U^#` and the slice forgetful functor to `Sh(C)`. Both functors
-- are faithful, hence both reflect monomorphisms, so the composite does as well.
/-- Lemma 7.25.6 (1): for a site `(C, J)` and an object `U : C`, the localization lower shriek
functor `j_{U!}` reflects monomorphisms; equivalently, it reflects injections of set-valued
sheaves. -/
instance localizationLowerShriek_reflectsMonomorphisms
    :
    ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).ReflectsMonomorphisms := by
  let comparison := J.representableLocalizationComparison U
  haveI : comparison.IsEquivalence := J.representableLocalizationComparison_isEquivalence U
  simpa [comparison] using
    (inferInstance :
      (comparison ⋙ Over.forget h[U]^#[J]).ReflectsMonomorphisms)

-- Proof sketch: the same comparison identifies `j_{U!}` with a composite of faithful functors,
-- so epimorphisms are reflected for the same owner-level reason.
/-- Lemma 7.25.6 (2): for a site `(C, J)` and an object `U : C`, the localization lower shriek
functor `j_{U!}` reflects epimorphisms; equivalently, it reflects surjections of set-valued
sheaves. -/
instance localizationLowerShriek_reflectsEpimorphisms
    :
    ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).ReflectsEpimorphisms := by
  let comparison := J.representableLocalizationComparison U
  haveI : comparison.IsEquivalence := J.representableLocalizationComparison_isEquivalence U
  simpa [comparison] using
    (inferInstance :
      (comparison ⋙ Over.forget h[U]^#[J]).ReflectsEpimorphisms)

end
