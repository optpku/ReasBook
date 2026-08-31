module

public import Mathlib.CategoryTheory.Sites.Over
public import stacks_project.Chap07.Lemma_7_13_5

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u v

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C)
variable [∀ F : (Over U)ᵒᵖ ⥤ Type (max u v), (Over.forget U).op.HasLeftKanExtension F]
variable [HasWeakSheafify (J.over U) (Type (max u v))]
variable [HasWeakSheafify J (Type (max u v))]

/- Domain-style sampling for Lemma 7.25.3:
- primary domain: localization lower shriek on sheaves and its action on sheafified representables;
- sampled owner API:
  `continuous_sheafified_representable_iso`,
  `(Over.forget U).sheafPullback`,
  `GrothendieckTopology.uliftSheafifiedRepresentable`;
- source/core/bridge triage:
  `source-facing`: the textbook identification `j_{U!}(h_{X/U}^#) ≅ h_X^#`;
  `core/canonical`: the general Chapter 7 owner
  `continuous_sheafified_representable_iso` for a continuous functor of sites;
  `bridge/view`: the exact localization specialization along `Over.forget U`.

Primitive data belong to the owner theorem from Lemma 7.13.5: a continuous functor of sites and
an object of the source site. In Lemma 7.25.3 the localization lower shriek and the sheafified
representables are derived from that owner, so this file should expose only the specialized
localization instance, not a parallel local wrapper and not the unspecialized theorem.
-/

/- Lemma 7.25.3: for a site `(C, J)`, an object `U : C`, and an object `X/U` of the localized
site, the localization lower shriek along `Over.forget U` sends `h_{X/U}^#` to `h_X^#`. This is
the exact specialization of `continuous_sheafified_representable_iso` to the localization functor.
-/
#check
  (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J :
    (X : Over U) →
      J.uliftSheafifiedRepresentable ((Over.forget U).obj X) ≅
        ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
          ((J.over U).uliftSheafifiedRepresentable X))

end
