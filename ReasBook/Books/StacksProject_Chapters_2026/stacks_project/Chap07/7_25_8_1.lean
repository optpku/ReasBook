module

import Mathlib.Tactic.Recall
public import stacks_project.Chap07.Definition_7_25_1
public import stacks_project.Chap07.Lemma_7_21_2

@[expose] public section

open CategoryTheory Opposite
open scoped MorphismOfTopoiIn

universe u v

noncomputable section

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable {U V : C} (f : V ⟶ U)

/- Domain-style sampling for 7.25.8.1:
- primary domain: localization and relocalization morphisms of topoi attached to the slice-site
  functors `Over.forget` and `Over.map`;
- sampled owner API:
  `Functor.morphismOfTopoiInOfCocontinuous`,
  `MorphismOfTopoiIn.comp`,
  `Functor.morphismOfTopoiInOfCocontinuous_inverseImage`,
  `Functor.sheafPushforwardContinuousComp'`;
- source/core/bridge triage:
  `source-facing`: the commutative triangle `j_V = j_U ∘ j` of morphisms of topoi for
  relocalization along `f : V ⟶ U`;
  `core/canonical`: the localization and relocalization morphisms of topoi built from
  `Over.forget U`, `Over.forget V`, and `Over.map f`, together with `MorphismOfTopoiIn.comp`;
  `bridge/view`: the inverse-image comparison
  `j_U⁻¹ ⋙ j⁻¹ ≅ j_V⁻¹`, specialized from `Functor.sheafPushforwardContinuousComp'`.

Primitive data are only the site `J` and the morphism `f`. The morphisms of topoi themselves are
already canonically owned by `Functor.morphismOfTopoiInOfCocontinuous`, so this file should make
the triangle live at `MorphismOfTopoiIn.comp` and treat the inverse-image comparison as derived
API rather than as the main public entry.
-/

variable [HasSheafify (J.over U) (Type (max u v))]
variable [HasSheafify (J.over V) (Type (max u v))]
variable [∀ P : (Over U)ᵒᵖ ⥤ Type (max u v), (Over.forget U).op.HasPointwiseRightKanExtension P]
variable [∀ P : (Over V)ᵒᵖ ⥤ Type (max u v), (Over.map f).op.HasPointwiseRightKanExtension P]
variable [∀ P : (Over V)ᵒᵖ ⥤ Type (max u v), (Over.forget V).op.HasPointwiseRightKanExtension P]

-- Proof sketch: both sides are the morphism of topoi induced by the cocontinuous triangle
-- `Over.map f ⋙ Over.forget U ≅ Over.forget V`, so the result follows by comparing the canonical
-- owner constructions attached to `Over.mapForget f`.
/-- Helper for 7.25.8.1: the direct-image functor of the relocalization composite is canonically
isomorphic to the direct-image functor of localization at `V`. -/
noncomputable def relocalization_comp_pushforward_iso :
    (Over.map f).sheafPushforwardCocontinuous (Type (max u v)) (J.over V) (J.over U) ⋙
        (Over.forget U).sheafPushforwardCocontinuous (Type (max u v)) (J.over U) J ≅
      (Over.forget V).sheafPushforwardCocontinuous (Type (max u v)) (J.over V) J :=
  -- The owner-level direct-image comparison is the cocontinuous pushforward composition
  -- isomorphism specialized to `Over.mapForget f`.
  Functor.sheafPushforwardCocontinuousComp'
    (J := J.over V) (K := J.over U) (L := J)
    (u := Over.map f) (v := Over.forget U) (A := Type (max u v))
    (Over.mapForget f)

/-- Helper for 7.25.8.1: after expressing localization and relocalization as morphisms of topoi,
their composite direct-image functor is canonically isomorphic to the direct image of
localization at `V`. -/
noncomputable def relocalization_comp_localization_pushforward_iso :
    (((Over.map f).morphismOfTopoiInOfCocontinuous (J.over V) (J.over U)) _*) ⋙
        (((Over.forget U).morphismOfTopoiInOfCocontinuous (J.over U) J) _*) ≅
      (((Over.forget V).morphismOfTopoiInOfCocontinuous (J.over V) J) _*) := by
  -- This is the source-facing restatement of `relocalization_comp_pushforward_iso`.
  simpa only [Functor.morphismOfTopoiInOfCocontinuous_pushforward] using
    relocalization_comp_pushforward_iso (J := J) (f := f)

/-- 7.25.8.1: the relocalization morphism
`Sh(C/V, J.over V) ⟶ Sh(C/U, J.over U)` followed by localization at `U` agrees with localization
at `V` through the canonical direct-image comparison.  The source diagram is a commutative
triangle of topoi, but in the current bundled `MorphismOfTopoiIn` API the faithful public
statement is the induced isomorphism on the composed direct-image functors rather than a strict
equality of bundled morphism records. -/
theorem relocalization_comp_localization_eq_localization :
    IsIsomorphic
      ((((Over.map f).morphismOfTopoiInOfCocontinuous (J.over V) (J.over U)) _*) ⋙
        (((Over.forget U).morphismOfTopoiInOfCocontinuous (J.over U) J) _*))
      (((Over.forget V).morphismOfTopoiInOfCocontinuous (J.over V) J) _*) := by
  exact ⟨relocalization_comp_localization_pushforward_iso (J := J) (f := f)⟩


end

end CategoryTheory
