module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Tactic.Recall
public import stacks_project.Chap07.Lemma_7_21_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u v

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C)

/- Domain-style sampling for Definition 7.25.1:
- primary domain: localization of a site at an object and the induced localization morphism of
  topoi;
- sampled owner API:
  `GrothendieckTopology.over`,
  `GrothendieckTopology.instIsCocontinuousOverForgetOver`,
  `Functor.morphismOfTopoiInOfCocontinuous`,
  `Functor.morphismOfTopoiInOfCocontinuous_inverseImage`,
  `Functor.morphismOfTopoiInOfCocontinuous_pushforward`;
- source/core/bridge triage:
  `source-facing`: the localized site `(Over U, J.over U)` and the localization morphism
  `j_U : Sh(C/U, J.over U) ⟶ Sh(C, J)`;
  `core/canonical`: the owner construction `GrothendieckTopology.over` and the bundled morphism
  `(Over.forget U).morphismOfTopoiInOfCocontinuous (J.over U) J :
    MorphismOfTopoiIn J (J.over U)`;
  `bridge/view`: the simp theorems identifying the inverse-image and direct-image fields of that
  morphism with the canonical cocontinuous sheaf pullback and pushforward owners.

Primitive data are just the ambient site `J` and the object `U`. The localized topology `J.over U`
is source-facing data, while the cocontinuity of `Over.forget U` and the resulting geometric
morphism are already owned upstream. This file therefore targets the `core/canonical` layer:
direct recall of those owners, with the inverse-image and direct-image functors left as derived
API rather than separate local declarations.
-/

/- Definition 7.25.1: for a site `(C, J)` and an object `U : C`, the localization of the site at
`U` is the slice site `C/U` endowed with the induced Grothendieck topology. This notion is
canonically owned by `GrothendieckTopology.over`. -/
recall GrothendieckTopology.over

/- Companion specialization: applied to `(J, U)`, the localized site is `J.over U` on `Over U`.
-/
#check (J.over U : GrothendieckTopology (Over U))

/- Companion recall: the localization morphism
`j_U : Sh(C/U, J.over U) ⟶ Sh(C, J)` is the canonical morphism of topoi attached to the
cocontinuous localization functor `Over.forget U`. -/
recall Functor.morphismOfTopoiInOfCocontinuous

/- Companion specialization: for localization at `U`, the bundled morphism is the cocontinuous
site morphism induced by `Over.forget U`. -/
#check
  ((Over.forget U).morphismOfTopoiInOfCocontinuous (J.over U) J :
    MorphismOfTopoiIn J (J.over U))

/- Companion recall: the inverse-image functor of `j_U` is canonically the cocontinuous sheaf
pullback along `Over.forget U`. -/
recall Functor.morphismOfTopoiInOfCocontinuous_inverseImage

/- Companion recall: the direct-image functor of `j_U` is canonically the cocontinuous sheaf
pushforward along `Over.forget U`. -/
recall Functor.morphismOfTopoiInOfCocontinuous_pushforward

end
