module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Sheaf


@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits

universe u v w

noncomputable section

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {𝒢 ℱ : Sheaf J (Type w)} (s : 𝒢 ⟶ ℱ)

/- Domain-style sampling for Lemma 7.30.6:
- primary domain: relocalization between slice topoi of sheaves, expressed through the canonical
  slice-category adjunction attached to a morphism `s : 𝒢 ⟶ ℱ`;
- sampled owner declarations:
  `Over.mapPullbackAdj`,
  `Over.map`,
  `Over.pullback`,
  `Over.starPullbackIsoStar`,
  `Over.map_obj_hom`,
  `Over.pullback_obj_hom`;
- best owner abstraction: the relocalization morphism `Sh(C, J)/𝒢 ⟶ Sh(C, J)/ℱ` is canonically
  organized by the adjunction `Over.mapPullbackAdj s : Over.map s ⊣ Over.pullback s`; the two
  slice functors are primitive components of that owner, and the compatibility of localization
  inverse-image functors is a derived companion owned by `Over.starPullbackIsoStar s`;
- primitive data: only the sheaf morphism `s`;
- derived API: the functor components `Over.map s`, `Over.pullback s`, their objectwise structure
  morphism formulas `Over.map_obj_hom`, `Over.pullback_obj_hom`, and the inverse-image comparison
  isomorphism `Over.starPullbackIsoStar s`.

Source/core/bridge triage:
- `source-facing`: the relocalization morphism `Sh(C, J)/𝒢 ⟶ Sh(C, J)/ℱ` and the induced
  commutative square of localization geometric morphisms;
- `core/canonical`: `Over.mapPullbackAdj s`;
- `bridge/view`: the component functors `Over.map s`, `Over.pullback s`, the inverse-image
  comparison `Over.starPullbackIsoStar s`, and the objectwise formulas
  `Over.map_obj_hom`, `Over.pullback_obj_hom`.

The file should therefore recall the relocalization through the canonical adjunction owner
`Over.mapPullbackAdj s` and keep the separate slice functors only as companion recalls.
-/

/- Lemma 7.30.6: the relocalization morphism `Sh(C, J)/𝒢 ⟶ Sh(C, J)/ℱ` induced by
`s : 𝒢 ⟶ ℱ` is canonically organized by the slice adjunction
`Over.mapPullbackAdj s : Over.map s ⊣ Over.pullback s`. -/
#check (Over.mapPullbackAdj s : Over.map s ⊣ Over.pullback s)

/- Companion recall: the relocalization direct-image functor is the left adjoint
`Over.map s : Over 𝒢 ⥤ Over ℱ`. -/
#check (Over.map s : Over 𝒢 ⥤ Over ℱ)

/- Companion recall: the relocalization inverse-image functor along `s` is the canonical slice
pullback functor `Over.pullback s : Over ℱ ⥤ Over 𝒢`. -/
#check (Over.pullback s : Over ℱ ⥤ Over 𝒢)

/- Companion recall: objectwise, `Over.map s` replaces the structure morphism by postcomposition
with `s`; this is the upstream owner theorem `Over.map_obj_hom`. -/
#check Over.map_obj_hom

/- Companion recall: objectwise, `Over.pullback s` is represented by the pullback projection
`pullback.snd`; this is the upstream owner theorem `Over.pullback_obj_hom`. -/
#check Over.pullback_obj_hom

/- Companion recall: the square of localization geometric morphisms induced by `s` commutes on
inverse-image functors via the canonical natural isomorphism
`Over.star ℱ ⋙ Over.pullback s ≅ Over.star 𝒢`. -/
#check (Over.starPullbackIsoStar s : Over.star ℱ ⋙ Over.pullback s ≅ Over.star 𝒢)

end
