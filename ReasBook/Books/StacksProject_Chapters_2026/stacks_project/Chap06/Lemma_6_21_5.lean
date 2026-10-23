module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Topology.Sheaves.Stalks


@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits TopCat
open TopCat.Presheaf
open scoped TopCat

noncomputable section

universe w v u

namespace TopCat

/- Source-facing notation for inverse image on sheaves. The ambient coefficient category is
inferred from the expected functor type. -/
scoped notation:max f:max "⁻¹" => TopCat.Sheaf.pullback _ f

end TopCat

namespace TopCat.Sheaf

/- Domain-style sampling for Lemma 6.21.5:
- primary domain: stalkwise comparison for inverse-image sheaves on topological spaces;
- sampled owner declarations:
  `TopCat.Presheaf.stalkPullbackIso`,
  `TopCat.Sheaf.pullback`,
  `TopCat.Sheaf.pullbackIso`,
  `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`;
- owner abstraction: the core upstream owner is the presheaf-level stalk comparison
  `TopCat.Presheaf.stalkPullbackIso`; this file supplies the sheaf-level bridge owner obtained by
  composing that canonical isomorphism with the stalkwise sheafification comparison for pullback
  and the sheaf pullback comparison `TopCat.Sheaf.pullbackIso`;
- primitive data: a continuous map `f : X ⟶ Y`, a sheaf `𝒢 : Y.Sheaf A`, and a point `x : X`;
- derived API: only the comparison from the stalk of the presheaf pullback to the stalk of the
  sheaf pullback.

Source/core/bridge triage:
- `source-facing`: the Stacks-style statement that the stalk of `f⁻¹𝒢` at `x` is the stalk of
  `𝒢` at `f x`;
- `core/canonical`: `TopCat.Presheaf.stalkPullbackIso`;
- `bridge/view`: the stalkwise comparison between the presheaf pullback and the sheaf pullback. -/

variable {A : Type u} [Category.{w} A] {FA : A → A → Type v} {CA : A → Type w}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w} A FA]
variable [HasColimits A] [HasLimits A]
variable [PreservesLimits (CategoryTheory.forget A)]
variable [PreservesFilteredColimits (CategoryTheory.forget A)]
variable [(CategoryTheory.forget A).ReflectsIsomorphisms]

public noncomputable abbrev pullbackSheafifyStalkIso
    {X Y : TopCat.{w}} (f : X ⟶ Y) (𝒢 : Y.Sheaf A) (x : X) :
    ((TopCat.Presheaf.pullback A f).obj 𝒢.presheaf).stalk x ≅
      ((pullback A f).obj 𝒢).presheaf.stalk x := by
  let F := ((forget A Y ⋙ TopCat.Presheaf.pullback A f).obj 𝒢)
  let h : IsIso
      ((stalkFunctor A x).map
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X) F)) := by
    simpa [F] using stalkFunctor_map_unit_toSheafify_isIso x A F
  exact
    @asIso _ _ _ _
      ((stalkFunctor A x).map
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X) F)) h ≪≫
    ((stalkFunctor A x).mapIso ((forget A X).mapIso ((pullbackIso A f).app 𝒢))).symm

/-- Lemma 6.21.5: for a continuous map `f : X ⟶ Y`, a sheaf `𝒢` on `Y`, and a point `x : X`,
the canonical map on stalks identifies the stalk of `𝒢` at `f x` with the stalk of the inverse-
image sheaf at `x`. For the textbook statement take `A := Type u`; the same construction works for
any ambient category satisfying the hypotheses needed to form `TopCat.Sheaf.pullback`. -/
noncomputable abbrev stalkPullbackIso
    {X Y : TopCat.{w}} (f : X ⟶ Y) (𝒢 : Y.Sheaf A) (x : X) :
    𝒢.presheaf.stalk (f x) ≅ ((f⁻¹).obj 𝒢).presheaf.stalk x :=
  TopCat.Presheaf.stalkPullbackIso A f 𝒢.presheaf x ≪≫ pullbackSheafifyStalkIso f 𝒢 x

-- Proof sketch: unfold `stalkPullbackIso`; it is defined as the composite of the presheaf-level
-- stalk pullback isomorphism with the stalkwise comparison between presheaf pullback and sheaf
-- pullback.
/-- Unfolding `stalkPullbackIso` identifies it with the composite of the canonical presheaf stalk
comparison and the pullback-sheafification stalk comparison. -/
theorem stalkPullbackIso_def
    {X Y : TopCat.{w}} (f : X ⟶ Y) (𝒢 : Y.Sheaf A) (x : X) :
    stalkPullbackIso f 𝒢 x =
      TopCat.Presheaf.stalkPullbackIso A f 𝒢.presheaf x ≪≫ pullbackSheafifyStalkIso f 𝒢 x := by
  -- Unfold the abbreviation: the sheaf-level comparison is defined to be this composite.
  rfl

end TopCat.Sheaf
