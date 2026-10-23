module

public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.Topology.Sheaves.Stalks
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain-style sampling for Lemma 6.13.1:
- primary domain: stalks of presheaves as neighbourhood colimits, and comparison with
  postcomposition by a filtered-colimit-preserving functor.
- inspected owner declarations:
  `TopCat.Presheaf.stalkFunctor`,
  `TopCat.Presheaf.stalk`,
  `CategoryTheory.Limits.preservesColimitNatIso`,
  `CategoryTheory.GrothendieckTopology.Point.presheafFiberCompIso`.
- owner abstraction: the source-facing owner in this file is the weaker
  `filteredStalkFunctor`, matching mathlib’s canonical `TopCat.Presheaf.stalkFunctor`
  once full colimits are available.
- primitive data: the neighbourhood diagram `((OpenNhds.inclusion x).op ⋙ ℱ)`.
- derived API: the object-level `filteredStalk`, the functor-level comparison isomorphism with
  postcomposition by `F`, its objectwise component `stalkCompIso`, and the bridge back to the
  canonical mathlib stalk under `[HasColimits C]`.

Source/core/bridge triage:
- `source-facing`: the weaker filtered-colimit stalk functor `filteredStalkFunctor` needed under
  `[HasFilteredColimits C]`.
- `core/canonical`: `TopCat.Presheaf.stalkFunctor` and `TopCat.Presheaf.stalk`.
- `bridge/view`: `filteredStalkCompIso`, its component `stalkCompIso`, and
  `filteredStalk_eq_stalk`.

The refinement keeps the weaker source-facing stalk functor because mathlib’s canonical stalk owner
currently lives under the stronger `[HasColimits C]` hypothesis, then bridges back to that owner
when the stronger hypothesis is available. -/

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite TopCat
open TopCat.Presheaf TopologicalSpace

universe v w

noncomputable section

section

variable {C : Type v} [Category.{w} C]
variable [HasFilteredColimits C]
variable {X : TopCat.{w}} (x : X)

/-- Lemma 6.13.1 (1): under `[HasFilteredColimits C]`, the assignment `ℱ ↦ ℱ_x` is already a
functor, obtained by taking the filtered colimit over open neighborhoods of `x`. -/
noncomputable abbrev filteredStalkFunctor : X.Presheaf C ⥤ C :=
  (whiskeringLeft (OpenNhds x)ᵒᵖ (Opens X)ᵒᵖ C).obj (OpenNhds.inclusion x).op ⋙ colim

/-- The stalk of a `C`-valued presheaf at `x`, computed as the value of
`filteredStalkFunctor x`. -/
noncomputable abbrev filteredStalk (ℱ : X.Presheaf C) : C :=
  (filteredStalkFunctor x).obj ℱ

/-- Evaluating `filteredStalkFunctor x` on a presheaf computes `filteredStalk x`. -/
-- Proof sketch: this is definitional, since `filteredStalk` was introduced as the object part of
-- `filteredStalkFunctor`.
@[simp] theorem filteredStalkFunctor_obj (ℱ : X.Presheaf C) :
    (filteredStalkFunctor x).obj ℱ = filteredStalk x ℱ := by
  -- `filteredStalk` was introduced as the object part of `filteredStalkFunctor`.
  rfl

-- Proof sketch: unfold `filteredStalkFunctor`; this is exactly the neighborhood-diagram colimit
-- functor used in its definition.
/-- Unfolding `filteredStalkFunctor` identifies it with the neighborhood-colimit functor over the
point `x`. -/
theorem filteredStalkFunctor_def :
    filteredStalkFunctor x =
      (whiskeringLeft (OpenNhds x)ᵒᵖ (Opens X)ᵒᵖ C).obj (OpenNhds.inclusion x).op ⋙ colim := by
  -- `filteredStalkFunctor` is defined to be this neighborhood-diagram colimit functor.
  rfl

-- Proof sketch: under `[HasColimits C]`, both functors are given by the same neighborhood-colimit
-- construction, so they agree functorially.
/-- Companion bridge: with all colimits available, `filteredStalkFunctor` is the canonical
mathlib stalk functor. -/
@[simp] theorem filteredStalkFunctor_eq_stalkFunctor [HasColimits C] :
    filteredStalkFunctor x = stalkFunctor C x := by
  -- Both functors are the same neighborhood-colimit construction.
  rfl

variable (F : C ⥤ Type w)
variable [PreservesFilteredColimits F]

/-- Lemma 6.13.1 (2): applying `F` after the filtered-colimit stalk functor is naturally
isomorphic
to taking stalks after postcomposing presheaves with `F`. -/
noncomputable def filteredStalkCompIso :
    filteredStalkFunctor x ⋙ F ≅
      (whiskeringRight (Opens X)ᵒᵖ C (Type w)).obj F ⋙ stalkFunctor (Type w) x :=
  isoWhiskerLeft
    ((whiskeringLeft (OpenNhds x)ᵒᵖ (Opens X)ᵒᵖ C).obj (OpenNhds.inclusion x).op)
    (preservesColimitNatIso F)

-- Proof sketch: unfold `filteredStalkCompIso`; it is defined to be the whiskering of
-- `preservesColimitNatIso F` along the neighborhood diagram functor.
/-- Unfolding `filteredStalkCompIso` gives the whiskered colimit-comparison isomorphism attached
to `F`. -/
theorem filteredStalkCompIso_def :
    filteredStalkCompIso x F =
      isoWhiskerLeft
        ((whiskeringLeft (OpenNhds x)ᵒᵖ (Opens X)ᵒᵖ C).obj (OpenNhds.inclusion x).op)
        (preservesColimitNatIso F) := by
  -- `filteredStalkCompIso` is defined by whiskering `preservesColimitNatIso`.
  rfl

/-- The objectwise component of `filteredStalkCompIso`. -/
noncomputable abbrev stalkCompIso (ℱ : X.Presheaf C) :
    F.obj (filteredStalk x ℱ) ≅ stalk (ℱ ⋙ F) x :=
  (filteredStalkCompIso x F).app ℱ

/-- The component of `filteredStalkCompIso x F` at a presheaf is `stalkCompIso x F`. -/
-- Proof sketch: `stalkCompIso` is defined to be the component of the natural isomorphism
-- `filteredStalkCompIso`.
@[simp] theorem filteredStalkCompIso_app (ℱ : X.Presheaf C) :
    (filteredStalkCompIso x F).app ℱ = stalkCompIso x F ℱ := by
  -- `stalkCompIso` is defined as this component.
  rfl

-- Proof sketch: pass from the component isomorphism to its forward morphism on the chosen
-- presheaf.
/-- The forward morphism of `filteredStalkCompIso x F` at `ℱ` is the forward map of
`stalkCompIso x F ℱ`. -/
@[simp] theorem filteredStalkCompIso_hom_app (ℱ : X.Presheaf C) :
    (filteredStalkCompIso x F).hom.app ℱ = (stalkCompIso x F ℱ).hom := by
  -- Take the forward morphism of the component isomorphism.
  rfl

-- Proof sketch: likewise, the inverse component of the natural isomorphism agrees with the
-- inverse of the objectwise comparison isomorphism.
/-- The inverse morphism of `filteredStalkCompIso x F` at `ℱ` is the inverse map of
`stalkCompIso x F ℱ`. -/
@[simp] theorem filteredStalkCompIso_inv_app (ℱ : X.Presheaf C) :
    (filteredStalkCompIso x F).inv.app ℱ = (stalkCompIso x F ℱ).inv := by
  -- Take the inverse morphism of the component isomorphism.
  rfl

/-- Under the stronger `[HasColimits C]` hypothesis, `filteredStalk` is the canonical mathlib
stalk. -/
@[simp] theorem filteredStalk_eq_stalk [HasColimits C] (ℱ : X.Presheaf C) :
    filteredStalk x ℱ = ℱ.stalk x :=
  let _ : HasFilteredColimits C := hasFilteredColimitsOfSize_of_hasColimitsOfSize
  rfl

end
