module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Sites.Pullback

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe w u₁ u₂ v₁ v₂

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D)

/- Domain-style sampling for Definition 7.14.1:
- primary domain: Grothendieck topologies, continuous functors of sites, and exact inverse-image
  functors on set-valued sheaves;
- sampled owner API:
  `Functor.IsContinuous`,
  `RepresentablyFlat`,
  `Functor.sheafPullback`,
  `Functor.sheafAdjunctionContinuous`;
- source/core/bridge triage:
  `source-facing`: the Stacks notion of a morphism of sites `(D, K) → (C, J)`;
  `core/canonical`: the owner predicates `Functor.IsContinuous u J K` and
  `RepresentablyFlat u`;
  `bridge/view`: the chapter class `IsMorphismOfSites J K u`.

Primitive data are exactly continuity and representable flatness. Exactness of the induced inverse
image on sheaves is derived API, so the public consequence below is stated from the source-facing
owner `IsMorphismOfSites`, which supplies the canonical owners by inheritance. Cover preservation
is a separate stronger site-level owner and is not part of `IsMorphismOfSites`.
-/

/-- Definition 7.14.1: a morphism of sites `(D, K) → (C, J)` is represented by a continuous
functor `u : C ⥤ D` whose inverse-image functor `u_s` on set-valued sheaves is exact. Mathlib's
canonical owner for that exactness criterion is `RepresentablyFlat u`, so we store continuity and
representable flatness as primitive data and derive exactness of `u.sheafPullback` from the
canonical pullback API. -/
class IsMorphismOfSites
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : C ⥤ D) : Prop
    extends u.IsContinuous J K, RepresentablyFlat u

/-- A continuous representably flat functor defines a morphism of sites. This is the canonical
mathlib criterion guaranteeing exactness of the inverse-image functor on sheaves. -/
instance isMorphismOfSites_of_isContinuous_representablyFlat
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (u : C ⥤ D) [u.IsContinuous J K] [RepresentablyFlat u] :
    IsMorphismOfSites J K u where
  toIsContinuous := inferInstance
  toRepresentablyFlat := inferInstance

/-- For a morphism of sites, the induced inverse-image functor on set-valued sheaves is exact
once the standard sheafification and Kan-extension hypotheses needed to construct it are
available. -/
theorem isMorphismOfSites_sheafPullback_exact
    [IsMorphismOfSites J K u]
    [HasSheafify J (Type w)]
    [HasSheafify K (Type w)]
    [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension P]
    [PreservesFiniteLimits
      (u.op.lan : (Cᵒᵖ ⥤ Type w) ⥤ Dᵒᵖ ⥤ Type w)] :
    exactFunctor (Sheaf J (Type w)) (Sheaf K (Type w))
      (u.sheafPullback (Type w) J K) := by
  let _ : (u.sheafPullback (Type w) J K).IsLeftAdjoint :=
    (u.sheafAdjunctionContinuous (Type w) J K).isLeftAdjoint
  simp only [exactFunctor_iff]
  exact ⟨inferInstance, inferInstance⟩

end
