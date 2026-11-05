module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Definition_7_14_1
public import stacks_project.Chap07.Definition_7_15_1_Topoi

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-
Domain-style sampling for Lemma 7.15.2:
- primary domain: the passage from a morphism of sites to the induced morphism of topoi on
  set-valued sheaves;
- sampled owner API:
  `IsMorphismOfSites`,
  `Functor.sheafPullback`,
  `Functor.sheafPullbackConstruction.preservesFiniteLimits`,
  `Functor.morphismOfTopoiInOfContinuous`,
  `MorphismOfTopoiIn`;
- source-facing layer: a morphism of sites `(D, K) ⟶ (C, J)`;
- core/canonical owner: `Functor.morphismOfTopoiInOfContinuous`;
- bridge/view: this file specializes that owner along the chapter class `IsMorphismOfSites`.

Primitive data are the functor `u` and the site-morphism structure. The needed left exactness of
`u.sheafPullback (Type w) J K` is derived canonically from `RepresentablyFlat u`, already carried
by `IsMorphismOfSites J K u`, via the owner-side finite-limit instance for `sheafPullback` under
the standard sheafification and Kan-extension hypotheses. This file should stay a thin bridge and
not introduce a parallel wrapper declaration.
-/

section

variable (u : C ⥤ D) [IsMorphismOfSites J K u]
variable [HasSheafify J (Type w)] [HasSheafify K (Type w)]
variable [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension P]
variable [PreservesFiniteLimits (u.op.lan : (Cᵒᵖ ⥤ Type w) ⥤ Dᵒᵖ ⥤ Type w)]

/- Lemma 7.15.2: if `u : C ⥤ D` presents a morphism of sites `(D, K) → (C, J)`, then the
associated inverse-image functor `u_s` and direct-image functor `u^s` define the canonical
morphism of topoi `Sh(K) ⟶ Sh(J)`. In Lean this is exactly the owner
`u.morphismOfTopoiInOfContinuous J K`, viewed in the source-facing type `MorphismOfTopoiIn J K`.
-/
#check Functor.morphismOfTopoiInOfContinuous

end

end CategoryTheory
