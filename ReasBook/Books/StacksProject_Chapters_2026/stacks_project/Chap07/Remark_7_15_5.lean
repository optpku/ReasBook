module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Lemma_7_15_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-
Domain-style sampling for Remark 7.15.5:
- primary domain: morphisms of sites and the induced morphisms of topoi on sheaf categories;
- sampled owner API:
  `IsMorphismOfSites`,
  `Functor.morphismOfTopoiInOfContinuous`,
  `Functor.sheafPullback`,
  `isMorphismOfSites_sheafPullback_exact`;
- source/core/bridge triage:
  `source-facing`: the Stacks remark that a quasi-morphism of sites yields a morphism of topoi;
  `core/canonical`: `IsMorphismOfSites J K u` for the site-level owner and
    `u.morphismOfTopoiInOfContinuous J K` for the induced morphism of topoi;
  `bridge/view`: Remark 7.14.9 upgrades the quasi-morphism hypotheses to `IsMorphismOfSites`.

Primitive data here are only the site morphism structure and the standard sheafification/Kan
extension hypotheses needed to form the inverse-image functor on sheaves, together with the
left-exactness input required by the owner constructor `morphismOfTopoiInOfContinuous` in this
weak-sheafification setup. The exactness part of the quasi-morphism story is already carried by
the canonical owner `IsMorphismOfSites J K u`, so this file should remain a direct recall of the
induced morphism-of-topoi owner rather than introducing any parallel wrapper.
-/

section

variable (u : C ⥤ D)
variable [IsMorphismOfSites J K u]
variable [HasWeakSheafify K (Type w)]
variable [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension P]
variable [PreservesFiniteLimits (u.sheafPullback (Type w) J K)]

/- Remark 7.15.5: a quasi-morphism of sites `f : (D, K) ⟶ (C, J)` gives rise to a morphism of
topoi `Sh(K) ⟶ Sh(J)` exactly as in Lemma 7.15.2. In Lean this is the same canonical construction
`u.morphismOfTopoiInOfContinuous J K`; after the refinement of Remark 7.14.9, the exactness part
of a quasi-morphism is carried directly by the canonical owner `IsMorphismOfSites J K u` rather
than by a separate wrapper class. -/
#check (u.morphismOfTopoiInOfContinuous J K : MorphismOfTopoiIn J K)

end

end CategoryTheory
