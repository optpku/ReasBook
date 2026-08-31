module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Proposition_7_14_7
public import stacks_project.Chap07.Remark_7_13_6

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe w u₁ u₂ v₁ v₂

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

namespace CategoryTheory

/- Domain-style sampling for Remark 7.14.9:
- primary domain: quasi-continuous functors between sites, morphisms of sites, and exact
  inverse-image functors on set-valued sheaves;
- sampled owner API:
  `Functor.IsQuasiContinuousSiteFunctor`,
  `Functor.IsContinuous`,
  `IsMorphismOfSites`,
  `isMorphismOfSites_sheafPullback_exact`;
- source/core/bridge triage:
  `source-facing`: the Stacks remark that a quasi-morphism is a quasi-continuous functor whose
    inverse-image functor on sheaves is exact;
  `core/canonical`: `Functor.IsQuasiContinuousSiteFunctor u J K` for the extra source data and
    `IsMorphismOfSites J K u` for the exact inverse-image package;
  `bridge/view`: the theorems below upgrading quasi-continuity, terminal preservation, and
    pullback preservation to `IsMorphismOfSites`.

Primitive data here are only quasi-continuity and the finite-limit hypotheses from
Proposition 7.14.7. Exactness of `u.sheafPullback` is already derived API from
`IsMorphismOfSites` via `isMorphismOfSites_sheafPullback_exact`, so this file should not
introduce a second bundled owner class around those existing predicates. -/

/- Remark 7.14.9: in this project the Stacks phrase “quasi-morphism of sites” is expressed by the
existing owners `Functor.IsQuasiContinuousSiteFunctor u J K` and `IsMorphismOfSites J K u`,
rather than by a second wrapper class. The source-facing content of the remark is therefore the
bridge from quasi-continuity and the Proposition 7.14.7 hypotheses to `IsMorphismOfSites`. -/

-- Proof sketch: a quasi-continuous functor is continuous by Remark `7.13.6`. With the chosen
-- terminal-object preservation and pullback-preservation hypotheses, Proposition `7.14.7` gives a
-- morphism of sites. The exactness part of the quasi-morphism remark is then the canonical
-- consequence `isMorphismOfSites_sheafPullback_exact`.
/-- Canonical quasi-continuous analogue of Proposition 7.14.7: a quasi-continuous functor that
preserves terminal objects and pullbacks defines a morphism of sites. -/
theorem isMorphismOfSites_of_isQuasiContinuous_preservesTerminal_and_pullbacks
    (u : C ⥤ D) [HasPullbacks C] [HasPullbacks D]
    [Functor.IsQuasiContinuousSiteFunctor u J K] [HasTerminal C]
    [PreservesLimit (Functor.empty.{0} C) u]
    [PreservesLimitsOfShape WalkingCospan u] :
    IsMorphismOfSites J K u := by
  let _ : Functor.IsContinuous u J K := inferInstance
  exact isMorphismOfSites_of_preservesTerminal_and_pullbacks u

/-- Textbook-form bridge for Remark 7.14.9, using an explicit terminal object whose image is
terminal. -/
theorem isMorphismOfSites_of_isQuasiContinuous_terminal_and_pullbacks
    (u : C ⥤ D) [HasPullbacks C] [HasPullbacks D]
    [Functor.IsQuasiContinuousSiteFunctor u J K]
    (X : C) (hX : IsTerminal X) (huX : IsTerminal (u.obj X))
    [PreservesLimitsOfShape WalkingCospan u] :
    IsMorphismOfSites J K u := by
  let _ : Functor.IsContinuous u J K := inferInstance
  exact isMorphismOfSites_of_terminal_and_pullbacks u X hX huX

-- Proof sketch: first upgrade the quasi-continuous functor to a morphism of sites by the previous
-- bridge theorem, then apply the canonical exactness consequence
-- `isMorphismOfSites_sheafPullback_exact`.
/-- Remark 7.14.9, exactness clause: under the Proposition 7.14.7 finite-limit hypotheses, a
quasi-continuous functor has exact inverse-image functor on set-valued sheaves. -/
theorem sheafPullback_exact_of_isQuasiContinuous_preservesTerminal_and_pullbacks
    (u : C ⥤ D) [HasPullbacks C] [HasPullbacks D]
    [Functor.IsQuasiContinuousSiteFunctor u J K] [HasTerminal C]
    [PreservesLimit (Functor.empty.{0} C) u]
    [PreservesLimitsOfShape WalkingCospan u]
    [HasSheafify J (Type w)] [HasSheafify K (Type w)]
    [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension P]
    [PreservesFiniteLimits
      (u.op.lan : (Cᵒᵖ ⥤ Type w) ⥤ Dᵒᵖ ⥤ Type w)] :
    exactFunctor (Sheaf J (Type w)) (Sheaf K (Type w))
      (u.sheafPullback (Type w) J K) := by
  let _ : IsMorphismOfSites J K u :=
    isMorphismOfSites_of_isQuasiContinuous_preservesTerminal_and_pullbacks u
  exact isMorphismOfSites_sheafPullback_exact u

-- Proof sketch: the explicit terminal-object version first recovers a morphism of sites and then
-- reuses the canonical exactness theorem.
/-- Textbook-form exactness clause for Remark 7.14.9, using an explicit terminal object whose
image is terminal. -/
theorem sheafPullback_exact_of_isQuasiContinuous_terminal_and_pullbacks
    (u : C ⥤ D) [HasPullbacks C] [HasPullbacks D]
    [Functor.IsQuasiContinuousSiteFunctor u J K]
    (X : C) (hX : IsTerminal X) (huX : IsTerminal (u.obj X))
    [PreservesLimitsOfShape WalkingCospan u]
    [HasSheafify J (Type w)] [HasSheafify K (Type w)]
    [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension P]
    [PreservesFiniteLimits
      (u.op.lan : (Cᵒᵖ ⥤ Type w) ⥤ Dᵒᵖ ⥤ Type w)] :
    exactFunctor (Sheaf J (Type w)) (Sheaf K (Type w))
      (u.sheafPullback (Type w) J K) := by
  let _ : IsMorphismOfSites J K u :=
    isMorphismOfSites_of_isQuasiContinuous_terminal_and_pullbacks u X hX huX
  exact isMorphismOfSites_sheafPullback_exact u

end CategoryTheory

end
