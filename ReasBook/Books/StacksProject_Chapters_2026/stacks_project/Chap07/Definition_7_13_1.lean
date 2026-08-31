module

public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import stacks_project.Chap07.Definition_7_6_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

namespace Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/- Domain-style sampling for Definition 7.13.1:
- primary domain: continuous functors between sites presented by precoverages;
- sampled owner API:
  `CategoryTheory.Precoverage.PullbacksPreservedBy`,
  `CategoryTheory.Functor.IsContinuous`,
  `CategoryTheory.Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy`,
  `CategoryTheory.CoverPreserving`;
- source/core/bridge triage:
  `source-facing`: the Stacks Project continuity condition at the precoverage level;
  `core/canonical`: `Precoverage.PullbacksPreservedBy` and `Functor.IsContinuous`;
  `bridge/view`: the relation `J ≤ K.comap u` and the passage to `Precoverage.toGrothendieck`.

Primitive data are the cover-preservation relation `J ≤ K.comap u` and pullback preservation along
members of covering families. Under the source pullback hypothesis, these data induce the
canonical owner `J.PullbacksPreservedBy u`; the resulting Grothendieck-topology continuity
statement and the cover-preservation result after passing to topologies are derived API.
-/

/-- Definition 7.13.1: for sites presented by covering families, a functor is continuous in the
Stacks Project sense if it sends covering families to covering families and the canonical
comparison map from the image of an induced fiber product to the induced fiber product of the
images is an isomorphism. -/
class IsContinuousSiteFunctor
    (u : C ⥤ D) (J : Precoverage C) (K : Precoverage D) : Prop where
  /-- Covering families are preserved, expressed via the canonical precoverage comap. -/
  toLeComap : J ≤ K.comap u
  /-- Pullbacks along arrows of covering families are preserved. Equivalently, the canonical
  pullback-comparison map into the induced image pullback is an isomorphism whenever the source
  pullback exists. -/
  preservesPullback
    {V : C} {R : Presieve V} (hR : R ∈ J V) {Y : C} {i : Y ⟶ V} (hi : R i)
    {T : C} (f : T ⟶ V) [HasPullback f i] :
    PreservesLimit (cospan f i) u

variable {J : Precoverage C} {K : Precoverage D} {u : C ⥤ D}

section

variable [J.HasPullbacks]

/-- Under the ambient pullback hypothesis on the source site, the Stacks Project continuity data
recover the canonical owner expressing preservation of pairwise pullbacks of covering families. -/
theorem IsContinuousSiteFunctor.pullbacksPreservedBy (h : IsContinuousSiteFunctor u J K) :
    J.PullbacksPreservedBy u := by
  refine ⟨?_⟩
  intro X R hR
  refine { preservesLimit := ?_ }
  intro Y Z f i hf hi
  let _ : HasPullback f i := (J.hasPairwisePullbacks_of_mem hR).has_pullbacks hf hi
  exact h.preservesPullback hR hi f

end

section

variable [J.HasIsos] [J.IsStableUnderBaseChange] [J.IsStableUnderComposition]
variable [J.HasPullbacks]

/-- A continuous site functor in the Stacks Project sense is cover-preserving for the associated
Grothendieck topologies. -/
theorem IsContinuousSiteFunctor.coverPreserving (h : IsContinuousSiteFunctor u J K) :
    CoverPreserving J.toGrothendieck K.toGrothendieck u where
  cover_preserve {U} {S} hS := by
    rw [Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hS
    rcases hS with ⟨R, hR, hRS⟩
    have hgen : Sieve.generate R ≤ S := (Sieve.giGenerate.gc R S).2 hRS
    apply K.toGrothendieck.superset_covering
      (Sieve.functorPushforward_monotone u U hgen)
    simpa [Sieve.generate_map_eq_functorPushforward] using
      Precoverage.generate_mem_toGrothendieck
        (show R.map u ∈ K (u.obj U) from h.toLeComap U hR)

end

section

variable [J.IsStableUnderBaseChange] [J.HasPullbacks]
variable [K.IsStableUnderBaseChange] [K.HasPullbacks]

/-- A continuous site functor in the Stacks Project sense is continuous in the canonical
sheaf-theoretic sense after passing from the source-facing sites to their associated
Grothendieck topologies. -/
instance instIsContinuousOfIsContinuousSiteFunctor
    [h : IsContinuousSiteFunctor u J K] :
    Functor.IsContinuous u J.toGrothendieck K.toGrothendieck :=
  by
    let _ : J.PullbacksPreservedBy u := h.pullbacksPreservedBy
    exact Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy u J K h.toLeComap

end

/-- The identity functor on a source-facing site is continuous in the Stacks Project sense. -/
instance isContinuousSiteFunctor_id (J : Precoverage C) :
    IsContinuousSiteFunctor (𝟭 C) J J where
  toLeComap := by
    intro X R hR
    simpa using hR
  preservesPullback _ _ _ := by infer_instance

end Functor

end CategoryTheory
