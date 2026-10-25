module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Definition_7_13_1
public import stacks_project.Chap07.Definition_7_8_1
public import stacks_project.Chap07.Definition_7_8_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

namespace Functor

open SemiRepresentableFamily.Over

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- Helper for Remark 7.13.6: the componentwise image of a fixed-target family along a functor. -/
def imageFamily (u : C ⥤ D) {V : C} (S : SemiRepresentableFamily.Over V) :
    SemiRepresentableFamily.Over (u.obj V) where
  index := S.index
  obj := fun i ↦ (Over.post u).obj (S.obj i)

/- Domain-style sampling for Remark 7.13.6:
- primary domain: quasi-continuous functors between sites and their canonical continuity owners;
- sampled owner API:
  `CategoryTheory.Functor.IsContinuousSiteFunctor`,
  `CategoryTheory.Functor.IsContinuous`,
  `CategoryTheory.Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy`,
  `CategoryTheory.Over.post`,
  `CategoryTheory.SemiRepresentableFamily.map`,
  `CategoryTheory.SemiRepresentableFamily.Over.TautologicallyEquivalent`;
- source/core/bridge triage:
  `source-facing`: `Functor.IsQuasiContinuousSiteFunctor`;
  `core/canonical`: `Functor.IsContinuousSiteFunctor` and `Functor.IsContinuous`;
  `bridge/view`: the instance upgrading quasi-continuity to continuity.

Primitive data are:
1. mapped covering families being tautologically equivalent to covering families in the target
   site;
2. pullback-comparison isomorphisms for arrows in covering presieves, assuming only the
   pointwise source and target pullbacks needed to form that comparison map.

Derived API are the induced `IsContinuousSiteFunctor` structure and the resulting canonical
`Functor.IsContinuous` instance; the latter additionally uses global source and target pullbacks
through the existing precoverage-to-topology bridge.
-/

/-- Remark 7.13.6: a functor of sites is quasi-continuous if every `J`-covering family over `V`
maps to a family tautologically equivalent to some `K`-covering family over `u(V)`, and if base
change along each member of a covering family is preserved up to the canonical
pullback-comparison isomorphism. -/
class IsQuasiContinuousSiteFunctor
    (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D) : Prop where
  image_cover_tautologicallyEquivalent :
    ∀ {V : C} (S : SemiRepresentableFamily.Over.{max u₁ v₁} V),
      IsCovering J.toPrecoverage S →
      ∃ T : SemiRepresentableFamily.Over.{max u₁ v₁} (u.obj V),
        IsCovering K.toPrecoverage T ∧
        TautologicallyEquivalent (imageFamily u S) T
  pullbackComparison_isIso_of_mem :
    ∀ {V : C} {R : Presieve V}, R ∈ J.toPrecoverage V →
      ∀ {Y : C} {i : Y ⟶ V}, R i →
      ∀ {T : C} (f : T ⟶ V) [HasPullback f i] [HasPullback (u.map f) (u.map i)],
        IsIso (pullbackComparison u f i)

theorem pullbackComparison_isIso_of_coveringFamily (h : IsQuasiContinuousSiteFunctor u J K)
    {V : C} (S : SemiRepresentableFamily.Over.{max u₁ v₁} V)
    (hS : IsCovering J.toPrecoverage S) {Y : C} {i : Y ⟶ V} (hi : S.toPresieve i)
    {T : C} (f : T ⟶ V) [HasPullback f i] [HasPullback (u.map f) (u.map i)] :
    IsIso (pullbackComparison u f i) :=
  h.pullbackComparison_isIso_of_mem hS hi f

/- Route correction: the local API does not provide `SemiRepresentableFamily.map`, so the mapped
family is expressed explicitly by `imageFamily` and compared through the generated sieve. -/
theorem map_mem_of_image_cover_tautologicallyEquivalent
    {V : C} {R : Presieve V} (h : IsQuasiContinuousSiteFunctor u J K)
    (hR : R ∈ J.toPrecoverage V) :
    R.map u ∈ K.toPrecoverage (u.obj V) := by
  obtain ⟨ι, Y, f, rfl⟩ := R.exists_eq_ofArrows
  let S : SemiRepresentableFamily.Over.{max u₁ v₁} V := ofArrows Y f
  -- Repackage the covering presieve as a covering family so the quasi-continuity hypothesis applies.
  rcases h.image_cover_tautologicallyEquivalent S (by simpa [S, IsCovering]) with ⟨T, hT, hST⟩
  rw [GrothendieckTopology.mem_toPrecoverage_iff]
  have hT' : Sieve.generate T.toPresieve ∈ K (u.obj V) := by
    exact (GrothendieckTopology.mem_toPrecoverage_iff K T.toPresieve).1 hT
  -- Tautological equivalence identifies the generated sieve of the mapped family with that of `T`.
  have hSieve :
      Sieve.generate ((Presieve.ofArrows Y f).map u) = Sieve.generate T.toPresieve := by
    simpa [S, imageFamily, toSieve, Presieve.map_ofArrows] using
      toSieve_eq_of_tautologicallyEquivalent hST
  rw [hSieve]
  exact hT'

theorem preservesPullback_of_pullbackComparison_isIso_of_mem
    [HasPullbacks D]
    {V : C} {R : Presieve V} (h : IsQuasiContinuousSiteFunctor u J K)
    (hR : R ∈ J.toPrecoverage V) {Y : C} {i : Y ⟶ V} (hi : R i)
    {T : C} (f : T ⟶ V) [HasPullback f i] :
    PreservesLimit (cospan f i) u := by
  -- The ambient target pullback gives the comparison map, and quasi-continuity makes it an isomorphism.
  let _ : HasPullback (u.map f) (u.map i) := inferInstance
  let _ : IsIso (pullbackComparison u f i) := h.pullbackComparison_isIso_of_mem hR hi f
  exact PreservesPullback.of_iso_comparison u

instance instIsContinuousSiteFunctorOfIsQuasiContinuousSiteFunctor
    [HasPullbacks D]
    [h : IsQuasiContinuousSiteFunctor u J K] :
    IsContinuousSiteFunctor u J.toPrecoverage K.toPrecoverage where
  toLeComap := by
    intro V R hR
    exact map_mem_of_image_cover_tautologicallyEquivalent h hR
  preservesPullback {V} {R} hR {Y} {i} hi {T} f := by
    exact preservesPullback_of_pullbackComparison_isIso_of_mem h hR hi f

theorem toPrecoverage_toGrothendieck_eq
    {E : Type*} [Category E] [HasPullbacks E] (L : GrothendieckTopology E) :
    L.toPrecoverage.toGrothendieck = L := by
  rw [← L.toPrecoverage.toGrothendieck_toPretopology_eq_toGrothendieck]
  exact (@Pretopology.gi E _ _).l_u_eq L

-- Proof sketch: the two source-facing clauses of quasi-continuity first recover the Chapter 7
-- precoverage-level owner `IsContinuousSiteFunctor u J.toPrecoverage K.toPrecoverage`, and then
-- the existing bridge from that owner yields mathlib's `Functor.IsContinuous`.
variable [HasPullbacks C] [HasPullbacks D]
variable (u : C ⥤ D)

/-- A quasi-continuous functor is continuous in the canonical sheaf-theoretic sense. -/
instance instIsContinuousOfIsQuasiContinuousSiteFunctor
    [IsQuasiContinuousSiteFunctor u J K] : Functor.IsContinuous u J K := by
  let _ :
      Functor.IsContinuousSiteFunctor
        u J.toPrecoverage K.toPrecoverage :=
    inferInstance
  simpa [toPrecoverage_toGrothendieck_eq J, toPrecoverage_toGrothendieck_eq K] using
    (inferInstance :
      Functor.IsContinuous
        u J.toPrecoverage.toGrothendieck K.toPrecoverage.toGrothendieck)

end Functor

end CategoryTheory
