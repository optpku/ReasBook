module

public import Mathlib.CategoryTheory.Sites.CoversTop
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Point.Map
public import Mathlib.CategoryTheory.Sites.Point.Over
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Definition_7_38_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.GrothendieckTopology Opposite

universe w v u

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [LocallySmall.{w} C]

/- Domain-style sampling for Lemma 7.38.5:
- primary domain: points of Grothendieck sites, localized sites, and cover-local detection of
  isomorphisms of sheaves;
- sampled owner API:
  `GrothendieckTopology.CoversTop`,
  `GrothendieckTopology.HasEnoughPoints`,
  `GrothendieckTopology.Point.map`,
  `GrothendieckTopology.Point.sheafFiberMapIso`;
- source/core/bridge triage:
  `source-facing`: the Stacks criterion that enough points can be checked on a family covering the
    terminal object;
  `core/canonical`: the owners `J.CoversTop` and `J.HasEnoughPoints`;
  `bridge/view`: localized points on `(C / U i, J.over (U i))` are transported to points of
    `(C, J)` by the canonical cocontinuous localization functor `Over.forget (U i)` via
    `Point.map`, and the comparison on stalk functors is owned by `Point.sheafFiberMapIso`.

Primitive data are only the covering-family hypothesis `hcover` and the local enough-points
hypotheses `hlocal`. Any conservative-family packaging on the slice sites, and its transport to
`(C, J)`, is derived API through `HasEnoughPoints.exists_objectProperty` and `Point.map`, so this
file should stay a thin source-facing bridge theorem rather than introducing a second owner.
-/
/-- Lemma 7.38.5: if the family `U` covers the terminal object of the site `(C, J)` and each
localized site `(C / U i, J.over (U i))` has enough points, then `(C, J)` has enough points. This
is the canonical site-level reformulation of the Stacks hypothesis that
`∐ h_{U_i}^{\#} ⟶ *` is surjective. -/
theorem hasEnoughPoints_of_covering_family_and_slice_sites
    {I : Type w} (U : I → C) (hcover : J.CoversTop U)
    (hlocal : ∀ i : I, HasEnoughPoints.{w} (J.over (U i))) :
    HasEnoughPoints.{w} J := by
  have hlocal' :
      ∀ i : I, ∃ (ι : Type w) (p : ι → Point.{w} (J.over (U i))),
        (ObjectProperty.ofObj p).IsConservativeFamilyOfPoints := fun i ↦
    hasEnoughPoints_iff_exists_conservativePointFamily.1 (hlocal i)
  choose ι p hp using hlocal'
  refine
    hasEnoughPoints_iff_exists_conservativePointFamily.2
      ⟨Σ i, ι i, fun s ↦ (p s.1 s.2).map (Over.forget (U s.1)) J, ?_⟩
  rw [isConservativePointFamily_iff]
  intro ℱ 𝒢 φ hφ
  have hslice :
      ∀ i : I, IsIso ((J.overPullback (Type w) (U i)).map φ) := by
    intro i
    exact
      (isConservativePointFamily_iff (p i)).1 (hp i)
        ((J.overPullback (Type w) (U i)).map φ) fun j ↦ by
          let e :
              ((p i j).map (Over.forget (U i)) J).sheafFiber ≅
                J.overPullback (Type w) (U i) ⋙ (p i j).sheafFiber :=
            (p i j).sheafFiberMapIso (Over.forget (U i)) J (Type w)
          exact (NatIso.isIso_map_iff e φ).1 (hφ ⟨i, j⟩)
  have hbij :
      ∀ (i : I) {Y : C} (g : Y ⟶ U i), Function.Bijective (φ.hom.app (op Y)) := by
    intro i Y g
    let φi := (J.overPullback (Type w) (U i)).map φ
    have hcomp :
        IsIso (((sheafToPresheaf (J.over (U i)) (Type w)).map φi).app (op (Over.mk g))) := by
      have : IsIso ((sheafToPresheaf (J.over (U i)) (Type w)).map φi) := by infer_instance
      exact (NatTrans.isIso_iff_isIso_app _).1 this _
    exact (isIso_iff_bijective _).1 (by
      simpa [GrothendieckTopology.overPullback] using hcomp)
  have hlocinj : Sheaf.IsLocallyInjective φ := by
    change Presheaf.IsLocallyInjective J φ.hom
    constructor
    intro X x y hxy
    refine J.superset_covering ?_ (hcover X.unop)
    intro Y g hg
    rw [Presheaf.equalizerSieve_apply]
    rcases hg with ⟨i, ⟨a⟩⟩
    have hxg : φ.hom.app (op Y) ((ℱ.obj.map g.op) x) = (𝒢.obj.map g.op) (φ.hom.app X x) := by
      simpa using congr_fun (φ.hom.naturality g.op) x
    have hyg : φ.hom.app (op Y) ((ℱ.obj.map g.op) y) = (𝒢.obj.map g.op) (φ.hom.app X y) := by
      simpa using congr_fun (φ.hom.naturality g.op) y
    have hmid : (𝒢.obj.map g.op) (φ.hom.app X x) = (𝒢.obj.map g.op) (φ.hom.app X y) := by
      simpa using congr_arg (𝒢.obj.map g.op) hxy
    apply (hbij i a).injective
    exact hxg.trans (hmid.trans hyg.symm)
  have hlocsurj : Sheaf.IsLocallySurjective φ := by
    change Presheaf.IsLocallySurjective J φ.hom
    constructor
    intro X s
    refine J.superset_covering ?_ (hcover X)
    intro Y g hg
    rw [Presheaf.imageSieve_apply]
    rcases hg with ⟨i, ⟨a⟩⟩
    obtain ⟨t, ht⟩ := (hbij i a).surjective ((𝒢.obj.map g.op) s)
    exact ⟨t, ht⟩
  exact (Sheaf.isLocallyBijective_iff_isIso φ).1 ⟨hlocinj, hlocsurj⟩

end

end CategoryTheory
