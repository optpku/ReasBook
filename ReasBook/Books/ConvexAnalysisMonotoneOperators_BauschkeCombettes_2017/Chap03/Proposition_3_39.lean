/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

/-- Helper for Proposition 3.39: the convex join of two compact sets is compact because it is the
continuous image of the compact parameter space of endpoints together with a scalar in `[0,1]`. -/
private lemma isCompact_convexJoin {E : Type*}
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] {s t : Set E} (hs : IsCompact s) (ht : IsCompact t) :
    IsCompact (convexJoin ℝ s t) := by
  -- Parameterize each point of the join by its two endpoints and one interpolation scalar.
  have hjoin :
      convexJoin ℝ s t =
        (fun p : (E × E) × ℝ ↦ (1 - p.2) • p.1.1 + p.2 • p.1.2) ''
          ((s ×ˢ t) ×ˢ Set.Icc (0 : ℝ) 1) := by
    ext z
    constructor
    · intro hz
      rcases mem_convexJoin.mp hz with ⟨x, hx, y, hy, hzSeg⟩
      rw [segment_eq_image_lineMap] at hzSeg
      rcases hzSeg with ⟨a, ha, rfl⟩
      refine ⟨((x, y), a), ⟨⟨hx, hy⟩, ha⟩, ?_⟩
      simp [AffineMap.lineMap_apply_module]
    · rintro ⟨p, hp, rfl⟩
      rcases p with ⟨⟨x, y⟩, a⟩
      rcases hp with ⟨⟨hx, hy⟩, ha⟩
      rcases ha with ⟨ha0, ha1⟩
      refine mem_convexJoin.mpr ⟨x, hx, y, hy, ?_⟩
      refine ⟨1 - a, a, sub_nonneg.mpr ha1, ha0, by ring, rfl⟩
  -- Compactness follows from compactness of the parameter space and continuity of the join map.
  rw [hjoin]
  have hcont : Continuous fun p : (E × E) × ℝ ↦ (1 - p.2) • p.1.1 + p.2 • p.1.2 := by
    fun_prop
  exact ((hs.prod ht).prod isCompact_Icc).image hcont

/-- Helper for Proposition 3.39: a finite family of compact convex sets has compact convex hull. -/
private lemma isCompact_convexHull_iUnion_finset {ι : Type*} {E : Type*}
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] (s : Finset ι) (C : ι → Set E)
    (hconv : ∀ i, Convex ℝ (C i)) (hcompact : ∀ i, IsCompact (C i)) :
    IsCompact (convexHull ℝ (⋃ i ∈ s, C i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert i s hi ih =>
      have hUnion : (⋃ j ∈ insert i s, C j) = C i ∪ ⋃ j ∈ s, C j := by
        ext x
        simp
      rw [hUnion]
      by_cases hi_nonempty : (C i).Nonempty
      · by_cases hs_nonempty : (⋃ j ∈ s, C j).Nonempty
        · rw [convexHull_union hi_nonempty hs_nonempty, hconv i |>.convexHull_eq]
          exact isCompact_convexJoin (hcompact i) ih
        · have hs_empty : (⋃ j ∈ s, C j) = ∅ := Set.not_nonempty_iff_eq_empty.mp hs_nonempty
          simp [hs_empty, hconv i |>.convexHull_eq, hcompact i]
      · have hi_empty : C i = ∅ := Set.not_nonempty_iff_eq_empty.mp hi_nonempty
        simp [hi_empty, ih]

-- Proof sketch: write `convexHull ℝ (⋃ i, C i)` as the image of the compact product
-- `(∏ i, C i) × stdSimplex ℝ (Fin m)` under the continuous barycentric map
-- `(x, η) ↦ ∑ i, η i • x i`, using convexity of each `C i` to regroup any finite convex
-- combination into one point from each `C i`.
/-- Proposition 3.39 (1): the convex hull of a finite family of compact convex subsets of a real
topological vector space, hence in particular of a real Hilbert space, is compact. -/
theorem isCompact_convexHull_iUnion_fin
    {ι : Type*} [Finite ι] {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] (C : ι → Set E)
    (hconv : ∀ i, Convex ℝ (C i))
    (hcompact : ∀ i, IsCompact (C i)) :
    IsCompact (convexHull ℝ (⋃ i, C i) : Set E) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  simpa using isCompact_convexHull_iUnion_finset (Finset.univ : Finset ι) C hconv hcompact

private lemma isCompact_convexHull_iUnion_fin_weakSpace
    {ι : Type*} [Finite ι] (C : ι → Set (WeakSpace ℝ 𝓗))
    (hconv : ∀ i, Convex ℝ (C i)) (hcompact : ∀ i, IsCompact (C i)) :
    IsCompact (convexHull ℝ (⋃ i, C i) : Set (WeakSpace ℝ 𝓗)) := by
  let hModule : Module ℝ (WeakSpace ℝ 𝓗) := by
    haveI : AddCommGroup (WeakSpace ℝ 𝓗) := WeakSpace.instAddCommGroup
    infer_instance
  exact
    @isCompact_convexHull_iUnion_fin ι inferInstance (WeakSpace ℝ 𝓗)
      WeakSpace.instAddCommGroup hModule inferInstance WeakSpace.instIsTopologicalAddGroup
      WeakSpace.instContinuousSMul C hconv hcompact

-- Proof sketch: transport the family to `WeakSpace ℝ 𝓗`, where each image
-- `(toWeakSpace ℝ 𝓗) '' C i` is compact and convex. Then apply the first clause in the weak
-- topology and use that
-- `toWeakSpace ℝ 𝓗` commutes with convex hulls because it is linear.
/-- Proposition 3.39 (2): the convex hull of a finite family of weakly compact convex subsets of a
real Hilbert space is weakly compact, expressed as compactness in `WeakSpace ℝ 𝓗`. -/
theorem weaklyCompact_convexHull_iUnion_fin
    {ι : Type*} [Finite ι] (C : ι → Set 𝓗) (hconv : ∀ i, Convex ℝ (C i))
    (hweaklyCompact : ∀ i, IsCompact ((toWeakSpace ℝ 𝓗) '' C i)) :
    IsCompact ((toWeakSpace ℝ 𝓗) '' convexHull ℝ (⋃ i, C i)) := by
  classical
  -- Transport convexity to the weak space via the canonical linear map.
  have hconvWeak : ∀ i, Convex ℝ ((toWeakSpace ℝ 𝓗) '' C i) := by
    intro i
    exact (hconv i).linear_image (toWeakSpace ℝ 𝓗).toLinearMap
  -- The canonical map to `WeakSpace` commutes with convex hull and finite unions.
  have himage :
      (toWeakSpace ℝ 𝓗) '' convexHull ℝ (⋃ i, C i) =
        convexHull ℝ (⋃ i, (toWeakSpace ℝ 𝓗) '' C i) := by
    simpa [Set.image_iUnion] using
      (LinearMap.image_convexHull (toWeakSpace ℝ 𝓗).toLinearMap (⋃ i, C i))
  rw [himage]
  -- Apply the same compact-convex-hull theorem inside the weak topology.
  simpa using
    (isCompact_convexHull_iUnion_fin_weakSpace
      (fun i ↦ (toWeakSpace ℝ 𝓗) '' C i) hconvWeak hweaklyCompact :
        IsCompact
          (convexHull ℝ (⋃ i, (toWeakSpace ℝ 𝓗) '' C i) : Set (WeakSpace ℝ 𝓗)))
