/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Tactic.Recall

open AffineMap
open PointedCone (hull)
open scoped Pointwise

/-!
Theorem 2.28 lies in the convex-geometry and topological-closure domain for subsets of
finite-dimensional real normed spaces.

Sampled owner-style declarations:
* `PointedCone.hull` together with `PointedCone.convex`
* `IsClosed.add_left_of_isCompact` and `IsClosed.add_right_of_isCompact`
* `Convex.convexJoin`, `segment_eq_image_lineMap`, and
  `AffineMap.lineMap_continuous_uncurry`
* `Convex.affine_image`, `Convex.affine_preimage`, `IsClosed.preimage`,
  `Metric.isCompact_iff_isClosed_bounded`, and `IsCompact.image`

Best owner abstractions:
* `PointedCone ℝ E` for conic hulls
* `IsCompact Q` for the compact-source bridge items
* `Convex ℝ s` for convexity-preservation items
* `IsClosed s` and `IsCompact s` for the finite-dimensional closedness bridges
* affine maps `E₁ →ᵃ[ℝ] E₂` for the image/preimage items, with compactness supplying the
  closed-image bridge

Primitive data:
* finite-dimensional real normed spaces `E`, `E₁`
* real normed codomains `E₂`
* sets `Q₁`, `Q₂`
* an affine map `f`

Derived API:
* direct owner recalls for the intersection, product, convex-join, and affine image/preimage
  closure rules
* the compact-source bridge theorem for item (8)
* the source-facing finite-dimensional bridge statements in items (4), (8), (10), and (12)

Source/core/bridge triage:
* direct owner recall/use: items (1), (2), (3), (5), (6), (7), (9), (11), (13), and (14)
* source-facing bridge items: (4), (10), and (12)
* bridge/view compact-source core: item (8) as `isClosed_hull_of_isCompact_of_zero_not_mem`
* derived source-facing corollary: the Euclidean-style closed-and-bounded form of item (8)

This file therefore reuses direct owner recalls wherever the exact API already exists, keeps the
compact-source core visible where compactness is the real primitive input, and derives the
textbook closed-and-bounded corollaries from that core.
-/

/- Theorem 2.28 (1), (2), (3), and (9) are direct owner recalls. -/
recall Convex.inter
recall IsClosed.inter
recall Convex.add
recall Convex.convexJoin

section FiniteDimensionalReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {Q₁ Q₂ : Set E}

/-- Theorem 2.28 (1): source item (4). The Minkowski sum of two closed subsets of `ℝⁿ` is closed
if one summand is bounded. -/
-- Proof sketch: in finite dimensions, the closed bounded summand is compact, so apply
-- `IsClosed.add_left_of_isCompact` or `IsClosed.add_right_of_isCompact`.
theorem isClosed_add_of_isClosed_of_isBounded
    (hQ₁_closed : IsClosed Q₁) (hQ₂_closed : IsClosed Q₂)
    (hbounded : Bornology.IsBounded Q₁ ∨ Bornology.IsBounded Q₂) :
    IsClosed (Q₁ + Q₂) := by
  rcases hbounded with hQ₁_bounded | hQ₂_bounded
  · simpa using hQ₂_closed.add_left_of_isCompact
      (Metric.isCompact_of_isClosed_isBounded hQ₁_closed hQ₁_bounded)
  · simpa using hQ₁_closed.add_right_of_isCompact
      (Metric.isCompact_of_isClosed_isBounded hQ₂_closed hQ₂_bounded)

end FiniteDimensionalReal

/- Theorem 2.28 (7) is the direct owner declaration `PointedCone.convex`
specialized to `hull ℝ Q₁`. -/
recall PointedCone.convex

section RealNormed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Q₁ : Set E}

/-- Helper for Theorem 2.28: a point in the pointed hull of a convex set is either `0` or a
positive multiple of a point of the set. -/
theorem mem_pointed_hull_of_convex_iff (hQ₁_convex : Convex ℝ Q₁) {z : E} :
    z ∈ ((hull ℝ Q₁ : PointedCone ℝ E) : Set E) ↔
      z = 0 ∨ ∃ r : ℝ, 0 < r ∧ z ∈ r • Q₁ := by
  constructor
  · intro hz
    -- Expand pointed-hull membership into a finite conical combination.
    have hz' := (PointedCone.mem_hull_set (R := ℝ) (s := Q₁) (x := z)).1 hz
    rcases hz' with ⟨c, hcQ₁, hnonneg, rfl⟩
    let r : ℝ := c.sum fun x a => a
    by_cases hr : r = 0
    · left
      -- If the total coefficient sum vanishes, every nonnegative coefficient vanishes.
      have hzero : ∀ x ∈ c.support, c x = 0 := by
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun x hx => hnonneg x)).1 (by
          simpa [r, Finsupp.sum] using hr)
      change ∑ x ∈ c.support, c x • x = 0
      apply Finset.sum_eq_zero
      intro x hx
      simp [hzero x hx]
    · right
      -- Otherwise, normalize by the positive total weight and use convexity.
      have hrpos : 0 < r := by
        exact lt_of_le_of_ne (Finsupp.sum_nonneg' (fun x => hnonneg x)) (Ne.symm hr)
      refine ⟨r, hrpos, ?_⟩
      refine Set.mem_smul_set.mpr ?_
      refine ⟨c.support.centerMass (fun x => c x) id, ?_, ?_⟩
      · apply hQ₁_convex.centerMass_mem
        · intro x hx
          exact hnonneg x
        · simpa [r, Finsupp.sum] using hrpos
        · intro x hx
          exact hcQ₁ hx
      · have hr' : (∑ x ∈ c.support, c x) ≠ 0 := by
          simpa [r, Finsupp.sum] using hr
        simp [r, Finsupp.sum, Finset.centerMass, hr', smul_smul]
  · intro hz
    rcases hz with rfl | ⟨r, hr, x, hxQ₁, rfl⟩
    · exact (hull ℝ Q₁).zero_mem
    · exact (hull ℝ Q₁).smul_mem hr.le (PointedCone.subset_hull hxQ₁)

omit [NormedSpace ℝ E] in
/-- Helper for Theorem 2.28: a compact set away from the origin has uniform positive and finite
norm bounds. -/
theorem exists_norm_bounds_of_isCompact_of_zero_not_mem
    (hQ₁_compact : IsCompact Q₁) (hQ₁_zero : (0 : E) ∉ Q₁) :
    ∃ δ R : ℝ, 0 < δ ∧ 0 < R ∧ ∀ x ∈ Q₁, δ ≤ ‖x‖ ∧ ‖x‖ ≤ R := by
  -- The minimum norm is positive because `0` is excluded from the compact set.
  obtain ⟨δ, hδpos, hδ⟩ := hQ₁_compact.exists_forall_le' (f := fun x : E => ‖x‖)
    (by simpa using continuous_norm.continuousOn) (a := (0 : ℝ)) (by
      intro x hx
      exact norm_pos_iff.mpr (by exact fun hx0 => hQ₁_zero (hx0 ▸ hx)))
  -- Compactness also gives a uniform upper norm bound.
  obtain ⟨R, hRpos, hR⟩ := Bornology.IsBounded.exists_pos_norm_le (s := Q₁) hQ₁_compact.isBounded
  refine ⟨δ, R, hδpos, hRpos, ?_⟩
  intro x hx
  exact ⟨hδ x hx, hR x hx⟩

/-- Helper for Theorem 2.28: a point in `r • Q₁` bounds the scalar `r` once `Q₁` is uniformly away
from the origin. -/
theorem scalar_le_of_mem_smul_of_norm_lower_bound {δ r : ℝ} {z : E}
    (hδpos : 0 < δ) (hδ : ∀ x ∈ Q₁, δ ≤ ‖x‖)
    (hz : z ∈ r • Q₁) (hr : 0 ≤ r) :
    r ≤ ‖z‖ / δ := by
  rcases Set.mem_smul_set.mp hz with ⟨x, hxQ₁, rfl⟩
  -- Compare `1` with `‖x‖ / δ`, then scale the inequality by `r`.
  have hunit : 1 ≤ ‖x‖ / δ := (one_le_div hδpos).2 (hδ x hxQ₁)
  calc
    r = r * 1 := by ring
    _ ≤ r * (‖x‖ / δ) := by gcongr
    _ = ‖r • x‖ / δ := by
      rw [norm_smul, Real.norm_of_nonneg hr]
      field_simp [hδpos.ne']

/-- Helper for Theorem 2.28: the cone hull of a compact convex subset of a real normed space that
avoids the origin is closed. -/
theorem isClosed_hull_of_isCompact_of_zero_not_mem
    (hQ₁_compact : IsCompact Q₁) (hQ₁_convex : Convex ℝ Q₁) (hQ₁_zero : (0 : E) ∉ Q₁) :
    IsClosed ((hull ℝ Q₁ : PointedCone ℝ E) : Set E) := by
  -- Route correction: normalize pointed-hull membership to positive scalar multiples of `Q₁`,
  -- then run the source-faithful compactness/subsequence argument on those parameters.
  refine IsSeqClosed.isClosed ?_
  intro u z huzmem huz
  by_cases hzero_freq : ∃ᶠ n in Filter.atTop, u n = 0
  · -- If zeros occur frequently, the limit must itself be zero.
    have hz_zero_mem : z ∈ ({0} : Set E) := by
      exact isClosed_singleton.mem_of_frequently_of_tendsto
        (hzero_freq.mono fun n hn => by simp [hn]) huz
    have hz0 : z = 0 := by
      simpa using hz_zero_mem
    exact hz0 ▸ (hull ℝ Q₁).zero_mem
  · obtain ⟨δ, _, hδpos, _, hnorms⟩ :=
      exists_norm_bounds_of_isCompact_of_zero_not_mem hQ₁_compact hQ₁_zero
    have hnonzero : ∀ᶠ n in Filter.atTop, u n ≠ 0 := by
      simpa [Filter.Frequently] using hzero_freq
    rcases (Filter.eventually_atTop.mp hnonzero) with ⟨N, hN⟩
    let v : ℕ → E := fun n ↦ u (n + N)
    have hv_tendsto : Filter.Tendsto v Filter.atTop (nhds z) := by
      simpa [v] using (Filter.tendsto_add_atTop_iff_nat N).2 huz
    have hv_nonzero : ∀ n, v n ≠ 0 := by
      intro n
      exact hN (n + N) (Nat.le_add_left N n)
    have hv_repr : ∀ n, ∃ r : ℝ, ∃ x : E, 0 < r ∧ x ∈ Q₁ ∧ r • x = v n := by
      intro n
      rcases (mem_pointed_hull_of_convex_iff hQ₁_convex).1 (huzmem (n + N)) with hv0 | hmem
      · exact False.elim (hv_nonzero n hv0)
      · rcases hmem with ⟨r, hr, hmem⟩
        rcases Set.mem_smul_set.mp hmem with ⟨x, hxQ₁, hx⟩
        exact ⟨r, x, hr, hxQ₁, hx⟩
    choose r x hrpos hxQ₁ hrepr using hv_repr
    -- Convergence bounds the represented sequence, hence also the scalar parameters.
    obtain ⟨C, _, hC⟩ := Bornology.IsBounded.exists_pos_norm_le (s := Set.range v)
      (Metric.isBounded_range_of_tendsto v hv_tendsto)
    let K : Set (ℝ × E) := Set.Icc (0 : ℝ) (C / δ) ×ˢ Q₁
    have hK_compact : IsCompact K := isCompact_Icc.prod hQ₁_compact
    have hw_mem : ∀ n, (r n, x n) ∈ K := by
      intro n
      refine ⟨⟨(hrpos n).le, ?_⟩, hxQ₁ n⟩
      have hmem : v n ∈ r n • Q₁ := Set.mem_smul_set.mpr ⟨x n, hxQ₁ n, hrepr n⟩
      have hrle := scalar_le_of_mem_smul_of_norm_lower_bound
        hδpos (fun y hy => (hnorms y hy).1) hmem (hrpos n).le
      exact hrle.trans (div_le_div_of_nonneg_right (hC (v n) ⟨n, rfl⟩) hδpos.le)
    obtain ⟨p, hpK, φ, hφmono, hφtendsto⟩ := hK_compact.tendsto_subseq (fun n => hw_mem n)
    rcases p with ⟨β, y⟩
    -- Extract convergent scalar and point subsequences from the compact parameter space.
    have hφtendsto' :
        Filter.Tendsto ((fun n ↦ (r n, x n)) ∘ φ) Filter.atTop (nhds β ×ˢ nhds y) := by
      simpa [nhds_prod_eq] using hφtendsto
    have hr_tendsto : Filter.Tendsto (fun n ↦ r (φ n)) Filter.atTop (nhds β) := hφtendsto'.fst
    have hx_tendsto : Filter.Tendsto (fun n ↦ x (φ n)) Filter.atTop (nhds y) := hφtendsto'.snd
    have hv_sub_tendsto : Filter.Tendsto (v ∘ φ) Filter.atTop (nhds z) :=
      hv_tendsto.comp hφmono.tendsto_atTop
    have hsmul_tendsto :
        Filter.Tendsto (fun n ↦ r (φ n) • x (φ n)) Filter.atTop (nhds (β • y)) :=
      hr_tendsto.smul hx_tendsto
    have hp_eq_z : β • y = z := by
      exact tendsto_nhds_unique_of_eventuallyEq hsmul_tendsto hv_sub_tendsto
        (Filter.Eventually.of_forall fun n => hrepr (φ n))
    rcases hpK with ⟨hβIcc, hyQ₁⟩
    by_cases hβ0 : β = 0
    · have hz0 : z = 0 := by
        simpa [hβ0] using hp_eq_z.symm
      exact hz0 ▸ (hull ℝ Q₁).zero_mem
    · exact (mem_pointed_hull_of_convex_iff hQ₁_convex).2 <|
        Or.inr ⟨β, lt_of_le_of_ne hβIcc.1 (Ne.symm hβ0), Set.mem_smul_set.mpr ⟨y, hyQ₁, hp_eq_z⟩⟩

end RealNormed

section FiniteDimensionalReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {Q₁ Q₂ : Set E}

/-- Theorem 2.28 (2): source item (8). The cone hull of a closed bounded subset of `ℝⁿ` that
avoids the origin is closed. -/
-- Proof sketch: in finite dimensions, a closed bounded set is compact, so apply the compact-source
-- bridge theorem.
theorem isClosed_hull_of_isClosed_of_isBounded_of_zero_not_mem
    (hQ₁_closed : IsClosed Q₁) (hQ₁_bounded : Bornology.IsBounded Q₁)
    (hQ₁_convex : Convex ℝ Q₁) (hQ₁_zero : (0 : E) ∉ Q₁) :
    IsClosed ((hull ℝ Q₁ : PointedCone ℝ E) : Set E) :=
  isClosed_hull_of_isCompact_of_zero_not_mem
    (Metric.isCompact_of_isClosed_isBounded hQ₁_closed hQ₁_bounded) hQ₁_convex hQ₁_zero

omit [FiniteDimensional ℝ E] in
/-- Compact-source bridge for Theorem 2.28 (10): the convex join of two compact subsets of a real
normed space is compact. -/
theorem isCompact_convexJoin
    (hQ₁_compact : IsCompact Q₁) (hQ₂_compact : IsCompact Q₂) :
    IsCompact (convexJoin ℝ Q₁ Q₂) := by
  let K := Q₁ ×ˢ (Q₂ ×ˢ Set.Icc (0 : ℝ) 1)
  let interpolate : E × (E × ℝ) → E := fun pqt ↦ lineMap pqt.1 pqt.2.1 pqt.2.2
  have hK_compact : IsCompact K := by
    simpa [K] using hQ₁_compact.prod (hQ₂_compact.prod isCompact_Icc)
  have hinterpolate_compact : IsCompact (interpolate '' K) := by
    refine hK_compact.image_of_continuousOn ?_
    fun_prop
  have hinterpolate :
      interpolate '' K = convexJoin ℝ Q₁ Q₂ := by
    ext x
    constructor
    · rintro ⟨⟨a, b, t⟩, hmem, rfl⟩
      rcases hmem with ⟨ha, hb, ht⟩
      rw [mem_convexJoin]
      refine ⟨a, ha, b, hb, ?_⟩
      rw [segment_eq_image_lineMap]
      exact ⟨t, ht, rfl⟩
    · rw [mem_convexJoin]
      rintro ⟨a, ha, b, hb, hx⟩
      rw [segment_eq_image_lineMap] at hx
      rcases hx with ⟨t, ht, rfl⟩
      exact ⟨⟨a, b, t⟩, ⟨ha, hb, ht⟩, rfl⟩
  rw [← hinterpolate]
  exact hinterpolate_compact

/-- Theorem 2.28 (3): source item (10). The convex join of two closed bounded subsets of `ℝⁿ` is
closed. -/
-- Proof sketch: realize `convexJoin ℝ Q₁ Q₂` as the image of
-- `Set.Icc (0 : ℝ) 1 ×ˢ Q₁ ×ˢ Q₂` under the continuous interpolation map
-- `(t, x, y) ↦ (1 - t) • x + t • y`, then use compactness of the domain.
theorem isClosed_convexJoin_of_isClosed_of_isBounded
    (hQ₁_closed : IsClosed Q₁) (hQ₂_closed : IsClosed Q₂)
    (hQ₁_bounded : Bornology.IsBounded Q₁) (hQ₂_bounded : Bornology.IsBounded Q₂) :
    IsClosed (convexJoin ℝ Q₁ Q₂) :=
  (isCompact_convexJoin
    (Metric.isCompact_of_isClosed_isBounded hQ₁_closed hQ₁_bounded)
    (Metric.isCompact_of_isClosed_isBounded hQ₂_closed hQ₂_bounded)).isClosed

end FiniteDimensionalReal

/- Theorem 2.28 (5) and (6) are direct owner recalls. -/
recall Convex.prod
recall IsClosed.prod

section Affine

variable {E₁ E₂ : Type*}
variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
variable [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

variable {Q₁ : Set E₁}
variable (f : E₁ →ᵃ[ℝ] E₂)

/- Theorem 2.28 (11), (13), and (14) are direct owner recalls. For item (14), the textbook
boundedness assumption is auxiliary and does not affect the canonical closed-preimage statement.
For item (12), the local bridge keeps the valid compact-source closed-image consequence. -/
recall Convex.affine_image
recall Convex.affine_preimage
recall IsClosed.preimage

/-- Theorem 2.28 (4): source item (12). The affine image of a closed bounded subset of `ℝⁿ` is
closed in `ℝᵐ`. -/
-- Proof sketch: a closed bounded subset of a finite-dimensional real normed space is compact, and
-- the image of a compact set under a continuous affine map is compact, hence closed.
theorem isClosed_affine_image_of_isClosed_of_isBounded
    (hQ₁_closed : IsClosed Q₁) (hQ₁_bounded : Bornology.IsBounded Q₁) :
    IsClosed (f '' Q₁) := by
  simpa using
    (Metric.isCompact_of_isClosed_isBounded hQ₁_closed hQ₁_bounded).image
      f.continuous_of_finiteDimensional |>.isClosed

end Affine
