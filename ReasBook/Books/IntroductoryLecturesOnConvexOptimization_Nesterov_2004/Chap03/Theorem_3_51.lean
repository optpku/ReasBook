/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Positivity

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open MeasureTheory

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable {μ : Measure E} [μ.IsAddHaarMeasure]

local notation "dim" => Module.finrank ℝ E

/- Primary domain: intrinsic volume comparison for convex subsets of a closed ball in a
finite-dimensional real normed space.

Sampled owner-style declarations:
- `Convex.nullMeasurableSet`
- `MeasureTheory.measureReal_mono`
- `MeasureTheory.Measure.addHaar_real_closedBall`
- `Module.finrank_pos`

Owner abstraction:
- the ambient additive Haar measure owner `μ` together with its real-valued evaluation `μ.real`
  on an arbitrary finite-dimensional real normed space.

Layer of this file:
- `source-facing`. The theorem is the chapter's direct radius-volume comparison, while its owner
  layer is the intrinsic finite-dimensional real-space volume API rather than the coordinate model
  `EuclideanSpace ℝ (Fin n)`.

Primitive data:
- the convex set `Q`, the comparison set `Sk`, the center `xStar`, and the radii `D`, `vkStar`
- the positive-dimension hypothesis `0 < dim`
- convexity and outer-ball containment for `Q`
- positivity of `μ.real Q`
- the source-visible radius sign condition `0 < D`
- measurability of `Sk`
- the source-facing inclusion `Sk ⊆ Q`
- the inclusion `Metric.closedBall xStar vkStar ∩ Q ⊆ Sk`
- the chapter-context premise `xStar ∈ Q`

Derived API:
- positivity of `dim`, supplied directly by the public hypothesis
- finiteness of `Sk`, derived from `Sk ⊆ Q ⊆ Metric.closedBall xStar D`
- the real-valued bound on `vkStar` in terms of the measure ratio `μ.real Sk / μ.real Q`, with
  the exponent written canonically as `1 / dim`.
-/

/-- Helper for Theorem 3.51: if a positive-volume set `Q` contains the center `xStar` and is
contained in `Metric.closedBall xStar D`, then the outer radius `D` must be positive. -/
lemma outer_radius_pos_of_positive_measure
    (hdim : 0 < dim)
    {Q : Set E} {xStar : E} {D : ℝ}
    (hxStar : xStar ∈ Q)
    (hQ_pos : 0 < μ.real Q)
    (hQ_subset : Q ⊆ Metric.closedBall xStar D) :
    0 < D := by
  -- The center belongs to the closed ball, so the radius is at least `0`.
  have hD_nonneg : 0 ≤ D := by
    have hxBall : xStar ∈ Metric.closedBall xStar D := hQ_subset hxStar
    simpa [Metric.mem_closedBall] using hxBall
  by_contra hD_pos
  have hD_zero : D = 0 := le_antisymm (le_of_not_gt hD_pos) hD_nonneg
  have hQ_subset_zero : Q ⊆ Metric.closedBall xStar 0 := by
    simpa [hD_zero] using hQ_subset
  have hmono : μ.real Q ≤ μ.real (Metric.closedBall xStar 0) :=
    measureReal_mono hQ_subset_zero measure_closedBall_lt_top.ne
  -- A zero-radius closed ball is a singleton, hence has zero Haar measure in positive dimension.
  have hclosed_zero : μ.real (Metric.closedBall xStar 0) = 0 := by
    rw [Measure.addHaar_real_closedBall μ xStar (show 0 ≤ (0 : ℝ) by simp)]
    simp [zero_pow (Nat.ne_of_gt hdim)]
  rw [hclosed_zero] at hmono
  linarith

/-- Helper for Theorem 3.51: if the inner radius strictly exceeds the outer one, then the
inclusion hypothesis already forces `Q ⊆ Sk`. -/
lemma comparison_set_contains_domain_of_outer_radius_lt
    {Q Sk : Set E} {xStar : E} {D vkStar : ℝ}
    (hQ_subset : Q ⊆ Metric.closedBall xStar D)
    (hball : Metric.closedBall xStar vkStar ∩ Q ⊆ Sk)
    (hDv : D < vkStar) :
    Q ⊆ Sk := by
  intro y hy
  have hyD : y ∈ Metric.closedBall xStar D := hQ_subset hy
  have hyv : y ∈ Metric.closedBall xStar vkStar := by
    rw [Metric.mem_closedBall] at hyD ⊢
    exact le_of_lt (lt_of_le_of_lt hyD hDv)
  exact hball ⟨hyv, hy⟩

/-- Helper for Theorem 3.51: the homothety of `Q` centered at `xStar` with factor `α ∈ [0, 1]`
stays inside the smaller closed ball and inside `Q` itself. -/
lemma homothety_image_subset_closedBall_inter_of_convex
    {Q : Set E} {xStar : E} {α D : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hQ_convex : Convex ℝ Q) (hxStar : xStar ∈ Q)
    (hQ_subset : Q ⊆ Metric.closedBall xStar D) :
    AffineMap.homothety xStar α '' Q ⊆ Metric.closedBall xStar (α * D) ∩ Q := by
  rintro z ⟨y, hy, rfl⟩
  constructor
  · -- The outer-ball hypothesis contracts to radius `α * D` under homothety.
    rw [Metric.mem_closedBall]
    have hyD : dist y xStar ≤ D := by
      simpa [Metric.mem_closedBall] using hQ_subset hy
    calc
      dist ((AffineMap.homothety xStar α) y) xStar = ‖α‖ * dist xStar y :=
        dist_homothety_center xStar y α
      _ = α * dist y xStar := by
        rw [Real.norm_of_nonneg hα0, dist_comm]
      _ ≤ α * D := mul_le_mul_of_nonneg_left hyD hα0
  · -- Convexity keeps the entire segment from `xStar` to `y` inside `Q`.
    rw [AffineMap.homothety_eq_lineMap]
    exact hQ_convex.lineMap_mem hxStar hy ⟨hα0, hα1⟩

/-- Helper for Theorem 3.51: the real-valued Haar measure of a homothety image scales by
`α ^ dim` when `α ≥ 0`. -/
lemma measureReal_homothety_image
    {Q : Set E} {xStar : E} {α : ℝ}
    (hα0 : 0 ≤ α) :
    μ.real (AffineMap.homothety xStar α '' Q) = α ^ dim * μ.real Q := by
  -- Rewrite the owner-level ENNReal scaling law through `μ.real`.
  rw [MeasureTheory.Measure.real, Measure.addHaar_image_homothety]
  rw [ENNReal.toReal_ofReal_mul]
  · simp [MeasureTheory.Measure.real, abs_of_nonneg, hα0]
  · positivity

/-- Helper for Theorem 3.51: a lower bound on `α ^ dim * μ.real Q` turns into the claimed
`dim`-th-root bound on `α`. -/
lemma alpha_le_volume_ratio_rpow_of_measure_bound
    (hdim : 0 < dim)
    {Q Sk : Set E} {α : ℝ}
    (hQ_pos : 0 < μ.real Q)
    (hα0 : 0 ≤ α)
    (hmeasure : α ^ dim * μ.real Q ≤ μ.real Sk) :
    α ≤ Real.rpow (μ.real Sk / μ.real Q) (1 / (dim : ℝ)) := by
  have hratio_nonneg : 0 ≤ μ.real Sk / μ.real Q := by
    positivity
  have hpow_le : α ^ dim ≤ μ.real Sk / μ.real Q := by
    exact (le_div_iff₀ hQ_pos).2 hmeasure
  have hdim_pos_real : 0 < (dim : ℝ) := by
    exact_mod_cast hdim
  -- Take the `dim`-th root after dividing by the positive denominator.
  have hroot :=
    (Real.le_rpow_inv_iff_of_pos hα0 hratio_nonneg hdim_pos_real).2 (by
      simpa [Real.rpow_natCast] using hpow_le)
  simpa [one_div] using hroot

/-- Theorem 3.51, stated at the intrinsic owner level: if `0 < Module.finrank ℝ E`, if a convex
set `Q` of positive `μ`-volume in a finite-dimensional real normed space is contained in the
closed ball `B(xStar, D)` with `0 < D`, if `Sk ⊆ Q` is measurable, and if
`B(xStar, vkStar) ∩ Q ⊆ Sk`, then under the chapter's standing center context `xStar ∈ Q` and
the standing radius bound `vkStar ≤ D` coming from the earlier localization setup, the inner
radius `vkStar` is bounded by `D` times the `dim`-th root of the Haar-measure ratio
`μ.real Sk / μ.real Q`. The finite-volume side condition on `Sk` is derived internally from
`Sk ⊆ Q ⊆ B(xStar, D)`. Specializing to the canonical choice
`μ = Measure.addHaar` gives the chapter owner used downstream, and in Euclidean space this differs
from textbook Lebesgue volume only by a global positive normalization factor, so the displayed
ratio is unchanged.
-/
-- Proof sketch: the standing radius comparison gives `vkStar ≤ D`, so one can normalize
-- `α = vkStar / D ∈ [0, 1]`.
-- Since `xStar ∈ Q` and `Q` is convex, the homothetic copy `(1 - α) • xStar + α • Q` lies in
-- `Q`; because `Q ⊆ Metric.closedBall xStar D`, that same set also lies in
-- `Metric.closedBall xStar vkStar`. Hence it is contained in `Sk`. Taking volumes and using
-- translation invariance together with the scaling rule yields
-- `μ.real Sk ≥ α ^ dim * μ.real Q`, which rearranges to the claimed bound.
theorem inner_ball_radius_le_outer_radius_mul_volume_ratio_rpow_of_convex
    (hdim : 0 < dim)
    {Q Sk : Set E} {xStar : E} {D vkStar : ℝ}
    (hQ_convex : Convex ℝ Q) (hxStar : xStar ∈ Q)
    (hQ_pos : 0 < μ.real Q)
    (hD_pos : 0 < D)
    (hvkStar_le : vkStar ≤ D)
    (hQ_subset : Q ⊆ Metric.closedBall xStar D)
    (hSk_meas : MeasurableSet Sk)
    (hSk_subset : Sk ⊆ Q)
    (hball : Metric.closedBall xStar vkStar ∩ Q ⊆ Sk) :
    vkStar ≤
      D *
        Real.rpow
          (μ.real Sk / μ.real Q)
          (1 / (dim : ℝ)) := by
  let α : ℝ := vkStar / D
  have hD_nonneg : 0 ≤ D := le_of_lt hD_pos
  have hD_ne : D ≠ 0 := ne_of_gt hD_pos
  have hSk_subset_ball : Sk ⊆ Metric.closedBall xStar D := by
    -- The comparison set inherits the outer-ball bound from `Q`.
    intro y hy
    exact hQ_subset (hSk_subset hy)
  have hSk_finite : μ Sk ≠ ⊤ := by
    -- This finiteness side condition is needed to compare `μ.real` by monotonicity.
    exact measure_ne_top_of_subset hSk_subset_ball measure_closedBall_lt_top.ne
  by_cases hvk_nonneg : 0 ≤ vkStar
  · have hα0 : 0 ≤ α := by
      -- The normalized radius is nonnegative in the main geometric branch.
      dsimp [α]
      exact div_nonneg hvk_nonneg hD_nonneg
    have hα1 : α ≤ 1 := by
      -- The standing outer-radius bound forces `α ∈ [0, 1]`.
      dsimp [α]
      exact (div_le_iff₀ hD_pos).2 (by simpa using hvkStar_le)
    have hα_mul : α * D = vkStar := by
      -- Clearing the denominator recovers the original radius.
      dsimp [α]
      field_simp [hD_ne]
    have hhom_subset :
        AffineMap.homothety xStar α '' Q ⊆ Metric.closedBall xStar vkStar ∩ Q := by
      -- The convex homothety image lands in the inner ball after rewriting `α * D = vkStar`.
      intro z hz
      have hz' :=
        homothety_image_subset_closedBall_inter_of_convex
          hα0 hα1 hQ_convex hxStar hQ_subset hz
      simpa [hα_mul] using hz'
    have hmeasure :
        α ^ dim * μ.real Q ≤ μ.real Sk := by
      -- Volume monotonicity plus the homothety scaling rule yields the key comparison.
      have hmono :
          μ.real (AffineMap.homothety xStar α '' Q) ≤ μ.real Sk :=
        measureReal_mono (Set.Subset.trans hhom_subset hball) hSk_finite
      simpa [measureReal_homothety_image (μ := μ) (Q := Q) (xStar := xStar) hα0] using hmono
    have hα_le :
        α ≤ Real.rpow (μ.real Sk / μ.real Q) (1 / (dim : ℝ)) :=
      alpha_le_volume_ratio_rpow_of_measure_bound (μ := μ) hdim hQ_pos hα0 hmeasure
    -- Multiply the normalized estimate by `D` to recover the claimed radius bound.
    calc
      vkStar = D * α := by rw [mul_comm, hα_mul]
      _ ≤
          D *
            Real.rpow
              (μ.real Sk / μ.real Q)
              (1 / (dim : ℝ)) :=
        mul_le_mul_of_nonneg_left hα_le hD_nonneg
  · have hratio_nonneg : 0 ≤ μ.real Sk / μ.real Q := by
      positivity
    have hrhs_nonneg :
        0 ≤
          D *
            Real.rpow
              (μ.real Sk / μ.real Q)
              (1 / (dim : ℝ)) := by
      -- The right-hand side is nonnegative, so any negative `vkStar` is already bounded by it.
      exact mul_nonneg hD_nonneg (Real.rpow_nonneg hratio_nonneg _)
    have hvk_neg : vkStar < 0 := lt_of_not_ge hvk_nonneg
    exact le_trans (le_of_lt hvk_neg) hrhs_nonneg

end
