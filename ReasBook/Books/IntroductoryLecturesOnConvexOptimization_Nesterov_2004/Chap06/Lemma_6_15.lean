/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open MeasureTheory
open scoped BigOperators

/-
Lemma 6.15 lies in the one-dimensional interval-integral / convex-sampling domain.

Sampled owner-style declarations:
- `AntitoneOn.integral_le_sum` and `AntitoneOn.sum_le_integral` in
  `Mathlib/Analysis/SumIntegralComparisons`, the canonical left/right endpoint comparison lemmas
  for monotone samples against interval integrals;
- `intervalIntegral.sum_integral_adjacent_intervals`, the canonical owner for decomposing an
  interval integral into unit cells;
- `ConvexOn.map_sum_le` in `Mathlib/Analysis/Convex/Jensen`, the canonical finite Jensen owner for
  midpoint estimates of convex functions.

Best owner abstraction:
- source-facing: the textbook sandwich estimate for the integer samples of a decreasing convex
  function;
- core/canonical: `AntitoneOn`, `ConvexOn`, `intervalIntegral`, and Jensen-style midpoint bounds;
- bridge/view: the centered unit intervals `[k - 1 / 2, k + 1 / 2]`, whose midpoint is the sample
  point `k`.

Primitive data:
- `ξ : ℝ → ℝ`;
- integer endpoints `a ≤ b`.

Derived API:
- the sample sum `∑ k ∈ Finset.Icc a b, ξ k`;
- the two canonical interval integrals bounding that sum.

This item does not define a new owner. The refinement keeps the source-facing theorem, places its
conclusion on the canonical `Set.Icc` surface, and keeps the monotonicity and convexity hypotheses
on the separate minimal intervals actually used by the lower and upper bounds.
-/

/-- Helper for Lemma 6.15: the nat-valued cell count `(b + 1 - a).toNat` lands at the real
endpoint `b + 1`. -/
-- Proof idea: use `hab` to remove the `Int.toNat`, recast the resulting integer identity to `ℝ`,
-- and then normalize the endpoint arithmetic.
lemma int_shifted_endpoint_cast (a b : ℤ) (hab : a ≤ b) :
    (a : ℝ) + (b + 1 - a).toNat = (b : ℝ) + 1 := by
  have hN_nonneg : 0 ≤ b + 1 - a := by linarith
  have hN_cast : ((b + 1 - a).toNat : ℤ) = b + 1 - a := by
    simp [Int.toNat_of_nonneg hN_nonneg]
  have hN_real : ((b + 1 - a).toNat : ℝ) = (b : ℝ) + 1 - a := by
    exact_mod_cast hN_cast
  linarith

/-- Helper for Lemma 6.15: after centering the unit cells, the shifted nat-valued cell count lands
at the right endpoint `b + 1 / 2`. -/
-- Proof idea: subtract `1 / 2` from the endpoint identity proved in
-- `int_shifted_endpoint_cast`.
lemma int_shifted_centered_endpoint_cast (a b : ℤ) (hab : a ≤ b) :
    (a : ℝ) - (1 / 2 : ℝ) + (b + 1 - a).toNat = (b : ℝ) + (1 / 2 : ℝ) := by
  have hendpoint := int_shifted_endpoint_cast a b hab
  linarith

/-- Helper for Lemma 6.15: rewrite the integer sample sum over `Finset.Icc a b` as a shifted sum
over `Finset.range ((b + 1 - a).toNat)`. -/
-- Proof idea: expand `Int.Icc_eq_finset_map` and simplify the cast of each translated integer
-- sample.
lemma sum_Icc_int_cast_eq_sum_range_shift (ξ : ℝ → ℝ) (a b : ℤ) :
    (∑ k ∈ Finset.Icc a b, ξ (k : ℝ)) =
      ∑ i ∈ Finset.range ((b + 1 - a).toNat), ξ ((a : ℝ) + i) := by
  rw [Int.Icc_eq_finset_map, Finset.sum_map]
  refine Finset.sum_congr rfl ?_
  intro i hi
  norm_num [Int.cast_add, add_comm, add_left_comm, add_assoc]

/-- Helper for Lemma 6.15: on a centered unit cell, convexity bounds the function from above by
the larger endpoint value. -/
-- Proof idea: apply the interval maximum principle for convex functions directly on the cell.
lemma centered_cell_upper_bound (ξ : ℝ → ℝ) (m x : ℝ)
    (hcell :
      ConvexOn ℝ (Set.Icc (m - (1 / 2 : ℝ)) (m + (1 / 2 : ℝ))) ξ)
    (hx : x ∈ Set.Icc (m - (1 / 2 : ℝ)) (m + (1 / 2 : ℝ))) :
    ξ x ≤ max (ξ (m - (1 / 2 : ℝ))) (ξ (m + (1 / 2 : ℝ))) := by
  -- The whole centered cell lies between its two endpoints, so the standard convex interval
  -- maximum principle applies without further decomposition.
  exact hcell.le_max_of_mem_Icc
    (by constructor <;> linarith)
    (by constructor <;> linarith)
    hx

/-- Helper for Lemma 6.15: on the left half of a centered unit cell, convexity gives a uniform
lower bound from the midpoint and the right endpoint. -/
-- Proof idea: compare the secant through `x,m` with the secant through `m,m+1/2`; after
-- rearranging, the midpoint and right endpoint control the whole left half.
lemma centered_cell_left_lower_bound (ξ : ℝ → ℝ) (m x : ℝ)
    (hcell :
      ConvexOn ℝ (Set.Icc (m - (1 / 2 : ℝ)) (m + (1 / 2 : ℝ))) ξ)
    (hx_left : x ∈ Set.Icc (m - (1 / 2 : ℝ)) m) :
    min (ξ m) (2 * ξ m - ξ (m + (1 / 2 : ℝ))) ≤ ξ x := by
  by_cases hxm : x = m
  · -- At the midpoint itself, the claimed lower bound is immediate.
    subst hxm
    exact min_le_left _ _
  · -- On the strict left half, the secant through `x,m` sits above the secant through
    -- `m,m + 1 / 2`, so the affine lower line through `m` and `m + 1 / 2` controls `ξ x`.
    have hxm_lt : x < m := lt_of_le_of_ne hx_left.2 hxm
    have hx_cell : x ∈ Set.Icc (m - (1 / 2 : ℝ)) (m + (1 / 2 : ℝ)) := by
      exact ⟨hx_left.1, by linarith [hx_left.2]⟩
    have hz_cell : m + (1 / 2 : ℝ) ∈ Set.Icc (m - (1 / 2 : ℝ)) (m + (1 / 2 : ℝ)) := by
      constructor <;> linarith
    have hsecant := hcell.secant_mono_aux1 hx_cell hz_cell hxm_lt (by linarith)
    let t : ℝ := 2 * (m - x)
    have ht0 : 0 ≤ t := by
      dsimp [t]
      nlinarith [hx_left.2]
    have ht1 : t ≤ 1 := by
      dsimp [t]
      nlinarith [hx_left.1]
    have hline :
        (1 - t) * ξ m + t * (2 * ξ m - ξ (m + (1 / 2 : ℝ))) ≤ ξ x := by
      dsimp [t] at *
      nlinarith
    by_cases horder : ξ m ≤ 2 * ξ m - ξ (m + (1 / 2 : ℝ))
    · -- If the midpoint value is the smaller endpoint datum, the affine lower line stays above it.
      rw [min_eq_left horder]
      have havg :
          ξ m ≤ (1 - t) * ξ m + t * (2 * ξ m - ξ (m + (1 / 2 : ℝ))) := by
        nlinarith
      exact havg.trans hline
    · -- Otherwise the reflected endpoint datum is the minimum, and the same affine line stays above
      -- that smaller value on the whole left half-cell.
      have horder' : 2 * ξ m - ξ (m + (1 / 2 : ℝ)) ≤ ξ m := le_of_not_ge horder
      rw [min_eq_right horder']
      have havg :
          2 * ξ m - ξ (m + (1 / 2 : ℝ)) ≤
            (1 - t) * ξ m + t * (2 * ξ m - ξ (m + (1 / 2 : ℝ))) := by
        nlinarith
      exact havg.trans hline

/-- Helper for Lemma 6.15: on the right half of a centered unit cell, convexity gives a uniform
lower bound from the midpoint and the left endpoint. -/
-- Proof idea: compare the secant through `m,x` with the secant through `m-1/2,m`; after
-- rearranging, the midpoint and left endpoint control the whole right half.
lemma centered_cell_right_lower_bound (ξ : ℝ → ℝ) (m x : ℝ)
    (hcell :
      ConvexOn ℝ (Set.Icc (m - (1 / 2 : ℝ)) (m + (1 / 2 : ℝ))) ξ)
    (hx_right : x ∈ Set.Icc m (m + (1 / 2 : ℝ))) :
    min (ξ m) (2 * ξ m - ξ (m - (1 / 2 : ℝ))) ≤ ξ x := by
  by_cases hxm : x = m
  · -- At the midpoint itself, the claimed lower bound is immediate.
    subst hxm
    exact min_le_left _ _
  · -- On the strict right half, the secant through `m - 1 / 2,m` sits below the secant through
    -- `m,x`, so the affine lower line through `m - 1 / 2` and `m` controls `ξ x`.
    have hmx_ne : m ≠ x := by
      intro hmx
      exact hxm hmx.symm
    have hmx_lt : m < x := lt_of_le_of_ne hx_right.1 hmx_ne
    have hx_cell : x ∈ Set.Icc (m - (1 / 2 : ℝ)) (m + (1 / 2 : ℝ)) := by
      exact ⟨by linarith [hx_right.1], hx_right.2⟩
    have hx0_cell : m - (1 / 2 : ℝ) ∈ Set.Icc (m - (1 / 2 : ℝ)) (m + (1 / 2 : ℝ)) := by
      constructor <;> linarith
    have hsecant := hcell.secant_mono_aux1 hx0_cell hx_cell (by linarith) hmx_lt
    let t : ℝ := 2 * (x - m)
    have ht0 : 0 ≤ t := by
      dsimp [t]
      nlinarith [hx_right.1]
    have ht1 : t ≤ 1 := by
      dsimp [t]
      nlinarith [hx_right.2]
    have hline :
        (1 - t) * ξ m + t * (2 * ξ m - ξ (m - (1 / 2 : ℝ))) ≤ ξ x := by
      dsimp [t] at *
      nlinarith
    by_cases horder : ξ m ≤ 2 * ξ m - ξ (m - (1 / 2 : ℝ))
    · -- If the midpoint value is the smaller endpoint datum, the affine lower line stays above it.
      rw [min_eq_left horder]
      have havg :
          ξ m ≤ (1 - t) * ξ m + t * (2 * ξ m - ξ (m - (1 / 2 : ℝ))) := by
        nlinarith
      exact havg.trans hline
    · -- Otherwise the reflected endpoint datum is the minimum, and the same affine line stays above
      -- that smaller value on the whole right half-cell.
      have horder' : 2 * ξ m - ξ (m - (1 / 2 : ℝ)) ≤ ξ m := le_of_not_ge horder
      rw [min_eq_right horder']
      have havg :
          2 * ξ m - ξ (m - (1 / 2 : ℝ)) ≤
            (1 - t) * ξ m + t * (2 * ξ m - ξ (m - (1 / 2 : ℝ))) := by
        nlinarith
      exact havg.trans hline

/-- Helper for Lemma 6.15: convexity on a centered unit cell makes the function interval
integrable there. -/
-- Proof idea: continuity on the open cell gives measurability a.e.; the previous endpoint and
-- midpoint bounds produce a uniform bound on the whole closed cell, so bounded measurable
-- functions are integrable on that finite interval.
lemma convexOn_centered_cell_intervalIntegrable (ξ : ℝ → ℝ) (m : ℝ)
    (hcell :
      ConvexOn ℝ (Set.Icc (m - (1 / 2 : ℝ)) (m + (1 / 2 : ℝ))) ξ) :
    IntervalIntegrable ξ volume (m - (1 / 2 : ℝ)) (m + (1 / 2 : ℝ)) := by
  have hab : m - (1 / 2 : ℝ) ≤ m + (1 / 2 : ℝ) := by
    linarith
  have hopen :
      ConvexOn ℝ (Set.Ioo (m - (1 / 2 : ℝ)) (m + (1 / 2 : ℝ))) ξ := by
    refine hcell.subset ?_ (convex_Ioo _ _)
    intro x hx
    exact ⟨hx.1.le, hx.2.le⟩
  -- Convexity on the open cell gives the measurability needed for the bounded-integrability route.
  have hmeas :
      AEStronglyMeasurable ξ
        (volume.restrict (Set.Ioo (m - (1 / 2 : ℝ)) (m + (1 / 2 : ℝ)))) :=
    (hopen.continuousOn isOpen_Ioo).aestronglyMeasurable measurableSet_Ioo
  let lower : ℝ :=
    min (min (ξ m) (2 * ξ m - ξ (m + (1 / 2 : ℝ))))
      (min (ξ m) (2 * ξ m - ξ (m - (1 / 2 : ℝ))))
  let upper : ℝ := max (ξ (m - (1 / 2 : ℝ))) (ξ (m + (1 / 2 : ℝ)))
  -- The endpoint and midpoint bounds from the previous helpers give a uniform bound on the open
  -- cell, which is enough because the open interval has finite volume.
  have hbounded :
      ∀ᵐ x ∂volume.restrict (Set.Ioo (m - (1 / 2 : ℝ)) (m + (1 / 2 : ℝ))),
        ‖ξ x‖ ≤ |lower| + |upper| := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
    have hx_cell : x ∈ Set.Icc (m - (1 / 2 : ℝ)) (m + (1 / 2 : ℝ)) := ⟨hx.1.le, hx.2.le⟩
    have hupper : ξ x ≤ upper := centered_cell_upper_bound ξ m x hcell hx_cell
    have hlower : lower ≤ ξ x := by
      by_cases hxm : x ≤ m
      · have hx_left : x ∈ Set.Icc (m - (1 / 2 : ℝ)) m := ⟨hx_cell.1, hxm⟩
        exact (min_le_left _ _).trans
          (centered_cell_left_lower_bound ξ m x hcell hx_left)
      · have hmx : m ≤ x := le_of_not_ge hxm
        have hx_right : x ∈ Set.Icc m (m + (1 / 2 : ℝ)) := ⟨hmx, hx_cell.2⟩
        exact (min_le_right _ _).trans
          (centered_cell_right_lower_bound ξ m x hcell hx_right)
    have hneg :
        -(|lower| + |upper|) ≤ ξ x := by
      have hbound_left : -(|lower| + |upper|) ≤ -|lower| := by
        nlinarith [abs_nonneg upper]
      exact le_trans hbound_left (le_trans (neg_abs_le lower) hlower)
    have hpos :
        ξ x ≤ |lower| + |upper| := by
      calc
        ξ x ≤ upper := hupper
        _ ≤ |upper| := le_abs_self upper
        _ ≤ |lower| + |upper| := by nlinarith [abs_nonneg lower]
    simpa [Real.norm_eq_abs] using abs_le.2 ⟨hneg, hpos⟩
  exact
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (μ := volume) (f := ξ) hab).2
      ⟨hmeas, HasFiniteIntegral.restrict_of_bounded (C := |lower| + |upper|)
        measure_Ioo_lt_top hbounded⟩

/-- Helper for Lemma 6.15: convexity on a centered unit cell bounds the midpoint by each
symmetric pair of points. -/
-- Proof idea: evaluate the defining convexity inequality at the symmetric points `m - t` and
-- `m + t` with equal weights `1 / 2`.
lemma centeredCellMidpointPairBound (ξ : ℝ → ℝ) (m t : ℝ)
    (hcell :
      ConvexOn ℝ (Set.Icc (m - (1 / 2 : ℝ)) (m + (1 / 2 : ℝ))) ξ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 2 : ℝ)) :
    2 * ξ m ≤ ξ (m - t) + ξ (m + t) := by
  have hleft : m - t ∈ Set.Icc (m - (1 / 2 : ℝ)) (m + (1 / 2 : ℝ)) := by
    constructor
    · linarith [ht.2]
    · linarith [ht.1]
  have hright : m + t ∈ Set.Icc (m - (1 / 2 : ℝ)) (m + (1 / 2 : ℝ)) := by
    constructor
    · linarith [ht.1]
    · linarith [ht.2]
  -- The midpoint is the average of the symmetric pair, so the `1 / 2, 1 / 2` convexity
  -- inequality becomes the desired two-point lower bound after clearing denominators.
  have hconv :
      ξ ((1 / 2 : ℝ) • (m - t) + (1 / 2 : ℝ) • (m + t)) ≤
        (1 / 2 : ℝ) • ξ (m - t) + (1 / 2 : ℝ) • ξ (m + t) := by
    exact hcell.2 hleft hright (by norm_num) (by norm_num) (by norm_num)
  dsimp [smul_eq_mul] at hconv
  ring_nf at hconv ⊢
  nlinarith

/-- Helper for Lemma 6.15: on a centered unit cell, the midpoint value is bounded by the cell
average. -/
-- Proof idea: integrate the two-point convexity inequality
-- `2 ξ(m) ≤ ξ(m - t) + ξ(m + t)` on `t ∈ [0, 1 / 2]`, then rewrite the two translated integrals
-- back to the left and right half-cells and merge them.
lemma midpoint_le_average_on_centered_unit_cell (ξ : ℝ → ℝ) (m : ℝ)
    (hcell :
      ConvexOn ℝ (Set.Icc (m - (1 / 2 : ℝ)) (m + (1 / 2 : ℝ))) ξ) :
    ξ m ≤ ∫ x in (m - (1 / 2 : ℝ))..(m + (1 / 2 : ℝ)), ξ x := by
  have hcell_int :
      IntervalIntegrable ξ volume (m - (1 / 2 : ℝ)) (m + (1 / 2 : ℝ)) :=
    convexOn_centered_cell_intervalIntegrable (ξ := ξ) (m := m) hcell
  have hsub_half :
      Set.uIoc (0 : ℝ) (1 / 2 : ℝ) ⊆ Set.uIoc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    rw [Set.uIoc_of_le (by norm_num), Set.uIoc_of_le (by norm_num)]
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  -- Transport the full-cell integrability to the two translated half-cell parametrizations.
  have hleft_full :
      IntervalIntegrable (fun t ↦ ξ (m - t)) volume (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    simpa using (hcell_int.comp_sub_left m).symm
  have hright_full :
      IntervalIntegrable (fun t ↦ ξ (m + t)) volume (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    simpa [add_comm] using hcell_int.comp_add_right m
  have hleft_half :
      IntervalIntegrable (fun t ↦ ξ (m - t)) volume (0 : ℝ) (1 / 2 : ℝ) :=
    hleft_full.mono_set' hsub_half
  have hright_half :
      IntervalIntegrable (fun t ↦ ξ (m + t)) volume (0 : ℝ) (1 / 2 : ℝ) :=
    hright_full.mono_set' hsub_half
  have hpair_half :
      IntervalIntegrable (fun t ↦ ξ (m - t) + ξ (m + t)) volume (0 : ℝ) (1 / 2 : ℝ) :=
    hleft_half.add hright_half
  -- Integrate the symmetric convexity inequality on `[0, 1 / 2]`.
  have hmid :
      ξ m ≤
        (∫ t in (0 : ℝ)..(1 / 2 : ℝ), ξ (m - t)) +
          ∫ t in (0 : ℝ)..(1 / 2 : ℝ), ξ (m + t) := by
    have hmono :
        ∫ t in (0 : ℝ)..(1 / 2 : ℝ), (2 * ξ m) ≤
          ∫ t in (0 : ℝ)..(1 / 2 : ℝ), (ξ (m - t) + ξ (m + t)) := by
      refine intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := (1 / 2 : ℝ))
        (f := fun _ ↦ 2 * ξ m) (g := fun t ↦ ξ (m - t) + ξ (m + t)) (by norm_num)
        ?_ hpair_half ?_
      · simp
      · intro t ht
        simpa using centeredCellMidpointPairBound (ξ := ξ) (m := m) (t := t) hcell ht
    calc
      ξ m = ∫ t in (0 : ℝ)..(1 / 2 : ℝ), (2 * ξ m) := by
        simp [intervalIntegral.integral_const]
      _ ≤ ∫ t in (0 : ℝ)..(1 / 2 : ℝ), (ξ (m - t) + ξ (m + t)) := hmono
      _ =
          (∫ t in (0 : ℝ)..(1 / 2 : ℝ), ξ (m - t)) +
            ∫ t in (0 : ℝ)..(1 / 2 : ℝ), ξ (m + t) := by
            rw [intervalIntegral.integral_add hleft_half hright_half]
  have hleft_cell :
      IntervalIntegrable ξ volume (m - (1 / 2 : ℝ)) m := by
    refine hcell_int.mono_set' ?_
    rw [Set.uIoc_of_le (by linarith), Set.uIoc_of_le (by linarith)]
    intro x hx
    exact ⟨hx.1, hx.2.trans (by linarith)⟩
  have hright_cell :
      IntervalIntegrable ξ volume m (m + (1 / 2 : ℝ)) := by
    refine hcell_int.mono_set' ?_
    rw [Set.uIoc_of_le (by linarith), Set.uIoc_of_le (by linarith)]
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  -- Rewrite the translated half-cell integrals back to the original cell and merge the adjacent
  -- intervals.
  calc
    ξ m ≤
        (∫ t in (0 : ℝ)..(1 / 2 : ℝ), ξ (m - t)) +
          ∫ t in (0 : ℝ)..(1 / 2 : ℝ), ξ (m + t) := hmid
    _ = (∫ x in (m - (1 / 2 : ℝ))..m, ξ x) + ∫ x in m..(m + (1 / 2 : ℝ)), ξ x := by
      rw [intervalIntegral.integral_comp_sub_left, intervalIntegral.integral_comp_add_left]
      simp
    _ = ∫ x in (m - (1 / 2 : ℝ))..(m + (1 / 2 : ℝ)), ξ x := by
      rw [intervalIntegral.integral_add_adjacent_intervals hleft_cell hright_cell]

/-- Helper for Lemma 6.15: each shifted integer sample is bounded by the integral over its
centered unit cell. -/
-- Proof idea: restrict the global convexity hypothesis to the centered cell indexed by `i`, then
-- apply the midpoint-versus-cell-average estimate on that cell.
lemma centered_sample_le_centered_cell_integral (ξ : ℝ → ℝ) (a b : ℤ) (hab : a ≤ b)
    (hconvex :
      ConvexOn ℝ (Set.Icc ((a : ℝ) - (1 / 2 : ℝ)) ((b : ℝ) + (1 / 2 : ℝ))) ξ)
    {i : ℕ} (hi : i < (b + 1 - a).toNat) :
    ξ ((a : ℝ) + i) ≤
      ∫ x in ((a : ℝ) - (1 / 2 : ℝ) + i)..(((a : ℝ) - (1 / 2 : ℝ)) + (i + 1)), ξ x := by
  let m : ℝ := (a : ℝ) + i
  have hi_nonneg : 0 ≤ (i : ℝ) := by positivity
  have hi_succ_le : (i : ℝ) + 1 ≤ (b + 1 - a).toNat := by
    exact_mod_cast Nat.succ_le_of_lt hi
  have hright : m + (1 / 2 : ℝ) ≤ (b : ℝ) + (1 / 2 : ℝ) := by
    have hendpoint := int_shifted_centered_endpoint_cast a b hab
    dsimp [m]
    linarith
  have hsubset :
      Set.Icc (m - (1 / 2 : ℝ)) (m + (1 / 2 : ℝ)) ⊆
        Set.Icc ((a : ℝ) - (1 / 2 : ℝ)) ((b : ℝ) + (1 / 2 : ℝ)) := by
    intro x hx
    constructor
    · -- The shifted cell starts no earlier than the global centered interval.
      have hleft : (a : ℝ) - (1 / 2 : ℝ) ≤ m - (1 / 2 : ℝ) := by
        dsimp [m]
        nlinarith
      exact hleft.trans hx.1
    · -- The shifted cell ends before the global centered interval endpoint because `i + 1 ≤ N`.
      exact hx.2.trans hright
  have hcell :
      ConvexOn ℝ (Set.Icc (m - (1 / 2 : ℝ)) (m + (1 / 2 : ℝ))) ξ :=
    hconvex.subset hsubset (convex_Icc _ _)
  -- The centered cell midpoint estimate becomes the shifted-cell integral after rewriting
  -- the endpoints around `m = a + i`.
  have hm_left : (a : ℝ) - (1 / 2 : ℝ) + i = m - (1 / 2 : ℝ) := by
    dsimp [m]
    ring
  have hm_right : (a : ℝ) - (1 / 2 : ℝ) + (i + 1) = m + (1 / 2 : ℝ) := by
    dsimp [m]
    ring
  rw [hm_left, hm_right]
  exact midpoint_le_average_on_centered_unit_cell (ξ := ξ) (m := m) hcell

/-- Helper for Lemma 6.15: the sum of centered unit-cell integrals collapses to the full centered
interval integral. -/
-- Proof idea: each summand integrates over an adjacent unit interval, so the canonical adjacent
-- interval decomposition theorem collapses the range sum to one integral.
lemma sum_centered_cell_integrals_eq_intervalIntegral (ξ : ℝ → ℝ) (a b : ℤ) (hab : a ≤ b)
    (hconvex :
      ConvexOn ℝ (Set.Icc ((a : ℝ) - (1 / 2 : ℝ)) ((b : ℝ) + (1 / 2 : ℝ))) ξ) :
    ∑ i ∈ Finset.range ((b + 1 - a).toNat),
      ∫ x in ((a : ℝ) - (1 / 2 : ℝ) + i)..(((a : ℝ) - (1 / 2 : ℝ)) + (i + 1)), ξ x
      =
    ∫ x in ((a : ℝ) - (1 / 2 : ℝ))..((b : ℝ) + (1 / 2 : ℝ)), ξ x := by
  let c : ℕ → ℝ := fun i ↦ ((a : ℝ) - (1 / 2 : ℝ)) + i
  have hint :
      ∀ k < (b + 1 - a).toNat, IntervalIntegrable ξ volume (c k) (c (k + 1)) := by
    intro k hk
    let m : ℝ := (a : ℝ) + k
    have hk_nonneg : 0 ≤ (k : ℝ) := by positivity
    have hk_succ_le : (k : ℝ) + 1 ≤ (b + 1 - a).toNat := by
      exact_mod_cast Nat.succ_le_of_lt hk
    have hright : m + (1 / 2 : ℝ) ≤ (b : ℝ) + (1 / 2 : ℝ) := by
      have hendpoint := int_shifted_centered_endpoint_cast a b hab
      dsimp [m]
      linarith
    have hsubset :
        Set.Icc (m - (1 / 2 : ℝ)) (m + (1 / 2 : ℝ)) ⊆
          Set.Icc ((a : ℝ) - (1 / 2 : ℝ)) ((b : ℝ) + (1 / 2 : ℝ)) := by
      intro x hx
      constructor
      · -- The `k`-th centered cell starts inside the global centered interval.
        have hleft : (a : ℝ) - (1 / 2 : ℝ) ≤ m - (1 / 2 : ℝ) := by
          dsimp [m]
          nlinarith
        exact hleft.trans hx.1
      · -- The `k`-th centered cell ends inside the global centered interval because `k + 1 ≤ N`.
        exact hx.2.trans hright
    have hcell :
        ConvexOn ℝ (Set.Icc (m - (1 / 2 : ℝ)) (m + (1 / 2 : ℝ))) ξ :=
      hconvex.subset hsubset (convex_Icc _ _)
    -- Each adjacent summand is exactly one centered unit cell once `m = a + k` is expanded.
    have hk_left : c k = m - (1 / 2 : ℝ) := by
      dsimp [c, m]
      ring
    have hk_right : c (k + 1) = m + (1 / 2 : ℝ) := by
      calc
        c (k + 1) = (a : ℝ) - (1 / 2 : ℝ) + k + 1 := by
          simp [c, add_assoc, add_left_comm, add_comm]
        _ = (a : ℝ) + k + (1 / 2 : ℝ) := by ring
        _ = m + (1 / 2 : ℝ) := by simp [m, add_assoc]
    rw [hk_left, hk_right]
    exact convexOn_centered_cell_intervalIntegrable (ξ := ξ) (m := m) hcell
  have hcN : c ((b + 1 - a).toNat) = (b : ℝ) + (1 / 2 : ℝ) := by
    dsimp [c]
    simpa using int_shifted_centered_endpoint_cast a b hab
  have hc0 : c 0 = (a : ℝ) - (1 / 2 : ℝ) := by
    simp [c]
  -- The range sum is a chain of adjacent unit-cell integrals, so the canonical collapse theorem
  -- reduces it to the single centered interval integral.
  have hsum :=
    intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := ξ) (a := c) hint
  rw [hc0, hcN] at hsum
  simpa [c] using hsum

/-- Lemma 6.15: if a real function is decreasing on `[a, b + 1]` and convex on
`[a - 1 / 2, b + 1 / 2]`, then the sum of its integer samples from `a` to `b` lies between the
integral over `[a, b + 1]` and the centered integral over `[a - 1 / 2, b + 1 / 2]`. -/
-- Proof sketch: the lower bound comes from applying monotonicity on each unit interval
-- `[k, k + 1]`, while the upper bound comes from convexity on each centered interval
-- `[k - 1 / 2, k + 1 / 2]` and summing the resulting midpoint estimates.
theorem sum_integer_samples_between_intervalIntegrals_of_antitoneOn_convexOn
    (ξ : ℝ → ℝ) (a b : ℤ) (hab : a ≤ b)
    (hantitone : AntitoneOn ξ (Set.Icc (a : ℝ) ((b : ℝ) + 1)))
    (hconvex :
      ConvexOn ℝ (Set.Icc ((a : ℝ) - (1 / 2 : ℝ)) ((b : ℝ) + (1 / 2 : ℝ))) ξ) :
    (∑ k ∈ Finset.Icc a b, ξ (k : ℝ)) ∈
      Set.Icc
        (∫ x in (a : ℝ)..((b : ℝ) + 1), ξ x)
        (∫ x in ((a : ℝ) - (1 / 2 : ℝ))..((b : ℝ) + (1 / 2 : ℝ)), ξ x) := by
  let N : ℕ := (b + 1 - a).toNat
  let sampleSum : ℝ := ∑ k ∈ Finset.Icc a b, ξ (k : ℝ)

  -- The nat-valued cell count reaches the right endpoint.
  have shifted_endpoint_cast : (a : ℝ) + N = (b : ℝ) + 1 := by
    simpa [N] using int_shifted_endpoint_cast a b hab

  -- Rewrite the integer-indexed sample sum as a shifted `Finset.range`.
  have sum_Icc_int_cast_eq_sum_range_shift :
      sampleSum = ∑ i ∈ Finset.range N, ξ ((a : ℝ) + i) := by
    simpa [sampleSum, N] using
      sum_Icc_int_cast_eq_sum_range_shift (ξ := ξ) (a := a) (b := b)

  rw [Set.mem_Icc]
  constructor
  · -- The lower bound follows directly from the canonical antitone sum-integral comparison.
    have hanti_shifted : AntitoneOn ξ (Set.Icc (a : ℝ) ((a : ℝ) + N)) := by
      simpa [shifted_endpoint_cast] using hantitone
    calc
      ∫ x in (a : ℝ)..((b : ℝ) + 1), ξ x
          = ∫ x in (a : ℝ)..((a : ℝ) + N), ξ x := by rw [shifted_endpoint_cast]
      _ ≤ ∑ i ∈ Finset.range N, ξ ((a : ℝ) + i) := hanti_shifted.integral_le_sum
      _ = sampleSum := sum_Icc_int_cast_eq_sum_range_shift.symm
  · -- Route correction: keep the source midpoint-cell chain instead of switching to an unrelated
    -- induction. The remaining work is the centered convex cell estimate plus the adjacent
    -- interval collapse.
    have upper_bound :
        sampleSum ≤
          ∫ x in ((a : ℝ) - (1 / 2 : ℝ))..((b : ℝ) + (1 / 2 : ℝ)), ξ x := by
      rw [sum_Icc_int_cast_eq_sum_range_shift]
      -- Each centered unit cell dominates its midpoint sample, so summing the cellwise
      -- inequalities reduces the upper bound to a chain of adjacent interval integrals.
      calc
        ∑ i ∈ Finset.range N, ξ ((a : ℝ) + i)
            ≤ ∑ i ∈ Finset.range N,
                ∫ x in ((a : ℝ) - (1 / 2 : ℝ) + i)..(((a : ℝ) - (1 / 2 : ℝ)) + (i + 1)), ξ x := by
                  refine Finset.sum_le_sum ?_
                  intro i hi
                  exact centered_sample_le_centered_cell_integral
                    (ξ := ξ) (a := a) (b := b) hab hconvex (Finset.mem_range.1 hi)
        _ = ∫ x in ((a : ℝ) - (1 / 2 : ℝ))..((b : ℝ) + (1 / 2 : ℝ)), ξ x := by
              exact sum_centered_cell_integrals_eq_intervalIntegral
                (ξ := ξ) (a := a) (b := b) hab hconvex
    simpa [sampleSum] using upper_bound
