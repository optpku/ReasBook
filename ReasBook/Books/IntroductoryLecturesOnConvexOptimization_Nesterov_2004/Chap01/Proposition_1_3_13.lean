/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Lipschitz
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_12

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory intervalIntegral

/- Proposition 1.3.13 lies in the one-dimensional interval-integral / Lipschitz-Riemann-sum
domain.

Sampled owner-style declarations:
* `uniformGridRiemannSum` in `Definition_1_3_12`, the chapter owner for the source-facing
  right-endpoint sampled sum
* `∫ x in (0 : ℝ)..1, f x`, the canonical `intervalIntegral` owner for the exact quantity on
  `[0, 1]`
* `LipschitzOnWith`, the canonical mathlib owner for the Lipschitz hypothesis on `[0, 1]`
* `intervalIntegral.sum_integral_adjacent_intervals`, the canonical cell-decomposition API for the
  proof route behind the estimate

Best owner abstraction:
* source-facing: the approximation error between `∫ x in (0 : ℝ)..1, f x` and the right-endpoint
  uniform-grid Riemann sum on `[0, 1]`
* core/canonical: `uniformGridRiemannSum f N` together with the canonical interval-integral and
  Lipschitz owners already used in the statement
* bridge/view: the explicit finite-sum formula for `uniformGridRiemannSum`, already owned by
  `uniformGridRiemannSum_def`

Primitive data:
* `f : ℝ → ℝ`
* `L : NNReal`
* `N : ℕ+`
* `hLip : LipschitzOnWith L f (Set.Icc (0 : ℝ) 1)`

Derived API:
* the sharp error estimate `|(∫_0^1 f) - uniformGridRiemannSum f N| ≤ L / (2N)`
* the epsilon corollary obtained from the sharp estimate and a numerical lower bound on `N`

This file is already at the right abstraction level: Proposition 1.3.13 is a genuine
source-facing estimate, not a duplicate wrapper around an upstream owner theorem. The refinement is
therefore limited to keeping that owner theorem pair and factoring the shared context once. -/

section

variable (f : ℝ → ℝ) (L : NNReal) (N : ℕ+)
variable (hLip : LipschitzOnWith L f (Set.Icc (0 : ℝ) 1))

include hLip

/-- Helper for Proposition 1.3.13: rewrite the global quadrature error as a sum of cellwise
interval integrals over the uniform partition. -/
-- Proof idea: decompose `∫_0^1 f` into adjacent intervals, unfold the sampled sum, and rewrite
-- each cell contribution by subtracting the corresponding constant right-endpoint sample.
lemma uniformGridRiemannSum_error_eq_sum_cell_integrals :
    (∫ x in (0 : ℝ)..1, f x) - uniformGridRiemannSum f N =
      ∑ i ∈ Finset.range (N : ℕ), ∫ x in (i : ℝ) / N..((i + 1 : ℝ) / N),
        (f x - f ((i + 1 : ℝ) / N)) := by
  have hN_pos : 0 < (N : ℝ) := by
    exact_mod_cast N.pos
  have hcell_int : ∀ k < (N : ℕ), IntervalIntegrable f volume ((k : ℝ) / N) (((k + 1 : ℝ) / N)) := by
    intro k hk
    refine ((LipschitzOnWith.continuousOn hLip).mono ?_).intervalIntegrable_of_Icc ?_
    · exact Set.Icc_subset_Icc (by positivity) (by
        have hk' : (k + 1 : ℝ) ≤ N := by
          exact_mod_cast Nat.succ_le_of_lt hk
        exact (div_le_iff₀ hN_pos).2 (by simpa using hk'))
    · exact div_le_div_of_nonneg_right (by
        exact_mod_cast Nat.le_succ k) (le_of_lt hN_pos)
  let a : ℕ → ℝ := fun k => (k : ℝ) / N
  have hpartition :
      ∑ k ∈ Finset.range (N : ℕ), ∫ x in (k : ℝ) / N..((k + 1 : ℝ) / N), f x
        = ∫ x in (0 : ℝ)..1, f x := by
    -- First split the integral into the adjacent uniform cells.
    rw [show (∑ k ∈ Finset.range (N : ℕ), ∫ x in (k : ℝ) / N..((k + 1 : ℝ) / N), f x)
        = ∑ k ∈ Finset.range (N : ℕ), ∫ x in a k..a (k + 1), f x by
          simp [a]]
    rw [sum_integral_adjacent_intervals (a := a)]
    · simp [a]
    · intro k hk
      simpa [a] using hcell_int k hk
  -- Then match each cell integral against the sampled value at the right endpoint.
  rw [← hpartition, uniformGridRiemannSum_def, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hf_cell := hcell_int i (by simpa using hi)
  have hconst_cell :
      IntervalIntegrable (fun _ : ℝ ↦ f ((i + 1 : ℝ) / N)) volume ((i : ℝ) / N) (((i + 1 : ℝ) / N)) := by
    simp
  rw [intervalIntegral.integral_sub hf_cell hconst_cell, intervalIntegral.integral_const]
  ring

/-- Helper for Proposition 1.3.13: on each cell, the Lipschitz condition bounds the integrand by
the distance to the right endpoint. -/
-- Proof idea: place both points in `[0, 1]`, apply the Lipschitz estimate, and simplify the
-- resulting distance because points in the cell lie to the left of the right endpoint.
lemma abs_cell_integrand_le_right_endpoint_distance {i : ℕ} (hi : i < (N : ℕ)) {x : ℝ}
    (hx : x ∈ Set.Icc ((i : ℝ) / N) (((i + 1 : ℝ) / N))) :
    |f x - f ((i + 1 : ℝ) / N)| ≤ (L : ℝ) * ((((i + 1 : ℝ) / N) - x)) := by
  have hN_pos : 0 < (N : ℝ) := by
    exact_mod_cast N.pos
  have hx_unit : x ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact le_trans (by positivity) hx.1
    · have hupper : (((i + 1 : ℝ) / N) : ℝ) ≤ 1 := by
        have hi' : (i + 1 : ℝ) ≤ N := by
          exact_mod_cast Nat.succ_le_of_lt hi
        exact (div_le_iff₀ hN_pos).2 (by simpa using hi')
      exact le_trans hx.2 hupper
  have hright_unit : ((i + 1 : ℝ) / N : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · have hi' : (i + 1 : ℝ) ≤ N := by
        exact_mod_cast Nat.succ_le_of_lt hi
      exact (div_le_iff₀ hN_pos).2 (by simpa using hi')
  have hdist := LipschitzOnWith.dist_le_mul hLip x hx_unit ((i + 1 : ℝ) / N) hright_unit
  have hdist' : |f x - f ((i + 1 : ℝ) / N)| ≤ (L : ℝ) * |x - ((i + 1 : ℝ) / N)| := by
    simpa [Real.dist_eq] using hdist
  simpa [abs_of_nonpos (sub_nonpos.mpr hx.2)] using hdist'

/-- Helper for Proposition 1.3.13: the integral of the distance-to-right-endpoint profile on one
uniform cell equals the corresponding triangle area. -/
-- Proof idea: integrate the affine function by splitting it into a constant part minus `x`, then
-- normalize the resulting expression algebraically.
lemma integral_right_endpoint_minus_id_eq_half_inv_sq {i : ℕ} :
    ∫ x in (i : ℝ) / N..((i + 1 : ℝ) / N), (((i + 1 : ℝ) / N) - x) = 1 / (2 * (N : ℝ)^2) := by
  have hN_ne : (N : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt N.pos
  rw [intervalIntegral.integral_sub]
  · rw [intervalIntegral.integral_const, integral_id]
    have hstep : (((i + 1 : ℝ) / N) - ((i : ℝ) / N)) = 1 / (N : ℝ) := by
      field_simp [hN_ne]
      ring
    have hsquare : (((i + 1 : ℝ) / N) ^ 2 - ((i : ℝ) / N) ^ 2) = (2 * i + 1 : ℝ) / (N : ℝ)^2 := by
      field_simp [hN_ne]
      ring
    rw [hstep, hsquare]
    simp [smul_eq_mul]
    field_simp [hN_ne]
    ring
  · simp
  · exact continuousOn_id.intervalIntegrable

/-- Helper for Proposition 1.3.13: each cell contributes at most `L / (2 N^2)` to the absolute
quadrature error. -/
-- Proof idea: bound the absolute value of the cell integral by the integral of the absolute value,
-- compare pointwise with the Lipschitz triangle profile, and evaluate that profile exactly.
lemma cell_error_le_half_l_over_N_sq {i : ℕ} (hi : i < (N : ℕ)) :
    |∫ x in (i : ℝ) / N..((i + 1 : ℝ) / N), (f x - f ((i + 1 : ℝ) / N))|
      ≤ (L : ℝ) / (2 * (N : ℝ)^2) := by
  have hN_pos : 0 < (N : ℝ) := by
    exact_mod_cast N.pos
  have hcont_cell : ContinuousOn (fun x : ℝ ↦ f x - f ((i + 1 : ℝ) / N))
      (Set.Icc ((i : ℝ) / N) (((i + 1 : ℝ) / N))) := by
    exact ((LipschitzOnWith.continuousOn hLip).mono (Set.Icc_subset_Icc (by positivity) (by
      have hi' : (i + 1 : ℝ) ≤ N := by
        exact_mod_cast Nat.succ_le_of_lt hi
      exact (div_le_iff₀ hN_pos).2 (by simpa using hi')))).sub continuousOn_const
  have hcell_int : IntervalIntegrable (fun x : ℝ ↦ f x - f ((i + 1 : ℝ) / N)) volume
      ((i : ℝ) / N) (((i + 1 : ℝ) / N)) :=
    hcont_cell.intervalIntegrable_of_Icc
      (div_le_div_of_nonneg_right (by
        exact_mod_cast Nat.le_succ i) (le_of_lt hN_pos))
  have hab : ((i : ℝ) / N : ℝ) ≤ ((i + 1 : ℝ) / N : ℝ) := by
    exact div_le_div_of_nonneg_right (by
      exact_mod_cast Nat.le_succ i) (le_of_lt hN_pos)
  have habs := intervalIntegral.abs_integral_le_integral_abs (μ := volume)
    (f := fun x : ℝ ↦ f x - f ((i + 1 : ℝ) / N)) hab
  have hmono :
      ∫ x in (i : ℝ) / N..((i + 1 : ℝ) / N), |f x - f ((i + 1 : ℝ) / N)|
        ≤ ∫ x in (i : ℝ) / N..((i + 1 : ℝ) / N), (L : ℝ) * ((((i + 1 : ℝ) / N) - x)) := by
    -- The Lipschitz estimate gives a pointwise majorant on the entire cell.
    refine intervalIntegral.integral_mono_on hab ?_ ?_ ?_
    · exact hcell_int.abs
    · exact (continuousOn_const.mul (continuousOn_const.sub continuousOn_id)).intervalIntegrable_of_Icc hab
    · intro x hx
      exact abs_cell_integrand_le_right_endpoint_distance f L N hLip hi (by simpa using hx)
  calc
    |∫ x in (i : ℝ) / N..((i + 1 : ℝ) / N), (f x - f ((i + 1 : ℝ) / N))|
      ≤ ∫ x in (i : ℝ) / N..((i + 1 : ℝ) / N), |f x - f ((i + 1 : ℝ) / N)| := habs
    _ ≤ ∫ x in (i : ℝ) / N..((i + 1 : ℝ) / N), (L : ℝ) * ((((i + 1 : ℝ) / N) - x)) := hmono
    _ = (L : ℝ) / (2 * (N : ℝ)^2) := by
      rw [intervalIntegral.integral_const_mul, integral_right_endpoint_minus_id_eq_half_inv_sq f L N hLip (i := i)]
      ring_nf

/-- Proposition 1.3.13: If `f` is Lipschitz on `[0, 1]` with constant `L`, then the right-endpoint
uniform-grid Riemann sum with `N` subintervals approximates the integral over `[0, 1]` with error
at most `L / (2 N)`. -/
-- Proof sketch: partition `[0, 1]` into the intervals `[(i - 1) / N, i / N]`, rewrite the
-- difference between the integral and the Riemann sum as a sum of cellwise integrals, bound each
-- integrand by the Lipschitz estimate against the right endpoint `i / N`, and compute the
-- resulting triangular-area integral on each cell.
theorem abs_intervalIntegral_sub_uniformGridRiemannSum_le
    :
    |(∫ x in (0 : ℝ)..1, f x) - uniformGridRiemannSum f N| ≤ (L : ℝ) / (2 * (N : ℝ)) := by
  -- Rewrite the global error as the sum of the cellwise errors from the textbook proof.
  rw [uniformGridRiemannSum_error_eq_sum_cell_integrals f L N hLip]
  calc
    |∑ i ∈ Finset.range (N : ℕ), ∫ x in (i : ℝ) / N..((i + 1 : ℝ) / N),
        (f x - f ((i + 1 : ℝ) / N))|
      ≤ ∑ i ∈ Finset.range (N : ℕ),
          |∫ x in (i : ℝ) / N..((i + 1 : ℝ) / N), (f x - f ((i + 1 : ℝ) / N))| := by
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (N : ℕ), (L : ℝ) / (2 * (N : ℝ)^2) := by
        -- Each cell is controlled by the same triangular-area bound.
        refine Finset.sum_le_sum fun i hi ↦ ?_
        exact cell_error_le_half_l_over_N_sq f L N hLip (by simpa using hi)
    _ = (N : ℝ) * ((L : ℝ) / (2 * (N : ℝ)^2)) := by
        simp [Finset.sum_const]
    _ = (L : ℝ) / (2 * (N : ℝ)) := by
        have hN_ne : (N : ℝ) ≠ 0 := by
          exact_mod_cast Nat.ne_of_gt N.pos
        field_simp [hN_ne]

/-- If `N` is at least `L / (2 ε)`, then the uniform-grid Riemann sum error is at most `ε`. -/
-- Proof sketch: combine `abs_intervalIntegral_sub_uniformGridRiemannSum_le` with the numerical
-- inequality `(L : ℝ) / (2 * (N : ℝ)) ≤ ε`, which follows from the lower bound
-- `(L : ℝ) / (2 * ε) ≤ N` when `ε > 0`.
theorem abs_intervalIntegral_sub_uniformGridRiemannSum_le_eps
    {ε : ℝ} (hε : 0 < ε)
    (hNε : (L : ℝ) / (2 * ε) ≤ (N : ℝ)) :
    |(∫ x in (0 : ℝ)..1, f x) - uniformGridRiemannSum f N| ≤ ε := by
  have hL_nonneg : 0 ≤ (L : ℝ) := L.2
  have hbound : (L : ℝ) / (2 * (N : ℝ)) ≤ ε := by
    -- Convert the lower bound on `N` into the target denominator estimate.
    have hN_pos : 0 < (N : ℝ) := by
      exact_mod_cast N.pos
    have hmul : (L : ℝ) ≤ (N : ℝ) * (2 * ε) := by
      have htwoeps_pos : 0 < 2 * ε := by
        positivity
      have := mul_le_mul_of_nonneg_right hNε (le_of_lt htwoeps_pos)
      have htwoeps_ne : (2 * ε) ≠ 0 := by
        positivity
      rw [div_mul_cancel₀ _ htwoeps_ne] at this
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    have htwoN_pos : 0 < 2 * (N : ℝ) := by
      positivity
    exact (div_le_iff₀ htwoN_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)
  have hmain := abs_intervalIntegral_sub_uniformGridRiemannSum_le (f := f) (L := L) (N := N) hLip
  exact hmain.trans hbound

end
