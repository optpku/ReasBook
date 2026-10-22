/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.Extr
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_34

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

/- Proposition 3.35 is `source-facing`: its primitive data are the entropy-linear objective and
the resulting softmax point. The `core/canonical` owner declarations remain the simplex
`stdSimplex ℝ (Fin n)`, the multiplier condition `IsStdSimplexMultiplier`, and the
optimality criterion `isMinOn_stdSimplex_iff_exists_subgradient_vector_and_multiplier` from
Corollary 3.33. This file therefore keeps only the concrete source objective and its canonical
optimizer, without introducing a parallel wrapper for simplex optimality. -/
-- Semantic recall: leansearch confirmed `stdSimplex` as the canonical mathlib owner for the
-- simplex constraint used here.

section

variable {n : ℕ}

/-- The softmax point attached to `y`, with coordinates `exp (y i)` normalized to sum to `1`. -/
def softmax_point (y : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ Real.exp (y i) / ∑ j, Real.exp (y j)

/-- The entropy-linear objective
`x ↦ ∑ i, x i * log (x i) - ∑ i, y i * x i` on `ℝ^n`, modeled as `Fin n → ℝ`. -/
def entropy_linear_objective (y x : Fin n → ℝ) : ℝ :=
  ∑ i, x i * Real.log (x i) - ∑ i, y i * x i

/-- Every coordinate of the softmax point is strictly positive. -/
theorem softmax_point_pos (y : Fin n → ℝ) (i : Fin n) :
    0 < softmax_point y i := by
  have hdenom_pos : 0 < ∑ j, Real.exp (y j) := by
    refine lt_of_lt_of_le (Real.exp_pos (y i)) ?_
    exact Finset.single_le_sum (fun j _ ↦ le_of_lt (Real.exp_pos (y j))) (by simp)
  exact div_pos (Real.exp_pos (y i)) hdenom_pos

/-- The coordinates of the softmax point sum to `1` whenever `Fin n` is nonempty. -/
@[simp] theorem sum_softmax_point [NeZero n] (y : Fin n → ℝ) :
    ∑ i, softmax_point y i = 1 := by
  let i : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
  have hsum_pos : 0 < ∑ j, Real.exp (y j) := by
    refine lt_of_lt_of_le (Real.exp_pos (y i)) ?_
    exact Finset.single_le_sum (fun j _ ↦ le_of_lt (Real.exp_pos (y j))) (by simp)
  calc
    ∑ j, softmax_point y j = (∑ j, Real.exp (y j)) * (∑ j, Real.exp (y j))⁻¹ := by
      simp [softmax_point, div_eq_mul_inv, Finset.sum_mul]
    _ = 1 := by
      rw [mul_inv_cancel₀ hsum_pos.ne']

/-- For `n ≠ 0`, the softmax point is a point of the standard simplex `stdSimplex ℝ (Fin n)`. -/
theorem softmax_point_mem_stdSimplex [NeZero n] (y : Fin n → ℝ) :
    softmax_point y ∈ stdSimplex ℝ (Fin n) := by
  refine ⟨fun i ↦ le_of_lt (softmax_point_pos y i), sum_softmax_point y⟩

/-- Adding the same constant to every softmax weight does not change the normalized point. -/
theorem softmax_point_add_const (y : Fin n → ℝ) (c : ℝ) :
    softmax_point (fun i ↦ y i + c) = softmax_point y := by
  funext i
  calc
    softmax_point (fun j ↦ y j + c) i
        = (Real.exp (y i) * Real.exp c) / ((∑ j, Real.exp (y j)) * Real.exp c) := by
            simp [softmax_point, Real.exp_add, Finset.sum_mul]
    _ = softmax_point y i := by
      rw [mul_div_mul_right _ _ (Real.exp_ne_zero c), softmax_point]

/-- Helper for Proposition 3.35: a simplex point over `Fin n` forces `n ≠ 0`. -/
lemma neZero_of_mem_stdSimplex {x : Fin n → ℝ} (hx : x ∈ stdSimplex ℝ (Fin n)) : NeZero n := by
  obtain ⟨i, hi⟩ := exists_pos_of_mem_stdSimplex (xStar := x) hx
  have hn_pos : 0 < n := lt_of_lt_of_le (Nat.succ_pos i.1) (Nat.succ_le_of_lt i.2)
  exact ⟨Nat.pos_iff_ne_zero.mp hn_pos⟩

/-- Helper for Proposition 3.35: each softmax coordinate has logarithm
`y i - log (∑ j, exp (y j))`. -/
lemma softmax_point_log (y : Fin n → ℝ) (i : Fin n) :
    Real.log (softmax_point y i) = y i - Real.log (∑ j, Real.exp (y j)) := by
  -- Expand the normalized coordinate and simplify the logarithms of `exp` and the denominator.
  have hsum_pos : 0 < ∑ j, Real.exp (y j) := by
    refine lt_of_lt_of_le (Real.exp_pos (y i)) ?_
    exact Finset.single_le_sum (fun j _ ↦ le_of_lt (Real.exp_pos (y j))) (by simp)
  rw [show softmax_point y i = Real.exp (y i) / ∑ j, Real.exp (y j) by rfl]
  rw [Real.log_div (Real.exp_ne_zero _) hsum_pos.ne', Real.log_exp]

/-- Helper for Proposition 3.35: evaluating `entropy_linear_objective y` at the softmax point
produces the normalized log-partition value `-log (∑ j, exp (y j))`. -/
lemma entropyLinearObjective_softmax_eq_negLogSumExp [NeZero n] (y : Fin n → ℝ) :
    entropy_linear_objective y (softmax_point y) = -Real.log (∑ j, Real.exp (y j)) := by
  -- Rewrite each softmax logarithm by the normalization identity and use that softmax sums to `1`.
  calc
    entropy_linear_objective y (softmax_point y)
        = ∑ i, softmax_point y i * Real.log (softmax_point y i) -
            ∑ i, softmax_point y i * y i := by
            simp [entropy_linear_objective, mul_comm]
    _ = ∑ i, (softmax_point y i * Real.log (softmax_point y i) - softmax_point y i * y i) := by
          rw [Finset.sum_sub_distrib]
    _ = ∑ i, softmax_point y i * (Real.log (softmax_point y i) - y i) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          ring
    _ = ∑ i, softmax_point y i * (-Real.log (∑ j, Real.exp (y j))) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [softmax_point_log (y := y) i]
          ring
    _ = (∑ i, softmax_point y i) * (-Real.log (∑ j, Real.exp (y j))) := by
          rw [Finset.sum_mul]
    _ = -Real.log (∑ j, Real.exp (y j)) := by
          simp

/-- Helper for Proposition 3.35: the softmax objective gap is the weighted logarithmic ratio
`∑ i, x i * log (softmax_point y i / x i)`. -/
lemma entropyLinearObjective_softmaxGap_eq_sumLogRatio
    (y x : Fin n → ℝ) (hx : x ∈ stdSimplex ℝ (Fin n)) :
    entropy_linear_objective y (softmax_point y) - entropy_linear_objective y x =
      ∑ i, x i * Real.log (softmax_point y i / x i) := by
  letI : NeZero n := neZero_of_mem_stdSimplex hx
  set Z : ℝ := ∑ j, Real.exp (y j) with hZ
  -- Convert the softmax value to the log-partition form, then collect the simplex weights.
  calc
    entropy_linear_objective y (softmax_point y) - entropy_linear_objective y x
        = -Real.log Z - (∑ i, x i * Real.log (x i) - ∑ i, y i * x i) := by
            rw [entropyLinearObjective_softmax_eq_negLogSumExp (y := y), entropy_linear_objective,
              hZ]
    _ = (∑ i, x i) * (-Real.log Z) - (∑ i, x i * Real.log (x i) - ∑ i, y i * x i) := by
          rw [hx.2]
          ring
    _ = ∑ i, x i * (-Real.log Z) - (∑ i, x i * Real.log (x i) - ∑ i, y i * x i) := by
          rw [Finset.sum_mul]
    _ = ∑ i, x i * (-Real.log Z) - ∑ i, x i * Real.log (x i) + ∑ i, y i * x i := by
          ring
    _ = ∑ i, (x i * (-Real.log Z) - x i * Real.log (x i)) + ∑ i, y i * x i := by
          rw [← Finset.sum_sub_distrib]
    _ = ∑ i, (x i * (-Real.log Z) - x i * Real.log (x i) + y i * x i) := by
          rw [← Finset.sum_add_distrib]
    _ = ∑ i, x i * (-Real.log Z - Real.log (x i) + y i) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          ring
    _ = ∑ i, x i * Real.log (softmax_point y i / x i) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          by_cases hxi : x i = 0
          · simp [hxi]
          · rw [Real.log_div (softmax_point_pos y i).ne' hxi, softmax_point_log (y := y) i, hZ]
            ring

/-- Helper for Proposition 3.35: the weighted logarithmic softmax ratio is the logarithm of the
weighted geometric mean `∏ i, (softmax_point y i / x i) ^ (x i)`. -/
lemma softmaxRatio_logProd_eq_sumLogRatio
    (y x : Fin n → ℝ) (hx : x ∈ stdSimplex ℝ (Fin n)) :
    Real.log (∏ i, (softmax_point y i / x i) ^ x i) =
      ∑ i, x i * Real.log (softmax_point y i / x i) := by
  -- Every positive-weight ratio is positive, while zero-weight coordinates contribute `log 1 = 0`.
  rw [Real.log_prod]
  · refine Finset.sum_congr rfl ?_
    intro i _
    by_cases hxi : x i = 0
    · simp [hxi]
    · have hxi_pos : 0 < x i := lt_of_le_of_ne (hx.1 i) (Ne.symm hxi)
      have hratio_pos : 0 < softmax_point y i / x i := div_pos (softmax_point_pos y i) hxi_pos
      rw [Real.log_rpow hratio_pos]
  · intro i _
    by_cases hxi : x i = 0
    · simp [hxi]
    · have hxi_pos : 0 < x i := lt_of_le_of_ne (hx.1 i) (Ne.symm hxi)
      exact (Real.rpow_pos_of_pos (div_pos (softmax_point_pos y i) hxi_pos) _).ne'

/-- Helper for Proposition 3.35: the arithmetic mean of the softmax ratios never exceeds `1`
on the simplex. -/
lemma softmaxRatio_arithMean_le_one
    (y x : Fin n → ℝ) (hx : x ∈ stdSimplex ℝ (Fin n)) :
    ∑ i, x i * (softmax_point y i / x i) ≤ 1 := by
  letI : NeZero n := neZero_of_mem_stdSimplex hx
  have hterm_eq : ∀ i : Fin n, x i ≠ 0 → x i * (softmax_point y i / x i) = softmax_point y i := by
    intro i hxi
    -- A nonzero simplex weight cancels from the corresponding softmax ratio term.
    calc
      x i * (softmax_point y i / x i)
          = (x i * (x i)⁻¹) * softmax_point y i := by
              rw [div_eq_mul_inv]
              ac_rfl
      _ = softmax_point y i := by
            rw [mul_inv_cancel₀ hxi, one_mul]
  -- Compare the weighted arithmetic mean termwise with the full softmax sum.
  calc
    ∑ i, x i * (softmax_point y i / x i) ≤ ∑ i, softmax_point y i := by
      refine Finset.sum_le_sum ?_
      intro i _
      by_cases hxi : x i = 0
      · simp [hxi, le_of_lt (softmax_point_pos y i)]
      · simpa [hterm_eq i hxi]
    _ = 1 := sum_softmax_point y

-- Proof sketch: identify the softmax objective gap with a weighted logarithmic ratio, bound its
-- weighted geometric mean by its weighted arithmetic mean via AM-GM, and then use the simplex
-- normalization to show that the arithmetic mean is at most `1`.
/-- Helper for Proposition 3.35: the softmax point minimizes `entropy_linear_objective y` on the
standard simplex. -/
lemma entropyLinearObjective_softmax_le
    (y x : Fin n → ℝ) (hx : x ∈ stdSimplex ℝ (Fin n)) :
    entropy_linear_objective y (softmax_point y) ≤ entropy_linear_objective y x := by
  letI : NeZero n := neZero_of_mem_stdSimplex hx
  let z : Fin n → ℝ := fun i ↦ softmax_point y i / x i
  have hz_nonneg : ∀ i ∈ Finset.univ, 0 ≤ z i := by
    intro i _
    by_cases hxi : x i = 0
    · simp [z, hxi]
    · exact div_nonneg (le_of_lt (softmax_point_pos y i)) (hx.1 i)
  have hgeom_le :
      ∏ i, z i ^ x i ≤ ∑ i, x i * z i := by
    exact Real.geom_mean_le_arith_mean_weighted (s := Finset.univ) x z
      (fun i _ ↦ hx.1 i) hx.2 hz_nonneg
  have hprod_pos : 0 < ∏ i, z i ^ x i := by
    refine Finset.prod_pos ?_
    intro i _
    by_cases hxi : x i = 0
    · simp [z, hxi]
    · have hxi_pos : 0 < x i := lt_of_le_of_ne (hx.1 i) (Ne.symm hxi)
      exact Real.rpow_pos_of_pos (div_pos (softmax_point_pos y i) hxi_pos) _
  have hprod_le_one : ∏ i, z i ^ x i ≤ 1 := by
    calc
      ∏ i, z i ^ x i ≤ ∑ i, x i * z i := hgeom_le
      _ ≤ 1 := by
            simpa [z] using softmaxRatio_arithMean_le_one (y := y) (x := x) hx
  have hgap_nonpos :
      entropy_linear_objective y (softmax_point y) - entropy_linear_objective y x ≤ 0 := by
    -- Convert the KL-type gap to a logarithm of the weighted geometric mean and bound it by `0`.
    rw [entropyLinearObjective_softmaxGap_eq_sumLogRatio (y := y) (x := x) hx,
      ← softmaxRatio_logProd_eq_sumLogRatio (y := y) (x := x) hx]
    simpa using Real.log_le_log hprod_pos hprod_le_one
  exact sub_nonpos.mp hgap_nonpos

-- Proof sketch: equality in the softmax minimizer inequality forces equality in both the weighted
-- AM-GM step and the arithmetic-mean upper bound, so every simplex coordinate must be positive and
-- every softmax ratio must equal `1`.
/-- Helper for Proposition 3.35: a simplex point with the same objective value as the softmax
point must equal that softmax point. -/
lemma eq_softmax_of_memStdSimplex_of_entropyLinearObjective_eq_softmax
    (y x : Fin n → ℝ) (hx : x ∈ stdSimplex ℝ (Fin n))
    (heq : entropy_linear_objective y x = entropy_linear_objective y (softmax_point y)) :
    x = softmax_point y := by
  letI : NeZero n := neZero_of_mem_stdSimplex hx
  let z : Fin n → ℝ := fun i ↦ softmax_point y i / x i
  have hz_nonneg : ∀ i ∈ Finset.univ, 0 ≤ z i := by
    intro i _
    by_cases hxi : x i = 0
    · simp [z, hxi]
    · exact div_nonneg (le_of_lt (softmax_point_pos y i)) (hx.1 i)
  have hterm_eq : ∀ i : Fin n, x i ≠ 0 → x i * z i = softmax_point y i := by
    intro i hxi
    -- A nonzero simplex coordinate cancels from the corresponding softmax ratio.
    calc
      x i * z i = (x i * (x i)⁻¹) * softmax_point y i := by
        dsimp [z]
        rw [div_eq_mul_inv]
        ac_rfl
      _ = softmax_point y i := by
        rw [mul_inv_cancel₀ hxi, one_mul]
  have hgeom_le :
      ∏ i, z i ^ x i ≤ ∑ i, x i * z i := by
    exact Real.geom_mean_le_arith_mean_weighted (s := Finset.univ) x z
      (fun i _ ↦ hx.1 i) hx.2 hz_nonneg
  have hprod_pos : 0 < ∏ i, z i ^ x i := by
    refine Finset.prod_pos ?_
    intro i _
    by_cases hxi : x i = 0
    · simp [z, hxi]
    · have hxi_pos : 0 < x i := lt_of_le_of_ne (hx.1 i) (Ne.symm hxi)
      exact Real.rpow_pos_of_pos (div_pos (softmax_point_pos y i) hxi_pos) _
  have hgap_zero : ∑ i, x i * Real.log (softmax_point y i / x i) = 0 := by
    -- The objective values coincide, so the softmax gap vanishes exactly.
    rw [← entropyLinearObjective_softmaxGap_eq_sumLogRatio (y := y) (x := x) hx, heq, sub_self]
  have hprod_eq_one : ∏ i, z i ^ x i = 1 := by
    apply Real.eq_one_of_pos_of_log_eq_zero hprod_pos
    rw [softmaxRatio_logProd_eq_sumLogRatio (y := y) (x := x) hx]
    simpa [z] using hgap_zero
  have harith_eq_one : ∑ i, x i * z i = 1 := by
    refine le_antisymm ?_ ?_
    · simpa [z] using softmaxRatio_arithMean_le_one (y := y) (x := x) hx
    · calc
        1 = ∏ i, z i ^ x i := hprod_eq_one.symm
        _ ≤ ∑ i, x i * z i := hgeom_le
  have hgeom_eq :
      ∏ i, z i ^ x i = ∑ i, x i * z i := by
    rw [hprod_eq_one, harith_eq_one]
  have hz_eq_one : ∀ i : Fin n, x i ≠ 0 → z i = 1 := by
    intro i hxi
    have hconst :=
      (Real.geom_mean_eq_arith_mean_weighted_iff (s := Finset.univ) x z
        (fun j _ ↦ hx.1 j) hx.2 hz_nonneg).mp hgeom_eq i (by simp) hxi
    simpa [z, harith_eq_one] using hconst
  have hx_nonzero : ∀ i : Fin n, x i ≠ 0 := by
    intro i
    by_contra hxi
    have harith_lt : ∑ j, x j * z j < 1 := by
      let s : Finset (Fin n) := Finset.univ.erase i
      have hsum_erase_raw :
          s.sum (fun j ↦ x j * z j) + x i * z i = ∑ j, x j * z j := by
        dsimp [s]
        simpa using
          (Finset.sum_erase_add (s := Finset.univ) (f := fun j ↦ x j * z j) i (Finset.mem_univ i))
      have hsum_erase : (∑ j, x j * z j) = s.sum (fun j ↦ x j * z j) := by
        rw [← hsum_erase_raw]
        simp [z, hxi]
      have hsoft_sum_raw :
          s.sum (fun j ↦ softmax_point y j) + softmax_point y i = ∑ j, softmax_point y j := by
        dsimp [s]
        simpa using
          (Finset.sum_erase_add (s := Finset.univ) (f := fun j ↦ softmax_point y j) i
            (Finset.mem_univ i))
      calc
        ∑ j, x j * z j = s.sum (fun j ↦ x j * z j) := hsum_erase
        _ ≤ s.sum (fun j ↦ softmax_point y j) := by
          refine Finset.sum_le_sum ?_
          intro j hj
          by_cases hxj : x j = 0
          · simp [z, hxj, le_of_lt (softmax_point_pos y j)]
          · simpa [hterm_eq j hxj]
        _ < 1 := by
          calc
            s.sum (fun j ↦ softmax_point y j)
                < s.sum (fun j ↦ softmax_point y j) + softmax_point y i := by
                    linarith [softmax_point_pos y i]
            _ = ∑ j, softmax_point y j := by
                  exact hsoft_sum_raw
            _ = 1 := sum_softmax_point y
    have : ¬ ((∑ j, x j * z j) < 1) := by
      simpa [harith_eq_one]
    exact this harith_lt
  -- Every coordinate has positive weight, so the AM-GM equality condition forces each ratio to be `1`.
  ext i
  have hxi : x i ≠ 0 := hx_nonzero i
  have hcoord : softmax_point y i = x i := by
    have hcoord' : softmax_point y i = 1 * x i := by
      exact (div_eq_iff hxi).mp (by simpa [z] using hz_eq_one i hxi)
    simpa using hcoord'
  exact hcoord.symm

-- Proof sketch: apply the chapter owner criterion
-- `isMinOn_stdSimplex_iff_exists_subgradient_vector_and_multiplier` to the entropy-linear
-- objective, use the entropy singularity at the boundary to rule out zero coordinates of `xstar`,
-- and then collapse the multiplier condition to the stationarity equations
-- `log (xstar i) + 1 - y i = μ`. Exponentiating yields
-- `xstar i = α * exp (y i)` for a constant `α`, and the simplex constraint `∑ i, xstar i = 1`
-- determines `α = (∑ j, exp (y j))⁻¹`.
/-- Any minimizer of `entropy_linear_objective y` on `stdSimplex ℝ (Fin n)` has strictly positive
coordinates. -/
theorem isMinOn_stdSimplex_entropyLinearObjective_pos
    (y xstar : Fin n → ℝ)
    (hxstar_mem : xstar ∈ stdSimplex ℝ (Fin n))
    (hmin : IsMinOn (entropy_linear_objective y) (stdSimplex ℝ (Fin n)) xstar) :
    ∀ i, 0 < xstar i := by
  letI : NeZero n := neZero_of_mem_stdSimplex hxstar_mem
  have hsoft_mem : softmax_point y ∈ stdSimplex ℝ (Fin n) := softmax_point_mem_stdSimplex y
  have hsoft_le :
      entropy_linear_objective y (softmax_point y) ≤ entropy_linear_objective y xstar :=
    entropyLinearObjective_softmax_le (y := y) (x := xstar) hxstar_mem
  have hmin' := isMinOn_iff.mp hmin
  have hxstar_le :
      entropy_linear_objective y xstar ≤ entropy_linear_objective y (softmax_point y) :=
    hmin' _ hsoft_mem
  have hsoft_eq : xstar = softmax_point y :=
    eq_softmax_of_memStdSimplex_of_entropyLinearObjective_eq_softmax (y := y) (x := xstar)
      hxstar_mem (le_antisymm hxstar_le hsoft_le)
  -- Identify the minimizer with the softmax point, then read off coordinate positivity.
  intro i
  simpa [hsoft_eq] using softmax_point_pos y i

/-- Proposition 3.35: if `xstar` is a strictly positive minimizer of
`entropy_linear_objective y`, equivalently
`x ↦ ∑ i, x i * log (x i) - ∑ i, y i * x i`, on the unit simplex
`Δ_n = stdSimplex ℝ (Fin n)`, then `xstar` is the softmax point `softmax_point y`. -/
theorem eq_softmax_of_isMinOn_stdSimplex_entropyLinearObjective
    (y xstar : Fin n → ℝ)
    (hxstar_mem : xstar ∈ stdSimplex ℝ (Fin n))
    (hxstar_pos : ∀ i, 0 < xstar i)
    (hmin : IsMinOn (entropy_linear_objective y) (stdSimplex ℝ (Fin n)) xstar) :
    xstar = softmax_point y := by
  let _ := hxstar_pos
  letI : NeZero n := neZero_of_mem_stdSimplex hxstar_mem
  have hsoft_mem : softmax_point y ∈ stdSimplex ℝ (Fin n) := softmax_point_mem_stdSimplex y
  have hsoft_le :
      entropy_linear_objective y (softmax_point y) ≤ entropy_linear_objective y xstar :=
    entropyLinearObjective_softmax_le (y := y) (x := xstar) hxstar_mem
  have hmin' := isMinOn_iff.mp hmin
  have hxstar_le :
      entropy_linear_objective y xstar ≤ entropy_linear_objective y (softmax_point y) :=
    hmin' _ hsoft_mem
  -- The positivity hypothesis is compatible with the stronger equality-case argument on the simplex.
  exact eq_softmax_of_memStdSimplex_of_entropyLinearObjective_eq_softmax (y := y) (x := xstar)
    hxstar_mem (le_antisymm hxstar_le hsoft_le)

/-- Companion corollary: the stronger local API can recover the textbook positivity premise
from simplex optimality before applying Proposition 3.35. -/
theorem eq_softmax_of_mem_stdSimplex_and_isMinOn_stdSimplex_entropyLinearObjective
    (y xstar : Fin n → ℝ)
    (hxstar_mem : xstar ∈ stdSimplex ℝ (Fin n))
    (hmin : IsMinOn (entropy_linear_objective y) (stdSimplex ℝ (Fin n)) xstar) :
    xstar = softmax_point y := by
  -- First recover positivity from optimality, then invoke the textbook softmax characterization.
  exact
    eq_softmax_of_isMinOn_stdSimplex_entropyLinearObjective (y := y) (xstar := xstar)
      hxstar_mem
      (isMinOn_stdSimplex_entropyLinearObjective_pos (y := y) (xstar := xstar) hxstar_mem hmin)
      hmin

end
