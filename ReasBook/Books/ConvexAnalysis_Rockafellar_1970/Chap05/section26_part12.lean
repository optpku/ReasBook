/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section26_part11

section Chap05
section Section26

attribute [local instance] Classical.propDecidable
open scoped ConvexAnalysis Pointwise

/-- Helper for Example 26.2.1: outside the effective domain, the piecewise formula has no
subgradients because the base value is `+∞` while the origin still has finite value. -/
lemma helperForExample_26_2_1_subgradient_empty_off_effectiveDomain
    {x : Fin 2 → ℝ}
    (hx : x ∉ effectiveDomain (Set.univ : Set (Fin 2 → ℝ)) quadraticOverLinearMinusSqrtFunction) :
    subdifferentialAt quadraticOverLinearMinusSqrtFunction x = ∅ := by
  rcases helperForExample_26_2_1_effectiveDomain_and_axisValues with ⟨hdom, _haxis⟩
  refine Set.eq_empty_iff_forall_notMem.2 ?_
  intro g hg
  have hxTop : quadraticOverLinearMinusSqrtFunction x = (⊤ : EReal) := by
    have hxOutside :
        x ∉ {x | 0 < x 0 ∧ 0 ≤ x 1} ∪ ({0} : Set (Fin 2 → ℝ)) := by
      intro hxUnion
      exact hx (by simpa [hdom] using hxUnion)
    by_cases hbranch : 0 < x 0 ∧ 0 ≤ x 1
    · exact False.elim (hxOutside (Or.inl hbranch))
    · by_cases hxZero : x = 0
      · exact False.elim (hxOutside (Or.inr hxZero))
      · simp [quadraticOverLinearMinusSqrtFunction, hbranch, hxZero]
  have hzeroSub := hg (0 : Fin 2 → ℝ)
  have hzeroVal : quadraticOverLinearMinusSqrtFunction (0 : Fin 2 → ℝ) = (0 : EReal) := by
    simp [quadraticOverLinearMinusSqrtFunction]
  have htopLe : (⊤ : EReal) ≤ (0 : EReal) := by
    simpa [hxTop, hzeroVal] using hzeroSub
  exact not_top_le_coe 0 htopLe

/-- Helper for Example 26.2.1: the small perturbation `x + (t^3, t^2)` forces the subgradient
inequality to fail at every point of the nonnegative `ξ₁`-axis, so the boundary fiber is empty. -/
lemma helperForExample_26_2_1_axis_subgradient_empty_smallT
    {x : Fin 2 → ℝ} (hx : x ∈ nonnegativeXi1AxisR2) :
    subdifferentialAt quadraticOverLinearMinusSqrtFunction x = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 ?_
  intro g hg
  let a : ℝ := g ![1, 0]
  let b : ℝ := g ![0, 1]
  let M : ℝ := |a| + |b| + 1
  let t : ℝ := min 1 (1 / (4 * M))
  have hMpos : 0 < M := by
    dsimp [M]
    positivity
  have ht_pos : 0 < t := by
    dsimp [t]
    apply lt_min
    · norm_num
    · positivity
  have ht_le_one : t ≤ 1 := by
    dsimp [t]
    exact min_le_left _ _
  have ht_le_bound : t ≤ 1 / (4 * M) := by
    dsimp [t]
    exact min_le_right _ _
  have hxValue :
      quadraticOverLinearMinusSqrtFunction x = (0 : EReal) :=
    helperForExample_26_2_1_value_on_nonnegativeXi1Axis hx
  have hineq :=
    hg (x + ![t ^ 3, t ^ 2])
  have hperturbValue :
      quadraticOverLinearMinusSqrtFunction (x + ![t ^ 3, t ^ 2]) =
        (((t ^ 4 / (2 * (x 0 + t ^ 3)) - 2 * t : ℝ)) : EReal) :=
    helperForExample_26_2_1_axisPerturbation_value hx ht_pos
  have hsub :
      (x + ![t ^ 3, t ^ 2]) - x = (![t ^ 3, t ^ 2] : Fin 2 → ℝ) := by
    ext i
    fin_cases i
    · change Matrix.vecHead x + t ^ 3 - x 0 = t ^ 3
      have hx0' : Matrix.vecHead x = x 0 := rfl
      simp [hx0']
    · change Matrix.vecHead (Matrix.vecTail x) + t ^ 2 - x 1 = t ^ 2
      have hx1' : Matrix.vecHead (Matrix.vecTail x) = x 1 := rfl
      simp [hx1']
  have hineqReal :
      g (![t ^ 3, t ^ 2] : Fin 2 → ℝ) ≤ t ^ 4 / (2 * (x 0 + t ^ 3)) - 2 * t := by
    have hineqE :
        (((g (![t ^ 3, t ^ 2] : Fin 2 → ℝ) : ℝ)) : EReal) ≤
          quadraticOverLinearMinusSqrtFunction (x + ![t ^ 3, t ^ 2]) := by
      have hineq' := hineq
      simpa [hxValue, hsub, add_comm, add_left_comm, add_assoc] using hineq'
    rw [hperturbValue] at hineqE
    exact_mod_cast hineqE
  have hvec :
      (![t ^ 3, t ^ 2] : Fin 2 → ℝ) = t ^ 3 • ![1, 0] + t ^ 2 • ![0, 1] := by
    ext i
    fin_cases i <;> simp [pow_succ, mul_comm, mul_left_comm, mul_assoc]
  have hgVec :
      g (![t ^ 3, t ^ 2] : Fin 2 → ℝ) = a * t ^ 3 + b * t ^ 2 := by
    -- Expanding in the standard basis turns the affine support term into a polynomial in `t`.
    rw [hvec, map_add, map_smul, map_smul]
    dsimp [a, b]
    ring
  have ht_sq_nonneg : 0 ≤ t ^ 2 := sq_nonneg t
  have ht3_le_t2 : t ^ 3 ≤ t ^ 2 := by
    nlinarith [ht_pos, ht_le_one]
  have hsum_le_Mt2 :
      |a| * t ^ 3 + |b| * t ^ 2 ≤ M * t ^ 2 := by
    dsimp [M]
    nlinarith [abs_nonneg a, abs_nonneg b]
  have hMt_le_quarter : M * t ≤ (1 / 4 : ℝ) := by
    have h :
        4 * M * t ≤ 4 * M * (1 / (4 * M)) := by
      exact mul_le_mul_of_nonneg_left ht_le_bound (by positivity)
    have hEq : 4 * M * (1 / (4 * M)) = 1 := by
      field_simp [hMpos.ne']
    nlinarith [h]
  have hMt2_le_tquarter : M * t ^ 2 ≤ t / 4 := by
    calc
      M * t ^ 2 = (M * t) * t := by ring
      _ ≤ (1 / 4 : ℝ) * t := by
        exact mul_le_mul_of_nonneg_right hMt_le_quarter ht_pos.le
      _ = t / 4 := by ring
  have ht3_nonneg : 0 ≤ t ^ 3 := by positivity
  have habs_sum :
      |a * t ^ 3 + b * t ^ 2| ≤ |a| * t ^ 3 + |b| * t ^ 2 := by
    have htri : |a * t ^ 3 + b * t ^ 2| ≤ |a * t ^ 3| + |b * t ^ 2| :=
      abs_add_le _ _
    calc
      |a * t ^ 3 + b * t ^ 2| ≤ |a * t ^ 3| + |b * t ^ 2| := htri
      _ = |a| * t ^ 3 + |b| * t ^ 2 := by
        rw [abs_mul, abs_mul]
        simp [abs_of_nonneg, ht_sq_nonneg, ht3_nonneg]
  have habsPoly :
      |a * t ^ 3 + b * t ^ 2| ≤ t / 4 := by
    calc
      |a * t ^ 3 + b * t ^ 2| ≤ |a| * t ^ 3 + |b| * t ^ 2 := habs_sum
      _ ≤ M * t ^ 2 := hsum_le_Mt2
      _ ≤ t / 4 := hMt2_le_tquarter
  have hpolyLower :
      -(t / 4) ≤ a * t ^ 3 + b * t ^ 2 := by
    calc
      -(t / 4) ≤ -|a * t ^ 3 + b * t ^ 2| := by
        nlinarith [habsPoly]
      _ ≤ a * t ^ 3 + b * t ^ 2 := neg_abs_le _
  have hfrac_le : t ^ 4 / (2 * (x 0 + t ^ 3)) ≤ t / 2 := by
    rcases hx with ⟨hx0, _hx1⟩
    have hnum_le : t ^ 4 ≤ t * (x 0 + t ^ 3) := by
      nlinarith [hx0, ht_pos.le]
    have hden_pos : 0 < 2 * (x 0 + t ^ 3) := by
      have ht3_pos : 0 < t ^ 3 := by positivity
      positivity
    refine (div_le_iff₀ hden_pos).2 ?_
    nlinarith [hnum_le]
  have hleftUpper :
      t ^ 4 / (2 * (x 0 + t ^ 3)) - 2 * t ≤ -(3 / 2 : ℝ) * t := by
    nlinarith [hfrac_le]
  have hcontradiction :
      -(t / 4) ≤ -(3 / 2 : ℝ) * t := by
    rw [hgVec] at hineqReal
    exact le_trans hpolyLower (le_trans hineqReal hleftUpper)
  have : (5 / 4 : ℝ) * t ≤ 0 := by
    nlinarith [hcontradiction]
  linarith [ht_pos]

/-- Helper for Example 26.2.1: the already-proved exterior and axis exclusions show that every
point with nonempty subdifferential must lie in the open positive quadrant. -/
lemma helperForExample_26_2_1_subdifferentialEffectiveDomain_subset_openQuadrant :
    subdifferentialEffectiveDomain quadraticOverLinearMinusSqrtFunction ⊆
      openPositiveQuadrantR2 := by
  rcases helperForExample_26_2_1_effectiveDomain_and_axisValues with ⟨hdom, _haxis⟩
  intro x hxSub
  by_cases hxEff :
      x ∈ effectiveDomain (Set.univ : Set (Fin 2 → ℝ)) quadraticOverLinearMinusSqrtFunction
  · have hxUnion : x ∈ {x | 0 < x 0 ∧ 0 ≤ x 1} ∪ ({0} : Set (Fin 2 → ℝ)) := by
        simpa [hdom] using hxEff
    rcases hxUnion with hxBranch | hxZero
    · rcases hxBranch with ⟨hx0, hx1nonneg⟩
      by_cases hx1pos : 0 < x 1
      · exact ⟨hx0, hx1pos⟩
      · have hxAxis : x ∈ nonnegativeXi1AxisR2 := by
          refine ⟨le_of_lt hx0, ?_⟩
          exact le_antisymm (not_lt.mp hx1pos) hx1nonneg
        have hEmpty :
            subdifferentialAt quadraticOverLinearMinusSqrtFunction x = ∅ :=
          helperForExample_26_2_1_axis_subgradient_empty_smallT hxAxis
        exact False.elim (hxSub hEmpty)
    · have hxAxis : x ∈ nonnegativeXi1AxisR2 := by
        rw [Set.mem_singleton_iff] at hxZero
        subst hxZero
        simp [nonnegativeXi1AxisR2]
      have hEmpty :
          subdifferentialAt quadraticOverLinearMinusSqrtFunction x = ∅ :=
        helperForExample_26_2_1_axis_subgradient_empty_smallT hxAxis
      exact False.elim (hxSub hEmpty)
  · have hEmpty :
        subdifferentialAt quadraticOverLinearMinusSqrtFunction x = ∅ :=
      helperForExample_26_2_1_subgradient_empty_off_effectiveDomain hxEff
    exact False.elim (hxSub hEmpty)

/-- Helper for Example 26.2.1: positive convex combinations of open-quadrant points stay in the
open positive quadrant. -/
lemma helperForExample_26_2_1_openQuadrant_combo_mem
    {x y : Fin 2 → ℝ} (hx : x ∈ openPositiveQuadrantR2) (hy : y ∈ openPositiveQuadrantR2)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    a • x + b • y ∈ openPositiveQuadrantR2 := by
  rcases hx with ⟨hx0, hx1⟩
  rcases hy with ⟨hy0, hy1⟩
  constructor
  · -- Both first coordinates stay strictly positive under a positive convex combination.
    have : 0 < a * x 0 + b * y 0 := by
      nlinarith
    simpa [smul_eq_mul] using this
  · -- The same positivity argument applies to the second coordinate.
    have : 0 < a * x 1 + b * y 1 := by
      nlinarith
    simpa [smul_eq_mul] using this

/-- Helper for Example 26.2.1: the quadratic-over-linear part satisfies its convexity inequality
on positive convex combinations inside the open quadrant. -/
lemma helperForExample_26_2_1_quadraticOverLinear_real_convex_combo
    {x y : Fin 2 → ℝ} (hx : x ∈ openPositiveQuadrantR2) (hy : y ∈ openPositiveQuadrantR2)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    (((a • x + b • y) 1) ^ 2 / (2 * ((a • x + b • y) 0)) : ℝ) ≤
      a * (x 1 ^ 2 / (2 * x 0)) + b * (y 1 ^ 2 / (2 * y 0)) := by
  rcases hx with ⟨hx0, _hx1⟩
  rcases hy with ⟨hy0, _hy1⟩
  have hnotbot :
      ∀ ξ ∈ (Set.univ : Set (Fin 2 → ℝ)), quadraticOverLinearEReal ξ ≠ ⊥ := by
    intro ξ _
    by_cases hξ : 0 < ξ 0
    · -- On the positive branch `quadraticOverLinearEReal` is a finite real number.
      simp [quadraticOverLinearEReal, hξ]
    · by_cases hzero : ξ 0 = 0 ∧ ξ 1 = 0
      · -- At the origin the exceptional branch is still finite.
        simp [quadraticOverLinearEReal, hξ, hzero]
      · -- Away from the positive branch and the origin the value is `+∞`, never `⊥`.
        simp [quadraticOverLinearEReal, hξ, hzero]
  have hsegment :=
    (convexFunctionOn_iff_segment_inequality
      (C := (Set.univ : Set (Fin 2 → ℝ))) (f := quadraticOverLinearEReal)
      convex_univ hnotbot).1 convexFunctionOn_quadraticOverLinearEReal
  have hb_lt_one : b < 1 := by
    linarith
  have hz0 : 0 < a * x 0 + b * y 0 := by
    nlinarith
  have hsegmentE := hsegment x (by simp) y (by simp) b hb hb_lt_one
  have hab' : 1 - b = a := by
    linarith
  rw [hab'] at hsegmentE
  have hrealE :
      ((((a * x 1 + b * y 1) ^ 2 / (2 * (a * x 0 + b * y 0)) : ℝ)) : EReal) ≤
        (((a * (x 1 ^ 2 / (2 * x 0)) + b * (y 1 ^ 2 / (2 * y 0)) : ℝ)) : EReal) := by
    -- Rewrite the extended-real convexity inequality on the positive branch back to real data.
    simpa [quadraticOverLinearEReal, hx0, hy0, hz0, smul_eq_mul] using hsegmentE
  exact_mod_cast hrealE

/-- Helper for Example 26.2.1: for fixed positive `ξ₂ = c`, the map
`ξ₁ ↦ c^2 / (2 ξ₁)` is strictly convex on `(0, ∞)`. -/
lemma helperForExample_26_2_1_fixedSecondCoordinate_strictConvex_firstCoordinate
    {u v c a b : ℝ} (hu : 0 < u) (hv : 0 < v) (hc : 0 < c) (huv : u ≠ v)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    c ^ 2 / (2 * (a * u + b * v)) <
      a * (c ^ 2 / (2 * u)) + b * (c ^ 2 / (2 * v)) := by
  have hdiff :
      a * (c ^ 2 / (2 * u)) + b * (c ^ 2 / (2 * v)) - c ^ 2 / (2 * (a * u + b * v)) =
        c ^ 2 * (a * b * (u - v) ^ 2) / (2 * u * v * (a * u + b * v)) := by
    have hsum_ne : 2 * (a * u + b * v) ≠ 0 := by
      positivity
    field_simp [hu.ne', hv.ne', hsum_ne]
    have hab' : b = 1 - a := by
      linarith
    rw [hab']
    ring_nf
  have hsq : 0 < (u - v) ^ 2 := by
    exact sq_pos_of_ne_zero (sub_ne_zero.mpr huv)
  have hgt :
      0 <
        a * (c ^ 2 / (2 * u)) + b * (c ^ 2 / (2 * v)) -
          c ^ 2 / (2 * (a * u + b * v)) := by
    rw [hdiff]
    have hden : 0 < 2 * u * v * (a * u + b * v) := by
      positivity
    have hnum : 0 < c ^ 2 * (a * b * (u - v) ^ 2) := by
      have hc_sq : 0 < c ^ 2 := by positivity
      have hab_pos : 0 < a * b := mul_pos ha hb
      exact mul_pos hc_sq (mul_pos hab_pos hsq)
    exact div_pos hnum hden
  linarith

/-- Helper for Example 26.2.1: the textbook two-case argument yields strict convexity of the
real branch on the open positive quadrant. -/
lemma helperForExample_26_2_1_strictConvexOn_openQuadrant :
    StrictConvexOn ℝ openPositiveQuadrantR2
      (fun x => (quadraticOverLinearMinusSqrtFunction x).toReal) := by
  refine ⟨?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    rcases hx with ⟨hx0, hx1⟩
    rcases hy with ⟨hy0, hy1⟩
    constructor
    · -- Convexity only needs nonnegative weights, and positivity of the endpoints is preserved.
      have hxTerm : 0 ≤ a * x 0 := mul_nonneg ha hx0.le
      have hyTerm : 0 ≤ b * y 0 := mul_nonneg hb hy0.le
      by_cases ha0 : a = 0
      · have hb1 : b = 1 := by linarith
        simpa [smul_eq_mul, ha0, hb1] using hy0
      · have haPos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        have hxTermPos : 0 < a * x 0 := mul_pos haPos hx0
        have : 0 < a * x 0 + b * y 0 := add_pos_of_pos_of_nonneg hxTermPos hyTerm
        simpa [smul_eq_mul] using this
    · have : 0 < a * x 1 + b * y 1 := by
        have hxTerm : 0 ≤ a * x 1 := mul_nonneg ha hx1.le
        have hyTerm : 0 ≤ b * y 1 := mul_nonneg hb hy1.le
        by_cases ha0 : a = 0
        · have hb1 : b = 1 := by linarith
          simpa [smul_eq_mul, ha0, hb1] using hy1
        · have haPos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
          have hxTermPos : 0 < a * x 1 := mul_pos haPos hx1
          exact add_pos_of_pos_of_nonneg hxTermPos hyTerm
      simpa [smul_eq_mul] using this
  · intro x hx y hy hxy a b ha hb hab
    let z : Fin 2 → ℝ := a • x + b • y
    have hz : z ∈ openPositiveQuadrantR2 :=
      helperForExample_26_2_1_openQuadrant_combo_mem hx hy ha hb hab
    have hxReal :
        (quadraticOverLinearMinusSqrtFunction x).toReal =
          x 1 ^ 2 / (2 * x 0) - 2 * Real.sqrt (x 1) := by
      -- Inside the open quadrant the `EReal` value is represented by the explicit real formula.
      simpa using congrArg EReal.toReal (helperForExample_26_2_1_value_on_openQuadrant hx)
    have hyReal :
        (quadraticOverLinearMinusSqrtFunction y).toReal =
          y 1 ^ 2 / (2 * y 0) - 2 * Real.sqrt (y 1) := by
      -- The same branch reduction applies at the second endpoint.
      simpa using congrArg EReal.toReal (helperForExample_26_2_1_value_on_openQuadrant hy)
    have hzReal :
        (quadraticOverLinearMinusSqrtFunction z).toReal =
          z 1 ^ 2 / (2 * z 0) - 2 * Real.sqrt (z 1) := by
      -- The midpoint stays in the open quadrant, so we again use the real branch.
      simpa using congrArg EReal.toReal (helperForExample_26_2_1_value_on_openQuadrant hz)
    by_cases hsecond : x 1 = y 1
    · have hfirst : x 0 ≠ y 0 := by
        intro h0
        apply hxy
        ext i
        fin_cases i
        · simpa using h0
        · simpa [hsecond]
      have hz1 : z 1 = x 1 := by
        calc
          z 1 = a * x 1 + b * y 1 := by
            simp [z, smul_eq_mul]
          _ = a * x 1 + b * x 1 := by rw [hsecond]
          _ = (a + b) * x 1 := by ring
          _ = x 1 := by rw [hab]; ring
      have hquad :
          z 1 ^ 2 / (2 * z 0) <
            a * (x 1 ^ 2 / (2 * x 0)) + b * (y 1 ^ 2 / (2 * y 0)) := by
        rcases hx with ⟨hx0, hx1⟩
        rcases hy with ⟨hy0, _hy1⟩
        -- When the second coordinates agree, strictness comes from the `ξ₁`-dependence alone.
        simpa [z, hz1, hsecond, smul_eq_mul] using
          helperForExample_26_2_1_fixedSecondCoordinate_strictConvex_firstCoordinate
            hx0 hy0 hx1 hfirst ha hb hab
      -- The shared `-2 √ξ₂` term cancels, leaving the strict first-coordinate inequality.
      change (quadraticOverLinearMinusSqrtFunction z).toReal <
          a * (quadraticOverLinearMinusSqrtFunction x).toReal +
            b * (quadraticOverLinearMinusSqrtFunction y).toReal
      rw [hxReal, hyReal, hzReal]
      have hySqrt : Real.sqrt (y 1) = Real.sqrt (x 1) := by rw [hsecond]
      have hzSqrt :
          Real.sqrt (z 1) = Real.sqrt (x 1) := by
        rw [hz1]
      rw [hySqrt, hzSqrt]
      have hright :
          a * (x 1 ^ 2 / (2 * x 0) - 2 * Real.sqrt (x 1)) +
              b * (y 1 ^ 2 / (2 * y 0) - 2 * Real.sqrt (x 1)) =
            (a * (x 1 ^ 2 / (2 * x 0)) + b * (y 1 ^ 2 / (2 * y 0))) -
              2 * Real.sqrt (x 1) := by
        calc
          a * (x 1 ^ 2 / (2 * x 0) - 2 * Real.sqrt (x 1)) +
              b * (y 1 ^ 2 / (2 * y 0) - 2 * Real.sqrt (x 1)) =
            (a * (x 1 ^ 2 / (2 * x 0)) + b * (y 1 ^ 2 / (2 * y 0))) -
              (a + b) * (2 * Real.sqrt (x 1)) := by
                ring
          _ =
            (a * (x 1 ^ 2 / (2 * x 0)) + b * (y 1 ^ 2 / (2 * y 0))) -
              2 * Real.sqrt (x 1) := by
                rw [hab]
                ring
      rw [hright]
      exact sub_lt_sub_right hquad (2 * Real.sqrt (x 1))
    · have hsqrt :
          -2 * Real.sqrt (z 1) <
            a * (-2 * Real.sqrt (x 1)) + b * (-2 * Real.sqrt (y 1)) := by
        rcases hx with ⟨_hx0, hx1⟩
        rcases hy with ⟨_hy0, hy1⟩
        have hsqrtBase := Real.strictConcaveOn_sqrt.2 hx1.le hy1.le hsecond ha hb hab
        have hsqrtScaled :
            2 * (a * Real.sqrt (x 1) + b * Real.sqrt (y 1)) < 2 * Real.sqrt (z 1) := by
          simpa [z, smul_eq_mul] using
            mul_lt_mul_of_pos_left hsqrtBase (by norm_num : 0 < (2 : ℝ))
        have hsqrtNeg :
            -(2 * Real.sqrt (z 1)) < -(2 * (a * Real.sqrt (x 1) + b * Real.sqrt (y 1))) := by
          exact neg_lt_neg hsqrtScaled
        ring_nf at hsqrtNeg ⊢
        linarith
      have hquad :
          z 1 ^ 2 / (2 * z 0) ≤
            a * (x 1 ^ 2 / (2 * x 0)) + b * (y 1 ^ 2 / (2 * y 0)) :=
        helperForExample_26_2_1_quadraticOverLinear_real_convex_combo hx hy ha hb hab
      -- In the genuinely two-dimensional case, the strictness is supplied by the `-2 √ξ₂` term.
      change (quadraticOverLinearMinusSqrtFunction z).toReal <
          a * (quadraticOverLinearMinusSqrtFunction x).toReal +
            b * (quadraticOverLinearMinusSqrtFunction y).toReal
      rw [hxReal, hyReal, hzReal]
      linarith

end Section26
end Chap05
