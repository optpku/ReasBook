/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_14
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-
Proposition 3.31 is `source-facing` at the possible-median predicate for an indexed finite sample
and the unit-weight one-dimensional Fermat-Weber objective. The public owner for that objective is
already `fermatWeberObjective` from Definition 3.14, so the textbook sum `x ↦ ∑ i, |x - a i|` is
only a `bridge/view` description here rather than a second objective wrapper. The `core/canonical`
owner in this domain is `IsMinOn` for global minimizers. On the median side, the primitive
counting predicate remains local here, because the earlier chapter owner `median_set` is defined
on `Finset ℝ` and would erase sample multiplicities through `Finset.image`; a named set-valued
companion is still useful for downstream reuse of the indexed notion.
-/

recall IsMinOn
recall fermatWeberObjective
recall fermatWeberObjective_one_apply_eq_sum_abs

/-- A real number is a possible median of a finite real sample when at least half of the sample
lies on each side of it, counted with multiplicity. -/
def IsPossibleMedian (a : Fin n → ℝ) (x : ℝ) : Prop :=
  2 * (Finset.univ.filter fun i ↦ a i ≤ x).card ≥ n ∧
    2 * (Finset.univ.filter fun i ↦ x ≤ a i).card ≥ n

/-- The set of possible medians of an indexed finite real sample, counted with multiplicity. -/
def possibleMedianSet (a : Fin n → ℝ) : Set ℝ :=
  {x | IsPossibleMedian a x}

/-- Membership in `possibleMedianSet a` is exactly the possible-median predicate. -/
@[simp] theorem mem_possibleMedianSet {a : Fin n → ℝ} {x : ℝ} :
    x ∈ possibleMedianSet a ↔ IsPossibleMedian a x :=
  Iff.rfl

/-- The defining inequalities for a possible sample median. -/
@[simp] theorem isPossibleMedian_iff {a : Fin n → ℝ} {x : ℝ} :
    IsPossibleMedian a x ↔
      2 * (Finset.univ.filter fun i ↦ a i ≤ x).card ≥ n ∧
        2 * (Finset.univ.filter fun i ↦ x ≤ a i).card ≥ n :=
  Iff.rfl

/-- Helper for Proposition 3.31: the indices with `a i ≤ x` and the indices with `x < a i`
partition `Fin n`. -/
lemma card_filter_le_add_card_filter_gt (a : Fin n → ℝ) (x : ℝ) :
    (Finset.univ.filter fun i ↦ a i ≤ x).card +
      (Finset.univ.filter fun i ↦ x < a i).card =
        n := by
  classical
  simpa [not_le] using
    (Finset.univ.card_filter_add_card_filter_not fun i : Fin n ↦ a i ≤ x)

/-- Helper for Proposition 3.31: the indices with `a i < x` and the indices with `x ≤ a i`
partition `Fin n`. -/
lemma card_filter_lt_add_card_filter_ge (a : Fin n → ℝ) (x : ℝ) :
    (Finset.univ.filter fun i ↦ a i < x).card +
      (Finset.univ.filter fun i ↦ x ≤ a i).card =
        n := by
  classical
  simpa [not_lt] using
    (Finset.univ.card_filter_add_card_filter_not fun i : Fin n ↦ a i < x)

/-- Helper for Proposition 3.31: if `t ≤ x ≤ y`, then moving from `x` to `y` increases
`|· - t|` by exactly `y - x`. -/
lemma abs_sub_sub_eq_of_le_left {t x y : ℝ} (htx : t ≤ x) (hxy : x ≤ y) :
    |y - t| - |x - t| = y - x := by
  -- On this side of `t`, both absolute values drop to ordinary differences.
  have hyt : t ≤ y := le_trans htx hxy
  simp [abs_of_nonneg (sub_nonneg.mpr hyt), abs_of_nonneg (sub_nonneg.mpr htx)]

/-- Helper for Proposition 3.31: if `y ≤ x ≤ t`, then moving from `x` to `y` increases
`|· - t|` by exactly `x - y`. -/
lemma abs_sub_sub_eq_of_le_right {t x y : ℝ} (hyx : y ≤ x) (hxt : x ≤ t) :
    |y - t| - |x - t| = x - y := by
  -- On this side of `t`, both absolute values drop to reversed differences.
  have hyt : y ≤ t := le_trans hyx hxt
  simp [abs_of_nonpos (sub_nonpos.mpr hyt), abs_of_nonpos (sub_nonpos.mpr hxt)]

/-- Helper for Proposition 3.31: if `x` is a possible median, then moving to the right cannot
decrease the total absolute deviation. -/
lemma sumAbsDifferenceNonneg_of_isPossibleMedian_right
    (a : Fin n → ℝ) (x y : ℝ) (hx : IsPossibleMedian a x) (hxy : x ≤ y) :
    0 ≤ ∑ i : Fin n, (|y - a i| - |x - a i|) := by
  let left := Finset.univ.filter fun i : Fin n ↦ a i ≤ x
  let right := Finset.univ.filter fun i : Fin n ↦ x < a i
  -- The median inequality controls the block counts after partitioning the sample.
  have hxleft : 2 * left.card ≥ n := by
    simpa [left] using hx.1
  have hcount : right.card ≤ left.card := by
    have hpart : left.card + right.card = n := by
      simpa [left, right] using card_filter_le_add_card_filter_gt a x
    omega
  have hsplit :
      ∑ i : Fin n, (|y - a i| - |x - a i|) =
        Finset.sum left (fun i : Fin n ↦ |y - a i| - |x - a i|) +
          Finset.sum right (fun i : Fin n ↦ |y - a i| - |x - a i|) := by
    simpa [left, right, not_le] using
      (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun i : Fin n ↦ a i ≤ x) (fun i : Fin n ↦ |y - a i| - |x - a i|)).symm
  have hleft :
      Finset.sum left (fun i : Fin n ↦ |y - a i| - |x - a i|) = (left.card : ℝ) * (y - x) := by
    -- On the left block, the absolute value stays on the same linear branch.
    calc
      Finset.sum left (fun i : Fin n ↦ |y - a i| - |x - a i|) =
          Finset.sum left (fun _ : Fin n ↦ y - x) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        exact abs_sub_sub_eq_of_le_left (Finset.mem_filter.mp hi).2 hxy
      _ = (left.card : ℝ) * (y - x) := by
        simp
        ring
  have hright :
      (right.card : ℝ) * (-(y - x)) ≤
        Finset.sum right (fun i : Fin n ↦ |y - a i| - |x - a i|) := by
    -- On the complementary block, the reverse triangle inequality gives a uniform lower bound.
    calc
      (right.card : ℝ) * (-(y - x)) = Finset.sum right (fun _ : Fin n ↦ -(y - x)) := by
        simp
        ring
      _ ≤ Finset.sum right (fun i : Fin n ↦ |y - a i| - |x - a i|) := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have habs := abs_sub_abs_le_abs_sub (x - a i) (y - a i)
        have hterm : |x - a i| - |y - a i| ≤ y - x := by
          calc
            |x - a i| - |y - a i| ≤ |(x - a i) - (y - a i)| := habs
            _ = |x - y| := by
              ring_nf
            _ = y - x := by
              rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
              ring
        linarith
  have hbase :
      0 ≤ (left.card : ℝ) * (y - x) + (right.card : ℝ) * (-(y - x)) := by
    have hcountReal : (right.card : ℝ) ≤ left.card := by
      exact_mod_cast hcount
    have hstep : 0 ≤ y - x := sub_nonneg.mpr hxy
    nlinarith
  -- Combining the two block estimates gives the global lower bound.
  calc
    0 ≤ (left.card : ℝ) * (y - x) + (right.card : ℝ) * (-(y - x)) := hbase
    _ ≤
        Finset.sum left (fun i : Fin n ↦ |y - a i| - |x - a i|) +
          Finset.sum right (fun i : Fin n ↦ |y - a i| - |x - a i|) := by
      exact add_le_add (le_of_eq hleft.symm) hright
    _ = ∑ i : Fin n, (|y - a i| - |x - a i|) := by
      simp [hsplit]

/-- Helper for Proposition 3.31: if `x` is a possible median, then moving to the left cannot
decrease the total absolute deviation. -/
lemma sumAbsDifferenceNonneg_of_isPossibleMedian_left
    (a : Fin n → ℝ) (x y : ℝ) (hx : IsPossibleMedian a x) (hyx : y ≤ x) :
    0 ≤ ∑ i : Fin n, (|y - a i| - |x - a i|) := by
  let left := Finset.univ.filter fun i : Fin n ↦ a i < x
  let right := Finset.univ.filter fun i : Fin n ↦ x ≤ a i
  -- The second median inequality controls the symmetric partition counts.
  have hxright : 2 * right.card ≥ n := by
    simpa [right] using hx.2
  have hcount : left.card ≤ right.card := by
    have hpart : left.card + right.card = n := by
      simpa [left, right] using card_filter_lt_add_card_filter_ge a x
    omega
  have hsplit :
      ∑ i : Fin n, (|y - a i| - |x - a i|) =
        Finset.sum left (fun i : Fin n ↦ |y - a i| - |x - a i|) +
          Finset.sum right (fun i : Fin n ↦ |y - a i| - |x - a i|) := by
    simpa [left, right, not_lt] using
      (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun i : Fin n ↦ a i < x) (fun i : Fin n ↦ |y - a i| - |x - a i|)).symm
  have hleft :
      (left.card : ℝ) * (-(x - y)) ≤
        Finset.sum left (fun i : Fin n ↦ |y - a i| - |x - a i|) := by
    -- On the left block, the reverse triangle inequality gives the needed lower bound.
    calc
      (left.card : ℝ) * (-(x - y)) = Finset.sum left (fun _ : Fin n ↦ -(x - y)) := by
        simp
        ring
      _ ≤ Finset.sum left (fun i : Fin n ↦ |y - a i| - |x - a i|) := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have habs := abs_sub_abs_le_abs_sub (x - a i) (y - a i)
        have hterm : |x - a i| - |y - a i| ≤ x - y := by
          calc
            |x - a i| - |y - a i| ≤ |(x - a i) - (y - a i)| := habs
            _ = |x - y| := by
              ring_nf
            _ = x - y := by
              rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
        linarith
  have hright :
      Finset.sum right (fun i : Fin n ↦ |y - a i| - |x - a i|) = (right.card : ℝ) * (x - y) := by
    -- On the right block, the absolute value again stays on one linear branch.
    calc
      Finset.sum right (fun i : Fin n ↦ |y - a i| - |x - a i|) =
          Finset.sum right (fun _ : Fin n ↦ x - y) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        exact abs_sub_sub_eq_of_le_right hyx (Finset.mem_filter.mp hi).2
      _ = (right.card : ℝ) * (x - y) := by
        simp
        ring
  have hbase :
      0 ≤ (left.card : ℝ) * (-(x - y)) + (right.card : ℝ) * (x - y) := by
    have hcountReal : (left.card : ℝ) ≤ right.card := by
      exact_mod_cast hcount
    have hstep : 0 ≤ x - y := sub_nonneg.mpr hyx
    nlinarith
  -- Combining the two block estimates gives the global lower bound.
  calc
    0 ≤ (left.card : ℝ) * (-(x - y)) + (right.card : ℝ) * (x - y) := hbase
    _ ≤
        Finset.sum left (fun i : Fin n ↦ |y - a i| - |x - a i|) +
          Finset.sum right (fun i : Fin n ↦ |y - a i| - |x - a i|) := by
      exact add_le_add hleft (le_of_eq hright.symm)
    _ = ∑ i : Fin n, (|y - a i| - |x - a i|) := by
      simp [hsplit]

/-- Helper for Proposition 3.31: if too few sample points lie at or to the left of `x`, then a
small move to the right strictly decreases the unit-weight Fermat-Weber objective. -/
lemma existsStrictDescentRight_of_badLeftCount
    (a : Fin n → ℝ) (x : ℝ)
    (hbad : 2 * (Finset.univ.filter fun i ↦ a i ≤ x).card < n) :
    ∃ y, fermatWeberObjective (fun _ : Fin n ↦ (1 : ℝ)) a y <
      fermatWeberObjective (fun _ : Fin n ↦ (1 : ℝ)) a x := by
  classical
  let left := Finset.univ.filter fun i : Fin n ↦ a i ≤ x
  let right := Finset.univ.filter fun i : Fin n ↦ x < a i
  have hbad' : 2 * left.card < n := by
    simpa [left] using hbad
  have hpart : left.card + right.card = n := by
    simpa [left, right] using card_filter_le_add_card_filter_gt a x
  have hcount : left.card < right.card := by
    omega
  have hrightPos : 0 < right.card := by
    omega
  let rightValues : Finset ℝ := right.image a
  have hrightValuesNonempty : rightValues.Nonempty := by
    rcases Finset.card_pos.mp hrightPos with ⟨i, hi⟩
    exact ⟨a i, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩
  let r := rightValues.min' hrightValuesNonempty
  have hr_mem : r ∈ rightValues := by
    exact Finset.min'_mem _ _
  have hx_lt_r : x < r := by
    rcases Finset.mem_image.mp hr_mem with ⟨i, hi, hir⟩
    have hi' : x < a i := (Finset.mem_filter.mp hi).2
    simpa [hir] using hi'
  have hr_le {i : Fin n} (hi : i ∈ right) : r ≤ a i := by
    have hai : a i ∈ rightValues := Finset.mem_image.mpr ⟨i, hi, rfl⟩
    exact Finset.min'_le _ _ hai
  let y : ℝ := (x + r) / 2
  have hxy : x < y := by
    -- The midpoint stays strictly to the right of `x`.
    dsimp [y]
    linarith
  have hyr : y < r := by
    -- The midpoint also stays strictly before the first site to the right.
    dsimp [y]
    linarith
  have hsplit :
      ∑ i : Fin n, (|y - a i| - |x - a i|) =
        Finset.sum left (fun i : Fin n ↦ |y - a i| - |x - a i|) +
          Finset.sum right (fun i : Fin n ↦ |y - a i| - |x - a i|) := by
    simpa [left, right, not_le] using
      (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun i : Fin n ↦ a i ≤ x) (fun i : Fin n ↦ |y - a i| - |x - a i|)).symm
  have hleft :
      Finset.sum left (fun i : Fin n ↦ |y - a i| - |x - a i|) = (left.card : ℝ) * (y - x) := by
    -- No left-block summand crosses a sample point.
    calc
      Finset.sum left (fun i : Fin n ↦ |y - a i| - |x - a i|) =
          Finset.sum left (fun _ : Fin n ↦ y - x) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        exact abs_sub_sub_eq_of_le_left (Finset.mem_filter.mp hi).2 (le_of_lt hxy)
      _ = (left.card : ℝ) * (y - x) := by
        simp
        ring
  have hright :
      Finset.sum right (fun i : Fin n ↦ |y - a i| - |x - a i|) = (right.card : ℝ) * (x - y) := by
    -- Every right-block summand stays on the opposite linear branch.
    calc
      Finset.sum right (fun i : Fin n ↦ |y - a i| - |x - a i|) =
          Finset.sum right (fun _ : Fin n ↦ x - y) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hya : y ≤ a i := le_trans (le_of_lt hyr) (hr_le hi)
        have hterm := abs_sub_sub_eq_of_le_right (le_of_lt hxy) hya
        linarith
      _ = (right.card : ℝ) * (x - y) := by
        simp
        ring
  have hsumlt : ∑ i : Fin n, (|y - a i| - |x - a i|) < 0 := by
    have hcountReal : (left.card : ℝ) < right.card := by
      exact_mod_cast hcount
    have hstep : 0 < y - x := sub_pos.mpr hxy
    calc
      ∑ i : Fin n, (|y - a i| - |x - a i|) =
          (left.card : ℝ) * (y - x) + (right.card : ℝ) * (x - y) := by
        rw [hsplit, hleft, hright]
      _ = ((left.card : ℝ) - right.card) * (y - x) := by
        ring
      _ < 0 := by
        nlinarith
  refine ⟨y, ?_⟩
  -- Rewrite the objective to the absolute-deviation sum and use the negative total change.
  rw [fermatWeberObjective_one_apply_eq_sum_abs, fermatWeberObjective_one_apply_eq_sum_abs]
  have hdiff : (∑ i : Fin n, |y - a i|) - ∑ i : Fin n, |x - a i| < 0 := by
    simpa [Finset.sum_sub_distrib] using hsumlt
  linarith

/-- Helper for Proposition 3.31: if too few sample points lie at or to the right of `x`, then a
small move to the left strictly decreases the unit-weight Fermat-Weber objective. -/
lemma existsStrictDescentLeft_of_badRightCount
    (a : Fin n → ℝ) (x : ℝ)
    (hbad : 2 * (Finset.univ.filter fun i ↦ x ≤ a i).card < n) :
    ∃ y, fermatWeberObjective (fun _ : Fin n ↦ (1 : ℝ)) a y <
      fermatWeberObjective (fun _ : Fin n ↦ (1 : ℝ)) a x := by
  classical
  let left := Finset.univ.filter fun i : Fin n ↦ a i < x
  let right := Finset.univ.filter fun i : Fin n ↦ x ≤ a i
  have hbad' : 2 * right.card < n := by
    simpa [right] using hbad
  have hpart : left.card + right.card = n := by
    simpa [left, right] using card_filter_lt_add_card_filter_ge a x
  have hcount : right.card < left.card := by
    omega
  have hleftPos : 0 < left.card := by
    omega
  let leftValues : Finset ℝ := left.image a
  have hleftValuesNonempty : leftValues.Nonempty := by
    rcases Finset.card_pos.mp hleftPos with ⟨i, hi⟩
    exact ⟨a i, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩
  let l := leftValues.max' hleftValuesNonempty
  have hl_mem : l ∈ leftValues := by
    exact Finset.max'_mem _ _
  have hl_lt_x : l < x := by
    rcases Finset.mem_image.mp hl_mem with ⟨i, hi, hil⟩
    have hi' : a i < x := (Finset.mem_filter.mp hi).2
    simpa [hil] using hi'
  have hle_l {i : Fin n} (hi : i ∈ left) : a i ≤ l := by
    have hai : a i ∈ leftValues := Finset.mem_image.mpr ⟨i, hi, rfl⟩
    exact Finset.le_max' _ _ hai
  let y : ℝ := (x + l) / 2
  have hyx : y < x := by
    -- The midpoint stays strictly to the left of `x`.
    dsimp [y]
    linarith
  have hly : l < y := by
    -- The midpoint also stays strictly after the last site to the left.
    dsimp [y]
    linarith
  have hsplit :
      ∑ i : Fin n, (|y - a i| - |x - a i|) =
        Finset.sum left (fun i : Fin n ↦ |y - a i| - |x - a i|) +
          Finset.sum right (fun i : Fin n ↦ |y - a i| - |x - a i|) := by
    simpa [left, right, not_lt] using
      (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun i : Fin n ↦ a i < x) (fun i : Fin n ↦ |y - a i| - |x - a i|)).symm
  have hleft :
      Finset.sum left (fun i : Fin n ↦ |y - a i| - |x - a i|) = (left.card : ℝ) * (y - x) := by
    -- Every left-block summand stays on the same linear branch.
    calc
      Finset.sum left (fun i : Fin n ↦ |y - a i| - |x - a i|) =
          Finset.sum left (fun _ : Fin n ↦ y - x) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hai : a i ≤ y := le_trans (hle_l hi) (le_of_lt hly)
        have hterm := abs_sub_sub_eq_of_le_left hai (le_of_lt hyx)
        linarith
      _ = (left.card : ℝ) * (y - x) := by
        simp
        ring
  have hright :
      Finset.sum right (fun i : Fin n ↦ |y - a i| - |x - a i|) = (right.card : ℝ) * (x - y) := by
    -- Every right-block summand stays on the opposite linear branch.
    calc
      Finset.sum right (fun i : Fin n ↦ |y - a i| - |x - a i|) =
          Finset.sum right (fun _ : Fin n ↦ x - y) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        exact abs_sub_sub_eq_of_le_right (le_of_lt hyx) (Finset.mem_filter.mp hi).2
      _ = (right.card : ℝ) * (x - y) := by
        simp
        ring
  have hsumlt : ∑ i : Fin n, (|y - a i| - |x - a i|) < 0 := by
    have hcountReal : (right.card : ℝ) < left.card := by
      exact_mod_cast hcount
    have hstep : 0 < x - y := sub_pos.mpr hyx
    calc
      ∑ i : Fin n, (|y - a i| - |x - a i|) =
          (left.card : ℝ) * (y - x) + (right.card : ℝ) * (x - y) := by
        rw [hsplit, hleft, hright]
      _ = ((right.card : ℝ) - left.card) * (x - y) := by
        ring
      _ < 0 := by
        nlinarith
  refine ⟨y, ?_⟩
  -- Rewrite the objective to the absolute-deviation sum and use the negative total change.
  rw [fermatWeberObjective_one_apply_eq_sum_abs, fermatWeberObjective_one_apply_eq_sum_abs]
  have hdiff : (∑ i : Fin n, |y - a i|) - ∑ i : Fin n, |x - a i| < 0 := by
    simpa [Finset.sum_sub_distrib] using hsumlt
  linarith

/-- Helper for Proposition 3.31: a possible median globally minimizes the unit-weight
Fermat-Weber objective. -/
lemma isMinOn_fermatWeberObjective_one_of_isPossibleMedian
    (a : Fin n → ℝ) (x : ℝ) (hx : IsPossibleMedian a x) :
    IsMinOn (fermatWeberObjective (fun _ : Fin n ↦ (1 : ℝ)) a) Set.univ x := by
  rw [isMinOn_univ_iff]
  intro y
  rw [fermatWeberObjective_one_apply_eq_sum_abs, fermatWeberObjective_one_apply_eq_sum_abs]
  rcases le_total x y with hxy | hyx
  · -- The right half-line is handled by the first one-sided aggregation lemma.
    have hnonneg :
        0 ≤ (∑ i : Fin n, |y - a i|) - ∑ i : Fin n, |x - a i| := by
      simpa [Finset.sum_sub_distrib] using
        sumAbsDifferenceNonneg_of_isPossibleMedian_right a x y hx hxy
    exact sub_nonneg.mp hnonneg
  · -- The left half-line is handled symmetrically.
    have hnonneg :
        0 ≤ (∑ i : Fin n, |y - a i|) - ∑ i : Fin n, |x - a i| := by
      simpa [Finset.sum_sub_distrib] using
        sumAbsDifferenceNonneg_of_isPossibleMedian_left a x y hx hyx
    exact sub_nonneg.mp hnonneg

-- Proof sketch: for `n = 0`, both sides are trivial. For general `n`, the forward direction
-- compares the sum at `x` and `y` by splitting indices according to which side of `x` they lie
-- on. The converse should choose a midpoint with the nearest offending sample on the side where
-- a median inequality fails; because that move crosses no sample value, every summand changes by
-- exactly `±(y - x)`, giving a strict decrease of the objective.
/-- Proposition 3.31: a real number is a possible median of a finite real sample if and only if
it globally minimizes the unit-weight Fermat-Weber objective, equivalently the absolute-deviation
objective `x ↦ ∑ i, |x - a i|`. -/
theorem isPossibleMedian_iff_isMinOn_fermatWeberObjective_one
    (a : Fin n → ℝ) (x : ℝ) :
    IsPossibleMedian a x ↔
      IsMinOn (fermatWeberObjective (fun _ : Fin n ↦ (1 : ℝ)) a) Set.univ x := by
  constructor
  · -- The solved direction uses only count complements plus per-summand absolute-value bounds.
    exact isMinOn_fermatWeberObjective_one_of_isPossibleMedian a x
  · intro hmin
    rw [isMinOn_univ_iff] at hmin
    by_cases hleft : 2 * (Finset.univ.filter fun i : Fin n ↦ a i ≤ x).card ≥ n
    · by_cases hright : 2 * (Finset.univ.filter fun i : Fin n ↦ x ≤ a i).card ≥ n
      · -- Both median inequalities hold, so `x` is a possible median.
        exact ⟨hleft, hright⟩
      · -- Route correction: use an explicit midpoint descent witness on the bad side.
        have hbad : 2 * (Finset.univ.filter fun i : Fin n ↦ x ≤ a i).card < n :=
          lt_of_not_ge hright
        rcases existsStrictDescentLeft_of_badRightCount a x hbad with ⟨y, hy⟩
        exact (hy.not_ge (hmin y)).elim
    · -- The symmetric bad-side midpoint witness again contradicts global minimality.
      have hbad : 2 * (Finset.univ.filter fun i : Fin n ↦ a i ≤ x).card < n :=
        lt_of_not_ge hleft
      rcases existsStrictDescentRight_of_badLeftCount a x hbad with ⟨y, hy⟩
      exact (hy.not_ge (hmin y)).elim

/-- Set-valued form of Proposition 3.31 for a finite sample, using the Chapter 8 global argmin
owner `unconstrained_problem_solutions`. -/
theorem possibleMedianSet_eq_globalMinimizers_fermatWeberObjective_one (a : Fin n → ℝ) :
    possibleMedianSet a =
      unconstrained_problem_solutions (fermatWeberObjective (fun _ : Fin n ↦ (1 : ℝ)) a) := by
  ext x
  rw [mem_possibleMedianSet, mem_unconstrained_problem_solutions_iff]
  exact isPossibleMedian_iff_isMinOn_fermatWeberObjective_one a x

end
