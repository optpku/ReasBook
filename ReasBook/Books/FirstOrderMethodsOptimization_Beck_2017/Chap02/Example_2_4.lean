/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.InformationTheory.Hamming
import Mathlib.Topology.Semicontinuity.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

universe u

/-- The scalar `{0, 1}`-valued indicator of the nonzero locus, expressed via the canonical set
indicator. -/
noncomputable def l0Indicator (y : ℝ) : ℝ :=
  ({0} : Set ℝ)ᶜ.indicator (fun _ ↦ (1 : ℝ)) y

/-- `l0Indicator` is the canonical set indicator of the complement of `{0}` with constant value
`1`. -/
theorem l0Indicator_eq_indicator_compl :
    l0Indicator = (({0} : Set ℝ)ᶜ.indicator fun _ ↦ (1 : ℝ)) :=
  rfl

-- Proof sketch: unfold `l0Indicator`; since `0 ∉ ({0} : Set ℝ)ᶜ`, the indicator takes the value
-- `0` at the origin.
/-- The scalar `ℓ₀` indicator vanishes at the origin. -/
@[simp] theorem l0Indicator_zero :
    l0Indicator 0 = 0 := by
  simp [l0Indicator]

-- Proof sketch: unfold `l0Indicator`; when `y ≠ 0`, the point lies in `({0} : Set ℝ)ᶜ`, so the
-- indicator takes the constant branch value `1`.
/-- Away from the origin, the scalar `ℓ₀` indicator is `1`. -/
@[simp] theorem l0Indicator_of_ne_zero {y : ℝ} (hy : y ≠ 0) :
    l0Indicator y = 1 := by
  simp [l0Indicator, hy]

/-- The scalar `ℓ₀` indicator vanishes exactly at the origin. -/
@[simp] theorem l0Indicator_eq_zero_iff {y : ℝ} :
    l0Indicator y = 0 ↔ y = 0 := by
  by_cases hy : y = 0
  · simp [hy]
  · simp [hy]

/-- The scalar `ℓ₀` indicator equals `1` exactly away from the origin. -/
@[simp] theorem l0Indicator_eq_one_iff {y : ℝ} :
    l0Indicator y = 1 ↔ y ≠ 0 := by
  by_cases hy : y = 0
  · simp [hy]
  · simp [hy]

section

-- Proof sketch: unfold `l0Indicator`; if `a < 0`, neither branch can satisfy
-- `l0Indicator y ≤ a`, since both possible values `0` and `1` are nonnegative.
/-- The sublevel set of `l0Indicator` is empty below `0`. -/
theorem l0Indicator_sublevelSet_of_lt_zero {a : ℝ} (ha : a < 0) :
    l0Indicator ⁻¹' Set.Iic a = ∅ := by
  ext y
  by_cases hy : y = 0
  · simp [l0Indicator, hy, not_le.mpr ha]
  · have h1 : ¬ (1 : ℝ) ≤ a := not_le.mpr (lt_trans ha zero_lt_one)
    simp [l0Indicator, hy, h1]

-- Proof sketch: unfold `l0Indicator`; for `0 ≤ a < 1`, the inequality
-- `l0Indicator y ≤ a` holds exactly when the branch value is `0`, i.e. exactly when `y = 0`.
/-- Between `0` and `1`, the sublevel set of `l0Indicator` is the singleton `{0}`. -/
theorem l0Indicator_sublevelSet_of_nonneg_of_lt_one {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    l0Indicator ⁻¹' Set.Iic a = ({0} : Set ℝ) := by
  ext y
  by_cases hy : y = 0
  · simp [hy, ha0]
  · have h1 : ¬ (1 : ℝ) ≤ a := not_le.mpr ha1
    simp [hy, h1]

-- Proof sketch: unfold `l0Indicator`; both possible values `0` and `1` are bounded above by any
-- `a ≥ 1`, so every real number lies in the sublevel set.
/-- Once the level is at least `1`, the sublevel set of `l0Indicator` is all of `ℝ`. -/
theorem l0Indicator_sublevelSet_of_one_le {a : ℝ} (ha : 1 ≤ a) :
    l0Indicator ⁻¹' Set.Iic a = Set.univ := by
  ext y
  have h0 : 0 ≤ a := le_trans zero_le_one ha
  by_cases hy : y = 0
  · simp [hy, h0]
  · simp [hy, ha]

/-- Every real sublevel set of `l0Indicator` is closed. -/
theorem l0Indicator_isClosed_preimage_Iic (a : ℝ) :
    IsClosed (l0Indicator ⁻¹' Set.Iic a) := by
  by_cases ha0 : a < 0
  · simp [l0Indicator_sublevelSet_of_lt_zero ha0]
  · by_cases ha1 : a < 1
    · have h0a : 0 ≤ a := le_of_not_gt ha0
      simp [l0Indicator_sublevelSet_of_nonneg_of_lt_one h0a ha1]
    · have h1a : 1 ≤ a := le_of_not_gt ha1
      simp [l0Indicator_sublevelSet_of_one_le h1a]

/-- The scalar indicator entering the `ℓ₀` example is closed, i.e. lower semicontinuous. -/
theorem l0Indicator_lowerSemicontinuous :
    LowerSemicontinuous l0Indicator := by
  exact lowerSemicontinuous_iff_isClosed_preimage.2 l0Indicator_isClosed_preimage_Iic

section

variable {ι : Type u} [Fintype ι]

-- Proof sketch: `hammingNorm x` is the canonical owner object for the number of nonzero
-- coordinates of `x`, while each term `l0Indicator (x i)` contributes `1` exactly when `x i ≠ 0`
-- and `0` otherwise; compare the resulting finite sum with `(hammingNorm x : ℝ)`.
/-- The `ℓ₀` count is the finite sum of the scalar nonzero indicators of the coordinates. -/
theorem hammingNorm_eq_sum_l0Indicator (x : ι → ℝ) :
    (hammingNorm x : ℝ) = ∑ i, l0Indicator (x i) := by
  classical
  rw [hammingNorm]
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  by_cases hi : x i = 0
  · simp [l0Indicator, hi]
  · simp [l0Indicator, hi]

-- Proof sketch: rewrite the real-valued `ℓ₀` count using `hammingNorm_eq_sum_l0Indicator`; for
-- each coordinate `i`, the map `x ↦ l0Indicator (x i)` is lower semicontinuous by composing
-- `l0Indicator_lowerSemicontinuous` with the continuous evaluation map `x ↦ x i`, and then apply
-- `lowerSemicontinuous_sum`.
/-- Example 2.4: the `ℓ₀` function on a finite real coordinate space is closed, equivalently
lower semicontinuous, because it is the finite sum of the coordinatewise nonzero indicator. -/
theorem hammingNorm_lowerSemicontinuous :
    LowerSemicontinuous (fun x : ι → ℝ ↦ (hammingNorm x : ℝ)) := by
  have hcoord : ∀ i, LowerSemicontinuous (fun x : ι → ℝ ↦ l0Indicator (x i)) := by
    intro i
    simpa [Function.comp] using l0Indicator_lowerSemicontinuous.comp (continuous_apply i)
  have hsum : LowerSemicontinuous (fun x : ι → ℝ ↦ ∑ i, l0Indicator (x i)) :=
    lowerSemicontinuous_sum fun i _ ↦ hcoord i
  simpa [hammingNorm_eq_sum_l0Indicator] using hsum

end

end
