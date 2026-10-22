/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Lemma_2_1

-- Declarations for this item will be appended below by the statement pipeline.

section

open WithLp (toLp)

local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- The parabolic region `C = {(x₁, x₂) | x₁ + x₂^2 / 2 ≤ 0}` from Proposition 2.5. -/
def parabolicRegion : Set E2 := {x : E2 | x 0 + x 1 ^ 2 / 2 ≤ 0}

@[simp] theorem mem_parabolicRegion (x : E2) :
    x ∈ parabolicRegion ↔ x 0 + x 1 ^ 2 / 2 ≤ 0 :=
  Iff.rfl

/-- Helper for Proposition 2.5: in `ℝ²`, the Euclidean pairing with `y` is the coordinate
formula `y₁ x₁ + y₂ x₂`. -/
lemma parabolicRegion_pairing_eq (y x : E2) :
    inner ℝ y x = y 0 * x 0 + y 1 * x 1 := by
  -- Expand the `Fin 2` inner product into its two coordinate contributions.
  calc
    inner ℝ y x = inner ℝ (y 0) (x 0) + inner ℝ (y 1) (x 1) := by
      simp [PiLp.inner_apply, Fin.sum_univ_two]
    _ = x 0 * y 0 + x 1 * y 1 := by
      change x 0 * starRingEnd ℝ (y 0) + x 1 * starRingEnd ℝ (y 1) = _
      simp
    _ = y 0 * x 0 + y 1 * x 1 := by
      ring

/-- Helper for Proposition 2.5: when `y 0 > 0`, the pairing image over `parabolicRegion` has the
displayed quadratic maximum. -/
lemma parabolicRegionPositiveImageIsGreatest {y : E2} (hy : 0 < y 0) :
    IsGreatest ((fun x : E2 ↦ (inner ℝ y x : EReal)) '' parabolicRegion)
      ((((y 1) ^ 2) / (2 * y 0) : ℝ) : EReal) := by
  let xStar : E2 := toLp 2 ![-((y 1 / y 0) ^ 2) / 2, y 1 / y 0]
  have hy0 : y 0 ≠ 0 := ne_of_gt hy
  have hxStar_mem : xStar ∈ parabolicRegion := by
    -- The optimizer sits on the boundary parabola.
    change -((y 1 / y 0) ^ 2) / 2 + (y 1 / y 0) ^ 2 / 2 ≤ 0
    ring_nf
    norm_num
  refine ⟨?_, ?_⟩
  · refine ⟨xStar, hxStar_mem, ?_⟩
    -- Evaluate the pairing at the boundary maximizer.
    change ((inner ℝ y xStar : ℝ) : EReal) = ((((y 1) ^ 2) / (2 * y 0) : ℝ) : EReal)
    have hxStar_value : inner ℝ y xStar = (y 1) ^ 2 / (2 * y 0) := by
      calc
        inner ℝ y xStar =
            y 0 * (-((y 1 / y 0) ^ 2) / 2) + y 1 * (y 1 / y 0) := by
          simp [parabolicRegion_pairing_eq, xStar]
        _ = (y 1) ^ 2 / (2 * y 0) := by
          field_simp [hy0]
          ring
    exact_mod_cast hxStar_value
  · rintro z ⟨x, hx, rfl⟩
    change ((inner ℝ y x : ℝ) : EReal) ≤ ((((y 1) ^ 2) / (2 * y 0) : ℝ) : EReal)
    have hx0 : x 0 ≤ -(x 1 ^ 2) / 2 := by
      have hx' : x 0 + x 1 ^ 2 / 2 ≤ 0 := by
        simpa [parabolicRegion] using hx
      nlinarith [hx']
    have hmul :
        y 0 * x 0 ≤ y 0 * (-(x 1 ^ 2) / 2) := by
      exact mul_le_mul_of_nonneg_left hx0 (le_of_lt hy)
    have hpair_le :
        inner ℝ y x ≤ y 0 * (-(x 1 ^ 2) / 2) + y 1 * x 1 := by
      rw [parabolicRegion_pairing_eq]
      linarith
    have hsquare : 0 ≤ (y 0 * x 1 - y 1) ^ 2 := sq_nonneg _
    have hden_pos : 0 < 2 * y 0 := by
      nlinarith
    have hquad_mul :
        (y 0 * (-(x 1 ^ 2) / 2) + y 1 * x 1) * (2 * y 0) ≤ (y 1) ^ 2 := by
      nlinarith
    have hquad :
        y 0 * (-(x 1 ^ 2) / 2) + y 1 * x 1 ≤ (y 1) ^ 2 / (2 * y 0) := by
      exact (le_div_iff₀ hden_pos).mpr <|
        by simpa [mul_comm, mul_left_comm, mul_assoc] using hquad_mul
    have hreal : inner ℝ y x ≤ (y 1) ^ 2 / (2 * y 0) := hpair_le.trans hquad
    exact_mod_cast hreal

/-- Helper for Proposition 2.5: if `y 0 < 0`, moving far enough along the negative first-axis ray
forces the pairing above any prescribed real level. -/
lemma parabolicRegionWitnessAbove_of_fstNeg {y : E2} (hy : y 0 < 0) (r : ℝ) :
    ∃ x ∈ parabolicRegion, (r : EReal) < (inner ℝ y x : EReal) := by
  have hyPos : 0 < -y 0 := by
    linarith
  obtain ⟨t, ht⟩ := exists_gt (max (r / (-y 0)) 0)
  let x : E2 := toLp 2 ![-t, 0]
  have hrt_div : r / (-y 0) < t := lt_of_le_of_lt (le_max_left _ _) ht
  have hrt : r < (-y 0) * t := by
    simpa [mul_comm] using (div_lt_iff₀ hyPos).mp hrt_div
  have hx_mem : x ∈ parabolicRegion := by
    -- The ray `(-t, 0)` stays in the feasible set once `t > 0`.
    have ht0 : 0 < t := lt_of_le_of_lt (le_max_right _ _) ht
    simp [x, parabolicRegion, ht0.le]
  refine ⟨x, hx_mem, ?_⟩
  have hx_value : inner ℝ y x = (-y 0) * t := by
    -- On this ray, only the first coordinate contributes.
    calc
      inner ℝ y x = y 0 * (-t) + y 1 * 0 := by
        simp [parabolicRegion_pairing_eq, x]
      _ = (-y 0) * t := by
        ring
  have hreal : r < inner ℝ y x := by
    exact lt_of_lt_of_eq hrt hx_value.symm
  exact_mod_cast hreal

/-- Helper for Proposition 2.5: if `y 0 = 0` but `y 1 ≠ 0`, moving along the boundary parabola
forces the pairing above any prescribed real level. -/
lemma parabolicRegionWitnessAbove_of_fstZero_of_sndNeZero {y : E2}
    (hy0 : y 0 = 0) (hy1 : y 1 ≠ 0) (r : ℝ) :
    ∃ x ∈ parabolicRegion, (r : EReal) < (inner ℝ y x : EReal) := by
  rcases lt_or_gt_of_ne hy1 with hy1neg | hy1pos
  · have hyPos : 0 < -y 1 := by
      linarith
    obtain ⟨t, ht⟩ := exists_gt (max (r / (-y 1)) 0)
    let x : E2 := toLp 2 ![-t ^ 2 / 2, -t]
    have hrt_div : r / (-y 1) < t := lt_of_le_of_lt (le_max_left _ _) ht
    have hrt : r < (-y 1) * t := by
      simpa [mul_comm] using (div_lt_iff₀ hyPos).mp hrt_div
    have hx_mem : x ∈ parabolicRegion := by
      -- These witnesses lie on the boundary parabola.
      simp [x, parabolicRegion]
      nlinarith
    refine ⟨x, hx_mem, ?_⟩
    have hx_value : inner ℝ y x = (-y 1) * t := by
      -- With `y 0 = 0`, only the second coordinate remains.
      calc
        inner ℝ y x = y 0 * (-t ^ 2 / 2) + y 1 * (-t) := by
          simp [parabolicRegion_pairing_eq, x]
        _ = (-y 1) * t := by
          rw [hy0]
          ring
    have hreal : r < inner ℝ y x := by
      exact lt_of_lt_of_eq hrt hx_value.symm
    exact_mod_cast hreal
  · obtain ⟨t, ht⟩ := exists_gt (max (r / y 1) 0)
    let x : E2 := toLp 2 ![-t ^ 2 / 2, t]
    have hrt_div : r / y 1 < t := lt_of_le_of_lt (le_max_left _ _) ht
    have hrt : r < y 1 * t := by
      simpa [mul_comm] using (div_lt_iff₀ hy1pos).mp hrt_div
    have hx_mem : x ∈ parabolicRegion := by
      -- These witnesses lie on the same boundary parabola with the opposite sign choice.
      simp [x, parabolicRegion]
      nlinarith
    refine ⟨x, hx_mem, ?_⟩
    have hx_value : inner ℝ y x = y 1 * t := by
      -- With `y 0 = 0`, the first coordinate drops out.
      calc
        inner ℝ y x = y 0 * (-t ^ 2 / 2) + y 1 * t := by
          simp [parabolicRegion_pairing_eq, x]
        _ = y 1 * t := by
          simp [hy0]
    have hreal : r < inner ℝ y x := by
      exact lt_of_lt_of_eq hrt hx_value.symm
    exact_mod_cast hreal

-- Proof sketch: write the constraint as `x 0 ≤ -(x 1 ^ 2) / 2`. If `0 < y 0`, then for each fixed
-- `x 1` the pairing is maximized at the boundary value `x 0 = -(x 1 ^ 2) / 2`, reducing the
-- problem to maximizing a concave quadratic in `x 1`, whose maximum is `y 1 ^ 2 / (2 * y 0)`.
-- If `y 0 < 0`, then sending `x 0 → -∞` makes the pairing tend to `⊤`. If `y 0 = 0` and
-- `y 1 ≠ 0`, evaluating on boundary points gives arbitrarily large values. At `y = 0`, every
-- pairing is `0`, so the support function is `0`.
/-- Proposition 2.5: for `C = {(x₁, x₂) | x₁ + x₂^2 / 2 ≤ 0}` in `ℝ²`, the primal support
function `σ[C]` equals `y₂^2 / (2 y₁)` when `y₁ > 0`, equals `0` at the origin, and equals `⊤`
otherwise. -/
theorem support_function_parabolic_region (y : E2) :
    σ[parabolicRegion] y =
      if 0 < y 0 then ((((y 1) ^ 2) / (2 * y 0) : ℝ) : EReal)
      else if y = 0 then (0 : EReal)
      else ⊤ := by
  by_cases hy : 0 < y 0
  · -- In the positive branch, evaluate the defining supremum via the explicit maximizer.
    rw [support_function_eq_sSup, (parabolicRegionPositiveImageIsGreatest hy).csSup_eq]
    simp [hy]
  · by_cases hyZero : y = 0
    · -- At the origin, every feasible pairing vanishes, and `0` is attained by the zero vector.
      have hzeroGreatest :
          IsGreatest ((fun x : E2 ↦ (inner ℝ y x : EReal)) '' parabolicRegion) (0 : EReal) := by
        refine ⟨?_, ?_⟩
        · refine ⟨0, ?_, ?_⟩
          · simp [parabolicRegion]
          · simp [hyZero]
        · rintro z ⟨x, hx, rfl⟩
          simp [hyZero]
      rw [support_function_eq_sSup, hzeroGreatest.csSup_eq]
      simp [hyZero]
    · -- Outside the positive and origin branches, either the first coordinate is negative or the
      -- second coordinate alone makes the support function unbounded along the boundary parabola.
      have hy_le : y 0 ≤ 0 := le_of_not_gt hy
      have hcases : y 0 < 0 ∨ (y 0 = 0 ∧ y 1 ≠ 0) := by
        rcases lt_or_eq_of_le hy_le with hyNeg | hyEq
        · exact Or.inl hyNeg
        · refine Or.inr ⟨hyEq, ?_⟩
          intro hy1
          apply hyZero
          ext i
          fin_cases i <;> simp [hyEq, hy1]
      rcases hcases with hyNeg | ⟨hyEq, hy1⟩
      · rw [if_neg hy, if_neg hyZero, EReal.eq_top_iff_forall_lt]
        intro r
        rw [support_function_eq_sSup]
        rcases parabolicRegionWitnessAbove_of_fstNeg hyNeg r with ⟨x, hx, hrx⟩
        exact lt_of_lt_of_le hrx (le_sSup ⟨x, hx, rfl⟩)
      · rw [if_neg hy, if_neg hyZero, EReal.eq_top_iff_forall_lt]
        intro r
        rw [support_function_eq_sSup]
        rcases parabolicRegionWitnessAbove_of_fstZero_of_sndNeZero hyEq hy1 r with
          ⟨x, hx, hrx⟩
        exact lt_of_lt_of_le hrx (le_sSup ⟨x, hx, rfl⟩)

/-- In the positive-first-coordinate branch, Proposition 2.5 evaluates the support function by the
explicit quadratic formula. -/
theorem support_function_parabolicRegion_of_pos {y : E2} (hy : 0 < y 0) :
    σ[parabolicRegion] y = ((((y 1) ^ 2) / (2 * y 0) : ℝ) : EReal) := by
  simpa [hy] using support_function_parabolic_region y

/-- At the origin, Proposition 2.5 gives the support function value `0`. -/
@[simp] theorem support_function_parabolicRegion_zero :
    σ[parabolicRegion] (0 : E2) = 0 := by
  simpa using support_function_parabolic_region (0 : E2)

/-- If the first coordinate is negative, the support function of `parabolicRegion` is `⊤`. -/
theorem support_function_parabolicRegion_of_fst_neg {y : E2} (hy : y 0 < 0) :
    σ[parabolicRegion] y = ⊤ := by
  have hy' : ¬ 0 < y 0 := not_lt.mpr hy.le
  have hne : y ≠ 0 := by
    intro hz
    exact hy.ne' <| by simp [hz]
  simpa [hy', hne] using support_function_parabolic_region y

/-- If `y₁ = 0` but `y₂ ≠ 0`, the support function of `parabolicRegion` is `⊤`. -/
theorem support_function_parabolicRegion_of_fst_zero_of_snd_ne_zero {y : E2}
    (hy0 : y 0 = 0) (hy1 : y 1 ≠ 0) :
    σ[parabolicRegion] y = ⊤ := by
  have hy' : ¬ 0 < y 0 := by simp [hy0]
  have hne : y ≠ 0 := by
    intro hz
    exact hy1 <| by simp [hz]
  simpa [hy', hne] using support_function_parabolic_region y

end
