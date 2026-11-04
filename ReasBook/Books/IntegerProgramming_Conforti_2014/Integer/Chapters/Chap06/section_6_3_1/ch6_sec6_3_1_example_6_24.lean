/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_1.ch6_sec6_3_1_one_periodic_extension
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_1.ch6_sec6_3_1_theorem_6_27

-- Declarations for this item will be appended below by the statement pipeline.

section Example624

private noncomputable def example_6_24_pi_on_unit_interval (f : ℝ) : ℝ → ℝ :=
  fun u ↦
    if u ≤ 1 - f then
      u / (1 - f)
    else
      u / (2 - f)

/-- Example 6.24 (1). The discontinuous function from Fig. 6.9 is defined on `[0,1)` by the
displayed two-slope formula and extended to all real arguments by period `1`. -/
noncomputable def example_6_24_pi (f : ℝ) : ℝ → ℝ :=
  onePeriodicExtension (example_6_24_pi_on_unit_interval f)

/-- Unfolding formula for `example_6_24_pi`: the source piecewise expression is evaluated at
`Int.fract r` to produce the `1`-periodic extension. -/
theorem example_6_24_pi_apply (f r : ℝ) :
    example_6_24_pi f r =
      if Int.fract r ≤ 1 - f then
        Int.fract r / (1 - f)
      else
        Int.fract r / (2 - f) :=
  rfl

/-- On the fundamental interval `[0, 1)`, `example_6_24_pi` agrees with the displayed source
formula. -/
theorem example_6_24_pi_eq_on_Ico (f u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    example_6_24_pi f u =
      if u ≤ 1 - f then
        u / (1 - f)
      else
        u / (2 - f) := by
  simpa [example_6_24_pi, example_6_24_pi_on_unit_interval] using
    onePeriodicExtension_eq_on_Ico (example_6_24_pi_on_unit_interval f) hu0 hu1

/-- The function `example_6_24_pi f` has period `1`, matching the source's periodic extension. -/
theorem example_6_24_pi_periodic (f : ℝ) :
    Function.Periodic (example_6_24_pi f) 1 :=
  onePeriodicExtension_periodic _

/-- Helper for Example 6.24: the `1`-periodic extension can always be reduced to the fractional
part of its argument. -/
theorem example_6_24_pi_eq_fract (f r : ℝ) :
    example_6_24_pi f r = example_6_24_pi f (Int.fract r) := by
  -- Rewrite the input as an integer translate of its fractional part and remove that translate by
  -- periodicity.
  have hr : r = (Int.floor r : ℝ) + Int.fract r := by
    simpa [add_comm] using (Int.fract_add_floor r).symm
  rw [hr]
  simpa [one_mul, add_comm, add_left_comm, add_assoc] using
    (example_6_24_pi_periodic f).int_mul (Int.floor r) (Int.fract r)

/-- Helper for Example 6.24: on `[0, 1)`, the displayed example uses the steep left branch up to
the breakpoint. -/
theorem example_6_24_pi_leftBranch
    {f u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (hu_break : u ≤ 1 - f) :
    example_6_24_pi f u = u / (1 - f) := by
  -- Evaluate the periodic extension on the fundamental interval and select the left branch.
  rw [example_6_24_pi_eq_on_Ico f u hu0 hu1, if_pos hu_break]

/-- Helper for Example 6.24: on `[0, 1)`, the displayed example uses the shallower right branch
strictly after the breakpoint. -/
theorem example_6_24_pi_rightBranch
    {f u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (hu_break : 1 - f < u) :
    example_6_24_pi f u = u / (2 - f) := by
  -- The same fundamental-interval formula switches to the right branch after the breakpoint.
  rw [example_6_24_pi_eq_on_Ico f u hu0 hu1, if_neg (not_le_of_gt hu_break)]

/-- Helper for Example 6.24: on the fundamental interval, the function dominates the shallower
right-branch slope `u / (2 - f)`. -/
theorem example_6_24_pi_ge_rightSlope
    {f u : ℝ} (h₀ : 0 < 1 - f) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    u / (2 - f) ≤ example_6_24_pi f u := by
  by_cases hu_break : u ≤ 1 - f
  · -- On the left branch, a smaller denominator only increases the value.
    rw [example_6_24_pi_leftBranch hu0 hu1 hu_break]
    have hrecip : 1 / (2 - f) ≤ 1 / (1 - f) := by
      refine one_div_le_one_div_of_le h₀ ?_
      linarith
    have hrecip' : (2 - f)⁻¹ ≤ (1 - f)⁻¹ := by
      simpa [one_div] using hrecip
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hrecip' hu0
  · -- On the right branch, the lower bound is the exact branch formula.
    rw [example_6_24_pi_rightBranch hu0 hu1 (lt_of_not_ge hu_break)]

/-- Helper for Example 6.24: the source breakpoint still carries the left-branch value `1`. -/
theorem example_6_24_pi_breakpointValue
    {f : ℝ} (h_break : 1 - f ∈ Set.Ioo (0 : ℝ) 1) :
    example_6_24_pi f (1 - f) = 1 := by
  -- Evaluate the displayed formula exactly at the breakpoint, where the left branch is active.
  rw [example_6_24_pi_leftBranch (le_of_lt h_break.1) (by simpa using h_break.2) le_rfl]
  have hα_ne : 1 - f ≠ 0 := by linarith [h_break.1]
  field_simp [hα_ne]

/-- Helper for Example 6.24: on the fundamental interval `[0, 1)`, the source symmetry equation
already holds. -/
theorem example_6_24_pi_symmetryOnIco
    {f u : ℝ} (h₀ : 0 < 1 - f) (h₁ : 1 - f < (1 : ℝ) / 2) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    example_6_24_pi f u + example_6_24_pi f (-f - u) = 1 := by
  let α : ℝ := 1 - f
  have hα_pos : 0 < α := h₀
  have hα_lt_one : α < 1 := by
    dsimp [α] at *
    linarith
  have hβ_ne : 2 - f ≠ 0 := by
    linarith [h₀]
  by_cases hu_break : u ≤ α
  · -- On the left branch, shifting by one period moves `-f - u` to `α - u`.
    have hu_formula :
        example_6_24_pi f u = u / α := by
      simpa [α] using example_6_24_pi_leftBranch hu0 hu1 hu_break
    have hshift :
        example_6_24_pi f (-f - u) = example_6_24_pi f (α - u) := by
      have hper := example_6_24_pi_periodic f (-f - u)
      simpa [α, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hper.symm
    have hαu0 : 0 ≤ α - u := by
      linarith
    have hαu1 : α - u < 1 := by
      linarith
    have hαu_break : α - u ≤ α := by
      linarith
    have hcomp_formula :
        example_6_24_pi f (α - u) = (α - u) / α := by
      simpa [α] using example_6_24_pi_leftBranch hαu0 hαu1 hαu_break
    calc
      example_6_24_pi f u + example_6_24_pi f (-f - u)
          = u / α + (α - u) / α := by rw [hu_formula, hshift, hcomp_formula]
      _ = 1 := by
        field_simp [hα_pos.ne']
        ring
  · -- On the right branch, a second period shift moves the companion point to `1 + α - u`.
    have hu_break' : α < u := lt_of_not_ge hu_break
    have hu_formula :
        example_6_24_pi f u = u / (2 - f) := by
      simpa using example_6_24_pi_rightBranch hu0 hu1 (by simpa [α] using hu_break')
    have hshift₁ :
        example_6_24_pi f (-f - u) = example_6_24_pi f (α - u) := by
      have hper := example_6_24_pi_periodic f (-f - u)
      simpa [α, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hper.symm
    have hshift₂ :
        example_6_24_pi f (α - u) = example_6_24_pi f (1 + α - u) := by
      have hper := example_6_24_pi_periodic f (α - u)
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hper.symm
    have hcomp0 : 0 ≤ 1 + α - u := by
      linarith
    have hcomp1 : 1 + α - u < 1 := by
      linarith
    have hcomp_break : 1 - f < 1 + α - u := by
      dsimp [α]
      linarith
    have hcomp_formula :
        example_6_24_pi f (1 + α - u) = (1 + α - u) / (2 - f) := by
      simpa [α] using example_6_24_pi_rightBranch hcomp0 hcomp1 hcomp_break
    calc
      example_6_24_pi f u + example_6_24_pi f (-f - u)
          = u / (2 - f) + (1 + α - u) / (2 - f) := by
              rw [hu_formula, hshift₁, hshift₂, hcomp_formula]
      _ = 1 := by
        field_simp [hβ_ne]
        dsimp [α]
        ring

/-- Helper for Example 6.24: the displayed symmetry relation extends from `[0, 1)` to all real
arguments by `1`-periodicity. -/
theorem example_6_24_pi_symmetryReal
    {f : ℝ} (h₀ : 0 < 1 - f) (h₁ : 1 - f < (1 : ℝ) / 2) :
    ∀ r : ℝ, example_6_24_pi f r + example_6_24_pi f (-f - r) = 1 := by
  intro r
  let u : ℝ := Int.fract r
  have hu0 : 0 ≤ u := by
    dsimp [u]
    exact Int.fract_nonneg r
  have hu1 : u < 1 := by
    dsimp [u]
    exact Int.fract_lt_one r
  have hr :
      example_6_24_pi f r = example_6_24_pi f u := by
    simpa [u] using example_6_24_pi_eq_fract f r
  have hcomp :
      example_6_24_pi f (-f - r) = example_6_24_pi f (-f - u) := by
    have hper := (example_6_24_pi_periodic f).int_mul (-Int.floor r) (-f - u)
    have hrewrite : (-Int.floor r : ℝ) + (-f - u) = -f - r := by
      dsimp [u]
      have hr' : r = Int.fract r + (Int.floor r : ℝ) := by
        simpa [add_comm] using (Int.fract_add_floor r).symm
      linarith
    calc
      example_6_24_pi f (-f - r) = example_6_24_pi f ((-Int.floor r : ℝ) + (-f - u)) := by
        rw [hrewrite]
      _ = example_6_24_pi f (-f - u) := by
        simpa [one_mul, add_assoc, add_left_comm, add_comm] using hper
  calc
    example_6_24_pi f r + example_6_24_pi f (-f - r)
        = example_6_24_pi f u + example_6_24_pi f (-f - u) := by rw [hr, hcomp]
    _ = 1 := example_6_24_pi_symmetryOnIco h₀ h₁ hu0 hu1

/-- Helper for Example 6.24: on the fundamental square `[0, 1) × [0, 1)`, the displayed example
is subadditive. -/
theorem example_6_24_pi_subadditiveOnIco
    {f u v : ℝ} (h₀ : 0 < 1 - f)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hv0 : 0 ≤ v) (hv1 : v < 1) :
    example_6_24_pi f (u + v) ≤ example_6_24_pi f u + example_6_24_pi f v := by
  let α : ℝ := 1 - f
  let β : ℝ := 2 - f
  have hα_pos : 0 < α := h₀
  have hβ_pos : 0 < β := by
    dsimp [β, α]
    linarith
  have hu_lower : u / β ≤ example_6_24_pi f u := by
    simpa [β] using example_6_24_pi_ge_rightSlope h₀ hu0 hu1
  have hv_lower : v / β ≤ example_6_24_pi f v := by
    simpa [β] using example_6_24_pi_ge_rightSlope h₀ hv0 hv1
  by_cases hsum1 : u + v < 1
  · have huv0 : 0 ≤ u + v := add_nonneg hu0 hv0
    by_cases hsum_break : u + v ≤ α
    · -- If the sum stays before the breakpoint, all three points lie on the left branch.
      have hu_break : u ≤ α := by
        linarith
      have hv_break : v ≤ α := by
        linarith
      have hu_formula :
          example_6_24_pi f u = u / α := by
        simpa [α] using example_6_24_pi_leftBranch hu0 hu1 hu_break
      have hv_formula :
          example_6_24_pi f v = v / α := by
        simpa [α] using example_6_24_pi_leftBranch hv0 hv1 hv_break
      have huv_formula :
          example_6_24_pi f (u + v) = (u + v) / α := by
        simpa [α] using example_6_24_pi_leftBranch huv0 hsum1 hsum_break
      rw [huv_formula, hu_formula, hv_formula]
      simpa [add_div]
    · -- Once the sum crosses the breakpoint, the right branch is dominated by the lower slope.
      have huv_formula :
          example_6_24_pi f (u + v) = (u + v) / β := by
        simpa [β] using
          example_6_24_pi_rightBranch huv0 hsum1 (by
            dsimp [α] at hsum_break
            linarith [lt_of_not_ge hsum_break])
      have hsum_lower : (u + v) / β ≤ example_6_24_pi f u + example_6_24_pi f v := by
        calc
          (u + v) / β = u / β + v / β := by
            rw [add_div]
          _ ≤ example_6_24_pi f u + example_6_24_pi f v := add_le_add hu_lower hv_lower
      rw [huv_formula]
      exact hsum_lower
  · -- If the sum leaves the unit interval, reduce it by one period and compare with the same
    -- right-slope lower bound.
    have hsum_ge_one : 1 ≤ u + v := by
      linarith
    let w : ℝ := u + v - 1
    have hw0 : 0 ≤ w := by
      dsimp [w]
      linarith
    have hw1 : w < 1 := by
      dsimp [w]
      linarith
    have hshift :
        example_6_24_pi f (u + v) = example_6_24_pi f w := by
      have hper := example_6_24_pi_periodic f w
      have hw_eq : w + 1 = u + v := by
        dsimp [w]
        ring
      calc
        example_6_24_pi f (u + v) = example_6_24_pi f (w + 1) := by rw [hw_eq]
        _ = example_6_24_pi f w := hper
    by_cases hsum_beta : u + v ≤ β
    · -- When the reduced sum lands before the breakpoint, compare `(u + v - 1) / α` with the
      -- right-slope lower bound `(u + v) / β`.
      have hw_break : w ≤ α := by
        dsimp [w, α, β] at *
        linarith
      have hw_formula :
          example_6_24_pi f w = w / α := by
        simpa [α] using example_6_24_pi_leftBranch hw0 hw1 hw_break
      have hcomp : w / α ≤ (u + v) / β := by
        have hα_ne : α ≠ 0 := by linarith
        have hβ_ne : β ≠ 0 := by linarith
        field_simp [hα_ne, hβ_ne]
        dsimp [w, α, β] at *
        nlinarith
      have hsum_lower : (u + v) / β ≤ example_6_24_pi f u + example_6_24_pi f v := by
        calc
          (u + v) / β = u / β + v / β := by
            rw [add_div]
          _ ≤ example_6_24_pi f u + example_6_24_pi f v := add_le_add hu_lower hv_lower
      calc
        example_6_24_pi f (u + v) = example_6_24_pi f w := hshift
        _ = w / α := hw_formula
        _ ≤ (u + v) / β := hcomp
        _ ≤ example_6_24_pi f u + example_6_24_pi f v := hsum_lower
    · -- If the reduced sum stays after the breakpoint, the same lower-slope comparison closes the
      -- estimate directly.
      have hw_break : α < w := by
        dsimp [w, α, β] at *
        linarith
      have hw_formula :
          example_6_24_pi f w = w / β := by
        simpa [β, α] using example_6_24_pi_rightBranch hw0 hw1 hw_break
      have hw_le : w / β ≤ (u + v) / β := by
        have hw_le_sum : w ≤ u + v := by
          dsimp [w]
          linarith
        exact (div_le_div_iff_of_pos_right hβ_pos).2 hw_le_sum
      have hsum_lower : (u + v) / β ≤ example_6_24_pi f u + example_6_24_pi f v := by
        calc
          (u + v) / β = u / β + v / β := by
            rw [add_div]
          _ ≤ example_6_24_pi f u + example_6_24_pi f v := add_le_add hu_lower hv_lower
      calc
        example_6_24_pi f (u + v) = example_6_24_pi f w := hshift
        _ = w / β := hw_formula
        _ ≤ (u + v) / β := hw_le
        _ ≤ example_6_24_pi f u + example_6_24_pi f v := hsum_lower

/-- Helper for Example 6.24: the displayed example is subadditive on all of `ℝ` after reducing
each argument to the fundamental interval. -/
theorem example_6_24_pi_subadditive
    {f : ℝ} (h₀ : 0 < 1 - f) :
    Function.Subadditive (example_6_24_pi f) := by
  intro r s
  let u : ℝ := Int.fract r
  let v : ℝ := Int.fract s
  have hu0 : 0 ≤ u := by
    dsimp [u]
    exact Int.fract_nonneg r
  have hu1 : u < 1 := by
    dsimp [u]
    exact Int.fract_lt_one r
  have hv0 : 0 ≤ v := by
    dsimp [v]
    exact Int.fract_nonneg s
  have hv1 : v < 1 := by
    dsimp [v]
    exact Int.fract_lt_one s
  have hr : example_6_24_pi f r = example_6_24_pi f u := by
    simpa [u] using example_6_24_pi_eq_fract f r
  have hs : example_6_24_pi f s = example_6_24_pi f v := by
    simpa [v] using example_6_24_pi_eq_fract f s
  have hsum :
      example_6_24_pi f (r + s) = example_6_24_pi f (u + v) := by
    have hper := (example_6_24_pi_periodic f).int_mul (Int.floor r + Int.floor s) (u + v)
    have hrewrite :
        u + v + (((Int.floor r + Int.floor s : ℤ) : ℝ) * 1) = r + s := by
      dsimp [u, v]
      rw [Int.cast_add, mul_one]
      have hr' : Int.fract r + (Int.floor r : ℝ) = r := Int.fract_add_floor r
      have hs' : Int.fract s + (Int.floor s : ℝ) = s := Int.fract_add_floor s
      nlinarith
    calc
      example_6_24_pi f (r + s)
          = example_6_24_pi f (u + v + (((Int.floor r + Int.floor s : ℤ) : ℝ) * 1)) := by
              rw [← hrewrite]
      _ = example_6_24_pi f (u + v) := hper
  calc
    example_6_24_pi f (r + s) = example_6_24_pi f (u + v) := hsum
    _ ≤ example_6_24_pi f u + example_6_24_pi f v :=
      example_6_24_pi_subadditiveOnIco h₀ hu0 hu1 hv0 hv1
    _ = example_6_24_pi f r + example_6_24_pi f s := by rw [hr, hs]

/-- Helper for Example 6.24: the discontinuous two-slope example satisfies the minimal-valid
criterion from Theorem 6.22. -/
theorem example_6_24_pi_minimal
    {f : ℝ} (h₀ : 0 < 1 - f) (h₁ : 1 - f < (1 : ℝ) / 2) :
    pure_integer_minimal_valid_function_on_R f (example_6_24_pi f) := by
  -- Route correction: package Example 6.24 through Theorem 6.22's scalar criterion rather than
  -- the continuity-based two-slope theorem.
  change pure_integer_minimal_valid_function (fun _ : Fin 1 ↦ f)
    (fun r : Fin 1 → ℝ ↦ example_6_24_pi f (r 0))
  refine pure_integer_minimal_valid_function_of_zero_subadditive_periodic_symmetry ?_ ?_ ?_ ?_ ?_
  · -- Nonnegativity reduces to the fundamental interval, where the right-slope lower bound is
    -- nonnegative.
    intro r
    let u : ℝ := Int.fract (r 0)
    have hu0 : 0 ≤ u := by
      dsimp [u]
      exact Int.fract_nonneg (r 0)
    have hu1 : u < 1 := by
      dsimp [u]
      exact Int.fract_lt_one (r 0)
    have hu_lower : u / (2 - f) ≤ example_6_24_pi f u := by
      simpa [u] using example_6_24_pi_ge_rightSlope h₀ hu0 hu1
    have hu_nonneg : 0 ≤ u / (2 - f) := by
      have hβ_pos : 0 < 2 - f := by
        linarith [h₀]
      positivity
    have hr_eq : example_6_24_pi f (r 0) = example_6_24_pi f u := by
      simpa [u] using example_6_24_pi_eq_fract f (r 0)
    rw [hr_eq]
    linarith
  · -- The origin lies in the left branch and keeps value `0`.
    have hzero : example_6_24_pi f 0 = 0 := by
      rw [example_6_24_pi_leftBranch (f := f) (u := 0)]
      · simp
      · norm_num
      · norm_num
      · linarith
    simpa using hzero
  · -- Scalar subadditivity transports directly to the `Fin 1` owner.
    intro r s
    simpa using example_6_24_pi_subadditive h₀ (r 0) (s 0)
  · -- Scalar `1`-periodicity yields invariance under every integer translate in dimension `1`.
    intro r w
    have hper := (example_6_24_pi_periodic f).int_mul (w 0) (r 0)
    simpa [one_mul, add_comm, add_left_comm, add_assoc] using hper.symm
  · -- The symmetry condition is already available in scalar form.
    intro r
    simpa using example_6_24_pi_symmetryReal h₀ h₁ (r 0)

/-- Example 6.24 (2). When the breakpoint `1 - f` lies in the fundamental interval `(0, 1)`, the
function from Fig. 6.9 is discontinuous there. -/
theorem example_6_24_pi_not_continuousAt
    {f : ℝ} (h_break : 1 - f ∈ Set.Ioo (0 : ℝ) 1) :
    ¬ ContinuousAt (example_6_24_pi f) (1 - f) := by
  intro hcont
  let α : ℝ := 1 - f
  have hα_pos : 0 < α := h_break.1
  have hα_lt_one : α < 1 := h_break.2
  have hf_pos : 0 < f := by
    dsimp [α] at *
    linarith
  have hvalue : example_6_24_pi f α = 1 := by
    simpa [α] using example_6_24_pi_breakpointValue h_break
  let u : ℕ → ℝ := fun n ↦ α + f / (n + 1)
  have hu_tendsto : Filter.Tendsto u Filter.atTop (nhds α) := by
    -- The right-approach sequence converges to the breakpoint because its correction term tends
    -- to zero.
    have hdiv :
        Filter.Tendsto (fun n : ℕ ↦ f / (n + 1 : ℝ)) Filter.atTop (nhds 0) := by
      have hbase :=
        (tendsto_const_div_atTop_nhds_zero_nat f).comp (Filter.tendsto_add_atTop_nat 1)
      convert hbase using 1
      ext n
      norm_num [Function.comp, Nat.cast_add, add_assoc, add_comm, add_left_comm]
    simpa [u] using tendsto_const_nhds.add hdiv
  have hu_right :
      ∀ᶠ n : ℕ in Filter.atTop, α < u n ∧ u n < 1 := by
    -- After the zeroth term, the sequence lies strictly inside the right branch.
    refine Filter.eventually_atTop.2 ?_
    refine ⟨1, ?_⟩
    intro n hn
    have hden_gt_one : (1 : ℝ) < n + 1 := by
      norm_num
      exact_mod_cast hn
    have hfrac_pos : 0 < f / (n + 1 : ℝ) := by
      positivity
    have hfrac_lt : f / (n + 1 : ℝ) < f := by
      have hden_ne : (n + 1 : ℝ) ≠ 0 := by positivity
      field_simp [hden_ne]
      nlinarith
    constructor
    · dsimp [u]
      linarith
    · dsimp [u, α]
      linarith
  have hseq_limit :
      Filter.Tendsto (fun n : ℕ ↦ example_6_24_pi f (u n)) Filter.atTop
        (nhds (α / (2 - f))) := by
    -- Eventually the sequence follows the right branch exactly, so its limit is the right-hand
    -- branch value at the breakpoint.
    have hbranch :
        ∀ᶠ n : ℕ in Filter.atTop, example_6_24_pi f (u n) = u n / (2 - f) := by
      filter_upwards [hu_right] with n hn
      have hu0 : 0 ≤ u n := by
        dsimp [u]
        linarith [h_break.1, hn.1]
      exact example_6_24_pi_rightBranch hu0 hn.2 (by simpa [α] using hn.1)
    have hquot :
        Filter.Tendsto (fun n : ℕ ↦ u n / (2 - f)) Filter.atTop
          (nhds (α / (2 - f))) := by
      simpa [u] using hu_tendsto.div_const (2 - f)
    have hbranchEq :
        (fun n : ℕ ↦ example_6_24_pi f (u n)) =ᶠ[Filter.atTop] fun n ↦ u n / (2 - f) := hbranch
    exact Filter.Tendsto.congr' hbranchEq.symm hquot
  have hcont_limit :
      Filter.Tendsto (fun n : ℕ ↦ example_6_24_pi f (u n)) Filter.atTop
        (nhds (example_6_24_pi f α)) :=
    hcont.tendsto.comp hu_tendsto
  have hlimit_eq : example_6_24_pi f α = α / (2 - f) :=
    tendsto_nhds_unique hcont_limit hseq_limit
  have hright_lt_one : α / (2 - f) < 1 := by
    have hβ_pos : 0 < 2 - f := by
      dsimp [α] at *
      linarith
    have hlt : α < 2 - f := by
      dsimp [α] at *
      linarith
    have hβ_ne : 2 - f ≠ 0 := by
      linarith
    field_simp [hβ_ne]
    linarith
  have : (1 : ℝ) = α / (2 - f) := by
    simpa [hvalue] using hlimit_eq
  linarith

/-- Example 6.24 (3). For `0 < 1 - f < 1/2`, the discontinuous two-slope function from Fig. 6.9
is a valid function for the one-dimensional pure integer infinite relaxation. -/
theorem example_6_24_pi_valid
    {f : ℝ} (h₀ : 0 < 1 - f) (h₁ : 1 - f < (1 : ℝ) / 2) :
    pure_integer_valid_function_on_R f (example_6_24_pi f) := by
  -- Theorem 6.22 already packages this example as minimal, hence valid.
  let _ : pure_integer_minimal_valid_function_on_R f (example_6_24_pi f) :=
    example_6_24_pi_minimal h₀ h₁
  infer_instance

/-- Under the source hypotheses of Example 6.24, `example_6_24_pi f` is available as a valid
function instance. -/
instance instExample624Valid
    {f : ℝ} [Fact (0 < 1 - f)] [Fact (1 - f < (1 : ℝ) / 2)] :
    pure_integer_valid_function_on_R f (example_6_24_pi f) :=
  example_6_24_pi_valid ‹Fact (0 < 1 - f)›.out ‹Fact (1 - f < (1 : ℝ) / 2)›.out

/-- Helper for Example 6.24: any valid midpoint components of `example_6_24_pi f` already agree
with the source function on the left branch `Set.Icc 0 (1 - f)`. -/
theorem example_6_24_midpointComponents_eqOn_leftBranch
    {f : ℝ} (h₀ : 0 < 1 - f) (h₁ : 1 - f < (1 : ℝ) / 2)
    {π₁ π₂ : ℝ → ℝ}
    (hπ₁ : pure_integer_valid_function_on_R f π₁)
    (hπ₂ : pure_integer_valid_function_on_R f π₂)
    (hmid : example_6_24_pi f = (1 / 2 : ℝ) • π₁ + (1 / 2 : ℝ) • π₂) :
    Set.EqOn (example_6_24_pi f) π₁ (Set.Icc (0 : ℝ) (1 - f)) ∧
      Set.EqOn (example_6_24_pi f) π₂ (Set.Icc (0 : ℝ) (1 - f)) := by
  let α : ℝ := 1 - f
  let π : ℝ → ℝ := example_6_24_pi f
  have hα_pos : 0 < α := h₀
  have hα_lt_one : α < 1 := by
    dsimp [α] at *
    linarith
  have hhalf_pos : 0 < α / 2 := by
    linarith
  have hπ : pure_integer_minimal_valid_function_on_R f π := example_6_24_pi_minimal h₀ h₁
  rcases midpointComponentsAreMinimalValidFunctionOnR hπ hπ₁ hπ₂ hmid with
    ⟨hπ₁_min, hπ₂_min⟩
  rcases pureIntegerMinimalValidFunctionOnR_periodicEndpoints hπ₁_min with
    ⟨_, hπ₁_zero, _, hπ₁_alpha, hπ₁_bdd⟩
  rcases pureIntegerMinimalValidFunctionOnR_periodicEndpoints hπ₂_min with
    ⟨_, hπ₂_zero, _, hπ₂_alpha, hπ₂_bdd⟩
  let hadd_transfer := scalarMidpointAdditivityTransfer hπ hπ₁ hπ₂ hmid
  have hπ_add :
      ∀ ⦃x y : ℝ⦄, x ∈ Set.Icc (0 : ℝ) (α / 2) → y ∈ Set.Icc (0 : ℝ) (α / 2) →
        π x + π y = π (x + y) := by
    intro x y hx hy
    have hx_lt_one : x < 1 := by
      linarith [hx.2, hα_lt_one]
    have hy_lt_one : y < 1 := by
      linarith [hy.2, hα_lt_one]
    have hx_le_alpha : x ≤ α := by
      linarith [hx.2]
    have hy_le_alpha : y ≤ α := by
      linarith [hy.2]
    have hxy_nonneg : 0 ≤ x + y := add_nonneg hx.1 hy.1
    have hxy_lt_one : x + y < 1 := by
      linarith [hx.2, hy.2, hα_lt_one]
    have hxy_le_alpha : x + y ≤ α := by
      linarith [hx.2, hy.2]
    -- On this left rectangle all three values use the same source branch `u ↦ u / (1 - f)`.
    dsimp [π]
    rw [example_6_24_pi_leftBranch hx.1 hx_lt_one (by simpa [α] using hx_le_alpha)]
    rw [example_6_24_pi_leftBranch hy.1 hy_lt_one (by simpa [α] using hy_le_alpha)]
    rw [example_6_24_pi_leftBranch hxy_nonneg hxy_lt_one (by simpa [α] using hxy_le_alpha)]
    have hα_ne : α ≠ 0 := by
      linarith
    field_simp [hα_ne]
  have hπ₁_add :
      ∀ ⦃x y : ℝ⦄, x ∈ Set.Icc (0 : ℝ) (α / 2) → y ∈ Set.Icc (0 : ℝ) (α / 2) →
        π₁ x + π₁ y = π₁ (x + y) := by
    intro x y hx hy
    exact (hadd_transfer (hπ_add hx hy)).1
  have hπ₂_add :
      ∀ ⦃x y : ℝ⦄, x ∈ Set.Icc (0 : ℝ) (α / 2) → y ∈ Set.Icc (0 : ℝ) (α / 2) →
        π₂ x + π₂ y = π₂ (x + y) := by
    intro x y hx hy
    exact (hadd_transfer (hπ_add hx hy)).2
  rcases interval_lemma_affine_with_common_slope
      (f := π₁) (a₁ := 0) (a₂ := α / 2) (b₁ := 0) (b₂ := α / 2)
      hπ₁_bdd hhalf_pos hhalf_pos
      (by
        intro x y hx hy
        exact hπ₁_add hx hy) with
    ⟨c₁, _gA₁, _gB₁, gAB₁, _hgA₁, _hgAeq₁, _hgB₁, _hgBeq₁, hgAB₁, hgABeq₁⟩
  rcases interval_lemma_affine_with_common_slope
      (f := π₂) (a₁ := 0) (a₂ := α / 2) (b₁ := 0) (b₂ := α / 2)
      hπ₂_bdd hhalf_pos hhalf_pos
      (by
        intro x y hx hy
        exact hπ₂_add hx hy) with
    ⟨c₂, _gA₂, _gB₂, gAB₂, _hgA₂, _hgAeq₂, _hgB₂, _hgBeq₂, hgAB₂, hgABeq₂⟩
  have hsum_half : α / 2 + α / 2 = α := by
    ring
  have hπ₁_affine_owner :
      ∃ g : ℝ →ᵃ[ℝ] ℝ,
        g.linear = (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight c₁ ∧
          Set.EqOn π₁ g (Set.Icc (0 : ℝ) α) := by
    refine ⟨gAB₁, hgAB₁, ?_⟩
    simpa [hsum_half] using hgABeq₁
  have hπ₂_affine_owner :
      ∃ g : ℝ →ᵃ[ℝ] ℝ,
        g.linear = (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight c₂ ∧
          Set.EqOn π₂ g (Set.Icc (0 : ℝ) α) := by
    refine ⟨gAB₂, hgAB₂, ?_⟩
    simpa [hsum_half] using hgABeq₂
  rcases (exists_affineMap_eqOn_iff (f := π₁) (s := Set.Icc (0 : ℝ) α) (c := c₁)).1
      hπ₁_affine_owner with
    ⟨d₁, hd₁⟩
  rcases (exists_affineMap_eqOn_iff (f := π₂) (s := Set.Icc (0 : ℝ) α) (c := c₂)).1
      hπ₂_affine_owner with
    ⟨d₂, hd₂⟩
  have hd₁_zero : d₁ = 0 := by
    have h0 := hd₁ (by exact ⟨le_rfl, le_of_lt hα_pos⟩)
    rw [hπ₁_zero] at h0
    linarith
  have hd₂_zero : d₂ = 0 := by
    have h0 := hd₂ (by exact ⟨le_rfl, le_of_lt hα_pos⟩)
    rw [hπ₂_zero] at h0
    linarith
  have hc₁ : c₁ = 1 / α := by
    have hα_mem : α ∈ Set.Icc (0 : ℝ) α := by
      exact ⟨le_of_lt hα_pos, le_rfl⟩
    have hα_eq := hd₁ hα_mem
    rw [hπ₁_alpha, hd₁_zero] at hα_eq
    have hα_ne : α ≠ 0 := by
      linarith
    apply (eq_div_iff hα_ne).2
    linarith
  have hc₂ : c₂ = 1 / α := by
    have hα_mem : α ∈ Set.Icc (0 : ℝ) α := by
      exact ⟨le_of_lt hα_pos, le_rfl⟩
    have hα_eq := hd₂ hα_mem
    rw [hπ₂_alpha, hd₂_zero] at hα_eq
    have hα_ne : α ≠ 0 := by
      linarith
    apply (eq_div_iff hα_ne).2
    linarith
  constructor
  · intro x hx
    have hx_lt_one : x < 1 := lt_of_le_of_lt hx.2 hα_lt_one
    have hπ_raw : π x = x / α := by
      simpa [π, α] using example_6_24_pi_leftBranch hx.1 hx_lt_one hx.2
    have hα_ne : α ≠ 0 := by
      linarith
    calc
      π x = x / α := hπ_raw
      _ = c₁ * x + d₁ := by
        rw [hc₁, hd₁_zero]
        field_simp [hα_ne]
        ring
      _ = π₁ x := by
        symm
        exact hd₁ hx
  · intro x hx
    have hx_lt_one : x < 1 := lt_of_le_of_lt hx.2 hα_lt_one
    have hπ_raw : π x = x / α := by
      simpa [π, α] using example_6_24_pi_leftBranch hx.1 hx_lt_one hx.2
    have hα_ne : α ≠ 0 := by
      linarith
    calc
      π x = x / α := hπ_raw
      _ = c₂ * x + d₂ := by
        rw [hc₂, hd₂_zero]
        field_simp [hα_ne]
        ring
      _ = π₂ x := by
        symm
        exact hd₂ hx

/-- Helper for Example 6.24: the midpoint components already take the source-normalized values at
the special right-branch points `(2 - f) / 3`, `2 * (2 - f) / 3`, and `(2 - f) / 2`. -/
theorem example_6_24_midpointComponents_rightSpecialValues
    {f : ℝ} (h₀ : 0 < 1 - f) (h₁ : 1 - f < (1 : ℝ) / 2)
    {π₁ π₂ : ℝ → ℝ}
    (hπ₁ : pure_integer_valid_function_on_R f π₁)
    (hπ₂ : pure_integer_valid_function_on_R f π₂)
    (hmid : example_6_24_pi f = (1 / 2 : ℝ) • π₁ + (1 / 2 : ℝ) • π₂) :
    π₁ ((2 - f) / 3) = example_6_24_pi f ((2 - f) / 3) ∧
      π₂ ((2 - f) / 3) = example_6_24_pi f ((2 - f) / 3) ∧
        π₁ (2 * ((2 - f) / 3)) = example_6_24_pi f (2 * ((2 - f) / 3)) ∧
          π₂ (2 * ((2 - f) / 3)) = example_6_24_pi f (2 * ((2 - f) / 3)) ∧
            π₁ ((2 - f) / 2) = example_6_24_pi f ((2 - f) / 2) ∧
              π₂ ((2 - f) / 2) = example_6_24_pi f ((2 - f) / 2) := by
  let α : ℝ := 1 - f
  let β : ℝ := 2 - f
  let x : ℝ := β / 3
  let m : ℝ := β / 2
  have hπ : pure_integer_minimal_valid_function_on_R f (example_6_24_pi f) :=
    example_6_24_pi_minimal h₀ h₁
  rcases midpointComponentsAreMinimalValidFunctionOnR hπ hπ₁ hπ₂ hmid with
    ⟨hπ₁_min, hπ₂_min⟩
  rcases pureIntegerMinimalValidFunctionOnR_periodicEndpoints hπ₁_min with
    ⟨hπ₁_periodic, _, _, _, _⟩
  rcases pureIntegerMinimalValidFunctionOnR_periodicEndpoints hπ₂_min with
    ⟨hπ₂_periodic, _, _, _, _⟩
  let hadd_transfer := scalarMidpointAdditivityTransfer hπ hπ₁ hπ₂ hmid
  have hβ_ne : β ≠ 0 := by
    dsimp [β]
    linarith [h₀]
  have hx_nonneg : 0 ≤ x := by
    dsimp [x, β]
    linarith [h₀]
  have hx_lt_one : x < 1 := by
    dsimp [x, β, α] at *
    linarith
  have hx_break : α < x := by
    dsimp [x, β, α] at *
    linarith
  have h2x_nonneg : 0 ≤ 2 * x := by
    linarith [hx_nonneg]
  have h2x_lt_one : 2 * x < 1 := by
    dsimp [x, β, α] at *
    linarith
  have h2x_break : α < 2 * x := by
    dsimp [x, β, α] at *
    linarith
  have hm_nonneg : 0 ≤ m := by
    dsimp [m, β]
    linarith [h₀]
  have hm_lt_one : m < 1 := by
    dsimp [m, β, α] at *
    linarith
  have hm_break : α < m := by
    dsimp [m, β, α] at *
    linarith
  have hπx_raw : example_6_24_pi f x = x / β := by
    -- The first anchor lies strictly inside the discontinuous right branch.
    simpa [α, β, x] using example_6_24_pi_rightBranch hx_nonneg hx_lt_one (by simpa [α] using hx_break)
  have hπ2x_raw : example_6_24_pi f (2 * x) = (2 * x) / β := by
    -- The doubled anchor stays inside the same right branch.
    simpa [α, β, x] using
      example_6_24_pi_rightBranch h2x_nonneg h2x_lt_one (by simpa [α] using h2x_break)
  have hπm_raw : example_6_24_pi f m = m / β := by
    -- The midpoint anchor is also a right-branch point.
    simpa [α, β, m] using example_6_24_pi_rightBranch hm_nonneg hm_lt_one (by simpa [α] using hm_break)
  have hπx : example_6_24_pi f x = 1 / 3 := by
    -- Evaluating the raw right-branch formula at `β / 3` gives the normalized value `1 / 3`.
    calc
      example_6_24_pi f x = x / β := hπx_raw
      _ = 1 / 3 := by
        dsimp [x]
        field_simp [hβ_ne]
  have hπ2x : example_6_24_pi f (2 * x) = 2 / 3 := by
    -- The doubled anchor similarly normalizes to `2 / 3`.
    calc
      example_6_24_pi f (2 * x) = (2 * x) / β := hπ2x_raw
      _ = 2 / 3 := by
        dsimp [x]
        field_simp [hβ_ne]
  have hπm : example_6_24_pi f m = 1 / 2 := by
    -- The midpoint `β / 2` gives the expected self-symmetric value `1 / 2`.
    calc
      example_6_24_pi f m = m / β := hπm_raw
      _ = 1 / 2 := by
        dsimp [m]
        field_simp [hβ_ne]
  have hπ_add_xx : example_6_24_pi f x + example_6_24_pi f x = example_6_24_pi f (x + x) := by
    -- Additivity holds because `x`, `x`, and `x + x` all stay in the right-branch affine window.
    calc
      example_6_24_pi f x + example_6_24_pi f x = x / β + x / β := by
        simpa [hπx_raw]
      _ = (2 * x) / β := by
        field_simp [hβ_ne]
        ring
      _ = example_6_24_pi f (2 * x) := by rw [hπ2x_raw]
      _ = example_6_24_pi f (x + x) := by congr 1; ring
  have hπ₁_add : π₁ x + π₁ x = π₁ (2 * x) := by
    -- Transfer this scalar additivity identity to the first midpoint component.
    simpa [two_mul] using (hadd_transfer hπ_add_xx).1
  have hπ₂_add : π₂ x + π₂ x = π₂ (2 * x) := by
    -- The same additivity transfer applies to the second midpoint component.
    simpa [two_mul] using (hadd_transfer hπ_add_xx).2
  have hπ₁_shift_x : π₁ (-f - x) = π₁ (2 * x) := by
    -- Periodicity rewrites the symmetry partner of `x` to the doubled anchor `2 * x`.
    calc
      π₁ (-f - x) = π₁ (((2 : ℤ) : ℝ) * 1 + (-f - x)) := by
        simpa [one_mul, add_assoc, add_left_comm, add_comm] using
          (hπ₁_periodic.int_mul (2 : ℤ) (-f - x)).symm
      _ = π₁ (2 - f - x) := by ring_nf
      _ = π₁ (2 * x) := by
        congr 1
        dsimp [x, β]
        ring
  have hπ₂_shift_x : π₂ (-f - x) = π₂ (2 * x) := by
    -- The second midpoint component has the same periodic rewrite.
    calc
      π₂ (-f - x) = π₂ (((2 : ℤ) : ℝ) * 1 + (-f - x)) := by
        simpa [one_mul, add_assoc, add_left_comm, add_comm] using
          (hπ₂_periodic.int_mul (2 : ℤ) (-f - x)).symm
      _ = π₂ (2 - f - x) := by ring_nf
      _ = π₂ (2 * x) := by
        congr 1
        dsimp [x, β]
        ring
  have hπ₁_sym_x : π₁ x + π₁ (2 * x) = 1 := by
    -- Symmetry at `x` closes the two-equation system with the transferred additivity identity.
    calc
      π₁ x + π₁ (2 * x) = π₁ x + π₁ (-f - x) := by rw [hπ₁_shift_x]
      _ = 1 := by
        simpa using pure_integer_minimal_valid_function_symmetry hπ₁_min (fun _ : Fin 1 ↦ x)
  have hπ₂_sym_x : π₂ x + π₂ (2 * x) = 1 := by
    -- The same symmetry equation holds for the second midpoint component.
    calc
      π₂ x + π₂ (2 * x) = π₂ x + π₂ (-f - x) := by rw [hπ₂_shift_x]
      _ = 1 := by
        simpa using pure_integer_minimal_valid_function_symmetry hπ₂_min (fun _ : Fin 1 ↦ x)
  have hπ₁_x : π₁ x = 1 / 3 := by
    -- Solve the first linear system `2π₁(x) = π₁(2x)` and `π₁(x) + π₁(2x) = 1`.
    linarith
  have hπ₂_x : π₂ x = 1 / 3 := by
    -- The second midpoint component satisfies the same linear system.
    linarith
  have hπ₁_2x : π₁ (2 * x) = 2 / 3 := by
    -- The doubled anchor value follows from the same system.
    linarith
  have hπ₂_2x : π₂ (2 * x) = 2 / 3 := by
    -- And likewise for the second midpoint component.
    linarith
  have hπ₁_shift_m : π₁ (-f - m) = π₁ m := by
    -- The midpoint is fixed by the reflected right-branch involution after a period shift.
    calc
      π₁ (-f - m) = π₁ (((2 : ℤ) : ℝ) * 1 + (-f - m)) := by
        simpa [one_mul, add_assoc, add_left_comm, add_comm] using
          (hπ₁_periodic.int_mul (2 : ℤ) (-f - m)).symm
      _ = π₁ (2 - f - m) := by ring_nf
      _ = π₁ m := by
        congr 1
        dsimp [m, β]
        ring
  have hπ₂_shift_m : π₂ (-f - m) = π₂ m := by
    -- The same fixed-point rewrite applies to the second midpoint component.
    calc
      π₂ (-f - m) = π₂ (((2 : ℤ) : ℝ) * 1 + (-f - m)) := by
        simpa [one_mul, add_assoc, add_left_comm, add_comm] using
          (hπ₂_periodic.int_mul (2 : ℤ) (-f - m)).symm
      _ = π₂ (2 - f - m) := by ring_nf
      _ = π₂ m := by
        congr 1
        dsimp [m, β]
        ring
  have hπ₁_m : π₁ m = 1 / 2 := by
    -- Symmetry at the fixed point `m` immediately gives the midpoint value.
    have hsym : π₁ m + π₁ m = 1 := by
      calc
        π₁ m + π₁ m = π₁ m + π₁ (-f - m) := by rw [hπ₁_shift_m]
        _ = 1 := by
          simpa using pure_integer_minimal_valid_function_symmetry hπ₁_min (fun _ : Fin 1 ↦ m)
    linarith
  have hπ₂_m : π₂ m = 1 / 2 := by
    -- The same fixed-point symmetry argument works for the second midpoint component.
    have hsym : π₂ m + π₂ m = 1 := by
      calc
        π₂ m + π₂ m = π₂ m + π₂ (-f - m) := by rw [hπ₂_shift_m]
        _ = 1 := by
          simpa using pure_integer_minimal_valid_function_symmetry hπ₂_min (fun _ : Fin 1 ↦ m)
    linarith
  refine ?_
  constructor
  · calc
      π₁ x = 1 / 3 := hπ₁_x
      _ = example_6_24_pi f x := hπx.symm
  constructor
  · calc
      π₂ x = 1 / 3 := hπ₂_x
      _ = example_6_24_pi f x := hπx.symm
  constructor
  · calc
      π₁ (2 * x) = 2 / 3 := hπ₁_2x
      _ = example_6_24_pi f (2 * x) := hπ2x.symm
  constructor
  · calc
      π₂ (2 * x) = 2 / 3 := hπ₂_2x
      _ = example_6_24_pi f (2 * x) := hπ2x.symm
  constructor
  · calc
      π₁ m = 1 / 2 := hπ₁_m
      _ = example_6_24_pi f m := hπm.symm
  · calc
      π₂ m = 1 / 2 := hπ₂_m
      _ = example_6_24_pi f m := hπm.symm

/-- Helper for Example 6.24: once the right-branch rigidity is available, the left and right
branch agreements assemble into equality on the full unit interval. -/
theorem example_6_24_midpointComponents_eqOn_unitInterval
    {f : ℝ} (h₀ : 0 < 1 - f) (h₁ : 1 - f < (1 : ℝ) / 2)
    {π₁ π₂ : ℝ → ℝ}
    (hπ₁ : pure_integer_valid_function_on_R f π₁)
    (hπ₂ : pure_integer_valid_function_on_R f π₂)
    (hmid : example_6_24_pi f = (1 / 2 : ℝ) • π₁ + (1 / 2 : ℝ) • π₂)
    (hright :
      Set.EqOn (example_6_24_pi f) π₁ (Set.Icc (1 - f) 1) ∧
        Set.EqOn (example_6_24_pi f) π₂ (Set.Icc (1 - f) 1)) :
    Set.EqOn (example_6_24_pi f) π₁ (Set.Icc (0 : ℝ) 1) ∧
      Set.EqOn (example_6_24_pi f) π₂ (Set.Icc (0 : ℝ) 1) := by
  rcases example_6_24_midpointComponents_eqOn_leftBranch h₀ h₁ hπ₁ hπ₂ hmid with
    ⟨hleft₁, hleft₂⟩
  rcases hright with ⟨hright₁, hright₂⟩
  constructor
  · intro x hx
    by_cases hx_left : x ≤ 1 - f
    · exact hleft₁ ⟨hx.1, hx_left⟩
    · exact hright₁ ⟨le_of_lt (lt_of_not_ge hx_left), hx.2⟩
  · intro x hx
    by_cases hx_left : x ≤ 1 - f
    · exact hleft₂ ⟨hx.1, hx_left⟩
    · exact hright₂ ⟨le_of_lt (lt_of_not_ge hx_left), hx.2⟩

/-- Helper for Example 6.24: two affine descriptions with the same slope agree on an interval as
soon as they agree at one anchor point in that interval. -/
theorem eqOn_ofSharedAffineSlopeAndPointValue
    {φ ψ : ℝ → ℝ} {a b anchor sigma dφ dψ : ℝ}
    (hanchor : anchor ∈ Set.Icc a b)
    (hφ : Set.EqOn φ (fun x ↦ sigma * x + dφ) (Set.Icc a b))
    (hψ : Set.EqOn ψ (fun x ↦ sigma * x + dψ) (Set.Icc a b))
    (hvalue : φ anchor = ψ anchor) :
    Set.EqOn φ ψ (Set.Icc a b) := by
  have hd : dφ = dψ := by
    -- Matching the two affine models at the anchor point identifies the intercept.
    have hφ_anchor := hφ hanchor
    have hψ_anchor := hψ hanchor
    linarith
  intro x hx
  -- Once the intercepts coincide, both affine descriptions are literally the same function.
  rw [hφ hx, hψ hx, hd]

/-- Helper for Example 6.24: affine formulas agreeing at two distinct points have the same
slope. -/
theorem affineSlope_eq_of_eqAt_twoPoints
    {c d sigma e x y : ℝ} (hxy : x < y)
    (hx : c * x + d = sigma * x + e) (hy : c * y + d = sigma * y + e) :
    c = sigma := by
  -- Subtract the endpoint identities and cancel their nonzero separation.
  have hmul : (c - sigma) * (y - x) = 0 := by
    linear_combination hy - hx
  have hsep : y - x ≠ 0 := sub_ne_zero.mpr hxy.ne'
  exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hsep)

/-- Helper for Example 6.24: compatible affine formulas on nested closed intervals patch to an
affine formula on their half-open union. -/
theorem existsAffineFormulaOnIco_of_nestedAffineFormulas
    {φ : ℝ → ℝ} {x q₀ m : ℝ} (hxq₀ : x < q₀) (hq₀m : q₀ < m)
    (hlocal :
      ∀ q : ℝ, q₀ < q → q < m →
        ∃ c d : ℝ, Set.EqOn φ (fun u ↦ c * u + d) (Set.Icc x q)) :
    ∃ c d : ℝ, Set.EqOn φ (fun u ↦ c * u + d) (Set.Ico x m) := by
  let q₁ : ℝ := (q₀ + m) / 2
  have hq₀q₁ : q₀ < q₁ := by
    dsimp [q₁]
    linarith
  have hq₁m : q₁ < m := by
    dsimp [q₁]
    linarith
  rcases hlocal q₁ hq₀q₁ hq₁m with ⟨c, d, hbase⟩
  refine ⟨c, d, ?_⟩
  intro u hu
  by_cases huq₁ : u ≤ q₁
  · -- The initial affine chart already covers this point.
    exact hbase ⟨hu.1, huq₁⟩
  · -- A larger chart overlaps the initial one at two points, so their slopes and intercepts agree.
    let q : ℝ := (u + m) / 2
    have huq : u < q := by
      dsimp [q]
      linarith [hu.2]
    have hqm : q < m := by
      dsimp [q]
      linarith [hu.2]
    have hq₀q : q₀ < q := by
      linarith [hq₀q₁, lt_of_not_ge huq₁, huq]
    rcases hlocal q hq₀q hqm with ⟨c', d', hext⟩
    have hx_base : x ∈ Set.Icc x q₁ := ⟨le_rfl, (hxq₀.trans hq₀q₁).le⟩
    have hq₀_base : q₀ ∈ Set.Icc x q₁ := ⟨hxq₀.le, hq₀q₁.le⟩
    have hx_ext : x ∈ Set.Icc x q := ⟨le_rfl, (hxq₀.trans hq₀q).le⟩
    have hq₀_ext : q₀ ∈ Set.Icc x q := ⟨hxq₀.le, hq₀q.le⟩
    have hx_eq : c' * x + d' = c * x + d := by
      calc
        c' * x + d' = φ x := (hext hx_ext).symm
        _ = c * x + d := hbase hx_base
    have hq₀_eq : c' * q₀ + d' = c * q₀ + d := by
      calc
        c' * q₀ + d' = φ q₀ := (hext hq₀_ext).symm
        _ = c * q₀ + d := hbase hq₀_base
    have hc : c' = c := by
      exact affineSlope_eq_of_eqAt_twoPoints hxq₀ hx_eq hq₀_eq
    have hd : d' = d := by
      rw [hc] at hx_eq
      linarith [hx_eq]
    calc
      φ u = c' * u + d' := hext ⟨hu.1, huq.le⟩
      _ = c * u + d := by rw [hc, hd]

/-- Helper for Example 6.24: when `(2 - f) / 6` already lies strictly to the right of the source
breakpoint, the core window is the sum of the right-branch cell `[(2 - f) / 6, (2 - f) / 3]`
with itself, so Lemma 6.26 makes both midpoint components affine on the whole core window. -/
theorem example_6_24_midpointComponents_eqOn_coreWindow_of_smallBeta
    {f : ℝ} (h₀ : 0 < 1 - f) (h₁ : 1 - f < (1 : ℝ) / 2)
    (hβ_small : 2 - f < (6 : ℝ) / 5)
    {π₁ π₂ : ℝ → ℝ}
    (hπ₁ : pure_integer_valid_function_on_R f π₁)
    (hπ₂ : pure_integer_valid_function_on_R f π₂)
    (hmid : example_6_24_pi f = (1 / 2 : ℝ) • π₁ + (1 / 2 : ℝ) • π₂) :
    Set.EqOn (example_6_24_pi f) π₁ (Set.Icc ((2 - f) / 3) (2 * ((2 - f) / 3))) ∧
      Set.EqOn (example_6_24_pi f) π₂ (Set.Icc ((2 - f) / 3) (2 * ((2 - f) / 3))) := by
  let α : ℝ := 1 - f
  let β : ℝ := 2 - f
  let a : ℝ := β / 6
  let x : ℝ := β / 3
  let y : ℝ := 2 * x
  let π : ℝ → ℝ := example_6_24_pi f
  have hα_pos : 0 < α := h₀
  have hβ_pos : 0 < β := by
    dsimp [β, α]
    linarith
  have hβ_ne : β ≠ 0 := by
    linarith
  have ha_lt_x : a < x := by
    dsimp [a, x, β]
    linarith
  have hα_lt_a : α < a := by
    dsimp [a, β, α] at *
    linarith
  have ha_nonneg : 0 ≤ a := by
    dsimp [a, β]
    linarith
  have hx_nonneg : 0 ≤ x := by
    dsimp [x, β]
    linarith
  have hx_lt_one : x < 1 := by
    dsimp [x, β, α] at *
    linarith
  have hy_nonneg : 0 ≤ y := by
    dsimp [y]
    linarith [hx_nonneg]
  have hy_lt_one : y < 1 := by
    dsimp [y, x, β, α] at *
    linarith
  have hx_break : α < x := by
    dsimp [x, β, α] at *
    linarith
  have hy_break : α < y := by
    dsimp [y, x, β, α] at *
    linarith
  have hπ : pure_integer_minimal_valid_function_on_R f π := example_6_24_pi_minimal h₀ h₁
  rcases midpointComponentsAreMinimalValidFunctionOnR hπ hπ₁ hπ₂ hmid with
    ⟨hπ₁_min, hπ₂_min⟩
  rcases pureIntegerMinimalValidFunctionOnR_periodicEndpoints hπ₁_min with
    ⟨_, _, _, _, hπ₁_bdd⟩
  rcases pureIntegerMinimalValidFunctionOnR_periodicEndpoints hπ₂_min with
    ⟨_, _, _, _, hπ₂_bdd⟩
  rcases example_6_24_midpointComponents_rightSpecialValues h₀ h₁ hπ₁ hπ₂ hmid with
    ⟨hx₁, hx₂, hy₁, hy₂, _, _⟩
  let hadd_transfer := scalarMidpointAdditivityTransfer hπ hπ₁ hπ₂ hmid
  have hπx : π x = 1 / 3 := by
    -- The first core anchor still lies on the source right branch.
    have hraw : π x = x / β := by
      simpa [π, β] using example_6_24_pi_rightBranch hx_nonneg hx_lt_one (by simpa [α] using hx_break)
    calc
      π x = x / β := hraw
      _ = 1 / 3 := by
        dsimp [x]
        field_simp [hβ_ne]
  have hπy : π y = 2 / 3 := by
    -- Doubling the first anchor keeps the source inside the same affine branch.
    have hraw : π y = y / β := by
      simpa [π, β] using
        example_6_24_pi_rightBranch hy_nonneg hy_lt_one (by simpa [α] using hy_break)
    calc
      π y = y / β := hraw
      _ = 2 / 3 := by
        dsimp [y, x]
        field_simp [hβ_ne]
  have hπ_add :
      ∀ ⦃u v : ℝ⦄, u ∈ Set.Icc a x → v ∈ Set.Icc a x → π u + π v = π (u + v) := by
    intro u v hu hv
    have hu_lt_one : u < 1 := lt_of_le_of_lt hu.2 hx_lt_one
    have hv_lt_one : v < 1 := lt_of_le_of_lt hv.2 hx_lt_one
    have hu_break : α < u := lt_of_lt_of_le hα_lt_a hu.1
    have hv_break : α < v := lt_of_lt_of_le hα_lt_a hv.1
    have huv_nonneg : 0 ≤ u + v := add_nonneg (le_trans ha_nonneg hu.1) (le_trans ha_nonneg hv.1)
    have huv_lt_one : u + v < 1 := by
      have huv_le : u + v ≤ y := by
        have huv_le' : u + v ≤ x + x := add_le_add hu.2 hv.2
        simpa [y, two_mul] using huv_le'
      linarith
    have huv_break : α < u + v := by
      linarith [hu_break, hv.1]
    -- All three points lie in the same affine right branch, so the source is literally additive.
    have hu_formula : π u = u / β := by
      simpa [π, β] using
        example_6_24_pi_rightBranch (le_trans ha_nonneg hu.1) hu_lt_one (by simpa [α] using hu_break)
    have hv_formula : π v = v / β := by
      simpa [π, β] using
        example_6_24_pi_rightBranch (le_trans ha_nonneg hv.1) hv_lt_one (by simpa [α] using hv_break)
    have huv_formula : π (u + v) = (u + v) / β := by
      simpa [π, β] using
        example_6_24_pi_rightBranch huv_nonneg huv_lt_one (by simpa [α] using huv_break)
    rw [hu_formula, hv_formula, huv_formula]
    field_simp [hβ_ne]
  have hπ₁_add :
      ∀ ⦃u v : ℝ⦄, u ∈ Set.Icc a x → v ∈ Set.Icc a x → π₁ u + π₁ v = π₁ (u + v) := by
    intro u v hu hv
    exact (hadd_transfer (hπ_add hu hv)).1
  have hπ₂_add :
      ∀ ⦃u v : ℝ⦄, u ∈ Set.Icc a x → v ∈ Set.Icc a x → π₂ u + π₂ v = π₂ (u + v) := by
    intro u v hu hv
    exact (hadd_transfer (hπ_add hu hv)).2
  rcases interval_lemma_affine_with_common_slope
      (f := π₁) (a₁ := a) (a₂ := x) (b₁ := a) (b₂ := x)
      hπ₁_bdd ha_lt_x ha_lt_x
      (by
        intro u v hu hv
        exact hπ₁_add hu hv) with
    ⟨c₁, _gA₁, _gB₁, gAB₁, _hgA₁, _hgAeq₁, _hgB₁, _hgBeq₁, hgAB₁, hgABeq₁⟩
  rcases interval_lemma_affine_with_common_slope
      (f := π₂) (a₁ := a) (a₂ := x) (b₁ := a) (b₂ := x)
      hπ₂_bdd ha_lt_x ha_lt_x
      (by
        intro u v hu hv
        exact hπ₂_add hu hv) with
    ⟨c₂, _gA₂, _gB₂, gAB₂, _hgA₂, _hgAeq₂, _hgB₂, _hgBeq₂, hgAB₂, hgABeq₂⟩
  have hπ₁_affine_owner :
      ∃ g : ℝ →ᵃ[ℝ] ℝ,
        g.linear = (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight c₁ ∧
          Set.EqOn π₁ g (Set.Icc x y) := by
    refine ⟨gAB₁, hgAB₁, ?_⟩
    have hsum_left : a + a = x := by
      dsimp [a, x]
      ring
    simpa [hsum_left, y, two_mul, add_assoc, add_left_comm, add_comm] using hgABeq₁
  have hπ₂_affine_owner :
      ∃ g : ℝ →ᵃ[ℝ] ℝ,
        g.linear = (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight c₂ ∧
          Set.EqOn π₂ g (Set.Icc x y) := by
    refine ⟨gAB₂, hgAB₂, ?_⟩
    have hsum_left : a + a = x := by
      dsimp [a, x]
      ring
    simpa [hsum_left, y, two_mul, add_assoc, add_left_comm, add_comm] using hgABeq₂
  rcases (exists_affineMap_eqOn_iff (f := π₁) (s := Set.Icc x y) (c := c₁)).1 hπ₁_affine_owner with
    ⟨d₁, hd₁⟩
  rcases (exists_affineMap_eqOn_iff (f := π₂) (s := Set.Icc x y) (c := c₂)).1 hπ₂_affine_owner with
    ⟨d₂, hd₂⟩
  have hx_mem : x ∈ Set.Icc x y := by
    constructor
    · exact le_rfl
    · dsimp [y]
      linarith [hx_nonneg]
  have hy_mem : y ∈ Set.Icc x y := by
    constructor
    · dsimp [y]
      linarith [hx_nonneg]
    · exact le_rfl
  have hc₁ : c₁ = 1 / β := by
    -- The shared endpoint values at `x` and `y` pin down the slope on the whole core window.
    have hx_formula := hd₁ hx_mem
    have hy_formula := hd₁ hy_mem
    have hdiff : c₁ * (y - x) = π₁ y - π₁ x := by
      linarith
    have hcore_step : c₁ * (β / 3) = 1 / 3 := by
      rw [show y - x = β / 3 by
        dsimp [y, x, β]
        ring] at hdiff
      have hdiff' := hdiff
      rw [hx₁, hy₁] at hdiff'
      have hdiff'' : c₁ * (β / 3) = π y - π x := by
        simpa [π, x, y] using hdiff'
      linarith [hdiff'', hπx, hπy]
    apply (eq_div_iff hβ_ne).2
    linarith
  have hc₂ : c₂ = 1 / β := by
    -- The second midpoint component is normalized by the same endpoint comparison.
    have hx_formula := hd₂ hx_mem
    have hy_formula := hd₂ hy_mem
    have hdiff : c₂ * (y - x) = π₂ y - π₂ x := by
      linarith
    have hcore_step : c₂ * (β / 3) = 1 / 3 := by
      rw [show y - x = β / 3 by
        dsimp [y, x, β]
        ring] at hdiff
      have hdiff' := hdiff
      rw [hx₂, hy₂] at hdiff'
      have hdiff'' : c₂ * (β / 3) = π y - π x := by
        simpa [π, x, y] using hdiff'
      linarith [hdiff'', hπx, hπy]
    apply (eq_div_iff hβ_ne).2
    linarith
  have hπ_core : Set.EqOn π (fun u ↦ (1 / β) * u + 0) (Set.Icc x y) := by
    intro u hu
    have hu_lt_one : u < 1 := lt_of_le_of_lt hu.2 hy_lt_one
    have hu_break : α < u := lt_of_lt_of_le hx_break hu.1
    -- Every point of the core window stays on the source right branch.
    calc
      π u = u / β := by
        simpa [π, β] using
          example_6_24_pi_rightBranch (le_trans hx_nonneg hu.1) hu_lt_one (by simpa [α] using hu_break)
      _ = (1 / β) * u + 0 := by
        field_simp [hβ_ne]
        ring
  have hπ₁_core_affine : Set.EqOn π₁ (fun u ↦ (1 / β) * u + d₁) (Set.Icc x y) := by
    intro u hu
    simpa [hc₁, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using hd₁ hu
  have hπ₂_core_affine : Set.EqOn π₂ (fun u ↦ (1 / β) * u + d₂) (Set.Icc x y) := by
    intro u hu
    simpa [hc₂, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using hd₂ hu
  constructor
  · -- Matching the source at `x` upgrades the affine midpoint component to equality on the core.
    exact eqOn_ofSharedAffineSlopeAndPointValue hx_mem hπ_core hπ₁_core_affine hx₁.symm
  · -- The same anchor-value comparison closes the second midpoint component.
    exact eqOn_ofSharedAffineSlopeAndPointValue hx_mem hπ_core hπ₂_core_affine hx₂.symm

/-- Helper for Example 6.24: below the boundary value `1 - f = 1 / 3`, an auxiliary interval
strictly between `1 - f` and `f / 2` transports the right-branch slope to the lower half of the
core window; symmetry supplies the upper half. -/
theorem example_6_24_midpointComponents_eqOn_coreWindow_of_lt_third
    {f : ℝ} (h₀ : 0 < 1 - f) (h₁ : 1 - f < (1 : ℝ) / 2)
    (hthird : 1 - f < (1 : ℝ) / 3)
    {π₁ π₂ : ℝ → ℝ}
    (hπ₁ : pure_integer_valid_function_on_R f π₁)
    (hπ₂ : pure_integer_valid_function_on_R f π₂)
    (hmid : example_6_24_pi f = (1 / 2 : ℝ) • π₁ + (1 / 2 : ℝ) • π₂) :
    Set.EqOn (example_6_24_pi f) π₁ (Set.Icc ((2 - f) / 3) (2 * ((2 - f) / 3))) ∧
      Set.EqOn (example_6_24_pi f) π₂ (Set.Icc ((2 - f) / 3) (2 * ((2 - f) / 3))) := by
  let α : ℝ := 1 - f
  let β : ℝ := 2 - f
  let x : ℝ := β / 3
  let m : ℝ := β / 2
  let y : ℝ := 2 * x
  let a : ℝ := (α + (1 - m)) / 2
  let b : ℝ := (a + (1 - m)) / 2
  let π : ℝ → ℝ := example_6_24_pi f
  have hα_pos : 0 < α := h₀
  have hα_lt_anchor : α < 1 - m := by
    dsimp [α, m, β] at *
    linarith
  have hα_lt_a : α < a := by
    dsimp [a]
    linarith
  have ha_lt_b : a < b := by
    dsimp [b, a]
    linarith
  have hb_lt_anchor : b < 1 - m := by
    dsimp [b, a]
    linarith
  have hx_lt_m : x < m := by
    dsimp [x, m, β, α]
    linarith
  have hx_nonneg : 0 ≤ x := by
    dsimp [x, β, α]
    linarith
  have hx_break : α < x := by
    dsimp [x, β, α] at *
    linarith
  have hm_lt_one : m < 1 := by
    dsimp [m, β, α] at *
    linarith
  have hy_lt_one : y < 1 := by
    dsimp [y, x, β, α] at *
    linarith
  have hxy : x + y = β := by
    dsimp [x, y]
    ring
  have hmm : m + m = β := by
    dsimp [m]
    ring
  have hβ_ne : β ≠ 0 := by
    dsimp [β, α]
    linarith
  have hβ_pos : 0 < β := by
    dsimp [β, α]
    linarith
  have hπ : pure_integer_minimal_valid_function_on_R f π :=
    example_6_24_pi_minimal h₀ h₁
  rcases midpointComponentsAreMinimalValidFunctionOnR hπ hπ₁ hπ₂ hmid with
    ⟨hπ₁_min, hπ₂_min⟩
  rcases pureIntegerMinimalValidFunctionOnR_periodicEndpoints hπ₁_min with
    ⟨hπ₁_periodic, _, _, _, hπ₁_bdd⟩
  rcases pureIntegerMinimalValidFunctionOnR_periodicEndpoints hπ₂_min with
    ⟨hπ₂_periodic, _, _, _, hπ₂_bdd⟩
  rcases example_6_24_midpointComponents_rightSpecialValues h₀ h₁ hπ₁ hπ₂ hmid with
    ⟨hx₁, hx₂, _, _, hm₁, hm₂⟩
  let hadd_transfer := scalarMidpointAdditivityTransfer hπ hπ₁ hπ₂ hmid
  have hπ_add :
      ∀ ⦃u v : ℝ⦄, u ∈ Set.Icc a b → v ∈ Set.Icc x m → π u + π v = π (u + v) := by
    intro u v hu hv
    have hu_nonneg : 0 ≤ u := by
      linarith [hα_pos, hα_lt_a, hu.1]
    have hv_nonneg : 0 ≤ v := le_trans hx_nonneg hv.1
    have hu_lt_one : u < 1 := by
      linarith [hu.2, hb_lt_anchor]
    have hv_lt_one : v < 1 := lt_of_le_of_lt hv.2 hm_lt_one
    have hu_break : α < u := lt_of_lt_of_le hα_lt_a hu.1
    have hv_break : α < v := lt_of_lt_of_le hx_break hv.1
    have huv_nonneg : 0 ≤ u + v := add_nonneg hu_nonneg hv_nonneg
    have huv_lt_one : u + v < 1 := by
      linarith [hu.2, hv.2, hb_lt_anchor]
    have huv_break : α < u + v := by
      linarith [hu_break, hv_nonneg]
    -- All three arguments remain in the same affine right branch, so the source is additive.
    have hu_formula : π u = u / β := by
      simpa [π, β] using
        example_6_24_pi_rightBranch hu_nonneg hu_lt_one (by simpa [α] using hu_break)
    have hv_formula : π v = v / β := by
      simpa [π, β] using
        example_6_24_pi_rightBranch hv_nonneg hv_lt_one (by simpa [α] using hv_break)
    have huv_formula : π (u + v) = (u + v) / β := by
      simpa [π, β] using
        example_6_24_pi_rightBranch huv_nonneg huv_lt_one (by simpa [α] using huv_break)
    rw [hu_formula, hv_formula, huv_formula]
    field_simp [hβ_ne]
  have hπ₁_add :
      ∀ ⦃u v : ℝ⦄, u ∈ Set.Icc a b → v ∈ Set.Icc x m → π₁ u + π₁ v = π₁ (u + v) := by
    intro u v hu hv
    exact (hadd_transfer (hπ_add hu hv)).1
  have hπ₂_add :
      ∀ ⦃u v : ℝ⦄, u ∈ Set.Icc a b → v ∈ Set.Icc x m → π₂ u + π₂ v = π₂ (u + v) := by
    intro u v hu hv
    exact (hadd_transfer (hπ_add hu hv)).2
  rcases interval_lemma_affine_with_common_slope hπ₁_bdd ha_lt_b hx_lt_m
      (by
        intro u v hu hv
        exact hπ₁_add hu hv) with
    ⟨c₁, _gA₁, gB₁, _gAB₁, _hgA₁, _hgAeq₁, hgB₁, hgBeq₁, _hgAB₁, _hgABeq₁⟩
  rcases interval_lemma_affine_with_common_slope hπ₂_bdd ha_lt_b hx_lt_m
      (by
        intro u v hu hv
        exact hπ₂_add hu hv) with
    ⟨c₂, _gA₂, gB₂, _gAB₂, _hgA₂, _hgAeq₂, hgB₂, hgBeq₂, _hgAB₂, _hgABeq₂⟩
  have hπ₁_affine_owner :
      ∃ g : ℝ →ᵃ[ℝ] ℝ,
        g.linear = (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight c₁ ∧
          Set.EqOn π₁ g (Set.Icc x m) := by
    exact ⟨gB₁, hgB₁, hgBeq₁⟩
  have hπ₂_affine_owner :
      ∃ g : ℝ →ᵃ[ℝ] ℝ,
        g.linear = (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight c₂ ∧
          Set.EqOn π₂ g (Set.Icc x m) := by
    exact ⟨gB₂, hgB₂, hgBeq₂⟩
  rcases (exists_affineMap_eqOn_iff (f := π₁) (s := Set.Icc x m) (c := c₁)).1
      hπ₁_affine_owner with ⟨d₁, hd₁⟩
  rcases (exists_affineMap_eqOn_iff (f := π₂) (s := Set.Icc x m) (c := c₂)).1
      hπ₂_affine_owner with ⟨d₂, hd₂⟩
  have hx_mem : x ∈ Set.Icc x m := ⟨le_rfl, hx_lt_m.le⟩
  have hm_mem : m ∈ Set.Icc x m := ⟨hx_lt_m.le, le_rfl⟩
  have hπx : π x = x / β := by
    simpa [π, β] using example_6_24_pi_rightBranch hx_nonneg (lt_trans hx_lt_m hm_lt_one)
      (by simpa [α] using hx_break)
  have hπm : π m = m / β := by
    have hm_nonneg : 0 ≤ m := le_trans hx_nonneg hx_lt_m.le
    have hm_break : α < m := lt_trans hx_break hx_lt_m
    simpa [π, β] using
      example_6_24_pi_rightBranch hm_nonneg hm_lt_one (by simpa [α] using hm_break)
  have hc₁ : c₁ = 1 / β := by
    have hx_component : π₁ x = π x := by
      simpa [π, x] using hx₁
    have hm_component : π₁ m = π m := by
      simpa [π, m] using hm₁
    have hx_compare : c₁ * x + d₁ = (1 / β) * x + 0 := by
      calc
        c₁ * x + d₁ = π₁ x := (hd₁ hx_mem).symm
        _ = π x := hx_component
        _ = x / β := hπx
        _ = (1 / β) * x + 0 := by ring
    have hm_compare : c₁ * m + d₁ = (1 / β) * m + 0 := by
      calc
        c₁ * m + d₁ = π₁ m := (hd₁ hm_mem).symm
        _ = π m := hm_component
        _ = m / β := hπm
        _ = (1 / β) * m + 0 := by ring
    exact affineSlope_eq_of_eqAt_twoPoints hx_lt_m hx_compare hm_compare
  have hc₂ : c₂ = 1 / β := by
    have hx_component : π₂ x = π x := by
      simpa [π, x] using hx₂
    have hm_component : π₂ m = π m := by
      simpa [π, m] using hm₂
    have hx_compare : c₂ * x + d₂ = (1 / β) * x + 0 := by
      calc
        c₂ * x + d₂ = π₂ x := (hd₂ hx_mem).symm
        _ = π x := hx_component
        _ = x / β := hπx
        _ = (1 / β) * x + 0 := by ring
    have hm_compare : c₂ * m + d₂ = (1 / β) * m + 0 := by
      calc
        c₂ * m + d₂ = π₂ m := (hd₂ hm_mem).symm
        _ = π m := hm_component
        _ = m / β := hπm
        _ = (1 / β) * m + 0 := by ring
    exact affineSlope_eq_of_eqAt_twoPoints hx_lt_m hx_compare hm_compare
  have hπ_lower : Set.EqOn π (fun u ↦ (1 / β) * u + 0) (Set.Icc x m) := by
    intro u hu
    have hu_nonneg : 0 ≤ u := le_trans hx_nonneg hu.1
    have hu_lt_one : u < 1 := lt_of_le_of_lt hu.2 hm_lt_one
    have hu_break : α < u := lt_of_lt_of_le hx_break hu.1
    calc
      π u = u / β := by
        simpa [π, β] using
          example_6_24_pi_rightBranch hu_nonneg hu_lt_one (by simpa [α] using hu_break)
      _ = (1 / β) * u + 0 := by
        field_simp [hβ_ne]
        ring
  have hπ₁_lower_affine : Set.EqOn π₁ (fun u ↦ (1 / β) * u + d₁) (Set.Icc x m) := by
    intro u hu
    simpa [hc₁, mul_comm] using hd₁ hu
  have hπ₂_lower_affine : Set.EqOn π₂ (fun u ↦ (1 / β) * u + d₂) (Set.Icc x m) := by
    intro u hu
    simpa [hc₂, mul_comm] using hd₂ hu
  have hlower₁ : Set.EqOn π π₁ (Set.Icc x m) :=
    eqOn_ofSharedAffineSlopeAndPointValue hx_mem hπ_lower hπ₁_lower_affine hx₁.symm
  have hlower₂ : Set.EqOn π π₂ (Set.Icc x m) :=
    eqOn_ofSharedAffineSlopeAndPointValue hx_mem hπ_lower hπ₂_lower_affine hx₂.symm
  have hshift₁ (u : ℝ) : π₁ (u - 2) = π₁ u := by
    have hper := hπ₁_periodic.int_mul (-2) u
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hper
  have hshift₂ (u : ℝ) : π₂ (u - 2) = π₂ u := by
    have hper := hπ₂_periodic.int_mul (-2) u
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hper
  have hupper₁ : Set.EqOn π π₁ (Set.Icc m y) := by
    intro u hu
    let v : ℝ := β - u
    have hv_mem : v ∈ Set.Icc x m := by
      constructor
      · dsimp [v]
        linarith [hu.2, hxy]
      · dsimp [v]
        linarith [hu.1, hmm]
    have hπ_sym : π v + π u = 1 := by
      have hbase := example_6_24_pi_symmetryReal h₀ h₁ v
      have hrewrite : -f - v = u - 2 := by
        dsimp [v, β]
        ring
      have hshift : example_6_24_pi f (u - 2) = π u := by
        simpa [π] using (show π (u - 2) = π u by
          have hper := (example_6_24_pi_periodic f).int_mul (-2) u
          simpa [π, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hper)
      rw [hrewrite, hshift] at hbase
      simpa [π] using hbase
    have hπ₁_sym : π₁ v + π₁ u = 1 := by
      have hbase : π₁ v + π₁ (-f - v) = 1 := by
        simpa using pure_integer_minimal_valid_function_symmetry hπ₁_min (fun _ : Fin 1 ↦ v)
      have hrewrite : -f - v = u - 2 := by
        dsimp [v, β]
        ring
      rw [hrewrite, hshift₁ u] at hbase
      exact hbase
    have hv_eq : π v = π₁ v := hlower₁ hv_mem
    linarith
  have hupper₂ : Set.EqOn π π₂ (Set.Icc m y) := by
    intro u hu
    let v : ℝ := β - u
    have hv_mem : v ∈ Set.Icc x m := by
      constructor
      · dsimp [v]
        linarith [hu.2, hxy]
      · dsimp [v]
        linarith [hu.1, hmm]
    have hπ_sym : π v + π u = 1 := by
      have hbase := example_6_24_pi_symmetryReal h₀ h₁ v
      have hrewrite : -f - v = u - 2 := by
        dsimp [v, β]
        ring
      have hper := (example_6_24_pi_periodic f).int_mul (-2) u
      have hshift : example_6_24_pi f (u - 2) = π u := by
        simpa [π, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hper
      rw [hrewrite, hshift] at hbase
      simpa [π] using hbase
    have hπ₂_sym : π₂ v + π₂ u = 1 := by
      have hbase : π₂ v + π₂ (-f - v) = 1 := by
        simpa using pure_integer_minimal_valid_function_symmetry hπ₂_min (fun _ : Fin 1 ↦ v)
      have hrewrite : -f - v = u - 2 := by
        dsimp [v, β]
        ring
      rw [hrewrite, hshift₂ u] at hbase
      exact hbase
    have hv_eq : π v = π₂ v := hlower₂ hv_mem
    linarith
  constructor
  · intro u hu
    by_cases hu_lower : u ≤ m
    · exact hlower₁ ⟨hu.1, hu_lower⟩
    · exact hupper₁ ⟨le_of_lt (lt_of_not_ge hu_lower), hu.2⟩
  · intro u hu
    by_cases hu_lower : u ≤ m
    · exact hlower₂ ⟨hu.1, hu_lower⟩
    · exact hupper₂ ⟨le_of_lt (lt_of_not_ge hu_lower), hu.2⟩

/-- Helper for Example 6.24: subadditivity and symmetry force an affine formula below the
boundary midpoint to have limiting value at least `1 / 2`. -/
theorem affineBoundaryLimit_ge_half
    {g : ℝ → ℝ} {c d : ℝ}
    (hg_min : pure_integer_minimal_valid_function_on_R ((2 : ℝ) / 3) g)
    (hg_periodic : Function.Periodic g 1)
    (hg_left :
      Set.EqOn (example_6_24_pi ((2 : ℝ) / 3)) g
        (Set.Icc (0 : ℝ) ((1 : ℝ) / 3)))
    (hg_below :
      Set.EqOn g (fun u ↦ c * u + d)
        (Set.Ico ((4 : ℝ) / 9) ((2 : ℝ) / 3))) :
    (1 : ℝ) / 2 ≤ c * ((2 : ℝ) / 3) + d := by
  have hg_subadditive : g.Subadditive := by
    intro u v
    simpa using
      pure_integer_minimal_valid_function_subadditive hg_min
        (fun _ : Fin 1 ↦ u) (fun _ : Fin 1 ↦ v)
  refine le_of_forall_pos_le_add (fun ε hε ↦ ?_)
  let D : ℝ := |3 - c| + 1
  let t : ℝ := min ((1 : ℝ) / 6) (ε / D)
  have hD_pos : 0 < D := by
    dsimp [D]
    linarith [abs_nonneg (3 - c)]
  have ht_pos : 0 < t := by
    apply lt_min
    · norm_num
    · exact div_pos hε hD_pos
  have ht_le_sixth : t ≤ (1 : ℝ) / 6 := min_le_left _ _
  have ht_le_quot : t ≤ ε / D := min_le_right _ _
  have ht_nonneg : 0 ≤ t := le_of_lt ht_pos
  let lower : ℝ := (2 : ℝ) / 3 - t / 2
  have hlower_mem : lower ∈ Set.Ico ((4 : ℝ) / 9) ((2 : ℝ) / 3) := by
    constructor
    · dsimp [lower]
      linarith
    · dsimp [lower]
      linarith
  have ht_left : t ∈ Set.Icc (0 : ℝ) ((1 : ℝ) / 3) := by
    exact ⟨ht_nonneg, by linarith⟩
  have hgt : g t = 3 * t := by
    have hπt_raw :
        example_6_24_pi ((2 : ℝ) / 3) t = t / (1 - (2 : ℝ) / 3) := by
      exact example_6_24_pi_leftBranch ht_nonneg (by linarith [ht_le_sixth])
        (by norm_num; exact ht_left.2)
    calc
      g t = example_6_24_pi ((2 : ℝ) / 3) t := (hg_left ht_left).symm
      _ = t / (1 - (2 : ℝ) / 3) := hπt_raw
      _ = 3 * t := by ring
  have hlower_formula := hg_below hlower_mem
  have hshift : g (-((2 : ℝ) / 3) - lower) = g (lower + t) := by
    calc
      g (-((2 : ℝ) / 3) - lower) =
          g (((2 : ℤ) : ℝ) * 1 + (-((2 : ℝ) / 3) - lower)) := by
            simpa [one_mul, add_assoc, add_left_comm, add_comm] using
              (hg_periodic.int_mul (2 : ℤ) (-((2 : ℝ) / 3) - lower)).symm
      _ = g (lower + t) := by
        congr 1
        dsimp [lower]
        ring
  have hsym : g lower + g (lower + t) = 1 := by
    have hbase : g lower + g (-((2 : ℝ) / 3) - lower) = 1 := by
      simpa using pure_integer_minimal_valid_function_symmetry hg_min (fun _ : Fin 1 ↦ lower)
    rwa [hshift] at hbase
  have hsub : g (lower + t) ≤ g lower + g t := hg_subadditive lower t
  have hmain_ineq : 1 ≤ 2 * (c * ((2 : ℝ) / 3) + d) + (3 - c) * t := by
    have hadd_ineq : g lower + g (lower + t) ≤ g lower + (g lower + g t) := by
      linarith [hsub]
    calc
      1 = g lower + g (lower + t) := hsym.symm
      _ ≤ g lower + (g lower + g t) := hadd_ineq
      _ = 2 * (c * ((2 : ℝ) / 3) + d) + (3 - c) * t := by
        rw [hlower_formula, hgt]
        dsimp [lower]
        ring
  have hD_upper : |3 - c| ≤ D := by
    dsimp [D]
    linarith
  have hquot_nonneg : 0 ≤ ε / D := div_nonneg hε.le hD_pos.le
  have hmul_bound : |3 - c| * t ≤ ε := by
    calc
      |3 - c| * t ≤ D * (ε / D) :=
        mul_le_mul hD_upper ht_le_quot ht_nonneg hD_pos.le
      _ = ε := by field_simp [ne_of_gt hD_pos]
  have herror_bound : (3 - c) * t ≤ 2 * ε := by
    calc
      (3 - c) * t ≤ |3 - c| * t :=
        mul_le_mul_of_nonneg_right (le_abs_self (3 - c)) ht_nonneg
      _ ≤ ε := hmul_bound
      _ ≤ 2 * ε := by linarith
  norm_num at hmain_ineq herror_bound ⊢
  linarith

/-- Helper for Example 6.24: symmetry reflects equality on the lower boundary half-core to the
upper half-core. -/
theorem eqOn_boundaryUpperCore_of_eqOn_lowerCore
    {g : ℝ → ℝ}
    (hg_min : pure_integer_minimal_valid_function_on_R ((2 : ℝ) / 3) g)
    (hg_periodic : Function.Periodic g 1)
    (hlower :
      Set.EqOn (example_6_24_pi ((2 : ℝ) / 3)) g
        (Set.Icc ((4 : ℝ) / 9) ((2 : ℝ) / 3))) :
    Set.EqOn (example_6_24_pi ((2 : ℝ) / 3)) g
      (Set.Icc ((2 : ℝ) / 3) ((8 : ℝ) / 9)) := by
  have hshift (u : ℝ) : g (u - 2) = g u := by
    have hper := hg_periodic.int_mul (-2) u
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hper
  intro u hu
  let v : ℝ := (4 : ℝ) / 3 - u
  have hv_mem : v ∈ Set.Icc ((4 : ℝ) / 9) ((2 : ℝ) / 3) := by
    constructor
    · dsimp [v]
      norm_num at hu ⊢
      linarith [hu.2]
    · dsimp [v]
      norm_num at hu ⊢
      linarith [hu.1]
  have hπ_sym :
      example_6_24_pi ((2 : ℝ) / 3) v + example_6_24_pi ((2 : ℝ) / 3) u = 1 := by
    have hbase := example_6_24_pi_symmetryReal (f := (2 : ℝ) / 3) (by norm_num) (by norm_num) v
    have hrewrite : -((2 : ℝ) / 3) - v = u - 2 := by
      dsimp [v]
      ring
    rw [hrewrite] at hbase
    have hsource_shift :
        example_6_24_pi ((2 : ℝ) / 3) (u - 2) =
          example_6_24_pi ((2 : ℝ) / 3) u := by
      have hper := (example_6_24_pi_periodic ((2 : ℝ) / 3)).int_mul (-2) u
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hper
    rw [hsource_shift] at hbase
    exact hbase
  have hg_sym : g v + g u = 1 := by
    have hbase : g v + g (-((2 : ℝ) / 3) - v) = 1 := by
      simpa using pure_integer_minimal_valid_function_symmetry hg_min (fun _ : Fin 1 ↦ v)
    have hrewrite : -((2 : ℝ) / 3) - v = u - 2 := by
      dsimp [v]
      ring
    rwa [hrewrite, hshift u] at hbase
  have hv_eq := hlower hv_mem
  linarith

/-- Helper for Example 6.24: at the boundary `1 - f = 1 / 3`, bounded additivity rectangles
approaching the midpoint and subadditivity at the midpoint force the right-branch slope. -/
theorem example_6_24_midpointComponents_eqOn_coreWindow_of_eq_third
    {f : ℝ} (h₀ : 0 < 1 - f) (h₁ : 1 - f < (1 : ℝ) / 2)
    (hthird : 1 - f = (1 : ℝ) / 3)
    {π₁ π₂ : ℝ → ℝ}
    (hπ₁ : pure_integer_valid_function_on_R f π₁)
    (hπ₂ : pure_integer_valid_function_on_R f π₂)
    (hmid : example_6_24_pi f = (1 / 2 : ℝ) • π₁ + (1 / 2 : ℝ) • π₂) :
    Set.EqOn (example_6_24_pi f) π₁ (Set.Icc ((2 - f) / 3) (2 * ((2 - f) / 3))) ∧
      Set.EqOn (example_6_24_pi f) π₂ (Set.Icc ((2 - f) / 3) (2 * ((2 - f) / 3))) := by
  have hf : f = (2 : ℝ) / 3 := by
    linarith
  subst f
  let π : ℝ → ℝ := example_6_24_pi ((2 : ℝ) / 3)
  let x : ℝ := (4 : ℝ) / 9
  let q₀ : ℝ := (5 : ℝ) / 9
  let m : ℝ := (2 : ℝ) / 3
  let y : ℝ := (8 : ℝ) / 9
  have hxq₀ : x < q₀ := by
    norm_num [x, q₀]
  have hq₀m : q₀ < m := by
    norm_num [q₀, m]
  have hx_pos : 0 < x := by
    norm_num [x]
  have hx_break : (1 : ℝ) / 3 < x := by
    norm_num [x]
  have hm_lt_one : m < 1 := by
    norm_num [m]
  have hπ : pure_integer_minimal_valid_function_on_R ((2 : ℝ) / 3) π := by
    simpa [π] using example_6_24_pi_minimal h₀ h₁
  rcases midpointComponentsAreMinimalValidFunctionOnR hπ hπ₁ hπ₂ (by simpa [π] using hmid) with
    ⟨hπ₁_min, hπ₂_min⟩
  rcases pureIntegerMinimalValidFunctionOnR_periodicEndpoints hπ₁_min with
    ⟨hπ₁_periodic, _, _, _, hπ₁_bdd⟩
  rcases pureIntegerMinimalValidFunctionOnR_periodicEndpoints hπ₂_min with
    ⟨hπ₂_periodic, _, _, _, hπ₂_bdd⟩
  rcases example_6_24_midpointComponents_eqOn_leftBranch h₀ h₁ hπ₁ hπ₂ hmid with
    ⟨hleft₁_raw, hleft₂_raw⟩
  have hleft₁ : Set.EqOn π π₁ (Set.Icc (0 : ℝ) ((1 : ℝ) / 3)) := by
    norm_num at hleft₁_raw
    simpa [π] using hleft₁_raw
  have hleft₂ : Set.EqOn π π₂ (Set.Icc (0 : ℝ) ((1 : ℝ) / 3)) := by
    norm_num at hleft₂_raw
    simpa [π] using hleft₂_raw
  rcases example_6_24_midpointComponents_rightSpecialValues h₀ h₁ hπ₁ hπ₂ hmid with
    ⟨hx₁_raw, hx₂_raw, _, _, hm₁_raw, hm₂_raw⟩
  have hx₁ : π₁ x = π x := by
    norm_num [x, π] at hx₁_raw ⊢
    exact hx₁_raw
  have hx₂ : π₂ x = π x := by
    norm_num [x, π] at hx₂_raw ⊢
    exact hx₂_raw
  have hm₁ : π₁ m = π m := by
    norm_num [m, π] at hm₁_raw ⊢
    exact hm₁_raw
  have hm₂ : π₂ m = π m := by
    norm_num [m, π] at hm₂_raw ⊢
    exact hm₂_raw
  have hmidπ : π = (1 / 2 : ℝ) • π₁ + (1 / 2 : ℝ) • π₂ := by
    simpa [π] using hmid
  let hadd_transfer := scalarMidpointAdditivityTransfer hπ hπ₁ hπ₂ hmidπ
  have hlocalAffine
      (g : ℝ → ℝ) (hg_bdd : BoundedOnBoundedIntervals g)
      (hg_transfer :
        ∀ ⦃u v : ℝ⦄, π u + π v = π (u + v) → g u + g v = g (u + v)) :
      ∀ q : ℝ, q₀ < q → q < m →
        ∃ c d : ℝ, Set.EqOn g (fun u ↦ c * u + d) (Set.Icc x q) := by
    intro q hq₀q hqm
    let a : ℝ := (((1 : ℝ) / 3) + (1 - q)) / 2
    let b : ℝ := (a + (1 - q)) / 2
    have hgap : (1 : ℝ) / 3 < 1 - q := by
      dsimp [m] at hqm
      linarith
    have hbreak_a : (1 : ℝ) / 3 < a := by
      dsimp [a]
      linarith
    have hab : a < b := by
      dsimp [b, a]
      linarith
    have hb_gap : b < 1 - q := by
      dsimp [b, a]
      linarith
    have hq_pos : 0 < q := by
      linarith [hq₀q, hxq₀, hx_pos]
    have hxq : x < q := hxq₀.trans hq₀q
    have hπ_add :
        ∀ ⦃u v : ℝ⦄, u ∈ Set.Icc a b → v ∈ Set.Icc x q →
          π u + π v = π (u + v) := by
      intro u v hu hv
      have hu_nonneg : 0 ≤ u := by
        linarith [hbreak_a, hu.1]
      have hv_nonneg : 0 ≤ v := by
        linarith [hx_pos, hv.1]
      have hu_lt_one : u < 1 := by
        linarith [hu.2, hb_gap, hq_pos]
      have hv_lt_one : v < 1 := by
        linarith [hv.2, hqm, hm_lt_one]
      have hu_break : (1 : ℝ) / 3 < u := lt_of_lt_of_le hbreak_a hu.1
      have hv_break : (1 : ℝ) / 3 < v := lt_of_lt_of_le hx_break hv.1
      have huv_nonneg : 0 ≤ u + v := add_nonneg hu_nonneg hv_nonneg
      have huv_lt_one : u + v < 1 := by
        linarith [hu.2, hv.2, hb_gap]
      have huv_break : (1 : ℝ) / 3 < u + v := by
        linarith [hu_break, hv_nonneg]
      have hu_formula : π u = u / (2 - (2 : ℝ) / 3) := by
        simpa [π] using
          example_6_24_pi_rightBranch hu_nonneg hu_lt_one (by norm_num; exact hu_break)
      have hv_formula : π v = v / (2 - (2 : ℝ) / 3) := by
        simpa [π] using
          example_6_24_pi_rightBranch hv_nonneg hv_lt_one (by norm_num; exact hv_break)
      have huv_formula : π (u + v) = (u + v) / (2 - (2 : ℝ) / 3) := by
        simpa [π] using
          example_6_24_pi_rightBranch huv_nonneg huv_lt_one (by norm_num; exact huv_break)
      rw [hu_formula, hv_formula, huv_formula]
      ring
    rcases interval_lemma_affine_with_common_slope hg_bdd hab hxq
        (by
          intro u v hu hv
          exact hg_transfer (hπ_add hu hv)) with
      ⟨c, _gA, gB, _gAB, _hgA, _hgAeq, hgB, hgBeq, _hgAB, _hgABeq⟩
    have howner :
        ∃ gAffine : ℝ →ᵃ[ℝ] ℝ,
          gAffine.linear = (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight c ∧
            Set.EqOn g gAffine (Set.Icc x q) :=
      ⟨gB, hgB, hgBeq⟩
    rcases (exists_affineMap_eqOn_iff (f := g) (s := Set.Icc x q) (c := c)).1 howner with
      ⟨d, hd⟩
    exact ⟨c, d, hd⟩
  have hlocal₁ :
      ∀ q : ℝ, q₀ < q → q < m →
        ∃ c d : ℝ, Set.EqOn π₁ (fun u ↦ c * u + d) (Set.Icc x q) := by
    intro q hq₀q hqm
    exact hlocalAffine π₁ hπ₁_bdd (fun _ _ hadd ↦ (hadd_transfer hadd).1) q hq₀q hqm
  have hlocal₂ :
      ∀ q : ℝ, q₀ < q → q < m →
        ∃ c d : ℝ, Set.EqOn π₂ (fun u ↦ c * u + d) (Set.Icc x q) := by
    intro q hq₀q hqm
    exact hlocalAffine π₂ hπ₂_bdd (fun _ _ hadd ↦ (hadd_transfer hadd).2) q hq₀q hqm
  rcases existsAffineFormulaOnIco_of_nestedAffineFormulas hxq₀ hq₀m hlocal₁ with
    ⟨c₁, d₁, hbelow₁⟩
  rcases existsAffineFormulaOnIco_of_nestedAffineFormulas hxq₀ hq₀m hlocal₂ with
    ⟨c₂, d₂, hbelow₂⟩
  have hπx : π x = (1 : ℝ) / 3 := by
    have hraw : π x = x / (2 - (2 : ℝ) / 3) := by
      simpa [π] using
        example_6_24_pi_rightBranch (le_of_lt hx_pos) (by norm_num [x]) (by norm_num [x])
    rw [hraw]
    norm_num [x]
  have hπq₀ : π q₀ = (5 : ℝ) / 12 := by
    have hraw : π q₀ = q₀ / (2 - (2 : ℝ) / 3) := by
      simpa [π] using
        example_6_24_pi_rightBranch (by norm_num [q₀]) (by norm_num [q₀]) (by norm_num [q₀])
    rw [hraw]
    norm_num [q₀]
  have hsum_q₀ : π₁ q₀ + π₂ q₀ = (5 : ℝ) / 6 := by
    have hpoint := congrFun hmidπ q₀
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hpoint
    linarith [hπq₀]
  have hx_mem : x ∈ Set.Ico x m := ⟨le_rfl, hxq₀.trans hq₀m⟩
  have hq₀_mem : q₀ ∈ Set.Ico x m := ⟨hxq₀.le, hq₀m⟩
  have hx_formula₁ := hbelow₁ hx_mem
  have hx_formula₂ := hbelow₂ hx_mem
  have hq₀_formula₁ := hbelow₁ hq₀_mem
  have hq₀_formula₂ := hbelow₂ hq₀_mem
  have hlimit_sum : (c₁ * m + d₁) + (c₂ * m + d₂) = 1 := by
    have hx_value₁ : π₁ x = (1 : ℝ) / 3 := by linarith [hx₁, hπx]
    have hx_value₂ : π₂ x = (1 : ℝ) / 3 := by linarith [hx₂, hπx]
    dsimp [x, q₀, m] at hx_formula₁ hx_formula₂ hq₀_formula₁ hq₀_formula₂ ⊢
    linarith
  have hlimit₁ : (1 : ℝ) / 2 ≤ c₁ * m + d₁ := by
    simpa [π, x, m] using
      affineBoundaryLimit_ge_half hπ₁_min hπ₁_periodic hleft₁ hbelow₁
  have hlimit₂ : (1 : ℝ) / 2 ≤ c₂ * m + d₂ := by
    simpa [π, x, m] using
      affineBoundaryLimit_ge_half hπ₂_min hπ₂_periodic hleft₂ hbelow₂
  have hlimit₁_eq : c₁ * m + d₁ = (1 : ℝ) / 2 := by
    norm_num at hlimit_sum hlimit₁ hlimit₂ ⊢
    linarith [hlimit_sum, hlimit₂]
  have hlimit₂_eq : c₂ * m + d₂ = (1 : ℝ) / 2 := by
    norm_num at hlimit_sum hlimit₁ hlimit₂ hlimit₁_eq ⊢
    linarith [hlimit_sum, hlimit₁]
  have hc₁ : c₁ = (3 : ℝ) / 4 := by
    have hx_value : π₁ x = (1 : ℝ) / 3 := by linarith [hx₁, hπx]
    dsimp [x, m] at hx_formula₁ hlimit₁_eq ⊢
    linarith
  have hc₂ : c₂ = (3 : ℝ) / 4 := by
    have hx_value : π₂ x = (1 : ℝ) / 3 := by linarith [hx₂, hπx]
    dsimp [x, m] at hx_formula₂ hlimit₂_eq ⊢
    linarith
  have hd₁ : d₁ = 0 := by
    have hx_value : π₁ x = (1 : ℝ) / 3 := by linarith [hx₁, hπx]
    dsimp [x] at hx_formula₁
    linarith
  have hd₂ : d₂ = 0 := by
    have hx_value : π₂ x = (1 : ℝ) / 3 := by linarith [hx₂, hπx]
    dsimp [x] at hx_formula₂
    linarith
  have hlower₁ : Set.EqOn π π₁ (Set.Icc x m) := by
    intro u hu
    by_cases hum : u = m
    · subst u
      exact hm₁.symm
    · have hu_lt_m : u < m := lt_of_le_of_ne hu.2 hum
      have hu_nonneg : 0 ≤ u := le_trans (le_of_lt hx_pos) hu.1
      have hu_break : (1 : ℝ) / 3 < u := lt_of_lt_of_le hx_break hu.1
      have hπu : π u = (3 : ℝ) / 4 * u := by
        have hraw : π u = u / (2 - (2 : ℝ) / 3) := by
          simpa [π] using
            example_6_24_pi_rightBranch hu_nonneg (lt_trans hu_lt_m hm_lt_one)
              (by norm_num; exact hu_break)
        rw [hraw]
        ring
      calc
        π u = (3 : ℝ) / 4 * u := hπu
        _ = c₁ * u + d₁ := by rw [hc₁, hd₁]; ring
        _ = π₁ u := (hbelow₁ ⟨hu.1, hu_lt_m⟩).symm
  have hlower₂ : Set.EqOn π π₂ (Set.Icc x m) := by
    intro u hu
    by_cases hum : u = m
    · subst u
      exact hm₂.symm
    · have hu_lt_m : u < m := lt_of_le_of_ne hu.2 hum
      have hu_nonneg : 0 ≤ u := le_trans (le_of_lt hx_pos) hu.1
      have hu_break : (1 : ℝ) / 3 < u := lt_of_lt_of_le hx_break hu.1
      have hπu : π u = (3 : ℝ) / 4 * u := by
        have hraw : π u = u / (2 - (2 : ℝ) / 3) := by
          simpa [π] using
            example_6_24_pi_rightBranch hu_nonneg (lt_trans hu_lt_m hm_lt_one)
              (by norm_num; exact hu_break)
        rw [hraw]
        ring
      calc
        π u = (3 : ℝ) / 4 * u := hπu
        _ = c₂ * u + d₂ := by rw [hc₂, hd₂]; ring
        _ = π₂ u := (hbelow₂ ⟨hu.1, hu_lt_m⟩).symm
  have hupper₁ : Set.EqOn π π₁ (Set.Icc m y) := by
    simpa [π, x, m, y] using
      eqOn_boundaryUpperCore_of_eqOn_lowerCore hπ₁_min hπ₁_periodic hlower₁
  have hupper₂ : Set.EqOn π π₂ (Set.Icc m y) := by
    simpa [π, x, m, y] using
      eqOn_boundaryUpperCore_of_eqOn_lowerCore hπ₂_min hπ₂_periodic hlower₂
  constructor
  · intro u hu
    have hu_core : u ∈ Set.Icc x y := by
      norm_num [x, y] at hu ⊢
      exact hu
    by_cases hum : u ≤ m
    · exact hlower₁ ⟨hu_core.1, hum⟩
    · exact hupper₁ ⟨le_of_lt (lt_of_not_ge hum), hu_core.2⟩
  · intro u hu
    have hu_core : u ∈ Set.Icc x y := by
      norm_num [x, y] at hu ⊢
      exact hu
    by_cases hum : u ≤ m
    · exact hlower₂ ⟨hu_core.1, hum⟩
    · exact hupper₂ ⟨le_of_lt (lt_of_not_ge hum), hu_core.2⟩

/-- Helper for Example 6.24: the remaining missing step is right-branch rigidity for midpoint
components on `Set.Icc (1 - f) 1`. -/
theorem example_6_24_midpointComponents_eqOn_rightBranch_of_eqOn_core
    {f : ℝ} (h₀ : 0 < 1 - f) (h₁ : 1 - f < (1 : ℝ) / 2)
    {π₁ π₂ : ℝ → ℝ}
    (hπ₁ : pure_integer_valid_function_on_R f π₁)
    (hπ₂ : pure_integer_valid_function_on_R f π₂)
    (hmid : example_6_24_pi f = (1 / 2 : ℝ) • π₁ + (1 / 2 : ℝ) • π₂)
    (hcore :
      Set.EqOn (example_6_24_pi f) π₁ (Set.Icc ((2 - f) / 3) (2 * ((2 - f) / 3))) ∧
        Set.EqOn (example_6_24_pi f) π₂ (Set.Icc ((2 - f) / 3) (2 * ((2 - f) / 3)))) :
    Set.EqOn (example_6_24_pi f) π₁ (Set.Icc (1 - f) 1) ∧
      Set.EqOn (example_6_24_pi f) π₂ (Set.Icc (1 - f) 1) := by
  let α : ℝ := 1 - f
  let β : ℝ := 2 - f
  let x : ℝ := β / 3
  let y : ℝ := 2 * x
  let π : ℝ → ℝ := example_6_24_pi f
  have hα_pos : 0 < α := h₀
  have hβ_pos : 0 < β := by
    dsimp [β, α]
    linarith
  have hβ_ne : β ≠ 0 := by
    linarith
  have hx_nonneg : 0 ≤ x := by
    dsimp [x, β]
    linarith
  have hx_lt_one : x < 1 := by
    dsimp [x, β, α] at *
    linarith
  have hx_break : α < x := by
    dsimp [x, β, α] at *
    linarith
  have hy_nonneg : 0 ≤ y := by
    dsimp [y]
    linarith [hx_nonneg]
  have hy_lt_one : y < 1 := by
    dsimp [y, x, β, α] at *
    linarith
  have hy_break : α < y := by
    dsimp [y, x, β, α] at *
    linarith
  have hπ : pure_integer_minimal_valid_function_on_R f π := example_6_24_pi_minimal h₀ h₁
  rcases midpointComponentsAreMinimalValidFunctionOnR hπ hπ₁ hπ₂ hmid with
    ⟨hπ₁_min, hπ₂_min⟩
  rcases pureIntegerMinimalValidFunctionOnR_periodicEndpoints hπ with
    ⟨_, _, hπ_one, _, _⟩
  rcases pureIntegerMinimalValidFunctionOnR_periodicEndpoints hπ₁_min with
    ⟨hπ₁_periodic, _, hπ₁_one, _, _⟩
  rcases pureIntegerMinimalValidFunctionOnR_periodicEndpoints hπ₂_min with
    ⟨hπ₂_periodic, _, hπ₂_one, _, _⟩
  rcases example_6_24_midpointComponents_eqOn_leftBranch h₀ h₁ hπ₁ hπ₂ hmid with
    ⟨hleft₁, hleft₂⟩
  rcases example_6_24_midpointComponents_rightSpecialValues h₀ h₁ hπ₁ hπ₂ hmid with
    ⟨hx₁, hx₂, hy₁, hy₂, _, _⟩
  rcases hcore with ⟨hcore₁, hcore₂⟩
  let hadd_transfer := scalarMidpointAdditivityTransfer hπ hπ₁ hπ₂ hmid
  have hleftOuter₁ :
      Set.EqOn π π₁ (Set.Icc α x) := by
    intro u hu
    by_cases hu_alpha : u = α
    · -- The discontinuous breakpoint is already controlled by the closed left-branch theorem.
      subst hu_alpha
      simpa [π, α] using hleft₁ (show α ∈ Set.Icc (0 : ℝ) (1 - f) by
        constructor
        · exact le_of_lt hα_pos
        · simpa [α])
    · -- Past the breakpoint, adding the first right-branch anchor `x = (2 - f) / 3` lands in the
      -- core window where equality is already known.
      have hu_gt : α < u := lt_of_le_of_ne hu.1 (Ne.symm hu_alpha)
      have hu_nonneg : 0 ≤ u := by
        linarith
      have hu_lt_one : u < 1 := lt_of_le_of_lt hu.2 hx_lt_one
      have hux_mem : u + x ∈ Set.Icc x y := by
        constructor
        · linarith [hx_nonneg]
        · have hux_le : u + x ≤ x + x := add_le_add hu.2 le_rfl
          simpa [y, two_mul] using hux_le
      have hux_lt_one : u + x < 1 := by
        have hux_le : u + x ≤ y := by
          have hux_le' : u + x ≤ x + x := add_le_add hu.2 le_rfl
          simpa [y, two_mul] using hux_le'
        linarith
      have hux_break : α < u + x := by
        linarith [hu_gt, hx_nonneg]
      have hπu : π u = u / β := by
        simpa [π, β] using example_6_24_pi_rightBranch hu_nonneg hu_lt_one (by simpa [α] using hu_gt)
      have hπx : π x = x / β := by
        simpa [π, β] using
          example_6_24_pi_rightBranch hx_nonneg hx_lt_one (by simpa [α] using hx_break)
      have hπux : π (u + x) = (u + x) / β := by
        simpa [π, β] using
          example_6_24_pi_rightBranch (add_nonneg hu_nonneg hx_nonneg) hux_lt_one
            (by simpa [α] using hux_break)
      have hπ_add : π u + π x = π (u + x) := by
        rw [hπu, hπx, hπux]
        field_simp [hβ_ne]
      have hπ₁_add : π₁ u + π₁ x = π₁ (u + x) := (hadd_transfer hπ_add).1
      have hcore_val : π (u + x) = π₁ (u + x) := by
        simpa [π, x, y] using hcore₁ hux_mem
      have hx_eq : π x = π₁ x := by
        simpa [π, x, β] using hx₁.symm
      calc
        π u = π (u + x) - π x := by linarith [hπ_add]
        _ = π₁ (u + x) - π x := by rw [hcore_val]
        _ = π₁ (u + x) - π₁ x := by rw [hx_eq]
        _ = π₁ u := by linarith [hπ₁_add]
  have hleftOuter₂ :
      Set.EqOn π π₂ (Set.Icc α x) := by
    intro u hu
    by_cases hu_alpha : u = α
    · -- The second midpoint component shares the same controlled breakpoint value.
      subst hu_alpha
      simpa [π, α] using hleft₂ (show α ∈ Set.Icc (0 : ℝ) (1 - f) by
        constructor
        · exact le_of_lt hα_pos
        · simpa [α])
    · -- The same anchor-additivity transport works verbatim for the second midpoint component.
      have hu_gt : α < u := lt_of_le_of_ne hu.1 (Ne.symm hu_alpha)
      have hu_nonneg : 0 ≤ u := by
        linarith
      have hu_lt_one : u < 1 := lt_of_le_of_lt hu.2 hx_lt_one
      have hux_mem : u + x ∈ Set.Icc x y := by
        constructor
        · linarith [hx_nonneg]
        · have hux_le : u + x ≤ x + x := add_le_add hu.2 le_rfl
          simpa [y, two_mul] using hux_le
      have hux_lt_one : u + x < 1 := by
        have hux_le : u + x ≤ y := by
          have hux_le' : u + x ≤ x + x := add_le_add hu.2 le_rfl
          simpa [y, two_mul] using hux_le'
        linarith
      have hux_break : α < u + x := by
        linarith [hu_gt, hx_nonneg]
      have hπu : π u = u / β := by
        simpa [π, β] using example_6_24_pi_rightBranch hu_nonneg hu_lt_one (by simpa [α] using hu_gt)
      have hπx : π x = x / β := by
        simpa [π, β] using
          example_6_24_pi_rightBranch hx_nonneg hx_lt_one (by simpa [α] using hx_break)
      have hπux : π (u + x) = (u + x) / β := by
        simpa [π, β] using
          example_6_24_pi_rightBranch (add_nonneg hu_nonneg hx_nonneg) hux_lt_one
            (by simpa [α] using hux_break)
      have hπ_add : π u + π x = π (u + x) := by
        rw [hπu, hπx, hπux]
        field_simp [hβ_ne]
      have hπ₂_add : π₂ u + π₂ x = π₂ (u + x) := (hadd_transfer hπ_add).2
      have hcore_val : π (u + x) = π₂ (u + x) := by
        simpa [π, x, y] using hcore₂ hux_mem
      have hx_eq : π x = π₂ x := by
        simpa [π, x, β] using hx₂.symm
      calc
        π u = π (u + x) - π x := by linarith [hπ_add]
        _ = π₂ (u + x) - π x := by rw [hcore_val]
        _ = π₂ (u + x) - π₂ x := by rw [hx_eq]
        _ = π₂ u := by linarith [hπ₂_add]
  have hshift_pi (u : ℝ) : π (u - 2) = π u := by
    -- Two applications of `1`-periodicity identify the shifted symmetry partner with `u`.
    have hper := (example_6_24_pi_periodic f).int_mul (-2) u
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hper
  have hshift_π₁ (u : ℝ) : π₁ (u - 2) = π₁ u := by
    -- The first midpoint component inherits the same integer-period shift.
    have hper := hπ₁_periodic.int_mul (-2) u
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hper
  have hshift_π₂ (u : ℝ) : π₂ (u - 2) = π₂ u := by
    -- The second midpoint component has the same period-shift identity.
    have hper := hπ₂_periodic.int_mul (-2) u
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hper
  have hrightOuter₁ :
      Set.EqOn π π₁ (Set.Icc y 1) := by
    intro u hu
    by_cases hu_one : u = 1
    · -- The endpoint `1` is already normalized by periodicity for both functions.
      subst hu_one
      calc
        π 1 = 0 := hπ_one
        _ = π₁ 1 := hπ₁_one.symm
    · -- Reflect the right outer window through `u ↦ 2 - f - u` and reuse the left outer window.
      let v : ℝ := β - u
      have hu_lt_one : u < 1 := lt_of_le_of_ne hu.2 hu_one
      have hv_mem : v ∈ Set.Icc α x := by
        constructor
        · dsimp [v, β, α] at *
          have hv_gt : α < v := by
            linarith
          exact le_of_lt hv_gt
        · have hupper : β - u ≤ x := by
            dsimp [y, x, β] at *
            linarith [hu.1]
          simpa [v] using hupper
      have hπ_sym : π v + π u = 1 := by
        have hbase := example_6_24_pi_symmetryReal h₀ h₁ v
        have hrewrite : -f - v = u - 2 := by
          dsimp [v, β]
          ring
        have hshift : example_6_24_pi f (u - 2) = π u := by
          simpa [π] using hshift_pi u
        rw [hrewrite, hshift] at hbase
        simpa [π, add_comm] using hbase
      have hπ₁_sym : π₁ v + π₁ u = 1 := by
        have hbase : π₁ v + π₁ (-f - v) = 1 := by
          simpa using pure_integer_minimal_valid_function_symmetry hπ₁_min (fun _ : Fin 1 ↦ v)
        have hrewrite : -f - v = u - 2 := by
          dsimp [v, β]
          ring
        rw [hrewrite, hshift_π₁ u] at hbase
        simpa [add_comm] using hbase
      have hv_eq : π v = π₁ v := hleftOuter₁ hv_mem
      linarith
  have hrightOuter₂ :
      Set.EqOn π π₂ (Set.Icc y 1) := by
    intro u hu
    by_cases hu_one : u = 1
    · -- The second midpoint component also agrees with the source at the periodic endpoint `1`.
      subst hu_one
      calc
        π 1 = 0 := hπ_one
        _ = π₂ 1 := hπ₂_one.symm
    · -- The reflected point again lands in the left outer window already controlled above.
      let v : ℝ := β - u
      have hu_lt_one : u < 1 := lt_of_le_of_ne hu.2 hu_one
      have hv_mem : v ∈ Set.Icc α x := by
        constructor
        · dsimp [v, β, α] at *
          have hv_gt : α < v := by
            linarith
          exact le_of_lt hv_gt
        · have hupper : β - u ≤ x := by
            dsimp [y, x, β] at *
            linarith [hu.1]
          simpa [v] using hupper
      have hπ_sym : π v + π u = 1 := by
        have hbase := example_6_24_pi_symmetryReal h₀ h₁ v
        have hrewrite : -f - v = u - 2 := by
          dsimp [v, β]
          ring
        have hshift : example_6_24_pi f (u - 2) = π u := by
          simpa [π] using hshift_pi u
        rw [hrewrite, hshift] at hbase
        simpa [π, add_comm] using hbase
      have hπ₂_sym : π₂ v + π₂ u = 1 := by
        have hbase : π₂ v + π₂ (-f - v) = 1 := by
          simpa using pure_integer_minimal_valid_function_symmetry hπ₂_min (fun _ : Fin 1 ↦ v)
        have hrewrite : -f - v = u - 2 := by
          dsimp [v, β]
          ring
        rw [hrewrite, hshift_π₂ u] at hbase
        simpa [add_comm] using hbase
      have hv_eq : π v = π₂ v := hleftOuter₂ hv_mem
      linarith
  constructor
  · intro u hu
    by_cases hleft_cut : u ≤ x
    · exact hleftOuter₁ ⟨hu.1, hleft_cut⟩
    · by_cases hcore_cut : u ≤ y
      · exact hcore₁ ⟨le_of_lt (lt_of_not_ge hleft_cut), hcore_cut⟩
      · exact hrightOuter₁ ⟨le_of_lt (lt_of_not_ge hcore_cut), hu.2⟩
  · intro u hu
    by_cases hleft_cut : u ≤ x
    · exact hleftOuter₂ ⟨hu.1, hleft_cut⟩
    · by_cases hcore_cut : u ≤ y
      · exact hcore₂ ⟨le_of_lt (lt_of_not_ge hleft_cut), hcore_cut⟩
      · exact hrightOuter₂ ⟨le_of_lt (lt_of_not_ge hcore_cut), hu.2⟩

/-- Helper for Example 6.24: the remaining missing step is right-branch rigidity for midpoint
components on `Set.Icc (1 - f) 1` in the source-supported regime `1 - f ≤ 1 / 3`. -/
theorem example_6_24_midpointComponents_eqOn_rightBranch
    {f : ℝ} (h₀ : 0 < 1 - f) (h₁ : 1 - f < (1 : ℝ) / 2)
    (h₂ : 1 - f ≤ (1 : ℝ) / 3)
    {π₁ π₂ : ℝ → ℝ}
    (hπ₁ : pure_integer_valid_function_on_R f π₁)
    (hπ₂ : pure_integer_valid_function_on_R f π₂)
    (hmid : example_6_24_pi f = (1 / 2 : ℝ) • π₁ + (1 / 2 : ℝ) • π₂) :
    Set.EqOn (example_6_24_pi f) π₁ (Set.Icc (1 - f) 1) ∧
      Set.EqOn (example_6_24_pi f) π₂ (Set.Icc (1 - f) 1) := by
  -- Route correction: reduce the discontinuous endpoints to a smaller continuous core window.
  -- One additivity step handles `(1 - f, (2 - f) / 3]`, and symmetry handles `[2 * ((2 - f) / 3), 1)`.
  have hcore :
      Set.EqOn (example_6_24_pi f) π₁ (Set.Icc ((2 - f) / 3) (2 * ((2 - f) / 3))) ∧
        Set.EqOn (example_6_24_pi f) π₂ (Set.Icc ((2 - f) / 3) (2 * ((2 - f) / 3))) := by
    by_cases hthird : 1 - f < (1 : ℝ) / 3
    · -- Strictly below the boundary, the existing auxiliary rectangle reaches the midpoint.
      exact
        example_6_24_midpointComponents_eqOn_coreWindow_of_lt_third
          h₀ h₁ hthird hπ₁ hπ₂ hmid
    · -- At equality, nested rectangles approach the midpoint and subadditivity fixes their slope.
      have hthird_eq : 1 - f = (1 : ℝ) / 3 := le_antisymm h₂ (le_of_not_gt hthird)
      exact
        example_6_24_midpointComponents_eqOn_coreWindow_of_eq_third
          h₀ h₁ hthird_eq hπ₁ hπ₂ hmid
  exact example_6_24_midpointComponents_eqOn_rightBranch_of_eqOn_core
    h₀ h₁ hπ₁ hπ₂ hmid hcore

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_3_1/ch6_sec6_3_1_example_6_24.lean

Example 6.24 (4). For `0 < 1 - f ≤ 1/3`, the discontinuous two-slope function from Fig. 6.9 is an
extreme valid function for the one-dimensional pure integer infinite relaxation. -/
theorem example_6_24_pi_extreme
    {f : ℝ} (h₀ : 0 < 1 - f) (h₁ : 1 - f < (1 : ℝ) / 2)
    (h₂ : 1 - f ≤ (1 : ℝ) / 3) :
    pure_integer_extreme_valid_function_on_R f (example_6_24_pi f) := by
  refine
    { nonneg := (example_6_24_pi_minimal h₀ h₁).nonneg
      one_le_sum := (example_6_24_pi_minimal h₀ h₁).one_le_sum
      eq_of_eq_midpoint := ?_ }
  intro π₁Vec π₂Vec hπ₁Vec hπ₂Vec hmidVec
  let π₁ : ℝ → ℝ := fun r ↦ π₁Vec (fun _ : Fin 1 ↦ r)
  let π₂ : ℝ → ℝ := fun r ↦ π₂Vec (fun _ : Fin 1 ↦ r)
  have hπ₁_vec_eq : π₁Vec = fun r : Fin 1 → ℝ ↦ π₁ (r 0) := by
    -- In dimension `1`, every vector input is determined by its `0`-th coordinate.
    ext r
    change π₁Vec r = π₁Vec (fun _ : Fin 1 ↦ r 0)
    have hr : r = fun _ : Fin 1 ↦ r 0 := by
      ext i
      fin_cases i
      rfl
    rw [hr]
  have hπ₂_vec_eq : π₂Vec = fun r : Fin 1 → ℝ ↦ π₂ (r 0) := by
    -- The same scalarization identity applies to the second midpoint component.
    ext r
    change π₂Vec r = π₂Vec (fun _ : Fin 1 ↦ r 0)
    have hr : r = fun _ : Fin 1 ↦ r 0 := by
      ext i
      fin_cases i
      rfl
    rw [hr]
  have hπ₁ : pure_integer_valid_function_on_R f π₁ := by
    -- Rewrite the canonical owner along the scalarization identity.
    change pure_integer_valid_function (fun _ : Fin 1 ↦ f) (fun r : Fin 1 → ℝ ↦ π₁ (r 0))
    simpa [hπ₁_vec_eq] using hπ₁Vec
  have hπ₂ : pure_integer_valid_function_on_R f π₂ := by
    -- Apply the same bridge to the right midpoint component.
    change pure_integer_valid_function (fun _ : Fin 1 ↦ f) (fun r : Fin 1 → ℝ ↦ π₂ (r 0))
    simpa [hπ₂_vec_eq] using hπ₂Vec
  have hmid : example_6_24_pi f = (1 / 2 : ℝ) • π₁ + (1 / 2 : ℝ) • π₂ := by
    -- Evaluate the midpoint identity on constant `Fin 1` vectors.
    ext r
    have hpoint := congrFun hmidVec (fun _ : Fin 1 ↦ r)
    simpa [π₁, π₂, Pi.add_apply, Pi.smul_apply] using hpoint
  -- Route correction: the discontinuous example still uses the standard scalar midpoint
  -- skeleton; only the unit-interval rigidity step is bespoke.
  have hunit :
      Set.EqOn (example_6_24_pi f) π₁ (Set.Icc (0 : ℝ) 1) ∧
        Set.EqOn (example_6_24_pi f) π₂ (Set.Icc (0 : ℝ) 1) := by
    have hright := example_6_24_midpointComponents_eqOn_rightBranch h₀ h₁ h₂ hπ₁ hπ₂ hmid
    exact example_6_24_midpointComponents_eqOn_unitInterval h₀ h₁ hπ₁ hπ₂ hmid hright
  have hπ : pure_integer_minimal_valid_function_on_R f (example_6_24_pi f) :=
    example_6_24_pi_minimal h₀ h₁
  rcases midpointComponentsAreMinimalValidFunctionOnR hπ hπ₁ hπ₂ hmid with
    ⟨hπ₁_min, hπ₂_min⟩
  rcases pureIntegerMinimalValidFunctionOnR_periodicEndpoints hπ with
    ⟨hπ_periodic, _, _, _, _⟩
  rcases pureIntegerMinimalValidFunctionOnR_periodicEndpoints hπ₁_min with
    ⟨hπ₁_periodic, _, _, _, _⟩
  rcases pureIntegerMinimalValidFunctionOnR_periodicEndpoints hπ₂_min with
    ⟨hπ₂_periodic, _, _, _, _⟩
  rcases hunit with ⟨hEq₁_unit, hEq₂_unit⟩
  have hEq₁ :
      example_6_24_pi f = π₁ := by
    exact eq_of_eqOn_unitInterval_of_onePeriodic hπ_periodic hπ₁_periodic hEq₁_unit
  have hEq₂ :
      example_6_24_pi f = π₂ := by
    exact eq_of_eqOn_unitInterval_of_onePeriodic hπ_periodic hπ₂_periodic hEq₂_unit
  constructor
  · ext r
    simpa [hπ₁_vec_eq] using congrFun hEq₁ (r 0)
  · ext r
    simpa [hπ₂_vec_eq] using congrFun hEq₂ (r 0)

/-- Under the source hypotheses of Example 6.24, `example_6_24_pi f` is available as an extreme
valid function instance. -/
instance instExample624Extreme
    {f : ℝ} [Fact (0 < 1 - f)] [Fact (1 - f < (1 : ℝ) / 2)]
    [Fact (1 - f ≤ (1 : ℝ) / 3)] :
    pure_integer_extreme_valid_function_on_R f (example_6_24_pi f) :=
  example_6_24_pi_extreme ‹Fact (0 < 1 - f)›.out ‹Fact (1 - f < (1 : ℝ) / 2)›.out
    ‹Fact (1 - f ≤ (1 : ℝ) / 3)›.out

end Example624
