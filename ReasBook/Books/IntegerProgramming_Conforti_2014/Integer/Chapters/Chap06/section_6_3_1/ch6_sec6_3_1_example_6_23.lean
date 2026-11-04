/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_1.ch6_sec6_3_1_one_periodic_extension

-- Semantic recall note: no deferred Lean semantic-search tool such as `lean_leansearch` was
-- available in this runner, so this file follows local repository precedent for explicit
-- piecewise definitions together with a companion periodicity statement.

section Example623

private noncomputable def example_6_23_pi1_on_unit_interval
    (t f : ℝ) : ℝ → ℝ :=
  fun u ↦
    if _ : u ≤ 1 - f then
      u / (1 - f)
    else if _ : u ≤ 1 - f + (t / 2) / (1 - f + t) then
      (1 - u + t - f) / t
    else if _ : u ≤ 1 - (t / 2) / (1 - f + t) then
      (u - 1 / 2) / (1 - f)
    else
      (1 - u) / t

/-- Example 6.23 (1). For parameters `0 < t < f < 1`, this is the function `π₁` defined by the
displayed piecewise formula on `[0, 1]` and extended to all real arguments by period `1`. -/
noncomputable def example_6_23_pi1
    (t f : ℝ) : ℝ → ℝ :=
  onePeriodicExtension (example_6_23_pi1_on_unit_interval t f)

/-- Unfolding formula for `example_6_23_pi1`: the source piecewise expression is evaluated at
`Int.fract r` to produce the `1`-periodic extension. -/
theorem example_6_23_pi1_apply (t f r : ℝ) :
    example_6_23_pi1 t f r =
      if Int.fract r ≤ 1 - f then
        Int.fract r / (1 - f)
      else if Int.fract r ≤ 1 - f + (t / 2) / (1 - f + t) then
        (1 - Int.fract r + t - f) / t
      else if Int.fract r ≤ 1 - (t / 2) / (1 - f + t) then
        (Int.fract r - 1 / 2) / (1 - f)
      else
        (1 - Int.fract r) / t :=
  rfl

/-- On the fundamental interval `[0, 1)`, `example_6_23_pi1` agrees with the displayed source
formula. -/
theorem example_6_23_pi1_eq_on_Ico (t f u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    example_6_23_pi1 t f u =
      if u ≤ 1 - f then
        u / (1 - f)
      else if u ≤ 1 - f + (t / 2) / (1 - f + t) then
        (1 - u + t - f) / t
      else if u ≤ 1 - (t / 2) / (1 - f + t) then
        (u - 1 / 2) / (1 - f)
      else
        (1 - u) / t := by
  simpa [example_6_23_pi1, example_6_23_pi1_on_unit_interval] using
    onePeriodicExtension_eq_on_Ico (φ := example_6_23_pi1_on_unit_interval t f) hu0 hu1

/-- The function `example_6_23_pi1` has period `1`, matching the source's extension by
periodicity. -/
theorem example_6_23_pi1_periodic
    (t f : ℝ) :
    Function.Periodic (example_6_23_pi1 t f) 1 :=
  onePeriodicExtension_periodic _

private noncomputable def example_6_23_pi2_on_unit_interval
    (t f : ℝ) : ℝ → ℝ :=
  fun u ↦
    if _ : u ≤ 1 - f then
      u / (1 - f)
    else if _ : u ≤ 1 - f + t / (2 - f + t) then
      (1 - u + t - f) / t
    else if _ : u ≤ 1 - t / (2 - f + t) then
      u / (2 - f)
    else
      (1 - u) / t

/-- Example 6.23 (2). For parameters `0 < t < f < 1`, this is the function `π₂` defined by the
displayed piecewise formula on `[0, 1]` and extended to all real arguments by period `1`. -/
noncomputable def example_6_23_pi2
    (t f : ℝ) : ℝ → ℝ :=
  onePeriodicExtension (example_6_23_pi2_on_unit_interval t f)

/-- Unfolding formula for `example_6_23_pi2`: the source piecewise expression is evaluated at
`Int.fract r` to produce the `1`-periodic extension. -/
theorem example_6_23_pi2_apply (t f r : ℝ) :
    example_6_23_pi2 t f r =
      if Int.fract r ≤ 1 - f then
        Int.fract r / (1 - f)
      else if Int.fract r ≤ 1 - f + t / (2 - f + t) then
        (1 - Int.fract r + t - f) / t
      else if Int.fract r ≤ 1 - t / (2 - f + t) then
        Int.fract r / (2 - f)
      else
        (1 - Int.fract r) / t :=
  rfl

/-- On the fundamental interval `[0, 1)`, `example_6_23_pi2` agrees with the displayed source
formula. -/
theorem example_6_23_pi2_eq_on_Ico (t f u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    example_6_23_pi2 t f u =
      if u ≤ 1 - f then
        u / (1 - f)
      else if u ≤ 1 - f + t / (2 - f + t) then
        (1 - u + t - f) / t
      else if u ≤ 1 - t / (2 - f + t) then
        u / (2 - f)
      else
        (1 - u) / t := by
  simpa [example_6_23_pi2, example_6_23_pi2_on_unit_interval] using
    onePeriodicExtension_eq_on_Ico (φ := example_6_23_pi2_on_unit_interval t f) hu0 hu1

/-- The function `example_6_23_pi2` has period `1`, matching the source's extension by
periodicity. -/
theorem example_6_23_pi2_periodic
    (t f : ℝ) :
    Function.Periodic (example_6_23_pi2 t f) 1 :=
  onePeriodicExtension_periodic _

end Example623
