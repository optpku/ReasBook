/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Definition_3_2
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Order.Filter.Extr

public section

noncomputable section

namespace LineSearch
namespace AlternatingDescent

/-- The objective function in Example 3.13 is `J(x) = x ^ 2`. -/
def objective : ℝ → ℝ :=
  fun x ↦ x ^ 2

/-- The prescribed descent direction sequence in Example 3.13 is
`p_v = (-1 : ℝ) ^ (v + 1)`. -/
def direction : ℕ → ℝ :=
  fun v ↦ (-1 : ℝ) ^ (v + 1)

/-- The prescribed step-length sequence in Example 3.13 is
`τ_v = 2 + 3 / (2 : ℝ) ^ (v + 1)`. -/
def stepSize : ℕ → ℝ :=
  fun v ↦ 2 + 3 / (2 : ℝ) ^ (v + 1)

/-- The iterates in Example 3.13 start at `x_0 = 2` and follow the update
`x_(v + 1) = x_v + τ_v * p_v`. -/
def iterate : ℕ → ℝ
  | 0 => 2
  | v + 1 => iterate v + stepSize v • direction v

/-- The prescribed step lengths in Example 3.13 are positive. -/
theorem stepSize_pos (v : ℕ) :
    0 < stepSize v := by
  -- Unfold the concrete step length and use positivity of the denominator.
  dsimp [stepSize]
  positivity

/-- The zeroth iterate in Example 3.13 is `x_0 = 2`. -/
theorem iterate_zero :
    iterate 0 = 2 := by
  -- The initial iterate is the defining base case of `iterate`.
  rfl

/-- The successor iterate in Example 3.13 is obtained from the prescribed step
length and descent direction. -/
theorem iterate_succ (v : ℕ) :
    iterate (v + 1) = iterate v + stepSize v • direction v := by
  -- The update rule is the defining recursive step of `iterate`.
  rfl

/-- Helper for Example 3.13: the iterates alternate in sign while their radius is
`1 + 1 / (2 : ℝ) ^ v`. -/
theorem iterate_eq_alternatingRadius (v : ℕ) :
    iterate v = (-1 : ℝ) ^ v * (1 + 1 / (2 : ℝ) ^ v) := by
  induction v with
  | zero =>
      -- The base iterate is exactly the claimed radius `2 = 1 + 1`.
      norm_num [iterate_zero]
  | succ v ih =>
      -- Expand one update step and normalize the resulting rational identity.
      rw [iterate_succ, ih]
      simp only [stepSize, direction, smul_eq_mul]
      rw [pow_succ]
      have hpow : (2 : ℝ) ^ v ≠ 0 := by
        positivity
      field_simp [pow_succ, hpow]
      ring

/-- The prescribed directions in Example 3.13 are descent directions for the
objective `J(x) = x ^ 2` along the concrete iterate sequence. -/
theorem direction_isDescentDirection (v : ℕ) :
    LineSearch.IsDescentDirection objective (iterate v) (direction v) := by
  rw [LineSearch.isDescentDirection_iff]
  refine ⟨1, by norm_num, ?_⟩
  intro τ hτpos hτlt
  let radius : ℝ := 1 + 1 / (2 : ℝ) ^ v
  have hradius_gt_one : 1 < radius := by
    -- The closed form shows each iterate has radius strictly larger than `1`.
    dsimp [radius]
    have hfrac_pos : 0 < 1 / (2 : ℝ) ^ v := by
      positivity
    nlinarith
  have hsub_pos : 0 < radius - τ := by
    nlinarith
  have hsq : (radius - τ) ^ 2 < radius ^ 2 := by
    -- Moving a positive distance `τ` inward strictly reduces the squared radius.
    nlinarith
  have hsign : (((-1 : ℝ) ^ v) ^ 2) = 1 := by
    rw [← pow_mul]
    simp
  have hnext :
      objective (iterate v + τ • direction v) = (radius - τ) ^ 2 := by
    -- Rewrite the updated iterate as the same sign times the reduced radius.
    rw [objective, iterate_eq_alternatingRadius, direction]
    simp only [smul_eq_mul, radius]
    calc
      (((-1 : ℝ) ^ v * (1 + 1 / (2 : ℝ) ^ v) + τ * (-1 : ℝ) ^ (v + 1)) ^ 2)
          = (((-1 : ℝ) ^ v * ((1 + 1 / (2 : ℝ) ^ v) - τ)) ^ 2) := by
              rw [pow_succ]
              ring
      _ = (((-1 : ℝ) ^ v) ^ 2) * (((1 + 1 / (2 : ℝ) ^ v) - τ) ^ 2) := by
            ring
      _ = (radius - τ) ^ 2 := by
            simp [hsign, radius]
  have hcurrent :
      objective (iterate v) = radius ^ 2 := by
    -- The alternating sign disappears after squaring the current iterate.
    rw [objective, iterate_eq_alternatingRadius]
    calc
      (((-1 : ℝ) ^ v * (1 + 1 / (2 : ℝ) ^ v)) ^ 2)
          = (((-1 : ℝ) ^ v) ^ 2) * ((1 + 1 / (2 : ℝ) ^ v) ^ 2) := by
              ring
      _ = radius ^ 2 := by
            simp [hsign, radius]
  calc
    objective (iterate v + τ • direction v) = (radius - τ) ^ 2 := hnext
    _ < radius ^ 2 := hsq
    _ = objective (iterate v) := hcurrent.symm

/-- The closed form asserted in Example 3.13 is
`x_v = (-1 : ℝ) ^ v * (1 + 1 / (2 : ℝ) ^ v)`. -/
theorem iterate_eq_closedForm (v : ℕ) :
    iterate v = (-1 : ℝ) ^ v * (1 + 1 / (2 : ℝ) ^ v) := by
  -- The book-facing closed form is exactly the alternating-radius helper.
  exact iterate_eq_alternatingRadius v

/-- The objective values in Example 3.13 strictly decrease along the iterate
sequence. -/
theorem objective_strictly_decreases (v : ℕ) :
    objective (iterate (v + 1)) < objective (iterate v) := by
  let radius : ℝ := 1 + 1 / (2 : ℝ) ^ v
  let nextRadius : ℝ := 1 + 1 / (2 : ℝ) ^ (v + 1)
  have hradius_pos : 0 < radius := by
    -- Both radii are positive because they are `1` plus a positive correction.
    dsimp [radius]
    positivity
  have hnextRadius_pos : 0 < nextRadius := by
    dsimp [nextRadius]
    positivity
  have hnext_lt : nextRadius < radius := by
    -- The correction term shrinks by a factor of `2` at each step.
    have hpow : (2 : ℝ) ^ v ≠ 0 := by
      positivity
    have hfrac : 1 / (2 : ℝ) ^ (v + 1) < 1 / (2 : ℝ) ^ v := by
      rw [pow_succ]
      field_simp [hpow]
      norm_num
    dsimp [radius, nextRadius]
    linarith
  have hsign_v : (((-1 : ℝ) ^ v) ^ 2) = 1 := by
    rw [← pow_mul]
    simp
  have hsign_succ : (((-1 : ℝ) ^ (v + 1)) ^ 2) = 1 := by
    rw [← pow_mul]
    simp
  have hcurrent :
      objective (iterate v) = radius ^ 2 := by
    -- Normalize the current objective value to the squared positive radius.
    rw [objective, iterate_eq_closedForm]
    calc
      (((-1 : ℝ) ^ v * (1 + 1 / (2 : ℝ) ^ v)) ^ 2)
          = (((-1 : ℝ) ^ v) ^ 2) * ((1 + 1 / (2 : ℝ) ^ v) ^ 2) := by
              ring
      _ = radius ^ 2 := by
            simp [hsign_v, radius]
  have hnext :
      objective (iterate (v + 1)) = nextRadius ^ 2 := by
    -- The same normalization removes the sign at the next iterate.
    rw [objective, iterate_eq_closedForm]
    calc
      (((-1 : ℝ) ^ (v + 1) * (1 + 1 / (2 : ℝ) ^ (v + 1))) ^ 2)
          = (((-1 : ℝ) ^ (v + 1)) ^ 2) * ((1 + 1 / (2 : ℝ) ^ (v + 1)) ^ 2) := by
              ring
      _ = nextRadius ^ 2 := by
            simp [hsign_succ, nextRadius]
  have hsq : nextRadius ^ 2 < radius ^ 2 := by
    -- Squaring preserves the strict inequality because both radii are positive.
    nlinarith
  calc
    objective (iterate (v + 1)) = nextRadius ^ 2 := hnext
    _ < radius ^ 2 := hsq
    _ = objective (iterate v) := hcurrent.symm

/-- Helper for Example 3.13: the absolute value of each iterate equals its
positive radius. -/
theorem abs_iterate_eq_radius (v : ℕ) :
    |iterate v| = 1 + 1 / (2 : ℝ) ^ v := by
  have hradius_nonneg : 0 ≤ 1 + 1 / (2 : ℝ) ^ v := by
    -- The radius is nonnegative, so the absolute value only removes the sign.
    have hfrac_nonneg : 0 ≤ 1 / (2 : ℝ) ^ v := by
      positivity
    nlinarith
  calc
    |iterate v| = |(-1 : ℝ) ^ v * (1 + 1 / (2 : ℝ) ^ v)| := by
      rw [iterate_eq_alternatingRadius]
    _ = |(-1 : ℝ) ^ v| * |1 + 1 / (2 : ℝ) ^ v| := by
          rw [abs_mul]
    _ = 1 * (1 + 1 / (2 : ℝ) ^ v) := by
          rw [abs_of_nonneg hradius_nonneg]
          simp
    _ = 1 + 1 / (2 : ℝ) ^ v := by ring

/-- Example 3.13. The iterate sequence does not converge to `0`. -/
theorem not_tendsto_zero :
    ¬ Filter.Tendsto iterate Filter.atTop (nhds (0 : ℝ)) := by
  intro hT
  have hball :
      Metric.ball (0 : ℝ) (1 / 2) ∈ nhds (0 : ℝ) := by
    -- A genuine neighborhood of `0` must eventually contain the iterates.
    exact Metric.ball_mem_nhds 0 (by norm_num)
  have hEvent :
      {n : ℕ | iterate n ∈ Metric.ball (0 : ℝ) (1 / 2)} ∈ Filter.atTop := by
    simpa using hT hball
  rcases Filter.mem_atTop_sets.mp hEvent with ⟨N, hN⟩
  have houtside : iterate N ∉ Metric.ball (0 : ℝ) (1 / 2) := by
    -- Every iterate has absolute value strictly larger than `1`, hence is outside
    -- the ball of radius `1 / 2` around `0`.
    rw [mem_ball_zero_iff, Real.norm_eq_abs, abs_iterate_eq_radius]
    have hfrac_pos : 0 < 1 / (2 : ℝ) ^ N := by
      positivity
    have hbound : (1 / 2 : ℝ) < 1 + 1 / (2 : ℝ) ^ N := by
      nlinarith
    exact not_lt.mpr hbound.le
  exact houtside (hN N le_rfl)

end AlternatingDescent
end LineSearch
