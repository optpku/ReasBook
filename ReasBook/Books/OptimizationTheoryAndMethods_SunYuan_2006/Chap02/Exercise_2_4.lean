/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib
import Mathlib.Order.Filter.Extr

/-- The objective function `t ↦ 1 - t * exp (-(t ^ 2))`
from the quadratic interpolation exercise. -/
noncomputable def quadraticInterpolationExerciseObjective (t : ℝ) : ℝ :=
  1 - t * Real.exp (-(t ^ 2))

-- Semantic recall: `IsMinOn` is the canonical API for minima on `Set.Icc`.
/-- Chapter02 Exercise 2.4. The function `quadraticInterpolationExerciseObjective` attains its
minimum on `Set.Icc (0 : ℝ) 1` at `Real.sqrt 2 / 2`. -/
theorem quadraticInterpolationExerciseObjective_isMinOn_unitInterval :
    IsMinOn quadraticInterpolationExerciseObjective (Set.Icc (0 : ℝ) 1) (Real.sqrt 2 / 2) := by
  rw [isMinOn_iff]
  intro t ht
  have hsqrt2_sq : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by
    nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2)]
  have h_xstar_sq : ((Real.sqrt 2 / 2 : ℝ) ^ 2) = 1 / 2 := by
    nlinarith [hsqrt2_sq]
  have h_quad : Real.sqrt 2 * t ≤ t ^ 2 + 1 / 2 := by
    nlinarith [sq_nonneg (t - Real.sqrt 2 / 2), hsqrt2_sq]
  have h_exp : t ^ 2 + 1 / 2 ≤ Real.exp (t ^ 2 - 1 / 2) := by
    have h_add : t ^ 2 - 1 / 2 + 1 ≤ Real.exp (t ^ 2 - 1 / 2) :=
      Real.add_one_le_exp (t ^ 2 - 1 / 2)
    nlinarith
  have h_bound : Real.sqrt 2 * t ≤ Real.exp (t ^ 2 - 1 / 2) :=
    le_trans h_quad h_exp
  have h_mul :
      Real.sqrt 2 * (t * Real.exp (-(t ^ 2))) ≤ Real.exp (-(1 / 2 : ℝ)) := by
    have h_mul' :=
      mul_le_mul_of_nonneg_right h_bound (le_of_lt (Real.exp_pos (-(t ^ 2))))
    calc
      Real.sqrt 2 * (t * Real.exp (-(t ^ 2)))
          = (Real.sqrt 2 * t) * Real.exp (-(t ^ 2)) := by ring
      _ ≤ Real.exp (t ^ 2 - 1 / 2) * Real.exp (-(t ^ 2)) := h_mul'
      _ = Real.exp (-(1 / 2 : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hsqrt2_pos : 0 < Real.sqrt 2 := by
    positivity
  have h_factor :
      Real.sqrt 2 * ((Real.sqrt 2 / 2) * Real.exp (-(1 / 2 : ℝ))) =
        Real.exp (-(1 / 2 : ℝ)) := by
    calc
      Real.sqrt 2 * ((Real.sqrt 2 / 2) * Real.exp (-(1 / 2 : ℝ))) =
          ((Real.sqrt 2 : ℝ) ^ 2 / 2) * Real.exp (-(1 / 2 : ℝ)) := by ring
      _ = Real.exp (-(1 / 2 : ℝ)) := by rw [hsqrt2_sq]; ring
  have h_peak :
      t * Real.exp (-(t ^ 2)) ≤
        (Real.sqrt 2 / 2) * Real.exp (-(1 / 2 : ℝ)) := by
    have h_scaled :
        Real.sqrt 2 * (t * Real.exp (-(t ^ 2))) ≤
          Real.sqrt 2 * ((Real.sqrt 2 / 2) * Real.exp (-(1 / 2 : ℝ))) := by
      calc
        Real.sqrt 2 * (t * Real.exp (-(t ^ 2)))
            ≤ Real.exp (-(1 / 2 : ℝ)) := h_mul
        _ = Real.sqrt 2 * ((Real.sqrt 2 / 2) * Real.exp (-(1 / 2 : ℝ))) := by
          symm
          exact h_factor
    exact le_of_mul_le_mul_left h_scaled hsqrt2_pos
  have h_min :
      quadraticInterpolationExerciseObjective (Real.sqrt 2 / 2) ≤
        quadraticInterpolationExerciseObjective t := by
    simp [quadraticInterpolationExerciseObjective, h_xstar_sq]
    nlinarith
  exact h_min
