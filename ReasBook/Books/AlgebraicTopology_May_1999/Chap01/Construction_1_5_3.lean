/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/-- The exponential line underlying the standard loop is continuous on the unit interval. -/
-- Proof sketch: `Circle.exp` is continuous on `ℝ`, and composing it with the affine map
-- `s ↦ 2 * π * n * s` preserves continuity; then restrict to `unitInterval`.
theorem standardLoop_continuousOn (n : ℤ) :
    ContinuousOn
      (fun s : ℝ ↦ Circle.exp (2 * Real.pi * (n : ℝ) * s))
      unitInterval := by
  -- The loop comes from composing `Circle.exp` with the affine line `s ↦ 2 * π * n * s`.
  have hline : Continuous (fun s : ℝ ↦ 2 * Real.pi * (n : ℝ) * s) := by
    fun_prop
  exact (Circle.exp.continuous.comp hline).continuousOn

/-- The exponential line defining the standard loop starts at the circle basepoint `1`. -/
-- Proof sketch: evaluate at `s = 0` and simplify the exponent to `0`, then use
-- `Circle.exp_zero`.
theorem standardLoop_zero (n : ℤ) :
    Circle.exp (2 * Real.pi * (n : ℝ) * 0) = (1 : Circle) := by
  -- At `s = 0`, the exponent is `0`, so the exponential hits the basepoint.
  simp

/-- The exponential line defining the standard loop ends at the circle basepoint `1`. -/
-- Proof sketch: evaluate at `s = 1`, rewrite the exponent as `2 * π * n`, and apply
-- `Circle.exp_two_pi_mul_int`.
theorem standardLoop_one (n : ℤ) :
    Circle.exp (2 * Real.pi * (n : ℝ) * 1) = (1 : Circle) := by
  -- At `s = 1`, the exponent is `2 * π * n`, which is a full integer number of turns.
  simpa [mul_assoc] using Circle.exp_two_pi_mul_int n

/-- Construction 1.5.3: for each integer `n`, the standard loop on `S^1` based at `1` is the
path `s ↦ e^{2πins}`, represented in mathlib by `s ↦ Circle.exp (2 * π * n * s)`. -/
def standardLoop (n : ℤ) : Path (1 : Circle) 1 :=
  Path.ofLine (standardLoop_continuousOn n) (standardLoop_zero n) (standardLoop_one n)

/-- Evaluating the standard loop gives the expected exponential formula on the unit interval. -/
@[simp] theorem standardLoop_apply (n : ℤ) (s : unitInterval) :
    standardLoop n s = Circle.exp (2 * Real.pi * (n : ℝ) * (s : ℝ)) :=
  rfl
