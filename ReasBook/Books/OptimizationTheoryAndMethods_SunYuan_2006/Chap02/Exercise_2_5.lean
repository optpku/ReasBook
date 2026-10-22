/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_5_extra_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_5_extra_3

-- Chapter 2 already owns the one-dimensional sufficient-decrease, Goldstein, and
-- Wolfe-Powell predicates, so this exercise keeps only the concrete cubic profile data.

/-- The cubic function `φ(t) = -2 t^3 + 21 t^2 - 60 t + 50` from the line-search exercise. -/
def exercise25Phi : ℝ → ℝ :=
  fun t ↦ -2 * t ^ 3 + 21 * t ^ 2 - 60 * t + 50

/-- The derivative `φ'(t) = -6 t^2 + 42 t - 60` of `exercise25Phi`. -/
def exercise25PhiDeriv : ℝ → ℝ :=
  fun t ↦ -6 * t ^ 2 + 42 * t - 60

/-- The cubic profile takes the value `50` at the origin. -/
theorem exercise25Phi_zero : exercise25Phi 0 = 50 := by
  norm_num [exercise25Phi]

/-- The cubic profile takes the value `25` at `t = 1 / 2`. -/
theorem exercise25Phi_half : exercise25Phi (1 / 2 : ℝ) = 25 := by
  norm_num [exercise25Phi]

/-- The stored slope datum at the origin is `φ'(0) = -60`. -/
theorem exercise25PhiDeriv_zero : exercise25PhiDeriv 0 = -60 := by
  norm_num [exercise25PhiDeriv]

/-- The derivative at `t = 1 / 2` is `φ'(1 / 2) = -81 / 2`. -/
theorem exercise25PhiDeriv_half : exercise25PhiDeriv (1 / 2 : ℝ) = -81 / 2 := by
  norm_num [exercise25PhiDeriv]

/-- Chapter02 Exercise 2.5 (1): the initial trial step `t₀ = 1 / 2` satisfies the Armijo
sufficient-decrease inequality for `φ(t) = -2 t^3 + 21 t^2 - 60 t + 50` with `ρ = 1 / 10`. -/
theorem chapter02Exercise25_armijoAcceptsInitialStep :
    goldsteinSufficientDecrease exercise25Phi (exercise25PhiDeriv 0) (1 / 10 : ℝ) (1 / 2 : ℝ) := by
  rw [goldsteinSufficientDecrease, exercise25Phi_half, exercise25Phi_zero, exercise25PhiDeriv_zero]
  norm_num

/-- Chapter02 Exercise 2.5 (2): the initial trial step `t₀ = 1 / 2` satisfies the Goldstein
condition for `φ(t) = -2 t^3 + 21 t^2 - 60 t + 50` with `ρ = 1 / 10`. -/
theorem chapter02Exercise25_goldsteinAcceptsInitialStep :
    GoldsteinCondition exercise25Phi (exercise25PhiDeriv 0) (1 / 10 : ℝ) (1 / 2 : ℝ) := by
  rw [goldsteinCondition_iff, GoldsteinParameters,
    exercise25Phi_half, exercise25Phi_zero, exercise25PhiDeriv_zero]
  norm_num

/-- Chapter02 Exercise 2.5 (3): the initial trial step `t₀ = 1 / 2` satisfies the Wolfe
condition for `φ(t) = -2 t^3 + 21 t^2 - 60 t + 50` with `ρ = 1 / 10` and `σ = 4 / 5`. -/
theorem chapter02Exercise25_wolfeAcceptsInitialStep :
    WolfePowellCondition exercise25Phi exercise25PhiDeriv
      (1 / 10 : ℝ) (4 / 5 : ℝ) (1 / 2 : ℝ) := by
  refine ⟨?_, by norm_num, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, by norm_num⟩
  · rw [exercise25Phi_half, exercise25Phi_zero, exercise25PhiDeriv_zero]
    norm_num
  · rw [exercise25PhiDeriv_zero, exercise25PhiDeriv_half]
    norm_num
