/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

public section

noncomputable section

namespace Fredholm1D

/-- The Figure 1.1 benchmark true solution for Exercise 1.14 as an explicit
function `ℝ → ℝ` with value `0.75` on `(0.1, 0.25)`, value `0.25` on
`(0.3, 0.32)`, value `Real.sin (2 * Real.pi * x) ^ 4` on `(0.5, 1)`, and value
`0` elsewhere. -/
@[expose] def figure11TrueSolution : ℝ → ℝ :=
  fun x ↦
    if x ∈ Set.Ioo (0.1 : ℝ) 0.25 then
      0.75
    else if x ∈ Set.Ioo (0.3 : ℝ) 0.32 then
      0.25
    else if x ∈ Set.Ioo (0.5 : ℝ) 1 then
      Real.sin (2 * Real.pi * x) ^ 4
    else
      0

/-- Exercise 1.14. The Figure 1.1 benchmark true solution is given by the
piecewise four-case formula recorded in `Fredholm1D.figure11TrueSolution`. -/
theorem exercise_1_14 (x : ℝ) :
    figure11TrueSolution x =
      if x ∈ Set.Ioo (0.1 : ℝ) 0.25 then
        0.75
      else if x ∈ Set.Ioo (0.3 : ℝ) 0.32 then
        0.25
      else if x ∈ Set.Ioo (0.5 : ℝ) 1 then
        Real.sin (2 * Real.pi * x) ^ 4
      else
        0 := by
  -- The main exercise entry is exactly the defining pointwise formula.
  rfl

/-- Companion API for the pointwise four-case formula of
`Fredholm1D.figure11TrueSolution`. -/
theorem figure11TrueSolution_eq_if (x : ℝ) :
    figure11TrueSolution x =
      if x ∈ Set.Ioo (0.1 : ℝ) 0.25 then
        0.75
      else if x ∈ Set.Ioo (0.3 : ℝ) 0.32 then
        0.25
      else if x ∈ Set.Ioo (0.5 : ℝ) 1 then
        Real.sin (2 * Real.pi * x) ^ 4
      else
        0 := by
  -- The companion theorem restates the main exercise identity under a descriptive name.
  exact exercise_1_14 x

/-- Helper for Exercise 1.14: on the first plateau interval, the benchmark solution equals
`0.75`. -/
theorem figure11TrueSolution_of_mem_firstPlateau {x : ℝ}
    (hx : x ∈ Set.Ioo (0.1 : ℝ) 0.25) :
    figure11TrueSolution x = 0.75 := by
  -- The first branch of the piecewise definition applies immediately on `(0.1, 0.25)`.
  simp [figure11TrueSolution, hx]

/-- Helper for Exercise 1.14: outside the three active intervals, the benchmark solution
vanishes. -/
theorem figure11TrueSolution_eq_zero_of_not_mem_intervals {x : ℝ}
    (hFirst : x ∉ Set.Ioo (0.1 : ℝ) 0.25)
    (hSecond : x ∉ Set.Ioo (0.3 : ℝ) 0.32)
    (hOscillatory : x ∉ Set.Ioo (0.5 : ℝ) 1) :
    figure11TrueSolution x = 0 := by
  -- Once all three interval tests fail, only the fallback branch remains.
  simp [figure11TrueSolution, hFirst, hSecond, hOscillatory]

end Fredholm1D
