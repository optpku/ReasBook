/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Algorithm_3_1_1.Iterates

public section

noncomputable section

namespace SteepestDescent

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Exercise 8.4. A sequence satisfies the forward-Euler recurrence
`f (v + 1) = f v - Δt • gradient T (f v)` with initial value `f 0 = f0` if and
only if it is the steepest-descent iterate sequence
`SteepestDescent.iterates T (fun _ ↦ Δt) f0`, so the line-search parameter is
the fixed constant step `fun _ ↦ Δt`. -/
theorem forwardEuler_iff_eq_iterates_constStep
    (T : H → ℝ) (Δt : ℝ) (f0 : H) (f : ℕ → H) :
    ((f 0 = f0) ∧ ∀ v : ℕ, f (v + 1) = f v - Δt • gradient T (f v)) ↔
      f = iterates T (fun _ ↦ Δt) f0 := by
  simpa [SteepestDescent.update_eq_sub_smul_gradient] using
    recurrence_iff_eq_iterates T (fun _ ↦ Δt) f0 f

end SteepestDescent
