/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Definition_7_5

public section

noncomputable section

/-!
Exercise 7.27 (minimum-bound comparison).

This exercise asks for a qualitative comparison of the minimum-bound method
with the other parameter-choice rules from Section 7.6. The canonical Chapter 7
owner for the method is `IsMinimumBoundParameter`: it says that `α` minimizes
the minimum-bound objective on the admissible positive parameters. The
source-facing comparison content is therefore the direct inequality asserting
that the minimum-bound choice is no worse than any other admissible positive
comparison parameter with respect to the same objective.
-/

universe u

section

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- Exercise 7.27. A minimum-bound parameter gives a minimum-bound value no
larger than any other admissible positive comparison parameter. In particular,
this compares the minimum-bound choice qualitatively with any competing
Section 7.6 parameter once that parameter is known to be positive. -/
theorem minimumBoundComparison
    (K : Matrix n n ℝ) (rfamily : ℝ → EuclideanSpace ℝ n) (γ σ α : ℝ)
    (hα : IsMinimumBoundParameter K rfamily γ σ α)
    (β : ℝ) (hβ : 0 < β) :
    minimumBound K rfamily γ σ α ≤ minimumBound K rfamily γ σ β := by
  exact (isMinOn_iff.mp (hα.isMinOn K rfamily γ σ α)) β hβ

end

end
