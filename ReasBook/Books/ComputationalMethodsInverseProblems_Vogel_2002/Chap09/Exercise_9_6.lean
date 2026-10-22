/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Remark_9_10

public section

noncomputable section

namespace NonnegativeOrthant

variable {n : ℕ}
variable {J : EuclideanSpace ℝ (Fin n) → ℝ}
variable {fStar : EuclideanSpace ℝ (Fin n)}

/-- Exercise 9.6. If `J` is strictly convex on the nonnegative orthant and
Fréchet differentiable at every feasible point, then any critical point `fStar`
for problem `(9.16)` is the unique global constrained minimizer. -/
theorem isMinOn_and_eq_of_isCriticalPoint_of_strictConvexOn
    (hJ_diff :
      ∀ x ∈ feasibleSet n,
        DifferentiableAt ℝ J x)
    (hJ_strict :
      StrictConvexOn ℝ (feasibleSet n) J)
    (hcrit : IsCriticalPoint J fStar) :
    fStar ∈ feasibleSet n ∧
      IsMinOn J (feasibleSet n) fStar ∧
      ∀ g : EuclideanSpace ℝ (Fin n),
        g ∈ feasibleSet n →
        IsMinOn J (feasibleSet n) g →
          g = fStar := by
  refine ⟨hcrit.mem_feasibleSet, ?_, ?_⟩
  · exact isMinOn_of_isCriticalPoint_of_strictConvexOn hJ_diff hJ_strict hcrit
  · intro g hg hmin
    exact hJ_strict.eq_of_isMinOn hmin
      (isMinOn_of_isCriticalPoint_of_strictConvexOn hJ_diff hJ_strict hcrit)
      hg hcrit.mem_feasibleSet

end NonnegativeOrthant
