/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Definition_9_9.CriticalPoint
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Definition_9_13.ProjectedGradient

public section

noncomputable section

namespace NonnegativeOrthant

variable {n : ℕ}

/-- Proposition 9.14. A feasible point for the nonnegative-orthant problem
`(9.16)` is a critical point if and only if its projected gradient vanishes. -/
theorem isCriticalPoint_iff_projectedGradient_eq_zero
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    (f : feasibleSet n) :
    IsCriticalPoint J f ↔ projectedGradient J f = 0 := by
  have hf : ∀ i : Fin n, 0 ≤ (f : EuclideanSpace ℝ (Fin n)) i := by
    exact mem_feasibleSet.mp f.property
  constructor
  · intro hcrit
    ext i
    by_cases hpos : 0 < (f : EuclideanSpace ℝ (Fin n)) i
    · rw [projectedGradient_apply_of_pos J (f : EuclideanSpace ℝ (Fin n)) f.property i hpos]
      exact (mul_eq_zero.mp (hcrit.complementarity i)).resolve_left (ne_of_gt hpos)
    · have hi : (f : EuclideanSpace ℝ (Fin n)) i = 0 := le_antisymm (le_of_not_gt hpos) (hf i)
      rw [projectedGradient_apply_of_eq_zero J (f : EuclideanSpace ℝ (Fin n)) f.property i hi]
      exact min_eq_left (hcrit.gradientNonneg i)
  · intro hproj
    refine (isCriticalPoint_iff J f).2 ?_
    refine ⟨f.property, ?_, ?_⟩
    · intro i
      by_cases hpos : 0 < (f : EuclideanSpace ℝ (Fin n)) i
      · have hgrad : gradient J f i = 0 := by
          have hcoord : projectedGradient J f i = 0 := by
            simpa using congrArg (fun g ↦ g i) hproj
          rw [projectedGradient_apply_of_pos J
            (f : EuclideanSpace ℝ (Fin n)) f.property i hpos] at hcoord
          exact hcoord
        simp [hgrad]
      · have hi : (f : EuclideanSpace ℝ (Fin n)) i = 0 := le_antisymm (le_of_not_gt hpos) (hf i)
        have hcoord : min (0 : ℝ) (gradient J f i) = 0 := by
          have hpg : projectedGradient J f i = 0 := by
            simpa using congrArg (fun g ↦ g i) hproj
          rw [projectedGradient_apply_of_eq_zero J
            (f : EuclideanSpace ℝ (Fin n)) f.property i hi] at hpg
          exact hpg
        exact min_eq_left_iff.mp hcoord
    · intro i
      by_cases hpos : 0 < (f : EuclideanSpace ℝ (Fin n)) i
      · have hgrad : gradient J f i = 0 := by
          have hcoord : projectedGradient J f i = 0 := by
            simpa using congrArg (fun g ↦ g i) hproj
          rw [projectedGradient_apply_of_pos J
            (f : EuclideanSpace ℝ (Fin n)) f.property i hpos] at hcoord
          exact hcoord
        simp [hgrad]
      · have hi : (f : EuclideanSpace ℝ (Fin n)) i = 0 := le_antisymm (le_of_not_gt hpos) (hf i)
        simp [hi]

end NonnegativeOrthant
