/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Definition_9_9.CriticalPoint
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Definition_9_5.StrictComplementarity

public section

noncomputable section

namespace NonnegativeOrthant

variable {n : ℕ}

/-- Helper for Remark 9.11: `KKT.StrictComplementarity` specialized to the
nonnegative-orthant constraints `x ↦ x i` and multipliers `gradient J f i`. -/
abbrev StrictComplementarity
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    (f : EuclideanSpace ℝ (Fin n)) : Prop :=
  KKT.StrictComplementarity (fun i x ↦ x i) f (fun i ↦ gradient J f i)

/-- Remark 9.11. The strict complementarity condition `(9.20)` for
nonnegatively constrained minimization is equivalent to the coordinatewise form
`f i = 0 → 0 < gradient J f i`. -/
theorem strictComplementarity_iff
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    (f : EuclideanSpace ℝ (Fin n)) :
    StrictComplementarity J f ↔
      ∀ i : Fin n, f i = 0 → 0 < gradient J f i := by
  -- This is the generic KKT strict-complementarity equivalence for `c i x = x i`.
  simpa [StrictComplementarity] using
    (KKT.strictComplementarity_iff
      (fun i x ↦ x i) f (fun i ↦ gradient J f i))

end NonnegativeOrthant

/- Remark 9.11 (1). As a consequence of `(9.17)`-`(9.19)`, if
`0 < gradient J fStar i`, then `fStar i = 0`. -/
#check NonnegativeOrthant.IsCriticalPoint.eq_zero_of_gradient_pos

/- Remark 9.11 (2). The strict complementarity condition `(9.20)` for
nonnegatively constrained minimization is formalized by
`NonnegativeOrthant.StrictComplementarity`. -/
#check NonnegativeOrthant.StrictComplementarity
