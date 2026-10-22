/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Theorem_26_26.Coefficients

namespace ProbabilityTheory

variable {n : ℕ}

/-- Shared Stroock--Varadhan growth hypothesis used in Theorem 26.26. -/
def StroockVaradhanGrowthCondition
    (a : StroockVaradhanDiffusionMatrixCoeff n) (b : StroockVaradhanDriftCoeff n) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    (∀ x : StroockVaradhanState n, ∀ i j : Fin n, |a 0 x i j| ≤ C * (1 + ‖x‖ ^ 2)) ∧
    ∀ x : StroockVaradhanState n, ∀ i : Fin n, |b 0 x i| ≤ C * (1 + ‖x‖)

end ProbabilityTheory
