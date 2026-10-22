/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.InnerProductSpace.Positive

public section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

namespace ContinuousLinearMap

/-- A bounded operator `L` on a real Hilbert space is strongly positive if there exists
`c0 > 0` such that `c0 * ‖f‖ ^ 2 ≤ inner ℝ (L f) f` for every `f`. -/
def IsStronglyPositive (L : H →L[ℝ] H) : Prop :=
  ∃ c0 : ℝ, 0 < c0 ∧ ∀ f : H, c0 * ‖f‖ ^ 2 ≤ inner ℝ (L f) f

/-- Rewrites `L.IsStronglyPositive` as the source lower-bound condition on `inner ℝ (L f) f`. -/
theorem isStronglyPositive_iff {L : H →L[ℝ] H} :
    L.IsStronglyPositive ↔
      ∃ c0 : ℝ, 0 < c0 ∧ ∀ f : H, c0 * ‖f‖ ^ 2 ≤ inner ℝ (L f) f := by
  rfl

namespace IsStronglyPositive

/-- A strongly positive operator admits the source lower bound `c0 * ‖f‖ ^ 2 ≤ inner ℝ (L f) f`
for some `c0 > 0`. -/
theorem exists_inner_lowerBound {L : H →L[ℝ] H} (hL : L.IsStronglyPositive) :
    ∃ c0 : ℝ, 0 < c0 ∧ ∀ f : H, c0 * ‖f‖ ^ 2 ≤ inner ℝ (L f) f := by
  exact hL

end IsStronglyPositive

end ContinuousLinearMap
