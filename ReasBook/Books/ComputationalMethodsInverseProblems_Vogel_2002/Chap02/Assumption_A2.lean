/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Assumption_A2.StronglyPositive

public section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

namespace ContinuousLinearMap

/-- Assumption A2. A bounded operator `L` on the real Hilbert space `H` is self-adjoint and
strongly positive. -/
@[mk_iff selfAdjointStronglyPositive_iff]
structure SelfAdjointStronglyPositive (L : H →L[ℝ] H) : Prop where
  /-- The operator `L` is self-adjoint. -/
  isSelfAdjoint : IsSelfAdjoint L
  /-- The operator `L` satisfies a strict lower bound on `inner ℝ (L f) f`. -/
  stronglyPositive : L.IsStronglyPositive

namespace SelfAdjointStronglyPositive

/-- Build `SelfAdjointStronglyPositive L` from self-adjointness and strong positivity. -/
theorem ofSelfAdjoint_isStronglyPositive {L : H →L[ℝ] H}
    (hSelfAdjoint : IsSelfAdjoint L) (hStronglyPositive : L.IsStronglyPositive) :
    SelfAdjointStronglyPositive L :=
  ⟨hSelfAdjoint, hStronglyPositive⟩

/-- The source lower bound `(2.55)` follows:
`c0 * ‖f‖ ^ 2 ≤ inner ℝ (L f) f` for some `c0 > 0`. -/
theorem exists_inner_lowerBound {L : H →L[ℝ] H} (hL : SelfAdjointStronglyPositive L) :
    ∃ c0 : ℝ, 0 < c0 ∧ ∀ f : H, c0 * ‖f‖ ^ 2 ≤ inner ℝ (L f) f :=
  hL.stronglyPositive

/-- A self-adjoint strongly positive operator is positive in mathlib's sense. -/
theorem isPositive {L : H →L[ℝ] H} (hL : SelfAdjointStronglyPositive L) :
    L.IsPositive := by
  rw [ContinuousLinearMap.isPositive_def']
  obtain ⟨c0, hc0, hbound⟩ := hL.stronglyPositive
  refine ⟨hL.isSelfAdjoint, fun f => ?_⟩
  have hnonneg : 0 ≤ inner ℝ (L f) f :=
    le_trans (mul_nonneg hc0.le (sq_nonneg _)) (hbound f)
  rw [ContinuousLinearMap.reApplyInnerSelf_apply]
  simpa using hnonneg

/-- A self-adjoint strongly positive operator has strictly positive quadratic form on nonzero
vectors. -/
theorem inner_pos {L : H →L[ℝ] H} (hL : SelfAdjointStronglyPositive L) {f : H} (hf : f ≠ 0) :
    0 < inner ℝ (L f) f := by
  obtain ⟨c0, hc0, hbound⟩ := hL.stronglyPositive
  have hnorm : 0 < ‖f‖ ^ 2 := by
    have hpos : 0 < ‖f‖ := norm_pos_iff.mpr hf
    positivity
  exact lt_of_lt_of_le (mul_pos hc0 hnorm) (hbound f)

end SelfAdjointStronglyPositive

end ContinuousLinearMap
