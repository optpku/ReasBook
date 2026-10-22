/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Example_13_18
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open ContinuousLinearMap
open scoped InnerProduct InnerProductSpace

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {α β : Set.Ioi (0 : ℝ)} {A B : S(H)}

-- Proof sketch: from `β • 1 ≤ B ≤ A` in the self-adjoint Loewner order, both operators are
-- positive and bounded below away from zero, hence invertible. Apply the standard order-reversing
-- property of inversion on positive operators.
/-- Text 13.18.1: clause (i). For self-adjoint operators, if `β • Id ≤ B ≤ A`, then taking
inverses reverses the Loewner order: `A⁻¹ ≤ B⁻¹`. -/
theorem sandwiched_positive_operators_inverse_antitone
    (hBA : B ≤ A)
    (hβB : (β : ℝ) • 1 ≤ B) :
    (A : H →L[ℝ] H).inverse ≤ (B : H →L[ℝ] H).inverse := sorry

-- Proof sketch: the lower bound `β • 1 ≤ B` in `S(H)` makes `B` positive and bounded below away
-- from zero, hence injective with closed range, so `B` is invertible.
/-- Clause (i): a self-adjoint operator `B` is invertible as soon as `β • Id ≤ B`. -/
theorem sandwiched_positive_operators_right_isUnit
    (hβB : (β : ℝ) • 1 ≤ B) :
    IsUnit (B : H →L[ℝ] H) := sorry

-- Proof sketch: the direct lower bound `β • 1 ≤ A` makes `A` positive and bounded below away
-- from zero, hence invertible. Compare `A` with `α • 1` and reverse the order after inversion.
/-- Clause (i): if the self-adjoint operator `A` satisfies `β • Id ≤ A ≤ α • Id`, then `A⁻¹`
dominates `α⁻¹ • Id`. -/
theorem sandwiched_positive_operators_left_endpoint_le_inverse
    (hA_upper : A ≤ (α : ℝ) • 1)
    (hβA : (β : ℝ) • 1 ≤ A) :
    ((α : ℝ)⁻¹) • (1 : H →L[ℝ] H) ≤ (A : H →L[ℝ] H).inverse := sorry

-- Proof sketch: first prove that `B` is invertible. Then compare `β • 1` with `B` and reverse
-- the order after taking inverses.
/-- Clause (i): if `B` is self-adjoint and `β • Id ≤ B`, then `B⁻¹` is bounded above by
`β⁻¹ • Id`. -/
theorem sandwiched_positive_operators_inverse_le_right_endpoint
    (hβB : (β : ℝ) • 1 ≤ B) :
    (B : H →L[ℝ] H).inverse ≤ ((β : ℝ)⁻¹) • (1 : H →L[ℝ] H) := sorry

-- Proof sketch: for a positive self-adjoint operator, positivity gives the order bound
-- `A ≤ ‖A‖ • 1`. Reverse that inequality after inversion and evaluate the resulting operator
-- inequality on `x`.
/-- Clause (ii): for a positive invertible self-adjoint operator, the quadratic form of the
inverse is bounded below by `‖A‖⁻¹ ‖x‖²`. -/
theorem positive_unit_operator_inverse_inner_self_ge_inv_norm
    (A : S(H)) (hA_nonneg : 0 ≤ A)
    (hA_unit : IsUnit (A : H →L[ℝ] H)) (x : H) :
    ((‖(A : H →L[ℝ] H)‖ : ℝ)⁻¹) * ‖x‖ ^ 2 ≤
      ⟪((A : H →L[ℝ] H).inverse) x, x⟫_ℝ := sorry

-- Proof sketch: the lower bound `β • 1 ≤ A` in the self-adjoint Loewner order becomes
-- `A.inverse ≤ β⁻¹ • 1` after inversion. Taking operator norms then yields the stated estimate.
/-- Clause (iii): if the self-adjoint operator `A` dominates `β • Id` with `β > 0`, then the norm
of its inverse is at most `β⁻¹`. -/
theorem lower_bounded_operator_norm_inverse_le_inv_scalar
    (β : Set.Ioi (0 : ℝ)) (A : S(H))
    (hβA : (β : ℝ) • 1 ≤ A) :
    ‖((A : H →L[ℝ] H).inverse)‖ ≤ (β : ℝ)⁻¹ := sorry

end

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

namespace ContinuousLinearMap

/-- The Gram operator `A†A`, packaged in the self-adjoint Loewner-order owner `S(H)`. -/
noncomputable abbrev gram (A : H →L[ℝ] H) : S(H) :=
  ⟨A.adjoint.comp A, (isPositive_adjoint_comp_self A).isSelfAdjoint⟩

end ContinuousLinearMap

-- Proof sketch: `LipschitzWith 1 A` is equivalent to `‖A‖ ≤ 1` by the operator-norm/Lipschitz
-- API. For the positive self-adjoint Gram operator `A.gram`, the quadratic-form inequality from
-- Example 13.18 rewrites `A†A ≤ 1` to `‖A x‖² ≤ ‖x‖²`, which is the same
-- contraction bound.
/-- Text 13.18.1: clause (iv), operator-order form. A linear operator is nonexpansive exactly when
its Gram operator `A.gram` is bounded above by `Id` in the Loewner order on `S(H)`. -/
theorem nonexpansive_iff_gram_le_one
    (A : H →L[ℝ] H) :
    LipschitzWith 1 A ↔ A.gram ≤ 1 := sorry

-- Proof sketch: use `strictlyLoewner_iff_forall_inner_lt` from Example 13.18 on `A.gram`, then
-- rewrite `⟪(A†A) x, x⟫ = ‖A x‖²`. The resulting strict quadratic-form inequality is
-- equivalent to strict distance contraction between distinct vectors by applying it to `x - y`.
/-- Companion operator-order reformulation of Text 13.18.1, clause (v): whole-space strict
nonexpansiveness of a linear operator is equivalent to strict Loewner domination `A.gram ≺ Id`. -/
theorem strictly_nonexpansive_iff_gram_strictlyLoewner_one
    (A : H →L[ℝ] H) :
    StrictlyNonexpansiveOn Set.univ A ↔ A.gram ≺ 1 := sorry

end

section

variable {𝕜 : Type*} [NormedField 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [NormedSpace 𝕜 H]

-- Proof sketch: for a linear map, pairwise nonexpansiveness is equivalent to the one-point
-- estimate `‖A x‖ ≤ ‖x‖` by applying the pairwise bound to `(x, 0)` and using linearity.
/-- Companion norm reformulation of Text 13.18.1, clause (iv): for a linear operator,
nonexpansiveness is equivalent to the pointwise bound `‖A x‖ ≤ ‖x‖` for every vector `x`. -/
theorem nonexpansive_iff_forall_norm_image_le
    (A : H →L[𝕜] H) :
    LipschitzWith 1 A ↔ ∀ x : H, ‖A x‖ ≤ ‖x‖ := sorry

-- Proof sketch: if the fixed-point set is `{0}`, then strict quasinonexpansiveness reduces to the
-- strict contraction estimate against the single fixed point `0`; for a linear map, that is
-- exactly the canonical whole-space strict-nonexpansive owner on `Set.univ`.
/-- Companion bridge for Text 13.18.1, clause (v): if `Function.fixedPoints A = {0}`, then strict
quasinonexpansiveness on the whole space is exactly whole-space strict nonexpansiveness. -/
theorem strict_quasinonexpansive_with_zero_fixedPoints_iff_strictly_nonexpansive
    (A : H →L[𝕜] H) :
    (StrictlyQuasinonexpansiveOn Set.univ A ∧
      Function.fixedPoints A = ({0} : Set H)) ↔
      StrictlyNonexpansiveOn Set.univ A := sorry

-- Proof sketch: for a linear map, strict nonexpansiveness on all pairs reduces to the origin-based
-- estimate `‖A x‖ < ‖x‖` for `x ≠ 0` by applying the pairwise inequality to `(x, 0)` and using
-- linearity.
/-- Companion norm reformulation of Text 13.18.1, clause (v): whole-space strict nonexpansiveness
of a linear operator is equivalent to strict norm contraction on every nonzero vector. -/
theorem strictly_nonexpansive_iff_forall_norm_image_lt
    (A : H →L[𝕜] H) :
    StrictlyNonexpansiveOn Set.univ A ↔
      ∀ x : H, x ≠ 0 → ‖A x‖ < ‖x‖ := sorry

end

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Text 13.18.1: clause (v). A linear operator is strictly quasinonexpansive on the whole space
with fixed-point set `{0}` exactly when its Gram operator is strictly below `Id` in the strict
Loewner order. -/
theorem strict_quasinonexpansive_with_zero_fixedPoints_iff_gram_strictlyLoewner_one
    (A : H →L[ℝ] H) :
    (StrictlyQuasinonexpansiveOn Set.univ A ∧
      Function.fixedPoints A = ({0} : Set H)) ↔ A.gram ≺ 1 := by
  rw [strict_quasinonexpansive_with_zero_fixedPoints_iff_strictly_nonexpansive,
    strictly_nonexpansive_iff_gram_strictlyLoewner_one]

end
