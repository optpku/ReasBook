/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Example_20_16

-- Declarations for this item will be appended below by the statement pipeline.

open ContinuousLinearMap
open scoped InnerProduct InnerProductSpace

universe u

namespace ContinuousLinearMap

/-- The quadratic potential `q_A(x) = (1 / 2) ⟪x, A x⟫_ℝ` attached to a bounded linear operator,
realized as the diagonal of the canonical sesquilinear form `toSesqForm A`. -/
noncomputable def quadraticPotential {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H →L[ℝ] H) : H → ℝ :=
  fun x ↦ (1 / 2 : ℝ) * A.toSesqForm x x

/- Lean cannot parse an arbitrary term as a literal subscript, so we use the bracketed surface
`q[A]` as the direct notation for the quadratic potential `q_A`. -/
scoped notation:max "q[" A:max "]" => quadraticPotential A

/-- Evaluating `quadraticPotential A` at `x` gives `(1 / 2) ⟪x, A x⟫_ℝ`. -/
@[simp] theorem quadraticPotential_apply {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (A : H →L[ℝ] H) (x : H) :
    q[A] x = (1 / 2 : ℝ) * ⟪x, A x⟫_ℝ := rfl

end ContinuousLinearMap

-- Proof sketch: Example 2.57 identifies the gradient of the quadratic form
-- `x ↦ ⟪x, A x⟫_ℝ` with the linear field `x ↦ (A + A.adjoint) x`. Proposition 17.7 on
-- `Set.univ` then says that convexity is equivalent to pointwise nonnegativity of the quadratic
-- form of this second derivative, which here is exactly
-- `x ↦ ⟪(A + A†) x, x⟫_ℝ`.
/-- Example 17.8: for a bounded linear operator `A` on a real Hilbert space, the quadratic form
`x ↦ ⟪x, A x⟫_ℝ` is convex on `H` if and only if the quadratic form of the symmetric part `A + A†`
is pointwise nonnegative. -/
theorem quadraticForm_convexOn_univ_iff_symmetricPart_nonnegative
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →L[ℝ] H) :
    ConvexOn ℝ Set.univ (fun x : H ↦ ⟪x, A x⟫_ℝ) ↔
      ∀ x : H, 0 ≤ ⟪(A + A†) x, x⟫_ℝ := sorry

-- Proof sketch: use Example 20.16 to replace monotonicity of `A + A†` by the canonical owner
-- predicate `LinearMap.IsMonotone`, then unfold that owner on the symmetric part.
/-- Canonical bridge for Example 17.8: the same convexity criterion can be expressed by saying
that `A` is monotone. -/
theorem quadraticForm_convexOn_univ_iff_isMonotone
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →L[ℝ] H) :
    ConvexOn ℝ Set.univ (fun x : H ↦ ⟪x, A x⟫_ℝ) ↔
      A.toLinearMap.IsMonotone := by
  rw [isMonotone_iff_add_adjoint_isMonotone]
  simpa [LinearMap.IsMonotone] using
    quadraticForm_convexOn_univ_iff_symmetricPart_nonnegative A
