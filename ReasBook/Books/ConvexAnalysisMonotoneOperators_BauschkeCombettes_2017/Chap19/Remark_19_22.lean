/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap19.Proposition_19_21

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped InnerProductSpace

universe u v

namespace ERealFunction

section EqualityConstraintDuality

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- The unconstrained affine objective obtained from the equality-constraint Lagrangian after
freezing the multiplier `v`, written in the primitive pairing form `f x + ⟪L x, v⟫`. In
complete Hilbert spaces this agrees with `f x + ⟪x, L.adjoint v⟫`. -/
def equalityConstraintAffineObjective
    (f : H → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) (v : K) : H → EReal :=
  fun x ↦ (f x : EReal) + (⟪L x, v⟫_ℝ : EReal)

-- Proof sketch: use the saddle-point inequalities directly on the canonical owner
-- `ℒ[equalityConstraintPerturbationFunction f L r]`. Proposition 19.21 (4) rewrites each
-- Lagrangian fiber as `x ↦ f x + ⟪L x - r, v⟫` on `effectiveDomain f`. At `(x̄, v̄)`, varying the
-- multiplier forces `L x̄ = r`; then the same branch formula turns the right saddle inequality
-- into the desired optimality inequality for the affine objective `x ↦ f x + ⟪L x, v̄⟫`.
/-- A Lagrange multiplier associated with `x̄` makes `x̄` solve the unconstrained minimization
problem `min_x f x + ⟪L x, v̄⟫`, equivalently `min_x f x + ⟪x, L^* v̄⟫` when the adjoint is
available. -/
theorem mem_argmin_of_isEqualityConstraintLagrangeMultiplier
    (f : H → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K) (r : K)
    {xbar : H} {vbar : K}
    (hsaddle :
      IsSaddlePointOn (Set.univ : Set H) (Set.univ : Set K)
        (ℒ[equalityConstraintPerturbationFunction f L r]) xbar vbar) :
    xbar ∈ Argmin (equalityConstraintAffineObjective f L vbar) := sorry

end EqualityConstraintDuality

end ERealFunction
