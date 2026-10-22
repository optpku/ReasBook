/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Basic

open Filter Asymptotics

section InexactNewtonMethod

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- Source/core/bridge triage:
-- * source-facing: `IsInexactNewtonSequence`
-- * core/canonical: `HasFDerivAt`, `fderiv`, and the ambient normed-space Newton equation
-- * bridge/view: accessor lemmas extracting the derivative, residual, and update data
--
-- Domain sampling:
-- * `Mathlib.Analysis.Calculus.FDeriv.Basic`: `HasFDerivAt.fderiv`
-- * `Chapter03/Theorem_3_2_2.lean`: `IsNewtonMethodSequence`
-- * `Chapter03/Algorithm_3_2_3.lean`: `NewtonMethodWithLineSearch`
--
-- The primitive Chapter 3.6 data are the four sequences `x`, `s`, `r`, and `ηSeq`. The
-- derivative, linear-system, residual-bound, and update conditions are logical constraints on
-- that data, so the source-facing owner is the sequence predicate rather than a wrapper
-- structure with duplicated fields.

/-- Chapter03 Algorithm 3.6-extra-2: sequences `x k`, `s k`, `r k`, and `ηSeq k` are generated
by the inexact Newton method for `F : E → E` when `F` is Fréchet differentiable at each
iterate `x k`, the inexact Newton equation `fderiv ℝ F (x k) (s k) = -F (x k) + r k` holds, the
residual bound `‖r k‖ ≤ ηSeq k * ‖F (x k)‖` is satisfied, and the update is
`x (k + 1) = x k + s k`. -/
def IsInexactNewtonSequence
    (F : E → E) (x s r : ℕ → E) (ηSeq : ℕ → ℝ) : Prop :=
  (∀ k : ℕ, HasFDerivAt F (fderiv ℝ F (x k)) (x k)) ∧
    (∀ k : ℕ, fderiv ℝ F (x k) (s k) = -F (x k) + r k) ∧
    (∀ k : ℕ, ‖r k‖ ≤ ηSeq k * ‖F (x k)‖) ∧
    ∀ k : ℕ, x (k + 1) = x k + s k

/-- Unfolding formula for `IsInexactNewtonSequence`. -/
theorem isInexactNewtonSequence_iff
    (F : E → E) (x s r : ℕ → E) (ηSeq : ℕ → ℝ) :
    IsInexactNewtonSequence F x s r ηSeq ↔
      (∀ k : ℕ, HasFDerivAt F (fderiv ℝ F (x k)) (x k)) ∧
        (∀ k : ℕ, fderiv ℝ F (x k) (s k) = -F (x k) + r k) ∧
        (∀ k : ℕ, ‖r k‖ ≤ ηSeq k * ‖F (x k)‖) ∧
        (∀ k : ℕ, x (k + 1) = x k + s k) :=
  Iff.rfl

namespace IsInexactNewtonSequence

/-- An inexact Newton sequence records the derivative, linear-system, residual, and update
conditions. -/
theorem spec
    {F : E → E} {x s r : ℕ → E} {ηSeq : ℕ → ℝ}
    (h : IsInexactNewtonSequence F x s r ηSeq) :
    (∀ k : ℕ, HasFDerivAt F (fderiv ℝ F (x k)) (x k)) ∧
      (∀ k : ℕ, fderiv ℝ F (x k) (s k) = -F (x k) + r k) ∧
      (∀ k : ℕ, ‖r k‖ ≤ ηSeq k * ‖F (x k)‖) ∧
      (∀ k : ℕ, x (k + 1) = x k + s k) :=
  h

/-- `F` is Fréchet differentiable at each iterate of an inexact Newton sequence. -/
theorem hasFDerivAt
    {F : E → E} {x s r : ℕ → E} {ηSeq : ℕ → ℝ}
    (h : IsInexactNewtonSequence F x s r ηSeq) (k : ℕ) :
    HasFDerivAt F (fderiv ℝ F (x k)) (x k) :=
  h.spec.1 k

/-- Each step of an inexact Newton sequence satisfies the inexact Newton linear system. -/
theorem linearSystem
    {F : E → E} {x s r : ℕ → E} {ηSeq : ℕ → ℝ}
    (h : IsInexactNewtonSequence F x s r ηSeq) (k : ℕ) :
    fderiv ℝ F (x k) (s k) = -F (x k) + r k :=
  h.spec.2.1 k

/-- Each residual in an inexact Newton sequence satisfies the forcing bound. -/
theorem residualBound
    {F : E → E} {x s r : ℕ → E} {ηSeq : ℕ → ℝ}
    (h : IsInexactNewtonSequence F x s r ηSeq) (k : ℕ) :
    ‖r k‖ ≤ ηSeq k * ‖F (x k)‖ :=
  h.spec.2.2.1 k

/-- The pointwise residual bound of an inexact Newton sequence is the canonical asymptotic
estimate `‖r k‖ = O(ηSeq k * ‖F (x k)‖)` at `k → ∞`. -/
theorem residual_isBigO
    {F : E → E} {x s r : ℕ → E} {ηSeq : ℕ → ℝ}
    (h : IsInexactNewtonSequence F x s r ηSeq)
    (hη_nonneg : ∀ k : ℕ, 0 ≤ ηSeq k) :
    (fun k ↦ ‖r k‖) =O[atTop] fun k ↦ ηSeq k * ‖F (x k)‖ :=
  isBigO_of_le atTop fun k ↦ by
    simpa [Real.norm_eq_abs, abs_of_nonneg (hη_nonneg k), abs_of_nonneg (norm_nonneg _)] using
      h.residualBound k

/-- The iterates of an inexact Newton sequence update by the Newton step. -/
theorem update
    {F : E → E} {x s r : ℕ → E} {ηSeq : ℕ → ℝ}
    (h : IsInexactNewtonSequence F x s r ηSeq) (k : ℕ) :
    x (k + 1) = x k + s k :=
  h.spec.2.2.2 k

/-- The residual is the defect `fderiv ℝ F (x k) (s k) + F (x k)` of the exact Newton
equation. -/
theorem residual_eq
    {F : E → E} {x s r : ℕ → E} {ηSeq : ℕ → ℝ}
    (h : IsInexactNewtonSequence F x s r ηSeq) (k : ℕ) :
    r k = fderiv ℝ F (x k) (s k) + F (x k) := by
  calc
    r k = r k + (-F (x k) + F (x k)) := by simp
    _ = (-F (x k) + r k) + F (x k) := by ac_rfl
    _ = fderiv ℝ F (x k) (s k) + F (x k) := by rw [← h.linearSystem k]

end IsInexactNewtonSequence

end InexactNewtonMethod
