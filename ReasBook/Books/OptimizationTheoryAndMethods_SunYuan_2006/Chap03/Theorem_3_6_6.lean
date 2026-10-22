/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Theorem_3_6_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Theorem_3_4_4

open Filter
open scoped Topology

/-- A forcing sequence is bounded by `η` when every term lies in the interval `[0, η]`. -/
def HasInexactNewtonForcingBound (ηSeq : ℕ → ℝ) (η : ℝ) : Prop :=
  (∀ k : ℕ, 0 ≤ ηSeq k) ∧ ∀ k : ℕ, ηSeq k ≤ η

/-- Unfolding formula for `HasInexactNewtonForcingBound`. -/
theorem hasInexactNewtonForcingBound_iff (ηSeq : ℕ → ℝ) (η : ℝ) :
    HasInexactNewtonForcingBound ηSeq η ↔
      (∀ k : ℕ, 0 ≤ ηSeq k) ∧ ∀ k : ℕ, ηSeq k ≤ η :=
  Iff.rfl

namespace HasInexactNewtonForcingBound

/-- A forcing-bound hypothesis gives nonnegativity of each forcing term. -/
theorem nonneg {ηSeq : ℕ → ℝ} {η : ℝ} (h : HasInexactNewtonForcingBound ηSeq η) (k : ℕ) :
    0 ≤ ηSeq k :=
  h.1 k

/-- A forcing-bound hypothesis gives the uniform upper bound `ηSeq k ≤ η`. -/
theorem le {ηSeq : ℕ → ℝ} {η : ℝ} (h : HasInexactNewtonForcingBound ηSeq η) (k : ℕ) :
    ηSeq k ≤ η :=
  h.2 k

end HasInexactNewtonForcingBound

section InexactNewtonMethod

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

-- Semantic recall: the generic Chapter 3.6 owners `IsRegularZero` and
-- `IsInexactNewtonSequence` already live upstream on intrinsic normed-space declarations.
-- This file keeps the bounded-forcing and eventual-linear convergence owners intrinsic, then
-- specializes the labeled source theorem to `ℝⁿ`.

/-- Chapter03 Theorem 3.6.6 (1): if `(A1)`-`(A3)` hold at the regular zero `xStar`,
`0 ≤ ηSeq k ≤ η < 1`, and the initial iterate is sufficiently near `xStar`, then the
inexact Newton iterates converge to `xStar` and eventually satisfy the linear rate
`‖x (k + 1) - xStar‖ ≤ c * ‖x k - xStar‖` for some `0 < c < 1`. -/
theorem inexactNewton_tendsto_root_and_eventually_linear_of_forcing_bounded
    (F : Point → Point) (xStar : Point) (η : ℝ)
    (h_regular : IsRegularZero F xStar)
    (hη_lt_one : η < 1) :
    ∃ ε > 0, ∀ x s r : ℕ → Point, ∀ ηSeq : ℕ → ℝ,
      ‖x 0 - xStar‖ < ε →
      IsInexactNewtonSequence F x s r ηSeq →
      HasInexactNewtonForcingBound ηSeq η →
      HasEventuallyLinearConvergenceTo x xStar := sorry

/-- Chapter03 Theorem 3.6.6 (2): under the same regular-zero and bounded-forcing hypotheses,
if additionally `ηSeq ⟶ 0`, then every sufficiently near inexact Newton sequence converges to
`xStar` superlinearly. -/
theorem inexactNewton_tendsto_root_and_superlinear_of_forcing_tendsto_zero
    (F : Point → Point) (xStar : Point) (η : ℝ)
    (h_regular : IsRegularZero F xStar)
    (hη_lt_one : η < 1) :
    ∃ ε > 0, ∀ x s r : ℕ → Point, ∀ ηSeq : ℕ → ℝ,
      ‖x 0 - xStar‖ < ε →
      IsInexactNewtonSequence F x s r ηSeq →
      HasInexactNewtonForcingBound ηSeq η →
      Tendsto ηSeq atTop (nhds 0) →
      HasSuperlinearConvergenceTo x xStar := sorry

/-- Chapter03 Theorem 3.6.6 (3): under the same regular-zero and bounded-forcing hypotheses,
if additionally `ηSeq = O(‖F (x k)‖)`, then every sufficiently near inexact Newton sequence
converges to `xStar` quadratically. -/
theorem inexactNewton_tendsto_root_and_quadratic_of_forcing_isBigO
    (F : Point → Point) (xStar : Point) (η : ℝ)
    (h_regular : IsRegularZero F xStar)
    (hη_lt_one : η < 1) :
    ∃ ε > 0, ∀ x s r : ℕ → Point, ∀ ηSeq : ℕ → ℝ,
      ‖x 0 - xStar‖ < ε →
      IsInexactNewtonSequence F x s r ηSeq →
      HasInexactNewtonForcingBound ηSeq η →
      ((fun k ↦ ηSeq k) =O[atTop] fun k ↦ ‖F (x k)‖) →
      HasQuadraticConvergenceTo x xStar := sorry

end InexactNewtonMethod
