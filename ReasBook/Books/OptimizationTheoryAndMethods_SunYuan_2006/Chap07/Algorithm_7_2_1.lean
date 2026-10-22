/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import OptimizationTheoryAndMethods_SunYuan_2006.Chap07.Theorem_7_2_2

noncomputable section

open Matrix

section

variable {m n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "Residual" => EuclideanSpace ℝ (Fin m)
local notation "JacobianMatrix" => Matrix (Fin m) (Fin n) ℝ
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

-- Domain sampling for this item:
-- * primary domain: finite-dimensional nonlinear least-squares Gauss-Newton iteration data with
--   a source-faithful stopping rule;
-- * sampled declarations in the owner family:
--   `Matrix.toEuclideanLin`,
--   `SunYuanOptimizationTheoryMethods.Chap07.Theorem_7_2_2.leastSquaresGradient`,
--   `SunYuanOptimizationTheoryMethods.Chap03.Algorithm_3_2_3.
--      NewtonMethodWithLineSearch.IsTerminalIndex`,
--   `SunYuanOptimizationTheoryMethods.Chap05.Algorithm_5_7_2.LBFGSMethod.terminatedAt`;
-- * source-facing owner here: the stopping-aware Gauss-Newton iteration object;
-- * core/canonical owner reused here: the Chapter 7 least-squares gradient owner
--   `leastSquaresGradient` together with the Euclidean-space matrix action
--   `Matrix.toEuclideanLin`;
-- * primitive data here: iterate and step sequences together with the active-step normal equation
--   and update law, plus the constant-tail rule after the stopping test fires;
-- * derived API here: the stopping/active predicates, their complementarity, the terminal-index
--   view, and bundled active-step consequences.

/-- The Gauss-Newton gradient `g(x) = J(x)ᵀ r(x)` used in the stopping test. -/
def gaussNewtonGradient
    (J : Point → JacobianMatrix) (r : Point → Residual) (x : Point) : Point :=
  ((J x)ᵀ).toEuclideanLin (r x)

/-- Unfolding formula for `gaussNewtonGradient`. -/
theorem gaussNewtonGradient_eq
    (J : Point → JacobianMatrix) (r : Point → Residual) (x : Point) :
    gaussNewtonGradient J r x =
      ((J x)ᵀ).toEuclideanLin (r x) :=
  rfl

/-- When `J` is the actual Jacobian field of `r`, the source-facing Gauss-Newton gradient agrees
with the canonical Chapter 7 least-squares gradient owner. -/
theorem gaussNewtonGradient_eq_leastSquaresGradient
    (J : Point → JacobianMatrix) (r : Point → Residual)
    (hJ : ∀ x : Point, J x = residualJacobianMatrix r x) (x : Point) :
    gaussNewtonGradient J r x = leastSquaresGradient r x := by
  simp [gaussNewtonGradient, leastSquaresGradient, hJ x]

/-- Specializing the bridge to the actual Jacobian owner `residualJacobianMatrix`. -/
@[simp] theorem gaussNewtonGradient_residualJacobianMatrix
    (r : Point → Residual) (x : Point) :
    gaussNewtonGradient (residualJacobianMatrix r) r x = leastSquaresGradient r x :=
  rfl

/-- Chapter07 Algorithm 7.2.1: a Gauss-Newton iteration for residual map `r` and Jacobian map
`J` starts from `x₀`, uses a tolerance `ε`, stops whenever `‖J(xₖ)ᵀ r(xₖ)‖ ≤ ε`, and
otherwise chooses a step `sₖ` solving `J(xₖ)ᵀ J(xₖ) sₖ = -J(xₖ)ᵀ r(xₖ)` and updates
`xₖ₊₁ = xₖ + sₖ`; once the stopping test fires, the iterate sequence stays constant. -/
structure GaussNewtonIteration
    (J : Point → JacobianMatrix) (r : Point → Residual) (x0 : Point) (ε : ℝ) where
  x : ℕ → Point
  step : ℕ → Point
  x_zero : x 0 = x0
  step_solves_normalEquation (k : ℕ) (hActive : ε < ‖gaussNewtonGradient J r (x k)‖) :
    (((J (x k))ᵀ * J (x k)) : MatrixN).toEuclideanLin (step k) =
      -gaussNewtonGradient J r (x k)
  next_eq_of_active (k : ℕ) (hActive : ε < ‖gaussNewtonGradient J r (x k)‖) :
    x (k + 1) = x k + step k
  next_eq_of_terminated (k : ℕ) (hTerm : ‖gaussNewtonGradient J r (x k)‖ ≤ ε) :
    x (k + 1) = x k

namespace GaussNewtonIteration

variable {J : Point → JacobianMatrix} {r : Point → Residual} {x0 : Point} {ε : ℝ}

/-- A Gauss-Newton iteration coerces to its sequence of iterates. -/
instance : CoeFun (GaussNewtonIteration J r x0 ε) (fun _ ↦ ℕ → Point) where
  coe iter := iter.x

/-- Evaluating a Gauss-Newton iteration as a function returns its iterate sequence. -/
theorem coe_apply (iter : GaussNewtonIteration J r x0 ε) (k : ℕ) : iter k = iter.x k := rfl

/-- The algorithm terminates at stage `k` when the Gauss-Newton gradient norm is at most `ε`. -/
def terminatedAt (iter : GaussNewtonIteration J r x0 ε) (k : ℕ) : Prop :=
  ‖gaussNewtonGradient J r (iter k)‖ ≤ ε

/-- The algorithm is active at stage `k` when the stopping test has not yet fired. -/
def activeAt (iter : GaussNewtonIteration J r x0 ε) (k : ℕ) : Prop :=
  ε < ‖gaussNewtonGradient J r (iter k)‖

/-- Expanding `terminatedAt` gives the source stopping inequality. -/
theorem terminatedAt_iff (iter : GaussNewtonIteration J r x0 ε) (k : ℕ) :
    terminatedAt iter k ↔ ‖gaussNewtonGradient J r (iter k)‖ ≤ ε :=
  Iff.rfl

/-- Expanding `activeAt` gives the active-iteration inequality used in the update clauses. -/
theorem activeAt_iff (iter : GaussNewtonIteration J r x0 ε) (k : ℕ) :
    activeAt iter k ↔ ε < ‖gaussNewtonGradient J r (iter k)‖ :=
  Iff.rfl

/-- The active and terminated predicates are complementary reformulations of the same stopping
test. -/
theorem activeAt_iff_not_terminatedAt
    (iter : GaussNewtonIteration J r x0 ε) (k : ℕ) :
    iter.activeAt k ↔ ¬ iter.terminatedAt k := by
  rw [activeAt_iff, terminatedAt_iff]
  constructor
  · exact not_le_of_gt
  · exact lt_of_not_ge

/-- Once the stopping test fires, the next iterate is unchanged. -/
theorem next_eq_of_terminatedAt
    (iter : GaussNewtonIteration J r x0 ε) (k : ℕ) (hTerm : iter.terminatedAt k) :
    iter (k + 1) = iter k :=
  iter.next_eq_of_terminated k hTerm

/-- Termination at stage `k` forces termination at stage `k + 1`. -/
theorem terminatedAt_succ
    (iter : GaussNewtonIteration J r x0 ε) {k : ℕ} (hTerm : iter.terminatedAt k) :
    iter.terminatedAt (k + 1) := by
  simpa [terminatedAt, iter.next_eq_of_terminated k hTerm] using hTerm

/-- After termination, the iterate sequence stays constant on the whole tail. -/
theorem eq_of_terminated_le
    (iter : GaussNewtonIteration J r x0 ε) {k t : ℕ}
    (hTerm : iter.terminatedAt k) (hkt : k ≤ t) :
    iter t = iter k := by
  induction hkt with
  | refl =>
      rfl
  | @step t hkt ih =>
      have hTerm_t : iter.terminatedAt t := by
        rw [terminatedAt, ih]
        exact hTerm
      calc
        iter (t + 1) = iter t := iter.next_eq_of_terminated t hTerm_t
        _ = iter k := ih

/-- `iter.IsTerminalIndex k` means that the source stopping test has fired at stage `k`, and the
iterate sequence stays constant afterwards. -/
def IsTerminalIndex (iter : GaussNewtonIteration J r x0 ε) (k : ℕ) : Prop :=
  iter.terminatedAt k ∧ ∀ t : ℕ, k ≤ t → iter t = iter k

/-- Unfolding `iter.IsTerminalIndex k` gives the stopping test together with the constant tail. -/
theorem isTerminalIndex_iff
    (iter : GaussNewtonIteration J r x0 ε) (k : ℕ) :
    iter.IsTerminalIndex k ↔ iter.terminatedAt k ∧ ∀ t : ℕ, k ≤ t → iter t = iter k :=
  Iff.rfl

/-- Any terminated stage is automatically a terminal index because the iteration stabilizes
after stopping. -/
theorem isTerminalIndex_of_terminated
    (iter : GaussNewtonIteration J r x0 ε) {k : ℕ} (hTerm : iter.terminatedAt k) :
    iter.IsTerminalIndex k := by
  exact ⟨hTerm, fun t hkt ↦ iter.eq_of_terminated_le hTerm hkt⟩

/-- The active-stage data consist exactly of the Gauss-Newton normal equation and the iterate
update. -/
theorem stepSpec
    (iter : GaussNewtonIteration J r x0 ε) (k : ℕ) (hActive : iter.activeAt k) :
    (((J (iter k))ᵀ * J (iter k)) : MatrixN).toEuclideanLin (iter.step k) =
        -gaussNewtonGradient J r (iter k) ∧
      iter (k + 1) = iter k + iter.step k := by
  exact ⟨iter.step_solves_normalEquation k hActive, iter.next_eq_of_active k hActive⟩

end GaussNewtonIteration

end
