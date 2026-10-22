/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {X : Type u} [NormedAddCommGroup X]

local notation "Z" => ℝ × X

open scoped ConstrainedArgmin

/- Proposition 3.48 lies in the chapter's constrained minimization / explicit argmin domain.

Relevant owner-style declarations sampled before refinement:
- `constrainedArgmin` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the chapter
  owner for minimizers of an objective over a feasible set;
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the later package owner built
  from a feasible set and an objective;
- `IsMinOn` and `isMinOn_iff` in mathlib, the canonical pointwise minimizer predicate on a set.

Best owner abstraction:
- source-facing: the explicit Kelley complete-data objective `f(y, x) = max {|y|, ‖x‖²}` and
  feasible set `Q = {(y, x) | y² + ‖x‖² ≤ 1}`;
- core/canonical: the minimizer owner `argmin[Q] f`, with `mem_constrainedArgmin_iff` as the
  atomic membership view;
- bridge/view: the later problem package
  `SetConstrainedMinimizationProblem.mk kelleyCompleteFeasibleSet kelleyCompleteObjective`.

Primitive data:
- the explicit objective `kelleyCompleteObjective`;
- the explicit feasible set `kelleyCompleteFeasibleSet`.

Derived API:
- feasibility and objective-value simplification at the origin;
- the argmin set equality and its atomic membership corollary.

This proposition is therefore kept source-facing on the explicit `f` and `Q`, while exposing its
optimality result through the canonical constrained-argmin owner rather than through any extra
wrapper around the same minimizer set.
-/

/-- The objective `f(y, x) = max {|y|, ‖x‖²}` from the complete-data example for Kelley's
method. -/
def kelleyCompleteObjective (z : Z) : ℝ :=
  max |z.1| (‖z.2‖ ^ (2 : ℕ))

/-- The feasible set `Q = {(y, x) | y² + ‖x‖² ≤ 1}` for the complete-data example. -/
def kelleyCompleteFeasibleSet : Set Z :=
  {z | z.1 ^ (2 : ℕ) + ‖z.2‖ ^ (2 : ℕ) ≤ 1}

/-- Membership in `kelleyCompleteFeasibleSet` is exactly the displayed quadratic constraint
defining the unit ball `Q`. -/
@[simp] theorem mem_kelleyCompleteFeasibleSet_iff
    {z : Z} :
    z ∈ kelleyCompleteFeasibleSet ↔
      z.1 ^ (2 : ℕ) + ‖z.2‖ ^ (2 : ℕ) ≤ 1 :=
  Iff.rfl

/-- The Kelley complete-data objective is nonnegative at every point. -/
theorem kelleyCompleteObjective_nonneg (z : Z) :
    0 ≤ kelleyCompleteObjective z := by
  unfold kelleyCompleteObjective
  positivity

/-- The origin is feasible for the Kelley complete-data unit ball constraint. -/
@[simp] theorem zero_mem_kelleyCompleteFeasibleSet :
    (0 : Z) ∈ kelleyCompleteFeasibleSet := by
  simp [kelleyCompleteFeasibleSet]

/-- Evaluating the complete-data Kelley objective at the origin gives the optimal value candidate
`0`. -/
-- Proof sketch: unfold `kelleyCompleteObjective` and simplify `|0|`, `‖0‖`, and the maximum
-- of two zero terms.
@[simp] theorem kelleyCompleteObjective_zero :
    kelleyCompleteObjective (0 : Z) = 0 := by
  simp [kelleyCompleteObjective]

/-- Proposition 3.48: for the problem
`min {f(y, x) | (y, x) ∈ Q}` with
`f(y, x) = max {|y|, ‖x‖²}` and `Q = {(y, x) | y² + ‖x‖² ≤ 1}`,
the unique optimal solution is the origin, i.e. the minimizer set is `{(0, 0)}`. Specializing
`X = EuclideanSpace ℝ (Fin n)` recovers the textbook `ℝ × ℝⁿ` instance. -/
-- Proof sketch: first show every feasible point has nonnegative objective value, while the origin
-- is feasible and attains value `0`. Hence the origin is a minimizer. If another feasible point
-- were also minimizing, its objective value would be `0`, forcing both `|y| = 0` and `‖x‖² = 0`,
-- so `y = 0` and `x = 0`.
theorem kelleyCompleteArgmin_eq_singleton_origin :
    (argmin[kelleyCompleteFeasibleSet] kelleyCompleteObjective : Set Z) =
      ({(0 : Z)} : Set Z) := by
  ext z
  rw [mem_constrainedArgmin_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hz_feasible, hz_min⟩
    rw [isMinOn_iff] at hz_min
    have hz_nonneg : 0 ≤ kelleyCompleteObjective z :=
      kelleyCompleteObjective_nonneg z
    have hzero_feasible : (0 : Z) ∈ kelleyCompleteFeasibleSet := by simp
    have hz_le_zero : kelleyCompleteObjective z ≤ 0 := by
      simpa [kelleyCompleteObjective_zero] using hz_min (0 : Z) hzero_feasible
    have hy_abs_le_zero : |z.1| ≤ 0 := by
      exact (le_max_left |z.1| (‖z.2‖ ^ (2 : ℕ))).trans hz_le_zero
    have hy_zero : z.1 = 0 := by
      exact abs_eq_zero.mp (le_antisymm hy_abs_le_zero (abs_nonneg _))
    have hx_sq_le_zero : ‖z.2‖ ^ (2 : ℕ) ≤ 0 := by
      exact (le_max_right |z.1| (‖z.2‖ ^ (2 : ℕ))).trans hz_le_zero
    have hx_sq_eq_zero : ‖z.2‖ ^ (2 : ℕ) = 0 := by
      exact le_antisymm hx_sq_le_zero <| by positivity
    have hx_zero : z.2 = 0 := by
      apply norm_eq_zero.mp
      exact sq_eq_zero_iff.mp <| by simpa using hx_sq_eq_zero
    exact Prod.ext hy_zero hx_zero
  · intro hz
    subst hz
    refine ⟨?_, ?_⟩
    · simp
    · rw [isMinOn_iff]
      intro w hw
      simpa using kelleyCompleteObjective_nonneg w

/-- Membership in the Kelley complete-data argmin set is exactly the assertion that the point is
the origin. -/
@[simp] theorem mem_kelleyCompleteArgmin_iff
    {z : Z} :
    z ∈ (argmin[kelleyCompleteFeasibleSet] kelleyCompleteObjective : Set Z) ↔ z = 0 := by
  simp [kelleyCompleteArgmin_eq_singleton_origin]
