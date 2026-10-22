/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {α : Type u} [Semiring α] [Preorder α]

/-
Definition 7.1 lies in the chapter's relative-accuracy / approximate-solution domain.

Sampled owner-style declarations:
* `SetConstrainedMinimizationProblem.IsApproximateMinimizer` in
  `Chap01/Definition_1_3_7`, the project owner for additive approximate minimizers on a feasible
  set;
* `IsApproximateSolution` in `Chap03/Definition_3_34`, where the primitive data are reduced to a
  scalar objective-gap predicate relative to a chosen minimizer;
* `IsRelativeDeltaApproximateSolutionOn` in `Chap07/Definition_7_92`, where the optimization-layer
  relative notion is owned by a direct `Prop`, not by a typeclass packaging of its fields;
* `HasMixedAccuracy` in `Chap07/Definition_7_89`, which shows the local chapter style for small
  accuracy predicates.

Best owner abstraction:
* source-facing: the statement that an attained objective value is a relative-`δ` approximation of
  a positive optimal value;
* core/canonical: a scalar `Prop` on `(fStar, δ, fBar)` over the semiring / preorder layer;
* bridge/view: evaluation at `f xBar` for a real-valued objective.

Primitive data:
* the positive optimal value `fStar`;
* the relative-accuracy parameter `delta`;
* the attained value `fBar`.

Derived API:
* the source-facing specialization to `f xBar`.

The previous file used a typeclass wrapper and a `Fact` instance for four scalar inequalities.
Those inequalities are the mathematics, so the owner surface should be the direct scalar `Prop`.
Because the notion only uses order, `0`, `1`, addition, and multiplication, the scalar owner
should live directly over the semiring / preorder layer; the stronger linear-order and
strict-positivity monotonicity assumptions are needed only for the derived nonnegativity
consequence.
The objective-evaluation view remains a thin real-valued bridge theorem.
-/

/-- Definition 7.1: a value `fBar` has relative accuracy `delta` with respect to a positive
optimal value `fStar` when it lies between `fStar` and `(1 + delta) * fStar`. The nonnegativity
of `delta` is then forced by these bounds together with `0 < fStar`. -/
def IsRelativeAccuracy (fStar delta fBar : α) : Prop :=
  0 < fStar ∧ fStar ≤ fBar ∧ fBar ≤ (1 + delta) * fStar

end

/-- Unfolding `IsRelativeAccuracy fStar delta fBar` gives positivity of `fStar` together with the
two-sided relative bound on `fBar`. The nonnegativity of `delta` is derived separately from these
inequalities. -/
theorem isRelativeAccuracy_iff {α : Type u} [Semiring α] [Preorder α]
    (fStar delta fBar : α) :
    IsRelativeAccuracy fStar delta fBar ↔
      0 < fStar ∧ fStar ≤ fBar ∧ fBar ≤ (1 + delta) * fStar :=
  Iff.rfl

section

variable {α : Type u} [Semiring α] [LinearOrder α] [IsOrderedCancelAddMonoid α]
  [MulPosStrictMono α]

/-- Relative accuracy forces the relative-error parameter to be nonnegative. -/
theorem isRelativeAccuracy_delta_nonneg {fStar delta fBar : α}
    (h : IsRelativeAccuracy fStar delta fBar) :
    0 ≤ delta := by
  rcases h with ⟨hfStar_pos, hfStar_le_fBar, hfBar_le⟩
  have hbound : fStar ≤ (1 + delta) * fStar :=
    hfStar_le_fBar.trans hfBar_le
  have hdelta_mul : 0 ≤ delta * fStar := by
    have hsum : fStar ≤ fStar + delta * fStar := by
      simpa [add_mul, one_mul, add_assoc, add_left_comm, add_comm] using hbound
    exact (le_add_iff_nonneg_right fStar).1 hsum
  exact nonneg_of_mul_nonneg_left hdelta_mul hfStar_pos

end

/-- Source-facing form of Definition 7.1: the objective value at `xBar` has relative accuracy
`delta` with respect to `fStar` exactly when it satisfies the displayed positivity and two-sided
relative-error bounds. The condition `0 ≤ delta` is a derived consequence, not primitive data. -/
theorem isRelativeAccuracy_objectiveValue_iff
    {X : Type u} (f : X → ℝ) (fStar delta : ℝ) (xBar : X) :
    IsRelativeAccuracy fStar delta (f xBar) ↔
      0 < fStar ∧
        fStar ≤ f xBar ∧
          f xBar ≤ (1 + delta) * fStar :=
  Iff.rfl
