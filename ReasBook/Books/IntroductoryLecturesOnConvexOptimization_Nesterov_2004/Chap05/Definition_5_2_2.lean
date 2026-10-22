/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_2_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Definition 5.2.2 lies in the Chapter 5 self-concordant Newton-strategy domain.

Sampled owner declarations:
* `SelfConcordantNewtonVariant` in `Definition_5_2_1`, the chapter owner for the textbook Newton
  variants;
* `selfConcordantNewtonNextPoint` in `Theorem_5_2_2`, the downstream one-step owner specialized by
  a Newton variant.

Best owner abstraction:
* source-facing: the two-stage strategy choosing between the textbook damped and intermediate
  variants;
* core/canonical: `SelfConcordantNewtonVariant`;
* bridge/view: the threshold test `1 / (2 M_f) ≤ λ` selecting one of those two canonical
  variants.

Primitive data:
* the positive self-concordance parameter `M_f`;
* the current Newton decrement `λ`.

Derived API:
* the chosen canonical variant `selfConcordantTwoStageStrategy Mf decrement`;
* the branch characterizations for `.damped` and `.intermediate`.

This file keeps the source-facing two-stage choice, reuses the chapter owner
`SelfConcordantNewtonVariant`, and deletes the one-off threshold wrapper in favor of the direct
textbook inequality `1 / (2 M_f) ≤ λ` on the canonical positive-parameter surface `Mf : NNRealˣ`.
-/

/-- Definition 5.2.2: the two-stage strategy for self-concordant minimization chooses the damped
Newton method when the current Newton decrement is at least `1 / (2 M_f)`, and otherwise chooses
the intermediate method from Definition 5.2.1(C), viewed as the canonical Newton variant. -/
def selfConcordantTwoStageStrategy
    (Mf : NNRealˣ) (decrement : ℝ) : SelfConcordantNewtonVariant :=
  if 1 / (2 * (Mf : ℝ)) ≤ decrement then
    .damped
  else
    .intermediate

-- Proof sketch: unfold `selfConcordantTwoStageStrategy`; the result is definitionally the
-- displayed `if` expression selecting between the two canonical variants.
/-- Expanding `selfConcordantTwoStageStrategy Mf decrement` gives the textbook two-stage
branching rule. -/
@[simp] theorem selfConcordantTwoStageStrategy_def
    (Mf : NNRealˣ) (decrement : ℝ) :
    selfConcordantTwoStageStrategy Mf decrement =
      if 1 / (2 * (Mf : ℝ)) ≤ decrement then
        .damped
      else
        .intermediate := rfl

-- Proof sketch: split on the threshold inequality defining
-- `selfConcordantTwoStageStrategy`; in the two branches the strategy is definitionally
-- `.damped` or `.intermediate`.
/-- The two-stage strategy always returns one of the two textbook stages: the damped or the
intermediate Newton variant. -/
theorem selfConcordantTwoStageStrategy_spec
    (Mf : NNRealˣ) (decrement : ℝ) :
    selfConcordantTwoStageStrategy Mf decrement = .damped ∨
      selfConcordantTwoStageStrategy Mf decrement = .intermediate := by
  unfold selfConcordantTwoStageStrategy
  split_ifs <;> simp

-- Proof sketch: unfold `selfConcordantTwoStageStrategy`; the `if` branch is exactly the
-- first-stage condition `1 / (2 M_f) ≤ λ`.
/-- The two-stage strategy selects the damped Newton method exactly on the first-stage branch
`1 / (2 M_f) ≤ λ`. -/
@[simp] theorem selfConcordantTwoStageStrategy_eq_damped_iff
    (Mf : NNRealˣ) (decrement : ℝ) :
    selfConcordantTwoStageStrategy Mf decrement = .damped ↔
      1 / (2 * (Mf : ℝ)) ≤ decrement := by
  unfold selfConcordantTwoStageStrategy
  split_ifs with h
  · constructor
    · intro _
      exact h
    · intro _
      rfl
  · constructor
    · intro hs
      cases hs
    · intro hs
      exact (h hs).elim

-- Proof sketch: unfold `selfConcordantTwoStageStrategy`; the negated `if` branch is
-- equivalent to the second-stage inequality `λ < 1 / (2 M_f)`.
/-- The two-stage strategy selects the intermediate method exactly on the second-stage
branch `λ < 1 / (2 M_f)`. -/
@[simp] theorem selfConcordantTwoStageStrategy_eq_intermediate_iff
    (Mf : NNRealˣ) (decrement : ℝ) :
    selfConcordantTwoStageStrategy Mf decrement = .intermediate ↔
      decrement < 1 / (2 * (Mf : ℝ)) := by
  unfold selfConcordantTwoStageStrategy
  split_ifs with h
  · constructor
    · intro hs
      cases hs
    · intro hs
      exact (not_lt.mpr h hs).elim
  · constructor
    · intro _
      exact lt_of_not_ge h
    · intro _
      rfl

-- Proof sketch: unfold `selfConcordantTwoStageStrategy`; both branches are either `.damped`
-- or `.intermediate`, so the output cannot be `.standard`.
/-- The two-stage strategy never selects the standard Newton variant. -/
@[simp] theorem selfConcordantTwoStageStrategy_ne_standard
    (Mf : NNRealˣ) (decrement : ℝ) :
    selfConcordantTwoStageStrategy Mf decrement ≠ .standard := by
  unfold selfConcordantTwoStageStrategy
  split_ifs <;> decide

end
