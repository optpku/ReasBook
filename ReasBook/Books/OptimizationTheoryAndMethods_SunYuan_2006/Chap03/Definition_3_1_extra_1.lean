/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_4_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_1_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_2_extra_1

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
Chapter03 Definition 3.1-extra-1 (1): the source descent-direction notion is already owned by
Chapter01 Definition 1.4.3 as `IsDescentDirectionAt`.
-/
#check IsDescentDirectionAt

/-- Chapter03 Definition 3.1-extra-1 (2): the steepest descent direction is the negative
gradient. -/
noncomputable abbrev steepestDescentDirection (f : E → ℝ) (x : E) : E :=
  -gradient f x

/-- The line-search objective along the canonical steepest-descent ray from `x`. -/
noncomputable abbrev steepestDescentObjective (f : E → ℝ) (x : E) : ℝ → ℝ :=
  lineSearchObjective f x (steepestDescentDirection f x)

/-- The steepest descent direction is a descent direction whenever the gradient is nonzero. -/
theorem steepestDescentDirection_isDescentDirection (f : E → ℝ) (x : E)
    (hg : gradient f x ≠ 0) :
    IsDescentDirectionAt f x (steepestDescentDirection f x) := by
  rw [isDescentDirectionAt_iff]
  have hsq : 0 < ‖gradient f x‖ ^ (2 : ℕ) := by
    exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hg)
  have hneg : -(‖gradient f x‖ ^ (2 : ℕ)) < 0 := by
    linarith
  calc
    inner ℝ (gradient f x) (steepestDescentDirection f x) = -(‖gradient f x‖ ^ (2 : ℕ)) := by
      rw [steepestDescentDirection, inner_neg_right, real_inner_self_eq_norm_sq]
    _ < 0 := hneg

/-- Chapter03 Definition 3.1-extra-1 (3): one steepest descent update moves from `x` by the
step length `α` along the steepest descent direction. -/
noncomputable abbrev steepestDescentStep (f : E → ℝ) (x : E) (α : ℝ) : E :=
  x + α • steepestDescentDirection f x

/-- The steepest descent update has the form `x - α • gradient f x`. -/
theorem steepestDescentStep_eq (f : E → ℝ) (x : E) (α : ℝ) :
    steepestDescentStep f x α = x - α • gradient f x := by
  simp [steepestDescentStep, steepestDescentDirection, sub_eq_add_neg]

/-- A steepest-descent sequence uses exact line search along the canonical steepest-descent ray
and the canonical update at every step. -/
def IsSteepestDescentSequence (f : E → ℝ) (x : ℕ → E) (α : ℕ → ℝ) : Prop :=
  ∀ k : ℕ,
    IsExactLineSearchStepOnNonnegativeRay
        f
        (x k)
        (steepestDescentDirection f (x k))
        (α k) ∧
      x (k + 1) = steepestDescentStep f (x k) (α k)

/-- Unfolding lemma for `IsSteepestDescentSequence`. -/
theorem isSteepestDescentSequence_iff (f : E → ℝ) (x : ℕ → E) (α : ℕ → ℝ) :
    IsSteepestDescentSequence f x α ↔
      ∀ k : ℕ,
        IsExactLineSearchStepOnNonnegativeRay
            f
            (x k)
            (steepestDescentDirection f (x k))
            (α k) ∧
          x (k + 1) = steepestDescentStep f (x k) (α k) :=
  Iff.rfl

/-- A steepest-descent sequence performs exact line search along the canonical
steepest-descent ray at each step. -/
theorem IsSteepestDescentSequence.exactLineSearch
    {f : E → ℝ} {x : ℕ → E} {α : ℕ → ℝ}
    (hSeq : IsSteepestDescentSequence f x α) (k : ℕ) :
    IsExactLineSearchStepOnNonnegativeRay
      f
      (x k)
      (steepestDescentDirection f (x k))
      (α k) :=
  (hSeq k).1

/-- A steepest-descent sequence uses the canonical iterate update at each step. -/
theorem IsSteepestDescentSequence.update
    {f : E → ℝ} {x : ℕ → E} {α : ℕ → ℝ}
    (hSeq : IsSteepestDescentSequence f x α) (k : ℕ) :
    x (k + 1) = steepestDescentStep f (x k) (α k) :=
  (hSeq k).2
