/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Bounds.Basic

universe u

-- Source/core/bridge triage:
-- * source-facing: a successful backtracking line-search step, consisting of a
--   backtracking trial-step sequence together with its first accepted index;
-- * core/canonical: `IsLeast` on the acceptance set of trial indices;
-- * bridge/view: the trial-point map `n ↦ x + α n • d`.

/-- Chapter02 Definition 2.5-extra-4: a backtracking trial-step sequence starts from
`1`, stays positive, and strictly decreases at each backtracking step. -/
class IsBacktrackingStepSequence (α : ℕ → ℝ) : Prop where
  start : α 0 = 1
  step_pos (n : ℕ) : 0 < α n
  strictReduction (n : ℕ) : α (n + 1) < α n

/-- The predicate `IsBacktrackingStepSequence` is proposition-valued, hence
subsingleton. -/
instance isBacktrackingStepSequenceSubsingleton (α : ℕ → ℝ) :
    Subsingleton (IsBacktrackingStepSequence α) := inferInstance

/-- Unfolding specification for `IsBacktrackingStepSequence`. -/
theorem isBacktrackingStepSequence_iff (α : ℕ → ℝ) :
    IsBacktrackingStepSequence α ↔
      α 0 = 1 ∧
        (∀ n, 0 < α n) ∧
        (∀ n, α (n + 1) < α n) := by
  constructor
  · intro h
    exact ⟨h.start, h.step_pos, h.strictReduction⟩
  · rintro ⟨hStart, hPos, hReduction⟩
    exact ⟨hStart, hPos, hReduction⟩

section

variable {E : Type u} [Add E] [SMul ℝ E]

/-- The `n`-th backtracking trial point along the search ray from `x` in direction `d`
with trial step sequence `α` is `x + α n • d`. -/
def backtrackingTrialPoint (x d : E) (α : ℕ → ℝ) (n : ℕ) : E :=
  x + α n • d

/-- Evaluating `backtrackingTrialPoint x d α` at `n` gives `x + α n • d`. -/
theorem backtrackingTrialPoint_apply (x d : E) (α : ℕ → ℝ) (n : ℕ) :
    backtrackingTrialPoint x d α n = x + α n • d :=
  rfl

/-- Chapter02 Definition 2.5-extra-4: a successful backtracking line-search step consists
of a backtracking trial-step sequence together with the first index whose trial is
acceptable. -/
class IsBacktrackingLineSearchStep
    (acceptable : ℝ → E → Prop) (x d : E) (α : ℕ → ℝ) (m : ℕ) : Prop extends
    IsBacktrackingStepSequence α where
  acceptedIndex_isLeast :
    IsLeast {n : ℕ | acceptable (α n) (backtrackingTrialPoint x d α n)} m

/-- Backtracking line-search step witnesses are proposition-valued, hence subsingleton. -/
instance isBacktrackingLineSearchStepSubsingleton
    (acceptable : ℝ → E → Prop) (x d : E) (α : ℕ → ℝ) (m : ℕ) :
    Subsingleton (IsBacktrackingLineSearchStep acceptable x d α m) := inferInstance

/-- Unfolding `IsBacktrackingLineSearchStep` recovers the primitive backtracking sequence
data together with the least accepted trial index. -/
theorem isBacktrackingLineSearchStep_iff
    (acceptable : ℝ → E → Prop) (x d : E) (α : ℕ → ℝ) (m : ℕ) :
    IsBacktrackingLineSearchStep acceptable x d α m ↔
      IsBacktrackingStepSequence α ∧
        IsLeast {n : ℕ | acceptable (α n) (backtrackingTrialPoint x d α n)} m := by
  constructor
  · intro h
    exact ⟨h.toIsBacktrackingStepSequence, h.acceptedIndex_isLeast⟩
  · rintro ⟨hSequence, hAccepted⟩
    exact
      { toIsBacktrackingStepSequence := hSequence
        acceptedIndex_isLeast := hAccepted }

namespace IsLeast

/-- The least acceptable backtracking index satisfies the acceptability test at its
own trial point. -/
theorem backtrackingAccepts
    {acceptable : ℝ → E → Prop} {x d : E} {α : ℕ → ℝ} {m : ℕ}
    (h :
      IsLeast {n : ℕ | acceptable (α n) (backtrackingTrialPoint x d α n)} m) :
    acceptable (α m) (backtrackingTrialPoint x d α m) :=
  h.1

/-- No earlier index than the least acceptable backtracking index satisfies the same
acceptability test. -/
theorem not_backtrackingAccepts_of_lt
    {acceptable : ℝ → E → Prop} {x d : E} {α : ℕ → ℝ} {m n : ℕ}
    (h :
      IsLeast {k : ℕ | acceptable (α k) (backtrackingTrialPoint x d α k)} m)
    (hn : n < m) :
    ¬ acceptable (α n) (backtrackingTrialPoint x d α n) := by
  intro hAccepts
  exact Nat.not_lt_of_ge (h.2 hAccepts) hn

end IsLeast

/-- Unfolding the canonical least-index owner for backtracking line search recovers the
accepted trial together with the failure of every earlier trial. -/
theorem isLeast_backtrackingAccepts_iff
    (acceptable : ℝ → E → Prop) (x d : E) (α : ℕ → ℝ) (m : ℕ) :
    IsLeast {n : ℕ | acceptable (α n) (backtrackingTrialPoint x d α n)} m ↔
      acceptable (α m) (backtrackingTrialPoint x d α m) ∧
        ∀ n < m, ¬ acceptable (α n) (backtrackingTrialPoint x d α n) := by
  constructor
  · intro h
    exact ⟨h.backtrackingAccepts, fun n hn ↦ h.not_backtrackingAccepts_of_lt hn⟩
  · rintro ⟨hAccepts, hRejectedBefore⟩
    refine ⟨hAccepts, ?_⟩
    intro n hn
    exact le_of_not_gt (fun hnm ↦ hRejectedBefore n hnm hn)

namespace IsBacktrackingLineSearchStep

/-- The accepted backtracking trial is positive. -/
theorem acceptedStep_pos
    {acceptable : ℝ → E → Prop} {x d : E} {α : ℕ → ℝ} {m : ℕ}
    (h : IsBacktrackingLineSearchStep acceptable x d α m) :
    0 < α m :=
  h.step_pos m

/-- The accepted index of a backtracking line-search step satisfies the acceptability test. -/
theorem accepts
    {acceptable : ℝ → E → Prop} {x d : E} {α : ℕ → ℝ} {m : ℕ}
    (h : IsBacktrackingLineSearchStep acceptable x d α m) :
    acceptable (α m) (backtrackingTrialPoint x d α m) :=
  h.acceptedIndex_isLeast.backtrackingAccepts

/-- No earlier trial than the accepted index satisfies the acceptability test. -/
theorem not_accepts_of_lt
    {acceptable : ℝ → E → Prop} {x d : E} {α : ℕ → ℝ} {m n : ℕ}
    (h : IsBacktrackingLineSearchStep acceptable x d α m) (hn : n < m) :
    ¬ acceptable (α n) (backtrackingTrialPoint x d α n) :=
  h.acceptedIndex_isLeast.not_backtrackingAccepts_of_lt hn

/-- Any acceptable trial index is at least the accepted index. -/
theorem le_of_accepts
    {acceptable : ℝ → E → Prop} {x d : E} {α : ℕ → ℝ} {m n : ℕ}
    (h : IsBacktrackingLineSearchStep acceptable x d α m)
    (hn : acceptable (α n) (backtrackingTrialPoint x d α n)) :
    m ≤ n :=
  h.acceptedIndex_isLeast.2 hn

/-- The accepted index carried by `h` is the least accepted trial index. -/
theorem isLeastAcceptedIndex
    {acceptable : ℝ → E → Prop} {x d : E} {α : ℕ → ℝ} {m : ℕ}
    (h : IsBacktrackingLineSearchStep acceptable x d α m) :
    IsLeast {n : ℕ | acceptable (α n) (backtrackingTrialPoint x d α n)} m :=
  h.acceptedIndex_isLeast

end IsBacktrackingLineSearchStep

/-- Source-facing expansion of `IsBacktrackingLineSearchStep`: the trial sequence is a
backtracking sequence, the accepted trial passes the test, and every earlier trial fails. -/
theorem isBacktrackingLineSearchStep_iff_accepts_rejects
    (acceptable : ℝ → E → Prop) (x d : E) (α : ℕ → ℝ) (m : ℕ) :
    IsBacktrackingLineSearchStep acceptable x d α m ↔
      IsBacktrackingStepSequence α ∧
        acceptable (α m) (backtrackingTrialPoint x d α m) ∧
        ∀ n < m, ¬ acceptable (α n) (backtrackingTrialPoint x d α n) := by
  constructor
  · intro h
    exact
      ⟨h.toIsBacktrackingStepSequence, h.accepts, fun n hn ↦ h.not_accepts_of_lt hn⟩
  · rintro ⟨hSequence, hAccepts, hRejectedBefore⟩
    refine (isBacktrackingLineSearchStep_iff acceptable x d α m).2 ?_
    exact
      ⟨hSequence, (isLeast_backtrackingAccepts_iff acceptable x d α m).2
        ⟨hAccepts, hRejectedBefore⟩⟩

attribute [instance] IsBacktrackingLineSearchStep.toIsBacktrackingStepSequence

end
