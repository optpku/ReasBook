/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_2_1

section Chapter11Definition111Extra3

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

-- Layer triage:
-- * source-facing: `FeasiblePointExactLineSearch`
-- * core/canonical reused from Chapter 8: `IsFeasibleDirectionAt`
-- * bridge/view: `feasiblePointExactLineSearch_iff`

-- Semantic recall: Chapter 8 already owns the small-segment feasible-direction predicate.
-- This file keeps the source-facing exact line-search notion and only adds the chosen positive
-- feasible step and the canonical `IsMinOn` minimizer condition.

/-- The positive feasible step sizes along the ray `x + α • d`. -/
def feasiblePointLineSearchDomain (x d : E) (X : Set E) : Set ℝ :=
  {α | 0 < α ∧ x + α • d ∈ X}

/-- Membership in `feasiblePointLineSearchDomain x d X` is exactly positivity together with
feasibility of the trial point. -/
theorem mem_feasiblePointLineSearchDomain_iff
    (x d : E) (X : Set E) (α : ℝ) :
    α ∈ feasiblePointLineSearchDomain x d X ↔
      0 < α ∧ x + α • d ∈ X :=
  Iff.rfl

/-- Chapter11 Definition 11.1-extra-3: for a feasible point `x ∈ X` and a feasible direction
`d ∈ FD(x, X)`, a feasible point exact line search step is a positive step `α` such that
`f (x + α • d)` is minimal among all positive feasible steps. -/
class FeasiblePointExactLineSearch
    (f : E → ℝ) (X : Set E) (x d : E) (α : ℝ) : Prop
    extends IsFeasibleDirectionAt X x d where
  alpha_mem : α ∈ feasiblePointLineSearchDomain x d X
  isMinOn :
    IsMinOn (fun a : ℝ ↦ f (x + a • d))
      (feasiblePointLineSearchDomain x d X) α

/-- `FeasiblePointExactLineSearch f X x d α` is a proposition. -/
instance instSubsingletonFeasiblePointExactLineSearch
    (f : E → ℝ) (X : Set E) (x d : E) (α : ℝ) :
    Subsingleton (FeasiblePointExactLineSearch f X x d α) :=
  inferInstance

/-- Unfolding formula for `FeasiblePointExactLineSearch`. -/
theorem feasiblePointExactLineSearch_iff
    (f : E → ℝ) (X : Set E) (x d : E) (α : ℝ) :
    FeasiblePointExactLineSearch f X x d α ↔
      IsFeasibleDirectionAt X x d ∧
        α ∈ feasiblePointLineSearchDomain x d X ∧
          IsMinOn (fun a : ℝ ↦ f (x + a • d))
            (feasiblePointLineSearchDomain x d X) α := by
  constructor
  · intro h
    exact ⟨h.toIsFeasibleDirectionAt, h.alpha_mem, h.isMinOn⟩
  · rintro ⟨hd, hα, hmin⟩
    exact { toIsFeasibleDirectionAt := hd, alpha_mem := hα, isMinOn := hmin }

/-- A feasible point exact line-search step is based at a feasible point. -/
theorem FeasiblePointExactLineSearch.mem_base
    {f : E → ℝ} {X : Set E} {x d : E} {α : ℝ}
    (h : FeasiblePointExactLineSearch f X x d α) :
    x ∈ X :=
  h.toIsFeasibleDirectionAt.mem

/-- A feasible point exact line-search step is positive. -/
theorem FeasiblePointExactLineSearch.pos
    {f : E → ℝ} {X : Set E} {x d : E} {α : ℝ}
    (h : FeasiblePointExactLineSearch f X x d α) :
    0 < α :=
  (mem_feasiblePointLineSearchDomain_iff x d X α).mp h.alpha_mem |>.1

/-- The trial point reached by a feasible point exact line-search step remains feasible. -/
theorem FeasiblePointExactLineSearch.add_smul_mem
    {f : E → ℝ} {X : Set E} {x d : E} {α : ℝ}
    (h : FeasiblePointExactLineSearch f X x d α) :
    x + α • d ∈ X :=
  (mem_feasiblePointLineSearchDomain_iff x d X α).mp h.alpha_mem |>.2

#print axioms feasiblePointLineSearchDomain

end Chapter11Definition111Extra3
