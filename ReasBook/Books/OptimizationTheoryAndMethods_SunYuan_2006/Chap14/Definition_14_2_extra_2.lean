/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance

noncomputable section

open Metric

universe u

section

variable {X : Type u} [NormedAddCommGroup X]

-- Semantic recall: `Metric.infDist` is the canonical distance-to-set API, with lower-bound
-- characterization `Metric.isGLB_infDist`, and local Chapter 10 precedent records penalty
-- objectives as explicit definitions with companion `_apply` theorems.

/-- Chapter14 Definition 14.2-extra-2: for an objective `f`, feasible region `Y`, and penalty
parameter `σ`, the associated nonsmooth unconstrained penalty objective is
`x ↦ f x + σ * infDist x Y`, where `infDist x Y` is the canonical distance from `x` to `Y`. -/
def nonsmoothPenaltyObjective (f : X → ℝ) (Y : Set X) (σ : ℝ) : X → ℝ :=
  fun x ↦ f x + σ * infDist x Y

/-- Evaluating `nonsmoothPenaltyObjective f Y σ` gives the penalized objective
`f x + σ * infDist x Y`. -/
theorem nonsmoothPenaltyObjective_apply
    (f : X → ℝ) (Y : Set X) (σ : ℝ) (x : X) :
    nonsmoothPenaltyObjective f Y σ x = f x + σ * infDist x Y := rfl

/-- If `x ∈ Y`, then the feasible-point penalty term vanishes, so the penalized objective agrees
with the original objective at `x`. -/
theorem nonsmoothPenaltyObjective_eq_objective_of_mem
    (f : X → ℝ) (Y : Set X) (σ : ℝ) {x : X} (hx : x ∈ Y) :
    nonsmoothPenaltyObjective f Y σ x = f x := by
  rw [nonsmoothPenaltyObjective_apply, infDist_zero_of_mem hx, mul_zero, add_zero]

#print axioms nonsmoothPenaltyObjective

end
