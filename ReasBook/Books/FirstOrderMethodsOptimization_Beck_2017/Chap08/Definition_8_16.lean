/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open scoped BigOperators

section

variable {ι : Type w} [Fintype ι] {E : Type u} {α : Type v} [AddCommMonoid α]

/- Definition 8.16 is `source-facing`: the textbook introduces the constrained finite-sum model
`min {∑ᵢ fᵢ(x) : x ∈ C}` used by the incremental projected subgradient method. The genuinely new
mathematical object here is the aggregate objective `x ↦ ∑ i, f i x`, while the optimization
viewpoint is canonically expressed in mathlib through `IsMinOn` for the chosen feasible set `C`.
The public owner is therefore the aggregate objective, with a companion bridge to the minimization
predicate. -/

/-- Definition 8.16: the incremental projected subgradient problem uses the aggregate objective
obtained by summing the component functions `f i`. -/
def finite_sum_objective (f : ι → E → α) : E → α :=
  fun x ↦ ∑ i, f i x

-- Proof sketch: unfold `finite_sum_objective`; evaluation at `x` is definitionally the finite sum
-- of the component objective values `f i x`.
/-- Evaluating the finite-sum objective at `x` gives the sum of the component values `f i x`. -/
@[simp] theorem finite_sum_objective_apply (f : ι → E → α) (x : E) :
    finite_sum_objective f x = ∑ i, f i x := by
  -- Evaluating the aggregate objective is exactly its defining finite sum.
  rfl

end

section

variable {ι : Type w} [Fintype ι] {E : Type u} {α : Type v} [AddCommMonoid α] [Preorder α]

-- Proof sketch: unfold `finite_sum_objective`; this turns the displayed `IsMinOn` statement into
-- the same minimization predicate for the explicit pointwise sum `fun y ↦ ∑ i, f i y`.
/-- Minimizing the finite-sum objective on `C` is exactly minimizing the explicit sum
`x ↦ ∑ i, f i x` on `C`. -/
theorem isMinOn_finite_sum_objective_iff
    {f : ι → E → α} {C : Set E} {x : E} :
    IsMinOn (finite_sum_objective f) C x ↔
      IsMinOn (fun y ↦ ∑ i, f i y) C x := by
  -- Unfold the aggregate objective so both sides become the same `IsMinOn` statement.
  rfl

end
