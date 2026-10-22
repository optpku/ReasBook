/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} {α : Type*} [Preorder α]
variable [TopologicalSpace E] [AddCommMonoid E] [SMul ℝ E]

/- Assumption 13.17 is `source-facing`: it adds geometric hypotheses to a constrained problem with
feasible set `Ω` and chosen optimizer `xStar`.

Domain sampling against mathlib identifies the owner abstractions already present for each clause:
- `constrained_problem_solutions` from Chapter 8 for the constrained optimal-solution condition,
  with `mem_constrained_problem_solutions_iff` supplying the derived feasibility/minimizer view;
- `interior` and `frontier` for the topological position of `Ω` and `xStar`;
- `Ω.extremePoints ℝ` for the non-extremality clause.

The clean statement surface is therefore a small `Prop`-valued class on `(F, Ω, xStar)`, with the
solution-set membership kept as primitive data and its consequences recovered through the Chapter 8
owner theorem rather than through parallel local projections. -/

/-- Assumption 13.17: for the constrained problem from Definition 13.10, the feasible set `Ω` has
nonempty interior, and the chosen optimal solution `xStar = x*` lies on the boundary of `Ω` but is
not an extreme point of `Ω`. -/
class IsBoundaryNonExtremeOptimalSolution
    (F : E → α) (Ω : Set E) (xStar : E) : Prop where
  interior_nonempty : (interior Ω).Nonempty
  mem_constrained_problem_solutions : xStar ∈ constrained_problem_solutions F Ω
  mem_frontier : xStar ∈ frontier Ω
  not_mem_extremePoints : xStar ∉ Ω.extremePoints ℝ

/-- A boundary non-extreme optimal solution canonically provides the chosen optimizer as a
solution of the constrained problem. -/
instance instFactMemConstrainedProblemSolutionsOfIsBoundaryNonExtremeOptimalSolution
    {F : E → α} {Ω : Set E} {xStar : E}
    [h : IsBoundaryNonExtremeOptimalSolution F Ω xStar] :
    Fact (xStar ∈ constrained_problem_solutions F Ω) where
  out := h.mem_constrained_problem_solutions

end
