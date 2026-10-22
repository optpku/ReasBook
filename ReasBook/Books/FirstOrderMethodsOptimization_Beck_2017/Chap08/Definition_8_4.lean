/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Gradient

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Definition 8.4 is `source-facing`: the textbook introduces the admissible stepsizes obtained by
minimizing the one-dimensional restriction of `f` along the negative gradient direction at the
current iterate. Domain sampling shows that the `core/canonical` minimizer owner is mathlib's
`IsMinOn` on the feasible ray `Set.Ici 0`, while the chapter already uses the ambient gradient
notation `∇`. The public API therefore packages exact line search as the set of nonnegative
minimizers of that line-search objective, with no extra argmin wrapper structure. -/

/-- Definition 8.4: the exact line search stepsizes at the current iterate `x` are the
nonnegative scalars that minimize the one-dimensional descent objective
`t ↦ f (x - t • ∇ f x)` over all `t ≥ 0`. -/
def exact_line_search_stepsizes (f : E → ℝ) (x : E) : Set ℝ :=
  {t | t ∈ Set.Ici (0 : ℝ) ∧ IsMinOn (fun s ↦ f (x - s • ∇ f x)) (Set.Ici 0) t}

-- Proof sketch: unfold `exact_line_search_stepsizes`; membership is definitionally the conjunction
-- that `t` is feasible (`t ≥ 0`) and that it minimizes the line-search objective on the feasible
-- ray `Set.Ici 0`.
/-- A scalar belongs to `exact_line_search_stepsizes f x` exactly when it is nonnegative and
minimizes `t ↦ f (x - t • ∇ f x)` over all nonnegative step sizes. -/
@[simp] theorem mem_exact_line_search_stepsizes_iff {f : E → ℝ} {x : E} {t : ℝ} :
    t ∈ exact_line_search_stepsizes f x ↔
      0 ≤ t ∧ IsMinOn (fun s ↦ f (x - s • ∇ f x)) (Set.Ici 0) t := by
  -- Expand the set-valued definition and simplify feasibility on `Set.Ici 0`.
  simp [exact_line_search_stepsizes]

-- Proof sketch: every member of `exact_line_search_stepsizes f x` satisfies the defining
-- conjunction from `mem_exact_line_search_stepsizes_iff`, and its first component is exactly the
-- feasibility condition `0 ≤ t`.
/-- Every exact line search stepsize is nonnegative. -/
theorem exact_line_search_stepsizes_subset_Ici (f : E → ℝ) (x : E) :
    exact_line_search_stepsizes f x ⊆ Set.Ici (0 : ℝ) := by
  intro t ht
  -- Project the feasibility component from the membership characterization.
  rw [Set.mem_Ici]
  exact (mem_exact_line_search_stepsizes_iff.mp ht).1

end
