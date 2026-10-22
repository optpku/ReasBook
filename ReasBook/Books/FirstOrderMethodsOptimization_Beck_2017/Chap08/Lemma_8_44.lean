/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Assumption_8_41

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

universe u

section

variable {E : Type u} [AddCommMonoid E] [Module ℝ E]
variable {m : ℕ}

/- Lemma 8.44 is `source-facing` in the Chapter 8 dual projected-subgradient API. The canonical
owner abstractions already present in the project are the feasible-set owner
`dual_projected_subgradient_feasible_set`, the Lagrangian owner
`dual_projected_subgradient_lagrangian`, and mathlib's `IsMinOn`. The source assumption package
`Assumption 8.41` is mathematically redundant for this optimality implication, so the public
statement keeps only the actual data used by the lemma: a nonnegative multiplier vector, a
Lagrangian minimizer over `X`, and the exact feasibility equation `g(xBar) = 0`. -/

-- Proof sketch: for any feasible `x`, the coordinatewise inequalities `g i x ≤ 0` and
-- nonnegativity of `lamBar i` give
-- `f xBar ≤ f xBar + lamBarᵀ g(xBar) ≤ f x + lamBarᵀ g(x) ≤ f x`. The hypothesis
-- `g i xBar = 0` makes `xBar` feasible and identifies the Lagrangian value at `xBar` with
-- `f xBar`.
/-- Helper for Lemma 8.44: if `xBar ∈ X` and every constraint value at `xBar` is zero, then
`xBar` belongs to the primal feasible set. -/
lemma constraint_eq_zero_mem_dual_projected_subgradient_feasible_set
    {X : Set E} {g : Fin m → E → ℝ} {xBar : E}
    (hxBar : xBar ∈ X) (hzero : ∀ i : Fin m, g i xBar = 0) :
    xBar ∈ dual_projected_subgradient_feasible_set X g := by
  -- Rewriting feasible-set membership reduces feasibility to the ambient membership and the
  -- coordinatewise inequalities.
  rw [mem_dual_projected_subgradient_feasible_set]
  refine ⟨hxBar, ?_⟩
  intro i
  simp [hzero i]

/-- Helper for Lemma 8.44: the Lagrangian value at a point with vanishing constraints equals the
objective value at that point. -/
lemma dual_projected_subgradient_lagrangian_eq_objective_of_constraint_eq_zero
    {f : E → ℝ} {g : Fin m → E → ℝ} {lamBar : Fin m → NNReal} {xBar : E}
    (hzero : ∀ i : Fin m, g i xBar = 0) :
    dual_projected_subgradient_lagrangian f g lamBar xBar = f xBar := by
  -- The equality constraints make every penalty summand zero.
  rw [dual_projected_subgradient_lagrangian_apply]
  simp [hzero]

/-- Helper for Lemma 8.44: every feasible point has Lagrangian value at most its objective value,
because the multiplier vector is nonnegative and the constraint values are nonpositive. -/
lemma dual_projected_subgradient_lagrangian_le_objective_of_feasible
    {X : Set E} {f : E → ℝ} {g : Fin m → E → ℝ} {lamBar : Fin m → NNReal} {x : E}
    (hx : x ∈ dual_projected_subgradient_feasible_set X g) :
    dual_projected_subgradient_lagrangian f g lamBar x ≤ f x := by
  rcases (mem_dual_projected_subgradient_feasible_set.mp hx) with ⟨_, hxg⟩
  rw [dual_projected_subgradient_lagrangian_apply]
  -- Each penalty summand is nonpositive, so the whole penalty sum is nonpositive.
  have hsum_nonpos : ∑ i, (lamBar i : ℝ) * g i x ≤ 0 := by
    refine Finset.sum_nonpos ?_
    intro i hi
    exact mul_nonpos_of_nonneg_of_nonpos (NNReal.coe_nonneg (lamBar i)) (hxg i)
  linarith

/-- Lemma 8.44: if `xBar` minimizes the Lagrangian `f(x) + λ̄ᵀ g(x)` over `X` for some
nonnegative multiplier vector `λ̄` and satisfies `g(xBar) = 0`, then `xBar` is feasible for the
primal problem and minimizes `f` on the feasible set `{x ∈ X | g_i(x) ≤ 0}`. -/
theorem primal_optimality_of_lagrangian_isMinOn_of_constraint_eq_zero
    {X : Set E} {f : E → ℝ} {g : Fin m → E → ℝ} {lamBar : Fin m → NNReal} {xBar : E}
    (hxBar : xBar ∈ X)
    (hmin : IsMinOn (dual_projected_subgradient_lagrangian f g lamBar) X xBar)
    (hzero : ∀ i : Fin m, g i xBar = 0) :
    xBar ∈ dual_projected_subgradient_feasible_set X g ∧
      IsMinOn f (dual_projected_subgradient_feasible_set X g) xBar := by
  refine ⟨constraint_eq_zero_mem_dual_projected_subgradient_feasible_set hxBar hzero, ?_⟩
  rw [isMinOn_iff]
  intro x hx
  rcases (mem_dual_projected_subgradient_feasible_set.mp hx) with ⟨hxX, hxg⟩
  have hlagMin : dual_projected_subgradient_lagrangian f g lamBar xBar ≤
      dual_projected_subgradient_lagrangian f g lamBar x :=
    (isMinOn_iff.mp hmin) x hxX
  -- This is the source proof: `f xBar = L(xBar) ≤ L(x) ≤ f x` for every feasible `x`.
  calc
    f xBar = dual_projected_subgradient_lagrangian f g lamBar xBar := by
      symm
      exact dual_projected_subgradient_lagrangian_eq_objective_of_constraint_eq_zero hzero
    _ ≤ dual_projected_subgradient_lagrangian f g lamBar x := hlagMin
    _ ≤ f x := dual_projected_subgradient_lagrangian_le_objective_of_feasible
      (X := X) (f := f) (g := g) (lamBar := lamBar) (x := x)
      (mem_dual_projected_subgradient_feasible_set.mpr ⟨hxX, hxg⟩)

end
