/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

universe u

section

variable {E : Type u} [AddCommMonoid E] [Module ℝ E]

/- Assumption 8.41 is `source-facing`: it fixes the standing hypotheses for the convex
inequality-constrained primal problem used by the dual projected subgradient method. The
source-facing data are the ambient set `X`, the objective `f`, the constraint family `g`, the
optimal set `XStar`, and the optimal value `fOpt`. The public API records these assumptions
directly with mathlib's `Convex`, `ConvexOn`, `IsMinOn`, and `IsGLB`, using only the canonical
feasible set and Lagrangian as auxiliary owners. -/

/-- The feasible set for the primal problem underlying the dual projected subgradient method is
the intersection of the ambient convex set `X` with the inequality-feasible set cut out by the
constraint family `g`. -/
def dual_projected_subgradient_feasible_set {m : ℕ}
    (X : Set E) (g : Fin m → E → ℝ) : Set E :=
  {x | x ∈ X ∧ ∀ i : Fin m, g i x ≤ 0}

-- Proof sketch: unfold `dual_projected_subgradient_feasible_set`; membership is exactly
-- membership in `X` together with the coordinatewise inequalities `g i x ≤ 0`.
/-- Membership in `dual_projected_subgradient_feasible_set X g` means belonging to `X` and
satisfying every inequality constraint `g i x ≤ 0`. -/
@[simp] theorem mem_dual_projected_subgradient_feasible_set {m : ℕ}
    {X : Set E} {g : Fin m → E → ℝ} {x : E} :
    x ∈ dual_projected_subgradient_feasible_set X g ↔ x ∈ X ∧ ∀ i : Fin m, g i x ≤ 0 := by
  -- Unfolding the feasible-set owner exposes exactly the defining conjunction.
  rfl

/-- The Lagrangian of the inequality-constrained problem with nonnegative multiplier vector
`lam`. -/
def dual_projected_subgradient_lagrangian {m : ℕ}
    (f : E → ℝ) (g : Fin m → E → ℝ) (lam : Fin m → NNReal) : E → ℝ :=
  fun x ↦ f x + ∑ i, (lam i : ℝ) * g i x

-- Proof sketch: unfold `dual_projected_subgradient_lagrangian`; evaluation at `x` is the
-- objective value plus the finite weighted sum of the constraint values with multipliers
-- `lam i`.
/-- Evaluating `dual_projected_subgradient_lagrangian f g lam` at `x` gives
`f x + ∑ i, lam i * g i x`. -/
@[simp] theorem dual_projected_subgradient_lagrangian_apply {m : ℕ}
    (f : E → ℝ) (g : Fin m → E → ℝ) (lam : Fin m → NNReal) (x : E) :
    dual_projected_subgradient_lagrangian f g lam x =
      f x + ∑ i, (lam i : ℝ) * g i x := by
  -- Evaluating the Lagrangian is definitionally the displayed objective-plus-penalty sum.
  rfl

/-- Assumption 8.41: clauses (A)-(F) hold for the convex inequality-constrained problem over
`X`, namely `X` is convex, `f` and each `g i` are convex, `XStar` is the nonempty optimal set
with finite optimal value `fOpt`, there is a strict feasible point in `X`, and every
nonnegative-multiplier Lagrangian minimization over `X` attains a minimizer. -/
class IsDualProjectedSubgradientProblem {m : ℕ}
    (X XStar : Set E) (f : E → ℝ) (g : Fin m → E → ℝ) (fOpt : ℝ) : Prop where
  feasible_convex : Convex ℝ X
  objective_convex : ConvexOn ℝ Set.univ f
  constraint_convex (i : Fin m) : ConvexOn ℝ Set.univ (g i)
  optimal_set_eq :
    XStar = {x | IsMinOn f (dual_projected_subgradient_feasible_set X g) x}
  optimal_set_nonempty : XStar.Nonempty
  optimal_value_isGLB :
    IsGLB (f '' dual_projected_subgradient_feasible_set X g) fOpt
  slater_condition_on_X :
    ∃ x ∈ X, ∀ i : Fin m, g i x < 0
  lagrangian_has_minimizer (lam : Fin m → NNReal) :
    ∃ x, IsMinOn (dual_projected_subgradient_lagrangian f g lam) X x

/-- A dual projected subgradient problem package canonically supplies both a nonempty optimal set
and the greatest-lower-bound characterization of the optimal value. -/
instance instFactDualProjectedSubgradientOptimalSetNonemptyAndOptimalValueIsGLB
    {m : ℕ} {X XStar : Set E} {f : E → ℝ} {g : Fin m → E → ℝ} {fOpt : ℝ}
    [h : IsDualProjectedSubgradientProblem X XStar f g fOpt] :
    Fact
      (XStar.Nonempty ∧
        IsGLB (f '' dual_projected_subgradient_feasible_set X g) fOpt) where
  out := ⟨h.optimal_set_nonempty, h.optimal_value_isGLB⟩

end
