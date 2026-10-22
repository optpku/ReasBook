/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Example_6_4_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConstrainedArgmin
open CoordinateMaxCounterexample

/-
Text 6.4.2 lies in the Chapter 6 conditional-gradient / nonsmooth counterexample domain.

Sampled owner-style declarations:
- `conditionalGradient_iterates_mem_oracleHull` in `Example_6_4_1`, the source-facing owner of
  the trapping statement `x t ∈ oracleHull x₀`;
- `optimizer_not_mem_oracleHull` in `Example_6_4_1`, the fixed-set disjointness owner excluding
  `optimizer` from that trap set;
- `constrainedArgmin` with notation `argmin[Q] f` and `mem_constrainedArgmin_iff` in
  `Chap01/Definition_1_3_3`, the canonical project owner for linearized-oracle minimizers.

Best owner abstraction:
- source-facing: the textbook nonsmooth counterexample from Text 6.4.2;
- core/canonical: `oracleHull`, `conditionalGradient_iterates_mem_oracleHull`,
  `optimizer_not_mem_oracleHull`, and `argmin[feasibleSet]`;
- bridge/view: the fixed trap-set pair
  `Set.range x ⊆ oracleHull x₀ ∧ optimizer ∉ oracleHull x₀`.

Primitive data:
- the initial point `x₀`, step sizes `τ`, iterates `x`, admissible subgradients `g`, and oracle
  points `v`;
- the update rule and the canonical oracle membership
  `v t ∈ argmin[feasibleSet] (fun y ↦ inner ℝ (g t) y)`.

Derived API:
- the pointwise hull-membership theorem `conditionalGradient_iterates_mem_oracleHull`;
- the fixed-hull disjointness theorem `optimizer_not_mem_oracleHull`;
- the pointwise exclusion corollary `conditionalGradient_iterates_ne_optimizer`;
- the bridge from `argmin` membership to `IsMinOn` provided by `mem_constrainedArgmin_iff`.

This refinement keeps Text 6.4.2 as a thin bridge over the Chapter 6 counterexample owners. The
public theorem now uses the canonical oracle owner `argmin[feasibleSet]` directly, instead of a
parallel raw `v t ∈ feasibleSet ∧ IsMinOn ...` interface.
-/

section

local notation "E" => EuclideanSpace ℝ (Fin 2)

-- Proof sketch: this is the explicit trapping mechanism from Example 6.4.1. The admissible
-- subgradients are the two coordinate vectors `e₁` and `e₂`, so every linearized subproblem on
-- the unit disk selects one of the two oracle vertices. Induction on the update
-- `x_{t+1} = (1 - τ_t) x_t + τ_t v_t` keeps the whole trajectory in
-- `conv{x₀, y₁, y₂}`.
/-- Text 6 4 2 Why Smoothness Is Needed: in the nonsmooth counterexample of Example 6.4.1, if
the conditional-gradient update is driven by admissible subgradient choices of
`x ↦ max{x₁, x₂}`, then the full trajectory is trapped in the fixed set
`conv{x₀, (-1, 0), (0, -1)}`. -/
theorem coordinateMax_conditionalGradient_range_subset_oracleHull
    {x0 : E}
    {τ : ℕ → ℝ} (hτ : ∀ t : ℕ, τ t ∈ Set.Icc (0 : ℝ) 1)
    {x : ℕ → E} (hx_zero : x 0 = x0)
    {g : ℕ → E}
    (hg :
      ∀ t : ℕ,
        IsSubgradientAt (fun y ↦ (objective y : WithTop ℝ)) (x t) (g t) ∧
          (g t = firstSubgradient ∨ g t = secondSubgradient))
    {v : ℕ → E}
    (hv : ∀ t : ℕ, v t ∈ argmin[feasibleSet] (fun y : E ↦ inner ℝ (g t) y))
    (hx_succ : ∀ t : ℕ, x (t + 1) = (1 - τ t) • x t + τ t • v t) :
    Set.range x ⊆ oracleHull x0 := by
  -- First recover the owner theorem's pointwise trapping invariant for the iterates.
  have hx_mem : ∀ t : ℕ, x t ∈ oracleHull x0 :=
    CoordinateMaxCounterexample.conditionalGradient_iterates_mem_oracleHull
      hτ hx_zero hg hv hx_succ
  -- Then unpack an arbitrary point in the range of `x` and apply the pointwise invariant.
  intro y hy
  rcases hy with ⟨t, rfl⟩
  exact hx_mem t

-- Proof sketch: this is the fixed disjointness statement from Example 6.4.1 showing that the
-- trap set `conv{x₀, y₁, y₂}` misses the optimizer whenever `x₀ ≠ x_*`.
/-- Corollary for Text 6 4 2 Why Smoothness Is Needed: in the same nonsmooth counterexample, the
fixed trap set `conv{x₀, (-1, 0), (0, -1)}` excludes the optimizer `x_*`. -/
theorem coordinateMax_oracleHull_excludes_optimizer
    {x0 : E} (hx0_mem : x0 ∈ feasibleSet) (hx0_ne : x0 ≠ optimizer) :
    optimizer ∉ oracleHull x0 := by
  -- This is exactly the fixed hull-exclusion theorem from the owner file.
  exact CoordinateMaxCounterexample.optimizer_not_mem_oracleHull hx0_mem hx0_ne

end
