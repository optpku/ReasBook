/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_3_19
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

-- Domain sampling for this refine pass:
-- * primary domain: lower level sets and uniform Hessian quadratic-form bounds on `ℝ^n`;
-- * inspected owner declarations in this domain:
--   - `lowerLevelSetOn` / `mem_lowerLevelSetOn` in Chapter 1 for the canonical lower-level-set
--     owner;
--   - `HasHessianLowerBoundOn` / `HasHessianUpperBoundOn` in Chapter 1 for the ambient
--     Hessian-bound owners;
--   - the later duplicate `HasLowerLevelHessianUpperBound` shape in Chapter 5, which should be
--     owned earlier and reused rather than restated;
--   - `HasQuasiNewtonGlobalConvergenceAssumptions` in Chapter 5 as a source-facing assumption
--     package already organized over those owners instead of a wrapper masquerading as a set.
-- * best owner abstraction: the core/canonical owners are `lowerLevelSetOn Set.univ f x0`,
--   `HasHessianLowerBoundOn (Set.univ : Set Point) f m`, and
--   `HasHessianUpperBoundOn (Set.univ : Set Point) f M`;
-- * layer targeted here: `source-facing`, since Assumption 4.3-extra-1 is a chapter-local
--   assumption package, but it should be a `Prop`-valued class over explicit `x0`, not a
--   wrapper object with a `Membership` instance.
-- Primitive data vs derived API:
-- * primitive data: `x0`, `m`, `M`, `ContDiff ℝ 3 f`, and the lower/upper Hessian bounds on all
--   of `Set.univ`;
-- * derived API: the induced lower-level-set bounds, boundedness of that lower level set from
--   Chapter 1, plus the univ-level-set membership and nonemptiness lemmas below.

section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

/-- On `Set.univ`, the canonical lower-level-set owner is exactly the usual set
`{x | f x ≤ f x0}`. -/
@[simp] theorem mem_lowerLevelSetOn_univ
    (f : Point → ℝ) (x0 x : Point) :
    x ∈ lowerLevelSetOn Set.univ f x0 ↔ f x ≤ f x0 := by
  simp

/-- The anchored lower level set always contains its base point. -/
@[simp] theorem self_mem_lowerLevelSetOn_univ
    (f : Point → ℝ) (x0 : Point) :
    x0 ∈ lowerLevelSetOn Set.univ f x0 := by
  simp

/-- The anchored lower level set is nonempty. -/
theorem lowerLevelSetOn_univ_nonempty
    (f : Point → ℝ) (x0 : Point) :
    (lowerLevelSetOn Set.univ f x0 : Set Point).Nonempty :=
  ⟨x0, self_mem_lowerLevelSetOn_univ f x0⟩

/-- Chapter04 Assumption 4.3-extra-1: `f : ℝ^n → ℝ` is `ContDiff ℝ 3`, there are constants
`M > m > 0`, and the Hessian quadratic form is uniformly bounded below and above on all of
`ℝ^n`; by Chapter 1, the anchored lower level set
`lowerLevelSetOn Set.univ f x0 = {x | f x ≤ f x0}` is then bounded. For every `x : ℝ^n` and
every `y : ℝ^n`, the Hessian quadratic form satisfies
`m * ‖y‖^2 ≤ (iteratedFDeriv ℝ 2 f x) ![y, y] ≤ M * ‖y‖^2`. -/
class HasBoundedLowerLevelSetHessianBounds
    (f : Point → ℝ) (x0 : Point) : Prop where
  contDiff : ContDiff ℝ 3 f
  hessian_bounds :
    ∃ m M : ℝ,
      0 < m ∧
        m < M ∧
        HasHessianLowerBoundOn Set.univ f m ∧
        HasHessianUpperBoundOn Set.univ f M

theorem HasBoundedLowerLevelSetHessianBounds.exists_lower_hessianOn_univ
    {f : Point → ℝ} {x0 : Point}
    (h : HasBoundedLowerLevelSetHessianBounds f x0) :
    ∃ m > 0, HasHessianLowerBoundOn Set.univ f m := by
  rcases h.hessian_bounds with ⟨m, M, hm, hmM, hLower, hUpper⟩
  exact ⟨m, hm, hLower⟩

theorem HasBoundedLowerLevelSetHessianBounds.exists_upper_hessianOn_univ
    {f : Point → ℝ} {x0 : Point}
    (h : HasBoundedLowerLevelSetHessianBounds f x0) :
    ∃ M > 0, HasHessianUpperBoundOn Set.univ f M := by
  rcases h.hessian_bounds with ⟨m, M, hm, hmM, hLower, hUpper⟩
  exact ⟨M, lt_trans hm hmM, hUpper⟩

theorem HasBoundedLowerLevelSetHessianBounds.exists_lower_hessian
    {f : Point → ℝ} {x0 : Point}
    (h : HasBoundedLowerLevelSetHessianBounds f x0) :
    ∃ m > 0, HasLowerLevelHessianLowerBound Set.univ f x0 m := by
  rcases h.exists_lower_hessianOn_univ with ⟨m, hm, hLower⟩
  exact ⟨m, hm, hLower.mono (by intro x _; simp)⟩

theorem HasBoundedLowerLevelSetHessianBounds.exists_upper_hessian
    {f : Point → ℝ} {x0 : Point}
    (h : HasBoundedLowerLevelSetHessianBounds f x0) :
    ∃ M > 0, HasLowerLevelHessianUpperBound Set.univ f x0 M := by
  rcases h.exists_upper_hessianOn_univ with ⟨M, hM, hUpper⟩
  exact ⟨M, hM, hUpper.mono (by intro x hx; simp)⟩

/-- Assumption 4.3-extra-1 implies boundedness of the anchored lower level set via the Chapter 1
uniformly positive lower Hessian criterion. -/
theorem HasBoundedLowerLevelSetHessianBounds.levelSet_bounded
    {f : Point → ℝ} {x0 : Point}
    (h : HasBoundedLowerLevelSetHessianBounds f x0) :
    Bornology.IsBounded (lowerLevelSetOn Set.univ f x0) := by
  have hC2 : ContDiffOn ℝ 2 f Set.univ := by
    simpa using (h.contDiff.of_le (by norm_num) : ContDiff ℝ 2 f).contDiffOn
  exact
    bounded_lowerLevelSetOn_of_hessian_uniformly_pos
      Set.univ f x0
      (by simp)
      isOpen_univ
      (by simpa using (convex_univ : Convex ℝ (Set.univ : Set Point)))
      hC2
      h.exists_lower_hessian

end
