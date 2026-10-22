/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap04.Assumption_4_3_extra_1
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Convex.Extrema
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.InnerProductSpace.PiL2

-- Domain sampling for this refine pass:
-- * primary domain: lower level sets and Hessian bounds in Chapter 5 quasi-Newton convergence;
-- * source-facing owner: `HasQuasiNewtonGlobalConvergenceAssumptions`;
-- * core/canonical project owners: `lowerLevelSetOn`, `HasHessianLowerBoundOn`,
--   `HasHessianUpperBoundOn`;
-- * core/canonical mathlib owner: `StrongConvexOn`;
-- * bridge/view layer: `quasiNewtonLevelSet` is the source-facing `L(x0)` surface, realized as
--   the canonical owner `lowerLevelSetOn Set.univ f x0`.
-- Primitive data here is the Chapter 5 assumption package itself: openness, convexity, and
-- regularity on `D`, containment of `L(x0)` in `D`, and ambient lower/upper Hessian bounds on
-- `D`. The lower-level-set bounds, strong convexity, strict convexity, and uniqueness are
-- derived API.

section Chapter05Assumption531

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

/-- The Chapter 5 level set `L(x0) = {x | f x ≤ f x0}`. This is the source-facing bridge to the
canonical lower-level-set owner `lowerLevelSetOn`. -/
abbrev quasiNewtonLevelSet (f : Point → ℝ) (x0 : Point) : Set Point :=
  lowerLevelSetOn Set.univ f x0

@[simp] theorem mem_quasiNewtonLevelSet
    {f : Point → ℝ} {x0 x : Point} :
    x ∈ quasiNewtonLevelSet f x0 ↔ f x ≤ f x0 := by
  simp [quasiNewtonLevelSet]

/-- Chapter05 Assumption 5.3.1: `f` is twice continuously differentiable on a convex set `D`,
the level set `L(x0) = {x | f x ≤ f x0}` is contained in `D`, and there are positive constants
`m` and `M` giving lower and upper Hessian bounds on all of `D`. The canonical lower-level-set
bounds used later are derived by restriction. -/
class HasQuasiNewtonGlobalConvergenceAssumptions
    (D : Set Point) (f : Point → ℝ) (x0 : Point) : Prop where
  open_domain : IsOpen D
  convex_domain : Convex ℝ D
  contDiffOn : ContDiffOn ℝ 2 f D
  levelSet_subset : quasiNewtonLevelSet f x0 ⊆ D
  lower_hessian :
    ∃ m > 0, HasHessianLowerBoundOn D f m
  upper_hessian :
    ∃ M > 0, HasHessianUpperBoundOn D f M

/-- The base point belongs to its own quasi-Newton level set. -/
theorem mem_quasiNewtonLevelSet_self (f : Point → ℝ) (x0 : Point) :
    x0 ∈ quasiNewtonLevelSet f x0 := by
  simp [quasiNewtonLevelSet]

theorem HasQuasiNewtonGlobalConvergenceAssumptions.x0_mem
    {D : Set Point} {f : Point → ℝ} {x0 : Point}
    (h : HasQuasiNewtonGlobalConvergenceAssumptions D f x0) :
    x0 ∈ D :=
  h.levelSet_subset (mem_quasiNewtonLevelSet_self f x0)

/-- Under Assumption 5.3.1, the source-facing level set `L(x0)` agrees with the canonical
lower-level-set owner on `D`. -/
theorem HasQuasiNewtonGlobalConvergenceAssumptions.levelSet_eq_lowerLevelSetOn
    {D : Set Point} {f : Point → ℝ} {x0 : Point}
    (h : HasQuasiNewtonGlobalConvergenceAssumptions D f x0) :
    quasiNewtonLevelSet f x0 = lowerLevelSetOn D f x0 := by
  ext x
  rw [mem_quasiNewtonLevelSet, mem_lowerLevelSetOn]
  constructor
  · intro hx
    exact ⟨h.levelSet_subset (by simpa using hx), hx⟩
  · intro hx
    exact hx.2

/-- The quasi-Newton global-convergence assumptions imply that the level set `L(x0)` meets the
domain `D`, since the base point `x0` lies in `L(x0)` and `L(x0) ⊆ D`. -/
theorem HasQuasiNewtonGlobalConvergenceAssumptions.levelSetInter_nonempty
    {D : Set Point} {f : Point → ℝ} {x0 : Point}
    (h : HasQuasiNewtonGlobalConvergenceAssumptions D f x0) :
    (quasiNewtonLevelSet f x0 ∩ D : Set Point).Nonempty :=
  ⟨x0, mem_quasiNewtonLevelSet_self f x0, h.x0_mem⟩

/-- The ambient lower Hessian bound from Assumption 5.3.1 restricts to the canonical lower-level
set owner `lowerLevelSetOn D f x0`. -/
theorem HasQuasiNewtonGlobalConvergenceAssumptions.lower_hessianOn_levelSet
    {D : Set Point} {f : Point → ℝ} {x0 : Point}
    (h : HasQuasiNewtonGlobalConvergenceAssumptions D f x0) :
    ∃ m > 0, HasLowerLevelHessianLowerBound D f x0 m := by
  rcases h.lower_hessian with ⟨m, hm, hLower⟩
  refine ⟨m, hm, hLower.mono ?_⟩
  intro x hx
  exact hx.1

/-- The ambient upper Hessian bound from Assumption 5.3.1 restricts to the canonical lower-level
set owner `lowerLevelSetOn D f x0`. -/
theorem HasQuasiNewtonGlobalConvergenceAssumptions.upper_hessianOn_levelSet
    {D : Set Point} {f : Point → ℝ} {x0 : Point}
    (h : HasQuasiNewtonGlobalConvergenceAssumptions D f x0) :
    ∃ M > 0, HasLowerLevelHessianUpperBound D f x0 M := by
  rcases h.upper_hessian with ⟨M, hM, hUpper⟩
  refine ⟨M, hM, hUpper.mono ?_⟩
  intro x hx
  exact hx.1

/-- Assumption 5.3.1 makes the level set `L(x0)` convex by the Chapter 1 lower-level-set owner.
-/
theorem HasQuasiNewtonGlobalConvergenceAssumptions.levelSet_convex
    {D : Set Point} {f : Point → ℝ} {x0 : Point}
    (h : HasQuasiNewtonGlobalConvergenceAssumptions D f x0) :
    Convex ℝ (quasiNewtonLevelSet f x0) := by
  simpa [h.levelSet_eq_lowerLevelSetOn] using
    convex_lowerLevelSetOn_of_hessian_uniformly_pos
      D f x0 h.open_domain h.convex_domain h.contDiffOn h.lower_hessianOn_levelSet

/-- The lower Hessian bound in the quasi-Newton global-convergence assumptions makes the
Hessian quadratic form strictly positive in every nonzero direction on `L(x0)`. -/
theorem HasQuasiNewtonGlobalConvergenceAssumptions.hessian_positive_definite_on_levelSet
    {D : Set Point} {f : Point → ℝ} {x0 : Point}
    (h : HasQuasiNewtonGlobalConvergenceAssumptions D f x0) :
    ∀ x ∈ quasiNewtonLevelSet f x0, ∀ u : Point, u ≠ 0 →
      0 < (iteratedFDeriv ℝ 2 f x) ![u, u] := sorry

/-- The lower Hessian bound in Assumption 5.3.1 yields strong convexity on the level set
`L(x0)` for some source constant `m > 0`. -/
theorem HasQuasiNewtonGlobalConvergenceAssumptions.exists_strongConvexOn_levelSet
    {D : Set Point} {f : Point → ℝ} {x0 : Point}
    (h : HasQuasiNewtonGlobalConvergenceAssumptions D f x0) :
    ∃ m > 0, StrongConvexOn (quasiNewtonLevelSet f x0) m f := sorry

/-- The lower Hessian bound in Assumption 5.3.1 yields the canonical strict-convexity corollary
on the level set `L(x0)`. -/
theorem HasQuasiNewtonGlobalConvergenceAssumptions.strictConvexOn_levelSet
    {D : Set Point} {f : Point → ℝ} {x0 : Point}
    (h : HasQuasiNewtonGlobalConvergenceAssumptions D f x0) :
    StrictConvexOn ℝ (quasiNewtonLevelSet f x0) f := by
  rcases h.exists_strongConvexOn_levelSet with ⟨m, hm, hStrong⟩
  exact hStrong.strictConvexOn hm

/-- The Hessian bounds in the quasi-Newton global-convergence assumptions force any two
minimizers of `f` on `L(x0)` to coincide. -/
theorem HasQuasiNewtonGlobalConvergenceAssumptions.minimizerOnLevelSet_unique
    {D : Set Point} {f : Point → ℝ} {x0 xStar yStar : Point}
    (h : HasQuasiNewtonGlobalConvergenceAssumptions D f x0)
    (hxMin : IsMinOn f (quasiNewtonLevelSet f x0) xStar)
    (hyMin : IsMinOn f (quasiNewtonLevelSet f x0) yStar) :
    xStar = yStar := sorry

/-- If `f` attains its minimum on the level set `L(x0)`, then the Hessian bounds in
Chapter05 Assumption 5.3.1 make that minimizer unique. -/
theorem HasQuasiNewtonGlobalConvergenceAssumptions.existsUniqueMinimizerOnLevelSet
    {D : Set Point} {f : Point → ℝ} {x0 : Point}
    (h : HasQuasiNewtonGlobalConvergenceAssumptions D f x0)
    (h_attains : ∃ xStar : Point, IsMinOn f (quasiNewtonLevelSet f x0) xStar) :
    ∃! xStar : Point,
      IsMinOn f (quasiNewtonLevelSet f x0) xStar := sorry

end Chapter05Assumption531
