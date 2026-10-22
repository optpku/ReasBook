/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_5_extra_3
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Notation

-- The chapter-level owner for the one-dimensional Wolfe-Powell rule is
-- `WolfePowellCondition`, so this exercise keeps only the concrete profile data.

noncomputable section

local notation "Point" => EuclideanSpace ℝ (Fin 2)

/-- The objective `f(x) = x₁^4 + x₁^2 + x₂^2` from Exercise 2.6, encoded on `ℝ²`. -/
def chapter02Exercise26Objective (x : Point) : ℝ :=
  (x 0) ^ (4 : ℕ) + (x 0) ^ (2 : ℕ) + (x 1) ^ (2 : ℕ)

/-- The current point `(1, 1)` used in Exercise 2.6. -/
def chapter02Exercise26CurrentPoint : Point :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![(1 : ℝ), 1]

/-- The search direction `(-3, -1)` used in Exercise 2.6. -/
def chapter02Exercise26SearchDirection : Point :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![(-3 : ℝ), -1]

/-- The one-dimensional line-search profile `α ↦ f(xk + α • dk)` for Exercise 2.6. -/
def chapter02Exercise26Phi : ℝ → ℝ :=
  fun α ↦
    chapter02Exercise26Objective
      (chapter02Exercise26CurrentPoint + α • chapter02Exercise26SearchDirection)

/-- The explicit derivative `φ'(α) = 324 α^3 - 324 α^2 + 128 α - 20`
of the Exercise 2.6 line-search profile. -/
def chapter02Exercise26PhiDeriv : ℝ → ℝ :=
  fun α ↦ 324 * α ^ (3 : ℕ) - 324 * α ^ (2 : ℕ) + 128 * α - 20

/-- The accepted Wolfe-rule update point `(-1 / 2, 1 / 2)` from Exercise 2.6. -/
def chapter02Exercise26NextPoint : Point :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![(-(1 / 2 : ℝ)), 1 / 2]

/-- Helper for Chapter02 Exercise 2.6: the search ray from `(1, 1)` in direction `(-3, -1)`
has the explicit coordinate form `(1 - 3 α, 1 - α)`. -/
lemma search_ray_eq (α : ℝ) :
    chapter02Exercise26CurrentPoint + α • chapter02Exercise26SearchDirection =
      (EuclideanSpace.equiv (Fin 2) ℝ).symm ![(1 - 3 * α : ℝ), 1 - α] := by
  -- Read the search ray coordinatewise so later Wolfe checks reduce to scalar arithmetic.
  ext i
  fin_cases i <;>
    simp [chapter02Exercise26CurrentPoint, chapter02Exercise26SearchDirection] <;>
    ring

/-- Helper for Chapter02 Exercise 2.6: the line-search profile is the scalar quartic obtained by
substituting the explicit search ray into `f(x₁, x₂) = x₁^4 + x₁^2 + x₂^2`. -/
lemma phi_eq_profile (α : ℝ) :
    chapter02Exercise26Phi α =
      (1 - 3 * α) ^ (4 : ℕ) + (1 - 3 * α) ^ (2 : ℕ) + (1 - α) ^ (2 : ℕ) := by
  -- Rewrite `φ(α)` through the explicit search-ray coordinates from the textbook.
  rw [chapter02Exercise26Phi, chapter02Exercise26Objective, search_ray_eq α]
  simp

/-- Helper for Chapter02 Exercise 2.6: the accepted half-step update lands at `(-1 / 2, 1 / 2)`. -/
lemma half_step_update_eq :
    chapter02Exercise26CurrentPoint + (1 / 2 : ℝ) • chapter02Exercise26SearchDirection =
      chapter02Exercise26NextPoint := by
  -- Convert the half-step to coordinates and compare with the recorded next point.
  rw [search_ray_eq (1 / 2 : ℝ)]
  ext i
  fin_cases i <;> norm_num [chapter02Exercise26NextPoint]

/-- Chapter02 Exercise 2.6 (1): the half-step `α = 1 / 2` satisfies the Wolfe rule with
`ρ = 1 / 10` and `σ = 1 / 2`, and the resulting update point is `(-1 / 2, 1 / 2)`. -/
theorem chapter02Exercise26WolfeRuleProducesHalfStepUpdate :
    WolfePowellCondition chapter02Exercise26Phi chapter02Exercise26PhiDeriv
        (1 / 10 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) ∧
      chapter02Exercise26CurrentPoint +
          (1 / 2 : ℝ) • chapter02Exercise26SearchDirection =
        chapter02Exercise26NextPoint := by
  -- Follow the source route: verify the Wolfe inequalities on the scalar profile at `α = 1 / 2`.
  refine ⟨?_, half_step_update_eq⟩
  refine ⟨?_, by norm_num, ?_, ?_⟩
  · -- The exercise uses admissible Wolfe parameters `ρ = 1 / 10 < σ = 1 / 2 < 1`.
    refine ⟨by norm_num, by norm_num, by norm_num⟩
  · -- The sufficient-decrease inequality becomes a rational comparison after profiling `φ`.
    rw [phi_eq_profile (1 / 2 : ℝ), phi_eq_profile (0 : ℝ)]
    norm_num [chapter02Exercise26PhiDeriv]
  · -- The curvature inequality uses only the explicit derivative values at `0` and `1 / 2`.
    norm_num [chapter02Exercise26PhiDeriv]

/-- Chapter02 Exercise 2.6 (2): the trial steplength `α = 1` does not satisfy the Wolfe rule
for the Exercise 2.6 line-search profile with `ρ = 1 / 10` and `σ = 1 / 2`. -/
theorem chapter02Exercise26AlphaOneNotWolfe :
    ¬ WolfePowellCondition chapter02Exercise26Phi chapter02Exercise26PhiDeriv
        (1 / 10 : ℝ) (1 / 2 : ℝ) (1 : ℝ) := by
  -- Expand the Wolfe rule so it suffices to refute the failing sufficient-decrease inequality.
  rw [wolfePowellCondition_iff]
  intro hWolfe
  rcases hWolfe with ⟨_, _, hDecrease, _⟩
  -- On the concrete profile, the Armijo inequality at `α = 1` reduces to `5 ≤ 1`, which is false.
  rw [phi_eq_profile (1 : ℝ), phi_eq_profile (0 : ℝ)] at hDecrease
  norm_num [chapter02Exercise26PhiDeriv] at hDecrease

/-- Chapter02 Exercise 2.6 (3): the trial steplength `α = 1 / 2` satisfies the Wolfe rule
for the Exercise 2.6 line-search profile with `ρ = 1 / 10` and `σ = 1 / 2`. -/
theorem chapter02Exercise26AlphaHalfWolfe :
    WolfePowellCondition chapter02Exercise26Phi chapter02Exercise26PhiDeriv
        (1 / 10 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) := by
  -- Reuse the verified half-step Wolfe certificate from part (1).
  exact chapter02Exercise26WolfeRuleProducesHalfStepUpdate.1

/-- Chapter02 Exercise 2.6 (4): the trial steplength `α = 1 / 10` does not satisfy the Wolfe
rule for the Exercise 2.6 line-search profile with `ρ = 1 / 10` and `σ = 1 / 2`. -/
theorem chapter02Exercise26AlphaTenthNotWolfe :
    ¬ WolfePowellCondition chapter02Exercise26Phi chapter02Exercise26PhiDeriv
        (1 / 10 : ℝ) (1 / 2 : ℝ) (1 / 10 : ℝ) := by
  -- Expand the Wolfe rule and isolate the curvature inequality, which is the failing clause.
  rw [wolfePowellCondition_iff]
  intro hWolfe
  rcases hWolfe with ⟨_, _, _, hCurvature⟩
  -- The derivative values give `-10 ≤ -2529 / 250`, contradicting the curvature requirement.
  norm_num [chapter02Exercise26PhiDeriv] at hCurvature
