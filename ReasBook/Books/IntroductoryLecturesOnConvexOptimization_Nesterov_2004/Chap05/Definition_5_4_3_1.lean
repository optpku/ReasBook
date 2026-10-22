/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_30

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped EuclideanOrthant

variable {m n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Eₘ" => EuclideanSpace ℝ (Fin m)

/-- Definition 5.4.3.1: for `A ∈ ℝ^{m × n}`, `b ∈ ℝ^m`, and `c ∈ ℝ^n` with `m < n`, the linear
optimization problem with nonnegativity constraints is the minimization of the linear functional
`x ↦ ⟪c, x⟫` over the nonnegative orthant subject to the linear equality constraint `A x = b`. -/
def linearOptimizationProblemWithNonnegativityConstraints
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Eₘ) (c : Eₙ) :
    PrimalEqualityConstrainedProblem Eₙ Eₘ :=
  SetConstrainedMinimizationProblem.toPrimalEqualityConstrainedProblem
    ({ feasibleSet := ℝ₊^n
       objective := fun x ↦ inner ℝ c x } : SetConstrainedMinimizationProblem Eₙ)
    A.toEuclideanLin b

-- Proof sketch: unfold
-- `linearOptimizationProblemWithNonnegativityConstraints`; its ambient feasible set is the Chapter
-- 1 owner `nonnegativeOrthant n`, so membership is exactly coordinatewise nonnegativity.
/-- Membership in the ambient feasible set of the nonnegativity-constrained linear optimization
problem is exactly coordinatewise nonnegativity. -/
@[simp] theorem mem_linearOptimizationProblemWithNonnegativityConstraints_ambientFeasibleSet_iff
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Eₘ) (c : Eₙ) {x : Eₙ} :
    x ∈ (linearOptimizationProblemWithNonnegativityConstraints A b c).feasibleSet ↔
      ∀ i : Fin n, 0 ≤ x i := by
  rw [linearOptimizationProblemWithNonnegativityConstraints]
  simp

-- Proof sketch: the equality-problem owner already packages the intrinsic feasible set
-- `Q ∩ {x | A x = b}` as `equalityFeasibleSet`; expand that owner lemma and rewrite
-- `A.toEuclideanLin x` as the matrix action `A.mulVec x`.
/-- Membership in the equality-feasible set of the nonnegativity-constrained linear optimization
problem is exactly coordinatewise nonnegativity together with the equation `A x = b`. -/
theorem mem_linearOptimizationProblemWithNonnegativityConstraints_equalityFeasibleSet_iff
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Eₘ) (c : Eₙ) {x : Eₙ} :
    x ∈ (linearOptimizationProblemWithNonnegativityConstraints A b c).equalityFeasibleSet ↔
      (∀ i : Fin n, 0 ≤ x i) ∧ A.mulVec x = b := by
  rw [linearOptimizationProblemWithNonnegativityConstraints]
  rw [PrimalEqualityConstrainedProblem.mem_equalityFeasibleSet_iff]
  constructor
  · rintro ⟨hx, hxEq⟩
    exact ⟨by simpa using hx, by
      rw [Matrix.toEuclideanLin, Matrix.toLpLin] at hxEq
      simpa using congrArg WithLp.ofLp hxEq⟩
  · rintro ⟨hx, hxEq⟩
    exact ⟨by simpa using hx, by
      simpa [Matrix.toEuclideanLin, Matrix.toLpLin] using congrArg (WithLp.toLp 2) hxEq⟩

/-- The strict feasible set `{x | A x = b ∧ x ∈ \mathbb{R}^n_{++}}` of the
nonnegativity-constrained linear optimization problem. The objective vector does not enter this
owner because strict feasibility depends only on the constraints. -/
def linearOptimizationProblemWithNonnegativityConstraintsStrictFeasibleSet
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Eₘ) : Set Eₙ :=
  linearEqualityFeasibleSet (ℝ₊₊^n : Set Eₙ) A.toEuclideanLin b

/-- Membership in the strict feasible set of the nonnegativity-constrained linear optimization
problem means satisfying the equality constraint and lying in the strict positive orthant. -/
@[simp] theorem mem_linearOptimizationProblemWithNonnegativityConstraintsStrictFeasibleSet_iff
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Eₘ) {x : Eₙ} :
    x ∈ linearOptimizationProblemWithNonnegativityConstraintsStrictFeasibleSet A b ↔
      A.mulVec x = b ∧ x ∈ ℝ₊₊^n := by
  rw [linearOptimizationProblemWithNonnegativityConstraintsStrictFeasibleSet]
  rw [mem_linearEqualityFeasibleSet_iff]
  constructor
  · rintro ⟨hx, hxEq⟩
    exact ⟨by
      rw [Matrix.toEuclideanLin, Matrix.toLpLin] at hxEq
      simpa using congrArg WithLp.ofLp hxEq, hx⟩
  · rintro ⟨hxEq, hx⟩
    exact ⟨hx, by
      simpa [Matrix.toEuclideanLin, Matrix.toLpLin] using congrArg (WithLp.toLp 2) hxEq⟩

-- Proof sketch: the equality-constrained owner coerces to its objective on the ambient feasible
-- and that objective is defined to be the linear functional `x ↦ ⟪c, x⟫`.
/-- Evaluating the nonnegativity-constrained linear optimization problem returns the inner product
with the cost vector `c`. -/
theorem linearOptimizationProblemWithNonnegativityConstraints_objective_apply
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Eₘ) (c : Eₙ)
    (x : Eₙ) :
    linearOptimizationProblemWithNonnegativityConstraints A b c x = inner ℝ c x := by
  rw [linearOptimizationProblemWithNonnegativityConstraints]
  rfl

end
