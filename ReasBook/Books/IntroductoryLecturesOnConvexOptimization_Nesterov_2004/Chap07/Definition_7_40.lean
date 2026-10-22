/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_12

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped StandardSimplex

variable {n m : ℕ+}

local notation "Δₙ" => Δ[n]

/- Definition 7.40 lies in the finite simplex / simplex-saddle-point matrix-game domain.

Sampled owner-style declarations:
- `stdSimplex` and the Chapter 6 notation `Δ[n]` in `Chap06/Definition_6_11`, the canonical
  simplex owner;
- `SimplexSaddlePointProblem.primalObjective` in `Chap06/Definition_6_12`, the chapter owner for
  simplex max-type objectives of the form `x ↦ ⟪c, x⟫ + max_j {⟪a_j, x⟫ + b^(j)}`;
- `SetConstrainedMinimizationProblem.optimalValue` in `Chap01/Definition_1_3_7`, the project
  owner for constrained optimal values.

Best owner abstraction:
- source-facing: the matrix-game payoff on the simplex `Δ[n]`;
- core/canonical: `SimplexSaddlePointProblem.primalObjective` for the zero-linear-term saddle
  problem with matrix `Aᵀ`, together with `SetConstrainedMinimizationProblem.optimalValue`;
- bridge/view: the specialization from a nonnegative matrix-game matrix `A` to that simplex
  saddle-point owner, and the whole-domain constrained problem on the simplex subtype.

Primitive data:
- the matrix `A : Matrix (Fin (n : ℕ)) (Fin (m : ℕ)) ℝ`.

Derived API:
- the specialized simplex saddle-point problem with zero linear terms;
- the simplex payoff function;
- its textbook coordinate formula `max_i ⟪a_i, x⟫`;
- the constrained optimal value over simplex points.

The previous file overextended the source-facing matrix-game payoff to arbitrary `m : ℕ` by
inserting a synthetic `m = 0` branch, and it introduced a separate raw real-valued infimum. This
refinement moves back to the chapter's positive simplex dimension layer `n m : ℕ+`, reuses the
earlier Chapter 6 simplex saddle-point owner for the payoff, and derives the value from the
Chapter 1 constrained minimization owner instead of rebuilding a parallel value API.
-/

/-- The nonnegative matrix-game matrix determines a simplex saddle-point problem with zero primal
and dual linear terms. The row-wise primal objective of this owner is exactly the matrix-game
payoff. -/
def nonnegative_matrix_game_saddle_problem
    (A : Matrix (Fin (n : ℕ)) (Fin (m : ℕ)) ℝ) :
    SimplexSaddlePointProblem n m where
  matrix := A.transpose
  primalLinearTerm := 0
  dualLinearTerm := 0

/-- Definition 7.40: for the matrix `A` in the textbook nonnegative-matrix-game setup, the
associated simplex payoff is the Chapter 6 primal objective of the zero-linear-term simplex
saddle-point problem with matrix `Aᵀ`, restricted to `Δ[n]`. -/
def nonnegative_matrix_game_payoff
    (A : Matrix (Fin (n : ℕ)) (Fin (m : ℕ)) ℝ) : Δₙ → ℝ :=
  (nonnegative_matrix_game_saddle_problem A).primalObjective

/-- Evaluating `nonnegative_matrix_game_payoff A` recovers the textbook formula
`max_i ⟪a_i, x⟫`. -/
theorem nonnegative_matrix_game_payoff_apply
    (A : Matrix (Fin (n : ℕ)) (Fin (m : ℕ)) ℝ) (x : Δₙ) :
    nonnegative_matrix_game_payoff A x =
      ⨆ i : Fin (m : ℕ), dotProduct (fun j ↦ A j i) x.1 := by
  simpa [nonnegative_matrix_game_payoff, nonnegative_matrix_game_saddle_problem,
    Finset.sup'_univ_eq_ciSup] using
    SimplexSaddlePointProblem.primalObjective_eq_max_rows
      (nonnegative_matrix_game_saddle_problem A) x

/-- The minimax value `f* = min_{x ∈ Δ_n} f(x)` attached to `A`, formalized as the infimum of the
payoff over the standard simplex through the Chapter 1 constrained minimization owner. -/
def nonnegative_matrix_game_value
    (A : Matrix (Fin (n : ℕ)) (Fin (m : ℕ)) ℝ) : EReal :=
  (SetConstrainedMinimizationProblem.mk Set.univ (nonnegative_matrix_game_payoff A)).optimalValue

/-- Expanding `nonnegative_matrix_game_value A` gives the infimum of the simplex payoff range. -/
theorem nonnegative_matrix_game_value_eq_sInf_range
    (A : Matrix (Fin (n : ℕ)) (Fin (m : ℕ)) ℝ) :
    nonnegative_matrix_game_value A =
      sInf (Set.range fun x : Δₙ ↦ (nonnegative_matrix_game_payoff A x : EReal)) := by
  rw [nonnegative_matrix_game_value,
    SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image]
  simp
