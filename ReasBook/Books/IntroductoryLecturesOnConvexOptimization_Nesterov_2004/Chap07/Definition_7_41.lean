/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_18
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_11
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Theorem_7_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open EuclideanSpace (nonnegativeOrthant positiveOrthant)
open scoped StandardSimplex

/- Definition 7.41 lies in the linear-packing / constrained-optimization domain.

Sampled owner-style declarations:
- `orthantHalfspacePolyhedron` and `mem_orthantHalfspacePolyhedron_iff` in `Chap07/Theorem_7_9`,
  the chapter owner and membership API for orthant-constrained halfspace polyhedra;
- `maxTypeObjective` in `Chap02/Lemma_2_18`, the chapter owner for finite maxima over a nonempty
  family;
- `stdSimplex` and the Chapter 6 notation `Δ[n]` in `Chap06/Definition_6_11`, the canonical owner
  of the standard simplex;
- `EuclideanSpace.nonnegativeOrthant` and `EuclideanSpace.positiveOrthant` in
  `Chap01/Definition_1_10_2`, the project owners for coordinatewise nonnegativity and positivity;
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner of a
  feasible set together with a real-valued objective on a fixed ambient space;
- `SetConstrainedMinimizationProblem.optimalValue` in `Chap01/Definition_1_3_7`, the canonical
  owner optimal-value API.

Best owner abstraction:
- source-facing: `LinearPackingProblem m n`, carrying the packing data `(a_i, b, c)`;
- core/canonical: `nonnegativeOrthant`, `positiveOrthant`, `orthantHalfspacePolyhedron`, and
  `SetConstrainedMinimizationProblem (EuclideanSpace ℝ (Fin n))`;
- bridge/view: `problem.feasibleSet` as the chapter orthant-polyhedron owner specialized to
  `problem.a` and `problem.b`, and the negated-objective bridge to Chapter 1 minimization.

Primitive data:
- the constraint vectors `a_i`, right-hand side `b`, and objective coefficients `c`;
- the sign assumptions `a_i ∈ ℝⁿ_+`, `b ∈ ℝ₊₊ᵐ`, and `c ∈ ℝ₊₊ⁿ`.

Derived API:
- coordinatewise positivity/nonnegativity consequences of the orthant-membership hypotheses;
- the feasible packing set, via `orthantHalfspacePolyhedron`;
- the linear objective `y ↦ ⟪c, y⟫`;
- the normalized slice `{y ∈ ℝⁿ_+ | ⟪c, y⟫ = 1}` used in Proposition 7.18;
- the normalized gauge `y ↦ max_i ⟪a_i, y⟫ / b_i`;
- the simplex gauge obtained from the diagonal rescaling by `c`;
- the Chapter 1 constrained minimization bridge with objective `y ↦ -⟪c, y⟫`;
- the packed optimal value as the negated owner optimal value. -/

variable {m n : ℕ}

/-- Definition 7.41 (1): a linear packing problem consists of nonnegative constraint vectors
`a₁, …, aₘ ∈ ℝⁿ_+`, a positive right-hand side `b ∈ ℝᵐ`, and positive objective coefficients
`c ∈ ℝⁿ`. -/
structure LinearPackingProblem (m n : ℕ) where
  /-- The constraint vectors `a_i ∈ ℝⁿ_+`. -/
  a : Fin m → EuclideanSpace ℝ (Fin n)
  /-- The right-hand-side vector `b ∈ ℝᵐ`. -/
  b : EuclideanSpace ℝ (Fin m)
  /-- The objective coefficient vector `c ∈ ℝⁿ`. -/
  c : EuclideanSpace ℝ (Fin n)
  /-- Each constraint vector `a_i` lies in the nonnegative orthant `ℝⁿ_+`. -/
  a_nonneg (i : Fin m) : a i ∈ nonnegativeOrthant n
  /-- The right-hand side lies in the positive orthant `ℝ₊₊ᵐ`. -/
  b_pos : b ∈ positiveOrthant m
  /-- The objective coefficient vector lies in the positive orthant `ℝ₊₊ⁿ`. -/
  c_pos : c ∈ positiveOrthant n

namespace LinearPackingProblem

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Δₙ" => Δ[n]

/-- Coordinatewise nonnegativity of each constraint vector. -/
@[simp] theorem a_nonneg_apply (problem : LinearPackingProblem m n) (i : Fin m) (j : Fin n) :
    0 ≤ problem.a i j := by
  exact (show ∀ k : Fin n, 0 ≤ problem.a i k by simpa using problem.a_nonneg i) j

/-- Coordinatewise positivity of the right-hand side vector. -/
@[simp] theorem b_pos_apply (problem : LinearPackingProblem m n) (i : Fin m) :
    0 < problem.b i := by
  exact (show ∀ k : Fin m, 0 < problem.b k by simpa using problem.b_pos) i

/-- Coordinatewise positivity of the objective coefficient vector. -/
@[simp] theorem c_pos_apply (problem : LinearPackingProblem m n) (j : Fin n) :
    0 < problem.c j := by
  exact (show ∀ k : Fin n, 0 < problem.c k by simpa using problem.c_pos) j

/-- The feasible packing polyhedron `P = {y ≥ 0 | ⟪a_i, y⟫ ≤ b_i for all i}`. -/
abbrev feasibleSet (problem : LinearPackingProblem m n) : Set E :=
  orthantHalfspacePolyhedron problem.a (fun i ↦ problem.b i)

/-- Membership in `problem.feasibleSet` is exactly the nonnegativity and packing-constraint
condition. -/
@[simp] theorem mem_feasibleSet_iff
    (problem : LinearPackingProblem m n) {y : E} :
    y ∈ problem.feasibleSet ↔
      y ∈ nonnegativeOrthant n ∧ ∀ i : Fin m, inner ℝ (problem.a i) y ≤ problem.b i := by
  simp [feasibleSet]

/-- The packing objective `y ↦ ⟪c, y⟫`. -/
def objective (problem : LinearPackingProblem m n) : E → ℝ :=
  inner ℝ problem.c

@[simp] theorem objective_apply (problem : LinearPackingProblem m n) (y : E) :
    problem.objective y = inner ℝ problem.c y :=
  rfl

/-- The normalized nonnegative slice `{y ∈ ℝⁿ_+ | ⟪c, y⟫ = 1}` attached to a linear packing
problem. -/
def normalizedSlice (problem : LinearPackingProblem m n) : Set E :=
  {y | y ∈ nonnegativeOrthant n ∧ problem.objective y = 1}

/-- Membership in `problem.normalizedSlice` means belonging to the nonnegative orthant and
satisfying the normalization `⟪c, y⟫ = 1`. -/
@[simp] theorem mem_normalizedSlice_iff
    (problem : LinearPackingProblem m n) {y : E} :
    y ∈ problem.normalizedSlice ↔ y ∈ nonnegativeOrthant n ∧ inner ℝ problem.c y = 1 := by
  simp [normalizedSlice, objective]

/-- A linear packing problem can be used as its objective function `y ↦ ⟪c, y⟫`. -/
instance : CoeFun (LinearPackingProblem m n) (fun _ ↦ E → ℝ) where
  coe problem := problem.objective

@[simp] theorem coe_apply (problem : LinearPackingProblem m n) (y : E) :
    problem y = problem.objective y :=
  rfl

/-- The source-facing gauge `y ↦ max_i ⟪a_i, y⟫ / b_i` attached to a linear packing problem. The
positivity of `b_i` is primitive owner data, so this expression is used only in the faithful
packing regime. -/
abbrev gauge (problem : LinearPackingProblem m n) [Nonempty (Fin m)] : E → ℝ :=
  maxTypeObjective (fun i y ↦ inner ℝ (problem.a i) y / problem.b i)

@[simp] theorem gauge_apply (problem : LinearPackingProblem m n) [Nonempty (Fin m)] (y : E) :
    problem.gauge y =
      maxTypeObjective (fun i x ↦ inner ℝ (problem.a i) x / problem.b i) y :=
  rfl

/-- The simplex gauge obtained from `problem.gauge` after the diagonal change of variables
`x_j = c_j y_j`. -/
abbrev scaledGauge (problem : LinearPackingProblem m n) [Nonempty (Fin m)] : Δₙ → ℝ :=
  fun x ↦ maxTypeObjective
    (fun i y ↦ dotProduct (fun j ↦ problem.a i j / problem.c j) y / problem.b i) x.1

@[simp] theorem scaledGauge_apply
    (problem : LinearPackingProblem m n) [Nonempty (Fin m)] (x : Δₙ) :
    problem.scaledGauge x =
      maxTypeObjective
        (fun i y ↦ dotProduct (fun j ↦ problem.a i j / problem.c j) y / problem.b i) x.1 :=
  rfl

/-- The Chapter 1 constrained minimization owner attached to the packing problem, using the
negated objective so that maximization is represented canonically through minimization. -/
def toSetConstrainedMinimizationProblem
    (problem : LinearPackingProblem m n) : SetConstrainedMinimizationProblem E where
  feasibleSet := problem.feasibleSet
  objective := fun y ↦ -problem.objective y

@[simp] theorem toSetConstrainedMinimizationProblem_feasibleSet
    (problem : LinearPackingProblem m n) :
    problem.toSetConstrainedMinimizationProblem.feasibleSet = problem.feasibleSet :=
  rfl

@[simp] theorem toSetConstrainedMinimizationProblem_apply
    (problem : LinearPackingProblem m n) (y : E) :
    problem.toSetConstrainedMinimizationProblem y = -problem.objective y :=
  rfl

/-- Definition 7.41 (2): the packing optimal value `ψ*` is the negated Chapter 1 optimal value
of the associated constrained minimization problem with objective `y ↦ -⟪c, y⟫`. This is the
canonical owner form of the textbook supremum definition. -/
def optimalValue (problem : LinearPackingProblem m n) : EReal :=
  -problem.toSetConstrainedMinimizationProblem.optimalValue

/-- Helper for Definition 7.41: negating the infimum of the negated image of an `EReal` set
recovers the supremum of the original set. -/
private theorem neg_sInf_neg_image_eq_sSup (s : Set EReal) :
    -sInf ((fun z : EReal ↦ -z) '' s) = sSup s := by
  -- Negation converts upper bounds on `s` into lower bounds on the negated image.
  apply le_antisymm
  · rw [EReal.neg_le]
    refine le_sInf ?_
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    -- Every element of `s` lies below `sSup s`, so its negation lies above `-sSup s`.
    rw [EReal.neg_le, neg_neg]
    exact le_sSup hy
  · -- Conversely, each point of `s` is bounded above by the negated infimum bound.
    refine sSup_le ?_
    intro y hy
    rw [EReal.le_neg]
    exact sInf_le (Set.mem_image_of_mem (fun z : EReal ↦ -z) hy)

/-- Helper for Definition 7.41: unfolding the Chapter 1 minimization owner rewrites the packing
value as the negated infimum of the negated feasible objective-value image. -/
private theorem optimalValue_eq_neg_sInf_negated_feasible_values
    (problem : LinearPackingProblem m n) :
    problem.optimalValue =
      -sInf (((fun z : EReal ↦ -z) '' ((fun y ↦ (problem.objective y : EReal)) ''
        problem.feasibleSet))) := by
  -- Unfold the owner value and rewrite the Chapter 1 problem as an infimum over feasible values.
  rw [optimalValue, problem.toSetConstrainedMinimizationProblem.optimalValue_eq_sInf_image]
  -- The negated real objective becomes the negation map on the `EReal` objective-value image.
  simp [Set.image_image]

-- Proof sketch: unfold `optimalValue`, rewrite the Chapter 1 owner value as an infimum of the
-- negated objective on the feasible set, and use the order anti-isomorphism `x ↦ -x` to turn the
-- infimum of `-⟪c, y⟫` into the supremum of `⟪c, y⟫`.
/-- The canonical owner optimal value for Definition 7.41 is the supremum of the packing
objective on the feasible packing polyhedron, viewed in `EReal`. -/
theorem optimalValue_eq_sSup_image (problem : LinearPackingProblem m n) :
    problem.optimalValue =
      sSup ((fun y ↦ (problem.objective y : EReal)) '' problem.feasibleSet) := by
  -- First rewrite the packing owner into the negated-infimum form coming from Chapter 1.
  rw [optimalValue_eq_neg_sInf_negated_feasible_values]
  -- Then use the `EReal` negation/supremum bridge for the feasible objective-value set.
  exact neg_sInf_neg_image_eq_sSup _

end LinearPackingProblem

end
