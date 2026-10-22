/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_9_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_8_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Proposition_1_4_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Lemma 1.8.8 lies in the domain of transporting global minimizers along ambient translations in
Euclidean space.

Sampled owner-style declarations before refinement:
* `IsMinOn.on_preimage` in mathlib’s `Order.Filter.Extr`, the canonical transport rule for minima
  under pullback along a map;
* `isMinOn_univ_iff` in the same file, the canonical univ-specialization of global minimality;
* `UnconstrainedQuadraticMinimizationProblem.minimizer` in `Definition_1_9_1`;
* `Matrix.isPositive_toEuclideanLin_iff`, the bridge from positive semidefinite matrices to
  positive operators on Euclidean space.

Owner abstraction:
* `IsMinOn` transported by `IsMinOn.on_preimage`.

Primitive data:
* an unconstrained quadratic problem `problem`;
* a translation vector `xBar`.

Derived API:
* `problem.objective`;
* `problem.minimizer`;
* the local centered minimizer statement proved below;
* the translated minimizer statement below.

Source/core/bridge triage:
* source-facing: the translated quadratic model centered at `xBar`;
* core/canonical: completing the square around `problem.minimizer`;
* bridge/view: the affine translation `x ↦ x - xBar`.
-/

namespace UnconstrainedQuadraticMinimizationProblem

/-- Helper for Lemma 1.8.8: the canonical point `problem.minimizer = -A⁻¹ a` satisfies
`A problem.minimizer = -a`. -/
lemma apply_matrix_to_minimizer_eq_neg_linear_coefficient
    (problem : UnconstrainedQuadraticMinimizationProblem n) :
    problem.A.toEuclideanLin problem.minimizer = -problem.a := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hdet : problem.A.det ≠ 0 := ne_of_gt problem.posDef.det_pos
  -- Move to matrix coordinates so that `A * A⁻¹ = 1` cancels directly.
  change Matrix.toLin b b problem.A (-Matrix.toLin b b problem.A⁻¹ problem.a) = -problem.a
  rw [LinearMap.map_neg]
  rw [← Matrix.toLin_mul_apply b b b problem.A problem.A⁻¹ problem.a]
  simp [Matrix.toLin_one, b, hdet]

/-- Helper for Lemma 1.8.8: symmetry of the positive-definite matrix lets us move `A` across the
Euclidean inner product. -/
lemma matrix_inner_apply_swap
    (problem : UnconstrainedQuadraticMinimizationProblem n) (z w : E) :
    inner ℝ (problem.A.toEuclideanLin z) w =
      inner ℝ z (problem.A.toEuclideanLin w) := by
  have hsymm : problem.A.IsSymm := by
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using problem.posDef.1
  -- Rewrite the adjoint action through the transpose, then use symmetry of `A`.
  calc
    inner ℝ (problem.A.toEuclideanLin z) w
      = inner ℝ z ((Matrix.transpose problem.A).toEuclideanLin w) := by
          simpa using matrix_transpose_adjointness problem.A z w
    _ = inner ℝ z (problem.A.toEuclideanLin w) := by
          simp [Matrix.IsSymm.eq hsymm]

/-- Helper for Lemma 1.8.8: completing the square around `problem.minimizer` separates the
objective into its minimum value plus a nonnegative quadratic error. -/
lemma objective_eq_objective_minimizer_add_quadratic_error
    (problem : UnconstrainedQuadraticMinimizationProblem n) (y : E) :
    problem.objective y =
      problem.objective problem.minimizer +
        (1 / 2 : ℝ) * inner ℝ (problem.A.toEuclideanLin (y - problem.minimizer))
          (y - problem.minimizer) := by
  let z : E := y - problem.minimizer
  have hy : y = problem.minimizer + z := by
    simp [z]
  have hmix :
      inner ℝ (problem.A.toEuclideanLin z) problem.minimizer =
        inner ℝ (problem.A.toEuclideanLin problem.minimizer) z := by
    -- Use symmetry to identify the two mixed terms in the square expansion.
    calc
      inner ℝ (problem.A.toEuclideanLin z) problem.minimizer
        = inner ℝ z (problem.A.toEuclideanLin problem.minimizer) :=
            matrix_inner_apply_swap problem z problem.minimizer
      _ = inner ℝ (problem.A.toEuclideanLin problem.minimizer) z := by
            simpa using (real_inner_comm z (problem.A.toEuclideanLin problem.minimizer)).symm
  have hAmin : problem.A.toEuclideanLin problem.minimizer = -problem.a :=
    apply_matrix_to_minimizer_eq_neg_linear_coefficient problem
  -- Expand the objective at `problem.minimizer + z` and cancel the mixed linear terms.
  calc
    problem.objective y
      = problem.α + inner ℝ problem.a problem.minimizer + inner ℝ problem.a z +
          (1 / 2 : ℝ) * inner ℝ (problem.A.toEuclideanLin problem.minimizer)
            problem.minimizer +
          (1 / 2 : ℝ) * inner ℝ (problem.A.toEuclideanLin problem.minimizer) z +
          (1 / 2 : ℝ) * inner ℝ (problem.A.toEuclideanLin z) problem.minimizer +
          (1 / 2 : ℝ) * inner ℝ (problem.A.toEuclideanLin z) z := by
            conv_lhs =>
              rw [UnconstrainedQuadraticMinimizationProblem.objective, quadraticObjective, hy]
              rw [LinearMap.map_add, inner_add_right, inner_add_left, inner_add_right,
                inner_add_right]
            ring
    _ = problem.α + inner ℝ problem.a problem.minimizer + inner ℝ problem.a z +
          (1 / 2 : ℝ) * inner ℝ (problem.A.toEuclideanLin problem.minimizer)
            problem.minimizer +
          inner ℝ (problem.A.toEuclideanLin problem.minimizer) z +
          (1 / 2 : ℝ) * inner ℝ (problem.A.toEuclideanLin z) z := by
            rw [hmix]
            ring
    _ = problem.α + inner ℝ problem.a problem.minimizer +
          (1 / 2 : ℝ) * inner ℝ (problem.A.toEuclideanLin problem.minimizer)
            problem.minimizer +
          (1 / 2 : ℝ) * inner ℝ (problem.A.toEuclideanLin z) z := by
            rw [hAmin]
            have hcancel : inner ℝ problem.a z + inner ℝ (-problem.a) z = 0 := by
              simp
            nlinarith
    _ = problem.objective problem.minimizer +
          (1 / 2 : ℝ) * inner ℝ (problem.A.toEuclideanLin z) z := by
            simp [UnconstrainedQuadraticMinimizationProblem.objective, quadraticObjective]
    _ = problem.objective problem.minimizer +
          (1 / 2 : ℝ) * inner ℝ (problem.A.toEuclideanLin (y - problem.minimizer))
            (y - problem.minimizer) := by
            simp [z]

/-- Helper for Lemma 1.8.8: the quadratic error term is nonnegative because a positive-definite
matrix induces a positive linear operator on Euclidean space. -/
private lemma quadratic_error_nonneg
    (problem : UnconstrainedQuadraticMinimizationProblem n) (y : E) :
    0 ≤ inner ℝ (problem.A.toEuclideanLin y) y := by
  have hpositive : (problem.A.toEuclideanLin : E →ₗ[ℝ] E).IsPositive :=
    Matrix.isPositive_toEuclideanLin_iff.mpr problem.posDef.posSemidef
  -- Positivity of the operator is exactly the nonnegativity of the quadratic form.
  exact hpositive.inner_nonneg_left y

/-- Helper for Lemma 1.8.8: the canonical point `problem.minimizer` minimizes the centered
quadratic objective on the whole space. -/
lemma minimizer_isMinOn
    (problem : UnconstrainedQuadraticMinimizationProblem n) :
    IsMinOn problem Set.univ problem.minimizer := by
  rw [isMinOn_univ_iff]
  intro y
  -- Rewrite the objective as its minimum value plus a nonnegative quadratic error.
  have hobjective :=
    objective_eq_objective_minimizer_add_quadratic_error problem y
  have hnonneg :
      0 ≤ inner ℝ (problem.A.toEuclideanLin (y - problem.minimizer))
        (y - problem.minimizer) :=
    quadratic_error_nonneg problem (y - problem.minimizer)
  have hmin : problem.objective problem.minimizer ≤ problem.objective y := by
    nlinarith [hobjective, hnonneg]
  simpa using hmin

/-- Lemma 1.8.8, owner-centered form: translating the ambient coordinates of an unconstrained
quadratic minimization problem by `xBar` translates its global minimizer by the same amount. -/
theorem isMinOn_translate (problem : UnconstrainedQuadraticMinimizationProblem n) (xBar : E) :
    IsMinOn (fun x ↦ problem (x - xBar)) Set.univ (xBar + problem.minimizer) := by
  let g : E → E := fun x ↦ x - xBar
  -- Pull the centered minimum back through the translation map `x ↦ x - xBar`.
  have hcentered : IsMinOn problem Set.univ (g (xBar + problem.minimizer)) := by
    -- The translated candidate maps back to the centered minimizer.
    simpa [g, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      minimizer_isMinOn problem
  have htranslated : IsMinOn (problem ∘ g) (g ⁻¹' Set.univ) (xBar + problem.minimizer) :=
    hcentered.on_preimage g
  simpa [g, Function.comp, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using htranslated

end UnconstrainedQuadraticMinimizationProblem

end
