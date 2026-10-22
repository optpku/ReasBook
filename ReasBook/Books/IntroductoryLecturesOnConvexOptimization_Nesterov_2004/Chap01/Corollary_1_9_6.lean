/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Lemma_1_9_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Lemma_1_9_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient
open UnconstrainedQuadraticMinimizationProblem.IsConjugateGradientSequence

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

namespace IsConjugateGradientSequence

/-
Corollary 1.9.6 is a source-facing finite-dimensional consequence of the owner-side conjugate-
gradient datum `IsConjugateGradientSequence problem x0 xs`.

* primitive data: the quadratic problem, the initial point, the positive-indexed iterate sequence,
  and the owner hypothesis `hcg`;
* derived API: the full trajectory `conjugateGradientTrajectory x0 xs`, the owner-side span theorem
  `krylovSubspace_eq_span_gradients hcg`, the affine-span orthogonality theorem
  `gradients_pairwise_orthogonal_of_isMinOn_affineSpan_gradients`, and the quadratic objective
  `problem.objective`;
* finite-dimensional owner step: the mathlib facts
  `linearIndependent_of_ne_zero_of_inner_eq_zero` and
  `LinearIndependent.fintype_card_le_finrank`.

Accordingly, the corollary is stated directly as an owner-side consequence of `hcg`, not as a
parallel free-standing wrapper around the same data.
-/

/-- Corollary 1.9.6: a conjugate-gradient trajectory for problem `(1.3.2)` is finite in the sense
that some iterate among the first `n + 1` points of the full trajectory has vanishing gradient. -/
-- Proof sketch: rewrite each affine Krylov search space as the affine span of the earlier
-- trajectory gradients, then feed the resulting stagewise minimizer data into Lemma 1.9.5.
-- This makes the first `n + 1` trajectory gradients pairwise orthogonal, so finite-dimensional
-- linear algebra in `ℝⁿ` forces one of them to be zero.
theorem zero_gradient_within_dimension
    {problem : UnconstrainedQuadraticMinimizationProblem n} {x0 : E} {xs : ℕ+ → E}
    (hcg : IsConjugateGradientSequence problem x0 xs) :
    ∃ k ≤ n,
      ∇ problem.objective (conjugateGradientTrajectory x0 xs k) = 0 := by
  let trajectory : ℕ → E := conjugateGradientTrajectory x0 xs
  let gradient : ℕ → E := fun k ↦ ∇ problem.objective (trajectory k)
  -- The quadratic objective is differentiable at every trajectory point.
  have hdiff : ∀ k : ℕ, DifferentiableAt ℝ problem.objective (trajectory k) := by
    intro k
    have hsymm : problem.A.IsSymm := by
      simpa [Matrix.IsHermitian, Matrix.IsSymm] using problem.posDef.1
    simpa [UnconstrainedQuadraticMinimizationProblem.objective] using
      (symmetric_quadratic_contDiff_and_gradient_lipschitz
        problem.α problem.a problem.A hsymm).1.differentiable_one (trajectory k)
  -- Rewrite each positive-stage affine Krylov search space into the affine span format required
  -- by Lemma 1.9.5.
  have hmin :
      ∀ k : ℕ, 0 < k →
        let searchSpace : AffineSubspace ℝ E :=
          AffineSubspace.mk' (trajectory 0)
            (Submodule.span ℝ (Set.range fun j : Fin k ↦ gradient j))
        trajectory k ∈ searchSpace ∧
          IsMinOn problem.objective (searchSpace : Set E) (trajectory k) := by
    intro k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    let stage : ℕ+ := j.succPNat
    have hmem :
        trajectory (j + 1) ∈ problem.affineKrylovSearchSpace x0 stage := by
      simpa [trajectory, conjugateGradientTrajectory] using hcg.mem_affineKrylovSearchSpace stage
    have hmin_stage :
        IsMinOn problem.objective (problem.affineKrylovSearchSpace x0 stage : Set E)
          (trajectory (j + 1)) := by
      simpa [trajectory, conjugateGradientTrajectory] using
        hcg.isMinOn_affineKrylovSearchSpace stage
    simpa [stage, trajectory, gradient,
      UnconstrainedQuadraticMinimizationProblem.affineKrylovSearchSpace,
      krylovSubspace_eq_span_gradients hcg stage] using
      And.intro hmem hmin_stage
  -- Lemma 1.9.5 makes distinct trajectory gradients orthogonal, and hence every prefix is a
  -- pairwise orthogonal finite family.
  have horth :
      Pairwise fun i j : Fin (n + 1) ↦ inner ℝ (gradient i) (gradient j) = 0 := by
    intro i j hij
    exact
      gradients_pairwise_orthogonal_of_isMinOn_affineSpan_gradients
        problem.objective trajectory hdiff hmin (by
          intro h
          exact hij (Fin.ext h))
  -- If all of these gradients were nonzero, they would be linearly independent, contradicting the
  -- ambient dimension bound `finrank ℝ E = n`.
  by_contra hzero
  have hz : ∀ i : Fin (n + 1), gradient i ≠ 0 := by
    intro i hi
    exact hzero ⟨i, Nat.le_of_lt_succ i.is_lt, hi⟩
  let gradients : Fin (n + 1) → E := fun i ↦ gradient i
  have hlin : LinearIndependent ℝ gradients :=
    linearIndependent_of_ne_zero_of_inner_eq_zero hz horth
  have hcard : n + 1 ≤ n := by
    simpa using hlin.fintype_card_le_finrank
  exact (Nat.not_succ_le_self n) hcard

end IsConjugateGradientSequence
