/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Corollary_1_9_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-
Theorem 1.9.12 lies in finite-dimensional quadratic conjugate-gradient termination.

Sampled owner declarations in this domain:
* `UnconstrainedQuadraticMinimizationProblem`, the quadratic owner object;
* `IsConjugateGradientSequence`, the owner predicate for the textbook iterate sequence;
* `IsConjugateGradientSequence.zero_gradient_within_dimension`, the owner-side finite-dimensional
  termination step;
* `problem.eq_minimizer_of_gradient_eq_zero`, the owner-side identification of a stationary point
  with the canonical minimizer.

Best owner abstraction:
* the pair `UnconstrainedQuadraticMinimizationProblem` / `IsConjugateGradientSequence`.

Primitive data:
* `problem : UnconstrainedQuadraticMinimizationProblem n`;
* the initial point `x0`;
* the positive-indexed iterate sequence `xs`.

Derived API:
* `IsConjugateGradientSequence.zero_gradient_within_dimension hcg`;
* the full trajectory `conjugateGradientTrajectory x0 xs`;
* the canonical minimizer `problem.minimizer`.

Source/core/bridge triage:
* source-facing: finite-step attainment of the conjugate-gradient iterate `x_m = x*`;
* core/canonical: the owner-side zero-gradient theorem and stationary-point identification;
* bridge/view: the trajectory map `conjugateGradientTrajectory x0 xs`.

Accordingly, the theorem is stated directly on the owner hypothesis
`IsConjugateGradientSequence problem x0 xs`, and its proof delegates to the existing owner-side
termination and stationary-point API rather than introducing a parallel local wrapper.
-/

namespace IsConjugateGradientSequence

/-- Helper for Theorem 1.9.12: earlier trajectory gradients are orthogonal to later trajectory
gradients along a conjugate-gradient sequence. -/
-- Proof sketch: `krylovSubspace_eq_span_gradients` places the earlier gradient inside the later
-- Krylov space, and the later-stage orthogonality theorem makes the later gradient orthogonal to
-- that entire space.
lemma gradient_orthogonal_of_lt
    {problem : UnconstrainedQuadraticMinimizationProblem n} {x0 : E} {xs : ℕ+ → E}
    (hcg : IsConjugateGradientSequence problem x0 xs) :
    ∀ {a b : ℕ},
      a < b →
        inner ℝ
          (∇ problem.objective (conjugateGradientTrajectory x0 xs a))
          (∇ problem.objective (conjugateGradientTrajectory x0 xs b)) = 0 := by
  intro a b hab
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Nat.zero_lt_of_lt hab))
  let stage : ℕ+ := k.succPNat
  -- The earlier gradient belongs to the later Krylov subspace because that subspace is spanned
  -- by all preceding trajectory gradients.
  have hgrad_mem :
      ∇ problem.objective (conjugateGradientTrajectory x0 xs a) ∈ 𝓛(problem, x0, stage) := by
    rw [_root_.UnconstrainedQuadraticMinimizationProblem.IsConjugateGradientSequence.krylovSubspace_eq_span_gradients
      hcg stage]
    exact Submodule.subset_span ⟨⟨a, hab⟩, rfl⟩
  -- The later gradient is orthogonal to the same Krylov subspace by the owner-side optimality API.
  have horth_stage :
      ∇ problem.objective (conjugateGradientTrajectory x0 xs (k + 1)) ∈
        (𝓛(problem, x0, stage))ᗮ := by
    simpa [stage, conjugateGradientTrajectory] using
      gradient_mem_krylovSubspace_orthogonal hcg stage
  rw [Submodule.mem_orthogonal'] at horth_stage
  simpa [real_inner_comm] using horth_stage _ hgrad_mem

/-- Helper for Theorem 1.9.12: the first `n + 1` trajectory gradients form a pairwise orthogonal
family. -/
-- Proof sketch: compare two indices in `Fin (n + 1)`, reduce to one of the strict inequalities,
-- and then apply `gradient_orthogonal_of_lt`, flipping the inner product when needed.
lemma pairwise_gradient_orthogonal_prefix
    {problem : UnconstrainedQuadraticMinimizationProblem n} {x0 : E} {xs : ℕ+ → E}
    (hcg : IsConjugateGradientSequence problem x0 xs) :
    Pairwise fun i j : Fin (n + 1) ↦
      inner ℝ
        (∇ problem.objective (conjugateGradientTrajectory x0 xs i))
        (∇ problem.objective (conjugateGradientTrajectory x0 xs j)) = 0 := by
  intro i j hij
  have hij_nat : (i : ℕ) ≠ (j : ℕ) := by
    intro h
    exact hij (Fin.ext h)
  rcases lt_or_gt_of_ne hij_nat with hij_lt | hij_gt
  · exact gradient_orthogonal_of_lt hcg hij_lt
  · simpa [real_inner_comm] using gradient_orthogonal_of_lt hcg hij_gt

/-- Helper for Theorem 1.9.12: some trajectory point among the first `n + 1` iterates has
vanishing gradient. -/
-- Route correction: the missing compiled import for Corollary 1.9.6 is replaced by rebuilding the
-- same finite-dimensional orthogonality contradiction from the earlier owner-side API.
-- Proof sketch: if all first `n + 1` gradients were nonzero, the pairwise orthogonality lemma
-- would make them linearly independent, contradicting that `ℝⁿ` has dimension `n`.
lemma exists_stationary_trajectory_index_le_dimension
    {problem : UnconstrainedQuadraticMinimizationProblem n} {x0 : E} {xs : ℕ+ → E}
    (hcg : IsConjugateGradientSequence problem x0 xs) :
    ∃ k ≤ n,
      ∇ problem.objective (conjugateGradientTrajectory x0 xs k) = 0 := by
  let gradients : Fin (n + 1) → E := fun i ↦
    ∇ problem.objective (conjugateGradientTrajectory x0 xs i)
  have horth : Pairwise fun i j : Fin (n + 1) ↦ inner ℝ (gradients i) (gradients j) = 0 := by
    -- The strict-order orthogonality result already has exactly the right content on this prefix.
    simpa [gradients] using pairwise_gradient_orthogonal_prefix hcg
  by_contra hzero
  -- Negating the existential stationary point says every gradient in the prefix is nonzero.
  have hz : ∀ i : Fin (n + 1), gradients i ≠ 0 := by
    intro i hi
    exact hzero ⟨i, Nat.le_of_lt_succ i.is_lt, hi⟩
  -- Pairwise orthogonality plus nonvanishing implies linear independence.
  have hlin : LinearIndependent ℝ gradients :=
    linearIndependent_of_ne_zero_of_inner_eq_zero hz horth
  -- This contradicts the ambient dimension bound `finrank ℝ E = n`.
  have hcard : n + 1 ≤ n := by
    simpa [gradients] using hlin.fintype_card_le_finrank
  exact (Nat.not_succ_le_self n) hcard

/-- Theorem 1.9.12: for an unconstrained quadratic minimization problem on `ℝⁿ`, every
conjugate-gradient trajectory reaches the unique minimizer `x*` within at most `n` iterations. -/
-- Proof sketch: each iterate minimizes the quadratic objective on the affine Krylov search space
-- from Definition 1.9.3. The gradients are therefore orthogonal to the current Krylov subspace,
-- and in the positive-definite quadratic geometry the successive nonstationary search directions
-- become linearly independent. Since `ℝⁿ` has dimension `n`, this can happen for at most `n`
-- steps, so some iterate must already be stationary; Proposition 1.9.11 then identifies that
-- stationary iterate with the canonical minimizer `x* = problem.minimizer`.
theorem eq_minimizer_within_dimension
    {problem : UnconstrainedQuadraticMinimizationProblem n} {x0 : E} {xs : ℕ+ → E}
    (hcg : IsConjugateGradientSequence problem x0 xs) :
    ∃ m ≤ n, conjugateGradientTrajectory x0 xs m = problem.minimizer := by
  -- First find a stationary trajectory point within the ambient dimension bound.
  rcases exists_stationary_trajectory_index_le_dimension hcg with ⟨m, hm, hgrad⟩
  -- A zero gradient identifies the canonical minimizer for this positive-definite quadratic.
  refine ⟨m, hm, ?_⟩
  exact problem.eq_minimizer_of_gradient_eq_zero hgrad

end IsConjugateGradientSequence
