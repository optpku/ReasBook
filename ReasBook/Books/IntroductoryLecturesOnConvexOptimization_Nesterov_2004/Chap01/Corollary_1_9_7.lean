/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Lemma_1_9_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-
Corollary 1.9.7 is a source-facing consequence of the owner-side conjugate-gradient datum
`IsConjugateGradientSequence problem x0 xs`.

* primitive data: the quadratic problem `problem`, the initial point `x0`, the positive-indexed
  iterate sequence `xs`, the owner hypothesis `hcg`, and the stage `k`;
* owner abstraction: the canonical Krylov space `problem.krylovSubspace x0 k`;
* derived API: the owner-side orthogonality bridge
  `problem.gradient_mem_krylovSubspace_orthogonal_of_isMinOn_affineKrylovSearchSpace`.

Accordingly, the corollary is stated directly as an owner-side theorem on
`IsConjugateGradientSequence`, not as a parallel free-standing wrapper around the same data.
-/

/-- Corollary 1.9.7: in the conjugate-gradient method for an unconstrained quadratic problem, the
gradient at the `k`th iterate lies in the orthogonal complement of the `k`th Krylov subspace
`𝓛ₖ`. -/
-- Proof sketch: `hcg.isMinOn_affineKrylovSearchSpace k` says that `xs k` minimizes the quadratic
-- objective on the owner affine space `x₀ + 𝓛ₖ`. First-order optimality on an affine subspace
-- therefore makes `∇ problem.objective (xs k)` orthogonal to every vector in the direction of
-- that affine space. Since the direction of `problem.affineKrylovSearchSpace x0 k` is exactly
-- `problem.krylovSubspace x0 k`, the gradient lies in `𝓛ₖᗮ`.
theorem IsConjugateGradientSequence.gradient_mem_krylovSubspace_orthogonal
    {problem : UnconstrainedQuadraticMinimizationProblem n} {x0 : E} {xs : ℕ+ → E}
    (hcg : IsConjugateGradientSequence problem x0 xs) (k : ℕ+) :
    ∇ problem.objective (xs k) ∈ (𝓛(problem, x0, k))ᗮ := by
  -- The conjugate-gradient iterate lies in the affine Krylov search space at stage `k`.
  have hx_mem : xs k ∈ problem.affineKrylovSearchSpace x0 k := by
    simpa using hcg.mem_affineKrylovSearchSpace k
  -- The same iterate minimizes the quadratic objective on that affine search space.
  have hx_min :
      IsMinOn problem.objective (problem.affineKrylovSearchSpace x0 k : Set E) (xs k) := by
    simpa using hcg.isMinOn_affineKrylovSearchSpace k
  -- First-order optimality on the affine Krylov space yields orthogonality to its direction space.
  simpa using
    problem.gradient_mem_krylovSubspace_orthogonal_of_isMinOn_affineKrylovSearchSpace
      x0 (xs k) k
      hx_mem
      hx_min
