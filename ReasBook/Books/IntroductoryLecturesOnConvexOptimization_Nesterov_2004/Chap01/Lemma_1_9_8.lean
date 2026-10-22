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
Lemma 1.9.8 lies in the quadratic conjugate-gradient owner domain.

Sampled declarations in this domain:
* `problem.krylovSubspace x₀ k`, the chapter owner for the Krylov stages `𝓛ₖ`;
* `AffineSubspace.vsub_mem_direction`, the canonical affine-space bridge from iterate membership to
  Krylov-space displacement;
* `IsConjugateGradientSequence.mem_affineKrylovSearchSpace`, the owner membership theorem for the
  iterates;
* `IsConjugateGradientSequence.gradient_mem_krylovSubspace_orthogonal`, the owner-side
  orthogonality input from Corollary 1.9.7;
* `problem.gradient_eq`, `problem.matrix_inner_apply_swap`, and `Submodule.orthogonal_le`, the
  quadratic gradient, symmetry, and orthogonal-complement monotonicity owners used to convert
  gradient orthogonality into `A`-orthogonality of step differences.

Best owner abstraction:
* `IsConjugateGradientSequence problem x0 xs`.

Primitive data:
* the quadratic problem `problem`;
* the starting point `x0`;
* the positive-indexed conjugate-gradient iterate sequence `xs`.

Derived API:
* the full trajectory `conjugateGradientTrajectory x0 xs`;
* the owner-side theorem `stepDifference_mem_krylovSubspace`;
* the step differences `xₖ₊₁ - xₖ`;
* the Krylov stages `𝓛(problem, x0, k)` and their orthogonal complements.

Source/core/bridge triage:
* source-facing: pairwise `A`-orthogonality of distinct step differences along the
  conjugate-gradient trajectory;
* core/canonical: the owner Krylov spaces and their gradient-orthogonality API;
* bridge/view: `conjugateGradientTrajectory x0 xs`.
-/

namespace IsConjugateGradientSequence

/-- Helper for Lemma 1.9.8: each positive-indexed iterate displacement from the initial point lies
in the corresponding Krylov subspace. -/
private theorem iterateDisplacement_mem_krylovSubspace
    {problem : UnconstrainedQuadraticMinimizationProblem n} {x0 : E} {xs : ℕ+ → E}
    (hcg : IsConjugateGradientSequence problem x0 xs) (k : ℕ+) :
    xs k - x0 ∈ 𝓛(problem, x0, k) := by
  -- Unpack affine-search-space membership into a displacement in the direction subspace.
  simpa [UnconstrainedQuadraticMinimizationProblem.affineKrylovSearchSpace] using
    (AffineSubspace.mem_mk').1 (hcg.mem_affineKrylovSearchSpace k)

/-- Every conjugate-gradient step difference belongs to the corresponding Krylov stage. -/
theorem stepDifference_mem_krylovSubspace
    {problem : UnconstrainedQuadraticMinimizationProblem n} {x0 : E} {xs : ℕ+ → E}
    (hcg : IsConjugateGradientSequence problem x0 xs) (k : ℕ) :
    conjugateGradientTrajectory x0 xs (k + 1) - conjugateGradientTrajectory x0 xs k ∈
      𝓛(problem, x0, k.succPNat) := by
  let trajectory : ℕ → E := conjugateGradientTrajectory x0 xs
  cases k with
  | zero =>
      -- The first step is exactly the first iterate displacement from `x0`.
      simpa [trajectory] using
        iterateDisplacement_mem_krylovSubspace hcg (1 : ℕ+)
  | succ k =>
      -- Rewrite the later step as a difference of two iterate displacements from `x0`.
      have hk_mem :
          trajectory (k + 1) - x0 ∈ 𝓛(problem, x0, k.succPNat) := by
        simpa [trajectory] using
          iterateDisplacement_mem_krylovSubspace hcg k.succPNat
      have hk_next_mem :
          trajectory (k + 2) - x0 ∈ 𝓛(problem, x0, (k + 1).succPNat) := by
        simpa [trajectory] using
          iterateDisplacement_mem_krylovSubspace hcg (k + 1).succPNat
      have hk_mem' :
          trajectory (k + 1) - x0 ∈ 𝓛(problem, x0, (k + 1).succPNat) :=
        problem.krylovSubspace_mono x0
          ((Nat.succPNat_le_succPNat).2 (Nat.le_succ k))
          hk_mem
      have hsub :
          trajectory (k + 2) - trajectory (k + 1) =
            (trajectory (k + 2) - x0) - (trajectory (k + 1) - x0) := by
        abel
      rw [hsub]
      exact Submodule.sub_mem _ hk_next_mem hk_mem'

/-- Lemma 1.9.8: along a conjugate-gradient sequence for an unconstrained quadratic problem,
distinct step differences are `A`-orthogonal. -/
-- Proof sketch: the `i`th step difference lies in the owner Krylov space `𝓛ᵢ₊₁`, hence also in
-- every later stage by monotonicity. For `i < k`, Corollary 1.9.7 puts both
-- `∇f(x_k)` and `∇f(x_{k+1})` in `𝓛ₖᗮ`, so their difference is orthogonal to the earlier step.
-- The quadratic gradient identity `∇f(x) = A (x - x*)` then rewrites that gradient difference as
-- `A (x_{k+1} - x_k)`. The reverse order follows from symmetry of `A`.
theorem stepDifferences_pairwise_A_orthogonal
    {problem : UnconstrainedQuadraticMinimizationProblem n} {x0 : E} {xs : ℕ+ → E}
    (hcg : IsConjugateGradientSequence problem x0 xs) {k i : ℕ} (hki : k ≠ i) :
    inner ℝ
      (problem.A.toEuclideanLin
        (conjugateGradientTrajectory x0 xs (k + 1) - conjugateGradientTrajectory x0 xs k))
      (conjugateGradientTrajectory x0 xs (i + 1) - conjugateGradientTrajectory x0 xs i) = 0 := by
  let trajectory : ℕ → E := conjugateGradientTrajectory x0 xs
  have hAstep :
      ∀ k : ℕ,
        problem.A.toEuclideanLin (trajectory (k + 1) - trajectory k) =
          ∇ problem.objective (trajectory (k + 1)) -
            ∇ problem.objective (trajectory k) := by
    intro k
    -- Rewrite the step through the minimizer-centered gradient formula `∇f(x) = A (x - x*)`.
    calc
      problem.A.toEuclideanLin (trajectory (k + 1) - trajectory k)
          = problem.A.toEuclideanLin
              ((trajectory (k + 1) - problem.minimizer) -
                (trajectory k - problem.minimizer)) := by
              congr 1
              abel
      _ = problem.A.toEuclideanLin (trajectory (k + 1) - problem.minimizer) -
            problem.A.toEuclideanLin (trajectory k - problem.minimizer) := by
            rw [LinearMap.map_sub]
      _ = ∇ problem.objective (trajectory (k + 1)) -
            ∇ problem.objective (trajectory k) := by
            rw [problem.gradient_eq, problem.gradient_eq]
  have hlt :
      ∀ {a b : ℕ},
        a < b →
          inner ℝ (problem.A.toEuclideanLin (trajectory (b + 1) - trajectory b))
            (trajectory (a + 1) - trajectory a) = 0 := by
    intro a b hab
    obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Nat.zero_lt_of_lt hab))
    -- Put the earlier step into the later Krylov stage and then use orthogonality of the two
    -- consecutive gradients to that stage.
    have hstep_a :
        trajectory (a + 1) - trajectory a ∈ 𝓛(problem, x0, c.succPNat) := by
      exact
        problem.krylovSubspace_mono x0
          ((Nat.succPNat_le_succPNat).2 (Nat.lt_succ_iff.mp hab))
          (hcg.stepDifference_mem_krylovSubspace a)
    have hgrad_b :
        ∇ problem.objective (trajectory (c + 1)) ∈ (𝓛(problem, x0, c.succPNat))ᗮ := by
      simpa [trajectory] using
        hcg.gradient_mem_krylovSubspace_orthogonal c.succPNat
    have hgrad_b_succ' :
        ∇ problem.objective (trajectory (c + 2)) ∈
          (𝓛(problem, x0, (c + 1).succPNat))ᗮ := by
      simpa [trajectory] using
        hcg.gradient_mem_krylovSubspace_orthogonal (c + 1).succPNat
    have hgrad_b_succ :
        ∇ problem.objective (trajectory (c + 2)) ∈ (𝓛(problem, x0, c.succPNat))ᗮ :=
      Submodule.orthogonal_le
        (problem.krylovSubspace_mono x0
          ((Nat.succPNat_le_succPNat).2 (Nat.le_succ c)))
        hgrad_b_succ'
    have hinner :
        inner ℝ
          (∇ problem.objective (trajectory (c + 2)) -
            ∇ problem.objective (trajectory (c + 1)))
          (trajectory (a + 1) - trajectory a) = 0 := by
      exact
        (Submodule.mem_orthogonal' _ _).1
          (Submodule.sub_mem _ hgrad_b_succ hgrad_b)
          _
          hstep_a
    rw [hAstep (c + 1)]
    exact hinner
  have hswap :
      ∀ a b : ℕ,
        inner ℝ (problem.A.toEuclideanLin (trajectory (a + 1) - trajectory a))
          (trajectory (b + 1) - trajectory b) =
        inner ℝ (problem.A.toEuclideanLin (trajectory (b + 1) - trajectory b))
          (trajectory (a + 1) - trajectory a) := by
    intro a b
    -- Symmetry of the quadratic form lets us swap the two step differences.
    simpa [trajectory, real_inner_comm] using
      problem.matrix_inner_apply_swap
        (trajectory (a + 1) - trajectory a)
        (trajectory (b + 1) - trajectory b)
  rcases lt_or_gt_of_ne hki with hki | hki
  · rw [hswap k i]
    exact hlt hki
  · simpa [trajectory] using hlt hki

end IsConjugateGradientSequence
