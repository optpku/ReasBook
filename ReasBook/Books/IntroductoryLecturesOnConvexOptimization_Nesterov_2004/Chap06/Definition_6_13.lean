/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_11
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Lemma_6_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Remark_6_1_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open scoped StandardSimplex

noncomputable section

/- Definition 6.13 lies in the finite simplex / Euclidean prox-function domain.

Sampled owner declarations:
* mathlib `stdSimplex`, the canonical owner of the standard simplex;
* mathlib `stdSimplex_eq_inter`, the canonical set-level expansion of simplex membership;
* mathlib `stdSimplex.barycenter` and `stdSimplex.barycenter_apply`, the canonical simplex center;
* project `quadraticDistanceTo`, the chapter owner of the Euclidean prox term.

Best owner abstraction:
* source-facing: the Euclidean prox function on `Δ_n` centered at the canonical simplex
  barycenter;
* core/canonical: `stdSimplex.barycenter` and `quadraticDistanceTo` on
  `EuclideanSpace ℝ (Fin n)`, together with the canonical simplex owner `stdSimplex`;
* bridge/view: the Euclidean-coordinate realization `stdSimplexBarycenterEuclidean n`, and
  restriction of the Euclidean prox owner along the coordinate equivalence
  `EuclideanSpace.equiv (Fin n) ℝ`.

Primitive data:
* the positive dimension `n : ℕ+`.

Derived API:
* the upstream Euclidean bridge `stdSimplexBarycenterEuclidean n`;
* the coordinate formula for the Euclidean prox function.

Source/core/bridge triage:
* core/canonical: `stdSimplex.barycenter`;
* bridge/view: `stdSimplexBarycenterEuclidean` from `Lemma_6_3`;
* the prox function is then the restriction of the Euclidean owner
  `quadraticDistanceTo (stdSimplexBarycenterEuclidean n)` along
  `(EuclideanSpace.equiv (Fin n) ℝ).symm`.

The duplicate public owner `simplexUniformPoint` has been deleted. Its only content was the earlier
Euclidean realization of the canonical simplex barycenter, so keeping it violated the project’s
owner/bridge discipline. The prior `simplexEuclideanProxFunction` body also applied
`quadraticDistanceTo` directly on the subtype carrier `Fin n → ℝ`, which silently switched the
ambient norm to the product sup norm; the corrected bridge keeps the Euclidean owner on
`EuclideanSpace ℝ (Fin n)` via `stdSimplexBarycenterEuclidean`. -/

/-- Euclidean prox choice from Definition 6.13 on `Δ_n`: the restriction of the ambient
Euclidean prox owner centered at the canonical simplex barycenter `(1 / n, ..., 1 / n)`. The
simplex subtype is viewed in Euclidean coordinates through `(EuclideanSpace.equiv (Fin n) ℝ).symm`.
-/
abbrev simplexEuclideanProxFunction (n : ℕ+) : Δ[n] → ℝ :=
  fun x ↦
    quadraticDistanceTo (stdSimplexBarycenterEuclidean n) ((EuclideanSpace.equiv (Fin n) ℝ).symm x)

/-- Helper for Definition 6.13: each coordinate of the Euclidean realization of the simplex
barycenter is `(1 : ℝ) / n`. -/
theorem stdSimplexBarycenterEuclidean_apply (n : ℕ+) (i : Fin n) :
    (stdSimplexBarycenterEuclidean n).ofLp i = (1 : ℝ) / n := by
  -- Rewrite the canonical simplex barycenter coordinate, then transport it through the Euclidean
  -- coordinate equivalence used to define `stdSimplexBarycenterEuclidean`.
  have hcoord :
      (stdSimplex.barycenter : Δ[n]) i = (Fintype.card (Fin (n : ℕ)) : ℝ)⁻¹ :=
    stdSimplex.barycenter_apply i
  simpa [stdSimplexBarycenterEuclidean, Fintype.card_fin, one_div] using hcoord

-- Proof sketch: unfold `simplexEuclideanProxFunction`; then expand `quadraticDistanceTo` at the
-- Euclidean center `stdSimplexBarycenterEuclidean n`, rewrite the squared Euclidean norm by
-- `EuclideanSpace.real_norm_sq_eq`, evaluate the transported simplex point coordinatewise through
-- `EuclideanSpace.equiv`, and use `stdSimplex.barycenter_apply`.
/-- Definition 6.13: expanding `simplexEuclideanProxFunction n` gives the textbook formula
`(1 / 2) * Σ_i (x_i - 1 / n)^2`. -/
theorem simplexEuclideanProxFunction_apply (n : ℕ+) (x : Δ[n]) :
    simplexEuclideanProxFunction n x =
      (1 / 2 : ℝ) * ∑ i : Fin n, (x i - (1 : ℝ) / n) ^ (2 : ℕ) := by
  -- Expand the prox owner once so the goal is a squared Euclidean norm centered at the barycenter.
  rw [simplexEuclideanProxFunction, quadraticDistanceTo_apply]
  -- Normalize the Euclidean norm square into the coordinate sum from the textbook formula.
  rw [EuclideanSpace.real_norm_sq_eq]
  -- Rewrite the normalized sum termwise, using the canonical barycenter coordinate formula.
  have hsum :
      ∑ i : Fin n,
          (((EuclideanSpace.equiv (Fin n) ℝ).symm x - stdSimplexBarycenterEuclidean n).ofLp i) ^
            (2 : ℕ)
        =
          ∑ i : Fin n, (x i - (1 : ℝ) / n) ^ (2 : ℕ) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hcoord :
        ((EuclideanSpace.equiv (Fin n) ℝ).symm x - stdSimplexBarycenterEuclidean n).ofLp i =
          x i - (1 : ℝ) / n := by
      have hbary : (stdSimplex.barycenter : Δ[n]) i = (1 : ℝ) / n := by
        calc
          (stdSimplex.barycenter : Δ[n]) i = (Fintype.card (Fin (n : ℕ)) : ℝ)⁻¹ :=
            stdSimplex.barycenter_apply i
          _ = (1 : ℝ) / n := by
            simp [Fintype.card_fin, one_div]
      simp [hbary]
    exact congrArg (fun t : ℝ ↦ t ^ (2 : ℕ)) hcoord
  rw [hsum]
