/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Definition_3_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

/-- Helper for Remark 3.11.2: the orthogonal projection minimizes the distance to the
finite-dimensional subspace among all comparison points in that subspace. -/
private lemma orthogonalProjection_dist_le (C : Submodule ℝ 𝓗)
    [FiniteDimensional ℝ C] (x : 𝓗) {c : 𝓗} (hc : c ∈ (C : Set 𝓗)) :
    dist x (C.orthogonalProjection x : 𝓗) ≤ dist x c := by
  let p : 𝓗 := C.orthogonalProjection x
  have hp : p ∈ (C : Set 𝓗) := by
    exact (C.orthogonalProjection x).property
  -- The residual `x - p` is orthogonal to `C`, so it is orthogonal to every competitor direction.
  have hperp : x - p ∈ Cᗮ := by
    change x - C.starProjection x ∈ Cᗮ
    simp
  have hpc : p - c ∈ C := by
    exact Submodule.sub_mem C hp hc
  have hinner : inner ℝ (x - p) (p - c) = 0 :=
    Submodule.inner_left_of_mem_orthogonal hpc hperp
  -- Pythagoras compares the squared distances once `x - c` is decomposed into orthogonal pieces.
  have hsq : ‖x - p + (p - c)‖ ^ 2 = ‖x - p‖ ^ 2 + ‖p - c‖ ^ 2 := by
    simpa [pow_two] using
      (norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x - p) (p - c) hinner)
  have hdistsq : dist x c ^ 2 = dist x p ^ 2 + ‖p - c‖ ^ 2 := by
    rw [dist_eq_norm, dist_eq_norm, ← sub_add_sub_cancel x p c, hsq]
  have hnonneg : 0 ≤ ‖p - c‖ ^ 2 := by
    positivity
  have hpnonneg : 0 ≤ dist x p := dist_nonneg
  have hcnonneg : 0 ≤ dist x c := dist_nonneg
  nlinarith [hdistsq, hnonneg, hpnonneg, hcnonneg]

/-- Helper for Remark 3.11.2: the orthogonal projection is a best approximation in the canonical
`IsBestApproximation` API. -/
private theorem orthogonalProjection_isBestApproximation (C : Submodule ℝ 𝓗)
    [FiniteDimensional ℝ C] (x : 𝓗) :
    IsBestApproximation x (C : Set 𝓗) (C.orthogonalProjection x : 𝓗) := by
  rw [isBestApproximation_iff_mem_and_dist_eq_infDist]
  constructor
  · exact (C.orthogonalProjection x).property
  · refine le_antisymm ?_ (Metric.infDist_le_dist_of_mem (C.orthogonalProjection x).property)
    exact (Metric.le_infDist ⟨(C.orthogonalProjection x : 𝓗), (C.orthogonalProjection x).property⟩).2
      fun y hy ↦ orthogonalProjection_dist_le C x hy

/-- Helper for Remark 3.11.2: any point of the subspace that realizes the infimal distance must
coincide with the orthogonal projection. -/
private lemma bestApproximation_eq_orthogonalProjection (C : Submodule ℝ 𝓗)
    [FiniteDimensional ℝ C] {x q : 𝓗} (hq : q ∈ (C : Set 𝓗))
    (hqdist : dist x q = Metric.infDist x (C : Set 𝓗)) :
    q = (C.orthogonalProjection x : 𝓗) := by
  let p : 𝓗 := C.orthogonalProjection x
  have hp : p ∈ (C : Set 𝓗) := by
    exact (C.orthogonalProjection x).property
  have hpdist : dist x p = Metric.infDist x (C : Set 𝓗) := by
    simpa [p] using
      (isBestApproximation_iff_mem_and_dist_eq_infDist x (C : Set 𝓗) (C.orthogonalProjection x : 𝓗)).1
        (orthogonalProjection_isBestApproximation C x) |>.2
  have hdist : dist x q = dist x p := by
    rw [hqdist, hpdist]
  -- Reuse the same orthogonal decomposition, now with `q` as another minimizing point.
  have hperp : x - p ∈ Cᗮ := by
    change x - C.starProjection x ∈ Cᗮ
    simp
  have hpq : p - q ∈ C := by
    exact Submodule.sub_mem C hp hq
  have hinner : inner ℝ (x - p) (p - q) = 0 :=
    Submodule.inner_left_of_mem_orthogonal hpq hperp
  have hsq : ‖x - p + (p - q)‖ ^ 2 = ‖x - p‖ ^ 2 + ‖p - q‖ ^ 2 := by
    simpa [pow_two] using
      (norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x - p) (p - q) hinner)
  have hdistsq : dist x q ^ 2 = dist x p ^ 2 + ‖p - q‖ ^ 2 := by
    rw [dist_eq_norm, dist_eq_norm, ← sub_add_sub_cancel x p q, hsq]
  have hsamedist : dist x q ^ 2 = dist x p ^ 2 := by
    rw [hdist]
  have hnormsq : ‖p - q‖ ^ 2 = 0 := by
    nlinarith [hdistsq, hsamedist, sq_nonneg ‖p - q‖]
  have hnorm : ‖p - q‖ = 0 := by
    nlinarith
  have hpqeq : p - q = 0 := norm_eq_zero.mp hnorm
  simpa [p] using (sub_eq_zero.mp hpqeq).symm

/-- Helper for Remark 3.11.2: orthogonal projection is the unique best approximation in the
finite-dimensional subspace. -/
private theorem eq_orthogonalProjection_of_isBestApproximation (C : Submodule ℝ 𝓗)
    [FiniteDimensional ℝ C] {x q : 𝓗} (hq : IsBestApproximation x (C : Set 𝓗) q) :
    q = (C.orthogonalProjection x : 𝓗) := by
  exact bestApproximation_eq_orthogonalProjection C hq.1 hq.2

-- Proof sketch: finite-dimensional subspaces are complete, hence admit orthogonal projections.
-- For each `x`, take `p := (C.orthogonalProjection x : 𝓗)`. The residual `x - p` is orthogonal to
-- `C`, so the Pythagorean identity shows `p` realizes `Metric.infDist x (C : Set 𝓗)`. Uniqueness
-- follows because two minimizers differ by a vector of `C` orthogonal to itself.
/-- Remark 3.11.2: every finite-dimensional linear subspace of a real Hilbert space admits a unique
best approximation to each point of the ambient space. -/
theorem finiteDimensionalSubspace_has_unique_best_approximations [CompleteSpace 𝓗]
    (C : Submodule ℝ 𝓗) [FiniteDimensional ℝ C] :
    IsChebyshev (C : Set 𝓗) := by
  intro x
  refine ⟨C.orthogonalProjection x, orthogonalProjection_isBestApproximation C x, ?_⟩
  -- Any other minimizing point must equal the orthogonal projection by the uniqueness helper.
  intro q hq
  exact eq_orthogonalProjection_of_isBestApproximation C hq

/- Every finite-dimensional linear subspace is closed by the canonical mathlib theorem
`Submodule.closed_of_finiteDimensional`. -/
recall Submodule.closed_of_finiteDimensional
