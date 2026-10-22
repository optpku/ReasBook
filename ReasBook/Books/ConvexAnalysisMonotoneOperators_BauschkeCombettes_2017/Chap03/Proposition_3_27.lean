/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Data.List.TFAE
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Definition_3_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_16_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_16_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace
open ContinuousLinearMap

universe u v

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- The orthogonal projection of `K` onto the closed range of `T`. -/
noncomputable abbrev closedRangeProjection (T : H →L[ℝ] K)
    (hclosed : IsClosed (T.range : Set K)) : K →L[ℝ] K :=
  letI : CompleteSpace T.range := hclosed.completeSpace_coe
  T.range.starProjection

-- Proof sketch: `closedRangeProjection T hclosed` is the star projection onto the subspace
-- `T.range`, so its values belong to `T.range` by `Submodule.starProjection_apply_mem`.
/-- The orthogonal projection onto the closed range of `T` takes values in `range T`. -/
theorem closedRangeProjection_mem_range (T : H →L[ℝ] K)
    (hclosed : IsClosed (T.range : Set K)) (y : K) :
    closedRangeProjection T hclosed y ∈ T.range := by
  letI : CompleteSpace T.range := hclosed.completeSpace_coe
  simpa [closedRangeProjection] using T.range.starProjection_apply_mem y

/-- The orthogonal projection onto the closed range fixes every point already in the range. -/
theorem closedRangeProjection_eq_self_of_mem_range (T : H →L[ℝ] K)
    (hclosed : IsClosed (T.range : Set K)) {y : K} (hy : y ∈ T.range) :
    closedRangeProjection T hclosed y = y := by
  letI : CompleteSpace T.range := hclosed.completeSpace_coe
  simpa [closedRangeProjection] using (T.range.starProjection_eq_self_iff).2 hy

/-- The orthogonal projection onto the closed range vanishes on the orthogonal complement of that
range. -/
theorem closedRangeProjection_eq_zero_of_mem_orthogonalRange (T : H →L[ℝ] K)
    (hclosed : IsClosed (T.range : Set K)) {y : K} (hy : y ∈ T.rangeᗮ) :
    closedRangeProjection T hclosed y = 0 := by
  letI : CompleteSpace T.range := hclosed.completeSpace_coe
  simpa [closedRangeProjection] using (T.range.starProjection_apply_eq_zero_iff).2 hy

/-- `x` is a least-squares solution of `T z = y` if it minimizes `z ↦ ‖T z - y‖`. -/
abbrev IsLeastSquaresSolution (T : H →L[ℝ] K) (y : K) (x : H) : Prop :=
  ∀ z : H, ‖T x - y‖ ≤ ‖T z - y‖

-- Proof sketch: unfold `IsLeastSquaresSolution`.
/-- The least-squares predicate is the minimization condition for the residual norm. -/
theorem isLeastSquaresSolution_iff (T : H →L[ℝ] K) (y : K) (x : H) :
    IsLeastSquaresSolution T y x ↔ ∀ z : H, ‖T x - y‖ ≤ ‖T z - y‖ := by
  -- This theorem is just the definitional unfolding of `IsLeastSquaresSolution`.
  rfl

/-- Helper for Proposition 3.27: the orthogonal projection onto the closed range agrees with the
metric projection onto `range T`. -/
lemma closedRangeProjection_eq_projectionPoint (T : H →L[ℝ] K)
    (hclosed : IsClosed (T.range : Set K)) (y : K) :
    closedRangeProjection T hclosed y =
      projectionPoint (T.range : Set K)
        (isChebyshev_of_nonempty_isClosed_convex
          (show (T.range : Set K).Nonempty by
            refine ⟨0, ?_⟩
            exact ⟨0, by simp⟩)
          hclosed T.range.convex) y := by
  have hp_mem : closedRangeProjection T hclosed y ∈ (T.range : Set K) := by
    simpa using closedRangeProjection_mem_range T hclosed y
  have horth : y - closedRangeProjection T hclosed y ∈ (T.range : Submodule ℝ K)ᗮ := by
    letI : CompleteSpace T.range := hclosed.completeSpace_coe
    simpa [closedRangeProjection] using T.range.sub_starProjection_mem_orthogonal y
  refine
    (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
      (show (T.range : Set K).Nonempty by
        refine ⟨0, ?_⟩
        exact ⟨0, by simp⟩)
      hclosed T.range.convex).2 ?_
  refine ⟨hp_mem, ?_⟩
  intro r hr
  have hr_sub : r - closedRangeProjection T hclosed y ∈ (T.range : Submodule ℝ K) := by
    exact Submodule.sub_mem T.range hr hp_mem
  have hzero :=
    (Submodule.mem_orthogonal' (T.range : Submodule ℝ K)
      (y - closedRangeProjection T hclosed y)).1 horth
      (r - closedRangeProjection T hclosed y) hr_sub
  simpa [real_inner_comm] using le_of_eq hzero

/-- Helper for Proposition 3.27: minimizing the residual over `H` is equivalent to saying that
`T x` is a best approximation to `y` from `range T`. -/
lemma isLeastSquaresSolution_iff_isBestApproximation_range (T : H →L[ℝ] K)
    (y : K) (x : H) :
    IsLeastSquaresSolution T y x ↔ IsBestApproximation y (T.range : Set K) (T x) := by
  constructor
  · intro hx
    rw [isBestApproximation_iff_mem_and_dist_eq_infDist]
    refine ⟨⟨x, rfl⟩, ?_⟩
    -- The residual at `x` is a lower bound for all residuals coming from the range, and it is
    -- attained at the range point `T x`.
    rw [Metric.infDist_eq_iInf, dist_eq_norm, norm_sub_rev]
    refine le_antisymm ?_ ?_
    · show ‖T x - y‖ ≤ ⨅ r : T.range, dist y (r : K)
      refine le_ciInf ?_
      intro r
      rcases r with ⟨r, ⟨z, rfl⟩⟩
      simpa [dist_eq_norm, norm_sub_rev] using hx z
    · simpa [dist_eq_norm, norm_sub_rev] using
        (ciInf_le
          (show BddBelow (Set.range (fun r : T.range ↦ dist y (r : K))) by
            refine ⟨0, ?_⟩
            rintro _ ⟨r, rfl⟩
            exact dist_nonneg)
          (⟨T x, ⟨x, rfl⟩⟩ : T.range) :
          (⨅ r : T.range, dist y (r : K)) ≤ dist y ((⟨T x, ⟨x, rfl⟩⟩ : T.range) : K))
  · intro hx
    rw [isBestApproximation_iff_mem_and_dist_eq_infDist] at hx
    intro z
    have hle : Metric.infDist y (T.range : Set K) ≤ ‖T z - y‖ := by
      have hdist : Metric.infDist y (T.range : Set K) ≤ dist y (T z) :=
        Metric.infDist_le_dist_of_mem (show T z ∈ (T.range : Set K) by exact ⟨z, rfl⟩)
      simpa [dist_eq_norm, norm_sub_rev] using hdist
    calc
      ‖T x - y‖ = dist y (T x) := by rw [dist_comm, dist_eq_norm]
      _ = Metric.infDist y (T.range : Set K) := hx.2
      _ ≤ ‖T z - y‖ := hle

/-- Helper for Proposition 3.27: a least-squares solution is exactly a point whose image is the
orthogonal projection of `y` onto `range T`. -/
lemma isLeastSquaresSolution_iff_eq_closedRangeProjection (T : H →L[ℝ] K)
    (hclosed : IsClosed (T.range : Set K)) (y : K) (x : H) :
    IsLeastSquaresSolution T y x ↔ T x = closedRangeProjection T hclosed y := by
  let hCheb :=
    isChebyshev_of_nonempty_isClosed_convex
      (show (T.range : Set K).Nonempty by
        refine ⟨0, ?_⟩
        exact ⟨0, by simp⟩)
      hclosed T.range.convex
  constructor
  · intro hx
    have hbest : IsBestApproximation y (T.range : Set K) (T x) :=
      (isLeastSquaresSolution_iff_isBestApproximation_range T y x).1 hx
    -- Uniqueness of best approximations in the closed convex range identifies `T x` with the
    -- canonical projection point.
    have hproj : T x = projectionPoint (T.range : Set K) hCheb y := by
      exact (hCheb y).unique hbest
        (projectionPoint_isBestApproximation (T.range : Set K) hCheb y)
    simpa [closedRangeProjection_eq_projectionPoint T hclosed y] using hproj
  · intro hx
    have hproj : T x = projectionPoint (T.range : Set K) hCheb y := by
      simpa [closedRangeProjection_eq_projectionPoint T hclosed y] using hx
    have hbest : IsBestApproximation y (T.range : Set K) (T x) := by
      simpa [hproj] using
        (projectionPoint_isBestApproximation (T.range : Set K) hCheb y)
    exact (isLeastSquaresSolution_iff_isBestApproximation_range T y x).2 hbest

/-- Helper for Proposition 3.27: the projection identity is equivalent to the normal equation. -/
lemma eq_closedRangeProjection_iff_normal_equation (T : H →L[ℝ] K)
    (hclosed : IsClosed (T.range : Set K)) (y : K) (x : H) :
    T x = closedRangeProjection T hclosed y ↔
      adjoint T (T x) = adjoint T y := by
  constructor
  · intro hx
    have horth : y - T x ∈ (T.range : Submodule ℝ K)ᗮ := by
      letI : CompleteSpace T.range := hclosed.completeSpace_coe
      simpa [hx, closedRangeProjection] using T.range.sub_starProjection_mem_orthogonal y
    have hker : y - T x ∈ (adjoint T).ker := by
      simpa [ContinuousLinearMap.orthogonal_range] using horth
    have hzero : adjoint T (y - T x) = 0 := hker
    have hsub : adjoint T y - adjoint T (T x) = 0 := by
      simpa [ContinuousLinearMap.map_sub] using hzero
    exact (sub_eq_zero.mp hsub).symm
  · intro hEq
    have hsub : adjoint T y - adjoint T (T x) = 0 := by
      rw [hEq, sub_self]
    have hzero : adjoint T (y - T x) = 0 := by
      simpa [ContinuousLinearMap.map_sub] using hsub
    have hker : y - T x ∈ (adjoint T).ker := hzero
    have horth : y - T x ∈ (T.range : Submodule ℝ K)ᗮ := by
      simpa [ContinuousLinearMap.orthogonal_range] using hker
    have hx_mem : T x ∈ (T.range : Submodule ℝ K) := ⟨x, rfl⟩
    letI : CompleteSpace T.range := hclosed.completeSpace_coe
    have hproj :=
      T.range.eq_starProjection_of_mem_orthogonal hx_mem horth
    simpa [closedRangeProjection] using hproj.symm

-- Proof sketch: project `y` orthogonally onto the closed subspace `T.range`, use that the
-- projection point lies in `T.range` to obtain some `x` with `T x = closedRangeProjection T hclosed y`,
-- characterize best approximation in a closed subspace by the orthogonal projection, and rewrite the
-- orthogonality condition by the adjoint identity to obtain the normal equation.
/-- Proposition 3.27: if `range T` is closed, then the least-squares problem
`min_z ‖T z - y‖` admits a solution, and for every `x` the following are equivalent:
`x` is a least-squares solution, `T x` is the orthogonal projection of `y` onto `range T`,
and `T† (T x) = T† y`. -/
theorem leastSquares_tfae_and_exists_of_closed_range (T : H →L[ℝ] K)
    (hclosed : IsClosed (T.range : Set K)) (y : K) :
    (∃ x : H, IsLeastSquaresSolution T y x) ∧
      ∀ x : H, List.TFAE
        [IsLeastSquaresSolution T y x,
          T x = closedRangeProjection T hclosed y,
          adjoint T (T x) = adjoint T y] := by
  refine ⟨?_, ?_⟩
  · rcases closedRangeProjection_mem_range T hclosed y with ⟨x₀, hx₀⟩
    -- A preimage of the closed-range projection provides a least-squares solution.
    refine ⟨x₀, ?_⟩
    exact (isLeastSquaresSolution_iff_eq_closedRangeProjection T hclosed y x₀).2 hx₀
  · intro x
    -- The source proof decomposes the equivalence into the geometric projection criterion and the
    -- normal equation, then closes the three-way equivalence.
    tfae_have 1 ↔ 2 := by
      exact isLeastSquaresSolution_iff_eq_closedRangeProjection T hclosed y x
    tfae_have 2 ↔ 3 := by
      exact eq_closedRangeProjection_iff_normal_equation T hclosed y x
    tfae_finish
