/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Definition_3_26
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_16_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open ContinuousLinearMap
open scoped InnerProductSpace

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
variable {𝓚 : Type v} [NormedAddCommGroup 𝓚] [InnerProductSpace ℝ 𝓚] [CompleteSpace 𝓚]

/-- The normal-equation solution set is a closed set, being the preimage of a singleton under the
continuous map `x ↦ T* (T x)`. -/
private theorem isClosed_moorePenroseSolutionSet
    (T : 𝓗 →L[ℝ] 𝓚) (y : 𝓚) :
    IsClosed (moorePenroseSolutionSet T y) := by
  let A : 𝓗 →L[ℝ] 𝓗 := (adjoint T).comp T
  change IsClosed (A ⁻¹' {adjoint T y})
  exact isClosed_singleton.preimage A.continuous

/-- Once nonempty, the normal-equation solution set is an affine subspace translate, hence equals
its affine span. -/
private theorem affineSpan_moorePenroseSolutionSet
    (T : 𝓗 →L[ℝ] 𝓚) (y : 𝓚)
    (h_nonempty : (moorePenroseSolutionSet T y).Nonempty) :
    (affineSpan ℝ (moorePenroseSolutionSet T y) : Set 𝓗) = moorePenroseSolutionSet T y := by
  rcases h_nonempty with ⟨z, hz⟩
  let A : 𝓗 →L[ℝ] 𝓗 := (adjoint T).comp T
  have hset :
      moorePenroseSolutionSet T y = (AffineSubspace.mk' z A.ker : Set 𝓗) := by
    ext x
    rw [mem_moorePenroseSolutionSet_iff]
    change (adjoint T (T x) = adjoint T y) ↔ x ∈ AffineSubspace.mk' z A.ker
    rw [AffineSubspace.mem_mk', LinearMap.mem_ker]
    constructor
    · intro hx
      have hsub : A x - A z = 0 := by
        change adjoint T (T x) - adjoint T (T z) = 0
        rw [hx, (mem_moorePenroseSolutionSet_iff T y z).mp hz, sub_self]
      simpa [A, map_sub] using hsub
    · intro hx
      have hzero : A (x - z) = 0 := by simpa [A] using hx
      have hsub : A x - A z = 0 := by simpa [map_sub] using hzero
      rw [sub_eq_zero] at hsub
      exact hsub.trans ((mem_moorePenroseSolutionSet_iff T y z).mp hz)
  rw [hset]
  exact congrArg (fun Q : AffineSubspace ℝ 𝓗 ↦ (Q : Set 𝓗))
    (AffineSubspace.affineSpan_coe (AffineSubspace.mk' z A.ker))

/-- A nonempty affine set is convex, so the nonempty normal-equation solution set is convex. -/
private theorem moorePenroseSolutionSet_convex
    (T : 𝓗 →L[ℝ] 𝓚) (y : 𝓚)
    (h_nonempty : (moorePenroseSolutionSet T y).Nonempty) :
    Convex ℝ (moorePenroseSolutionSet T y) := by
  rw [← affineSpan_moorePenroseSolutionSet T y h_nonempty]
  exact (affineSpan ℝ (moorePenroseSolutionSet T y)).convex

private theorem isChebyshev_moorePenroseSolutionSet_of_nonempty_isClosed_affine
    (T : 𝓗 →L[ℝ] 𝓚) (y : 𝓚)
    (h_nonempty : (moorePenroseSolutionSet T y).Nonempty) :
    IsChebyshev (moorePenroseSolutionSet T y) :=
  isChebyshev_of_nonempty_isClosed_convex h_nonempty
    (isClosed_moorePenroseSolutionSet T y)
    (moorePenroseSolutionSet_convex T y h_nonempty)

/-- Definition 3.27.1: if the normal-equation solution set `{x | T* (T x) = T* y}` is nonempty,
its minimal-norm element is the metric projection of `0` onto that closed affine set. -/
noncomputable def minimalNormLeastSquaresSolution
    (T : 𝓗 →L[ℝ] 𝓚) (y : 𝓚)
    (h_nonempty : (moorePenroseSolutionSet T y).Nonempty) : 𝓗 :=
  projectionPoint (moorePenroseSolutionSet T y)
    (isChebyshev_moorePenroseSolutionSet_of_nonempty_isClosed_affine T y h_nonempty)
    0

/-- Definition 3.27.1, unfolded: the minimal-norm least-squares solution is the projection of `0`
onto the normal-equation solution set. -/
private theorem minimalNormLeastSquaresSolution_eq_projectionPoint
    (T : 𝓗 →L[ℝ] 𝓚) (y : 𝓚)
    (h_nonempty : (moorePenroseSolutionSet T y).Nonempty) :
    minimalNormLeastSquaresSolution T y h_nonempty =
      projectionPoint (moorePenroseSolutionSet T y)
        (isChebyshev_moorePenroseSolutionSet_of_nonempty_isClosed_affine T y h_nonempty) 0 :=
  rfl

/-- The point introduced in Definition 3.27.1 is a best approximation of `0` from the
normal-equation solution set. -/
theorem minimalNormLeastSquaresSolution_isBestApproximation
    (T : 𝓗 →L[ℝ] 𝓚) (y : 𝓚)
    (h_nonempty : (moorePenroseSolutionSet T y).Nonempty) :
    IsBestApproximation (0 : 𝓗) (moorePenroseSolutionSet T y)
      (minimalNormLeastSquaresSolution T y h_nonempty) := by
  simpa [minimalNormLeastSquaresSolution] using
    projectionPoint_isBestApproximation (moorePenroseSolutionSet T y)
      (isChebyshev_moorePenroseSolutionSet_of_nonempty_isClosed_affine T y h_nonempty)
      (0 : 𝓗)

/-- The point from Definition 3.27.1 belongs to the normal-equation solution set. -/
theorem minimalNormLeastSquaresSolution_mem
    (T : 𝓗 →L[ℝ] 𝓚) (y : 𝓚)
    (h_nonempty : (moorePenroseSolutionSet T y).Nonempty) :
    minimalNormLeastSquaresSolution T y h_nonempty ∈ moorePenroseSolutionSet T y := by
  exact
    projectionPoint_mem (moorePenroseSolutionSet T y)
      (isChebyshev_moorePenroseSolutionSet_of_nonempty_isClosed_affine T y h_nonempty)
      (0 : 𝓗)

/-- The point from Definition 3.27.1 satisfies the normal equation. -/
theorem minimalNormLeastSquaresSolution_normalEquation
    (T : 𝓗 →L[ℝ] 𝓚) (y : 𝓚)
    (h_nonempty : (moorePenroseSolutionSet T y).Nonempty) :
    adjoint T (T (minimalNormLeastSquaresSolution T y h_nonempty)) = adjoint T y := by
  exact (mem_moorePenroseSolutionSet_iff T y (minimalNormLeastSquaresSolution T y h_nonempty)).mp
    (minimalNormLeastSquaresSolution_mem T y h_nonempty)

/-- The point selected in Definition 3.27.1 has minimal norm among all normal-equation
solutions. -/
theorem norm_minimalNormLeastSquaresSolution_le
    (T : 𝓗 →L[ℝ] 𝓚) (y : 𝓚)
    (h_nonempty : (moorePenroseSolutionSet T y).Nonempty)
    {x : 𝓗} (hx : x ∈ moorePenroseSolutionSet T y) :
    ‖minimalNormLeastSquaresSolution T y h_nonempty‖ ≤ ‖x‖ := by
  have hbest := minimalNormLeastSquaresSolution_isBestApproximation T y h_nonempty
  calc
    ‖minimalNormLeastSquaresSolution T y h_nonempty‖ =
        dist (0 : 𝓗) (minimalNormLeastSquaresSolution T y h_nonempty) := by
          simp
    _ = Metric.infDist (0 : 𝓗) (moorePenroseSolutionSet T y) := hbest.2
    _ ≤ dist (0 : 𝓗) x := Metric.infDist_le_dist_of_mem hx
    _ = ‖x‖ := by simp
