/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Definition_3_27_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open ContinuousLinearMap
open scoped InnerProductSpace

variable {𝓗 : Type u} {𝓚 : Type v}
variable [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
variable [NormedAddCommGroup 𝓚] [InnerProductSpace ℝ 𝓚] [CompleteSpace 𝓚]

private theorem moorePenroseSolutionSet_nonempty_of_closed_range
    (T : 𝓗 →L[ℝ] 𝓚) (hT_closed : IsClosed (T.range : Set 𝓚)) (y : 𝓚) :
    (moorePenroseSolutionSet T y).Nonempty := by
  rcases isChebyshev_moorePenroseSolutionSet T hT_closed y 0 with ⟨x, hx, _⟩
  exact ⟨x, hx.1⟩

/-- Definition 3.28: for a bounded operator `T : 𝓗 →L[ℝ] 𝓚` with closed range, the generalized
(Moore-Penrose) inverse sends `y` to the metric projection of `0` onto the affine solution set
`{x | T* (T x) = T* y}`. -/
noncomputable def moorePenroseInverse (T : 𝓗 →L[ℝ] 𝓚)
    (hT_closed : IsClosed (T.range : Set 𝓚)) : 𝓚 → 𝓗 :=
  fun y ↦ minimalNormLeastSquaresSolution T y
    (moorePenroseSolutionSet_nonempty_of_closed_range T hT_closed y)

/-- Definition 3.28, in unfolded form: the generalized inverse is the projection of `0` onto the
normal-equation solution set. -/
theorem moorePenroseInverse_eq_projectionPoint_moorePenroseSolutionSet
    (T : 𝓗 →L[ℝ] 𝓚) (hT_closed : IsClosed (T.range : Set 𝓚)) (y : 𝓚) :
    moorePenroseInverse T hT_closed y =
      projectionPoint (moorePenroseSolutionSet T y)
        (isChebyshev_moorePenroseSolutionSet T hT_closed y) 0 := by
  have hbest : IsBestApproximation (0 : 𝓗) (moorePenroseSolutionSet T y)
      (moorePenroseInverse T hT_closed y) := by
    simpa [moorePenroseInverse] using minimalNormLeastSquaresSolution_isBestApproximation T y
      (moorePenroseSolutionSet_nonempty_of_closed_range T hT_closed y)
  exact
    (isChebyshev_moorePenroseSolutionSet T hT_closed y 0).unique hbest
      (projectionPoint_isBestApproximation (moorePenroseSolutionSet T y)
        (isChebyshev_moorePenroseSolutionSet T hT_closed y) 0)

-- Proof sketch: unfold `moorePenroseInverse` and apply `projectionPoint_mem` to the Chebyshev set
-- `moorePenroseSolutionSet T y`.
/-- The generalized inverse value belongs to the normal-equation solution set. -/
theorem moorePenroseInverse_mem_moorePenroseSolutionSet (T : 𝓗 →L[ℝ] 𝓚)
    (hT_closed : IsClosed (T.range : Set 𝓚)) (y : 𝓚) :
    moorePenroseInverse T hT_closed y ∈ moorePenroseSolutionSet T y := by
  simpa [moorePenroseInverse] using minimalNormLeastSquaresSolution_mem T y
    (moorePenroseSolutionSet_nonempty_of_closed_range T hT_closed y)

-- Proof sketch: combine `moorePenroseInverse_mem_moorePenroseSolutionSet` with
-- `mem_moorePenroseSolutionSet_iff`.
/-- The generalized inverse solves the normal equation `T* T x = T* y`. -/
theorem moorePenroseInverse_normalEquation (T : 𝓗 →L[ℝ] 𝓚)
    (hT_closed : IsClosed (T.range : Set 𝓚)) (y : 𝓚) :
    adjoint T (T (moorePenroseInverse T hT_closed y)) = adjoint T y := by
  simpa [moorePenroseInverse] using minimalNormLeastSquaresSolution_normalEquation T y
    (moorePenroseSolutionSet_nonempty_of_closed_range T hT_closed y)
