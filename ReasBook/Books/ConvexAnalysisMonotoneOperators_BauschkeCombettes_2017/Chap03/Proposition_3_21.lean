/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_16_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

section

variable {C : Set 𝓗}

-- Proof sketch: let `p := projectionPoint C hC x`. To show that the projection of
-- `p + t • (x - p)` is still `p`, it is enough to verify that `p` is again a best approximation
-- for the new point. Use the variational characterization of nearest points on convex Chebyshev
-- sets: the defining inequality for `p = projectionPoint C hC x` scales by the nonnegative factor
-- `t`, so `p` also satisfies the characterization at `p + t • (x - p)`.
/-- For a convex Chebyshev set, the projection of every point on the ray starting at
`projectionPoint C hC x` and pointing toward `x` remains `projectionPoint C hC x`. -/
theorem projectionPoint_ray_fixed (C : Set 𝓗) (hC : IsChebyshev C) (hC_convex : Convex ℝ C)
    (x : 𝓗) {t : ℝ} (ht : 0 ≤ t) :
    projectionPoint C hC (projectionPoint C hC x + t • (x - projectionPoint C hC x)) =
      projectionPoint C hC x := by
  -- Read off the projection variational inequality at the original point `x`.
  have hx :
      projectionPoint C hC x ∈ C ∧
        ∀ y ∈ C, ⟪y - projectionPoint C hC x, x - projectionPoint C hC x⟫_ℝ ≤ 0 := by
    exact
      (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos hC hC_convex).mp rfl
  -- Apply the same characterization at the point on the residual ray.
  have hray :
      projectionPoint C hC x =
        projectionPoint C hC (projectionPoint C hC x + t • (x - projectionPoint C hC x)) := by
    refine
      (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos hC hC_convex).mpr ?_
    refine ⟨hx.1, ?_⟩
    intro y hy
    -- The new displacement from `P x` is a nonnegative multiple of `x - P x`.
    calc
      ⟪y - projectionPoint C hC x,
          (projectionPoint C hC x + t • (x - projectionPoint C hC x)) -
            projectionPoint C hC x⟫_ℝ
          = ⟪y - projectionPoint C hC x, t • (x - projectionPoint C hC x)⟫_ℝ := by
              abel_nf
      _ = t * ⟪y - projectionPoint C hC x, x - projectionPoint C hC x⟫_ℝ := by
            rw [inner_smul_right]
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht (hx.2 y hy)
  simpa using hray.symm

/-- Proposition 3.21: if `C` is a nonempty closed convex subset of a real Hilbert space, then the
projection of every point on the ray starting at `P_C x` and pointing toward `x` remains `P_C x`.
-/
theorem projectionPoint_ray_fixed_of_nonempty_isClosed_convex
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (x : 𝓗)
    {t : ℝ} (ht : 0 ≤ t) :
    projectionPoint C
        (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex)
        (projectionPoint C
            (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x +
          t •
            (x -
              projectionPoint C
                (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x)) =
      projectionPoint C
        (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x := by
  simpa using
    projectionPoint_ray_fixed C
      (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex)
      hC_convex x ht

end
