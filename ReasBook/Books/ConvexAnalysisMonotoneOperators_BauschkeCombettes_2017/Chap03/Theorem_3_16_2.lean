/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_16_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

omit [CompleteSpace 𝓗] in
-- Proof sketch: rewrite `IsBestApproximation` as the metric equality defining a nearest point, then
-- `Mathlib.Analysis.InnerProductSpace.Projection.Minimal.norm_eq_iInf_iff_real_inner_le_zero`,
-- rewriting `Metric.infDist` as the corresponding `iInf`.
/-- In a convex subset of a real inner product space, a point is a best approximation to `x`
exactly when it lies in the set and satisfies the variational inequality against every point of the
set. -/
theorem isBestApproximation_iff_mem_and_inner_sub_right_nonpos {C : Set 𝓗}
    (hC_convex : Convex ℝ C) {x p : 𝓗} :
    IsBestApproximation x C p ↔ p ∈ C ∧ ∀ y ∈ C, ⟪y - p, x - p⟫_ℝ ≤ 0 := by
  rw [isBestApproximation_iff_mem_and_dist_eq_infDist]
  constructor
  · intro hp
    rw [dist_eq_norm, Metric.infDist_eq_iInf] at hp
    simp_rw [dist_eq_norm] at hp
    have hinner := (norm_eq_iInf_iff_real_inner_le_zero hC_convex hp.1).mp hp.2
    refine ⟨hp.1, ?_⟩
    intro y hy
    simpa [real_inner_comm] using hinner y hy
  · intro hp
    refine ⟨hp.1, ?_⟩
    rw [dist_eq_norm, Metric.infDist_eq_iInf]
    simp_rw [dist_eq_norm]
    refine (norm_eq_iInf_iff_real_inner_le_zero hC_convex hp.1).mpr ?_
    intro y hy
    simpa [real_inner_comm] using hp.2 y hy

omit [CompleteSpace 𝓗] in
-- Proof sketch: combine `projectionPoint_isBestApproximation` with the best-approximation
-- characterization above, and conversely use uniqueness in the Chebyshev hypothesis.
/-- In a convex Chebyshev set, a point is the projection of `x` exactly when it lies in the set and
satisfies the variational inequality against every point of the set. -/
theorem eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos {C : Set 𝓗} (hC : IsChebyshev C)
    (hC_convex : Convex ℝ C) {x p : 𝓗} :
    p = projectionPoint C hC x ↔ p ∈ C ∧ ∀ y ∈ C, ⟪y - p, x - p⟫_ℝ ≤ 0 := by
  constructor
  · intro hp
    exact
      (isBestApproximation_iff_mem_and_inner_sub_right_nonpos hC_convex).mp <|
        by simpa [hp] using projectionPoint_isBestApproximation C hC x
  · intro hp
    exact
      eq_projectionPoint_of_isBestApproximation C hC <|
        (isBestApproximation_iff_mem_and_inner_sub_right_nonpos hC_convex).mpr hp

-- Proof sketch: instantiate `eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos` with the
-- Chebyshev property supplied by `isChebyshev_of_nonempty_isClosed_convex`.
/-- Theorem 3.16.2: for a nonempty closed convex subset of a real Hilbert space, a point `p` is
the projection of `x` onto `C` exactly when `p ∈ C` and `⟪y - p, x - p⟫_ℝ ≤ 0` for every `y ∈ C`.
Here the projection is the canonical point
`projectionPoint C (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x`,
which also realizes `Metric.infDist x C`. -/
theorem eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
    {C : Set 𝓗} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    {x p : 𝓗} :
    p =
        projectionPoint C
          (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x ↔
      p ∈ C ∧ ∀ y ∈ C, ⟪y - p, x - p⟫_ℝ ≤ 0 := by
  -- The existence/uniqueness part is exactly Theorem 3.16.1, so the characterization reduces to
  -- the Chebyshev-convex case above.
  exact eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos
    (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) hC_convex
