/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Definition_3_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_16_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_28

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
variable (K : ProperCone ℝ 𝓗)

local notation "P" =>
  projectionPoint (K : Set 𝓗)
    (isChebyshev_of_nonempty_isClosed_convex K.nonempty K.isClosed K.convex)

/-- Helper for Proposition 6.32: expand the inner product against `x` into the norm square of the
projection residual plus the projection term. -/
lemma projectionPoint_inner_decomposition (x : 𝓗) :
    ⟪x, x - P x⟫_ℝ = ‖x - P x‖ ^ 2 + ⟪P x, x - P x⟫_ℝ := by
  -- Rewrite `x` as residual plus projection and expand the inner product linearly.
  calc
    ⟪x, x - P x⟫_ℝ = ⟪(x - P x) + P x, x - P x⟫_ℝ := by
      congr 1
      abel
    _ = ⟪x - P x, x - P x⟫_ℝ + ⟪P x, x - P x⟫_ℝ := by
      rw [inner_add_left]
    _ = ‖x - P x‖ ^ 2 + ⟪P x, x - P x⟫_ℝ := by
      rw [real_inner_self_eq_norm_sq]

-- Proof sketch: Proposition 6.28 gives `⟪P x, x - P x⟫_ℝ = 0` for the metric projection onto the
-- proper cone `K`. Subtracting this from the hypothesis yields `‖x - P x‖^2 ≤ 0`, so the residual
-- vanishes and hence `x = P x ∈ K`.
/-- Proposition 6.32: if the inner product of `x` with the residual from its metric projection onto
a nonempty closed convex cone `K` is nonpositive, then `x` already belongs to `K`. -/
theorem mem_of_inner_sub_projectionPoint_nonpos_of_properCone
    (x : 𝓗) (hinner : ⟪x, x - P x⟫_ℝ ≤ 0) :
    x ∈ K := by
  have hbest : IsBestApproximation x (K : Set 𝓗) (P x) :=
    projectionPoint_isBestApproximation (K : Set 𝓗)
      (isChebyshev_of_nonempty_isClosed_convex K.nonempty K.isClosed K.convex) x
  have hproj_mem : P x ∈ K := hbest.1
  have hbest_norm : ‖x - P x‖ = ⨅ y : K, ‖x - y‖ := by
    -- Rewrite the projection point's best-approximation property into the subtype infimum form
    -- expected by the Hilbert projection inequality.
    have hbest_dist : dist x (P x) = Metric.infDist x (K : Set 𝓗) := hbest.2
    rw [dist_eq_norm, Metric.infDist_eq_iInf] at hbest_dist
    simpa [dist_eq_norm] using hbest_dist
  have hproj_ineq :=
    (norm_eq_iInf_iff_real_inner_le_zero K.convex hproj_mem).mp hbest_norm
  -- Recover the Proposition 6.28 orthogonality by testing the variational inequality at
  -- `0` and `2 • P x`.
  have horth : ⟪P x, x - P x⟫_ℝ = 0 := by
    have hzero : ⟪x - P x, -P x⟫_ℝ ≤ 0 := by
      simpa using hproj_ineq 0 K.zero_mem
    have htwo : ⟪x - P x, P x⟫_ℝ ≤ 0 := by
      have htwo_mem : (2 : ℝ) • P x ∈ K := K.smul_mem hproj_mem (by norm_num)
      simpa [two_smul, sub_eq_add_neg, add_assoc] using hproj_ineq ((2 : ℝ) • P x) htwo_mem
    have hnonneg : 0 ≤ ⟪P x, x - P x⟫_ℝ := by
      have hzero' : -⟪P x, x - P x⟫_ℝ ≤ 0 := by
        simpa [real_inner_comm, inner_neg_right] using hzero
      linarith
    have hnonpos : ⟪P x, x - P x⟫_ℝ ≤ 0 := by
      simpa [real_inner_comm] using htwo
    linarith
  -- Expand the hypothesis into a norm-square inequality for the residual.
  have hnorm_sq_le : ‖x - P x‖ ^ 2 ≤ 0 := by
    calc
      ‖x - P x‖ ^ 2 = ⟪x, x - P x⟫_ℝ := by
        symm
        calc
          ⟪x, x - P x⟫_ℝ = ‖x - P x‖ ^ 2 + ⟪P x, x - P x⟫_ℝ :=
            projectionPoint_inner_decomposition (K := K) x
          _ = ‖x - P x‖ ^ 2 := by rw [horth, add_zero]
      _ ≤ 0 := hinner
  -- A square is always nonnegative, so the residual norm must vanish.
  have hnorm_sq_eq : ‖x - P x‖ ^ 2 = 0 := le_antisymm hnorm_sq_le (sq_nonneg ‖x - P x‖)
  have hnorm_eq : ‖x - P x‖ = 0 := sq_eq_zero_iff.mp hnorm_sq_eq
  have hsub_eq : x - P x = 0 := norm_eq_zero.mp hnorm_eq
  have hx_eq_proj : x = P x := sub_eq_zero.mp hsub_eq
  -- Rewrite `x` as its projection and inherit cone membership.
  rw [hx_eq_proj]
  exact hproj_mem

end
