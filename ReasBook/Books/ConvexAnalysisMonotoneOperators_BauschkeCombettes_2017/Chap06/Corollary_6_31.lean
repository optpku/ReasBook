/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Theorem_6_30

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped InnerProductSpace Pointwise

universe u

section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
variable (K : ProperCone ℝ 𝓗)

local notation "P" =>
  projectionPoint (K : Set 𝓗) (isChebyshev_of_properCone K)

local notation "Q" =>
  projectionPoint (negativePolar (K : Set 𝓗)) (isChebyshev_negativePolar K)

omit [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗] in
/-- Helper for Corollary 6.31: in a Chebyshev set, every nonprojection point is strictly farther
from `x` than the projection point. -/
lemma dist_projectionPoint_lt_dist_of_mem_ne {C : Set 𝓗} (hC : IsChebyshev C) {x y : 𝓗}
    (hy : y ∈ C) (hy_ne : y ≠ projectionPoint C hC x) :
    dist x (projectionPoint C hC x) < dist x y := by
  -- The projection realizes the infimum distance, so it is never farther than another point of `C`.
  have hle : dist x (projectionPoint C hC x) ≤ dist x y := by
    calc
      dist x (projectionPoint C hC x) = Metric.infDist x C := by
        exact (projectionPoint_isBestApproximation C hC x).2
      _ ≤ dist x y := Metric.infDist_le_dist_of_mem hy
  -- Equality would make `y` another best approximation, contradicting uniqueness.
  refine lt_of_le_of_ne hle ?_
  intro hdist_eq
  have hy_best : IsBestApproximation x C y := by
    refine ⟨hy, ?_⟩
    calc
      dist x y = dist x (projectionPoint C hC x) := hdist_eq.symm
      _ = Metric.infDist x C := by
        exact (projectionPoint_isBestApproximation C hC x).2
  have hy_proj : y = projectionPoint C hC x :=
    eq_projectionPoint_of_isBestApproximation C hC hy_best
  exact hy_ne hy_proj

-- Proof sketch: apply Theorem 3.16 to the Chebyshev set `negativePolar (K : Set 𝓗)` and the point
-- `z ≠ Q x` to get `‖x - Q x‖ < ‖x - z‖`; then rewrite `x - Q x = P x` using Theorem 6.30 and
-- `x - z = y` using `x = y + z`.
/-- Corollary 6.31 (1): clause (i). If `x = y + z` with `y ∈ K` and `z ∈ Kᵒ⊖`, and if `z` is not
the projection of `x` onto `Kᵒ⊖`, then the norm of the projection of `x` onto `K` is strictly less
than `‖y‖`. -/
theorem norm_projectionPoint_lt_norm_of_decomposition
    {x y z : 𝓗}
    (hy : y ∈ (K : Set 𝓗) \ {P x}) (hz : z ∈ negativePolar (K : Set 𝓗) \ {Q x})
    (hx : x = y + z) :
    ‖P x‖ < ‖y‖ := by
  let _ := hy
  have hz_mem : z ∈ negativePolar (K : Set 𝓗) := hz.1
  have hz_ne : z ≠ Q x := by
    simpa using hz.2
  -- Compare the negative-polar projection with the competing point `z`.
  have hdist :
      dist x (Q x) < dist x z :=
    dist_projectionPoint_lt_dist_of_mem_ne (isChebyshev_negativePolar K) hz_mem hz_ne
  set p : 𝓗 := P x with hp
  set q : 𝓗 := Q x with hq
  have hdist' : dist x q < dist x z := by
    simpa [hq] using hdist
  have hsum : p + q = x := by
    simpa [hp, hq] using (eq_projectionPoint_add_projectionPoint_negativePolar K x).symm
  have hx_sub_q : x - q = p := by
    calc
      x - q = (p + q) - q := by rw [← hsum]
      _ = p := by abel
  have hx_sub_z : x - z = y := by
    calc
      x - z = (y + z) - z := by rw [hx]
      _ = y := by abel
  -- Rewrite the strict distance comparison as the desired norm inequality.
  rw [hp]
  calc
    ‖p‖ = dist x q := by
      rw [dist_eq_norm, hx_sub_q]
    _ < dist x z := hdist'
    _ = ‖y‖ := by
      rw [dist_eq_norm, hx_sub_z]

-- Proof sketch: apply Theorem 3.16 to the Chebyshev set `K` and the point `y ≠ P x` to get
-- `‖x - P x‖ < ‖x - y‖`; then rewrite `x - P x = Q x` using Theorem 6.30 and `x - y = z` using
-- `x = y + z`.
/-- Corollary 6.31 (2): clause (i). If `x = y + z` with `y ∈ K` and `z ∈ Kᵒ⊖`, and if `y` is not
the projection of `x` onto `K`, then the norm of the projection of `x` onto `Kᵒ⊖` is strictly less
than `‖z‖`. -/
theorem norm_projectionPoint_negativePolar_lt_norm_of_decomposition
    {x y z : 𝓗}
    (hy : y ∈ (K : Set 𝓗) \ {P x}) (hz : z ∈ negativePolar (K : Set 𝓗) \ {Q x})
    (hx : x = y + z) :
    ‖Q x‖ < ‖z‖ := by
  let _ := hz
  have hy_mem : y ∈ (K : Set 𝓗) := hy.1
  have hy_ne : y ≠ P x := by
    simpa using hy.2
  -- Compare the cone projection with the competing point `y`.
  have hdist :
      dist x (P x) < dist x y :=
    dist_projectionPoint_lt_dist_of_mem_ne (isChebyshev_of_properCone K) hy_mem hy_ne
  set p : 𝓗 := P x with hp
  set q : 𝓗 := Q x with hq
  have hdist' : dist x p < dist x y := by
    simpa [hp] using hdist
  have hsum : p + q = x := by
    simpa [hp, hq] using (eq_projectionPoint_add_projectionPoint_negativePolar K x).symm
  have hx_sub_p : x - p = q := by
    calc
      x - p = (p + q) - p := by rw [← hsum]
      _ = q := by abel
  have hx_sub_y : x - y = z := by
    calc
      x - y = (y + z) - y := by rw [hx]
      _ = z := by abel
  -- Rewrite the strict distance comparison as the desired norm inequality.
  rw [hq]
  calc
    ‖q‖ = dist x p := by
      rw [dist_eq_norm, hx_sub_p]
    _ < dist x y := hdist'
    _ = ‖z‖ := by
      rw [dist_eq_norm, hx_sub_y]

-- Proof sketch: since `y ∈ K` and `z ∈ Kᵒ⊖`, one has `⟪y, z⟫ ≤ 0`. If equality held, then the
-- strict norm inequalities from the previous two clauses together with Theorem 6.30 would force
-- `‖x‖² > ‖x‖²`, a contradiction; finally use Theorem 6.30 to identify the projection inner
-- product with `0`.
/-- Corollary 6.31 (3): clause (ii). Under the same decomposition hypotheses, the inner product
`⟪y, z⟫` is strictly smaller than the inner product of the projections of `x` onto `K` and `Kᵒ⊖`.
By Theorem 6.30, that projection inner product is `0`. -/
theorem inner_lt_inner_projectionPoint_projectionPoint_negativePolar_of_decomposition
    {x y z : 𝓗}
    (hy : y ∈ (K : Set 𝓗) \ {P x}) (hz : z ∈ negativePolar (K : Set 𝓗) \ {Q x})
    (hx : x = y + z) :
    ⟪y, z⟫_ℝ < ⟪P x, Q x⟫_ℝ := by
  have hy_mem : y ∈ (K : Set 𝓗) := hy.1
  have hz_mem : z ∈ negativePolar (K : Set 𝓗) := hz.1
  have hPy_lt : ‖P x‖ < ‖y‖ :=
    norm_projectionPoint_lt_norm_of_decomposition (K := K) hy hz hx
  have hQz_lt : ‖Q x‖ < ‖z‖ :=
    norm_projectionPoint_negativePolar_lt_norm_of_decomposition (K := K) hy hz hx
  have hproj_inner_zero : ⟪P x, Q x⟫_ℝ = 0 :=
    inner_projectionPoint_projectionPoint_negativePolar_eq_zero K x
  have hnonpos : ⟪y, z⟫_ℝ ≤ 0 := by
    -- Membership in the negative polar gives the sign of the mixed term.
    rw [Set.mem_negativePolar] at hz_mem
    simpa [real_inner_comm] using hz_mem y hy_mem
  have hyz_ne : ⟪y, z⟫_ℝ ≠ 0 := by
    intro hyz_zero
    have hnorm_x_yz :
        ‖x‖ ^ 2 = ‖y‖ ^ 2 + ‖z‖ ^ 2 := by
      -- The assumed orthogonality of `y` and `z` removes the mixed term in `‖y + z‖²`.
      calc
        ‖x‖ ^ 2 = ‖y + z‖ ^ 2 := by rw [hx]
        _ = ‖y‖ ^ 2 + 2 * ⟪y, z⟫_ℝ + ‖z‖ ^ 2 := by
          simpa using norm_add_sq_real y z
        _ = ‖y‖ ^ 2 + ‖z‖ ^ 2 := by
          rw [hyz_zero]
          ring
    have hnorm_x_proj :
        ‖x‖ ^ 2 = ‖P x‖ ^ 2 + ‖Q x‖ ^ 2 := by
      set p : 𝓗 := P x with hp
      set q : 𝓗 := Q x with hq
      have hsum : p + q = x := by
        simpa [hp, hq] using (eq_projectionPoint_add_projectionPoint_negativePolar K x).symm
      have hproj_inner_zero' : ⟪p, q⟫_ℝ = 0 := by
        simpa [hp, hq] using hproj_inner_zero
      -- The Moreau decomposition is orthogonal by Theorem 6.30, so its mixed term also vanishes.
      rw [hp, hq]
      calc
        ‖x‖ ^ 2 = ‖p + q‖ ^ 2 := by rw [← hsum]
        _ = ‖p‖ ^ 2 + 2 * ⟪p, q⟫_ℝ + ‖q‖ ^ 2 := by
          simpa using norm_add_sq_real p q
        _ = ‖p‖ ^ 2 + ‖q‖ ^ 2 := by
          rw [hproj_inner_zero']
          ring
    have hPy_sq_lt : ‖P x‖ ^ 2 < ‖y‖ ^ 2 := by
      nlinarith [hPy_lt, norm_nonneg (P x), norm_nonneg y]
    have hQz_sq_lt : ‖Q x‖ ^ 2 < ‖z‖ ^ 2 := by
      nlinarith [hQz_lt, norm_nonneg (Q x), norm_nonneg z]
    -- The strict inequalities from clause (i) make the decomposed squared norms strictly smaller.
    nlinarith [hnorm_x_yz, hnorm_x_proj, hPy_sq_lt, hQz_sq_lt]
  have hyz_lt_zero : ⟪y, z⟫_ℝ < 0 := by
    exact lt_of_le_of_ne hnonpos hyz_ne
  -- Replace the projection inner product by `0` and conclude.
  calc
    ⟪y, z⟫_ℝ < 0 := hyz_lt_zero
    _ = ⟪P x, Q x⟫_ℝ := by
      rw [hproj_inner_zero]

-- Proof sketch: expand both squared norms using the polarization identity. Then combine the two
-- strict norm inequalities from clause (i), the strict inner-product inequality from clause (ii),
-- and the orthogonality of the projection pair from Theorem 6.30.
/-- Corollary 6.31 (4): clause (iii). Under the same decomposition hypotheses, the distance between
the projections of `x` onto `K` and `Kᵒ⊖` is strictly less than `‖y - z‖`. -/
theorem norm_sub_projectionPoints_lt_norm_sub_of_decomposition
    {x y z : 𝓗}
    (hy : y ∈ (K : Set 𝓗) \ {P x}) (hz : z ∈ negativePolar (K : Set 𝓗) \ {Q x})
    (hx : x = y + z) :
    ‖P x - Q x‖ < ‖y - z‖ := by
  have hPy_lt : ‖P x‖ < ‖y‖ :=
    norm_projectionPoint_lt_norm_of_decomposition (K := K) hy hz hx
  have hQz_lt : ‖Q x‖ < ‖z‖ :=
    norm_projectionPoint_negativePolar_lt_norm_of_decomposition (K := K) hy hz hx
  have hinner_lt : ⟪y, z⟫_ℝ < ⟪P x, Q x⟫_ℝ :=
    inner_lt_inner_projectionPoint_projectionPoint_negativePolar_of_decomposition
      (K := K) hy hz hx
  have hproj_inner_zero : ⟪P x, Q x⟫_ℝ = 0 :=
    inner_projectionPoint_projectionPoint_negativePolar_eq_zero K x
  have hsq_lt :
      ‖P x - Q x‖ ^ 2 < ‖y - z‖ ^ 2 := by
    -- Expand both squared norms and compare term-by-term using clauses (i) and (ii).
    have hproj_sq :
        ‖P x - Q x‖ ^ 2 = ‖P x‖ ^ 2 - 2 * ⟪P x, Q x⟫_ℝ + ‖Q x‖ ^ 2 := by
      simpa using norm_sub_sq_real (P x) (Q x)
    have hyz_sq :
        ‖y - z‖ ^ 2 = ‖y‖ ^ 2 - 2 * ⟪y, z⟫_ℝ + ‖z‖ ^ 2 := by
      simpa using norm_sub_sq_real y z
    have hPy_sq_lt : ‖P x‖ ^ 2 < ‖y‖ ^ 2 := by
      nlinarith [hPy_lt, norm_nonneg (P x), norm_nonneg y]
    have hQz_sq_lt : ‖Q x‖ ^ 2 < ‖z‖ ^ 2 := by
      nlinarith [hQz_lt, norm_nonneg (Q x), norm_nonneg z]
    nlinarith [hproj_sq, hyz_sq, hPy_sq_lt, hQz_sq_lt, hinner_lt]
  -- Pass from the strict inequality of squares back to the strict inequality of norms.
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg (y - z)) hsq_lt

end
