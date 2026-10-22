/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_46
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Corollary_3_22
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Corollary_5_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Theorem_5_5

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped InnerProductSpace Topology

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {C : AffineSubspace ℝ H}

variable (hC_nonempty : (C : Set H).Nonempty) (hC_closed : IsClosed (C : Set H))

local notation "P" =>
  projectionPoint (C : Set H)
    (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed C.convex)

private theorem projectionPoint_eq_self_of_mem_affineSubspace {x : H} (hx : x ∈ (C : Set H)) :
    P x = x := by
  have hx_proj : x = P x :=
    (eq_projectionPoint_iff_mem_and_inner_sub_eq_zero_of_nonempty_isClosed_affineSubspace
      hC_nonempty hC_closed).mpr <| by
        refine ⟨hx, ?_⟩
        intro y hy z hz
        simp
  simpa using hx_proj.symm

private theorem inner_sub_projection_residual_eq_zero (x y z : H)
    (hy : y ∈ (C : Set H)) (hz : z ∈ (C : Set H)) :
    ⟪y - z, x - P x⟫_ℝ = 0 := by
  exact
    ((eq_projectionPoint_iff_mem_and_inner_sub_eq_zero_of_nonempty_isClosed_affineSubspace
      hC_nonempty hC_closed).mp rfl).2 y hy z hz

private theorem projectionPoint_eq_succ_of_fejerMonotone_affineSubspace
    (x : ℕ → H) (hfejer : FejerMonotone (C : Set H) x) (n : ℕ) :
    P (x (n + 1)) = P (x n) := by
  let p := P (x n)
  let q := P (x (n + 1))
  have hp : p ∈ (C : Set H) := by
    simp [p]
  have hq : q ∈ (C : Set H) := by
    simp [q]
  let c : ℝ → H := fun t ↦ AffineMap.lineMap p q t
  have hc : ∀ t : ℝ, c t ∈ (C : Set H) := by
    intro t
    exact AffineMap.lineMap_mem t hp hq
  have horth_p : ∀ t : ℝ, ⟪p - c t, x n - p⟫_ℝ = 0 := by
    intro t
    simpa [p, c] using
      inner_sub_projection_residual_eq_zero hC_nonempty hC_closed (x n) p (c t) hp (hc t)
  have horth_q : ∀ t : ℝ, ⟪q - c t, x (n + 1) - q⟫_ℝ = 0 := by
    intro t
    simpa [q, c] using
      inner_sub_projection_residual_eq_zero hC_nonempty hC_closed (x (n + 1)) q (c t) hq (hc t)
  have hdist_sq_p : ∀ t : ℝ, ‖x n - c t‖ ^ 2 = ‖x n - p‖ ^ 2 + ‖p - c t‖ ^ 2 := by
    intro t
    have hdecomp : x n - c t = (x n - p) + (p - c t) := by
      abel
    calc
      ‖x n - c t‖ ^ 2 = ‖(x n - p) + (p - c t)‖ ^ 2 := by rw [hdecomp]
      _ = ‖x n - p‖ ^ 2 + 2 * ⟪x n - p, p - c t⟫_ℝ + ‖p - c t‖ ^ 2 := by
        rw [norm_add_sq_real]
      _ = ‖x n - p‖ ^ 2 + ‖p - c t‖ ^ 2 := by
        rw [real_inner_comm, horth_p t, mul_zero, add_zero]
  have hdist_sq_q : ∀ t : ℝ, ‖x (n + 1) - c t‖ ^ 2 = ‖x (n + 1) - q‖ ^ 2 + ‖q - c t‖ ^ 2 := by
    intro t
    have hdecomp : x (n + 1) - c t = (x (n + 1) - q) + (q - c t) := by
      abel
    calc
      ‖x (n + 1) - c t‖ ^ 2 = ‖(x (n + 1) - q) + (q - c t)‖ ^ 2 := by rw [hdecomp]
      _ = ‖x (n + 1) - q‖ ^ 2 + 2 * ⟪x (n + 1) - q, q - c t⟫_ℝ + ‖q - c t‖ ^ 2 := by
        rw [norm_add_sq_real]
      _ = ‖x (n + 1) - q‖ ^ 2 + ‖q - c t‖ ^ 2 := by
        rw [real_inner_comm, horth_q t, mul_zero, add_zero]
  have hp_sub_c : ∀ t : ℝ, p - c t = t • (p - q) := by
    intro t
    have hc_sub_p : c t - p = t • (q - p) := by
      simpa [c, vsub_eq_sub] using (AffineMap.lineMap_vsub_left p q t)
    calc
      p - c t = -(c t - p) := by abel
      _ = -(t • (q - p)) := by rw [hc_sub_p]
      _ = t • (p - q) := by rw [← smul_neg, neg_sub]
  have hq_sub_c : ∀ t : ℝ, q - c t = (1 - t) • (q - p) := by
    intro t
    simpa [c, vsub_eq_sub] using (AffineMap.right_vsub_lineMap p q t)
  let A : ℝ := ‖x (n + 1) - q‖ ^ 2
  let B : ℝ := ‖x n - p‖ ^ 2
  let d : ℝ := ‖q - p‖ ^ 2
  have hline : ∀ t : ℝ, A + (1 - t) ^ 2 * d ≤ B + t ^ 2 * d := by
    intro t
    have hdist : ‖x (n + 1) - c t‖ ≤ ‖x n - c t‖ := by
      simpa [dist_eq_norm] using hfejer (c t) (hc t) n
    have hsq : ‖x (n + 1) - c t‖ ^ 2 ≤ ‖x n - c t‖ ^ 2 := by
      nlinarith [hdist, norm_nonneg (x (n + 1) - c t), norm_nonneg (x n - c t)]
    rw [hdist_sq_q t, hdist_sq_p t] at hsq
    have hp_norm : ‖p - c t‖ ^ 2 = t ^ 2 * d := by
      calc
        ‖p - c t‖ ^ 2 = ‖t • (p - q)‖ ^ 2 := by rw [hp_sub_c t]
        _ = (|t| * ‖p - q‖) ^ 2 := by rw [norm_smul, Real.norm_eq_abs]
        _ = t ^ 2 * d := by
          calc
            (|t| * ‖p - q‖) ^ 2 = t ^ 2 * ‖p - q‖ ^ 2 := by rw [mul_pow, sq_abs]
            _ = t ^ 2 * ‖q - p‖ ^ 2 := by rw [norm_sub_rev]
            _ = t ^ 2 * d := by simp [d]
    have hq_norm : ‖q - c t‖ ^ 2 = (1 - t) ^ 2 * d := by
      calc
        ‖q - c t‖ ^ 2 = ‖(1 - t) • (q - p)‖ ^ 2 := by rw [hq_sub_c t]
        _ = (|1 - t| * ‖q - p‖) ^ 2 := by rw [norm_smul, Real.norm_eq_abs]
        _ = (1 - t) ^ 2 * d := by
          simpa [d] using
            (show (|1 - t| * ‖q - p‖) ^ 2 = (1 - t) ^ 2 * ‖q - p‖ ^ 2 by
              rw [mul_pow, sq_abs])
    rw [hp_norm, hq_norm] at hsq
    simpa [A, B] using hsq
  by_contra hpq
  have hpq' : q ≠ p := by
    simpa [eq_comm] using hpq
  have hdpos : 0 < d := by
    have hnorm_pos : 0 < ‖q - p‖ := by
      exact norm_pos_iff.mpr (sub_ne_zero.mpr hpq')
    dsimp [d]
    positivity
  have hlin : ∀ t : ℝ, A + d - 2 * t * d ≤ B := by
    intro t
    have ht := hline t
    nlinarith
  let r : ℝ := B - A - d
  have hdne : d ≠ 0 := ne_of_gt hdpos
  have hbad : A + d + 2 * (|r| + 1) ≤ B := by
    have hbad := hlin (-(|r| + 1) / d)
    field_simp [hdne] at hbad
    nlinarith
  have hr : 2 * |r| + 2 ≤ r := by
    dsimp [r] at hbad
    nlinarith
  have hr_le_abs : r ≤ |r| := le_abs_self r
  have habs : |r| + 2 ≤ 0 := by
    nlinarith
  nlinarith [abs_nonneg r, habs]

-- Proof sketch: use the affine-subspace projection identity from Chapter 3 together with the
-- affine-line argument from the textbook to show that every Fejér step preserves the projection
-- onto `C`, and then compare the `n`th shadow with the initial one.
/-- Proposition 5.9 (1): if a sequence is Fejér monotone with respect to a closed affine subspace
`C`, then the metric projection of every term onto `C` equals the projection of the initial term. -/
theorem projectionPoint_eq_initial_of_fejerMonotone_affineSubspace
    (x : ℕ → H) (hfejer : FejerMonotone (C : Set H) x) (n : ℕ) :
    P (x n) = P (x 0) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        P (x (n + 1)) = P (x n) :=
          projectionPoint_eq_succ_of_fejerMonotone_affineSubspace
            hC_nonempty hC_closed x hfejer n
        _ = P (x 0) := ih

-- Proof sketch: Theorem 5.5 gives weak convergence of `(x n)` to some point of `C` once every weak
-- sequential cluster point lies in `C`. Proposition 5.9 (1) identifies the projection of every
-- term with the fixed shadow `P (x 0)`, and Corollary 5.8 upgrades weak convergence to strong
-- convergence of the shadow sequence, forcing the weak limit to equal `P (x 0)`.
/-- Proposition 5.9 (2): if a Fejér-monotone sequence with respect to a closed affine subspace `C`
has all of its weak sequential cluster points in `C`, then it converges weakly to the metric
projection of its initial term onto `C`. -/
theorem tendsto_weakly_projectionPoint_initial_of_fejerMonotone_affineSubspace
    (x : ℕ → H) (hfejer : FejerMonotone (C : Set H) x)
    (hcluster :
      ∀ z : H,
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (x n)) (toWeakSpace ℝ H z) →
          z ∈ (C : Set H)) :
    Tendsto (fun n ↦ toWeakSpace ℝ H (x n)) atTop (𝓝 (toWeakSpace ℝ H (P (x 0)))) := by
  obtain ⟨z, hzC, hz⟩ :=
    tendsto_weakly_of_fejerMonotone_of_weakSequentialClusterPts_mem hC_nonempty x hfejer hcluster
  have hshadow :
      Tendsto (fun n ↦ P (x n)) atTop (𝓝 z) :=
    tendsto_projectionPoint_of_fejerMonotone_of_tendsto_weakly
      hC_nonempty hC_closed C.convex x hfejer hzC hz
  have hconst :
      (fun n ↦ P (x n)) =ᶠ[atTop] fun _ : ℕ ↦ P (x 0) :=
    Filter.Eventually.of_forall <|
      projectionPoint_eq_initial_of_fejerMonotone_affineSubspace
        hC_nonempty hC_closed x hfejer
  have hz_eq : z = P (x 0) :=
    tendsto_nhds_unique_of_eventuallyEq hshadow tendsto_const_nhds hconst
  simpa [hz_eq] using hz

end
