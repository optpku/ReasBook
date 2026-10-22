/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Definition_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped BigOperators Topology

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {C : Set H} {xₙ : ℕ → H}

namespace FejerMonotone

omit [CompleteSpace H] in
/-- Helper for Proposition 5.10: the auxiliary point lies in the prescribed open ball once
`ρ < ε`. -/
lemma auxiliary_point_mem_ball {c d : H} {ρ ε : ℝ} (hρ : 0 < ρ) (hρε : ρ < ε) :
    (if ‖d‖ = 0 then c else c - ρ • ‖d‖⁻¹ • d) ∈ Metric.ball c ε := by
  -- Split on whether the direction vanishes; in the nonzero case the displacement has norm `ρ`.
  by_cases hdnorm : ‖d‖ = 0
  · have hε : 0 < ε := lt_trans hρ hρε
    simp [Metric.mem_ball, hdnorm, hε]
  · have hdist :
        dist (if ‖d‖ = 0 then c else c - ρ • ‖d‖⁻¹ • d) c = ρ := by
      calc
        dist (if ‖d‖ = 0 then c else c - ρ • ‖d‖⁻¹ • d) c
            = ‖ρ • ‖d‖⁻¹ • d‖ := by
                rw [dist_eq_norm]
                simp [hdnorm]
        _ = ρ := by
              rw [norm_smul, norm_smul, Real.norm_of_nonneg hρ.le,
                Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg d)),
                inv_mul_cancel₀ hdnorm, mul_one]
    have hdist_lt : dist (if ‖d‖ = 0 then c else c - ρ • ‖d‖⁻¹ • d) c < ε := by
      rw [hdist]
      exact hρε
    simpa [Metric.mem_ball] using hdist_lt

omit [CompleteSpace H] in
/-- Helper for Proposition 5.10: testing Fejér monotonicity at the interior-direction auxiliary
point yields the textbook squared-distance drop. -/
lemma fejer_sqnorm_drop_of_interior_direction (hxₙ : FejerMonotone C xₙ)
    {c : H} {ρ ε : ℝ} (hball : Metric.ball c ε ⊆ C) (hρ : 0 < ρ) (hρε : ρ < ε) (n : ℕ) :
    2 * ρ * ‖xₙ (n + 1) - xₙ n‖ ≤ ‖xₙ n - c‖ ^ 2 - ‖xₙ (n + 1) - c‖ ^ 2 := by
  let d := xₙ (n + 1) - xₙ n
  let z := if ‖d‖ = 0 then c else c - ρ • ‖d‖⁻¹ • d
  have hz_ball : z ∈ Metric.ball c ε :=
    auxiliary_point_mem_ball (c := c) (d := d) hρ hρε
  have hzC : z ∈ C := hball hz_ball
  have hstep : ‖xₙ (n + 1) - z‖ ≤ ‖xₙ n - z‖ := by
    simpa [dist_eq_norm] using hxₙ.step z hzC n
  have hstep_sq : ‖xₙ (n + 1) - z‖ ^ 2 ≤ ‖xₙ n - z‖ ^ 2 := by
    nlinarith [hstep, norm_nonneg (xₙ (n + 1) - z), norm_nonneg (xₙ n - z)]
  -- The zero increment case is immediate because the two consecutive iterates coincide.
  by_cases hd : d = 0
  · have hsucc : xₙ (n + 1) = xₙ n := by
      simpa [d, sub_eq_zero] using hd
    simp [hsucc]
  · have hdnorm : ‖d‖ ≠ 0 := norm_ne_zero_iff.mpr hd
    have hz_eq : z = c - ρ • ‖d‖⁻¹ • d := by
      simp [z, d, norm_ne_zero_iff.mpr hd]
    have hsub_sq :
        ‖xₙ n - z‖ ^ 2 =
          ‖xₙ (n + 1) - z‖ ^ 2 - 2 * (inner ℝ (xₙ (n + 1) - z) d) + ‖d‖ ^ 2 := by
      have hnorm := norm_sub_sq_real (xₙ (n + 1) - z) d
      have hrewrite : xₙ n - z = (xₙ (n + 1) - z) - d := by
        simp [d]
      simpa [hrewrite] using hnorm
    have hinner_bound : 2 * (inner ℝ (xₙ (n + 1) - z) d) ≤ ‖d‖ ^ 2 := by
      nlinarith [hstep_sq, hsub_sq]
    have hz_inner :
        inner ℝ (xₙ (n + 1) - z) d =
          inner ℝ (xₙ (n + 1) - c) d + ρ * ‖d‖ := by
      calc
        inner ℝ (xₙ (n + 1) - z) d
            = inner ℝ (xₙ (n + 1) - c + (ρ • ‖d‖⁻¹ • d)) d := by
                rw [hz_eq]
                congr
                abel
        _ = inner ℝ (xₙ (n + 1) - c) d + inner ℝ (ρ • ‖d‖⁻¹ • d) d := by
              rw [inner_add_left]
        _ = inner ℝ (xₙ (n + 1) - c) d + (ρ * ‖d‖⁻¹) * inner ℝ d d := by
              rw [real_inner_smul_left, real_inner_smul_left]
              ring
        _ = inner ℝ (xₙ (n + 1) - c) d + (ρ * ‖d‖⁻¹) * ‖d‖ ^ 2 := by
              rw [real_inner_self_eq_norm_sq]
        _ = inner ℝ (xₙ (n + 1) - c) d + ρ * ‖d‖ := by
              field_simp [hdnorm]
    have hdrop_eq :
        ‖xₙ n - c‖ ^ 2 - ‖xₙ (n + 1) - c‖ ^ 2 =
          -2 * (inner ℝ (xₙ (n + 1) - c) d) + ‖d‖ ^ 2 := by
      have hnorm := norm_sub_sq_real (xₙ (n + 1) - c) d
      have hrewrite : xₙ n - c = (xₙ (n + 1) - c) - d := by
        simp [d]
      nlinarith [show ‖xₙ n - c‖ ^ 2 =
          ‖xₙ (n + 1) - c‖ ^ 2 - 2 * (inner ℝ (xₙ (n + 1) - c) d) + ‖d‖ ^ 2 by
          simpa [hrewrite] using hnorm]
    -- Route correction: rewrite the Fejér step into an inner-product bound first, then map it to
    -- the desired drop in `‖xₙ n - c‖ ^ 2` through `norm_sub_sq_real`.
    nlinarith [hinner_bound, hz_inner, hdrop_eq]

omit [CompleteSpace H] in
/-- Helper for Proposition 5.10: the one-step drop estimate telescopes to a uniform bound on the
partial sums of the increment norms. -/
lemma partial_sum_norm_sub_le_of_fejer_sqnorm_drop (hxₙ : FejerMonotone C xₙ)
    {c : H} {ρ ε : ℝ} (hball : Metric.ball c ε ⊆ C) (hρ : 0 < ρ) (hρε : ρ < ε) (N : ℕ) :
    Finset.sum (Finset.range N) (fun i ↦ ‖xₙ (i + 1) - xₙ i‖) ≤ ‖xₙ 0 - c‖ ^ 2 / (2 * ρ) := by
  have hsum_drop :
      2 * ρ * Finset.sum (Finset.range N) (fun i ↦ ‖xₙ (i + 1) - xₙ i‖) ≤
        Finset.sum (Finset.range N) (fun i ↦ ‖xₙ i - c‖ ^ 2 - ‖xₙ (i + 1) - c‖ ^ 2) := by
    -- Sum the one-step descent inequality over the finite range.
    calc
      2 * ρ * Finset.sum (Finset.range N) (fun i ↦ ‖xₙ (i + 1) - xₙ i‖)
          = Finset.sum (Finset.range N) (fun i ↦ 2 * ρ * ‖xₙ (i + 1) - xₙ i‖) := by
              rw [Finset.mul_sum]
      _ ≤ Finset.sum (Finset.range N) (fun i ↦ ‖xₙ i - c‖ ^ 2 - ‖xₙ (i + 1) - c‖ ^ 2) := by
            refine Finset.sum_le_sum ?_
            intro i hi
            exact fejer_sqnorm_drop_of_interior_direction hxₙ hball hρ hρε i
  have htel :
      Finset.sum (Finset.range N) (fun i ↦ ‖xₙ i - c‖ ^ 2 - ‖xₙ (i + 1) - c‖ ^ 2) =
        ‖xₙ 0 - c‖ ^ 2 - ‖xₙ N - c‖ ^ 2 := by
    let a : ℕ → ℝ := fun i ↦ ‖xₙ i - c‖ ^ 2
    have htel_raw := Finset.sum_range_sub a N
    rw [Finset.sum_sub_distrib] at htel_raw
    have htel_swap :
        Finset.sum (Finset.range N) (fun i ↦ a i) -
            Finset.sum (Finset.range N) (fun i ↦ a (i + 1)) =
          a 0 - a N := by
      calc
        Finset.sum (Finset.range N) (fun i ↦ a i) -
            Finset.sum (Finset.range N) (fun i ↦ a (i + 1))
            = -(Finset.sum (Finset.range N) (fun i ↦ a (i + 1)) -
                Finset.sum (Finset.range N) (fun i ↦ a i)) := by
                  ring
        _ = -(a N - a 0) := by rw [htel_raw]
        _ = a 0 - a N := by ring
    calc
      Finset.sum (Finset.range N) (fun i ↦ ‖xₙ i - c‖ ^ 2 - ‖xₙ (i + 1) - c‖ ^ 2)
          = Finset.sum (Finset.range N) (fun i ↦ ‖xₙ i - c‖ ^ 2) -
              Finset.sum (Finset.range N) (fun i ↦ ‖xₙ (i + 1) - c‖ ^ 2) := by
                rw [Finset.sum_sub_distrib]
      _ = a 0 - a N := htel_swap
      _ = ‖xₙ 0 - c‖ ^ 2 - ‖xₙ N - c‖ ^ 2 := by rfl
  have hbound :
      2 * ρ * Finset.sum (Finset.range N) (fun i ↦ ‖xₙ (i + 1) - xₙ i‖) ≤ ‖xₙ 0 - c‖ ^ 2 := by
    -- The telescoped right-hand side is at most the initial squared distance.
    rw [htel] at hsum_drop
    nlinarith [hsum_drop, sq_nonneg (‖xₙ N - c‖)]
  have h2ρ : 0 < 2 * ρ := by positivity
  exact (le_div_iff₀ h2ρ).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hbound)

-- Proof sketch: choose an interior point `c ∈ interior C` and a radius `ρ > 0` with
-- `Metric.ball c ρ ⊆ C`. Apply Fejer monotonicity to the auxiliary points obtained by moving from
-- `c` in the direction opposite to `xₙ₊₁ - xₙ`; the Hilbert-space norm expansion gives a telescopic
-- estimate for `‖xₙ - c‖ ^ 2` that implies `Summable (fun n ↦ ‖xₙ₊₁ - xₙ‖)`. The summability of the
-- increments makes `(xₙ)` Cauchy, and completeness yields strong convergence.
/-- Proposition 5.10: if `C` has nonempty interior and `xₙ` is Fejer monotone with respect to
`C`, then `xₙ` converges strongly in the real Hilbert space and the norms of its successive
increments form a summable series. -/
theorem exists_tendsto_and_summable_norm_sub_of_interior_nonempty
    (hxₙ : FejerMonotone C xₙ) (hC_int : (interior C).Nonempty) :
    ∃ x : H, Tendsto xₙ atTop (𝓝 x) ∧ Summable (fun n ↦ ‖xₙ (n + 1) - xₙ n‖) := by
  rcases hC_int with ⟨c, hc_int⟩
  rcases Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hc_int) with ⟨ε, hε, hball⟩
  let ρ : ℝ := ε / 2
  have hρ : 0 < ρ := by
    dsimp [ρ]
    positivity
  have hρε : ρ < ε := by
    dsimp [ρ]
    linarith
  have hpartial :
      ∀ N : ℕ, Finset.sum (Finset.range N) (fun i ↦ ‖xₙ (i + 1) - xₙ i‖) ≤
        ‖xₙ 0 - c‖ ^ 2 / (2 * ρ) := by
    -- The interior-point descent estimate gives a uniform bound on all partial sums.
    intro N
    exact partial_sum_norm_sub_le_of_fejer_sqnorm_drop hxₙ hball hρ hρε N
  have hsummable : Summable (fun n ↦ ‖xₙ (n + 1) - xₙ n‖) :=
    summable_of_sum_range_le (fun n ↦ norm_nonneg _) hpartial
  have hsummable_dist : Summable (fun n ↦ dist (xₙ n) (xₙ (n + 1))) := by
    simpa [dist_eq_norm, norm_sub_rev] using hsummable
  have hcauchy : CauchySeq xₙ :=
    cauchySeq_of_summable_dist hsummable_dist
  -- Completeness upgrades the Cauchy property to strong convergence in `H`.
  rcases cauchySeq_tendsto_of_complete hcauchy with ⟨x, hx⟩
  exact ⟨x, hx, hsummable⟩

end FejerMonotone

end
