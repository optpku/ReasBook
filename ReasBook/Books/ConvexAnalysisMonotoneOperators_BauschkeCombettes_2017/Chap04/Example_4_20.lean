/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Example_2_32_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Text_2_0_14
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_16_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Topology
open Filter

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "C" => Metric.closedBall (0 : H) 1

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Example 4.20: the closed unit ball is nonempty. -/
private theorem closedUnitBall_nonempty :
    (Metric.closedBall (0 : H) 1 : Set H).Nonempty := by
  refine ⟨0, ?_⟩
  simp [Metric.mem_closedBall]

local notation "P" =>
  projectionPoint C
    (isChebyshev_of_nonempty_isClosed_convex
      closedUnitBall_nonempty
      (Metric.isClosed_closedBall : IsClosed C)
      (convex_closedBall (0 : H) 1))

/-- Helper for Example 4.20: the metric projector onto the closed unit ball has the expected
radial formula. -/
private theorem projectionPoint_closedUnitBall_eq_radial_clip (x : H) :
    P x = if 1 < ‖x‖ then ‖x‖⁻¹ • x else x := by
  have hC_closed : IsClosed C := Metric.isClosed_closedBall
  have hC_convex : Convex ℝ C := convex_closedBall (0 : H) 1
  by_cases hx : 1 < ‖x‖
  · have hnormx_pos : 0 < ‖x‖ := lt_trans zero_lt_one hx
    have hnormx : ‖x‖ ≠ 0 := hnormx_pos.ne'
    have hp_norm : ‖‖x‖⁻¹ • x‖ = 1 := by
      calc
        ‖‖x‖⁻¹ • x‖ = |‖x‖⁻¹| * ‖x‖ := norm_smul _ _
        _ = ‖x‖⁻¹ * ‖x‖ := by
          rw [abs_of_pos (inv_pos.mpr hnormx_pos)]
        _ = 1 := by
          rw [inv_mul_cancel₀ hnormx]
    have hp_inner : inner ℝ (‖x‖⁻¹ • x) x = ‖x‖ := by
      calc
        inner ℝ (‖x‖⁻¹ • x) x = ‖x‖⁻¹ * inner ℝ x x := by
          rw [real_inner_smul_left]
        _ = ‖x‖⁻¹ * ‖x‖ ^ 2 := by
          rw [real_inner_self_eq_norm_sq]
        _ = ‖x‖ := by
          rw [pow_two]
          ring_nf
          field_simp [hnormx]
    have hproj :
        ‖x‖⁻¹ • x = P x := by
      refine
        (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
          closedUnitBall_nonempty hC_closed hC_convex).mpr ?_
      refine ⟨?_, ?_⟩
      · show dist (‖x‖⁻¹ • x) 0 ≤ 1
        simp [dist_eq_norm, hp_norm]
      · intro y hy
        have hy_norm : ‖y‖ ≤ 1 := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hy
        have hy_inner : inner ℝ y x ≤ ‖x‖ := by
          calc
            inner ℝ y x ≤ ‖y‖ * ‖x‖ := real_inner_le_norm y x
            _ ≤ 1 * ‖x‖ := by gcongr
            _ = ‖x‖ := by ring
        have hcoef_nonneg : 0 ≤ 1 - ‖x‖⁻¹ := by
          have hinv_lt : ‖x‖⁻¹ < 1 := by
            exact inv_lt_one_of_one_lt₀ hx
          linarith
        calc
          inner ℝ (y - ‖x‖⁻¹ • x) (x - ‖x‖⁻¹ • x)
              = (1 - ‖x‖⁻¹) * inner ℝ (y - ‖x‖⁻¹ • x) x := by
                  rw [show x - ‖x‖⁻¹ • x = (1 - ‖x‖⁻¹) • x by
                    calc
                      x - ‖x‖⁻¹ • x = (1 : ℝ) • x - ‖x‖⁻¹ • x := by
                        rw [one_smul]
                      _ = (1 - ‖x‖⁻¹) • x := by
                        rw [sub_smul], real_inner_smul_right]
          _ ≤ 0 := by
            refine mul_nonpos_of_nonneg_of_nonpos hcoef_nonneg ?_
            calc
              inner ℝ (y - ‖x‖⁻¹ • x) x = inner ℝ y x - inner ℝ (‖x‖⁻¹ • x) x := by
                rw [inner_sub_left]
              _ ≤ 0 := by
                linarith [hy_inner, hp_inner]
    simpa [hx] using hproj.symm
  · have hx_mem : x ∈ C := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using le_of_not_gt hx
    have hproj :
        x = P x := by
      refine
        (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
          closedUnitBall_nonempty hC_closed hC_convex).mpr ?_
      refine ⟨hx_mem, ?_⟩
      intro y hy
      simp
    simpa [hx] using hproj.symm

/-- Helper for Example 4.20: on the closed unit ball, the canonical metric projector acts as the
identity. -/
private theorem projectionPoint_closedUnitBall_eq_self_of_norm_le_one {x : H} (hx : ‖x‖ ≤ 1) :
    P x = x := by
  rw [projectionPoint_closedUnitBall_eq_radial_clip]
  simp [not_lt_of_ge hx]

/-- Helper for Example 4.20: outside the closed unit ball, the canonical metric projector rescales
a vector to norm `1`. -/
private theorem projectionPoint_closedUnitBall_eq_inv_norm_smul_of_one_lt_norm {x : H}
    (hx : 1 < ‖x‖) :
    P x = ‖x‖⁻¹ • x := by
  rw [projectionPoint_closedUnitBall_eq_radial_clip]
  simp [hx]

/-- Helper for Example 4.20: translating the weakly null tail of an orthonormal sequence by its
first vector yields weak convergence to that first vector. -/
private lemma orthonormal_base_add_succ_tendsto_base_weakly (e : ℕ → H) (he : Orthonormal ℝ e) :
    Tendsto (fun n ↦ toWeakSpace ℝ H (e 0 + e (n + 1))) atTop
      (𝓝 (toWeakSpace ℝ H (e 0))) := by
  have htail :
      Tendsto (fun n ↦ toWeakSpace ℝ H (e (n + 1))) atTop
        (𝓝 (0 : WeakSpace ℝ H)) :=
    orthonormal_sequence_tendsto_zero_weakly (fun n ↦ e (n + 1))
      (he.comp Nat.succ Nat.succ_injective)
  have hconst :
      Tendsto (fun _ : ℕ ↦ toWeakSpace ℝ H (e 0)) atTop
        (𝓝 (toWeakSpace ℝ H (e 0))) :=
    tendsto_const_nhds
  simpa [toWeakSpace] using hconst.add htail

omit [CompleteSpace H] in
/-- Helper for Example 4.20: orthogonality of the two summands forces the witness sequence
`e 0 + e (n + 1)` to have constant norm `√2`. -/
private lemma orthonormal_base_add_succ_norm_eq_sqrt_two
    (e : ℕ → H) (he : Orthonormal ℝ e) (n : ℕ) :
    ‖e 0 + e (n + 1)‖ = Real.sqrt 2 := by
  have hsq : ‖e 0 + e (n + 1)‖ ^ 2 = 2 := by
    rw [norm_add_sq_real]
    have h0 : ‖e 0‖ = 1 := he.norm_eq_one 0
    have h1 : ‖e (n + 1)‖ = 1 := he.norm_eq_one (n + 1)
    have hinner : inner ℝ (e 0) (e (n + 1)) = 0 := he.inner_eq_zero (Nat.succ_ne_zero n).symm
    nlinarith
  have hsqrt := congrArg Real.sqrt hsq
  have hnorm_nonneg : 0 ≤ ‖e 0 + e (n + 1)‖ := norm_nonneg _
  simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg hnorm_nonneg] using hsqrt

-- Proof sketch: choose an orthonormal sequence `(e_n)` in the infinite-dimensional Hilbert space
-- and consider `x n = e 0 + e (n + 1)`. Then `x n` converges weakly to `e 0`, while the
-- canonical projector onto the closed unit ball satisfies `P (x n) = (1 / √2) • x n`, which
-- converges weakly to `(1 / √2) • e 0`. Since `P (e 0) = e 0`, weak continuity would force
-- `(1 / √2) • e 0 = e 0`, contradicting `√2 ≠ 1`.
/-- Example 4.20: in an infinite-dimensional real Hilbert space, the metric projector onto the
closed unit ball is not weakly continuous. -/
theorem closedUnitBallProjector_not_weaklyContinuous
    (h_infinite : ¬ FiniteDimensional ℝ H) :
    ¬ WeaklyContinuous (fun x : (Set.univ : Set H) ↦ P x) := by
  intro hweak
  obtain ⟨e, he⟩ := exists_orthonormal_sequence_of_not_finiteDimensional h_infinite
  let x : ℕ → H := fun n ↦ e 0 + e (n + 1)
  have hx :
      Tendsto (fun n ↦ toWeakSpace ℝ H (x n)) atTop
        (𝓝 (toWeakSpace ℝ H (e 0))) := by
    simpa [x] using orthonormal_base_add_succ_tendsto_base_weakly e he
  have hx_norm : ∀ n, ‖x n‖ = Real.sqrt 2 := by
    intro n
    simpa [x] using orthonormal_base_add_succ_norm_eq_sqrt_two e he n
  have hproj_formula : ∀ n, P (x n) = (1 / Real.sqrt 2 : ℝ) • x n := by
    intro n
    have hnorm_gt_one : 1 < ‖x n‖ := by
      simpa [hx_norm n] using Real.one_lt_sqrt_two
    calc
      P (x n) = ‖x n‖⁻¹ • x n :=
        projectionPoint_closedUnitBall_eq_inv_norm_smul_of_one_lt_norm hnorm_gt_one
      _ = (1 / Real.sqrt 2 : ℝ) • x n := by
        simp [hx_norm n, one_div]
  have hproj_scaled :
      Tendsto (fun n ↦ toWeakSpace ℝ H (P (x n))) atTop
        (𝓝 (toWeakSpace ℝ H ((1 / Real.sqrt 2 : ℝ) • e 0))) := by
    have hscaled :
        Tendsto (fun n ↦ (1 / Real.sqrt 2 : ℝ) • toWeakSpace ℝ H (x n)) atTop
          (𝓝 ((1 / Real.sqrt 2 : ℝ) • toWeakSpace ℝ H (e 0))) :=
      hx.const_smul (1 / Real.sqrt 2 : ℝ)
    simpa [hproj_formula, toWeakSpace] using hscaled
  have he0_norm_le_one : ‖e 0‖ ≤ 1 := by
    simp [he.norm_eq_one 0]
  have hproj_cont :
      Tendsto (fun n ↦ toWeakSpace ℝ H (P (x n))) atTop
        (𝓝 (toWeakSpace ℝ H (e 0))) := by
    rw [weaklyContinuous_iff_forall_net_tendsto] at hweak
    have hmap :=
      hweak (fun n ↦ ⟨x n, Set.mem_univ (x n)⟩) ⟨e 0, Set.mem_univ (e 0)⟩ hx
    simpa [projectionPoint_closedUnitBall_eq_self_of_norm_le_one he0_norm_le_one] using hmap
  have hlimit_eq :
      toWeakSpace ℝ H ((1 / Real.sqrt 2 : ℝ) • e 0) = toWeakSpace ℝ H (e 0) :=
    tendsto_nhds_unique hproj_scaled hproj_cont
  have hvector_eq : ((1 / Real.sqrt 2 : ℝ) • e 0) = e 0 :=
    (toWeakSpace ℝ H).injective hlimit_eq
  have hscalar_eq : (1 / Real.sqrt 2 : ℝ) = 1 := by
    have hinner_eq := congrArg (fun z : H ↦ inner ℝ z (e 0)) hvector_eq
    simp [real_inner_smul_left, he.norm_eq_one 0] at hinner_eq
  have hsqrt_two_eq_one : Real.sqrt 2 = 1 := by
    have hinv_eq := congrArg (fun t : ℝ ↦ t⁻¹) hscalar_eq
    simp [one_div] at hinv_eq
  have hsqrt_two_ne_one : Real.sqrt 2 ≠ 1 := by
    linarith [Real.one_lt_sqrt_two]
  exact hsqrt_two_ne_one hsqrt_two_eq_one

end
