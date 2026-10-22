/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Exercise_3_1.Convergence

public section

universe u

namespace ConvergenceRate

variable {H : Type u} [NormedAddCommGroup H] (f : ℕ → H) (fStar : H)

/-- Helper for Exercise 3.1: a quadratic error bound with coefficient `C > 0`
is dominated by a strictly positive vanishing linear control sequence. -/
lemma quadraticControl_le_vanishingLinearControl
    (hconv : Filter.Tendsto f Filter.atTop (nhds fStar))
    {C : ℝ} (hC : 0 < C) :
    ∃ c : ℕ → ℝ,
      (∀ v : ℕ, 0 < c v) ∧
        Filter.Tendsto c Filter.atTop (nhds 0) ∧
          ∀ v : ℕ, C * ‖f v - fStar‖ ^ 2 ≤ c v * ‖f v - fStar‖ := by
  -- Convert convergence of the iterates into convergence of the error norms.
  have hconst : Filter.Tendsto (fun _ : ℕ => fStar) Filter.atTop (nhds fStar) :=
    tendsto_const_nhds
  have hsub : Filter.Tendsto (fun v => f v - fStar) Filter.atTop (nhds 0) := by
    simpa using hconv.sub hconst
  have hnorm : Filter.Tendsto (fun v => ‖f v - fStar‖) Filter.atTop (nhds 0) := by
    simpa using hsub.norm
  -- Use a positive perturbation so the control coefficient stays strictly positive.
  refine ⟨fun v => C * ‖f v - fStar‖ + 1 / ((v : ℝ) + 1), ?_, ?_, ?_⟩
  · intro v
    have hrecip : 0 < 1 / ((v : ℝ) + 1) := by
      positivity
    have hmul : 0 ≤ C * ‖f v - fStar‖ := by
      exact mul_nonneg hC.le (norm_nonneg _)
    linarith
  · have hmul :
        Filter.Tendsto (fun v => C * ‖f v - fStar‖) Filter.atTop (nhds (C * 0)) := by
      simpa using hnorm.const_mul C
    have hrecip :
        Filter.Tendsto (fun v : ℕ => 1 / ((v : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using hmul.add hrecip
  · intro v
    have hnorm_nonneg : 0 ≤ ‖f v - fStar‖ := norm_nonneg _
    have hrecip_nonneg : 0 ≤ 1 / ((v : ℝ) + 1) := by
      positivity
    simp only [pow_two]
    nlinarith [mul_nonneg hrecip_nonneg hnorm_nonneg]

/-- Exercise 3.1 (1). Under the Definition 3.1 setup for a convergent sequence
`f v ⟶ fStar`, the quadratic estimate `(3.3)` implies the superlinear estimate
`(3.2)`. -/
theorem quadraticEstimate_implies_superlinearEstimate
    (hconv : Filter.Tendsto f Filter.atTop (nhds fStar))
    (h33 : quadraticEstimate f fStar) :
    superlinearEstimate f fStar := by
  rw [quadraticEstimate_iff] at h33
  rw [superlinearEstimate_iff]
  rcases h33 with ⟨C, hC, v0, hv0⟩
  -- Package the quadratic coefficient into a positive control that tends to zero.
  rcases quadraticControl_le_vanishingLinearControl (f := f) (fStar := fStar) hconv hC with
    ⟨c, hc_pos, hc_tendsto, hc_dom⟩
  refine ⟨c, hc_pos, hc_tendsto, v0, ?_⟩
  -- Reuse the original threshold and bound the quadratic term by the new control.
  intro v hv
  exact (hv0 v hv).trans (hc_dom v)

/-- Exercise 3.1 (2). The superlinear estimate `(3.2)` implies the linear
estimate `(3.1)`. -/
theorem superlinearEstimate_implies_linearEstimate
    (h32 : superlinearEstimate f fStar) :
    linearEstimate f fStar := by
  rw [superlinearEstimate_iff] at h32
  rw [linearEstimate_iff]
  rcases h32 with ⟨c, hc_pos, hc_tendsto, v0, hv0⟩
  have hhalf_pos : 0 < (1 : ℝ) / 2 := by
    norm_num
  -- Extract an index beyond which the vanishing control is below `1 / 2`.
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (hc_tendsto.eventually (Iio_mem_nhds hhalf_pos))
  refine ⟨(1 : ℝ) / 2, ?_, ?_, max v0 N, ?_⟩
  · norm_num
  · norm_num
  · intro v hv
    have hv0' : ‖f (v + 1) - fStar‖ ≤ c v * ‖f v - fStar‖ := by
      exact hv0 v (le_trans (le_max_left _ _) hv)
    have hc_small : c v < (1 : ℝ) / 2 := by
      exact hN v (le_trans (le_max_right _ _) hv)
    have hnorm_nonneg : 0 ≤ ‖f v - fStar‖ := norm_nonneg _
    -- Freeze the variable coefficient by the fixed contraction factor `1 / 2`.
    calc
      ‖f (v + 1) - fStar‖ ≤ c v * ‖f v - fStar‖ := hv0'
      _ ≤ ((1 : ℝ) / 2) * ‖f v - fStar‖ := by
        exact mul_le_mul_of_nonneg_right (le_of_lt hc_small) hnorm_nonneg

end ConvergenceRate
