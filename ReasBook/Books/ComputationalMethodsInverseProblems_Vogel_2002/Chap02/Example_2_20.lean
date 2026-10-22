/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Remark_1_2

public section

open Filter
open scoped Topology

/-- Example 2.20 (1): for the TSVD and Tikhonov scalar filters, the Chapter 2
filter-limit condition `(2.28)` holds with parameter threshold `0`, expressed as
`w α (s ^ 2) → 1` as `α → 0+` for each `s > 0`. -/
theorem tsvdOrTikhonovFilterLimit
    {w : ℝ → ℝ → ℝ} {s : ℝ}
    (h_filter : w = SpectralFilter.tsvd ∨ w = SpectralFilter.tikhonov)
    (hs : 0 < s) :
    Tendsto
      (fun α : ℝ ↦ w α (s ^ 2))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (𝓝 (1 : ℝ)) := by
  have h :=
    (FilterRegularization.filterValueSubOne_tendstoZero_of_eq_tsvd_or_tikhonov hs h_filter).add
      (show Tendsto (fun _ : ℝ ↦ (1 : ℝ))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (𝓝 (1 : ℝ)) from tendsto_const_nhds)
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h

/- Example 2.20 (2): for the TSVD and Tikhonov scalar filters, the inverse-factor
bound `w α (s ^ 2) / s ≤ 1 / Real.sqrt α` is exactly the reusable Chapter 1 theorem
`SpectralFilter.inverseBound_of_eq_tsvd_or_tikhonov`. -/
#check SpectralFilter.inverseBound_of_eq_tsvd_or_tikhonov

/-- Example 2.20 (3): the concrete parameter rule `α = δ` satisfies the Chapter 2
parameter-choice limit condition `(2.29)`, namely `δ → 0` as `δ → 0+`. -/
theorem alphaEqDeltaTendstoZero :
    Tendsto
      (fun δ : ℝ ↦ δ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (𝓝 (0 : ℝ)) :=
  tendsto_id.mono_left nhdsWithin_le_nhds

/-- Example 2.20 (4): the concrete parameter rule `α = δ` satisfies the Chapter 2
inverse-bound limit condition `(2.30)`, namely `δ / Real.sqrt δ → 0` as
`δ → 0+`. -/
theorem deltaDivSqrtDeltaTendstoZero :
    Tendsto
      (fun δ : ℝ ↦ δ / Real.sqrt δ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (𝓝 (0 : ℝ)) := by
  have h :
      Tendsto
        (fun δ : ℝ ↦ δ / Real.sqrt (Real.rpow δ (1 : ℝ)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (𝓝 (0 : ℝ)) :=
    FilterRegularization.deltaDivSqrtRpow_tendstoZero zero_lt_one one_lt_two
  simpa [Real.rpow_one] using
    h
