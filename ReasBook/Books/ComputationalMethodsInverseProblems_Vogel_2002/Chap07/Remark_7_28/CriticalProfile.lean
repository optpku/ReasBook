/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_27.Benchmark

public section

noncomputable section

namespace TikhonovDiscrepancy

/-- Helper for Remark 7.28: the critical logarithmic profile exponent is
strictly positive in the admissible regime `p > 1`. -/
private lemma criticalProfileExponent_pos_local
    {p : ℝ} (h_p : 1 < p) :
    0 < ((2 * p + 1) / p : ℝ) := by
  have h_p0 : 0 < p := by
    linarith
  have h_num : 0 < 2 * p + 1 := by
    linarith
  exact div_pos h_num h_p0

/-- Helper for Remark 7.28: the small-branch cutoff for the critical
logarithmic profile is strictly positive. -/
private lemma criticalProfileUpper_pos_local
    (p : ℝ) :
    0 < Real.exp (-(p / (2 * p + 1))) :=
  Real.exp_pos _

/-- Helper for Remark 7.28: the small-branch cutoff lies below `1` once
`p > 1`. -/
private lemma criticalProfileUpper_lt_one_local
    {p : ℝ} (h_p : 1 < p) :
    Real.exp (-(p / (2 * p + 1))) < 1 := by
  have h_p0 : 0 < p := by
    linarith
  have h_den : 0 < 2 * p + 1 := by
    linarith
  have h_frac : 0 < p / (2 * p + 1) := by
    exact div_pos h_p0 h_den
  exact Real.exp_lt_one_iff.2 (by linarith)

/-- Helper for Remark 7.28: the theorem-local critical profile written in the
same source shape as the benchmark root equation. -/
@[expose] def criticalProfileLocal (p β : ℝ) : ℝ :=
  -(β ^ ((2 * p + 1) / p) * Real.log β)

/-- Helper for Remark 7.28: unfold the theorem-local critical profile to the
displayed logarithmic source expression. -/
@[simp] theorem criticalProfileLocal_def (p β : ℝ) :
    criticalProfileLocal p β =
      -(β ^ ((2 * p + 1) / p) * Real.log β) :=
  rfl

/-- Helper for Remark 7.28: the local critical profile equals a positive scalar
multiple of `Real.negMulLog` along the positive branch. -/
private lemma criticalProfile_eq_scaled_negMulLog_local
    {p β : ℝ} (h_p : 1 < p) (hβ : 0 < β) :
    criticalProfileLocal p β =
      (p / (2 * p + 1)) * Real.negMulLog (β ^ ((2 * p + 1) / p)) := by
  have hp_ne : p ≠ 0 := by
    linarith
  have hden_ne : 2 * p + 1 ≠ 0 := by
    linarith
  -- Rewrite the logarithm of the powered branch and cancel the scalar factor once.
  calc
    criticalProfileLocal p β
        = -(β ^ ((2 * p + 1) / p) * Real.log β) := by
            rw [criticalProfileLocal]
    _ = -(β ^ ((2 * p + 1) / p)) * Real.log β := by
          ring
    _ = (p / (2 * p + 1)) *
          (-(β ^ ((2 * p + 1) / p)) * Real.log (β ^ ((2 * p + 1) / p))) := by
            rw [Real.log_rpow hβ]
            field_simp [hp_ne, hden_ne]
    _ = (p / (2 * p + 1)) * Real.negMulLog (β ^ ((2 * p + 1) / p)) := by
          rfl

/-- Helper for Remark 7.28: rescaling the benchmark input by a fixed positive
factor rewrites the theorem-local critical profile by one exact logarithmic
correction term. -/
theorem criticalProfile_scale_exact_local
    {p t β : ℝ} (ht : 0 < t) (hβ : 0 < β) :
    criticalProfileLocal p (t * β) =
      t ^ ((2 * p + 1) / p) * criticalProfileLocal p β -
        t ^ ((2 * p + 1) / p) * β ^ ((2 * p + 1) / p) * Real.log t := by
  -- Expand the scaled logarithm and then factor the shared benchmark power.
  calc
    criticalProfileLocal p (t * β)
        = -((t * β) ^ ((2 * p + 1) / p) * Real.log (t * β)) := by
            rw [criticalProfileLocal]
    _ = -((t ^ ((2 * p + 1) / p) * β ^ ((2 * p + 1) / p)) *
          (Real.log t + Real.log β)) := by
            rw [Real.mul_rpow (le_of_lt ht) (le_of_lt hβ), Real.log_mul ht.ne' hβ.ne']
    _ = -(t ^ ((2 * p + 1) / p) * β ^ ((2 * p + 1) / p) * Real.log t) +
          -(t ^ ((2 * p + 1) / p) * β ^ ((2 * p + 1) / p) * Real.log β) := by
            ring
    _ = -(t ^ ((2 * p + 1) / p) * β ^ ((2 * p + 1) / p) * Real.log t) +
          t ^ ((2 * p + 1) / p) * criticalProfileLocal p β := by
            rw [criticalProfileLocal]
            ring
    _ = t ^ ((2 * p + 1) / p) * criticalProfileLocal p β -
          t ^ ((2 * p + 1) / p) * β ^ ((2 * p + 1) / p) * Real.log t := by
            ring

/-- Helper for Remark 7.28: the small-branch cutoff is sent to `exp (-1)` by
the local critical-profile exponent. -/
private lemma criticalProfileUpper_rpow_eq_local
    {p : ℝ} (h_p : 1 < p) :
    Real.exp (-(p / (2 * p + 1))) ^ ((2 * p + 1) / p) = Real.exp (-1) := by
  have hp_ne : p ≠ 0 := by
    linarith
  have hden_ne : 2 * p + 1 ≠ 0 := by
    linarith
  have hmul :
      (-(p / (2 * p + 1)) : ℝ) * ((2 * p + 1) / p) = -1 := by
    field_simp [hp_ne, hden_ne]
  rw [← Real.exp_mul, hmul]

/-- Helper for Remark 7.28: the local critical profile endpoint value on the
small branch is explicit. -/
private lemma criticalProfileUpper_value_local
    {p : ℝ} (h_p : 1 < p) :
    criticalProfileLocal p (Real.exp (-(p / (2 * p + 1)))) =
      (p / (2 * p + 1)) * Real.exp (-1) := by
  rw [criticalProfile_eq_scaled_negMulLog_local h_p (criticalProfileUpper_pos_local p)]
  rw [criticalProfileUpper_rpow_eq_local h_p]
  simp [Real.negMulLog_def]

/-- Helper for Remark 7.28: the explicit endpoint value of the local critical
profile is strictly positive. -/
private lemma criticalProfileUpper_value_pos_local
    {p : ℝ} (h_p : 1 < p) :
    0 < criticalProfileLocal p (Real.exp (-(p / (2 * p + 1)))) := by
  have h_p0 : 0 < p := by
    linarith
  have h_den : 0 < 2 * p + 1 := by
    linarith
  rw [criticalProfileUpper_value_local h_p]
  exact mul_pos (div_pos h_p0 h_den) (Real.exp_pos _)

/-- Helper for Remark 7.28: on the positive small branch, the theorem-local
critical logarithmic profile is strictly increasing. -/
theorem criticalProfile_strictMonoOn_smallBranch_local
    {p : ℝ} (h_p : 1 < p) :
    StrictMonoOn (criticalProfileLocal p) (Set.Ioc 0 (Real.exp (-(p / (2 * p + 1))))) := by
  have h_exp_pos : 0 < ((2 * p + 1) / p : ℝ) :=
    criticalProfileExponent_pos_local h_p
  have h_scale_pos : 0 < p / (2 * p + 1) := by
    have h_p0 : 0 < p := by
      linarith
    have h_den : 0 < 2 * p + 1 := by
      linarith
    exact div_pos h_p0 h_den
  have h_negMulLog_mono :
      StrictMonoOn Real.negMulLog (Set.Icc (0 : ℝ) (Real.exp (-1))) := by
    refine strictMonoOn_of_deriv_pos (D := Set.Icc (0 : ℝ) (Real.exp (-1)))
      (convex_Icc _ _) Real.continuous_negMulLog.continuousOn ?_
    intro x hx
    rw [interior_Icc] at hx
    have hx_pos : 0 < x := hx.1
    have hx_lt : x < Real.exp (-1) := hx.2
    -- The derivative is `-log x - 1`, which is positive exactly before `exp (-1)`.
    rw [Real.deriv_negMulLog hx_pos.ne']
    have hlog_lt : Real.log x < -1 :=
      (Real.log_lt_iff_lt_exp hx_pos).2 hx_lt
    linarith
  have h_rpow_mono :
      StrictMonoOn (fun β : ℝ ↦ β ^ ((2 * p + 1) / p))
        (Set.Ioc 0 (Real.exp (-(p / (2 * p + 1))))) := by
    intro x hx y hy hxy
    exact Real.rpow_lt_rpow hx.1.le hxy h_exp_pos
  have h_rpow_maps :
      Set.MapsTo
        (fun β : ℝ ↦ β ^ ((2 * p + 1) / p))
        (Set.Ioc 0 (Real.exp (-(p / (2 * p + 1)))))
        (Set.Icc (0 : ℝ) (Real.exp (-1))) := by
    intro β hβ
    refine ⟨le_of_lt (Real.rpow_pos_of_pos hβ.1 _), ?_⟩
    have hβ_le :
        β ^ ((2 * p + 1) / p) ≤
          Real.exp (-(p / (2 * p + 1))) ^ ((2 * p + 1) / p) := by
      exact Real.rpow_le_rpow hβ.1.le hβ.2 h_exp_pos.le
    simpa [criticalProfileUpper_rpow_eq_local h_p] using hβ_le
  have h_comp :
      StrictMonoOn
        (fun β : ℝ ↦ Real.negMulLog (β ^ ((2 * p + 1) / p)))
        (Set.Ioc 0 (Real.exp (-(p / (2 * p + 1))))) :=
    h_negMulLog_mono.comp h_rpow_mono h_rpow_maps
  intro x hx y hy hxy
  -- Rewrite the local critical profile through `negMulLog`, then use the
  -- positive scalar factor.
  rw [criticalProfile_eq_scaled_negMulLog_local h_p hx.1,
    criticalProfile_eq_scaled_negMulLog_local h_p hy.1]
  exact mul_lt_mul_of_pos_left (h_comp hx hy hxy) h_scale_pos

/-- Helper for Remark 7.28: the local critical profile divided by the input
leaves the vanishing factor `-log x * x^((p + 1) / p)`. -/
private lemma criticalProfile_div_self_tendsto_zero_local
    {p : ℝ} (h_p : 1 < p) :
    Filter.Tendsto
      (fun x : ℝ ↦ criticalProfileLocal p x / x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have h_exp_pos : 0 < ((p + 1) / p : ℝ) := by
    have h_p0 : 0 < p := by
      linarith
    exact div_pos (by linarith) h_p0
  have h_log :
      Filter.Tendsto
        (fun x : ℝ ↦ Real.log x * x ^ ((p + 1) / p))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    tendsto_log_mul_rpow_nhdsGT_zero h_exp_pos
  have h_rewrite :
      (fun x : ℝ ↦ criticalProfileLocal p x / x) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
        (fun x : ℝ ↦ -(Real.log x * x ^ ((p + 1) / p))) := by
    filter_upwards [eventually_mem_nhdsWithin] with x hx
    have hx_ne : x ≠ 0 := ne_of_gt hx
    have hp_ne : p ≠ 0 := by
      linarith
    have h_exp :
        (((2 * p + 1) / p : ℝ) - 1) = (p + 1) / p := by
      field_simp [hp_ne]
      ring
    -- Rewrite the normalized profile to the exact logarithmic-power shape
    -- used by the mathlib limit theorem.
    calc
      criticalProfileLocal p x / x
          = -(x ^ ((2 * p + 1) / p) * Real.log x) / x := by
              rw [criticalProfileLocal]
      _ = -((x ^ ((2 * p + 1) / p) * Real.log x) / x) := by
            rw [neg_div]
      _ = -((x ^ ((2 * p + 1) / p) / x) * Real.log x) := by
            congr 1
            field_simp [hx_ne]
      _ = -(x ^ (((2 * p + 1) / p : ℝ) - 1) * Real.log x) := by
            rw [← Real.rpow_sub_one hx_ne ((2 * p + 1) / p)]
      _ = -(Real.log x * x ^ (((2 * p + 1) / p : ℝ) - 1)) := by
            congr 1
            ac_rfl
      _ = -(Real.log x * x ^ ((p + 1) / p)) := by
            rw [h_exp]
  -- After the normalization, the desired limit is exactly the negated
  -- logarithmic-power asymptotic.
  refine Filter.Tendsto.congr' h_rewrite.symm ?_
  simpa using h_log.neg

/-- Helper for Remark 7.28: on the positive branch close to `0`, the theorem-
local critical profile lies strictly below the identity. -/
theorem criticalProfile_lt_self_eventually_small_local
    {p : ℝ} (h_p : 1 < p) :
    ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi 0), criticalProfileLocal p x < x := by
  have h_ratio_lt_one :
      ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi 0), criticalProfileLocal p x / x < 1 := by
    exact (criticalProfile_div_self_tendsto_zero_local h_p).eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [h_ratio_lt_one, eventually_mem_nhdsWithin] with x hx_ratio hx_pos
  -- Multiply the normalized inequality by the positive input to recover the
  -- pointwise small-branch estimate.
  have hx : criticalProfileLocal p x < 1 * x := by
    exact (div_lt_iff₀ hx_pos).mp hx_ratio
  simpa using hx

/-- Helper for Remark 7.28: the local critical-profile endpoint value is
strictly positive, so later comparisons can squeeze against a fixed barrier. -/
theorem criticalProfileUpper_value_pos_local_export
    {p : ℝ} (h_p : 1 < p) :
    0 < criticalProfileLocal p (Real.exp (-(p / (2 * p + 1)))) := by
  -- Re-export the private endpoint positivity lemma with a theorem-local name.
  exact criticalProfileUpper_value_pos_local h_p

end TikhonovDiscrepancy
