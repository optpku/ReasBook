/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_15.OptimalIndex
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

public section

noncomputable section

namespace TsvdEstimation

/-- The real-valued profile whose floor defines the TSVD optimal truncation
index `(7.63)`. -/
def optimalIndexProfile (b c p q σ : ℝ) : ℕ → ℝ :=
  fun n ↦ ((b * c) ^ (1 / (p + q))) * (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q))))

/-- The defining pointwise formula for `optimalIndexProfile`. -/
theorem optimalIndexProfile_def (b c p q σ : ℝ) (n : ℕ) :
    optimalIndexProfile b c p q σ n =
      ((b * c) ^ (1 / (p + q))) * (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q)))) := by
  rfl

/-- The real-valued TSVD index profile tends to `+∞`. -/
private theorem optimalIndexProfile_tendstoAtTop
    (b c p q σ : ℝ)
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q) (h_σ : 0 < σ) :
    Filter.Tendsto (optimalIndexProfile b c p q σ) Filter.atTop Filter.atTop := by
  have hpq_pos : 0 < p + q := by
    linarith
  have h_prefactor_pos : 0 < (b * c) ^ (1 / (p + q)) := by
    exact Real.rpow_pos_of_pos (mul_pos h_b h_c) _
  have h_ratio_tendsto_zero :
      Filter.Tendsto (fun n : ℕ ↦ (σ ^ 2) / (n : ℝ)) Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      (Filter.Tendsto.const_mul (σ ^ 2)
        (tendsto_inv_atTop_nhds_zero_nat :
          Filter.Tendsto (fun n : ℕ ↦ ((n : ℝ)⁻¹)) Filter.atTop (nhds 0)))
  have h_ratio_eventually_pos : ∀ᶠ n : ℕ in Filter.atTop, (σ ^ 2) / (n : ℝ) ∈ Set.Ioi 0 := by
    filter_upwards [Filter.Ici_mem_atTop 1] with n hn
    have hn_pos : 0 < (n : ℝ) := by
      exact Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hn)
    change 0 < (σ ^ 2) / (n : ℝ)
    positivity
  have h_ratio_tendsto_nhdsGT_zero :
      Filter.Tendsto (fun n : ℕ ↦ (σ ^ 2) / (n : ℝ)) Filter.atTop
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    exact tendsto_nhdsWithin_iff.mpr ⟨h_ratio_tendsto_zero, h_ratio_eventually_pos⟩
  have h_power_tendsto_atTop :
      Filter.Tendsto
        (fun n : ℕ ↦ ((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q))))
        Filter.atTop Filter.atTop := by
    refine (tendsto_rpow_neg_nhdsGT_zero ?_).comp h_ratio_tendsto_nhdsGT_zero
    have h_inv_pos : 0 < 1 / (p + q) := one_div_pos.mpr hpq_pos
    linarith
  unfold optimalIndexProfile
  exact Filter.Tendsto.const_mul_atTop h_prefactor_pos h_power_tendsto_atTop

/-- The floor-defined optimal index is asymptotically equivalent to its
underlying real-valued profile. -/
theorem optimalIndexCast_isEquivalent_profile
    (b c p q σ : ℝ)
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q) (h_σ : 0 < σ) :
    Asymptotics.IsEquivalent Filter.atTop
      (fun n ↦ (optimalIndex b c p q σ n : ℝ))
      (optimalIndexProfile b c p q σ) := by
  unfold optimalIndexProfile
  simpa [optimalIndex_def, optimalIndexProfile, Function.comp_def] using
    (Asymptotics.isEquivalent_nat_floor.comp_tendsto
      (optimalIndexProfile_tendstoAtTop b c p q σ h_b h_c h_p h_q h_σ))

end TsvdEstimation
