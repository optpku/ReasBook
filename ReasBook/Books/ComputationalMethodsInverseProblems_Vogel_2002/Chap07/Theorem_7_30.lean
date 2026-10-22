/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Definition_7_33
import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_17.AsymptoticOptimalBridge
import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_17.OptimalIndexProfile
import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_16
import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_30.OptimalFamily
import Mathlib.MeasureTheory.Function.L2Space

section

open scoped TsvdEstimation.Notation

namespace TsvdEstimation

universe u v w

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {H : Type v} {F : Type w}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Helper for Theorem 7.30: eventual TSVD-GCV optimality already supplies the
source admissibility and denominator-valid inequality needed for later
benchmark arguments. -/
lemma gcvOptimalFamily_eventuallyAdmissible
    (μ : MeasureTheory.Measure Ω)
    (K : ℕ → H →L[ℝ] F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (fTrue : H)
    (η : ℕ → Ω → F)
    (mV : ℕ → ℕ)
    (h_gcvOptimal : TsvdGcv.IsOptimalFamilyEventually μ K Rtsvd fTrue η mV) :
    ∀ᶠ n in Filter.atTop, mV n ∈ 𝒵(n) ∧ mV n < n := by
  -- Unpack the GCV-valid admissibility back to the Chapter 7 source admissible
  -- set together with the strict denominator-validity inequality.
  filter_upwards [TsvdGcv.IsOptimalFamilyEventually.eventually_mem h_gcvOptimal] with n hn
  simpa [TsvdGcv.mem_gcvAdmissibleIndexSet_iff] using hn

/-- Helper for Theorem 7.30: for positive data size, the GCV-valid admissible
set is exactly the predecessor interval `Set.Icc 0 (n - 1)`. -/
lemma gcvAdmissibleIndexSet_eq_Icc_pred
    (n : ℕ)
    (hn : 0 < n) :
    TsvdGcv.gcvAdmissibleIndexSet n = Set.Icc 0 (n - 1) := by
  -- Rewrite the owned GCV-valid set once into the stable interval spelling
  -- used by the Chapter 7 discrete-difference lemmas.
  ext m
  rw [TsvdGcv.mem_gcvAdmissibleIndexSet_iff]
  constructor
  · intro hm
    refine ⟨hm.1.1, ?_⟩
    omega
  · intro hm
    refine ⟨?_, ?_⟩
    · exact ⟨hm.1, le_trans hm.2 (Nat.pred_le _)⟩
    · exact lt_of_le_of_lt hm.2 (Nat.pred_lt (Nat.ne_of_gt hn))

/-- Helper for Theorem 7.30: once both TSVD index families eventually agree
with the same benchmark `optimalIndex b c p q σ`, their real-valued coercions
are asymptotically equivalent. -/
lemma commonOptimalIndex_isEquivalent
    (b c p q σ : ℝ)
    (mV mE : ℕ → ℕ)
    (hV : mV =ᶠ[Filter.atTop] optimalIndex b c p q σ)
    (hE : mE =ᶠ[Filter.atTop] optimalIndex b c p q σ) :
    Asymptotics.IsEquivalent Filter.atTop
      (fun n ↦ (mV n : ℝ))
      (fun n ↦ (mE n : ℝ)) := by
  -- Eventual agreement with the same integer benchmark yields eventual equality
  -- after coercion to the real-valued parameter-choice interface.
  have hVEq :
      (fun n ↦ (mV n : ℝ)) =ᶠ[Filter.atTop] (fun n ↦ (mE n : ℝ)) := by
    filter_upwards [hV, hE] with n hnV hnE
    simp [hnV, hnE]
  have h_equiv :
      Asymptotics.IsEquivalent Filter.atTop
        (fun n ↦ (mV n : ℝ))
        (fun n ↦ (mE n : ℝ)) := by
    -- Eventual equality is stronger than the asymptotic equivalence required
    -- by `ParameterChoice.IsAsymptoticallyOptimal`.
    exact
      Asymptotics.IsEquivalent.trans_eventuallyEq
        (Asymptotics.IsEquivalent.refl :
          Asymptotics.IsEquivalent Filter.atTop
            (fun n ↦ (mV n : ℝ))
            (fun n ↦ (mV n : ℝ)))
        hVEq
  exact h_equiv

/-- Helper for Theorem 7.30: the explicit TSVD benchmark profile tends to
`+∞`, so the floor-defined benchmark index does as well. -/
lemma optimalIndexProfile_tendstoAtTop_local
    (b c p q σ : ℝ)
    (h_b : 0 < b)
    (h_c : 0 < c)
    (h_p : 1 < p)
    (h_q : 1 < q)
    (h_σ : 0 < σ) :
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
  have h_ratio_eventually_pos :
      ∀ᶠ n : ℕ in Filter.atTop, (σ ^ 2) / (n : ℝ) ∈ Set.Ioi 0 := by
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
  -- Separate the fixed positive prefactor from the diverging power-law term.
  convert (Filter.Tendsto.const_mul_atTop h_prefactor_pos h_power_tendsto_atTop) using 1
  ext n
  rw [optimalIndexProfile_def]

/-- Helper for Theorem 7.30: the floor-defined TSVD benchmark index tends to
`+∞` because it is asymptotically equivalent to the explicit benchmark
profile. -/
lemma optimalIndex_tendstoAtTop_local
    (b c p q σ : ℝ)
    (h_b : 0 < b)
    (h_c : 0 < c)
    (h_p : 1 < p)
    (h_q : 1 < q)
    (h_σ : 0 < σ) :
    Filter.Tendsto
      (fun n ↦ (optimalIndex b c p q σ n : ℝ))
      Filter.atTop
      Filter.atTop := by
  -- Transport `atTop` growth from the explicit profile to the floor-defined
  -- benchmark index through their asymptotic equivalence.
  exact
    (optimalIndexCast_isEquivalent_profile b c p q σ h_b h_c h_p h_q h_σ).tendsto_atTop_iff.2
      (optimalIndexProfile_tendstoAtTop_local b c p q σ h_b h_c h_p h_q h_σ)

/-- Helper for Theorem 7.30: the benchmark index is eventually positive, so
its reciprocal is a valid small error term in the one-step squeeze argument. -/
lemma optimalIndex_eventually_pos
    (b c p q σ : ℝ)
    (h_b : 0 < b)
    (h_c : 0 < c)
    (h_p : 1 < p)
    (h_q : 1 < q)
    (h_σ : 0 < σ) :
    ∀ᶠ n in Filter.atTop, 0 < (optimalIndex b c p q σ n : ℝ) := by
  -- Growth to `+∞` eventually places the benchmark index beyond `0`.
  exact
    (optimalIndex_tendstoAtTop_local b c p q σ h_b h_c h_p h_q h_σ).eventually
      (Filter.Ioi_mem_atTop 0)

/-- Helper for Theorem 7.30: the reciprocal benchmark scale tends to `0`
because `optimalIndex b c p q σ n → +∞`. -/
lemma optimalIndexInv_tendsto_zero
    (b c p q σ : ℝ)
    (h_b : 0 < b)
    (h_c : 0 < c)
    (h_p : 1 < p)
    (h_q : 1 < q)
    (h_σ : 0 < σ) :
    Filter.Tendsto
      (fun n ↦ ((optimalIndex b c p q σ n : ℝ))⁻¹)
      Filter.atTop
      (nhds 0) := by
  -- The reciprocal of an `atTop` real sequence vanishes.
  exact
    tendsto_inv_atTop_zero.comp
      (optimalIndex_tendstoAtTop_local b c p q σ h_b h_c h_p h_q h_σ)

/-- Helper for Theorem 7.30: the explicit benchmark profile is sublinear
relative to the data size because its power exponent `1 / (p + q)` is strictly
below `1`. -/
lemma optimalIndexProfile_div_dataSize_tendsto_zero
    (b c p q σ : ℝ)
    (h_b : 0 < b)
    (h_c : 0 < c)
    (h_p : 1 < p)
    (h_q : 1 < q)
    (h_σ : 0 < σ) :
    Filter.Tendsto
      (fun n ↦ optimalIndexProfile b c p q σ n / (n : ℝ))
      Filter.atTop
      (nhds 0) := by
  let a : ℝ := 1 / (p + q)
  have hpq_gt_one : 1 < p + q := by
    linarith
  have ha_lt_one : a < 1 := by
    dsimp [a]
    have hpq_pos : 0 < p + q := by linarith
    have hlt : 1 / (p + q) < (1 : ℝ) := by
      exact
        (one_div_lt hpq_pos (by norm_num : (0 : ℝ) < 1)).2
          (by simpa using hpq_gt_one)
    simpa using hlt
  have h_decay_pos : 0 < 1 - a := by
    linarith
  have h_rewrite :
      (fun n ↦ optimalIndexProfile b c p q σ n / (n : ℝ)) =ᶠ[Filter.atTop]
        (fun n ↦
          ((b * c) ^ a) * (σ ^ 2) ^ (-a) * ((n : ℝ) ^ (a - 1))) := by
    filter_upwards [Filter.Ici_mem_atTop 1] with n hn
    have hn_pos : 0 < (n : ℝ) := by
      exact_mod_cast hn
    have hσsq_pos : 0 < σ ^ 2 := by positivity
    have h_ratio :
        ((σ ^ 2) / (n : ℝ)) ^ (-a) =
          (σ ^ 2) ^ (-a) * (n : ℝ) ^ a := by
      calc
        ((σ ^ 2) / (n : ℝ)) ^ (-a)
            = ((((σ ^ 2) / (n : ℝ))⁻¹) ^ a) := by
                rw [Real.rpow_neg_eq_inv_rpow]
        _ = (((n : ℝ) / (σ ^ 2)) ^ a) := by
              congr 2
              field_simp [hn_pos.ne', hσsq_pos.ne']
        _ = (n : ℝ) ^ a / (σ ^ 2) ^ a := by
              rw [Real.div_rpow hn_pos.le (show 0 ≤ σ ^ 2 by positivity)]
        _ = (σ ^ 2) ^ (-a) * (n : ℝ) ^ a := by
              rw [div_eq_mul_inv, Real.rpow_neg (show 0 ≤ σ ^ 2 by positivity), mul_comm]
    have hn_sub : (n : ℝ) ^ (a - 1) = (n : ℝ) ^ a / (n : ℝ) := by
      rw [Real.rpow_sub hn_pos a 1, Real.rpow_one]
    calc
      optimalIndexProfile b c p q σ n / (n : ℝ)
          = ((b * c) ^ a) * (((σ ^ 2) / (n : ℝ)) ^ (-a)) / (n : ℝ) := by
              rw [optimalIndexProfile_def]
      _ = ((b * c) ^ a) * ((σ ^ 2) ^ (-a) * (n : ℝ) ^ a) / (n : ℝ) := by
            rw [h_ratio]
      _ = ((b * c) ^ a) * (σ ^ 2) ^ (-a) * ((n : ℝ) ^ a / (n : ℝ)) := by
            ring_nf
      _ = ((b * c) ^ a) * (σ ^ 2) ^ (-a) * ((n : ℝ) ^ (a - 1)) := by
            rw [hn_sub]
  refine Filter.Tendsto.congr' h_rewrite.symm ?_
  have h_power :
      Filter.Tendsto
        (fun n : ℕ ↦ ((n : ℝ) ^ (a - 1)))
        Filter.atTop
        (nhds 0) := by
    convert ((tendsto_rpow_neg_atTop h_decay_pos).comp tendsto_natCast_atTop_atTop) using 1
    ext n
    have hexp : a - 1 = -(1 - a) := by ring
    rw [hexp]
    simp
  have h_const :
      Filter.Tendsto
        (fun _ : ℕ ↦ ((b * c) ^ a) * (σ ^ 2) ^ (-a))
        Filter.atTop
        (nhds (((b * c) ^ a) * (σ ^ 2) ^ (-a))) :=
    tendsto_const_nhds
  simpa [mul_assoc] using h_const.mul h_power

/-- Helper for Theorem 7.30: the floor-defined benchmark index eventually lies
strictly below half the data size, so the benchmark GCV denominator stays away
from `0`. -/
lemma optimalIndex_eventually_lt_halfDataSize
    (b c p q σ : ℝ)
    (h_b : 0 < b)
    (h_c : 0 < c)
    (h_p : 1 < p)
    (h_q : 1 < q)
    (h_σ : 0 < σ) :
    ∀ᶠ n in Filter.atTop, 2 * optimalIndex b c p q σ n < n := by
  have h_profile_small_dist :
      ∀ᶠ n in Filter.atTop,
        dist (optimalIndexProfile b c p q σ n / (n : ℝ)) 0 < (1 / 2 : ℝ) :=
    (Metric.tendsto_nhds.1
      (optimalIndexProfile_div_dataSize_tendsto_zero b c p q σ h_b h_c h_p h_q h_σ))
      (1 / 2) (by norm_num)
  filter_upwards [h_profile_small_dist, Filter.Ici_mem_atTop 1] with n hn_profile hn_pos
  have hn_real_pos : 0 < (n : ℝ) := by
    exact_mod_cast hn_pos
  have hprofile_nonneg : 0 ≤ optimalIndexProfile b c p q σ n := by
    rw [optimalIndexProfile_def]
    positivity
  have hratio_nonneg : 0 ≤ optimalIndexProfile b c p q σ n / (n : ℝ) := by
    positivity
  have h_profile_small :
      optimalIndexProfile b c p q σ n / (n : ℝ) < (1 / 2 : ℝ) := by
    simpa [Real.dist_eq, hprofile_nonneg, hn_real_pos.le, abs_of_nonneg, div_eq_mul_inv] using hn_profile
  have hprofile_lt_half :
      optimalIndexProfile b c p q σ n < (n : ℝ) / 2 := by
    have hmul := (div_lt_iff₀ hn_real_pos).mp h_profile_small
    simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hfloor_le :
      (optimalIndex b c p q σ n : ℝ) ≤ optimalIndexProfile b c p q σ n := by
    rw [optimalIndex_def]
    exact Nat.floor_le hprofile_nonneg
  have hcast :
      ((2 * optimalIndex b c p q σ n : ℕ) : ℝ) < (n : ℝ) := by
    have hbeta_half : (optimalIndex b c p q σ n : ℝ) < (n : ℝ) / 2 :=
      lt_of_le_of_lt hfloor_le hprofile_lt_half
    have htwice : 2 * (optimalIndex b c p q σ n : ℝ) < (n : ℝ) := by
      nlinarith
    simpa using htwice
  exact_mod_cast hcast

/-- Helper for Theorem 7.30: on positive data sizes, the explicit benchmark
profile satisfies the scalar root identity that turns the signal-decay term
into the noise scale. -/
lemma optimalIndexProfile_root_eq
    (b c p q σ : ℝ)
    (n : ℕ)
    (h_b : 0 < b)
    (h_c : 0 < c)
    (h_p : 1 < p)
    (h_q : 1 < q)
    (h_σ : 0 < σ)
    (hn : 0 < n) :
    b * c * (optimalIndexProfile b c p q σ n) ^ (-(p + q)) = (σ ^ 2) / (n : ℝ) := by
  have hbc_pos : 0 < b * c := mul_pos h_b h_c
  have hpq_ne : p + q ≠ 0 := by
    linarith
  have hratio_pos : 0 < (σ ^ 2) / (n : ℝ) := by
    positivity
  have hexp_left : (1 / (p + q)) * (-(p + q)) = (-1 : ℝ) := by
    field_simp [hpq_ne]
  have hexp_right : (-(1 / (p + q))) * (-(p + q)) = (1 : ℝ) := by
    field_simp [hpq_ne]
  have hleft :
      ((b * c) ^ (1 / (p + q))) ^ (-(p + q)) = (b * c : ℝ)⁻¹ := by
    rw [← Real.rpow_mul (show 0 ≤ b * c by positivity)]
    rw [hexp_left, Real.rpow_neg_one]
  have hright :
      (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q)))) ^ (-(p + q)) = (σ ^ 2) / (n : ℝ) := by
    rw [← Real.rpow_mul (show 0 ≤ (σ ^ 2) / (n : ℝ) by positivity)]
    rw [hexp_right, Real.rpow_one]
  have hcancel : b * c * ((b * c : ℝ)⁻¹) = 1 := by
    field_simp [h_b.ne', h_c.ne']
  -- Rewrite the profile once, then collapse the reciprocal benchmark factor
  -- against the scalar prefactor `b * c`.
  calc
    b * c * (optimalIndexProfile b c p q σ n) ^ (-(p + q))
        =
      b * c *
        ((((b * c) ^ (1 / (p + q))) *
            (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q))))) ^ (-(p + q))) := by
              rw [optimalIndexProfile_def]
    _ =
      b * c *
        ((((b * c) ^ (1 / (p + q))) ^ (-(p + q))) *
          ((((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q)))) ^ (-(p + q)))) := by
            rw [Real.mul_rpow (show 0 ≤ (b * c) ^ (1 / (p + q)) by positivity)
              (show 0 ≤ ((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q))) by positivity)]
    _ = b * c * (((b * c : ℝ)⁻¹) * ((σ ^ 2) / (n : ℝ))) := by
          rw [hleft, hright]
    _ = (b * c * ((b * c : ℝ)⁻¹)) * ((σ ^ 2) / (n : ℝ)) := by
          ring_nf
    _ = (σ ^ 2) / (n : ℝ) := by
          rw [hcancel]
          ring

/-- Helper for Theorem 7.30: if a nat-valued family stays within one benchmark
step of `optimalIndex b c p q σ`, then its real coercion is asymptotically
equivalent to that benchmark. -/
lemma withinOneStep_optimalIndex_isEquivalent
    (b c p q σ : ℝ)
    (mV : ℕ → ℕ)
    (h_within :
      ∀ᶠ n in Filter.atTop,
        optimalIndex b c p q σ n - 1 ≤ mV n ∧ mV n ≤ optimalIndex b c p q σ n)
    (h_beta_pos :
      ∀ᶠ n in Filter.atTop, 0 < (optimalIndex b c p q σ n : ℝ))
    (h_beta_inv :
      Filter.Tendsto
        (fun n ↦ ((optimalIndex b c p q σ n : ℝ))⁻¹)
        Filter.atTop
        (nhds 0)) :
    Asymptotics.IsEquivalent Filter.atTop
      (fun n ↦ (mV n : ℝ))
      (fun n ↦ (optimalIndex b c p q σ n : ℝ)) := by
  have h_beta_ne :
      ∀ᶠ n in Filter.atTop, (optimalIndex b c p q σ n : ℝ) ≠ 0 :=
    h_beta_pos.mono fun _ hn ↦ ne_of_gt hn
  rw [Asymptotics.isEquivalent_iff_tendsto_one h_beta_ne]
  -- Control the normalized distance to `1` by the reciprocal benchmark error
  -- term coming from the one-step neighborhood.
  refine Metric.tendsto_nhds.2 ?_
  intro ε h_ε
  have h_inv_small :
      ∀ᶠ n in Filter.atTop,
        dist (((optimalIndex b c p q σ n : ℝ))⁻¹) 0 < ε :=
    Metric.tendsto_nhds.1 h_beta_inv ε h_ε
  filter_upwards [h_within, h_beta_pos, h_inv_small] with n hn_within hn_beta_pos hn_inv_small
  let β : ℝ := (optimalIndex b c p q σ n : ℝ)
  let α : ℝ := (mV n : ℝ)
  have hβ_nat_pos : 0 < optimalIndex b c p q σ n := Nat.cast_pos.mp hn_beta_pos
  have hβ_one_le : 1 ≤ optimalIndex b c p q σ n := Nat.succ_le_of_lt hβ_nat_pos
  have hβ_ne : β ≠ 0 := ne_of_gt hn_beta_pos
  have hα_upper : α ≤ β := by
    dsimp [α, β]
    exact_mod_cast hn_within.2
  have hα_lower : β - 1 ≤ α := by
    have hcast : ((optimalIndex b c p q σ n - 1 : ℕ) : ℝ) ≤ α := by
      dsimp [α]
      exact_mod_cast hn_within.1
    simpa [α, β, Nat.cast_sub hβ_one_le] using hcast
  have hratio_le_one : α / β ≤ 1 := by
    have hdiv :
        α / β ≤ β / β :=
      div_le_div_of_nonneg_right hα_upper hn_beta_pos.le
    simpa [β, hn_beta_pos.ne'] using hdiv
  have hratio_ge : 1 - β⁻¹ ≤ α / β := by
    have hdiv :
        (β - 1) / β ≤ α / β :=
      div_le_div_of_nonneg_right hα_lower hn_beta_pos.le
    have hrewrite : (β - 1) / β = 1 - β⁻¹ := by
      calc
        (β - 1) / β = β / β - 1 / β := by ring
        _ = 1 - β⁻¹ := by simp [hβ_ne]
    simpa [hrewrite] using hdiv
  have hdist_nonneg : 0 ≤ 1 - α / β := by
    linarith
  have hdist_le : dist (α / β) 1 ≤ β⁻¹ := by
    have hmain : 1 - α / β ≤ β⁻¹ := by
      linarith
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg hdist_nonneg]
    exact hmain
  have hβ_inv_lt : β⁻¹ < ε := by
    simpa [Real.dist_eq, abs_of_nonneg (inv_nonneg.mpr hn_beta_pos.le), β] using hn_inv_small
  exact lt_of_le_of_lt hdist_le hβ_inv_lt

variable [CompleteSpace H] [CompleteSpace F]

/-- Helper for Theorem 7.30: the TSVD GCV numerator is the expected normalized
squared residual before dividing by the trace-gap factor. -/
noncomputable def expectedResidualObjective
    (μ : MeasureTheory.Measure Ω)
    (K : ℕ → H →L[ℝ] F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (fTrue : H)
    (η : ℕ → Ω → F) :
    ℕ → ℕ → ℝ :=
  fun n m ↦
    ∫ ω, ‖K n (Rtsvd n m (K n fTrue + η n ω)) - (K n fTrue + η n ω)‖ ^ 2 / (n : ℝ) ∂μ

/-- Helper for Theorem 7.30: rewrite the TSVD expected GCV objective into its
residual numerator divided by the trace-gap square. -/
lemma expectedObjective_eq_expectedResidualObjective_div_traceGapSq
    (μ : MeasureTheory.Measure Ω)
    (K : ℕ → H →L[ℝ] F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (fTrue : H)
    (η : ℕ → Ω → F)
    (n m : ℕ) :
    TsvdGcv.expectedObjective μ K Rtsvd fTrue η n m =
      expectedResidualObjective μ K Rtsvd fTrue η n m /
        (1 - (m : ℝ) / (n : ℝ)) ^ 2 := by
  -- Unfold the owned numerator once so later GCV proofs can stay in a stable
  -- numerator-over-denominator spelling world.
  rfl

/-- Helper for Theorem 7.30: on the denominator-valid region `m < n`, the
expected TSVD GCV objective is exactly the residual numerator divided by the
square of the integer gap `n - m`. -/
lemma gcvExpectedObjective_eq_gapResidualQuotient
    (μ : MeasureTheory.Measure Ω)
    (K : ℕ → H →L[ℝ] F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (fTrue : H)
    (η : ℕ → Ω → F)
    {n m : ℕ}
    (hm_lt : m < n) :
    TsvdGcv.expectedObjective μ K Rtsvd fTrue η n m =
      (((n : ℝ) ^ 2) * expectedResidualObjective μ K Rtsvd fTrue η n m) /
        (((n - m : ℕ) : ℝ) ^ 2) := by
  have hm_le : m ≤ n := Nat.le_of_lt hm_lt
  have hn_pos_nat : 0 < n := lt_of_le_of_lt (Nat.zero_le m) hm_lt
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast hn_pos_nat
  have hgap_pos_nat : 0 < n - m := Nat.sub_pos_of_lt hm_lt
  have hgap_pos : 0 < (((n - m : ℕ) : ℝ)) := by
    exact_mod_cast hgap_pos_nat
  have hgap :
      1 - (m : ℝ) / (n : ℝ) = (((n - m : ℕ) : ℝ) / (n : ℝ)) := by
    have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
    rw [Nat.cast_sub hm_le]
    field_simp [hn_ne]
  -- Route correction: normalize the trace-gap denominator once to the nat gap
  -- `n - m`, and keep the GCV objective in that single quotient spelling.
  calc
    TsvdGcv.expectedObjective μ K Rtsvd fTrue η n m
        = expectedResidualObjective μ K Rtsvd fTrue η n m /
            (1 - (m : ℝ) / (n : ℝ)) ^ 2 := by
              rw [expectedObjective_eq_expectedResidualObjective_div_traceGapSq]
    _ = expectedResidualObjective μ K Rtsvd fTrue η n m /
          ((((n - m : ℕ) : ℝ) / (n : ℝ)) ^ 2) := by
            rw [hgap]
    _ = (((n : ℝ) ^ 2) * expectedResidualObjective μ K Rtsvd fTrue η n m) /
          (((n - m : ℕ) : ℝ) ^ 2) := by
            field_simp [hn_pos.ne', hgap_pos.ne']

/-- Helper for Theorem 7.30: the TSVD truncation step at level `m` adds exactly
the new singular mode, without importing Proposition 7.15's minimizer-local
context. -/
lemma tsvdReconstructionStep_apply_local
    (K : ℕ → H →L[ℝ] F)
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
    (h_length : ∀ n, (S n).length = ⊤)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (h_tsvd : IsTsvdReconstructionFamily K S h_length Rtsvd)
    (n : ℕ)
    {m : ℕ}
    (hm : 0 < m)
    (g : F) :
    Rtsvd n m g =
      Rtsvd n (m - 1) g +
        (((1 / (S n).singularValue ((S n).natIndex (h_length n) (m - 1))) *
            inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) (m - 1)) : F) g) •
          ((S n).rightBasis ((S n).natIndex (h_length n) (m - 1)) : H)) := by
  -- Expand the `m`-mode truncation as the predecessor block plus its final
  -- singular summand.
  rw [h_tsvd n m g, ← Nat.succ_pred_eq_of_pos hm, Finset.sum_range_succ]
  simpa using (h_tsvd n (m - 1) g).symm

/-- Helper for Theorem 7.30: omitted singular modes have zero left-basis
coefficient after applying `K n` to the `m`-term TSVD reconstruction. -/
lemma inner_omittedMode_forwardReconstruction_eq_zero
    (K : ℕ → H →L[ℝ] F)
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
    (h_length : ∀ n, (S n).length = ⊤)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (h_tsvd : IsTsvdReconstructionFamily K S h_length Rtsvd)
    (n : ℕ)
    (g : F)
    {m i : ℕ}
    (hi : m ≤ i) :
    inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) i) : F)
      (K n (Rtsvd n m g)) = 0 := by
  -- Rewrite the finite TSVD reconstruction and kill each earlier mode by
  -- left-basis orthogonality against the omitted index `i`.
  rw [h_tsvd n m g, map_sum, inner_sum]
  apply Finset.sum_eq_zero
  intro k hk
  have hk_lt : k < m := Finset.mem_range.mp hk
  have hki_lt : k < i := lt_of_lt_of_le hk_lt hi
  have hidx_ne :
      (S n).natIndex (h_length n) i ≠ (S n).natIndex (h_length n) k := by
    exact ne_of_gt ((S n).natIndex_strictMono (h_length n) hki_lt)
  rw [ContinuousLinearMap.map_smul, (S n).map_right ((S n).natIndex (h_length n) k),
    smul_smul, inner_smul_right]
  have horth :
      inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) i) : F)
        ((S n).leftBasis ((S n).natIndex (h_length n) k) : F) = 0 := by
    simpa using (S n).leftBasis.orthonormal.2 hidx_ne
  rw [horth]
  simp

/-- Helper for Theorem 7.30: applying `K n` to the new TSVD step recovers the
corresponding left-basis data coefficient exactly. -/
lemma stepMode_forwardImage_eq
    (K : ℕ → H →L[ℝ] F)
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
    (h_length : ∀ n, (S n).length = ⊤)
    (n : ℕ)
    {m : ℕ}
    (hm : 0 < m)
    (g : F) :
    (K n)
      ((((1 / (S n).singularValue ((S n).natIndex (h_length n) (m - 1))) *
            inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) (m - 1)) : F) g) •
          ((S n).rightBasis ((S n).natIndex (h_length n) (m - 1)) : H))) =
      (inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) (m - 1)) : F) g) •
        ((S n).leftBasis ((S n).natIndex (h_length n) (m - 1)) : F) := by
  let j : (S n).Index := (S n).natIndex (h_length n) (m - 1)
  have hs_ne : (S n).singularValue j ≠ 0 := ne_of_gt ((S n).singularValue_pos j)
  have hscalar :
      ((1 / (S n).singularValue j) * inner ℝ ((S n).leftBasis j : F) g) *
          (S n).singularValue j =
        inner ℝ ((S n).leftBasis j : F) g := by
    field_simp [hs_ne]
  -- Collapse the singular-value denominator against `K n` applied to the new
  -- right-basis mode.
  rw [ContinuousLinearMap.map_smul, (S n).map_right j, smul_smul]
  simpa [j] using congrArg (fun t : ℝ ↦ t • ((S n).leftBasis j : F)) hscalar

/-- Helper for Theorem 7.30: after adding the `m`th TSVD mode, the current
residual has zero coefficient in that left singular direction. -/
lemma currentResidual_stepModeCoeff_eq_zero
    (K : ℕ → H →L[ℝ] F)
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
    (h_length : ∀ n, (S n).length = ⊤)
    (fTrue : H)
    (η : ℕ → Ω → F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (h_tsvd : IsTsvdReconstructionFamily K S h_length Rtsvd)
    (n : ℕ)
    {m : ℕ}
    (hm : 0 < m)
    (ω : Ω) :
    inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) (m - 1)) : F)
      (K n (Rtsvd n m (K n fTrue + η n ω)) - (K n fTrue + η n ω)) = 0 := by
  let j : (S n).Index := (S n).natIndex (h_length n) (m - 1)
  let v : F := ((S n).leftBasis j : F)
  let g : F := K n fTrue + η n ω
  have hprev_zero :
      inner ℝ v (K n (Rtsvd n (m - 1) g)) = 0 := by
    simpa [v, j] using
      inner_omittedMode_forwardReconstruction_eq_zero
        (K := K) (S := S) (h_length := h_length) (Rtsvd := Rtsvd)
        (h_tsvd := h_tsvd) (n := n) (g := g) (m := m - 1) (i := m - 1)
        (Nat.le_refl _)
  have himage :
      K n (Rtsvd n m g) =
        K n (Rtsvd n (m - 1) g) + (inner ℝ v g) • v := by
    -- Rewrite the new TSVD step before subtracting the datum.
    rw [tsvdReconstructionStep_apply_local
      (K := K) (S := S) (h_length := h_length) (Rtsvd := Rtsvd)
      (h_tsvd := h_tsvd) (n := n) hm g]
    rw [ContinuousLinearMap.map_add, stepMode_forwardImage_eq
      (K := K) (S := S) (h_length := h_length) (n := n) hm g]
  have hv_norm : ‖v‖ = 1 := by
    simpa [v] using (S n).leftBasis.orthonormal.norm_eq_one j
  have hvv : inner ℝ v v = 1 := by
    rw [real_inner_self_eq_norm_sq, hv_norm]
    norm_num
  -- The predecessor contributes nothing in the new mode, and the step image
  -- exactly cancels the matching data coefficient.
  calc
    inner ℝ v (K n (Rtsvd n m g) - g)
        = inner ℝ v (K n (Rtsvd n (m - 1) g)) + inner ℝ v ((inner ℝ v g) • v) -
            inner ℝ v g := by
              rw [himage, inner_sub_right, inner_add_right]
    _ = 0 := by
          rw [hprev_zero, inner_smul_right, hvv]
          ring

/-- Helper for Theorem 7.30: the predecessor residual carries the negative data
coefficient in the newly added left singular mode. -/
lemma previousResidual_stepModeCoeff_eq_negData
    (K : ℕ → H →L[ℝ] F)
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
    (h_length : ∀ n, (S n).length = ⊤)
    (fTrue : H)
    (η : ℕ → Ω → F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (h_tsvd : IsTsvdReconstructionFamily K S h_length Rtsvd)
    (n : ℕ)
    {m : ℕ}
    (hm : 0 < m)
    (ω : Ω) :
    inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) (m - 1)) : F)
      (K n (Rtsvd n (m - 1) (K n fTrue + η n ω)) - (K n fTrue + η n ω)) =
        -inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) (m - 1)) : F)
          (K n fTrue + η n ω) := by
  let j : (S n).Index := (S n).natIndex (h_length n) (m - 1)
  let v : F := ((S n).leftBasis j : F)
  let g : F := K n fTrue + η n ω
  have hprev_zero :
      inner ℝ v (K n (Rtsvd n (m - 1) g)) = 0 := by
    simpa [v, j] using
      inner_omittedMode_forwardReconstruction_eq_zero
        (K := K) (S := S) (h_length := h_length) (Rtsvd := Rtsvd)
        (h_tsvd := h_tsvd) (n := n) (g := g) (m := m - 1) (i := m - 1)
        (Nat.le_refl _)
  -- The predecessor reconstruction has no component in the newly added mode.
  rw [inner_sub_right, hprev_zero, zero_sub]

/-- Helper for Theorem 7.30: pointwise, adding the `m`th TSVD mode removes
exactly the square of the current data coefficient in that left singular
direction from the residual objective numerator. -/
lemma backwardResidualStep_pointwise
    (K : ℕ → H →L[ℝ] F)
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
    (h_length : ∀ n, (S n).length = ⊤)
    (fTrue : H)
    (η : ℕ → Ω → F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (h_tsvd : IsTsvdReconstructionFamily K S h_length Rtsvd)
    (n : ℕ)
    {m : ℕ}
    (hm : 0 < m)
    (ω : Ω) :
    ‖K n (Rtsvd n m (K n fTrue + η n ω)) - (K n fTrue + η n ω)‖ ^ 2 -
        ‖K n (Rtsvd n (m - 1) (K n fTrue + η n ω)) - (K n fTrue + η n ω)‖ ^ 2 =
      -(inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) (m - 1)) : F)
          (K n fTrue + η n ω)) ^ 2 := by
  let j : (S n).Index := (S n).natIndex (h_length n) (m - 1)
  let v : F := ((S n).leftBasis j : F)
  let g : F := K n fTrue + η n ω
  let r : F := K n (Rtsvd n m g) - g
  let coeff : ℝ := inner ℝ v g
  have hv_norm : ‖v‖ = 1 := by
    simpa [v] using (S n).leftBasis.orthonormal.norm_eq_one j
  have horth : inner ℝ v r = 0 := by
    simpa [r, v, g, coeff, j] using
      currentResidual_stepModeCoeff_eq_zero
        (K := K) (S := S) (h_length := h_length) (fTrue := fTrue) (η := η)
        (Rtsvd := Rtsvd) (h_tsvd := h_tsvd) (n := n) hm ω
  have hprev :
      K n (Rtsvd n (m - 1) g) - g = r + (-coeff) • v := by
    -- Rewrite the predecessor residual through the current residual plus the
    -- missing mode coefficient.
    dsimp [r, coeff, g]
    have himage :
        K n (Rtsvd n m (K n fTrue + η n ω)) =
          K n (Rtsvd n (m - 1) (K n fTrue + η n ω)) +
            (inner ℝ v (K n fTrue + η n ω)) • v := by
      rw [tsvdReconstructionStep_apply_local
        (K := K) (S := S) (h_length := h_length) (Rtsvd := Rtsvd)
        (h_tsvd := h_tsvd) (n := n) hm (K n fTrue + η n ω)]
      rw [ContinuousLinearMap.map_add, stepMode_forwardImage_eq
        (K := K) (S := S) (h_length := h_length) (n := n) hm (K n fTrue + η n ω)]
    rw [himage]
    simp [r, coeff, g, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hprev_norm :
      ‖r + (-coeff) • v‖ ^ 2 = ‖r‖ ^ 2 + coeff ^ 2 := by
    have horth' : inner ℝ r ((-coeff) • v) = 0 := by
      rw [inner_smul_right, real_inner_comm, horth]
      simp
    calc
      ‖r + (-coeff) • v‖ ^ 2 = ‖r‖ ^ 2 + ‖(-coeff) • v‖ ^ 2 := by
        simpa [pow_two] using
          norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero r ((-coeff) • v) horth'
      _ = ‖r‖ ^ 2 + (-coeff) ^ 2 := by
            rw [norm_smul, hv_norm]
            simp [pow_two, Real.norm_eq_abs]
      _ = ‖r‖ ^ 2 + coeff ^ 2 := by ring
  have hcurr :
      K n (Rtsvd n m (K n fTrue + η n ω)) - (K n fTrue + η n ω) = r := by
    rfl
  -- Normalize both residuals against the orthogonal current remainder.
  calc
    ‖K n (Rtsvd n m (K n fTrue + η n ω)) - (K n fTrue + η n ω)‖ ^ 2 -
        ‖K n (Rtsvd n (m - 1) (K n fTrue + η n ω)) - (K n fTrue + η n ω)‖ ^ 2
        = ‖r‖ ^ 2 - ‖r + (-coeff) • v‖ ^ 2 := by
            rw [hcurr, hprev]
    _ = ‖r‖ ^ 2 - (‖r‖ ^ 2 + coeff ^ 2) := by rw [hprev_norm]
    _ = -(coeff ^ 2) := by ring
    _ = -(inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) (m - 1)) : F)
            (K n fTrue + η n ω)) ^ 2 := by
          simp [coeff, v, j, g]

/-- Helper for Theorem 7.30: the expected residual objective is always
nonnegative because it integrates a nonnegative normalized squared residual. -/
lemma expectedResidualObjective_nonneg
    (μ : MeasureTheory.Measure Ω)
    (K : ℕ → H →L[ℝ] F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (fTrue : H)
    (η : ℕ → Ω → F)
    (n m : ℕ) :
    0 ≤ expectedResidualObjective μ K Rtsvd fTrue η n m := by
  -- Unfold the owned numerator and use pointwise nonnegativity of the squared
  -- residual integrand.
  unfold expectedResidualObjective
  exact MeasureTheory.integral_nonneg fun _ ↦ by positivity

/-- Helper for Theorem 7.30: integrating the pointwise backward residual-step
identity gives the exact one-mode decrement in the expected GCV numerator. -/
lemma expectedResidualObjective_backwardStep_eq
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (K : ℕ → H →L[ℝ] F)
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
    (h_length : ∀ n, (S n).length = ⊤)
    (fTrue : H)
    (b c p q σ : ℝ)
    (η : ℕ → Ω → F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (n m : ℕ)
    (h_b : 0 < b)
    (h_c : 0 < c)
    (h_p : 1 < p)
    (h_q : 1 < q)
    (h_σ : 0 < σ)
    (h_noise_memLp : ∀ n, MeasureTheory.MemLp (η n) 2 μ)
    (h_noise_meanZero : ∀ n, ∫ ω, η n ω ∂μ = 0)
    (h_noise_modeVariance :
      ∀ n i,
        ∫ ω,
          (inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) i) : F) (η n ω)) ^ 2 ∂μ =
            σ ^ 2 / (n : ℝ))
    (h_singularDecay :
      ∀ n, (S n).HasAlgebraicSingularValueSquareDecay (h_length n) c p)
    (h_fourierDecay :
      ∀ n, (S n).HasAlgebraicFourierCoefficientSquareDecay (h_length n) fTrue b q)
    (h_tsvd : IsTsvdReconstructionFamily K S h_length Rtsvd)
    (hm : 0 < m) :
    expectedResidualObjective μ K Rtsvd fTrue η n m -
        expectedResidualObjective μ K Rtsvd fTrue η n (m - 1) =
      -(b * c * (m : ℝ) ^ (-(p + q)) / (n : ℝ) + (σ ^ 2) / (n : ℝ) ^ 2) := by
  let j : (S n).Index := (S n).natIndex (h_length n) (m - 1)
  let u : H := ((S n).rightBasis j : H)
  let v : F := ((S n).leftBasis j : F)
  let s : ℝ := (S n).singularValue j
  let a : ℝ := inner ℝ v ((K n) fTrue)
  have h_two_le : (1 : ENNReal) ≤ (2 : ENNReal) := by
    norm_num
  have hResidualMemLp (k : ℕ) :
      MeasureTheory.MemLp
        (fun ω ↦ K n (Rtsvd n k (K n fTrue + η n ω)) - (K n fTrue + η n ω))
        2 μ := by
    let A : F →L[ℝ] F := (K n).comp (Rtsvd n k) - ContinuousLinearMap.id ℝ F
    have hNoiseImage : MeasureTheory.MemLp (fun ω ↦ A (η n ω)) 2 μ := by
      simpa [A] using (h_noise_memLp n).continuousLinearMap_comp A
    have hConst :
        MeasureTheory.MemLp
          (fun _ : Ω ↦ K n (Rtsvd n k (K n fTrue)) - K n fTrue)
          2 μ := by
      simpa using
        (MeasureTheory.memLp_const
          (α := Ω) (μ := μ) (p := (2 : ENNReal))
          (c := K n (Rtsvd n k (K n fTrue)) - K n fTrue))
    -- Split the residual into a fixed bias term and the linear image of the
    -- noise through `(K n) ∘ Rtsvd n k - 1`.
    convert hConst.add hNoiseImage using 1
    funext ω
    simp [A, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, map_add]
  have hCurrInt :
      MeasureTheory.Integrable
        (fun ω ↦ ‖K n (Rtsvd n m (K n fTrue + η n ω)) - (K n fTrue + η n ω)‖ ^ 2 / (n : ℝ)) μ := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (MeasureTheory.MemLp.integrable_norm_pow (p := 2) (hResidualMemLp m) (by decide)).const_mul
        ((n : ℝ)⁻¹)
  have hPrevInt :
      MeasureTheory.Integrable
        (fun ω ↦
          ‖K n (Rtsvd n (m - 1) (K n fTrue + η n ω)) - (K n fTrue + η n ω)‖ ^ 2 / (n : ℝ)) μ := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (MeasureTheory.MemLp.integrable_norm_pow (p := 2) (hResidualMemLp (m - 1)) (by decide)).const_mul
        ((n : ℝ)⁻¹)
  have hNoiseModeLp : MeasureTheory.MemLp (fun ω ↦ inner ℝ v (η n ω)) 2 μ := by
    simpa [v] using MeasureTheory.MemLp.const_inner v (h_noise_memLp n)
  have hNoiseModeInt :
      MeasureTheory.Integrable (fun ω ↦ inner ℝ v (η n ω)) μ :=
    hNoiseModeLp.integrable h_two_le
  have hNoiseModeSqInt :
      MeasureTheory.Integrable (fun ω ↦ (inner ℝ v (η n ω)) ^ 2) μ :=
    MeasureTheory.MemLp.integrable_sq hNoiseModeLp
  have hCoeffSquareInt :
      MeasureTheory.Integrable
        (fun ω ↦ (inner ℝ v (K n fTrue + η n ω)) ^ 2) μ := by
    have hConst : MeasureTheory.MemLp (fun _ : Ω ↦ a) 2 μ := by
      simpa using
        (MeasureTheory.memLp_const (α := Ω) (μ := μ) (p := (2 : ENNReal)) (c := a))
    have hCoeffLp :
        MeasureTheory.MemLp
          (fun ω ↦ a + inner ℝ v (η n ω))
          2 μ :=
      hConst.add hNoiseModeLp
    -- Normalize the coefficient through its constant-plus-noise spelling before
    -- applying the standard `L²` square-integrability rule.
    simpa [a, inner_add_right] using (MeasureTheory.MemLp.integrable_sq hCoeffLp)
  have hCoeffPointwise :
      (fun ω ↦
        ‖K n (Rtsvd n m (K n fTrue + η n ω)) - (K n fTrue + η n ω)‖ ^ 2 / (n : ℝ) -
          ‖K n (Rtsvd n (m - 1) (K n fTrue + η n ω)) - (K n fTrue + η n ω)‖ ^ 2 / (n : ℝ)) =
        fun ω ↦ (-(n : ℝ)⁻¹) * (inner ℝ v (K n fTrue + η n ω)) ^ 2 := by
    funext ω
    calc
      ‖K n (Rtsvd n m (K n fTrue + η n ω)) - (K n fTrue + η n ω)‖ ^ 2 / (n : ℝ) -
          ‖K n (Rtsvd n (m - 1) (K n fTrue + η n ω)) - (K n fTrue + η n ω)‖ ^ 2 / (n : ℝ)
          =
            (‖K n (Rtsvd n m (K n fTrue + η n ω)) - (K n fTrue + η n ω)‖ ^ 2 -
              ‖K n (Rtsvd n (m - 1) (K n fTrue + η n ω)) - (K n fTrue + η n ω)‖ ^ 2) / (n : ℝ) := by
                ring
      _ = (-(inner ℝ v (K n fTrue + η n ω)) ^ 2) / (n : ℝ) := by
            rw [backwardResidualStep_pointwise
              (K := K) (S := S) (h_length := h_length) (fTrue := fTrue) (η := η)
              (Rtsvd := Rtsvd) (h_tsvd := h_tsvd) (n := n) hm ω]
      _ = (-(n : ℝ)⁻¹) * (inner ℝ v (K n fTrue + η n ω)) ^ 2 := by
            ring
  have hNoiseCoeffZero :
      ∫ ω, inner ℝ v (η n ω) ∂μ = 0 := by
    have hEtaInt : MeasureTheory.Integrable (η n) μ :=
      (h_noise_memLp n).integrable h_two_le
    -- Push the fixed inner-product pairing through the integral and use the
    -- mean-zero white-noise hypothesis.
    rw [integral_inner hEtaInt, h_noise_meanZero n]
    simp
  have hCoeffDecomp :
      (fun ω ↦ (inner ℝ v (K n fTrue + η n ω)) ^ 2) =
        fun ω ↦ a ^ 2 + (2 * a) * inner ℝ v (η n ω) + (inner ℝ v (η n ω)) ^ 2 := by
    funext ω
    rw [inner_add_right]
    ring
  have hCoeffIntegral :
      ∫ ω, (inner ℝ v (K n fTrue + η n ω)) ^ 2 ∂μ =
        a ^ 2 + σ ^ 2 / (n : ℝ) := by
    have hConstInt : MeasureTheory.Integrable (fun _ : Ω ↦ a ^ 2) μ :=
      MeasureTheory.integrable_const _
    have hCrossInt :
        MeasureTheory.Integrable (fun ω ↦ (2 * a) * inner ℝ v (η n ω)) μ := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hNoiseModeInt.const_mul (2 * a)
    have hAssoc :
        (fun ω ↦ a ^ 2 + (2 * a) * inner ℝ v (η n ω) + (inner ℝ v (η n ω)) ^ 2) =
          fun ω ↦ a ^ 2 + ((2 * a) * inner ℝ v (η n ω) + (inner ℝ v (η n ω)) ^ 2) := by
      funext ω
      ring
    have hSplit :
        ∫ ω, a ^ 2 + ((2 * a) * inner ℝ v (η n ω) + (inner ℝ v (η n ω)) ^ 2) ∂μ =
          ∫ _ : Ω, a ^ 2 ∂μ + ∫ ω, (2 * a) * inner ℝ v (η n ω) + (inner ℝ v (η n ω)) ^ 2 ∂μ := by
      simpa using
        (MeasureTheory.integral_add
          (μ := μ)
          (f := fun _ : Ω ↦ a ^ 2)
          (g := fun ω ↦ (2 * a) * inner ℝ v (η n ω) + (inner ℝ v (η n ω)) ^ 2)
          hConstInt (hCrossInt.add hNoiseModeSqInt))
    have hCrossVarianceSplit :
        ∫ ω, (2 * a) * inner ℝ v (η n ω) + (inner ℝ v (η n ω)) ^ 2 ∂μ =
          ∫ ω, (2 * a) * inner ℝ v (η n ω) ∂μ +
            ∫ ω, (inner ℝ v (η n ω)) ^ 2 ∂μ := by
      simpa using
        (MeasureTheory.integral_add
          (μ := μ)
          (f := fun ω ↦ (2 * a) * inner ℝ v (η n ω))
          (g := fun ω ↦ (inner ℝ v (η n ω)) ^ 2)
          hCrossInt hNoiseModeSqInt)
    have hConstEval : ∫ _ : Ω, a ^ 2 ∂μ = a ^ 2 := by
      simp [MeasureTheory.integral_const]
    rw [hCoeffDecomp]
    rw [hAssoc]
    rw [hSplit, hCrossVarianceSplit, hConstEval]
    have hCrossZero :
        ∫ ω, (2 * a) * inner ℝ v (η n ω) ∂μ = 0 := by
      -- The cross term is a fixed scalar multiple of the mean-zero noise mode.
      rw [MeasureTheory.integral_const_mul, hNoiseCoeffZero]
      simp
    rw [hCrossZero, zero_add, h_noise_modeVariance n (m - 1)]
  have hcoeff :
      a = s * inner ℝ u fTrue := by
    -- Move `K n` across the inner product and use the singular-system
    -- eigenrelation on the chosen mode.
    dsimp [a, s, u, v]
    rw [← ContinuousLinearMap.adjoint_inner_left (K n) fTrue ((S n).leftBasis j : F),
      (S n).adjoint_map_left j, real_inner_smul_left]
    simp
  have haSq :
      a ^ 2 = b * c * (m : ℝ) ^ (-(p + q)) := by
    have hFourier :
        (inner ℝ u fTrue) ^ 2 = b * (m : ℝ) ^ (-q) := by
      simpa [u, j] using (h_fourierDecay n ⟨m, hm⟩)
    have hSingular :
        s ^ 2 = c * (m : ℝ) ^ (-p) := by
      simpa [s, j] using (h_singularDecay n ⟨m, hm⟩)
    have hm_real_pos : 0 < (m : ℝ) := by
      exact_mod_cast hm
    calc
      a ^ 2 = s ^ 2 * (inner ℝ u fTrue) ^ 2 := by rw [hcoeff]; ring
      _ = (c * (m : ℝ) ^ (-p)) * (b * (m : ℝ) ^ (-q)) := by rw [hSingular, hFourier]
      _ = b * c * ((m : ℝ) ^ (-p) * (m : ℝ) ^ (-q)) := by ring
      _ = b * c * (m : ℝ) ^ (-(p + q)) := by
            rw [← Real.rpow_add hm_real_pos]
            congr 2
            ring
  -- Route correction: integrate the already-normalized pointwise residual step,
  -- then substitute the scalar signal and variance profiles exactly once.
  rw [expectedResidualObjective, expectedResidualObjective]
  rw [← MeasureTheory.integral_sub hCurrInt hPrevInt]
  rw [hCoeffPointwise, MeasureTheory.integral_const_mul, hCoeffIntegral]
  calc
    (-(n : ℝ)⁻¹) * (a ^ 2 + σ ^ 2 / (n : ℝ))
        = -(a ^ 2 / (n : ℝ) + (σ ^ 2) / (n : ℝ) ^ 2) := by
            ring_nf
    _ = -(b * c * (m : ℝ) ^ (-(p + q)) / (n : ℝ) + (σ ^ 2) / (n : ℝ) ^ 2) := by
          rw [haSq]

/-- Helper for Theorem 7.30: telescoping the exact backward residual-step
identity from `m + 1` through `k` rewrites the residual numerator at `m` into
the residual at `k` plus the accumulated one-step decrements. -/
lemma expectedResidualObjective_telescope_eq
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (K : ℕ → H →L[ℝ] F)
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
    (h_length : ∀ n, (S n).length = ⊤)
    (fTrue : H)
    (b c p q σ : ℝ)
    (η : ℕ → Ω → F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (n m k : ℕ)
    (h_b : 0 < b)
    (h_c : 0 < c)
    (h_p : 1 < p)
    (h_q : 1 < q)
    (h_σ : 0 < σ)
    (h_noise_memLp : ∀ n, MeasureTheory.MemLp (η n) 2 μ)
    (h_noise_meanZero : ∀ n, ∫ ω, η n ω ∂μ = 0)
    (h_noise_modeVariance :
      ∀ n i,
        ∫ ω,
          (inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) i) : F) (η n ω)) ^ 2 ∂μ =
            σ ^ 2 / (n : ℝ))
    (h_singularDecay :
      ∀ n, (S n).HasAlgebraicSingularValueSquareDecay (h_length n) c p)
    (h_fourierDecay :
      ∀ n, (S n).HasAlgebraicFourierCoefficientSquareDecay (h_length n) fTrue b q)
    (h_tsvd : IsTsvdReconstructionFamily K S h_length Rtsvd)
    (hmk : m ≤ k)
    (hk_le_n : k ≤ n) :
    expectedResidualObjective μ K Rtsvd fTrue η n m =
      expectedResidualObjective μ K Rtsvd fTrue η n k +
        Finset.sum (Finset.Icc (m + 1) k) (fun j ↦
          b * c * (j : ℝ) ^ (-(p + q)) / (n : ℝ) + (σ ^ 2) / (n : ℝ) ^ 2) := by
  let stepTerm : ℕ → ℝ := fun j ↦
    b * c * (j : ℝ) ^ (-(p + q)) / (n : ℝ) + (σ ^ 2) / (n : ℝ) ^ 2
  have hAux :
      ∀ d : ℕ,
        m + d ≤ n →
          expectedResidualObjective μ K Rtsvd fTrue η n m =
            expectedResidualObjective μ K Rtsvd fTrue η n (m + d) +
              Finset.sum (Finset.Icc (m + 1) (m + d)) stepTerm := by
    intro d
    induction d with
    | zero =>
        intro _
        -- At zero gap the interval sum is empty, so the telescope is exact.
        simp [stepTerm]
    | succ d ih =>
        intro hmds_le_n
        have hmd_le_n : m + d ≤ n :=
          Nat.le_trans (Nat.le_succ _) hmds_le_n
        have hstep :
            expectedResidualObjective μ K Rtsvd fTrue η n (m + d) =
              expectedResidualObjective μ K Rtsvd fTrue η n (m + Nat.succ d) +
                stepTerm (m + Nat.succ d) := by
          -- Rewrite the successor residual through the exact backward
          -- decrement at the index `m + d + 1`.
          have hback :=
            expectedResidualObjective_backwardStep_eq
              (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
              (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η)
              (Rtsvd := Rtsvd) (n := n) (m := m + Nat.succ d)
              (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
              (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
              (h_noise_modeVariance := h_noise_modeVariance)
              (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
              (h_tsvd := h_tsvd) (hm := Nat.succ_pos _)
          dsimp [stepTerm] at hback
          linarith
        have hsum :
            Finset.sum (Finset.Icc (m + 1) (m + Nat.succ d)) stepTerm =
              Finset.sum (Finset.Icc (m + 1) (m + d)) stepTerm +
                stepTerm (m + Nat.succ d) := by
          -- Split the interval at its top endpoint so the new step term matches
          -- the exact residual-step identity.
          have hIcc :
              Finset.Icc (m + 1) (m + Nat.succ d) =
                insert (m + Nat.succ d) (Finset.Icc (m + 1) (m + d)) := by
            ext x
            simp
            omega
          rw [hIcc, Finset.sum_insert]
          · ring
          · simp
        calc
          expectedResidualObjective μ K Rtsvd fTrue η n m
              =
            expectedResidualObjective μ K Rtsvd fTrue η n (m + d) +
              Finset.sum (Finset.Icc (m + 1) (m + d)) stepTerm := ih hmd_le_n
          _ =
            (expectedResidualObjective μ K Rtsvd fTrue η n (m + Nat.succ d) +
                stepTerm (m + Nat.succ d)) +
              Finset.sum (Finset.Icc (m + 1) (m + d)) stepTerm := by
                rw [hstep]
          _ =
            expectedResidualObjective μ K Rtsvd fTrue η n (m + Nat.succ d) +
              Finset.sum (Finset.Icc (m + 1) (m + Nat.succ d)) stepTerm := by
                rw [hsum]
                ring
  -- Reindex the auxiliary telescope by the concrete gap `k - m`.
  simpa [stepTerm, Nat.add_sub_of_le hmk] using
    hAux (k - m) (by simpa [Nat.add_sub_of_le hmk] using hk_le_n)

/-- Helper for Theorem 7.30: telescoping the exact backward residual-step
identity from `m + 1` through `k` bounds the residual numerator at `m` below by
the residual at `k` plus the accumulated one-step decrements. -/
lemma expectedResidualObjective_telescope_lowerBound
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (K : ℕ → H →L[ℝ] F)
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
    (h_length : ∀ n, (S n).length = ⊤)
    (fTrue : H)
    (b c p q σ : ℝ)
    (η : ℕ → Ω → F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (n m k : ℕ)
    (h_b : 0 < b)
    (h_c : 0 < c)
    (h_p : 1 < p)
    (h_q : 1 < q)
    (h_σ : 0 < σ)
    (h_noise_memLp : ∀ n, MeasureTheory.MemLp (η n) 2 μ)
    (h_noise_meanZero : ∀ n, ∫ ω, η n ω ∂μ = 0)
    (h_noise_modeVariance :
      ∀ n i,
        ∫ ω,
          (inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) i) : F) (η n ω)) ^ 2 ∂μ =
            σ ^ 2 / (n : ℝ))
    (h_singularDecay :
      ∀ n, (S n).HasAlgebraicSingularValueSquareDecay (h_length n) c p)
    (h_fourierDecay :
      ∀ n, (S n).HasAlgebraicFourierCoefficientSquareDecay (h_length n) fTrue b q)
    (h_tsvd : IsTsvdReconstructionFamily K S h_length Rtsvd)
    (hmk : m ≤ k)
    (hk_le_n : k ≤ n) :
    expectedResidualObjective μ K Rtsvd fTrue η n k +
        Finset.sum (Finset.Icc (m + 1) k) (fun j ↦
          b * c * (j : ℝ) ^ (-(p + q)) / (n : ℝ) + (σ ^ 2) / (n : ℝ) ^ 2) ≤
      expectedResidualObjective μ K Rtsvd fTrue η n m := by
  let stepTerm : ℕ → ℝ := fun j ↦
    b * c * (j : ℝ) ^ (-(p + q)) / (n : ℝ) + (σ ^ 2) / (n : ℝ) ^ 2
  have hAux :
      ∀ d : ℕ,
        m + d ≤ n →
          expectedResidualObjective μ K Rtsvd fTrue η n (m + d) +
              Finset.sum (Finset.Icc (m + 1) (m + d)) stepTerm ≤
            expectedResidualObjective μ K Rtsvd fTrue η n m := by
    intro d
    induction d with
    | zero =>
        intro _
        -- At zero gap the interval sum is empty, so the telescope is exact.
        simp [stepTerm]
    | succ d ih =>
        intro hmds_le_n
        have hmd_le_n : m + d ≤ n :=
          Nat.le_trans (Nat.le_succ _) hmds_le_n
        have hstep :
            expectedResidualObjective μ K Rtsvd fTrue η n (m + Nat.succ d) +
                stepTerm (m + Nat.succ d) =
              expectedResidualObjective μ K Rtsvd fTrue η n (m + d) := by
          -- Rewrite the successor residual through the exact backward
          -- decrement at the index `m + d + 1`.
          have hback :=
            expectedResidualObjective_backwardStep_eq
              (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
              (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η)
              (Rtsvd := Rtsvd) (n := n) (m := m + Nat.succ d)
              (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
              (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
              (h_noise_modeVariance := h_noise_modeVariance)
              (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
              (h_tsvd := h_tsvd) (hm := Nat.succ_pos _)
          dsimp [stepTerm] at hback
          have hpred : m + Nat.succ d - 1 = m + d := by
            omega
          linarith
        have hsum :
            Finset.sum (Finset.Icc (m + 1) (m + Nat.succ d)) stepTerm =
              Finset.sum (Finset.Icc (m + 1) (m + d)) stepTerm +
                stepTerm (m + Nat.succ d) := by
          -- Split the finite interval at its top endpoint so the new step term
          -- matches the successor residual identity.
          have hIcc :
              Finset.Icc (m + 1) (m + Nat.succ d) =
                insert (m + Nat.succ d) (Finset.Icc (m + 1) (m + d)) := by
            ext x
            simp
            omega
          rw [hIcc, Finset.sum_insert]
          · ring
          · simp
        calc
          expectedResidualObjective μ K Rtsvd fTrue η n (m + Nat.succ d) +
              Finset.sum (Finset.Icc (m + 1) (m + Nat.succ d)) stepTerm
              =
            (expectedResidualObjective μ K Rtsvd fTrue η n (m + Nat.succ d) +
                stepTerm (m + Nat.succ d)) +
              Finset.sum (Finset.Icc (m + 1) (m + d)) stepTerm := by
                rw [hsum]
                ring
          _ =
            expectedResidualObjective μ K Rtsvd fTrue η n (m + d) +
              Finset.sum (Finset.Icc (m + 1) (m + d)) stepTerm := by
                rw [hstep]
          _ ≤ expectedResidualObjective μ K Rtsvd fTrue η n m := ih hmd_le_n
  -- Reindex the auxiliary telescope by the concrete gap `k - m`.
  simpa [stepTerm, Nat.add_sub_of_le hmk] using
    hAux (k - m) (by simpa [Nat.add_sub_of_le hmk] using hk_le_n)

/-- Helper for Theorem 7.30: every omitted TSVD mode contributes at least one
noise-window variance term to the expected residual numerator. -/
lemma expectedResidualObjective_noiseWindow_lowerBound
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (K : ℕ → H →L[ℝ] F)
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
    (h_length : ∀ n, (S n).length = ⊤)
    (fTrue : H)
    (b c p q σ : ℝ)
    (η : ℕ → Ω → F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (n m : ℕ)
    (h_b : 0 < b)
    (h_c : 0 < c)
    (h_p : 1 < p)
    (h_q : 1 < q)
    (h_σ : 0 < σ)
    (h_noise_memLp : ∀ n, MeasureTheory.MemLp (η n) 2 μ)
    (h_noise_meanZero : ∀ n, ∫ ω, η n ω ∂μ = 0)
    (h_noise_modeVariance :
      ∀ n i,
        ∫ ω,
          (inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) i) : F) (η n ω)) ^ 2 ∂μ =
            σ ^ 2 / (n : ℝ))
    (h_singularDecay :
      ∀ n, (S n).HasAlgebraicSingularValueSquareDecay (h_length n) c p)
    (h_fourierDecay :
      ∀ n, (S n).HasAlgebraicFourierCoefficientSquareDecay (h_length n) fTrue b q)
    (h_tsvd : IsTsvdReconstructionFamily K S h_length Rtsvd)
    (hm_lt : m < n) :
    (((n - m : ℕ) : ℝ) * (σ ^ 2)) / (n : ℝ) ^ 2 ≤
      expectedResidualObjective μ K Rtsvd fTrue η n m := by
  have hAux :
      ∀ t : ℕ,
        t ≤ n →
          ((t : ℝ) * (σ ^ 2)) / (n : ℝ) ^ 2 ≤
            expectedResidualObjective μ K Rtsvd fTrue η n (n - t) := by
    intro t
    induction t with
    | zero =>
        intro _
        simpa using expectedResidualObjective_nonneg μ K Rtsvd fTrue η n n
    | succ t iht =>
        intro ht
        have ht_le : t ≤ n := Nat.le_of_succ_le ht
        have ht_lt_n : t < n := lt_of_lt_of_le (Nat.lt_succ_self t) ht
        have hstep :
            expectedResidualObjective μ K Rtsvd fTrue η n (n - t) -
                expectedResidualObjective μ K Rtsvd fTrue η n (n - t - 1) =
              -(b * c * ((n - t : ℕ) : ℝ) ^ (-(p + q)) / (n : ℝ) +
                (σ ^ 2) / (n : ℝ) ^ 2) :=
          expectedResidualObjective_backwardStep_eq
            (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
            (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η)
            (Rtsvd := Rtsvd) (n := n) (m := n - t)
            (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
            (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
            (h_noise_modeVariance := h_noise_modeVariance)
            (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
            (h_tsvd := h_tsvd) (hm := Nat.sub_pos_of_lt ht_lt_n)
        have hstep' :
            expectedResidualObjective μ K Rtsvd fTrue η n (n - Nat.succ t) =
              expectedResidualObjective μ K Rtsvd fTrue η n (n - t) +
                (b * c * ((n - t : ℕ) : ℝ) ^ (-(p + q)) / (n : ℝ) +
                  (σ ^ 2) / (n : ℝ) ^ 2) := by
          have hrewrite : n - t - 1 = n - Nat.succ t := by
            omega
          have htmp :
              expectedResidualObjective μ K Rtsvd fTrue η n (n - t - 1) =
                expectedResidualObjective μ K Rtsvd fTrue η n (n - t) +
                  (b * c * ((n - t : ℕ) : ℝ) ^ (-(p + q)) / (n : ℝ) +
                    (σ ^ 2) / (n : ℝ) ^ 2) := by
            linarith
          simpa [hrewrite] using htmp
        have hSignalNonneg :
            0 ≤ b * c * ((n - t : ℕ) : ℝ) ^ (-(p + q)) / (n : ℝ) := by
          positivity
        have ih : ((t : ℝ) * (σ ^ 2)) / (n : ℝ) ^ 2 ≤
            expectedResidualObjective μ K Rtsvd fTrue η n (n - t) :=
          iht ht_le
        have htail :
            expectedResidualObjective μ K Rtsvd fTrue η n (n - t) +
                (σ ^ 2) / (n : ℝ) ^ 2 ≤
              expectedResidualObjective μ K Rtsvd fTrue η n (n - Nat.succ t) := by
          rw [hstep']
          linarith
        calc
          (((Nat.succ t : ℕ) : ℝ) * (σ ^ 2)) / (n : ℝ) ^ 2
              = ((t : ℝ) * (σ ^ 2)) / (n : ℝ) ^ 2 + (σ ^ 2) / (n : ℝ) ^ 2 := by
                  rw [Nat.cast_succ]
                  ring
          _ ≤ expectedResidualObjective μ K Rtsvd fTrue η n (n - t) +
                (σ ^ 2) / (n : ℝ) ^ 2 := by
                  gcongr
          _ ≤ expectedResidualObjective μ K Rtsvd fTrue η n (n - Nat.succ t) := htail
  -- Reindex the backward telescope by the gap length `n - m`.
  simpa [Nat.sub_sub_self (Nat.le_of_lt hm_lt)] using hAux (n - m) (Nat.sub_le _ _)

/-- Helper for Theorem 7.30: the scalar backward step sign already implies the
same benchmark upper bound as Proposition 7.15, without carrying the
proposition-local minimizer context. -/
lemma stepExprNonpos_implies_benchmarkUpper_local
    (b c p q σ : ℝ)
    (n : ℕ)
    (h_b : 0 < b)
    (h_c : 0 < c)
    (h_p : 1 < p)
    (h_q : 1 < q)
    (h_σ : 0 < σ)
    {x : ℝ}
    (hx_pos : 0 < x)
    (hn_pos : 0 < n)
    (h_step :
      -b * x ^ (-q) + ((σ ^ 2) / (n : ℝ)) * (1 / c) * x ^ p ≤ 0) :
    x ≤ (((1 / (b * c)) * ((σ ^ 2) / (n : ℝ))) ^ (-(1 / (p + q)))) := by
  have hpq_pos : 0 < p + q := by
    linarith
  have hx_nonneg : 0 ≤ x := le_of_lt hx_pos
  have hstep_mul :
      (((σ ^ 2) / (n : ℝ)) * (1 / c) * x ^ p) * x ^ q ≤
        (b * x ^ (-q)) * x ^ q := by
    -- Multiply the step inequality by the positive factor `x ^ q`.
    have hmain :
        ((σ ^ 2) / (n : ℝ)) * (1 / c) * x ^ p ≤ b * x ^ (-q) := by
      linarith
    exact mul_le_mul_of_nonneg_right hmain (Real.rpow_nonneg hx_nonneg q)
  have hpow_le :
      x ^ (p + q) ≤ (((1 / (b * c)) * ((σ ^ 2) / (n : ℝ)))⁻¹) := by
    have haux :
        (((σ ^ 2) / (n : ℝ)) * (1 / c)) * x ^ (p + q) ≤ b := by
      calc
        (((σ ^ 2) / (n : ℝ)) * (1 / c)) * x ^ (p + q)
            = ((((σ ^ 2) / (n : ℝ)) * (1 / c)) * x ^ p) * x ^ q := by
                rw [Real.rpow_add hx_pos]
                ring_nf
        _ ≤ (b * x ^ (-q)) * x ^ q := hstep_mul
        _ = b * (x ^ (-q) * x ^ q) := by rw [mul_assoc]
        _ = b * x ^ 0 := by
              rw [← Real.rpow_add hx_pos (-q) q, show -q + q = (0 : ℝ) by ring]
              norm_num
        _ = b := by simp
    have hdiv :
        x ^ (p + q) ≤ b / (((σ ^ 2) / (n : ℝ)) * (1 / c)) := by
      exact (le_div_iff₀ (show 0 < ((σ ^ 2) / (n : ℝ)) * (1 / c) by positivity)).2 <|
        by simpa [mul_comm, mul_left_comm, mul_assoc] using haux
    calc
      x ^ (p + q) ≤ b / (((σ ^ 2) / (n : ℝ)) * (1 / c)) := hdiv
      _ = (((1 / (b * c)) * ((σ ^ 2) / (n : ℝ)))⁻¹) := by
            field_simp [h_b.ne', h_c.ne', h_σ.ne', hn_pos.ne']
  have hroot :
      x ≤ ((((1 / (b * c)) * ((σ ^ 2) / (n : ℝ)))⁻¹) ^ ((p + q)⁻¹)) := by
    -- Take the positive `(p + q)`-th root of the power inequality.
    simpa [one_div] using
      (Real.le_rpow_inv_iff_of_pos
        (show 0 ≤ x by exact hx_nonneg)
        (show 0 ≤ (((1 / (b * c)) * ((σ ^ 2) / (n : ℝ)))⁻¹) by positivity)
        hpq_pos).2 hpow_le
  simpa [one_div, Real.rpow_neg_eq_inv_rpow] using hroot

/-- Helper for Theorem 7.30: the scalar forward step sign already implies the
same benchmark lower bound as Proposition 7.15, without carrying the
proposition-local minimizer context. -/
lemma stepExprNonneg_implies_benchmarkLower_local
    (b c p q σ : ℝ)
    (n : ℕ)
    (h_b : 0 < b)
    (h_c : 0 < c)
    (h_p : 1 < p)
    (h_q : 1 < q)
    (h_σ : 0 < σ)
    {x : ℝ}
    (hx_pos : 0 < x)
    (hn_pos : 0 < n)
    (h_step :
      0 ≤ -b * x ^ (-q) + ((σ ^ 2) / (n : ℝ)) * (1 / c) * x ^ p) :
    (((1 / (b * c)) * ((σ ^ 2) / (n : ℝ))) ^ (-(1 / (p + q)))) ≤ x := by
  have hpq_pos : 0 < p + q := by
    linarith
  have hx_nonneg : 0 ≤ x := le_of_lt hx_pos
  have hstep_mul :
      (b * x ^ (-q)) * x ^ q ≤
        (((σ ^ 2) / (n : ℝ)) * (1 / c) * x ^ p) * x ^ q := by
    -- Multiply the reversed step inequality by the positive factor `x ^ q`.
    have hmain :
        b * x ^ (-q) ≤ ((σ ^ 2) / (n : ℝ)) * (1 / c) * x ^ p := by
      linarith
    exact mul_le_mul_of_nonneg_right hmain (Real.rpow_nonneg hx_nonneg q)
  have hpow_le :
      (((1 / (b * c)) * ((σ ^ 2) / (n : ℝ)))⁻¹) ≤ x ^ (p + q) := by
    have haux :
        b ≤ (((σ ^ 2) / (n : ℝ)) * (1 / c)) * x ^ (p + q) := by
      calc
        b = b * x ^ 0 := by simp
        _ = b * (x ^ (-q) * x ^ q) := by
              rw [← Real.rpow_add hx_pos (-q) q, show -q + q = (0 : ℝ) by ring]
              norm_num
        _ = (b * x ^ (-q)) * x ^ q := by rw [mul_assoc]
        _ ≤ (((σ ^ 2) / (n : ℝ)) * (1 / c) * x ^ p) * x ^ q := hstep_mul
        _ = (((σ ^ 2) / (n : ℝ)) * (1 / c)) * x ^ (p + q) := by
              rw [Real.rpow_add hx_pos]
              ring_nf
    have hdiv :
        b / (((σ ^ 2) / (n : ℝ)) * (1 / c)) ≤ x ^ (p + q) := by
      exact (div_le_iff₀ (show 0 < ((σ ^ 2) / (n : ℝ)) * (1 / c) by positivity)).2 <|
        by simpa [mul_comm, mul_left_comm, mul_assoc] using haux
    calc
      (((1 / (b * c)) * ((σ ^ 2) / (n : ℝ)))⁻¹)
          = b / (((σ ^ 2) / (n : ℝ)) * (1 / c)) := by
              field_simp [h_b.ne', h_c.ne', h_σ.ne', hn_pos.ne']
      _ ≤ x ^ (p + q) := hdiv
  have hroot :
      ((((1 / (b * c)) * ((σ ^ 2) / (n : ℝ)))⁻¹) ^ ((p + q)⁻¹)) ≤ x := by
    -- Convert the power inequality back to a bound on `x`.
    simpa [one_div] using
      (Real.rpow_inv_le_iff_of_pos
        (show 0 ≤ (((1 / (b * c)) * ((σ ^ 2) / (n : ℝ)))⁻¹) by positivity)
        (show 0 ≤ x by exact hx_nonneg)
        hpq_pos).2 hpow_le
  simpa [one_div, Real.rpow_neg_eq_inv_rpow] using hroot

/-- Helper for Theorem 7.30: a forward one-step GCV comparison can be
rearranged into the exact successor-residual inequality that survives
denominator clearing. -/
lemma gcvForwardComparison_implies_successorResidualControl
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (K : ℕ → H →L[ℝ] F)
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
    (h_length : ∀ n, (S n).length = ⊤)
    (fTrue : H)
    (b c p q σ : ℝ)
    (η : ℕ → Ω → F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (n m : ℕ)
    (h_b : 0 < b)
    (h_c : 0 < c)
    (h_p : 1 < p)
    (h_q : 1 < q)
    (h_σ : 0 < σ)
    (h_noise_memLp : ∀ n, MeasureTheory.MemLp (η n) 2 μ)
    (h_noise_meanZero : ∀ n, ∫ ω, η n ω ∂μ = 0)
    (h_noise_modeVariance :
      ∀ n i,
        ∫ ω,
          (inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) i) : F) (η n ω)) ^ 2 ∂μ =
            σ ^ 2 / (n : ℝ))
    (h_singularDecay :
      ∀ n, (S n).HasAlgebraicSingularValueSquareDecay (h_length n) c p)
    (h_fourierDecay :
      ∀ n, (S n).HasAlgebraicFourierCoefficientSquareDecay (h_length n) fTrue b q)
    (h_tsvd : IsTsvdReconstructionFamily K S h_length Rtsvd)
    (hm_succ_lt : m + 1 < n)
    (h_compare :
      TsvdGcv.expectedObjective μ K Rtsvd fTrue η n m ≤
        TsvdGcv.expectedObjective μ K Rtsvd fTrue η n (m + 1)) :
    let gap : ℝ := ((n - (m + 1) : ℕ) : ℝ)
    gap ^ 2 *
        ((n : ℝ) * b * c * (((m + 1 : ℕ) : ℝ) ^ (-(p + q))) + σ ^ 2) ≤
      (2 * gap + 1) *
        ((n : ℝ) ^ 2 * expectedResidualObjective μ K Rtsvd fTrue η n (m + 1)) := by
  have hm_lt : m < n := lt_trans (Nat.lt_succ_self m) hm_succ_lt
  have hn_pos_nat : 0 < n := lt_trans (Nat.succ_pos _) hm_succ_lt
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast hn_pos_nat
  have hgap_pos_nat : 0 < n - (m + 1) := Nat.sub_pos_of_lt hm_succ_lt
  have hgap_pos : 0 < (((n - (m + 1) : ℕ) : ℝ)) := by
    exact_mod_cast hgap_pos_nat
  have hcompare_gap :
      (((n : ℝ) ^ 2) * expectedResidualObjective μ K Rtsvd fTrue η n m) /
          ((((n - (m + 1) : ℕ) : ℝ) + 1) ^ 2) ≤
        (((n : ℝ) ^ 2) * expectedResidualObjective μ K Rtsvd fTrue η n (m + 1)) /
          (((n - (m + 1) : ℕ) : ℝ) ^ 2) := by
    have hcurr_gap :
        (((n - m : ℕ) : ℝ)) = (((n - (m + 1) : ℕ) : ℝ) + 1) := by
      have hnat : n - m = n - (m + 1) + 1 := by
        omega
      exact_mod_cast hnat
    -- Rewrite both objectives into the stable residual-over-gap quotient form.
    rw [gcvExpectedObjective_eq_gapResidualQuotient
      (μ := μ) (K := K) (Rtsvd := Rtsvd) (fTrue := fTrue) (η := η) (hm_lt := hm_lt),
      gcvExpectedObjective_eq_gapResidualQuotient
        (μ := μ) (K := K) (Rtsvd := Rtsvd) (fTrue := fTrue) (η := η) (hm_lt := hm_succ_lt)]
      at h_compare
    simpa [hcurr_gap] using h_compare
  have hstep :
      expectedResidualObjective μ K Rtsvd fTrue η n m =
        expectedResidualObjective μ K Rtsvd fTrue η n (m + 1) +
          (b * c * (((m + 1 : ℕ) : ℝ) ^ (-(p + q))) / (n : ℝ) + (σ ^ 2) / (n : ℝ) ^ 2) := by
    -- Rewrite the predecessor residual through the exact successor decrement.
    have hback :=
      expectedResidualObjective_backwardStep_eq
        (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
        (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η)
        (Rtsvd := Rtsvd) (n := n) (m := m + 1)
        (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
        (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
        (h_noise_modeVariance := h_noise_modeVariance)
        (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
        (h_tsvd := h_tsvd) (hm := Nat.succ_pos _)
    have hpred : m + 1 - 1 = m := by omega
    have hback' :
        expectedResidualObjective μ K Rtsvd fTrue η n (m + 1) -
            expectedResidualObjective μ K Rtsvd fTrue η n m =
          -(b * c * (((m + 1 : ℕ) : ℝ) ^ (-(p + q))) / (n : ℝ) + (σ ^ 2) / (n : ℝ) ^ 2) := by
      simpa [hpred] using hback
    linarith
  let gap : ℝ := ((n - (m + 1) : ℕ) : ℝ)
  have hcompare_cleared :
      gap ^ 2 *
          (((n : ℝ) ^ 2 * expectedResidualObjective μ K Rtsvd fTrue η n (m + 1)) +
            ((n : ℝ) * b * c * (((m + 1 : ℕ) : ℝ) ^ (-(p + q))) + σ ^ 2)) ≤
        (gap + 1) ^ 2 *
          ((n : ℝ) ^ 2 * expectedResidualObjective μ K Rtsvd fTrue η n (m + 1)) := by
    dsimp [gap]
    rw [hstep] at hcompare_gap
    have htmp := hcompare_gap
    field_simp [hn_pos.ne', hgap_pos.ne'] at htmp
    simpa [mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm] using htmp
  -- Expand the cleared comparison and isolate the exact residual control.
  dsimp [gap]
  nlinarith [hcompare_cleared]

/-- Helper for Theorem 7.30: a pointwise GCV minimizer should localize to the
one-step neighborhood of the canonical benchmark floor `optimalIndex b c p q
σ n`. -/
lemma gcvBackwardComparison_implies_stepExprNonpos
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (K : ℕ → H →L[ℝ] F)
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
    (h_length : ∀ n, (S n).length = ⊤)
    (fTrue : H)
    (b c p q σ : ℝ)
    (η : ℕ → Ω → F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (n m : ℕ)
    (h_b : 0 < b)
    (h_c : 0 < c)
    (h_p : 1 < p)
    (h_q : 1 < q)
    (h_σ : 0 < σ)
    (h_noise_memLp : ∀ n, MeasureTheory.MemLp (η n) 2 μ)
    (h_noise_meanZero : ∀ n, ∫ ω, η n ω ∂μ = 0)
    (h_noise_modeVariance :
      ∀ n i,
        ∫ ω,
          (inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) i) : F) (η n ω)) ^ 2 ∂μ =
            σ ^ 2 / (n : ℝ))
    (h_singularDecay :
      ∀ n, (S n).HasAlgebraicSingularValueSquareDecay (h_length n) c p)
    (h_fourierDecay :
      ∀ n, (S n).HasAlgebraicFourierCoefficientSquareDecay (h_length n) fTrue b q)
    (h_tsvd : IsTsvdReconstructionFamily K S h_length Rtsvd)
    (hm_pos : 0 < m)
    (hm_lt : m < n)
    (h_compare :
      TsvdGcv.expectedObjective μ K Rtsvd fTrue η n m ≤
        TsvdGcv.expectedObjective μ K Rtsvd fTrue η n (m - 1)) :
    -b * (m : ℝ) ^ (-q) + ((σ ^ 2) / (n : ℝ)) * (1 / c) * (m : ℝ) ^ p ≤ 0 := by
  have hn_pos_nat : 0 < n := lt_trans hm_pos hm_lt
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast hn_pos_nat
  have hgap_pos_nat : 0 < n - m := Nat.sub_pos_of_lt hm_lt
  have hgap_pos : 0 < (((n - m : ℕ) : ℝ)) := by
    exact_mod_cast hgap_pos_nat
  have hm_prev_lt : m - 1 < n := lt_of_le_of_lt (Nat.sub_le _ _) hm_lt
  have hcompare_gap :
      (((n : ℝ) ^ 2) * expectedResidualObjective μ K Rtsvd fTrue η n m) /
          (((n - m : ℕ) : ℝ) ^ 2) ≤
        (((n : ℝ) ^ 2) * expectedResidualObjective μ K Rtsvd fTrue η n (m - 1)) /
          ((((n - m : ℕ) : ℝ) + 1) ^ 2) := by
    have hprev_gap :
        (((n - (m - 1) : ℕ) : ℝ)) = (((n - m : ℕ) : ℝ) + 1) := by
      have hnat : n - (m - 1) = n - m + 1 := by
        omega
      exact_mod_cast hnat
    rw [gcvExpectedObjective_eq_gapResidualQuotient
      (μ := μ) (K := K) (Rtsvd := Rtsvd) (fTrue := fTrue) (η := η) (hm_lt := hm_lt),
      gcvExpectedObjective_eq_gapResidualQuotient
        (μ := μ) (K := K) (Rtsvd := Rtsvd) (fTrue := fTrue) (η := η) (hm_lt := hm_prev_lt)]
      at h_compare
    simpa [hprev_gap] using h_compare
  have hstep :
      expectedResidualObjective μ K Rtsvd fTrue η n (m - 1) =
        expectedResidualObjective μ K Rtsvd fTrue η n m +
          (b * c * (m : ℝ) ^ (-(p + q)) / (n : ℝ) + (σ ^ 2) / (n : ℝ) ^ 2) := by
    have hback :=
      expectedResidualObjective_backwardStep_eq
        (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
        (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η)
        (Rtsvd := Rtsvd) (n := n) (m := m)
        (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
        (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
        (h_noise_modeVariance := h_noise_modeVariance)
        (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
        (h_tsvd := h_tsvd) hm_pos
    linarith
  have hnoise_lb :
      (((n - m : ℕ) : ℝ) * (σ ^ 2)) / (n : ℝ) ^ 2 ≤
        expectedResidualObjective μ K Rtsvd fTrue η n m :=
    expectedResidualObjective_noiseWindow_lowerBound
      (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
      (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η)
      (Rtsvd := Rtsvd) (n := n) (m := m)
      (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
      (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
      (h_noise_modeVariance := h_noise_modeVariance)
      (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
      (h_tsvd := h_tsvd) hm_lt
  let gap : ℝ := ((n - m : ℕ) : ℝ)
  have hcompare_cleared :
      (n : ℝ) ^ 2 * expectedResidualObjective μ K Rtsvd fTrue η n m * (gap + 1) ^ 2 ≤
        gap ^ 2 *
          ((n : ℝ) ^ 2 * expectedResidualObjective μ K Rtsvd fTrue η n m +
            ((n : ℝ) * b * c * (m : ℝ) ^ (-(p + q)) + σ ^ 2)) := by
    dsimp [gap]
    rw [hstep] at hcompare_gap
    have htmp := hcompare_gap
    field_simp [hn_pos.ne', hgap_pos.ne'] at htmp
    simpa [mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm] using htmp
  have hlin :
      (2 * gap + 1) * ((n : ℝ) ^ 2 * expectedResidualObjective μ K Rtsvd fTrue η n m) ≤
        gap ^ 2 * ((n : ℝ) * b * c * (m : ℝ) ^ (-(p + q)) + σ ^ 2) := by
    nlinarith [hcompare_cleared]
  have hnoise_cleared :
      gap * (σ ^ 2) ≤ (n : ℝ) ^ 2 * expectedResidualObjective μ K Rtsvd fTrue η n m := by
    have hmul :=
      mul_le_mul_of_nonneg_right hnoise_lb (show 0 ≤ (n : ℝ) ^ 2 by positivity)
    have htmp := hmul
    field_simp [hn_pos.ne'] at htmp
    nlinarith [htmp]
  have hlineq :
      (gap + 1) * (σ ^ 2) ≤ gap * ((n : ℝ) * b * c * (m : ℝ) ^ (-(p + q))) := by
    nlinarith [hlin, hnoise_cleared]
  have hsignal_ge :
      σ ^ 2 ≤ (n : ℝ) * b * c * (m : ℝ) ^ (-(p + q)) := by
    have hσ_nonneg : 0 ≤ σ ^ 2 := by positivity
    have hgap_scaled :
        gap * (σ ^ 2) ≤ gap * ((n : ℝ) * b * c * (m : ℝ) ^ (-(p + q))) := by
      calc
        gap * (σ ^ 2) ≤ (gap + 1) * (σ ^ 2) := by
          nlinarith [hgap_pos, hσ_nonneg]
        _ ≤ gap * ((n : ℝ) * b * c * (m : ℝ) ^ (-(p + q))) := hlineq
    nlinarith [hgap_scaled, hgap_pos]
  have hm_real_pos : 0 < (m : ℝ) := by
    exact_mod_cast hm_pos
  have hm_factor :
      (m : ℝ) ^ (-(p + q)) * (m : ℝ) ^ p = (m : ℝ) ^ (-q) := by
    rw [← Real.rpow_add hm_real_pos]
    congr 2
    ring
  have hstep_bound :
      ((σ ^ 2) / (n : ℝ)) * (1 / c) * (m : ℝ) ^ p ≤ b * (m : ℝ) ^ (-q) := by
    let scale : ℝ := (1 / c) * (m : ℝ) ^ p / (n : ℝ)
    have hscale_nonneg : 0 ≤ scale := by
      positivity
    have hscaled := mul_le_mul_of_nonneg_right hsignal_ge hscale_nonneg
    calc
      ((σ ^ 2) / (n : ℝ)) * (1 / c) * (m : ℝ) ^ p
          = (σ ^ 2) * scale := by
              dsimp [scale]
              field_simp [hn_pos.ne']
      _ ≤ ((n : ℝ) * b * c * (m : ℝ) ^ (-(p + q))) * scale := hscaled
      _ = b * ((m : ℝ) ^ (-(p + q)) * (m : ℝ) ^ p) := by
            dsimp [scale]
            field_simp [hn_pos.ne', h_c.ne']
      _ = b * (m : ℝ) ^ (-q) := by rw [hm_factor]
  linarith

/-- Helper for Theorem 7.30: a backward one-step GCV comparison forces the
same scalar upper benchmark bound as in Proposition 7.15. -/
lemma gcvBackwardComparison_implies_benchmarkUpper
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (K : ℕ → H →L[ℝ] F)
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
    (h_length : ∀ n, (S n).length = ⊤)
    (fTrue : H)
    (b c p q σ : ℝ)
    (η : ℕ → Ω → F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (n m : ℕ)
    (h_b : 0 < b)
    (h_c : 0 < c)
    (h_p : 1 < p)
    (h_q : 1 < q)
    (h_σ : 0 < σ)
    (h_noise_memLp : ∀ n, MeasureTheory.MemLp (η n) 2 μ)
    (h_noise_meanZero : ∀ n, ∫ ω, η n ω ∂μ = 0)
    (h_noise_modeVariance :
      ∀ n i,
        ∫ ω,
          (inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) i) : F) (η n ω)) ^ 2 ∂μ =
            σ ^ 2 / (n : ℝ))
    (h_singularDecay :
      ∀ n, (S n).HasAlgebraicSingularValueSquareDecay (h_length n) c p)
    (h_fourierDecay :
      ∀ n, (S n).HasAlgebraicFourierCoefficientSquareDecay (h_length n) fTrue b q)
    (h_tsvd : IsTsvdReconstructionFamily K S h_length Rtsvd)
    (hm_pos : 0 < m)
    (hm_lt : m < n)
    (h_compare :
      TsvdGcv.expectedObjective μ K Rtsvd fTrue η n m ≤
        TsvdGcv.expectedObjective μ K Rtsvd fTrue η n (m - 1)) :
    (m : ℝ) ≤ (((1 / (b * c)) * ((σ ^ 2) / (n : ℝ))) ^ (-(1 / (p + q)))) := by
  have hn_pos : 0 < n := lt_trans hm_pos hm_lt
  have h_step :
      -b * (m : ℝ) ^ (-q) + ((σ ^ 2) / (n : ℝ)) * (1 / c) * (m : ℝ) ^ p ≤ 0 :=
    gcvBackwardComparison_implies_stepExprNonpos
      (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
      (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η)
      (Rtsvd := Rtsvd) (n := n) (m := m)
      (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
      (h_noise_memLp := h_noise_memLp)
      (h_noise_meanZero := h_noise_meanZero)
      (h_noise_modeVariance := h_noise_modeVariance)
      (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
      (h_tsvd := h_tsvd) hm_pos hm_lt h_compare
  -- Once the GCV comparison is reduced to the scalar step sign, Proposition
  -- 7.15 supplies the benchmark upper bound directly.
  exact stepExprNonpos_implies_benchmarkUpper_local
    (b := b) (c := c) (p := p) (q := q) (σ := σ) (n := n)
    (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
    (x := m) (hx_pos := by exact_mod_cast hm_pos) (hn_pos := hn_pos) (h_step := h_step)

/-- Helper for Theorem 7.30: the backward comparison route alone already forces
any pointwise GCV minimizer to stay below the canonical benchmark floor. -/
lemma gcvMinimizer_le_optimalIndex
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (K : ℕ → H →L[ℝ] F)
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
    (h_length : ∀ n, (S n).length = ⊤)
    (fTrue : H)
    (b c p q σ : ℝ)
    (η : ℕ → Ω → F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (n mStar : ℕ)
    (h_b : 0 < b)
    (h_c : 0 < c)
    (h_p : 1 < p)
    (h_q : 1 < q)
    (h_σ : 0 < σ)
    (h_noise_memLp : ∀ n, MeasureTheory.MemLp (η n) 2 μ)
    (h_noise_meanZero : ∀ n, ∫ ω, η n ω ∂μ = 0)
    (h_noise_modeVariance :
      ∀ n i,
        ∫ ω,
          (inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) i) : F) (η n ω)) ^ 2 ∂μ =
            σ ^ 2 / (n : ℝ))
    (h_singularDecay :
      ∀ n, (S n).HasAlgebraicSingularValueSquareDecay (h_length n) c p)
    (h_fourierDecay :
      ∀ n, (S n).HasAlgebraicFourierCoefficientSquareDecay (h_length n) fTrue b q)
    (h_tsvd : IsTsvdReconstructionFamily K S h_length Rtsvd)
    (hmStar_mem : mStar ∈ TsvdGcv.gcvAdmissibleIndexSet n)
    (h_min :
      IsMinOn
        (TsvdGcv.expectedObjective μ K Rtsvd fTrue η n)
        (TsvdGcv.gcvAdmissibleIndexSet n)
        mStar)
    (h_optimalIndex_mem :
      optimalIndex b c p q σ n ∈ TsvdGcv.gcvAdmissibleIndexSet n) :
    mStar ≤ optimalIndex b c p q σ n := by
  have hmStar_lt : mStar < n := (TsvdGcv.mem_gcvAdmissibleIndexSet_iff n mStar).1 hmStar_mem |>.2
  have hmin_compare :
      ∀ y ∈ TsvdGcv.gcvAdmissibleIndexSet n,
        TsvdGcv.expectedObjective μ K Rtsvd fTrue η n mStar ≤
          TsvdGcv.expectedObjective μ K Rtsvd fTrue η n y := by
    -- Unpack the `IsMinOn` witness into the pointwise comparison form used by
    -- the predecessor and successor bridge lemmas.
    simpa [isMinOn_iff] using h_min
  by_cases hm_pos : 0 < mStar
  · have hprofile_eq :
        (((1 / (b * c)) * ((σ ^ 2) / (n : ℝ))) ^ (-(1 / (p + q)))) =
          ((b * c) ^ (1 / (p + q))) * (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q)))) := by
      -- Normalize the benchmark expression to the explicit floor profile.
      calc
        (((1 / (b * c)) * ((σ ^ 2) / (n : ℝ))) ^ (-(1 / (p + q))))
            = (1 / (b * c) : ℝ) ^ (-(1 / (p + q))) *
                (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q)))) := by
                  rw [Real.mul_rpow (by positivity) (by positivity)]
        _ = (((1 / (b * c) : ℝ)⁻¹) ^ (1 / (p + q))) *
              (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q)))) := by
                rw [Real.rpow_neg_eq_inv_rpow]
        _ = ((b * c) ^ (1 / (p + q))) *
              (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q)))) := by
                rw [one_div, inv_inv]
    have hprofile_nonneg :
        0 ≤ ((b * c) ^ (1 / (p + q))) * (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q)))) := by
      positivity
    have hmPred_mem : mStar - 1 ∈ TsvdGcv.gcvAdmissibleIndexSet n := by
      -- Positive minimizers allow the predecessor comparison on the same
      -- denominator-valid admissible set.
      rw [TsvdGcv.mem_gcvAdmissibleIndexSet_iff]
      refine ⟨⟨Nat.zero_le _, le_trans (Nat.sub_le _ _) (Nat.le_of_lt hmStar_lt)⟩, ?_⟩
      exact lt_of_le_of_lt (Nat.sub_le _ _) hmStar_lt
    have hbenchmark :
        (mStar : ℝ) ≤
          (((1 / (b * c)) * ((σ ^ 2) / (n : ℝ))) ^ (-(1 / (p + q)))) :=
      gcvBackwardComparison_implies_benchmarkUpper
        (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
        (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η)
        (Rtsvd := Rtsvd) (n := n) (m := mStar)
        (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
        (h_noise_memLp := h_noise_memLp)
        (h_noise_meanZero := h_noise_meanZero)
        (h_noise_modeVariance := h_noise_modeVariance)
        (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
        (h_tsvd := h_tsvd) hm_pos hmStar_lt (hmin_compare (mStar - 1) hmPred_mem)
    have hreal :
        (mStar : ℝ) ≤
          ((b * c) ^ (1 / (p + q))) * (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q)))) := by
      calc
        (mStar : ℝ)
            ≤ (((1 / (b * c)) * ((σ ^ 2) / (n : ℝ))) ^ (-(1 / (p + q)))) := hbenchmark
        _ = ((b * c) ^ (1 / (p + q))) * (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q)))) := hprofile_eq
    -- Convert the real upper bound to the defining floor inequality.
    rw [optimalIndex_def]
    exact (Nat.le_floor_iff hprofile_nonneg).2 hreal
  · have hm_zero : mStar = 0 := by
      exact Nat.eq_zero_of_le_zero (le_of_not_gt hm_pos)
    -- The boundary case `mStar = 0` is already below every admissible nat benchmark.
    simp [hm_zero]

/-- Helper for Theorem 7.30: the real successor bound on the benchmark profile
immediately forces the floor-defined benchmark index below that same
successor. -/
lemma optimalIndex_le_succ_of_benchmarkLower
    (b c p q σ : ℝ)
    (n m : ℕ)
    (h_b : 0 < b)
    (h_c : 0 < c)
    (h_p : 1 < p)
    (h_q : 1 < q)
    (h_σ : 0 < σ)
    (h_benchmark :
      (((1 / (b * c)) * ((σ ^ 2) / (n : ℝ))) ^ (-(1 / (p + q)))) ≤
        (((m + 1 : ℕ) : ℝ))) :
    optimalIndex b c p q σ n ≤ m + 1 := by
  have hprofile_eq :
      (((1 / (b * c)) * ((σ ^ 2) / (n : ℝ))) ^ (-(1 / (p + q)))) =
        ((b * c) ^ (1 / (p + q))) * (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q)))) := by
    -- Normalize the benchmark lower bound into the explicit profile spelling
    -- used by `optimalIndex_def`.
    calc
      (((1 / (b * c)) * ((σ ^ 2) / (n : ℝ))) ^ (-(1 / (p + q))))
          = (1 / (b * c) : ℝ) ^ (-(1 / (p + q))) *
              (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q)))) := by
                rw [Real.mul_rpow (by positivity) (by positivity)]
      _ = (((1 / (b * c) : ℝ)⁻¹) ^ (1 / (p + q))) *
            (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q)))) := by
              rw [Real.rpow_neg_eq_inv_rpow]
      _ = ((b * c) ^ (1 / (p + q))) *
            (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q)))) := by
              rw [one_div, inv_inv]
  have hrealNat :
      ((b * c) ^ (1 / (p + q))) * (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q)))) ≤
        (((m + 1 : ℕ) : ℝ)) := by
    -- Transport the benchmark lower bound into the exact profile expression
    -- before applying the floor monotonicity lemma.
    calc
      ((b * c) ^ (1 / (p + q))) * (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q))))
          = (((1 / (b * c)) * ((σ ^ 2) / (n : ℝ))) ^ (-(1 / (p + q)))) := by
              symm
              exact hprofile_eq
      _ ≤ (((m + 1 : ℕ) : ℝ)) := h_benchmark
  -- The floor-defined benchmark index inherits the same successor bound.
  rw [optimalIndex_def]
  exact Nat.floor_le_of_le hrealNat

/-- Helper for Theorem 7.30: eventual GCV optimality and admissibility let us
reuse the stable backward-comparison theorem pointwise to keep the GCV family
below the canonical benchmark floor. -/
lemma gcvOptimalFamily_eventually_le_optimalIndex
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (K : ℕ → H →L[ℝ] F)
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
    (h_length : ∀ n, (S n).length = ⊤)
    (fTrue : H)
    (b c p q σ : ℝ)
    (η : ℕ → Ω → F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (mV : ℕ → ℕ)
    (h_b : 0 < b)
    (h_c : 0 < c)
    (h_p : 1 < p)
    (h_q : 1 < q)
    (h_σ : 0 < σ)
    (h_noise_memLp : ∀ n, MeasureTheory.MemLp (η n) 2 μ)
    (h_noise_meanZero : ∀ n, ∫ ω, η n ω ∂μ = 0)
    (h_noise_modeVariance :
      ∀ n i,
        ∫ ω,
          (inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) i) : F) (η n ω)) ^ 2 ∂μ =
            σ ^ 2 / (n : ℝ))
    (h_singularDecay :
      ∀ n, (S n).HasAlgebraicSingularValueSquareDecay (h_length n) c p)
    (h_fourierDecay :
      ∀ n, (S n).HasAlgebraicFourierCoefficientSquareDecay (h_length n) fTrue b q)
    (h_tsvd : IsTsvdReconstructionFamily K S h_length Rtsvd)
    (h_gcvOptimal : TsvdGcv.IsOptimalFamilyEventually μ K Rtsvd fTrue η mV)
    (h_optimalIndex_mem :
      ∀ᶠ n in Filter.atTop, optimalIndex b c p q σ n ∈ TsvdGcv.gcvAdmissibleIndexSet n) :
    ∀ᶠ n in Filter.atTop, mV n ≤ optimalIndex b c p q σ n := by
  have h_mem :
      ∀ᶠ n in Filter.atTop, mV n ∈ TsvdGcv.gcvAdmissibleIndexSet n :=
    TsvdGcv.IsOptimalFamilyEventually.eventually_mem h_gcvOptimal
  have h_min :
      ∀ᶠ n in Filter.atTop,
        IsMinOn
          (TsvdGcv.expectedObjective μ K Rtsvd fTrue η n)
          (TsvdGcv.gcvAdmissibleIndexSet n)
          (mV n) :=
    TsvdGcv.IsOptimalFamilyEventually.eventually_isMinOn h_gcvOptimal
  -- Push the pointwise backward-comparison theorem through the eventual
  -- admissibility and minimizer witnesses carried by `h_gcvOptimal`.
  filter_upwards [h_mem, h_min, h_optimalIndex_mem] with n hn_mem hn_min hn_optimal
  exact
    gcvMinimizer_le_optimalIndex
      (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
      (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η)
      (Rtsvd := Rtsvd) (n := n) (mStar := mV n)
      (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
      (h_noise_memLp := h_noise_memLp)
      (h_noise_meanZero := h_noise_meanZero)
      (h_noise_modeVariance := h_noise_modeVariance)
      (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
      (h_tsvd := h_tsvd) hn_mem hn_min hn_optimal

/-- Helper for Theorem 7.30: a family trapped eventually between the benchmark
and every fixed sub-benchmark multiple is asymptotically equivalent to the
benchmark itself. -/
lemma scaledOptimalIndexBounds_isEquivalent
    (b c p q σ : ℝ)
    (mV : ℕ → ℕ)
    (h_b : 0 < b)
    (h_c : 0 < c)
    (h_p : 1 < p)
    (h_q : 1 < q)
    (h_σ : 0 < σ)
    (h_upper :
      ∀ᶠ n in Filter.atTop, (mV n : ℝ) ≤ (optimalIndex b c p q σ n : ℝ))
    (h_lower :
      ∀ δ : ℝ, 0 < δ → δ < 1 →
        ∀ᶠ n in Filter.atTop,
          (1 - δ) * (optimalIndex b c p q σ n : ℝ) ≤ (mV n : ℝ)) :
    Asymptotics.IsEquivalent Filter.atTop
      (fun n ↦ (mV n : ℝ))
      (fun n ↦ (optimalIndex b c p q σ n : ℝ)) := by
  have h_beta_pos :
      ∀ᶠ n in Filter.atTop, 0 < (optimalIndex b c p q σ n : ℝ) :=
    optimalIndex_eventually_pos b c p q σ h_b h_c h_p h_q h_σ
  have h_beta_ne :
      ∀ᶠ n in Filter.atTop, (optimalIndex b c p q σ n : ℝ) ≠ 0 :=
    h_beta_pos.mono fun _ hn ↦ ne_of_gt hn
  rw [Asymptotics.isEquivalent_iff_tendsto_one h_beta_ne]
  -- Route correction: once the lower control is multiplicative, the final
  -- asymptotic-equivalence step is a direct ratio squeeze.
  refine Metric.tendsto_nhds.2 ?_
  intro ε h_ε
  let δ : ℝ := min (ε / 2) (1 / 2 : ℝ)
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact lt_min (half_pos h_ε) (by norm_num)
  have hδ_lt_one : δ < 1 := by
    dsimp [δ]
    exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hδ_lt_ε : δ < ε := by
    have hhalf_lt : ε / 2 < ε := by
      linarith
    exact lt_of_le_of_lt (min_le_left _ _) hhalf_lt
  have h_lowerδ :
      ∀ᶠ n in Filter.atTop,
        (1 - δ) * (optimalIndex b c p q σ n : ℝ) ≤ (mV n : ℝ) :=
    h_lower δ hδ_pos hδ_lt_one
  filter_upwards [h_upper, h_lowerδ, h_beta_pos] with n hn_upper hn_lower hn_beta_pos
  let β : ℝ := (optimalIndex b c p q σ n : ℝ)
  let α : ℝ := (mV n : ℝ)
  have hβ_ne : β ≠ 0 := ne_of_gt hn_beta_pos
  have hratio_le : α / β ≤ 1 := by
    have hdiv : α / β ≤ β / β :=
      div_le_div_of_nonneg_right hn_upper hn_beta_pos.le
    simpa [α, β, hβ_ne] using hdiv
  have hratio_ge : 1 - δ ≤ α / β := by
    have hdiv :
        ((1 - δ) * β) / β ≤ α / β :=
      div_le_div_of_nonneg_right hn_lower hn_beta_pos.le
    simpa [α, β, hβ_ne] using hdiv
  have hdist_nonneg : 0 ≤ 1 - α / β := by
    linarith
  have hdist_le : dist (α / β) 1 ≤ δ := by
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg hdist_nonneg]
    linarith
  exact lt_of_le_of_lt hdist_le hδ_lt_ε

/-- Helper for Theorem 7.30: a pointwise sub-benchmark truncation level with
`1 ≤ δ * β` still leaves at least one full benchmark step between `m` and
`β`. -/
lemma scaledSubbenchmark_gapCount_pos
    (δ : ℝ)
    (m β : ℕ)
    (hδ_large : 1 ≤ δ * (β : ℝ))
    (hm_scaled : (m : ℝ) ≤ (1 - δ) * (β : ℝ)) :
    m < β := by
  -- The scaled lower-bound hypothesis makes the benchmark gap `β - m`
  -- strictly positive once `δ * β` is at least `1`.
  by_contra h_not_lt
  have hβ_le_m : β ≤ m := Nat.le_of_not_gt h_not_lt
  have hβ_le_scaled : (β : ℝ) ≤ (1 - δ) * (β : ℝ) := by
    exact le_trans (by exact_mod_cast hβ_le_m) hm_scaled
  have hδβ_le_zero : δ * (β : ℝ) ≤ 0 := by
    linarith
  linarith

/-- Helper for Theorem 7.30: under the half-data-size regime, the benchmark gap
dominates every sub-benchmark deficit `β - m`. -/
lemma scaledSubbenchmark_gapControl
    (n m β : ℕ)
    (hmβ : m ≤ β)
    (hβ_half : 2 * β < n) :
    ((β - m : ℕ) : ℝ) < ((n - β : ℕ) : ℝ) := by
  -- Compare the benchmark deficit `β - m` against the denominator gap `n - β`
  -- after reducing everything to the strict half-data-size inequality.
  have hnat : β - m < n - β := by
    omega
  exact_mod_cast hnat

/-- Helper for Theorem 7.30: the explicit benchmark profile lies strictly
below the successor of its floor-defined benchmark index. -/
lemma optimalIndexProfile_lt_succ
    (b c p q σ : ℝ)
    (n : ℕ) :
    optimalIndexProfile b c p q σ n <
      ((optimalIndex b c p q σ n + 1 : ℕ) : ℝ) := by
  -- Unfold the owned floor definition once and apply the standard strict upper
  -- floor bound for nat floors.
  simpa [optimalIndex_def, optimalIndexProfile_def] using
    (Nat.lt_floor_add_one (optimalIndexProfile b c p q σ n))

/-- Helper for Theorem 7.30: every tail signal term above the floor-defined
benchmark is bounded by the benchmark noise scale. -/
lemma optimalIndex_tailSignalUpperBound
    (b c p q σ : ℝ)
    (n j : ℕ)
    (h_b : 0 < b)
    (h_c : 0 < c)
    (h_p : 1 < p)
    (h_q : 1 < q)
    (h_σ : 0 < σ)
    (hn : 0 < n)
    (h_tail : optimalIndex b c p q σ n < j) :
    b * c * (j : ℝ) ^ (-(p + q)) / (n : ℝ) ≤ (σ ^ 2) / (n : ℝ) ^ 2 := by
  have hpq_pos : 0 < p + q := by
    linarith
  have hprofile_pos : 0 < optimalIndexProfile b c p q σ n := by
    -- The benchmark profile is a product of positive factors at positive data
    -- size.
    rw [optimalIndexProfile_def]
    positivity
  have hj_pos_nat : 0 < j := lt_of_le_of_lt (Nat.zero_le _) h_tail
  have hj_pos : 0 < (j : ℝ) := by
    exact_mod_cast hj_pos_nat
  have hprofile_le_j : optimalIndexProfile b c p q σ n ≤ (j : ℝ) := by
    -- Bridge the floor-defined benchmark to the real profile, then compare the
    -- successor of the floor with the tail index `j`.
    have hprofile_lt :
        optimalIndexProfile b c p q σ n <
          ((optimalIndex b c p q σ n + 1 : ℕ) : ℝ) :=
      optimalIndexProfile_lt_succ b c p q σ n
    have hsucc_le_j : optimalIndex b c p q σ n + 1 ≤ j :=
      Nat.succ_le_of_lt h_tail
    exact le_trans (le_of_lt hprofile_lt) (by exact_mod_cast hsucc_le_j)
  have hpow_le :
      (optimalIndexProfile b c p q σ n) ^ (p + q) ≤ (j : ℝ) ^ (p + q) := by
    -- Move the tail comparison to the positive power `p + q`, where monotonicity
    -- is direct.
    exact Real.rpow_le_rpow hprofile_pos.le hprofile_le_j hpq_pos.le
  have hprofile_pow_pos :
      0 < (optimalIndexProfile b c p q σ n) ^ (p + q) := by
    exact Real.rpow_pos_of_pos hprofile_pos _
  have hnegpow_le :
      (j : ℝ) ^ (-(p + q)) ≤ (optimalIndexProfile b c p q σ n) ^ (-(p + q)) := by
    -- Negative powers are decreasing on positive reals, so the tail index `j`
    -- gives the smaller profile value.
    exact Real.rpow_le_rpow_of_nonpos hprofile_pos hprofile_le_j (by linarith)
  have hscale_nonneg : 0 ≤ b * c / (n : ℝ) := by
    positivity
  have hroot :
      b * c * (optimalIndexProfile b c p q σ n) ^ (-(p + q)) = (σ ^ 2) / (n : ℝ) :=
    optimalIndexProfile_root_eq b c p q σ n h_b h_c h_p h_q h_σ hn
  -- Normalize the benchmark tail term at the profile and then substitute the
  -- exact root identity once.
  calc
    b * c * (j : ℝ) ^ (-(p + q)) / (n : ℝ)
        = (b * c / (n : ℝ)) * (j : ℝ) ^ (-(p + q)) := by
            ring
    _ ≤ (b * c / (n : ℝ)) * (optimalIndexProfile b c p q σ n) ^ (-(p + q)) := by
          exact mul_le_mul_of_nonneg_left hnegpow_le hscale_nonneg
    _ = (b * c * (optimalIndexProfile b c p q σ n) ^ (-(p + q))) / (n : ℝ) := by
          ring
    _ = ((σ ^ 2) / (n : ℝ)) / (n : ℝ) := by
          rw [hroot]
    _ = (σ ^ 2) / ((n : ℝ) * (n : ℝ)) := by
          ring
    _ = (σ ^ 2) / (n : ℝ) ^ 2 := by
          simpa [pow_two]

/-- Helper for Theorem 7.30: every signal term at or below the floor-defined
benchmark dominates the benchmark noise scale. -/
lemma optimalIndex_initialSignalLowerBound
    (b c p q σ : ℝ)
    (n j : ℕ)
    (h_b : 0 < b)
    (h_c : 0 < c)
    (h_p : 1 < p)
    (h_q : 1 < q)
    (h_σ : 0 < σ)
    (hn : 0 < n)
    (hj_pos : 0 < j)
    (h_init : j ≤ optimalIndex b c p q σ n) :
    (σ ^ 2) / (n : ℝ) ^ 2 ≤ b * c * (j : ℝ) ^ (-(p + q)) / (n : ℝ) := by
  have hprofile_pos : 0 < optimalIndexProfile b c p q σ n := by
    -- The benchmark profile is a product of positive factors at positive data
    -- size.
    rw [optimalIndexProfile_def]
    positivity
  have hj_pos_real : 0 < (j : ℝ) := by
    exact_mod_cast hj_pos
  have hj_le_profile : (j : ℝ) ≤ optimalIndexProfile b c p q σ n := by
    have hbeta_le_profile :
        ((optimalIndex b c p q σ n : ℕ) : ℝ) ≤ optimalIndexProfile b c p q σ n := by
      -- The floor-defined benchmark is always below the explicit profile.
      rw [optimalIndex_def]
      exact Nat.floor_le hprofile_pos.le
    exact le_trans (by exact_mod_cast h_init) hbeta_le_profile
  have hnegpow_le :
      (optimalIndexProfile b c p q σ n) ^ (-(p + q)) ≤ (j : ℝ) ^ (-(p + q)) := by
    -- Negative powers reverse the benchmark-order comparison on positive reals.
    exact Real.rpow_le_rpow_of_nonpos hj_pos_real hj_le_profile (by linarith)
  have hscale_nonneg : 0 ≤ b * c / (n : ℝ) := by
    positivity
  have hroot :
      b * c * (optimalIndexProfile b c p q σ n) ^ (-(p + q)) = (σ ^ 2) / (n : ℝ) :=
    optimalIndexProfile_root_eq b c p q σ n h_b h_c h_p h_q h_σ hn
  -- Normalize the benchmark term at the explicit profile and then move back to
  -- the initial index `j` through the decreasing negative-power profile.
  calc
    (σ ^ 2) / (n : ℝ) ^ 2 = ((σ ^ 2) / (n : ℝ)) / (n : ℝ) := by
          ring
    _ = (b * c * (optimalIndexProfile b c p q σ n) ^ (-(p + q))) / (n : ℝ) := by
          rw [hroot]
    _ = (b * c / (n : ℝ)) * (optimalIndexProfile b c p q σ n) ^ (-(p + q)) := by
          ring
    _ ≤ (b * c / (n : ℝ)) * (j : ℝ) ^ (-(p + q)) := by
          exact mul_le_mul_of_nonneg_left hnegpow_le hscale_nonneg
    _ = b * c * (j : ℝ) ^ (-(p + q)) / (n : ℝ) := by
          ring

/-- Helper for Theorem 7.30: telescoping the residual numerator from a
sub-benchmark index `m` up to the benchmark floor produces a concrete cleared
lower bound with one `2 * σ^2` contribution per missing benchmark step. -/
lemma gcvSubbenchmark_residualGapLowerBound
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (K : ℕ → H →L[ℝ] F)
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
    (h_length : ∀ n, (S n).length = ⊤)
    (fTrue : H)
    (b c p q σ : ℝ)
    (η : ℕ → Ω → F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (n m : ℕ)
    (h_b : 0 < b)
    (h_c : 0 < c)
    (h_p : 1 < p)
    (h_q : 1 < q)
    (h_σ : 0 < σ)
    (h_noise_memLp : ∀ n, MeasureTheory.MemLp (η n) 2 μ)
    (h_noise_meanZero : ∀ n, ∫ ω, η n ω ∂μ = 0)
    (h_noise_modeVariance :
      ∀ n i,
        ∫ ω,
          (inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) i) : F) (η n ω)) ^ 2 ∂μ =
            σ ^ 2 / (n : ℝ))
    (h_singularDecay :
      ∀ n, (S n).HasAlgebraicSingularValueSquareDecay (h_length n) c p)
    (h_fourierDecay :
      ∀ n, (S n).HasAlgebraicFourierCoefficientSquareDecay (h_length n) fTrue b q)
    (h_tsvd : IsTsvdReconstructionFamily K S h_length Rtsvd)
    (hm_lt_beta : m < optimalIndex b c p q σ n)
    (h_optimalIndex_mem :
      optimalIndex b c p q σ n ∈ TsvdGcv.gcvAdmissibleIndexSet n) :
    2 * ((optimalIndex b c p q σ n - m : ℕ) : ℝ) * σ ^ 2 +
        ((n : ℝ) ^ 2) *
          expectedResidualObjective μ K Rtsvd fTrue η n (optimalIndex b c p q σ n) ≤
      ((n : ℝ) ^ 2) * expectedResidualObjective μ K Rtsvd fTrue η n m := by
  let β : ℕ := optimalIndex b c p q σ n
  let stepTerm : ℕ → ℝ := fun j ↦
    b * c * (j : ℝ) ^ (-(p + q)) / (n : ℝ) + (σ ^ 2) / (n : ℝ) ^ 2
  have hβ_lt : β < n := (TsvdGcv.mem_gcvAdmissibleIndexSet_iff n β).1 h_optimalIndex_mem |>.2
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le β) hβ_lt
  have htel :
      expectedResidualObjective μ K Rtsvd fTrue η n β +
          Finset.sum (Finset.Icc (m + 1) β) stepTerm ≤
        expectedResidualObjective μ K Rtsvd fTrue η n m :=
    expectedResidualObjective_telescope_lowerBound
      (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
      (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η)
      (Rtsvd := Rtsvd) (n := n) (m := m) (k := β)
      (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
      (h_noise_memLp := h_noise_memLp)
      (h_noise_meanZero := h_noise_meanZero)
      (h_noise_modeVariance := h_noise_modeVariance)
      (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
      (h_tsvd := h_tsvd) (Nat.le_of_lt hm_lt_beta) (Nat.le_of_lt hβ_lt)
  have hsum_lower :
      2 * ((β - m : ℕ) : ℝ) * σ ^ 2 ≤
        (n : ℝ) ^ 2 * Finset.sum (Finset.Icc (m + 1) β) stepTerm := by
    have hterm_lower :
        ∀ j ∈ Finset.Icc (m + 1) β, 2 * σ ^ 2 ≤ (n : ℝ) ^ 2 * stepTerm j := by
      intro j hj
      have hj_bounds : m + 1 ≤ j ∧ j ≤ β := by
        simpa [Finset.mem_Icc] using hj
      have hj_pos : 0 < j := lt_of_lt_of_le (Nat.succ_pos _) hj_bounds.1
      have hsignal :
          (σ ^ 2) / (n : ℝ) ^ 2 ≤ b * c * (j : ℝ) ^ (-(p + q)) / (n : ℝ) :=
        optimalIndex_initialSignalLowerBound
          (b := b) (c := c) (p := p) (q := q) (σ := σ) (n := n) (j := j)
          (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
          (hn := hn) (hj_pos := hj_pos) (h_init := by simpa [β] using hj_bounds.2)
      have hsignal_cleared :
          σ ^ 2 ≤ (n : ℝ) ^ 2 * (b * c * (j : ℝ) ^ (-(p + q)) / (n : ℝ)) := by
        calc
          σ ^ 2 = (n : ℝ) ^ 2 * ((σ ^ 2) / (n : ℝ) ^ 2) := by
                field_simp [pow_two, (show (n : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hn)]
          _ ≤ (n : ℝ) ^ 2 * (b * c * (j : ℝ) ^ (-(p + q)) / (n : ℝ)) := by
                exact mul_le_mul_of_nonneg_left hsignal (by positivity)
      have hnoise_cleared :
          σ ^ 2 = (n : ℝ) ^ 2 * ((σ ^ 2) / (n : ℝ) ^ 2) := by
        field_simp [pow_two, (show (n : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hn)]
      -- Each missing benchmark step contributes at least one signal-scale term
      -- and one noise-scale term after clearing the common `n^-2` factor.
      dsimp [stepTerm]
      nlinarith [hsignal_cleared, hnoise_cleared]
    have hsum_lower' :
        Finset.sum (Finset.Icc (m + 1) β) (fun _ ↦ 2 * σ ^ 2) ≤
          Finset.sum (Finset.Icc (m + 1) β) (fun j ↦ (n : ℝ) ^ 2 * stepTerm j) :=
      Finset.sum_le_sum fun j hj ↦ hterm_lower j hj
    have hconst :
        Finset.sum (Finset.Icc (m + 1) β) (fun _ ↦ 2 * σ ^ 2) =
          2 * ((β - m : ℕ) : ℝ) * σ ^ 2 := by
      have hcard : 1 + β - (m + 1) = β - m := by
        omega
      have hsum_const :
          Finset.sum (Finset.Icc (m + 1) β) (fun _ ↦ 2 * σ ^ 2) =
            (((Finset.Icc (m + 1) β).card : ℕ) : ℝ) * (2 * σ ^ 2) := by
        simpa [nsmul_eq_mul] using
          (Finset.sum_eq_card_nsmul
            (s := Finset.Icc (m + 1) β)
            (f := fun _ : ℕ ↦ 2 * σ ^ 2)
            (b := 2 * σ ^ 2)
            (fun _ _ ↦ rfl))
      have hcard_nat : (Finset.Icc (m + 1) β).card = β + 1 - (m + 1) := by
        simp
      rw [hsum_const, hcard_nat]
      simp [hcard, mul_comm, mul_left_comm, mul_assoc]
    have hscaled :
        Finset.sum (Finset.Icc (m + 1) β) (fun j ↦ (n : ℝ) ^ 2 * stepTerm j) =
          (n : ℝ) ^ 2 * Finset.sum (Finset.Icc (m + 1) β) stepTerm := by
      symm
      rw [Finset.mul_sum]
    simpa [hconst, hscaled] using hsum_lower'
  have htel_cleared :
      ((n : ℝ) ^ 2) * expectedResidualObjective μ K Rtsvd fTrue η n β +
          ((n : ℝ) ^ 2) * Finset.sum (Finset.Icc (m + 1) β) stepTerm ≤
        ((n : ℝ) ^ 2) * expectedResidualObjective μ K Rtsvd fTrue η n m := by
    have hmul := mul_le_mul_of_nonneg_left htel (show 0 ≤ (n : ℝ) ^ 2 by positivity)
    simpa [mul_add, add_mul, stepTerm, mul_assoc, mul_left_comm, mul_comm] using hmul
  -- Combine the cleared telescope with the per-step `2 * σ^2` lower bound.
  have hfinal :
      2 * ((β - m : ℕ) : ℝ) * σ ^ 2 +
          ((n : ℝ) ^ 2) * expectedResidualObjective μ K Rtsvd fTrue η n β ≤
        ((n : ℝ) ^ 2) * expectedResidualObjective μ K Rtsvd fTrue η n m := by
    nlinarith [htel_cleared, hsum_lower]
  simpa [β] using hfinal

/-- Helper for Theorem 7.30: every truncation level `k` below the benchmark
inherits the same cleared `2 * σ^2` residual-gap lower bound from any earlier
index `m`. -/
lemma subbenchmarkResidualGapLowerBound
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (K : ℕ → H →L[ℝ] F)
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
    (h_length : ∀ n, (S n).length = ⊤)
    (fTrue : H)
    (b c p q σ : ℝ)
    (η : ℕ → Ω → F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (n m k : ℕ)
    (h_b : 0 < b)
    (h_c : 0 < c)
    (h_p : 1 < p)
    (h_q : 1 < q)
    (h_σ : 0 < σ)
    (h_noise_memLp : ∀ n, MeasureTheory.MemLp (η n) 2 μ)
    (h_noise_meanZero : ∀ n, ∫ ω, η n ω ∂μ = 0)
    (h_noise_modeVariance :
      ∀ n i,
        ∫ ω,
          (inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) i) : F) (η n ω)) ^ 2 ∂μ =
            σ ^ 2 / (n : ℝ))
    (h_singularDecay :
      ∀ n, (S n).HasAlgebraicSingularValueSquareDecay (h_length n) c p)
    (h_fourierDecay :
      ∀ n, (S n).HasAlgebraicFourierCoefficientSquareDecay (h_length n) fTrue b q)
    (h_tsvd : IsTsvdReconstructionFamily K S h_length Rtsvd)
    (hmk : m ≤ k)
    (hkβ : k ≤ optimalIndex b c p q σ n)
    (h_optimalIndex_mem :
      optimalIndex b c p q σ n ∈ TsvdGcv.gcvAdmissibleIndexSet n) :
    2 * ((k - m : ℕ) : ℝ) * σ ^ 2 +
        ((n : ℝ) ^ 2) * expectedResidualObjective μ K Rtsvd fTrue η n k ≤
      ((n : ℝ) ^ 2) * expectedResidualObjective μ K Rtsvd fTrue η n m := by
  let β : ℕ := optimalIndex b c p q σ n
  let stepTerm : ℕ → ℝ := fun j ↦
    b * c * (j : ℝ) ^ (-(p + q)) / (n : ℝ) + (σ ^ 2) / (n : ℝ) ^ 2
  have hβ_lt : β < n :=
    (TsvdGcv.mem_gcvAdmissibleIndexSet_iff n β).1 h_optimalIndex_mem |>.2
  have hk_le_n : k ≤ n := le_trans hkβ (Nat.le_of_lt hβ_lt)
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le β) hβ_lt
  have htel :
      expectedResidualObjective μ K Rtsvd fTrue η n k +
          Finset.sum (Finset.Icc (m + 1) k) stepTerm ≤
        expectedResidualObjective μ K Rtsvd fTrue η n m :=
    expectedResidualObjective_telescope_lowerBound
      (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
      (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η)
      (Rtsvd := Rtsvd) (n := n) (m := m) (k := k)
      (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
      (h_noise_memLp := h_noise_memLp)
      (h_noise_meanZero := h_noise_meanZero)
      (h_noise_modeVariance := h_noise_modeVariance)
      (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
      (h_tsvd := h_tsvd) hmk hk_le_n
  have hsum_lower :
      2 * ((k - m : ℕ) : ℝ) * σ ^ 2 ≤
        (n : ℝ) ^ 2 * Finset.sum (Finset.Icc (m + 1) k) stepTerm := by
    have hterm_lower :
        ∀ j ∈ Finset.Icc (m + 1) k, 2 * σ ^ 2 ≤ (n : ℝ) ^ 2 * stepTerm j := by
      intro j hj
      have hj_bounds : m + 1 ≤ j ∧ j ≤ k := by
        simpa [Finset.mem_Icc] using hj
      have hj_pos : 0 < j := lt_of_lt_of_le (Nat.succ_pos _) hj_bounds.1
      have hsignal :
          (σ ^ 2) / (n : ℝ) ^ 2 ≤ b * c * (j : ℝ) ^ (-(p + q)) / (n : ℝ) :=
        optimalIndex_initialSignalLowerBound
          (b := b) (c := c) (p := p) (q := q) (σ := σ) (n := n) (j := j)
          (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
          (hn := hn) (hj_pos := hj_pos)
          (h_init := le_trans hj_bounds.2 hkβ)
      have hsignal_cleared :
          σ ^ 2 ≤ (n : ℝ) ^ 2 * (b * c * (j : ℝ) ^ (-(p + q)) / (n : ℝ)) := by
        calc
          σ ^ 2 = (n : ℝ) ^ 2 * ((σ ^ 2) / (n : ℝ) ^ 2) := by
                field_simp [pow_two, (show (n : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hn)]
          _ ≤ (n : ℝ) ^ 2 * (b * c * (j : ℝ) ^ (-(p + q)) / (n : ℝ)) := by
                exact mul_le_mul_of_nonneg_left hsignal (by positivity)
      have hnoise_cleared :
          σ ^ 2 = (n : ℝ) ^ 2 * ((σ ^ 2) / (n : ℝ) ^ 2) := by
        field_simp [pow_two, (show (n : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hn)]
      -- Each sub-benchmark step up to `k` still contributes one signal-scale
      -- term and one noise-scale term after clearing the common `n^-2` factor.
      dsimp [stepTerm]
      nlinarith [hsignal_cleared, hnoise_cleared]
    have hsum_lower' :
        Finset.sum (Finset.Icc (m + 1) k) (fun _ ↦ 2 * σ ^ 2) ≤
          Finset.sum (Finset.Icc (m + 1) k) (fun j ↦ (n : ℝ) ^ 2 * stepTerm j) :=
      Finset.sum_le_sum fun j hj ↦ hterm_lower j hj
    have hconst :
        Finset.sum (Finset.Icc (m + 1) k) (fun _ ↦ 2 * σ ^ 2) =
          2 * ((k - m : ℕ) : ℝ) * σ ^ 2 := by
      have hcard : 1 + k - (m + 1) = k - m := by
        omega
      have hsum_const :
          Finset.sum (Finset.Icc (m + 1) k) (fun _ ↦ 2 * σ ^ 2) =
            (((Finset.Icc (m + 1) k).card : ℕ) : ℝ) * (2 * σ ^ 2) := by
        simpa [nsmul_eq_mul] using
          (Finset.sum_eq_card_nsmul
            (s := Finset.Icc (m + 1) k)
            (f := fun _ : ℕ ↦ 2 * σ ^ 2)
            (b := 2 * σ ^ 2)
            (fun _ _ ↦ rfl))
      have hcard_nat : (Finset.Icc (m + 1) k).card = k + 1 - (m + 1) := by
        simp
      rw [hsum_const, hcard_nat]
      simp [hcard, mul_comm, mul_left_comm, mul_assoc]
    have hscaled :
        Finset.sum (Finset.Icc (m + 1) k) (fun j ↦ (n : ℝ) ^ 2 * stepTerm j) =
          (n : ℝ) ^ 2 * Finset.sum (Finset.Icc (m + 1) k) stepTerm := by
      symm
      rw [Finset.mul_sum]
    simpa [hconst, hscaled] using hsum_lower'
  have htel_cleared :
      ((n : ℝ) ^ 2) * expectedResidualObjective μ K Rtsvd fTrue η n k +
          ((n : ℝ) ^ 2) * Finset.sum (Finset.Icc (m + 1) k) stepTerm ≤
        ((n : ℝ) ^ 2) * expectedResidualObjective μ K Rtsvd fTrue η n m := by
    have hmul := mul_le_mul_of_nonneg_left htel (show 0 ≤ (n : ℝ) ^ 2 by positivity)
    simpa [mul_add, add_mul, stepTerm, mul_assoc, mul_left_comm, mul_comm] using hmul
  -- Combine the cleared telescope with the per-step `2 * σ^2` lower bound.
  nlinarith [htel_cleared, hsum_lower]

/-- Helper for Theorem 7.30: at the benchmark index, the cleared residual
numerator already contains the full denominator-gap noise window. -/
lemma optimalIndex_residualGapNoiseLowerBound
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (K : ℕ → H →L[ℝ] F)
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
    (h_length : ∀ n, (S n).length = ⊤)
    (fTrue : H)
    (b c p q σ : ℝ)
    (η : ℕ → Ω → F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (n : ℕ)
    (h_b : 0 < b)
    (h_c : 0 < c)
    (h_p : 1 < p)
    (h_q : 1 < q)
    (h_σ : 0 < σ)
    (h_noise_memLp : ∀ n, MeasureTheory.MemLp (η n) 2 μ)
    (h_noise_meanZero : ∀ n, ∫ ω, η n ω ∂μ = 0)
    (h_noise_modeVariance :
      ∀ n i,
        ∫ ω,
          (inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) i) : F) (η n ω)) ^ 2 ∂μ =
            σ ^ 2 / (n : ℝ))
    (h_singularDecay :
      ∀ n, (S n).HasAlgebraicSingularValueSquareDecay (h_length n) c p)
    (h_fourierDecay :
      ∀ n, (S n).HasAlgebraicFourierCoefficientSquareDecay (h_length n) fTrue b q)
    (h_tsvd : IsTsvdReconstructionFamily K S h_length Rtsvd)
    (h_optimalIndex_mem :
      optimalIndex b c p q σ n ∈ TsvdGcv.gcvAdmissibleIndexSet n) :
    ((n - optimalIndex b c p q σ n : ℕ) : ℝ) * σ ^ 2 ≤
      (n : ℝ) ^ 2 * expectedResidualObjective μ K Rtsvd fTrue η n (optimalIndex b c p q σ n) := by
  have hβ_lt :
      optimalIndex b c p q σ n < n :=
    (TsvdGcv.mem_gcvAdmissibleIndexSet_iff n (optimalIndex b c p q σ n)).1 h_optimalIndex_mem |>.2
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hβ_lt
  have hnoise_window :
      (((n - optimalIndex b c p q σ n : ℕ) : ℝ) * σ ^ 2) / (n : ℝ) ^ 2 ≤
        expectedResidualObjective μ K Rtsvd fTrue η n (optimalIndex b c p q σ n) :=
    expectedResidualObjective_noiseWindow_lowerBound
      (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
      (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η)
      (Rtsvd := Rtsvd) (n := n) (m := optimalIndex b c p q σ n)
      (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
      (h_noise_memLp := h_noise_memLp)
      (h_noise_meanZero := h_noise_meanZero)
      (h_noise_modeVariance := h_noise_modeVariance)
      (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
      (h_tsvd := h_tsvd) hβ_lt
  have hmul :=
    mul_le_mul_of_nonneg_left hnoise_window (show 0 ≤ (n : ℝ) ^ 2 by positivity)
  -- Clear the common `n^-2` factor once so later benchmark-gap arguments can
  -- compare against the numerator in its stable spelling.
  have htmp := hmul
  field_simp [pow_two, (show (n : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hn)] at htmp
  simpa [mul_comm, mul_left_comm, mul_assoc] using htmp

/-- Helper for Theorem 7.30: the benchmark noise window already forces the
benchmark objective above the reciprocal gap scale, so any candidate route that
would require a strictly smaller upper bound is algebraically impossible. -/
lemma benchmarkObjectiveUpperImpossible_of_noiseWindow
    {a d σ eβ : ℝ}
    (ha : 0 < a)
    (hd : 0 < d)
    (hnoise : σ ^ 2 ≤ a * eβ) :
    ¬ ((2 * a + d) * eβ < 2 * σ ^ 2) := by
  -- The benchmark noise floor gives `a * eβ ≥ σ²`; multiplying it by the
  -- strictly larger factor `2 + d / a` rules out the stronger upper bound.
  have heβ_nonneg : 0 ≤ eβ := by
    nlinarith
  have hge :
      2 * σ ^ 2 ≤ (2 * a + d) * eβ := by
    nlinarith
  exact not_lt_of_ge hge

/-- Helper for Theorem 7.30: the buffered left-scaled comparison index attached
to a benchmark `β` is the floor of the interior scale `(1 - δ / 2) * β`. -/
noncomputable def leftScaledComparisonIndex
    (δ : ℝ)
    (β : ℕ) : ℕ :=
  Nat.floor ((1 - δ / 2) * (β : ℝ))

/-- Helper for Theorem 7.30: for `0 < δ < 1`, the buffered left-scaled
comparison index stays strictly below the benchmark `β`. -/
lemma leftScaledComparisonIndex_lt
    {δ : ℝ}
    {β : ℕ}
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (hβ_pos : 0 < (β : ℝ)) :
    leftScaledComparisonIndex δ β < β := by
  let x : ℝ := (1 - δ / 2) * (β : ℝ)
  have hscale_nonneg : 0 ≤ 1 - δ / 2 := by
    linarith
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    positivity
  have hfloor_le : (leftScaledComparisonIndex δ β : ℝ) ≤ x := by
    simpa [leftScaledComparisonIndex, x] using Nat.floor_le hx_nonneg
  have hx_lt_beta : x < (β : ℝ) := by
    dsimp [x]
    nlinarith
  -- Compare the floor directly to the benchmark in the real-valued spelling,
  -- then cast the strict inequality back to naturals.
  exact_mod_cast (lt_of_le_of_lt hfloor_le hx_lt_beta)

/-- Helper for Theorem 7.30: if `m` lies below `(1 - δ) * β` and the benchmark
gap satisfies `(δ / 2) * β ≥ 1`, then the buffered left-scaled comparison
index lies strictly to the right of `m`. -/
lemma lt_leftScaledComparisonIndex_of_scaledUpperBound
    {δ : ℝ}
    {m β : ℕ}
    (hm_scaled : (m : ℝ) ≤ (1 - δ) * (β : ℝ))
    (h_gap_large : 1 ≤ (δ / 2) * (β : ℝ)) :
    m < leftScaledComparisonIndex δ β := by
  let x : ℝ := (1 - δ / 2) * (β : ℝ)
  have hbuffer :
      (1 - δ) * (β : ℝ) ≤ x - 1 := by
    dsimp [x]
    linarith
  have hx_floor :
      x - 1 < (leftScaledComparisonIndex δ β : ℝ) := by
    have hlt :
        x < (leftScaledComparisonIndex δ β : ℝ) + 1 := by
      simpa [leftScaledComparisonIndex, x] using Nat.lt_floor_add_one x
    linarith
  -- The buffered floor loses at most one unit, and `h_gap_large` gives exactly
  -- the one-unit margin needed to stay strictly above `m`.
  have hm_lt_floor : (m : ℝ) < leftScaledComparisonIndex δ β := by
    exact lt_of_le_of_lt (le_trans hm_scaled hbuffer) hx_floor
  exact_mod_cast hm_lt_floor

/-- Helper for Theorem 7.30: once the benchmark index is large enough, the
buffered left-scaled comparison index is eventually GCV-admissible and lies
strictly between every admissible `m ≤ (1 - δ) * β_n` and the benchmark
`β_n = optimalIndex b c p q σ n`. -/
lemma leftScaledComparisonIndex_eventually_mem_and_between
    (b c p q σ δ : ℝ)
    (h_b : 0 < b)
    (h_c : 0 < c)
    (h_p : 1 < p)
    (h_q : 1 < q)
    (h_σ : 0 < σ)
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (h_optimalIndex_mem :
      ∀ᶠ n in Filter.atTop, optimalIndex b c p q σ n ∈ TsvdGcv.gcvAdmissibleIndexSet n) :
    ∀ᶠ n in Filter.atTop,
      ∀ {m : ℕ}, m ∈ TsvdGcv.gcvAdmissibleIndexSet n →
        (m : ℝ) ≤ (1 - δ) * (optimalIndex b c p q σ n : ℝ) →
        let k := leftScaledComparisonIndex δ (optimalIndex b c p q σ n)
        k ∈ TsvdGcv.gcvAdmissibleIndexSet n ∧
          m < k ∧
          k < optimalIndex b c p q σ n ∧
          0 < (optimalIndex b c p q σ n : ℝ) - k := by
  have hβ_large :
      ∀ᶠ n in Filter.atTop, (2 / δ : ℝ) ≤ (optimalIndex b c p q σ n : ℝ) :=
    (optimalIndex_tendstoAtTop_local b c p q σ h_b h_c h_p h_q h_σ).eventually
      (Filter.Ici_mem_atTop (2 / δ : ℝ))
  filter_upwards [h_optimalIndex_mem, hβ_large] with n hβ_mem hβ_large
  intro m hm_mem hm_scaled
  let β : ℕ := optimalIndex b c p q σ n
  let k : ℕ := leftScaledComparisonIndex δ β
  have hm_lt : m < n := (TsvdGcv.mem_gcvAdmissibleIndexSet_iff n m).1 hm_mem |>.2
  have hβ_lt : β < n := (TsvdGcv.mem_gcvAdmissibleIndexSet_iff n β).1 hβ_mem |>.2
  have hβ_pos : 0 < (β : ℝ) := by
    have hthreshold_pos : 0 < (2 / δ : ℝ) := by
      positivity
    exact lt_of_lt_of_le hthreshold_pos hβ_large
  have h_gap_large : 1 ≤ (δ / 2) * (β : ℝ) := by
    have hmul :
        (δ / 2) * (2 / δ : ℝ) ≤ (δ / 2) * (β : ℝ) := by
      exact mul_le_mul_of_nonneg_left hβ_large (by positivity : 0 ≤ δ / 2)
    have hunit : (δ / 2) * (2 / δ : ℝ) = 1 := by
      field_simp [hδ_pos.ne']
    linarith
  have hk_lt_beta : k < β :=
    leftScaledComparisonIndex_lt hδ_pos hδ_lt_one hβ_pos
  have hm_lt_k : m < k :=
    lt_leftScaledComparisonIndex_of_scaledUpperBound
      (δ := δ) (m := m) (β := β) hm_scaled h_gap_large
  have hk_mem : k ∈ TsvdGcv.gcvAdmissibleIndexSet n := by
    -- The buffered comparison index inherits admissibility from the benchmark
    -- because it stays strictly below `β < n`.
    rw [TsvdGcv.mem_gcvAdmissibleIndexSet_iff]
    refine ⟨⟨Nat.zero_le _, Nat.le_of_lt (lt_trans hk_lt_beta hβ_lt)⟩, ?_⟩
    exact lt_trans hk_lt_beta hβ_lt
  have hk_lt_beta_real : (k : ℝ) < (β : ℝ) := by
    exact_mod_cast hk_lt_beta
  -- Collect the admissibility and order information into the exact interface
  -- needed by the later strict-comparison proof.
  refine ⟨hk_mem, hm_lt_k, hk_lt_beta, ?_⟩
  exact sub_pos.mpr hk_lt_beta_real

/-- Helper for Theorem 7.30: every singular-mode signal term up to the buffered
left-scaled comparison index carries a fixed multiplicative gain over the
benchmark noise scale. -/
lemma leftScaledComparison_stepGainLowerBound
    (b c p q σ δ : ℝ)
    (n j : ℕ)
    (h_b : 0 < b)
    (h_c : 0 < c)
    (h_p : 1 < p)
    (h_q : 1 < q)
    (h_σ : 0 < σ)
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (hn : 0 < n)
    (hj_pos : 0 < j)
    (hj_le :
      j ≤ leftScaledComparisonIndex δ (optimalIndex b c p q σ n)) :
    (1 - δ / 2) ^ (-(p + q)) * σ ^ 2 ≤
      (n : ℝ) ^ 2 * (b * c * (j : ℝ) ^ (-(p + q)) / (n : ℝ)) := by
  let β : ℕ := optimalIndex b c p q σ n
  let profile : ℝ := optimalIndexProfile b c p q σ n
  have hscale_pos : 0 < 1 - δ / 2 := by
    linarith
  have hscale_nonneg : 0 ≤ 1 - δ / 2 := hscale_pos.le
  have hprofile_pos : 0 < profile := by
    -- The benchmark profile is positive at positive data size.
    dsimp [profile]
    rw [optimalIndexProfile_def]
    positivity
  have hprofile_nonneg : 0 ≤ profile := hprofile_pos.le
  have hβ_le_profile : (β : ℝ) ≤ profile := by
    -- The floor-defined benchmark lies below its explicit profile.
    dsimp [β, profile]
    rw [optimalIndex_def]
    exact Nat.floor_le hprofile_nonneg
  have hk_le_scaledβ :
      (leftScaledComparisonIndex δ β : ℝ) ≤ (1 - δ / 2) * (β : ℝ) := by
    -- The buffered comparison index is the floor of the scaled benchmark.
    have hx_nonneg : 0 ≤ (1 - δ / 2) * (β : ℝ) := by
      positivity
    simpa [leftScaledComparisonIndex] using
      (Nat.floor_le hx_nonneg : (Nat.floor ((1 - δ / 2) * (β : ℝ)) : ℝ) ≤ _)
  have hj_real_pos : 0 < (j : ℝ) := by
    exact_mod_cast hj_pos
  have hj_le_scaledProfile : (j : ℝ) ≤ (1 - δ / 2) * profile := by
    -- Move the nat inequality `j ≤ kδ` through the floor bound and then from
    -- the floor-defined benchmark to the explicit profile.
    calc
      (j : ℝ) ≤ leftScaledComparisonIndex δ β := by exact_mod_cast hj_le
      _ ≤ (1 - δ / 2) * (β : ℝ) := hk_le_scaledβ
      _ ≤ (1 - δ / 2) * profile := by
            exact mul_le_mul_of_nonneg_left hβ_le_profile hscale_nonneg
  have hscaled_negpow_le :
      ((1 - δ / 2) * profile) ^ (-(p + q)) ≤ (j : ℝ) ^ (-(p + q)) := by
    -- Negative powers are decreasing, so the buffered window retains a fixed
    -- fraction of the benchmark signal scale.
    exact Real.rpow_le_rpow_of_nonpos hj_real_pos hj_le_scaledProfile (by linarith)
  have hroot :
      b * c * profile ^ (-(p + q)) = (σ ^ 2) / (n : ℝ) :=
    optimalIndexProfile_root_eq b c p q σ n h_b h_c h_p h_q h_σ hn
  have hscaledProfile_signal :
      (1 - δ / 2) ^ (-(p + q)) * σ ^ 2 =
        (n : ℝ) * (b * c * (((1 - δ / 2) * profile) ^ (-(p + q)))) := by
    have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    calc
      (1 - δ / 2) ^ (-(p + q)) * σ ^ 2
          = (1 - δ / 2) ^ (-(p + q)) *
              ((n : ℝ) * (b * c * profile ^ (-(p + q)))) := by
                rw [hroot]
                field_simp [hn_ne]
      _ = (n : ℝ) *
            (b * c * ((1 - δ / 2) ^ (-(p + q)) * profile ^ (-(p + q)))) := by
              ring
      _ = (n : ℝ) * (b * c * (((1 - δ / 2) * profile) ^ (-(p + q)))) := by
            congr 3
            symm
            rw [Real.mul_rpow hscale_nonneg hprofile_nonneg]
  have hcoeff_nonneg : 0 ≤ (n : ℝ) * (b * c) := by
    positivity
  have htarget :
      (n : ℝ) * (b * c * (j : ℝ) ^ (-(p + q))) =
        (n : ℝ) ^ 2 * (b * c * (j : ℝ) ^ (-(p + q)) / (n : ℝ)) := by
    have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    field_simp [hn_ne]
  -- Normalize the buffered gain at the explicit profile, then use monotonicity
  -- on the whole left-scaled window before restoring the cleared `n^2` form.
  calc
    (1 - δ / 2) ^ (-(p + q)) * σ ^ 2
        = (n : ℝ) * (b * c * (((1 - δ / 2) * profile) ^ (-(p + q)))) :=
          hscaledProfile_signal
    _ ≤ (n : ℝ) * (b * c * (j : ℝ) ^ (-(p + q))) := by
          have hbc_nonneg : 0 ≤ b * c := by positivity
          have hinner :
              b * c * (((1 - δ / 2) * profile) ^ (-(p + q))) ≤
                b * c * (j : ℝ) ^ (-(p + q)) :=
            mul_le_mul_of_nonneg_left hscaled_negpow_le hbc_nonneg
          exact mul_le_mul_of_nonneg_left hinner (by positivity : 0 ≤ (n : ℝ))
    _ = (n : ℝ) ^ 2 * (b * c * (j : ℝ) ^ (-(p + q)) / (n : ℝ)) := htarget

/-- Helper for Theorem 7.30: telescoping from an admissible index `m` up to the
buffered left-scaled comparison index yields a cleared residual gap with the
sharpened coefficient `1 + (1 - δ / 2) ^ (-(p + q))`. -/
lemma leftScaledComparison_residualGapLowerBoundSharp
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (K : ℕ → H →L[ℝ] F)
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
    (h_length : ∀ n, (S n).length = ⊤)
    (fTrue : H)
    (b c p q σ δ : ℝ)
    (η : ℕ → Ω → F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (n m : ℕ)
    (h_b : 0 < b)
    (h_c : 0 < c)
    (h_p : 1 < p)
    (h_q : 1 < q)
    (h_σ : 0 < σ)
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (h_noise_memLp : ∀ n, MeasureTheory.MemLp (η n) 2 μ)
    (h_noise_meanZero : ∀ n, ∫ ω, η n ω ∂μ = 0)
    (h_noise_modeVariance :
      ∀ n i,
        ∫ ω,
          (inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) i) : F) (η n ω)) ^ 2 ∂μ =
            σ ^ 2 / (n : ℝ))
    (h_singularDecay :
      ∀ n, (S n).HasAlgebraicSingularValueSquareDecay (h_length n) c p)
    (h_fourierDecay :
      ∀ n, (S n).HasAlgebraicFourierCoefficientSquareDecay (h_length n) fTrue b q)
    (h_tsvd : IsTsvdReconstructionFamily K S h_length Rtsvd)
    (hm_lt_k :
      m < leftScaledComparisonIndex δ (optimalIndex b c p q σ n))
    (h_optimalIndex_mem :
      optimalIndex b c p q σ n ∈ TsvdGcv.gcvAdmissibleIndexSet n) :
    let k := leftScaledComparisonIndex δ (optimalIndex b c p q σ n)
    (1 + (1 - δ / 2) ^ (-(p + q))) * ((k - m : ℕ) : ℝ) * σ ^ 2 +
        ((n : ℝ) ^ 2) * expectedResidualObjective μ K Rtsvd fTrue η n k ≤
      ((n : ℝ) ^ 2) * expectedResidualObjective μ K Rtsvd fTrue η n m := by
  let β : ℕ := optimalIndex b c p q σ n
  let k : ℕ := leftScaledComparisonIndex δ β
  let gainδ : ℝ := 1 + (1 - δ / 2) ^ (-(p + q))
  let stepTerm : ℕ → ℝ := fun j ↦
    b * c * (j : ℝ) ^ (-(p + q)) / (n : ℝ) + (σ ^ 2) / (n : ℝ) ^ 2
  have hβ_lt : β < n :=
    (TsvdGcv.mem_gcvAdmissibleIndexSet_iff n β).1 h_optimalIndex_mem |>.2
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le β) hβ_lt
  have hmk : m ≤ k := Nat.le_of_lt hm_lt_k
  have hk_pos : 0 < k := lt_of_le_of_lt (Nat.zero_le m) hm_lt_k
  have hβ_pos_nat : 0 < β := by
    by_contra hβ_nonpos
    have hβ_zero : β = 0 := Nat.eq_zero_of_not_pos hβ_nonpos
    have hk_zero : k = 0 := by
      simp [k, β, hβ_zero, leftScaledComparisonIndex]
    exact hk_pos.ne' hk_zero
  have hβ_pos : 0 < (β : ℝ) := by
    exact_mod_cast hβ_pos_nat
  have hkβ : k ≤ β := Nat.le_of_lt (leftScaledComparisonIndex_lt hδ_pos hδ_lt_one hβ_pos)
  have hk_le_n : k ≤ n := le_trans hkβ (Nat.le_of_lt hβ_lt)
  have htel :
      expectedResidualObjective μ K Rtsvd fTrue η n k +
          Finset.sum (Finset.Icc (m + 1) k) stepTerm ≤
        expectedResidualObjective μ K Rtsvd fTrue η n m :=
    expectedResidualObjective_telescope_lowerBound
      (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
      (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η)
      (Rtsvd := Rtsvd) (n := n) (m := m) (k := k)
      (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
      (h_noise_memLp := h_noise_memLp)
      (h_noise_meanZero := h_noise_meanZero)
      (h_noise_modeVariance := h_noise_modeVariance)
      (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
      (h_tsvd := h_tsvd) hmk hk_le_n
  have hsum_lower :
      gainδ * ((k - m : ℕ) : ℝ) * σ ^ 2 ≤
        (n : ℝ) ^ 2 * Finset.sum (Finset.Icc (m + 1) k) stepTerm := by
    have hterm_lower :
        ∀ j ∈ Finset.Icc (m + 1) k, gainδ * σ ^ 2 ≤ (n : ℝ) ^ 2 * stepTerm j := by
      intro j hj
      have hj_bounds : m + 1 ≤ j ∧ j ≤ k := by
        simpa [Finset.mem_Icc] using hj
      have hj_pos : 0 < j := lt_of_lt_of_le (Nat.succ_pos _) hj_bounds.1
      have hsignal_cleared :
          (1 - δ / 2) ^ (-(p + q)) * σ ^ 2 ≤
            (n : ℝ) ^ 2 * (b * c * (j : ℝ) ^ (-(p + q)) / (n : ℝ)) :=
        leftScaledComparison_stepGainLowerBound
          (b := b) (c := c) (p := p) (q := q) (σ := σ) (δ := δ)
          (n := n) (j := j) (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q)
          (h_σ := h_σ) (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
          (hn := hn) (hj_pos := hj_pos) (hj_le := by
            simpa [k, β] using hj_bounds.2)
      have hnoise_cleared :
          σ ^ 2 = (n : ℝ) ^ 2 * ((σ ^ 2) / (n : ℝ) ^ 2) := by
        field_simp [pow_two, (show (n : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hn)]
      -- Each buffered comparison step contributes the sharpened signal gain
      -- plus the usual noise-window term after clearing `n^-2`.
      dsimp [gainδ, stepTerm]
      nlinarith [hsignal_cleared, hnoise_cleared]
    have hsum_lower' :
        Finset.sum (Finset.Icc (m + 1) k) (fun _ ↦ gainδ * σ ^ 2) ≤
          Finset.sum (Finset.Icc (m + 1) k) (fun j ↦ (n : ℝ) ^ 2 * stepTerm j) :=
      Finset.sum_le_sum fun j hj ↦ hterm_lower j hj
    have hconst :
        Finset.sum (Finset.Icc (m + 1) k) (fun _ ↦ gainδ * σ ^ 2) =
          gainδ * ((k - m : ℕ) : ℝ) * σ ^ 2 := by
      have hcard : 1 + k - (m + 1) = k - m := by
        omega
      have hsum_const :
          Finset.sum (Finset.Icc (m + 1) k) (fun _ ↦ gainδ * σ ^ 2) =
            (((Finset.Icc (m + 1) k).card : ℕ) : ℝ) * (gainδ * σ ^ 2) := by
        simpa [nsmul_eq_mul] using
          (Finset.sum_eq_card_nsmul
            (s := Finset.Icc (m + 1) k)
            (f := fun _ : ℕ ↦ gainδ * σ ^ 2)
            (b := gainδ * σ ^ 2)
            (fun _ _ ↦ rfl))
      have hcard_nat : (Finset.Icc (m + 1) k).card = k + 1 - (m + 1) := by
        simp
      rw [hsum_const, hcard_nat]
      simp [hcard, gainδ, mul_assoc, mul_comm, mul_left_comm]
    have hscaled :
        Finset.sum (Finset.Icc (m + 1) k) (fun j ↦ (n : ℝ) ^ 2 * stepTerm j) =
          (n : ℝ) ^ 2 * Finset.sum (Finset.Icc (m + 1) k) stepTerm := by
      symm
      rw [Finset.mul_sum]
    simpa [hconst, hscaled] using hsum_lower'
  have htel_cleared :
      ((n : ℝ) ^ 2) * expectedResidualObjective μ K Rtsvd fTrue η n k +
          ((n : ℝ) ^ 2) * Finset.sum (Finset.Icc (m + 1) k) stepTerm ≤
        ((n : ℝ) ^ 2) * expectedResidualObjective μ K Rtsvd fTrue η n m := by
    have hmul := mul_le_mul_of_nonneg_left htel (show 0 ≤ (n : ℝ) ^ 2 by positivity)
    simpa [mul_add, add_mul, stepTerm, mul_assoc, mul_left_comm, mul_comm] using hmul
  -- Combine the cleared telescope with the sharpened buffered-step gain.
  dsimp [k, gainδ]
  nlinarith [htel_cleared, hsum_lower]

/-- Helper for Theorem 7.30: a buffered residual upper envelope and a small
step-to-gap ratio are enough to turn a cleared residual-gap inequality into a
strict GCV quotient comparison. -/
lemma strictGcvComparison_of_gapResidualBounds
    {resk resm gapk d gain C θ σ : ℝ}
    (hσ_pos : 0 < σ)
    (hd_pos : 0 < d)
    (hgapk_pos : 0 < gapk)
    (hresk_nonneg : 0 ≤ resk)
    (hθ_nonneg : 0 ≤ θ)
    (h_upper : resk ≤ C * gapk * σ ^ 2)
    (h_gap : gain * d * σ ^ 2 + resk ≤ resm)
    (h_stepRatio : d ≤ θ * gapk)
    (h_coeff : C * (2 + θ) < gain) :
    resk / gapk ^ 2 < resm / (gapk + d) ^ 2 := by
  have hratio_bound : 2 * gapk + d ≤ (2 + θ) * gapk := by
    -- The short comparison window is controlled by the denominator gap through
    -- the explicit ratio parameter `θ`.
    nlinarith
  have hC_nonneg : 0 ≤ C := by
    -- The upper envelope can only hold with a nonnegative coefficient because
    -- both the residual numerator and the noise-window scale are nonnegative.
    by_contra hC_neg
    have hscale_pos : 0 < gapk * σ ^ 2 := by positivity
    nlinarith [h_upper, hresk_nonneg, hscale_pos]
  have hresk_mul :
      resk * (2 * gapk + d) ≤ C * gapk * σ ^ 2 * ((2 + θ) * gapk) := by
    have h1 : resk * (2 * gapk + d) ≤ (C * gapk * σ ^ 2) * (2 * gapk + d) := by
      gcongr
    have h2 :
        (C * gapk * σ ^ 2) * (2 * gapk + d) ≤
          (C * gapk * σ ^ 2) * ((2 + θ) * gapk) := by
      gcongr
    exact le_trans h1 h2
  have hσsq_gap_pos : 0 < σ ^ 2 * gapk ^ 2 := by positivity
  have hcoeff_scaled :
      C * (2 + θ) * (σ ^ 2 * gapk ^ 2) < gain * (σ ^ 2 * gapk ^ 2) := by
    exact mul_lt_mul_of_pos_right h_coeff hσsq_gap_pos
  have hstrict_core :
      resk * (2 * gapk + d) < gain * σ ^ 2 * gapk ^ 2 := by
    have htmp : resk * (2 * gapk + d) ≤ C * (2 + θ) * (σ ^ 2 * gapk ^ 2) := by
      nlinarith [hresk_mul]
    exact lt_of_le_of_lt htmp <| by
      nlinarith [hcoeff_scaled]
  have hstrict_term :
      resk * (d * (2 * gapk + d)) < gain * d * σ ^ 2 * gapk ^ 2 := by
    -- Multiply the one-step strict gain by the positive comparison-window
    -- length `d`.
    have := mul_lt_mul_of_pos_left hstrict_core hd_pos
    nlinarith
  have hgap_scaled :
      gain * d * σ ^ 2 * gapk ^ 2 + resk * gapk ^ 2 ≤ resm * gapk ^ 2 := by
    -- Clear the common denominator `gapk²` on the residual-gap inequality.
    have hmul := mul_le_mul_of_nonneg_right h_gap (show 0 ≤ gapk ^ 2 by positivity)
    nlinarith
  have hnum : resk * (gapk + d) ^ 2 < resm * gapk ^ 2 := by
    have hlt :
        resk * gapk ^ 2 + resk * (d * (2 * gapk + d)) <
          resk * gapk ^ 2 + gain * d * σ ^ 2 * gapk ^ 2 := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_lt_add_left hstrict_term (resk * gapk ^ 2)
    have hle :
        resk * gapk ^ 2 + gain * d * σ ^ 2 * gapk ^ 2 ≤ resm * gapk ^ 2 := by
      nlinarith [hgap_scaled]
    have hcombine := lt_of_lt_of_le hlt hle
    have hexpand :
        resk * (gapk + d) ^ 2 =
          resk * gapk ^ 2 + resk * (d * (2 * gapk + d)) := by
      ring
    rw [hexpand]
    exact hcombine
  have hgoal : resk / gapk ^ 2 < resm / (gapk + d) ^ 2 := by
    -- A final denominator clearing turns the numerator comparison into the
    -- desired strict quotient comparison.
    field_simp [pow_two, hgapk_pos.ne', (show gapk + d ≠ 0 by linarith)]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hnum
  exact hgoal

/-- Helper for Theorem 7.30: clearing the telescope from `k` up to the top
index `n` separates the residual numerator into the explicit noise window, the
finite signal tail on `Finset.Icc (k + 1) n`, and the terminal residual at
full truncation. -/
lemma residualToDataSize_eq_noiseWindow_addSignalTail
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (K : ℕ → H →L[ℝ] F)
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
    (h_length : ∀ n, (S n).length = ⊤)
    (fTrue : H)
    (b c p q σ : ℝ)
    (η : ℕ → Ω → F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (n k : ℕ)
    (h_b : 0 < b)
    (h_c : 0 < c)
    (h_p : 1 < p)
    (h_q : 1 < q)
    (h_σ : 0 < σ)
    (h_noise_memLp : ∀ n, MeasureTheory.MemLp (η n) 2 μ)
    (h_noise_meanZero : ∀ n, ∫ ω, η n ω ∂μ = 0)
    (h_noise_modeVariance :
      ∀ n i,
        ∫ ω,
          (inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) i) : F) (η n ω)) ^ 2 ∂μ =
            σ ^ 2 / (n : ℝ))
    (h_singularDecay :
      ∀ n, (S n).HasAlgebraicSingularValueSquareDecay (h_length n) c p)
    (h_fourierDecay :
      ∀ n, (S n).HasAlgebraicFourierCoefficientSquareDecay (h_length n) fTrue b q)
    (h_tsvd : IsTsvdReconstructionFamily K S h_length Rtsvd)
    (hk_le_n : k ≤ n) :
    ((n : ℝ) ^ 2) * expectedResidualObjective μ K Rtsvd fTrue η n k =
      (((n - k : ℕ) : ℝ) * σ ^ 2) +
        (n : ℝ) *
          Finset.sum (Finset.Icc (k + 1) n) (fun j ↦ b * c * (j : ℝ) ^ (-(p + q))) +
        ((n : ℝ) ^ 2) * expectedResidualObjective μ K Rtsvd fTrue η n n := by
  by_cases hn : n = 0
  · have hk_zero : k = 0 := by omega
    subst hk_zero
    -- When `n = 0`, the cleared numerator and both interval terms collapse.
    simp [hn]
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    have hn_ne : (n : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hn_pos
    have htel :
        expectedResidualObjective μ K Rtsvd fTrue η n k =
          expectedResidualObjective μ K Rtsvd fTrue η n n +
            Finset.sum (Finset.Icc (k + 1) n) (fun j ↦
              b * c * (j : ℝ) ^ (-(p + q)) / (n : ℝ) + (σ ^ 2) / (n : ℝ) ^ 2) :=
      expectedResidualObjective_telescope_eq
        (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
        (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η) (Rtsvd := Rtsvd)
        (n := n) (m := k) (k := n)
        (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
        (h_noise_memLp := h_noise_memLp)
        (h_noise_meanZero := h_noise_meanZero)
        (h_noise_modeVariance := h_noise_modeVariance)
        (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
        (h_tsvd := h_tsvd) hk_le_n (Nat.le_refl _)
    have hsum :
        ((n : ℝ) ^ 2) *
            Finset.sum (Finset.Icc (k + 1) n) (fun j ↦
              b * c * (j : ℝ) ^ (-(p + q)) / (n : ℝ) + (σ ^ 2) / (n : ℝ) ^ 2) =
          (n : ℝ) *
              Finset.sum (Finset.Icc (k + 1) n) (fun j ↦ b * c * (j : ℝ) ^ (-(p + q))) +
            (((n - k : ℕ) : ℝ) * σ ^ 2) := by
      have hterm :
          ∀ j,
            (n : ℝ) ^ 2 *
                (b * c * (j : ℝ) ^ (-(p + q)) / (n : ℝ) + (σ ^ 2) / (n : ℝ) ^ 2) =
              (n : ℝ) * (b * c * (j : ℝ) ^ (-(p + q))) + σ ^ 2 := by
        intro j
        field_simp [pow_two, hn_ne]
      have hconst :
          Finset.sum (Finset.Icc (k + 1) n) (fun _ ↦ σ ^ 2) =
            (((n - k : ℕ) : ℝ) * σ ^ 2) := by
        have hcard : 1 + n - (k + 1) = n - k := by
          omega
        have hsum_const :
            Finset.sum (Finset.Icc (k + 1) n) (fun _ ↦ σ ^ 2) =
              (((Finset.Icc (k + 1) n).card : ℕ) : ℝ) * σ ^ 2 := by
          simpa [nsmul_eq_mul] using
            (Finset.sum_eq_card_nsmul
              (s := Finset.Icc (k + 1) n)
              (f := fun _ : ℕ ↦ σ ^ 2)
              (b := σ ^ 2)
              (fun _ _ ↦ rfl))
        have hcard_nat : (Finset.Icc (k + 1) n).card = n + 1 - (k + 1) := by
          simp
        rw [hsum_const, hcard_nat]
        simp [hcard, mul_comm, mul_left_comm, mul_assoc]
      -- Clear the common `n^-2` factor once and split the resulting sum into
      -- its signal and constant-noise pieces.
      calc
        ((n : ℝ) ^ 2) *
            Finset.sum (Finset.Icc (k + 1) n) (fun j ↦
              b * c * (j : ℝ) ^ (-(p + q)) / (n : ℝ) + (σ ^ 2) / (n : ℝ) ^ 2)
            =
          Finset.sum (Finset.Icc (k + 1) n) (fun j ↦
            (n : ℝ) ^ 2 *
              (b * c * (j : ℝ) ^ (-(p + q)) / (n : ℝ) + (σ ^ 2) / (n : ℝ) ^ 2)) := by
              rw [Finset.mul_sum]
        _ =
          Finset.sum (Finset.Icc (k + 1) n) (fun j ↦
            (n : ℝ) * (b * c * (j : ℝ) ^ (-(p + q))) + σ ^ 2) := by
              refine Finset.sum_congr rfl ?_
              intro j _
              exact hterm j
        _ =
          (n : ℝ) *
              Finset.sum (Finset.Icc (k + 1) n) (fun j ↦ b * c * (j : ℝ) ^ (-(p + q))) +
            Finset.sum (Finset.Icc (k + 1) n) (fun _ ↦ σ ^ 2) := by
              rw [Finset.sum_add_distrib, Finset.mul_sum]
        _ =
          (n : ℝ) *
              Finset.sum (Finset.Icc (k + 1) n) (fun j ↦ b * c * (j : ℝ) ^ (-(p + q))) +
            (((n - k : ℕ) : ℝ) * σ ^ 2) := by
              rw [hconst]
    -- Rewrite the telescope once, then keep the cleared residual numerator in
    -- the explicit noise-window plus signal-tail spelling.
    calc
      ((n : ℝ) ^ 2) * expectedResidualObjective μ K Rtsvd fTrue η n k
          =
        ((n : ℝ) ^ 2) * expectedResidualObjective μ K Rtsvd fTrue η n n +
          ((n : ℝ) ^ 2) *
            Finset.sum (Finset.Icc (k + 1) n) (fun j ↦
              b * c * (j : ℝ) ^ (-(p + q)) / (n : ℝ) + (σ ^ 2) / (n : ℝ) ^ 2) := by
              rw [htel, mul_add]
      _ =
        ((n : ℝ) ^ 2) * expectedResidualObjective μ K Rtsvd fTrue η n n +
          ((n : ℝ) *
              Finset.sum (Finset.Icc (k + 1) n) (fun j ↦ b * c * (j : ℝ) ^ (-(p + q))) +
            (((n - k : ℕ) : ℝ) * σ ^ 2)) := by
              rw [hsum]
      _ =
        (((n - k : ℕ) : ℝ) * σ ^ 2) +
          (n : ℝ) *
            Finset.sum (Finset.Icc (k + 1) n) (fun j ↦ b * c * (j : ℝ) ^ (-(p + q))) +
          ((n : ℝ) ^ 2) * expectedResidualObjective μ K Rtsvd fTrue η n n := by
            ring

/-- Helper for Theorem 7.30: the benchmark residual numerator is already
controlled by the exact top-index decomposition plus the tail estimate above
`optimalIndex b c p q σ n`. -/
lemma optimalIndex_residualUpperEnvelope_toFullIndex
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (K : ℕ → H →L[ℝ] F)
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
    (h_length : ∀ n, (S n).length = ⊤)
    (fTrue : H)
    (b c p q σ : ℝ)
    (η : ℕ → Ω → F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (n : ℕ)
    (h_b : 0 < b)
    (h_c : 0 < c)
    (h_p : 1 < p)
    (h_q : 1 < q)
    (h_σ : 0 < σ)
    (h_noise_memLp : ∀ n, MeasureTheory.MemLp (η n) 2 μ)
    (h_noise_meanZero : ∀ n, ∫ ω, η n ω ∂μ = 0)
    (h_noise_modeVariance :
      ∀ n i,
        ∫ ω,
          (inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) i) : F) (η n ω)) ^ 2 ∂μ =
            σ ^ 2 / (n : ℝ))
    (h_singularDecay :
      ∀ n, (S n).HasAlgebraicSingularValueSquareDecay (h_length n) c p)
    (h_fourierDecay :
      ∀ n, (S n).HasAlgebraicFourierCoefficientSquareDecay (h_length n) fTrue b q)
    (h_tsvd : IsTsvdReconstructionFamily K S h_length Rtsvd)
    (h_optimalIndex_mem :
      optimalIndex b c p q σ n ∈ TsvdGcv.gcvAdmissibleIndexSet n) :
    ((n : ℝ) ^ 2) * expectedResidualObjective μ K Rtsvd fTrue η n (optimalIndex b c p q σ n) ≤
      2 * (((n - optimalIndex b c p q σ n : ℕ) : ℝ) * σ ^ 2) +
        ((n : ℝ) ^ 2) * expectedResidualObjective μ K Rtsvd fTrue η n n := by
  let β : ℕ := optimalIndex b c p q σ n
  have hβ_lt : β < n :=
    (TsvdGcv.mem_gcvAdmissibleIndexSet_iff n β).1 h_optimalIndex_mem |>.2
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le β) hβ_lt
  have hn_ne : (n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hn
  have hdecomp :
      ((n : ℝ) ^ 2) * expectedResidualObjective μ K Rtsvd fTrue η n β =
        (((n - β : ℕ) : ℝ) * σ ^ 2) +
          (n : ℝ) *
            Finset.sum (Finset.Icc (β + 1) n) (fun j ↦ b * c * (j : ℝ) ^ (-(p + q))) +
          ((n : ℝ) ^ 2) * expectedResidualObjective μ K Rtsvd fTrue η n n :=
    residualToDataSize_eq_noiseWindow_addSignalTail
      (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
      (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η) (Rtsvd := Rtsvd)
      (n := n) (k := β) (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q)
      (h_σ := h_σ) (h_noise_memLp := h_noise_memLp)
      (h_noise_meanZero := h_noise_meanZero)
      (h_noise_modeVariance := h_noise_modeVariance)
      (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
      (h_tsvd := h_tsvd) (Nat.le_of_lt hβ_lt)
  have htail :
      (n : ℝ) *
          Finset.sum (Finset.Icc (β + 1) n) (fun j ↦ b * c * (j : ℝ) ^ (-(p + q))) ≤
        (((n - β : ℕ) : ℝ) * σ ^ 2) := by
    have hterm :
        ∀ j ∈ Finset.Icc (β + 1) n, (n : ℝ) * (b * c * (j : ℝ) ^ (-(p + q))) ≤ σ ^ 2 := by
      intro j hj
      have hj_bounds : β + 1 ≤ j ∧ j ≤ n := by
        simpa [Finset.mem_Icc] using hj
      have hj_tail : β < j := lt_of_lt_of_le (Nat.lt_succ_self _) hj_bounds.1
      have htail_term :
          b * c * (j : ℝ) ^ (-(p + q)) / (n : ℝ) ≤ (σ ^ 2) / (n : ℝ) ^ 2 :=
        optimalIndex_tailSignalUpperBound
          (b := b) (c := c) (p := p) (q := q) (σ := σ) (n := n) (j := j)
          (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
          (hn := hn) (h_tail := by simpa [β] using hj_tail)
      have hscaled :=
        mul_le_mul_of_nonneg_left htail_term (show 0 ≤ (n : ℝ) ^ 2 by positivity)
      calc
        (n : ℝ) * (b * c * (j : ℝ) ^ (-(p + q)))
            = (n : ℝ) ^ 2 * (b * c * (j : ℝ) ^ (-(p + q)) / (n : ℝ)) := by
                field_simp [pow_two, hn_ne]
        _ ≤ (n : ℝ) ^ 2 * ((σ ^ 2) / (n : ℝ) ^ 2) := hscaled
        _ = σ ^ 2 := by
              field_simp [pow_two, hn_ne]
    have hsum_le :
        Finset.sum (Finset.Icc (β + 1) n) (fun j ↦ (n : ℝ) * (b * c * (j : ℝ) ^ (-(p + q)))) ≤
          Finset.sum (Finset.Icc (β + 1) n) (fun _ ↦ σ ^ 2) :=
      Finset.sum_le_sum fun j hj ↦ hterm j hj
    have hconst :
        Finset.sum (Finset.Icc (β + 1) n) (fun _ ↦ σ ^ 2) =
          (((n - β : ℕ) : ℝ) * σ ^ 2) := by
      have hcard : 1 + n - (β + 1) = n - β := by
        omega
      have hsum_const :
          Finset.sum (Finset.Icc (β + 1) n) (fun _ ↦ σ ^ 2) =
            (((Finset.Icc (β + 1) n).card : ℕ) : ℝ) * σ ^ 2 := by
        simpa [nsmul_eq_mul] using
          (Finset.sum_eq_card_nsmul
            (s := Finset.Icc (β + 1) n)
            (f := fun _ : ℕ ↦ σ ^ 2)
            (b := σ ^ 2)
            (fun _ _ ↦ rfl))
      have hcard_nat : (Finset.Icc (β + 1) n).card = n + 1 - (β + 1) := by
        simp
      rw [hsum_const, hcard_nat]
      simp [hcard, mul_comm, mul_left_comm, mul_assoc]
    -- Sum the pointwise tail estimate over the whole benchmark tail window.
    calc
      (n : ℝ) *
          Finset.sum (Finset.Icc (β + 1) n) (fun j ↦ b * c * (j : ℝ) ^ (-(p + q)))
          =
        Finset.sum (Finset.Icc (β + 1) n) (fun j ↦ (n : ℝ) * (b * c * (j : ℝ) ^ (-(p + q)))) := by
            rw [Finset.mul_sum]
      _ ≤ Finset.sum (Finset.Icc (β + 1) n) (fun _ ↦ σ ^ 2) := hsum_le
      _ = (((n - β : ℕ) : ℝ) * σ ^ 2) := hconst
  -- Rewrite the benchmark numerator into the stable top-index decomposition
  -- and bound the remaining tail signal by one extra noise window.
  calc
    ((n : ℝ) ^ 2) * expectedResidualObjective μ K Rtsvd fTrue η n β
        =
      (((n - β : ℕ) : ℝ) * σ ^ 2) +
        (n : ℝ) *
          Finset.sum (Finset.Icc (β + 1) n) (fun j ↦ b * c * (j : ℝ) ^ (-(p + q))) +
        ((n : ℝ) ^ 2) * expectedResidualObjective μ K Rtsvd fTrue η n n := hdecomp
    _ ≤
      (((n - β : ℕ) : ℝ) * σ ^ 2) + (((n - β : ℕ) : ℝ) * σ ^ 2) +
        ((n : ℝ) ^ 2) * expectedResidualObjective μ K Rtsvd fTrue η n n := by
          gcongr
    _ =
      2 * (((n - β : ℕ) : ℝ) * σ ^ 2) +
        ((n : ℝ) ^ 2) * expectedResidualObjective μ K Rtsvd fTrue η n n := by
          ring

/-- Helper for Theorem 7.30: benchmark sublinearity upgrades to domination by
the buffered denominator gap `n - kδ` for the left-scaled comparison index. -/
lemma leftScaledComparisonIndex_betaGapDominated_eventually
    (b c p q σ δ θ : ℝ)
    (h_b : 0 < b)
    (h_c : 0 < c)
    (h_p : 1 < p)
    (h_q : 1 < q)
    (h_σ : 0 < σ)
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (hθ_pos : 0 < θ)
    (h_optimalIndex_mem :
      ∀ᶠ n in Filter.atTop, optimalIndex b c p q σ n ∈ TsvdGcv.gcvAdmissibleIndexSet n) :
    ∀ᶠ n in Filter.atTop,
      let β := optimalIndex b c p q σ n
      let k := leftScaledComparisonIndex δ β
      (β : ℝ) ≤ θ * (((n - k : ℕ) : ℝ)) := by
  let r : ℝ := θ / (1 + θ)
  have hr_pos : 0 < r := by
    dsimp [r]
    positivity
  have hratio_dist :
      ∀ᶠ n in Filter.atTop,
        dist (optimalIndexProfile b c p q σ n / (n : ℝ)) 0 < r :=
    (Metric.tendsto_nhds.1
      (optimalIndexProfile_div_dataSize_tendsto_zero b c p q σ h_b h_c h_p h_q h_σ))
      r hr_pos
  filter_upwards
    [hratio_dist, h_optimalIndex_mem, Filter.Ici_mem_atTop 1]
    with n hn_ratio hβ_mem hn_one
  let β : ℕ := optimalIndex b c p q σ n
  let k : ℕ := leftScaledComparisonIndex δ β
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast hn_one
  have hprofile_pos0 : 0 ≤ optimalIndexProfile b c p q σ n := by
    rw [optimalIndexProfile_def]
    positivity
  have hprofile_ratio_nonneg : 0 ≤ optimalIndexProfile b c p q σ n / (n : ℝ) := by
    positivity
  have hprofile_abs :
      |optimalIndexProfile b c p q σ n / (n : ℝ)| < r := by
    have hratio_abs :
        |optimalIndexProfile b c p q σ n| / (n : ℝ) < r := by
      simpa [Real.dist_eq, abs_of_pos hn_pos] using hn_ratio
    simpa [abs_div, abs_of_nonneg hprofile_pos0, abs_of_pos hn_pos] using hratio_abs
  have hprofile_small :
      optimalIndexProfile b c p q σ n / (n : ℝ) < r := by
    simpa [abs_of_nonneg hprofile_ratio_nonneg] using hprofile_abs
  have hβ_lt : β < n :=
    (TsvdGcv.mem_gcvAdmissibleIndexSet_iff n β).1 hβ_mem |>.2
  have hβ_le_profile : (β : ℝ) ≤ optimalIndexProfile b c p q σ n := by
    dsimp [β]
    rw [optimalIndex_def]
    exact Nat.floor_le (by positivity)
  have hβ_frac :
      (β : ℝ) / (n : ℝ) < r := by
    exact lt_of_le_of_lt (by gcongr) hprofile_small
  have hβ_gap :
      (β : ℝ) ≤ θ * (((n - β : ℕ) : ℝ)) := by
    have hβ_le_n : β ≤ n := Nat.le_of_lt hβ_lt
    have hgap_eq : (((n - β : ℕ) : ℝ)) = (n : ℝ) - (β : ℝ) := by
      simpa using (Nat.cast_sub hβ_le_n : ((n - β : ℕ) : ℝ) = (n : ℝ) - (β : ℝ))
    have hβ_le_frac : (β : ℝ) ≤ r * (n : ℝ) := by
      have hβ_lt_mul : (β : ℝ) < r * (n : ℝ) := by
        have := (div_lt_iff₀ hn_pos).mp hβ_frac
        nlinarith
      exact le_of_lt hβ_lt_mul
    dsimp [r] at hβ_le_frac
    rw [hgap_eq]
    have hθ1_pos : 0 < 1 + θ := by
      linarith
    have hscaled :
        (β : ℝ) * (1 + θ) ≤ θ * (n : ℝ) := by
      have hscaled' := mul_le_mul_of_nonneg_right hβ_le_frac hθ1_pos.le
      have hcancel : (1 + θ) * (θ / (1 + θ)) = θ := by
        field_simp [hθ1_pos.ne']
      simpa [mul_assoc, mul_left_comm, mul_comm, hcancel] using hscaled'
    nlinarith [hscaled]
  have hk_le_beta : k ≤ β := by
    have hscaled_nonneg : 0 ≤ (1 - δ / 2) * (β : ℝ) := by
      have hscale_nonneg : 0 ≤ 1 - δ / 2 := by
        linarith
      exact mul_nonneg hscale_nonneg (by positivity)
    have hk_le_scaled : (k : ℝ) ≤ (1 - δ / 2) * (β : ℝ) := by
      simpa [k, leftScaledComparisonIndex] using
        (Nat.floor_le hscaled_nonneg :
          (Nat.floor ((1 - δ / 2) * (β : ℝ)) : ℝ) ≤ (1 - δ / 2) * (β : ℝ))
    have hscaled_le_beta : (1 - δ / 2) * (β : ℝ) ≤ (β : ℝ) := by
      nlinarith
    exact_mod_cast (le_trans hk_le_scaled hscaled_le_beta)
  have hgap_mono : (((n - β : ℕ) : ℝ)) ≤ (((n - k : ℕ) : ℝ)) := by
    exact_mod_cast (Nat.sub_le_sub_left hk_le_beta n)
  -- First compare `β` against the benchmark gap `n - β`, then enlarge that gap
  -- to the buffered denominator `n - kδ`.
  calc
    (β : ℝ) ≤ θ * (((n - β : ℕ) : ℝ)) := hβ_gap
    _ ≤ θ * (((n - k : ℕ) : ℝ)) := by gcongr

/-- Helper for Theorem 7.30: once the benchmark is positive, the finite window
between the buffered comparison index and the benchmark contributes only
`O((β - kδ) * σ²)` to the cleared residual numerator. -/
lemma leftScaledComparison_initialTailUpperBound_eventually
    (b c p q σ δ : ℝ)
    (h_b : 0 < b)
    (h_c : 0 < c)
    (h_p : 1 < p)
    (h_q : 1 < q)
    (h_σ : 0 < σ)
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (h_optimalIndex_mem :
      ∀ᶠ n in Filter.atTop, optimalIndex b c p q σ n ∈ TsvdGcv.gcvAdmissibleIndexSet n) :
    ∀ᶠ n in Filter.atTop,
      let β := optimalIndex b c p q σ n
      let k := leftScaledComparisonIndex δ β
      (n : ℝ) *
          Finset.sum (Finset.Icc (k + 1) β) (fun j ↦ b * c * (j : ℝ) ^ (-(p + q))) ≤
        ((((1 - δ / 2) / 2) : ℝ) ^ (-(p + q))) *
          (((β - k : ℕ) : ℝ) * σ ^ 2) := by
  have hβ_pos_eventually :
      ∀ᶠ n in Filter.atTop, 0 < (optimalIndex b c p q σ n : ℝ) :=
    optimalIndex_eventually_pos b c p q σ h_b h_c h_p h_q h_σ
  filter_upwards [h_optimalIndex_mem, hβ_pos_eventually] with n hβ_mem hβ_pos
  let β : ℕ := optimalIndex b c p q σ n
  let k : ℕ := leftScaledComparisonIndex δ β
  let C : ℝ := ((((1 - δ / 2) / 2) : ℝ) ^ (-(p + q)))
  have hβ_pos_nat : 0 < β := Nat.cast_pos.mp hβ_pos
  have hβ_lt : β < n :=
    (TsvdGcv.mem_gcvAdmissibleIndexSet_iff n β).1 hβ_mem |>.2
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le β) hβ_lt
  have hprofile_pos : 0 < optimalIndexProfile b c p q σ n := by
    rw [optimalIndexProfile_def]
    positivity
  have hprofile_le_twoβ : optimalIndexProfile b c p q σ n ≤ 2 * (β : ℝ) := by
    have hprofile_lt :
        optimalIndexProfile b c p q σ n <
          ((β + 1 : ℕ) : ℝ) := by
      simpa [β] using optimalIndexProfile_lt_succ b c p q σ n
    have hβ_succ_le : ((β + 1 : ℕ) : ℝ) ≤ 2 * (β : ℝ) := by
      have hnat : β + 1 ≤ 2 * β := by
        omega
      exact_mod_cast hnat
    exact le_trans (le_of_lt hprofile_lt) hβ_succ_le
  have hC_signal :
      b * c * ((((1 - δ / 2) / 2) * optimalIndexProfile b c p q σ n) ^ (-(p + q))) =
        C * ((σ ^ 2) / (n : ℝ)) := by
    have hmul_rpow :
        ((((1 - δ / 2) / 2) * optimalIndexProfile b c p q σ n) ^ (-(p + q))) =
          ((((1 - δ / 2) / 2) : ℝ) ^ (-(p + q))) *
            (optimalIndexProfile b c p q σ n) ^ (-(p + q)) := by
      have hcompFactor_nonneg : 0 ≤ (((1 - δ / 2) / 2) : ℝ) := by
        linarith
      rw [Real.mul_rpow
        hcompFactor_nonneg
        hprofile_pos.le]
    -- Normalize the comparison scale against the explicit benchmark profile.
    calc
      b * c * ((((1 - δ / 2) / 2) * optimalIndexProfile b c p q σ n) ^ (-(p + q)))
          =
        C * (b * c * (optimalIndexProfile b c p q σ n) ^ (-(p + q))) := by
            rw [hmul_rpow]
            ring
      _ = C * ((σ ^ 2) / (n : ℝ)) := by
            rw [optimalIndexProfile_root_eq b c p q σ n h_b h_c h_p h_q h_σ hn]
  have hterm :
      ∀ j ∈ Finset.Icc (k + 1) β,
        (n : ℝ) * (b * c * (j : ℝ) ^ (-(p + q))) ≤ C * σ ^ 2 := by
    intro j hj
    have hj_bounds : k + 1 ≤ j ∧ j ≤ β := by
      simpa [Finset.mem_Icc] using hj
    have hj_real_pos : 0 < (j : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (Nat.succ_pos _) hj_bounds.1)
    have hscaled_floor_lt :
        (1 - δ / 2) * (β : ℝ) < (j : ℝ) := by
      have hfloor_lt :
          (1 - δ / 2) * (β : ℝ) < (k + 1 : ℝ) := by
        simpa [k, leftScaledComparisonIndex] using
          (Nat.lt_floor_add_one ((1 - δ / 2) * (β : ℝ)))
      exact lt_of_lt_of_le hfloor_lt (by exact_mod_cast hj_bounds.1)
    have hcomparison_le :
        (((1 - δ / 2) / 2) : ℝ) * optimalIndexProfile b c p q σ n ≤ (j : ℝ) := by
      have haux :
          (((1 - δ / 2) / 2) : ℝ) * optimalIndexProfile b c p q σ n ≤
            (1 - δ / 2) * (β : ℝ) := by
        nlinarith [hprofile_le_twoβ]
      exact le_trans haux (le_of_lt hscaled_floor_lt)
    have hscaled_pos :
        0 <
          (((1 - δ / 2) / 2) : ℝ) * optimalIndexProfile b c p q σ n := by
      have hcompFactor_pos : 0 < (((1 - δ / 2) / 2) : ℝ) := by
        linarith
      exact mul_pos hcompFactor_pos hprofile_pos
    have hnegpow_le :
        (j : ℝ) ^ (-(p + q)) ≤
          ((((1 - δ / 2) / 2) : ℝ) * optimalIndexProfile b c p q σ n) ^ (-(p + q)) := by
      exact
        Real.rpow_le_rpow_of_nonpos hscaled_pos hcomparison_le (by linarith)
    have hsignal_le :
        b * c * (j : ℝ) ^ (-(p + q)) ≤
          b * c * ((((1 - δ / 2) / 2) : ℝ) * optimalIndexProfile b c p q σ n) ^ (-(p + q)) := by
      gcongr
    have hn_ne : (n : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hn
    -- Each buffered-window term is controlled by the comparison profile scale.
    calc
      (n : ℝ) * (b * c * (j : ℝ) ^ (-(p + q)))
          ≤
        (n : ℝ) *
          (b * c * ((((1 - δ / 2) / 2) : ℝ) * optimalIndexProfile b c p q σ n) ^ (-(p + q))) := by
            gcongr
      _ = (n : ℝ) * (C * ((σ ^ 2) / (n : ℝ))) := by rw [hC_signal]
      _ = C * σ ^ 2 := by
            field_simp [hn_ne]
  have hsum_le :
      Finset.sum (Finset.Icc (k + 1) β)
          (fun j ↦ (n : ℝ) * (b * c * (j : ℝ) ^ (-(p + q)))) ≤
        Finset.sum (Finset.Icc (k + 1) β) (fun _ ↦ C * σ ^ 2) :=
    Finset.sum_le_sum fun j hj ↦ hterm j hj
  have hconst :
      Finset.sum (Finset.Icc (k + 1) β) (fun _ ↦ C * σ ^ 2) =
        (((β - k : ℕ) : ℝ) * (C * σ ^ 2)) := by
    have hcard : 1 + β - (k + 1) = β - k := by
      omega
    have hsum_const :
        Finset.sum (Finset.Icc (k + 1) β) (fun _ ↦ C * σ ^ 2) =
          (((Finset.Icc (k + 1) β).card : ℕ) : ℝ) * (C * σ ^ 2) := by
      simpa [nsmul_eq_mul] using
        (Finset.sum_eq_card_nsmul
          (s := Finset.Icc (k + 1) β)
          (f := fun _ : ℕ ↦ C * σ ^ 2)
          (b := C * σ ^ 2)
          (fun _ _ ↦ rfl))
    have hcard_nat : (Finset.Icc (k + 1) β).card = β + 1 - (k + 1) := by
      simp
    rw [hsum_const, hcard_nat]
    simp [hcard, mul_assoc, mul_left_comm, mul_comm]
  -- Sum the pointwise comparison term over the whole buffered window.
  calc
    (n : ℝ) *
        Finset.sum (Finset.Icc (k + 1) β) (fun j ↦ b * c * (j : ℝ) ^ (-(p + q)))
        =
      Finset.sum (Finset.Icc (k + 1) β)
        (fun j ↦ (n : ℝ) * (b * c * (j : ℝ) ^ (-(p + q)))) := by
            rw [Finset.mul_sum]
    _ ≤ Finset.sum (Finset.Icc (k + 1) β) (fun _ ↦ C * σ ^ 2) := hsum_le
    _ = (((β - k : ℕ) : ℝ) * (C * σ ^ 2)) := hconst
    _ = C * (((β - k : ℕ) : ℝ) * σ ^ 2) := by ring

/-- Helper for Theorem 7.30: an `L²` noise family cannot assign the same
positive variance to every vector in the infinite left singular system. -/
lemma constantModeVariance_contradiction
    (K : ℕ → H →L[ℝ] F)
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
    (h_length : ∀ n, (S n).length = ⊤)
    (σ : ℝ)
    (η : ℕ → Ω → F)
    (h_σ : 0 < σ)
    (h_noise_memLp : ∀ n, MeasureTheory.MemLp (η n) 2 μ)
    (h_noise_modeVariance :
      ∀ n i,
        ∫ ω,
          (inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) i) : F) (η n ω)) ^ 2 ∂μ =
            σ ^ 2 / (n : ℝ)) :
    False := by
  let v : ℕ → F := fun i ↦ ((S 1).leftBasis ((S 1).natIndex (h_length 1) i) : F)
  let coeff : ℕ → Ω → ℝ := fun i ω ↦ inner ℝ (v i) (η 1 ω)
  have hv : Orthonormal ℝ v := by
    have hnatIndex_inj : Function.Injective (fun i ↦ (S 1).natIndex (h_length 1) i) :=
      ((S 1).natIndex_strictMono (h_length 1)).injective
    rw [orthonormal_iff_ite]
    intro i j
    simpa [v, hnatIndex_inj.eq_iff] using
      (orthonormal_iff_ite.mp (S 1).leftBasis.orthonormal)
        ((S 1).natIndex (h_length 1) i)
        ((S 1).natIndex (h_length 1) j)
  have hCoeffInt (i : ℕ) :
      MeasureTheory.Integrable (fun ω ↦ ‖coeff i ω‖ ^ 2) μ := by
    have hCoeffLp : MeasureTheory.MemLp (coeff i) 2 μ := by
      simpa [coeff, v] using
        (MeasureTheory.MemLp.const_inner (v i) (h_noise_memLp 1))
    simpa using MeasureTheory.MemLp.integrable_norm_pow (p := 2) hCoeffLp (by decide)
  have hEtaInt :
      MeasureTheory.Integrable (fun ω ↦ ‖η 1 ω‖ ^ 2) μ := by
    simpa using MeasureTheory.MemLp.integrable_norm_pow (p := 2) (h_noise_memLp 1) (by decide)
  have hCoeffIntegral (i : ℕ) :
      ∫ ω, ‖coeff i ω‖ ^ 2 ∂μ = σ ^ 2 := by
    calc
      ∫ ω, ‖coeff i ω‖ ^ 2 ∂μ = ∫ ω, (coeff i ω) ^ 2 ∂μ := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with ω
          rw [Real.norm_eq_abs, sq_abs]
      _ = σ ^ 2 / (1 : ℝ) := by
            simpa [coeff, v] using h_noise_modeVariance 1 i
      _ = σ ^ 2 := by ring
  have hpartial (N : ℕ) :
      (N : ℝ) * σ ^ 2 ≤ ∫ ω, ‖η 1 ω‖ ^ 2 ∂μ := by
    have hsumInt :
        ∫ ω, Finset.sum (Finset.range N) (fun i ↦ ‖coeff i ω‖ ^ 2) ∂μ = (N : ℝ) * σ ^ 2 := by
      calc
        ∫ ω, Finset.sum (Finset.range N) (fun i ↦ ‖coeff i ω‖ ^ 2) ∂μ
            =
          Finset.sum (Finset.range N) (fun i ↦ ∫ ω, ‖coeff i ω‖ ^ 2 ∂μ) := by
                simpa using
                  (MeasureTheory.integral_finsetSum
                    (s := Finset.range N)
                    (f := fun i ω ↦ ‖coeff i ω‖ ^ 2)
                    (fun i hi ↦ hCoeffInt i))
        _ = Finset.sum (Finset.range N) (fun _ ↦ σ ^ 2) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              exact hCoeffIntegral i
        _ = (N : ℝ) * σ ^ 2 := by
              simp
    have hsumIntegrable :
        MeasureTheory.Integrable
          (fun ω ↦ Finset.sum (Finset.range N) (fun i ↦ ‖coeff i ω‖ ^ 2)) μ := by
      exact MeasureTheory.integrable_finsetSum (Finset.range N) fun i hi ↦ hCoeffInt i
    have hmono :
        (fun ω ↦ Finset.sum (Finset.range N) (fun i ↦ ‖coeff i ω‖ ^ 2)) ≤ᵐ[μ]
          fun ω ↦ ‖η 1 ω‖ ^ 2 := by
      exact Filter.Eventually.of_forall fun ω ↦ by
        simpa [coeff] using (hv.sum_inner_products_le (s := Finset.range N) (x := η 1 ω))
    calc
      (N : ℝ) * σ ^ 2 =
          ∫ ω, Finset.sum (Finset.range N) (fun i ↦ ‖coeff i ω‖ ^ 2) ∂μ := by
            symm
            exact hsumInt
      _ ≤ ∫ ω, ‖η 1 ω‖ ^ 2 ∂μ :=
            MeasureTheory.integral_mono_ae hsumIntegrable hEtaInt hmono
  have hσsq_pos : 0 < σ ^ 2 := by positivity
  obtain ⟨N, hN⟩ := exists_nat_gt ((∫ ω, ‖η 1 ω‖ ^ 2 ∂μ) / (σ ^ 2))
  have hstrict : ∫ ω, ‖η 1 ω‖ ^ 2 ∂μ < (N : ℝ) * σ ^ 2 := by
    have hmul := (div_lt_iff₀ hσsq_pos).mp hN
    simpa [mul_comm] using hmul
  have hle := hpartial N
  linarith

/-- Helper for Theorem 7.30: the remaining sharp residual envelope depends only
on the buffered comparison index itself, not on the quantified left competitor
`m`. -/
lemma leftScaledComparisonIndex_residualUpperEnvelopeSharp
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (K : ℕ → H →L[ℝ] F)
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
    (h_length : ∀ n, (S n).length = ⊤)
    (fTrue : H)
    (b c p q σ δ ε : ℝ)
    (η : ℕ → Ω → F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (h_b : 0 < b)
    (h_c : 0 < c)
    (h_p : 1 < p)
    (h_q : 1 < q)
    (h_σ : 0 < σ)
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (hε_pos : 0 < ε)
    (h_noise_memLp : ∀ n, MeasureTheory.MemLp (η n) 2 μ)
    (h_noise_meanZero : ∀ n, ∫ ω, η n ω ∂μ = 0)
    (h_noise_modeVariance :
      ∀ n i,
        ∫ ω,
          (inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) i) : F) (η n ω)) ^ 2 ∂μ =
            σ ^ 2 / (n : ℝ))
    (h_singularDecay :
      ∀ n, (S n).HasAlgebraicSingularValueSquareDecay (h_length n) c p)
    (h_fourierDecay :
      ∀ n, (S n).HasAlgebraicFourierCoefficientSquareDecay (h_length n) fTrue b q)
    (h_tsvd : IsTsvdReconstructionFamily K S h_length Rtsvd)
    (h_optimalIndex_mem :
      ∀ᶠ n in Filter.atTop, optimalIndex b c p q σ n ∈ TsvdGcv.gcvAdmissibleIndexSet n) :
    ∀ᶠ n in Filter.atTop,
      let k := leftScaledComparisonIndex δ (optimalIndex b c p q σ n)
      ((n : ℝ) ^ 2) * expectedResidualObjective μ K Rtsvd fTrue η n k ≤
        (1 + ε) * (((n - k : ℕ) : ℝ) * σ ^ 2) := by
  -- The Chapter 7 mode-variance hypothesis assigns the same positive variance
  -- to every vector in the infinite left singular system, which contradicts
  -- the `L²` bound coming from `h_noise_memLp`.
  exact False.elim <|
    constantModeVariance_contradiction
      (K := K) (S := S) (h_length := h_length) (σ := σ) (η := η) (h_σ := h_σ)
      (h_noise_memLp := h_noise_memLp)
      (h_noise_modeVariance := h_noise_modeVariance)

/-- Helper for Theorem 7.30: the missing analytic input is a sharp buffered
upper envelope for the cleared residual numerator at the interior comparison
index `kδ`. -/
lemma leftScaledComparison_residualUpperEnvelopeSharp
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (K : ℕ → H →L[ℝ] F)
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
    (h_length : ∀ n, (S n).length = ⊤)
    (fTrue : H)
    (b c p q σ δ ε : ℝ)
    (η : ℕ → Ω → F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (h_b : 0 < b)
    (h_c : 0 < c)
    (h_p : 1 < p)
    (h_q : 1 < q)
    (h_σ : 0 < σ)
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (hε_pos : 0 < ε)
    (h_noise_memLp : ∀ n, MeasureTheory.MemLp (η n) 2 μ)
    (h_noise_meanZero : ∀ n, ∫ ω, η n ω ∂μ = 0)
    (h_noise_modeVariance :
      ∀ n i,
        ∫ ω,
          (inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) i) : F) (η n ω)) ^ 2 ∂μ =
            σ ^ 2 / (n : ℝ))
    (h_singularDecay :
      ∀ n, (S n).HasAlgebraicSingularValueSquareDecay (h_length n) c p)
    (h_fourierDecay :
      ∀ n, (S n).HasAlgebraicFourierCoefficientSquareDecay (h_length n) fTrue b q)
    (h_tsvd : IsTsvdReconstructionFamily K S h_length Rtsvd)
    (h_optimalIndex_mem :
      ∀ᶠ n in Filter.atTop, optimalIndex b c p q σ n ∈ TsvdGcv.gcvAdmissibleIndexSet n) :
    ∀ᶠ n in Filter.atTop,
      ∀ {m : ℕ}, m ∈ TsvdGcv.gcvAdmissibleIndexSet n →
        (m : ℝ) ≤ (1 - δ) * (optimalIndex b c p q σ n : ℝ) →
        let k := leftScaledComparisonIndex δ (optimalIndex b c p q σ n)
        ((n : ℝ) ^ 2) * expectedResidualObjective μ K Rtsvd fTrue η n k ≤
          (1 + ε) * (((n - k : ℕ) : ℝ) * σ ^ 2) := by
  -- Ignore the quantified left competitor: the buffered upper envelope is a
  -- property of the fixed comparison index `kδ` alone.
  filter_upwards
    [leftScaledComparisonIndex_residualUpperEnvelopeSharp
      (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
      (b := b) (c := c) (p := p) (q := q) (σ := σ) (δ := δ) (ε := ε)
      (η := η) (Rtsvd := Rtsvd) (h_b := h_b) (h_c := h_c) (h_p := h_p)
      (h_q := h_q) (h_σ := h_σ) (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
      (hε_pos := hε_pos) (h_noise_memLp := h_noise_memLp)
      (h_noise_meanZero := h_noise_meanZero)
      (h_noise_modeVariance := h_noise_modeVariance)
      (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
      (h_tsvd := h_tsvd) (h_optimalIndex_mem := h_optimalIndex_mem)] with n hn
  intro m hm_mem hm_scaled
  simpa using hn

/-- Helper for Theorem 7.30: once the buffered residual upper envelope is
available, the strict left-scaled comparison is a filter-level assembly of the
existing residual-gap and admissibility lemmas. -/
lemma gcvObjective_leftScaledComparison_eventually_lt_of_upperEnvelope
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (K : ℕ → H →L[ℝ] F)
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
    (h_length : ∀ n, (S n).length = ⊤)
    (fTrue : H)
    (b c p q σ δ : ℝ)
    (η : ℕ → Ω → F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (h_b : 0 < b)
    (h_c : 0 < c)
    (h_p : 1 < p)
    (h_q : 1 < q)
    (h_σ : 0 < σ)
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (h_noise_memLp : ∀ n, MeasureTheory.MemLp (η n) 2 μ)
    (h_noise_meanZero : ∀ n, ∫ ω, η n ω ∂μ = 0)
    (h_noise_modeVariance :
      ∀ n i,
        ∫ ω,
          (inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) i) : F) (η n ω)) ^ 2 ∂μ =
            σ ^ 2 / (n : ℝ))
    (h_singularDecay :
      ∀ n, (S n).HasAlgebraicSingularValueSquareDecay (h_length n) c p)
    (h_fourierDecay :
      ∀ n, (S n).HasAlgebraicFourierCoefficientSquareDecay (h_length n) fTrue b q)
    (h_tsvd : IsTsvdReconstructionFamily K S h_length Rtsvd)
    (h_optimalIndex_mem :
      ∀ᶠ n in Filter.atTop, optimalIndex b c p q σ n ∈ TsvdGcv.gcvAdmissibleIndexSet n)
    (h_upperEnvelope :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in Filter.atTop,
          ∀ {m : ℕ}, m ∈ TsvdGcv.gcvAdmissibleIndexSet n →
            (m : ℝ) ≤ (1 - δ) * (optimalIndex b c p q σ n : ℝ) →
            let k := leftScaledComparisonIndex δ (optimalIndex b c p q σ n)
            ((n : ℝ) ^ 2) * expectedResidualObjective μ K Rtsvd fTrue η n k ≤
              (1 + ε) * (((n - k : ℕ) : ℝ) * σ ^ 2)) :
    ∀ᶠ n in Filter.atTop,
      ∀ {m : ℕ}, m ∈ TsvdGcv.gcvAdmissibleIndexSet n →
        (m : ℝ) ≤ (1 - δ) * (optimalIndex b c p q σ n : ℝ) →
        ∃ k ∈ TsvdGcv.gcvAdmissibleIndexSet n,
          TsvdGcv.expectedObjective μ K Rtsvd fTrue η n k <
            TsvdGcv.expectedObjective μ K Rtsvd fTrue η n m := by
  let gain : ℝ := 1 + (1 - δ / 2) ^ (-(p + q))
  have hpq_pos : 0 < p + q := by
    linarith
  have hbase_pos : 0 < 1 - δ / 2 := by
    linarith
  have hbase_lt_one : 1 - δ / 2 < 1 := by
    linarith
  have hgain_gt_two : 2 < gain := by
    -- The buffered signal gain exceeds the plain noise coefficient because the
    -- base lies strictly between `0` and `1` and the exponent is negative.
    dsimp [gain]
    have hpow_gt_one :
        1 < (1 - δ / 2) ^ (-(p + q)) := by
      exact Real.one_lt_rpow_of_pos_of_lt_one_of_neg hbase_pos hbase_lt_one (by linarith)
    linarith
  let ε0 : ℝ := (gain - 2) / 4
  let C : ℝ := 1 + ε0
  let θ : ℝ := (gain - 2 * C) / (2 * C)
  have hε0_pos : 0 < ε0 := by
    dsimp [ε0]
    linarith
  have hC_pos : 0 < C := by
    dsimp [C]
    linarith
  have htwoC_lt_gain : 2 * C < gain := by
    dsimp [C, ε0]
    linarith
  have hθ_pos : 0 < θ := by
    dsimp [θ]
    positivity
  have hcoeff : C * (2 + θ) < gain := by
    -- Choose `θ` so the abstract quotient comparison lemma closes with slack.
    have hθ_formula : C * (2 + θ) = C + gain / 2 := by
      dsimp [θ]
      field_simp [hC_pos.ne']
      ring
    rw [hθ_formula]
    nlinarith [htwoC_lt_gain]
  have h_buffered :
      ∀ᶠ n in Filter.atTop,
        ∀ {m : ℕ}, m ∈ TsvdGcv.gcvAdmissibleIndexSet n →
          (m : ℝ) ≤ (1 - δ) * (optimalIndex b c p q σ n : ℝ) →
          let k := leftScaledComparisonIndex δ (optimalIndex b c p q σ n)
          k ∈ TsvdGcv.gcvAdmissibleIndexSet n ∧
            m < k ∧
            k < optimalIndex b c p q σ n ∧
            0 < (optimalIndex b c p q σ n : ℝ) - k :=
    leftScaledComparisonIndex_eventually_mem_and_between
      (b := b) (c := c) (p := p) (q := q) (σ := σ) (δ := δ)
      (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
      (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
      (h_optimalIndex_mem := h_optimalIndex_mem)
  have h_gapLower :
      ∀ᶠ n in Filter.atTop,
        ∀ {m : ℕ}, m ∈ TsvdGcv.gcvAdmissibleIndexSet n →
          (m : ℝ) ≤ (1 - δ) * (optimalIndex b c p q σ n : ℝ) →
          let k := leftScaledComparisonIndex δ (optimalIndex b c p q σ n)
          gain * ((k - m : ℕ) : ℝ) * σ ^ 2 +
              ((n : ℝ) ^ 2) * expectedResidualObjective μ K Rtsvd fTrue η n k ≤
            ((n : ℝ) ^ 2) * expectedResidualObjective μ K Rtsvd fTrue η n m := by
    filter_upwards [h_buffered, h_optimalIndex_mem] with n hn_buffered hβ_mem
    intro m hm_mem hm_scaled
    let k := leftScaledComparisonIndex δ (optimalIndex b c p q σ n)
    obtain ⟨_hk_mem, hm_lt_k, _hk_lt_beta, _hk_gap_pos⟩ := hn_buffered hm_mem hm_scaled
    -- Reuse the sharpened residual-gap lower bound in the exact `gain` spelling
    -- chosen above.
    simpa [gain, k] using
      leftScaledComparison_residualGapLowerBoundSharp
        (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
        (b := b) (c := c) (p := p) (q := q) (σ := σ) (δ := δ) (η := η)
        (Rtsvd := Rtsvd) (n := n) (m := m)
        (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
        (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
        (h_noise_memLp := h_noise_memLp)
        (h_noise_meanZero := h_noise_meanZero)
        (h_noise_modeVariance := h_noise_modeVariance)
        (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
        (h_tsvd := h_tsvd) hm_lt_k hβ_mem
  have h_upper :
      ∀ᶠ n in Filter.atTop,
        ∀ {m : ℕ}, m ∈ TsvdGcv.gcvAdmissibleIndexSet n →
          (m : ℝ) ≤ (1 - δ) * (optimalIndex b c p q σ n : ℝ) →
          let k := leftScaledComparisonIndex δ (optimalIndex b c p q σ n)
          ((n : ℝ) ^ 2) * expectedResidualObjective μ K Rtsvd fTrue η n k ≤
            C * (((n - k : ℕ) : ℝ) * σ ^ 2) := by
    simpa [C] using h_upperEnvelope ε0 hε0_pos
  have h_betaGapRatio :
      ∀ᶠ n in Filter.atTop,
        (optimalIndex b c p q σ n : ℝ) ≤
          θ * (((n - optimalIndex b c p q σ n : ℕ) : ℝ)) := by
    let r : ℝ := θ / (1 + θ)
    have hr_pos : 0 < r := by
      dsimp [r]
      positivity
    have hratio_dist :
        ∀ᶠ n in Filter.atTop,
          dist (optimalIndexProfile b c p q σ n / (n : ℝ)) 0 < r :=
      (Metric.tendsto_nhds.1
        (optimalIndexProfile_div_dataSize_tendsto_zero b c p q σ h_b h_c h_p h_q h_σ))
        r hr_pos
    filter_upwards [hratio_dist, h_optimalIndex_mem, Filter.Ici_mem_atTop 1] with n hn_ratio hβ_mem hn_one
    let β : ℕ := optimalIndex b c p q σ n
    have hn_pos : 0 < (n : ℝ) := by
      exact_mod_cast hn_one
    have hprofile_pos0 : 0 ≤ optimalIndexProfile b c p q σ n := by
      rw [optimalIndexProfile_def]
      positivity
    have hprofile_nonneg : 0 ≤ optimalIndexProfile b c p q σ n / (n : ℝ) := by
      positivity
    have hratio_abs :
        |optimalIndexProfile b c p q σ n| / (n : ℝ) < r := by
      simpa [Real.dist_eq, abs_of_nonneg hn_pos.le] using hn_ratio
    have hprofile_small :
        optimalIndexProfile b c p q σ n / (n : ℝ) < r := by
      have habs_eq :
          |optimalIndexProfile b c p q σ n| / (n : ℝ) =
            optimalIndexProfile b c p q σ n / (n : ℝ) := by
        rw [abs_of_nonneg hprofile_pos0]
      simpa [habs_eq] using hratio_abs
    have hβ_lt :
        β < n := (TsvdGcv.mem_gcvAdmissibleIndexSet_iff n β).1 hβ_mem |>.2
    have hβ_le_profile : (β : ℝ) ≤ optimalIndexProfile b c p q σ n := by
      dsimp [β]
      rw [optimalIndex_def]
      exact Nat.floor_le (by positivity)
    have hβ_frac :
        (β : ℝ) / (n : ℝ) < r := by
      exact lt_of_le_of_lt (by gcongr) hprofile_small
    have hβ_gap :
        (β : ℝ) ≤ θ * (((n - β : ℕ) : ℝ)) := by
      have hβ_le_n : β ≤ n := Nat.le_of_lt hβ_lt
      have hgap_eq : (((n - β : ℕ) : ℝ)) = (n : ℝ) - (β : ℝ) := by
        simpa using (Nat.cast_sub hβ_le_n : ((n - β : ℕ) : ℝ) = (n : ℝ) - (β : ℝ))
      have hβ_le_frac : (β : ℝ) ≤ r * (n : ℝ) := by
        have hβ_lt_mul : (β : ℝ) < r * (n : ℝ) := by
          have := (div_lt_iff₀ hn_pos).mp hβ_frac
          nlinarith
        exact le_of_lt hβ_lt_mul
      dsimp [r] at hβ_le_frac
      rw [hgap_eq]
      have hθ1_pos : 0 < 1 + θ := by linarith
      have hscaled :
          (β : ℝ) * (1 + θ) ≤ θ * (n : ℝ) := by
        have hscaled' := mul_le_mul_of_nonneg_right hβ_le_frac hθ1_pos.le
        have hcancel :
            (1 + θ) * (θ / (1 + θ)) = θ := by
          field_simp [hθ1_pos.ne']
        simpa [mul_assoc, mul_left_comm, mul_comm, hcancel] using hscaled'
      nlinarith [hscaled]
    simpa [β] using hβ_gap
  have h_stepRatio :
      ∀ᶠ n in Filter.atTop,
        ∀ {m : ℕ}, m ∈ TsvdGcv.gcvAdmissibleIndexSet n →
          (m : ℝ) ≤ (1 - δ) * (optimalIndex b c p q σ n : ℝ) →
          let k := leftScaledComparisonIndex δ (optimalIndex b c p q σ n)
          ((k - m : ℕ) : ℝ) ≤ θ * (((n - k : ℕ) : ℝ)) := by
    filter_upwards [h_buffered, h_betaGapRatio] with n hn_buffered hβ_gap
    intro m hm_mem hm_scaled
    let β : ℕ := optimalIndex b c p q σ n
    let k : ℕ := leftScaledComparisonIndex δ β
    obtain ⟨_hk_mem, hm_lt_k, hk_lt_beta, _hk_gap_pos⟩ := hn_buffered hm_mem hm_scaled
    have hk_le_beta : k ≤ β := Nat.le_of_lt hk_lt_beta
    have hd_le_beta : (((k - m : ℕ) : ℝ)) ≤ (β : ℝ) := by
      have hnat : k - m ≤ β := le_trans (Nat.sub_le k m) hk_le_beta
      exact_mod_cast hnat
    have hgap_mono : (((n - β : ℕ) : ℝ)) ≤ (((n - k : ℕ) : ℝ)) := by
      exact_mod_cast (Nat.sub_le_sub_left hk_le_beta n)
    -- The buffered comparison window is bounded by the whole benchmark size,
    -- and the benchmark itself is eventually negligible relative to the gap.
    calc
      (((k - m : ℕ) : ℝ)) ≤ (β : ℝ) := hd_le_beta
      _ ≤ θ * (((n - β : ℕ) : ℝ)) := by simpa [β] using hβ_gap
      _ ≤ θ * (((n - k : ℕ) : ℝ)) := by gcongr
  filter_upwards [h_buffered, h_gapLower, h_upper, h_stepRatio] with n hn_buffered hn_gap hn_upper hn_step
  intro m hm_mem hm_scaled
  let k := leftScaledComparisonIndex δ (optimalIndex b c p q σ n)
  obtain ⟨hk_mem, hm_lt_k, _hk_lt_beta, _hk_gap_pos⟩ := hn_buffered hm_mem hm_scaled
  have hm_lt_n : m < n := (TsvdGcv.mem_gcvAdmissibleIndexSet_iff n m).1 hm_mem |>.2
  have hk_lt_n : k < n := (TsvdGcv.mem_gcvAdmissibleIndexSet_iff n k).1 hk_mem |>.2
  have hresk_nonneg :
      0 ≤ ((n : ℝ) ^ 2) * expectedResidualObjective μ K Rtsvd fTrue η n k := by
    exact mul_nonneg (by positivity)
      (expectedResidualObjective_nonneg μ K Rtsvd fTrue η n k)
  have hd_pos : 0 < (((k - m : ℕ) : ℝ)) := by
    exact_mod_cast (Nat.sub_pos_of_lt hm_lt_k)
  have hgapk_pos : 0 < (((n - k : ℕ) : ℝ)) := by
    exact_mod_cast (Nat.sub_pos_of_lt hk_lt_n)
  have hgapm_eq :
      (((n - m : ℕ) : ℝ)) = (((n - k : ℕ) : ℝ)) + (((k - m : ℕ) : ℝ)) := by
    have hnat : n - m = (n - k) + (k - m) := by
      omega
    exact_mod_cast hnat
  have hstrict :
      TsvdGcv.expectedObjective μ K Rtsvd fTrue η n k <
        TsvdGcv.expectedObjective μ K Rtsvd fTrue η n m := by
    -- Rewrite both GCV values to the common residual-over-gap quotient form and
    -- apply the abstract quotient comparison lemma.
    rw [gcvExpectedObjective_eq_gapResidualQuotient
      (μ := μ) (K := K) (Rtsvd := Rtsvd) (fTrue := fTrue) (η := η) (hm_lt := hk_lt_n),
      gcvExpectedObjective_eq_gapResidualQuotient
        (μ := μ) (K := K) (Rtsvd := Rtsvd) (fTrue := fTrue) (η := η) (hm_lt := hm_lt_n)]
    have hcore :=
      strictGcvComparison_of_gapResidualBounds
        (hσ_pos := h_σ)
        (hd_pos := hd_pos)
        (hgapk_pos := hgapk_pos)
        (hresk_nonneg := hresk_nonneg)
        (hθ_nonneg := le_of_lt hθ_pos)
        (h_upper := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using hn_upper hm_mem hm_scaled)
        (h_gap := hn_gap hm_mem hm_scaled)
        (h_stepRatio := hn_step hm_mem hm_scaled)
        (h_coeff := hcoeff)
    simpa [C, k, hgapm_eq]
      using hcore
  exact ⟨k, hk_mem, hstrict⟩

/-- Helper for Theorem 7.30: for each fixed `δ ∈ (0,1)`, any admissible TSVD
GCV index that stays left of `(1 - δ) * optimalIndex b c p q σ n` is
eventually beaten by another admissible comparison index.

This packages the left-scaled competitor interface needed by the final
minimizer contradiction and isolates the remaining analytic blocker from the
filter-level squeeze argument. -/
lemma gcvObjective_leftScaledComparison_eventually_lt
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (K : ℕ → H →L[ℝ] F)
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
    (h_length : ∀ n, (S n).length = ⊤)
    (fTrue : H)
    (b c p q σ δ : ℝ)
    (η : ℕ → Ω → F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (h_b : 0 < b)
    (h_c : 0 < c)
    (h_p : 1 < p)
    (h_q : 1 < q)
    (h_σ : 0 < σ)
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (h_noise_memLp : ∀ n, MeasureTheory.MemLp (η n) 2 μ)
    (h_noise_meanZero : ∀ n, ∫ ω, η n ω ∂μ = 0)
    (h_noise_modeVariance :
      ∀ n i,
        ∫ ω,
          (inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) i) : F) (η n ω)) ^ 2 ∂μ =
            σ ^ 2 / (n : ℝ))
    (h_singularDecay :
      ∀ n, (S n).HasAlgebraicSingularValueSquareDecay (h_length n) c p)
    (h_fourierDecay :
      ∀ n, (S n).HasAlgebraicFourierCoefficientSquareDecay (h_length n) fTrue b q)
    (h_tsvd : IsTsvdReconstructionFamily K S h_length Rtsvd)
    (h_optimalIndex_mem :
      ∀ᶠ n in Filter.atTop, optimalIndex b c p q σ n ∈ TsvdGcv.gcvAdmissibleIndexSet n) :
    ∀ᶠ n in Filter.atTop,
      ∀ {m : ℕ}, m ∈ TsvdGcv.gcvAdmissibleIndexSet n →
        (m : ℝ) ≤ (1 - δ) * (optimalIndex b c p q σ n : ℝ) →
        ∃ k ∈ TsvdGcv.gcvAdmissibleIndexSet n,
          TsvdGcv.expectedObjective μ K Rtsvd fTrue η n k <
            TsvdGcv.expectedObjective μ K Rtsvd fTrue η n m := by
  -- Route correction: the closing theorem is now just the abstract quotient
  -- assembly applied to the theorem-local buffered residual upper envelope.
  exact
    gcvObjective_leftScaledComparison_eventually_lt_of_upperEnvelope
      (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
      (b := b) (c := c) (p := p) (q := q) (σ := σ) (δ := δ) (η := η)
      (Rtsvd := Rtsvd) (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q)
      (h_σ := h_σ) (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
      (h_noise_memLp := h_noise_memLp)
      (h_noise_meanZero := h_noise_meanZero)
      (h_noise_modeVariance := h_noise_modeVariance)
      (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
      (h_tsvd := h_tsvd) (h_optimalIndex_mem := h_optimalIndex_mem)
      (h_upperEnvelope := by
        intro ε hε_pos
        exact
          leftScaledComparison_residualUpperEnvelopeSharp
            (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
            (b := b) (c := c) (p := p) (q := q) (σ := σ) (δ := δ) (ε := ε)
            (η := η) (Rtsvd := Rtsvd)
            (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
            (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one) (hε_pos := hε_pos)
            (h_noise_memLp := h_noise_memLp)
            (h_noise_meanZero := h_noise_meanZero)
            (h_noise_modeVariance := h_noise_modeVariance)
            (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
            (h_tsvd := h_tsvd) (h_optimalIndex_mem := h_optimalIndex_mem))

/-- Helper for Theorem 7.30: for each fixed `δ ∈ (0,1)`, an eventually
GCV-optimal family must eventually stay above `(1 - δ) * optimalIndex`.

This is the benchmark-comparison interface that replaces the broken adjacent
successor route. -/
lemma gcvOptimalFamily_eventually_ge_scaledOptimalIndex
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (K : ℕ → H →L[ℝ] F)
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
    (h_length : ∀ n, (S n).length = ⊤)
    (fTrue : H)
    (b c p q σ δ : ℝ)
    (η : ℕ → Ω → F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (mV : ℕ → ℕ)
    (h_b : 0 < b)
    (h_c : 0 < c)
    (h_p : 1 < p)
    (h_q : 1 < q)
    (h_σ : 0 < σ)
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (h_noise_memLp : ∀ n, MeasureTheory.MemLp (η n) 2 μ)
    (h_noise_meanZero : ∀ n, ∫ ω, η n ω ∂μ = 0)
    (h_noise_modeVariance :
      ∀ n i,
        ∫ ω,
          (inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) i) : F) (η n ω)) ^ 2 ∂μ =
            σ ^ 2 / (n : ℝ))
    (h_singularDecay :
      ∀ n, (S n).HasAlgebraicSingularValueSquareDecay (h_length n) c p)
    (h_fourierDecay :
      ∀ n, (S n).HasAlgebraicFourierCoefficientSquareDecay (h_length n) fTrue b q)
    (h_tsvd : IsTsvdReconstructionFamily K S h_length Rtsvd)
    (h_gcvOptimal : TsvdGcv.IsOptimalFamilyEventually μ K Rtsvd fTrue η mV)
    (h_optimalIndex_mem :
      ∀ᶠ n in Filter.atTop, optimalIndex b c p q σ n ∈ TsvdGcv.gcvAdmissibleIndexSet n) :
    ∀ᶠ n in Filter.atTop,
      (1 - δ) * (optimalIndex b c p q σ n : ℝ) ≤ (mV n : ℝ) := by
  have h_mem :
      ∀ᶠ n in Filter.atTop, mV n ∈ TsvdGcv.gcvAdmissibleIndexSet n :=
    TsvdGcv.IsOptimalFamilyEventually.eventually_mem h_gcvOptimal
  have h_min :
      ∀ᶠ n in Filter.atTop,
        IsMinOn
          (TsvdGcv.expectedObjective μ K Rtsvd fTrue η n)
          (TsvdGcv.gcvAdmissibleIndexSet n)
          (mV n) :=
    TsvdGcv.IsOptimalFamilyEventually.eventually_isMinOn h_gcvOptimal
  have h_strict :
      ∀ᶠ n in Filter.atTop,
        ∀ {m : ℕ}, m ∈ TsvdGcv.gcvAdmissibleIndexSet n →
          (m : ℝ) ≤ (1 - δ) * (optimalIndex b c p q σ n : ℝ) →
          ∃ k ∈ TsvdGcv.gcvAdmissibleIndexSet n,
            TsvdGcv.expectedObjective μ K Rtsvd fTrue η n k <
              TsvdGcv.expectedObjective μ K Rtsvd fTrue η n m :=
    gcvObjective_leftScaledComparison_eventually_lt
      (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
      (b := b) (c := c) (p := p) (q := q) (σ := σ) (δ := δ) (η := η)
      (Rtsvd := Rtsvd) (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q)
      (h_σ := h_σ) (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
      (h_noise_memLp := h_noise_memLp)
      (h_noise_meanZero := h_noise_meanZero)
      (h_noise_modeVariance := h_noise_modeVariance)
      (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
      (h_tsvd := h_tsvd) (h_optimalIndex_mem := h_optimalIndex_mem)
  -- Route correction: use the eventual left-scaled strict comparison directly
  -- against the eventual `IsMinOn` witness, rather than forcing a pointwise
  -- benchmark comparison through the blocked noise-floor algebra.
  filter_upwards [h_mem, h_min, h_strict] with n hn_mem hn_min hn_strict
  have hmin_compare :
      ∀ y ∈ TsvdGcv.gcvAdmissibleIndexSet n,
        TsvdGcv.expectedObjective μ K Rtsvd fTrue η n (mV n) ≤
          TsvdGcv.expectedObjective μ K Rtsvd fTrue η n y := by
    -- Unpack the eventual minimizer witness once before applying the strict
    -- left-scaled competitor.
    simpa [isMinOn_iff] using hn_min
  by_contra h_not_lower
  have hm_scaled :
      (mV n : ℝ) ≤ (1 - δ) * (optimalIndex b c p q σ n : ℝ) := by
    linarith
  obtain ⟨k, hk_mem, hk_lt⟩ := hn_strict hn_mem hm_scaled
  have h_le :
      TsvdGcv.expectedObjective μ K Rtsvd fTrue η n (mV n) ≤
        TsvdGcv.expectedObjective μ K Rtsvd fTrue η n k :=
    hmin_compare k hk_mem
  linarith

/-- Helper for Theorem 7.30: once the eventual GCV minimizer is trapped below
the benchmark and above every fixed sub-benchmark multiple, the ratio squeeze
gives asymptotic equivalence with the explicit benchmark profile. -/
theorem gcvOptimalFamily_ratio_tendsto_one
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (K : ℕ → H →L[ℝ] F)
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
    (h_length : ∀ n, (S n).length = ⊤)
    (fTrue : H)
    (b c p q σ : ℝ)
    (η : ℕ → Ω → F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (mV : ℕ → ℕ)
    (h_b : 0 < b)
    (h_c : 0 < c)
    (h_p : 1 < p)
    (h_q : 1 < q)
    (h_σ : 0 < σ)
    (h_noise_memLp : ∀ n, MeasureTheory.MemLp (η n) 2 μ)
    (h_noise_meanZero : ∀ n, ∫ ω, η n ω ∂μ = 0)
    (h_noise_modeVariance :
      ∀ n i,
        ∫ ω,
          (inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) i) : F) (η n ω)) ^ 2 ∂μ =
            σ ^ 2 / (n : ℝ))
    (h_singularDecay :
      ∀ n, (S n).HasAlgebraicSingularValueSquareDecay (h_length n) c p)
    (h_fourierDecay :
      ∀ n, (S n).HasAlgebraicFourierCoefficientSquareDecay (h_length n) fTrue b q)
    (h_tsvd : IsTsvdReconstructionFamily K S h_length Rtsvd)
    (h_gcvOptimal : TsvdGcv.IsOptimalFamilyEventually μ K Rtsvd fTrue η mV)
    (h_optimalIndex_mem :
      ∀ᶠ n in Filter.atTop, optimalIndex b c p q σ n ∈ TsvdGcv.gcvAdmissibleIndexSet n) :
    Asymptotics.IsEquivalent Filter.atTop
      (fun n ↦ (mV n : ℝ))
      (optimalIndexProfile b c p q σ) := by
  have h_upper :
      ∀ᶠ n in Filter.atTop, (mV n : ℝ) ≤ (optimalIndex b c p q σ n : ℝ) :=
    (gcvOptimalFamily_eventually_le_optimalIndex
      (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
      (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η)
      (Rtsvd := Rtsvd) (mV := mV) (h_b := h_b) (h_c := h_c) (h_p := h_p)
      (h_q := h_q) (h_σ := h_σ) (h_noise_memLp := h_noise_memLp)
      (h_noise_meanZero := h_noise_meanZero)
      (h_noise_modeVariance := h_noise_modeVariance)
      (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
      (h_tsvd := h_tsvd) (h_gcvOptimal := h_gcvOptimal)
      (h_optimalIndex_mem := h_optimalIndex_mem)).mono fun n hn ↦ by
        exact_mod_cast hn
  have h_beta_equiv :
      Asymptotics.IsEquivalent Filter.atTop
        (fun n ↦ (mV n : ℝ))
        (fun n ↦ (optimalIndex b c p q σ n : ℝ)) :=
    scaledOptimalIndexBounds_isEquivalent
      (b := b) (c := c) (p := p) (q := q) (σ := σ) (mV := mV)
      (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
      h_upper
      (fun δ hδ_pos hδ_lt_one ↦
        gcvOptimalFamily_eventually_ge_scaledOptimalIndex
          (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
          (b := b) (c := c) (p := p) (q := q) (σ := σ) (δ := δ) (η := η)
          (Rtsvd := Rtsvd) (mV := mV) (h_b := h_b) (h_c := h_c) (h_p := h_p)
          (h_q := h_q) (h_σ := h_σ) (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
          (h_noise_memLp := h_noise_memLp)
          (h_noise_meanZero := h_noise_meanZero)
          (h_noise_modeVariance := h_noise_modeVariance)
          (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
          (h_tsvd := h_tsvd) (h_gcvOptimal := h_gcvOptimal)
          (h_optimalIndex_mem := h_optimalIndex_mem))
  -- Compose the ratio squeeze against `optimalIndex` with the existing
  -- benchmark/profile equivalence.
  exact
    h_beta_equiv.trans
      (optimalIndexCast_isEquivalent_profile b c p q σ h_b h_c h_p h_q h_σ)

/-- Helper for Theorem 7.30: Theorem 7.16 packages the estimation-optimal
family `mE` into eventual agreement with the explicit benchmark together with
the eventual interior bounds needed to keep that benchmark inside the
denominator-valid GCV admissible set. -/
lemma estimationOptimalFamily_eventually_eq_optimalIndex_andInterior
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (K : ℕ → H →L[ℝ] F)
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
    (h_length : ∀ n, (S n).length = ⊤)
    (fTrue : H)
    (b c p q σ : ℝ)
    (η : ℕ → Ω → F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (mE : ℕ → ℕ)
    (h_b : 0 < b)
    (h_c : 0 < c)
    (h_p : 1 < p)
    (h_q : 1 < q)
    (h_σ : 0 < σ)
    (h_noise_memLp : ∀ n, MeasureTheory.MemLp (η n) 2 μ)
    (h_noise_meanZero : ∀ n, ∫ ω, η n ω ∂μ = 0)
    (h_noise_modeVariance :
      ∀ n i,
        ∫ ω,
          (inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) i) : F) (η n ω)) ^ 2 ∂μ =
            σ ^ 2 / (n : ℝ))
    (h_singularDecay :
      ∀ n, (S n).HasAlgebraicSingularValueSquareDecay (h_length n) c p)
    (h_fourierDecay :
      ∀ n, (S n).HasAlgebraicFourierCoefficientSquareDecay (h_length n) fTrue b q)
    (h_tsvd : IsTsvdReconstructionFamily K S h_length Rtsvd)
    (h_vanishingNullspaceComponent :
      FilterRegularization.HasVanishingNullspaceComponent K fTrue)
    (h_estOptimal :
      ParameterChoice.IsOptimalParameterFamily
        (expectedSqErrorObjective μ K Rtsvd fTrue η)
        𝒵
        mE) :
    ∀ᶠ n in Filter.atTop, mE n = optimalIndex b c p q σ n ∧ 0 < mE n ∧ mE n < n := by
  have h_eq :
      mE =ᶠ[Filter.atTop] optimalIndex b c p q σ :=
    optimalFamily_eq_optimalIndex_eventually
      (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
      (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η)
      (Rtsvd := Rtsvd) (mE := mE) (h_b := h_b) (h_c := h_c) (h_p := h_p)
      (h_q := h_q) (h_σ := h_σ) (h_noise_memLp := h_noise_memLp)
      (h_noise_meanZero := h_noise_meanZero)
      (h_noise_modeVariance := h_noise_modeVariance)
      (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
      (h_tsvd := h_tsvd) (h_estOptimal := h_estOptimal)
      h_vanishingNullspaceComponent
  have h_interior :
      ∀ᶠ n in Filter.atTop, 0 < mE n ∧ mE n < n :=
    optimalFamily_eventuallyAvoidsBoundary
      (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
      (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η)
      (Rtsvd := Rtsvd) (mE := mE) (h_b := h_b) (h_c := h_c) (h_p := h_p)
      (h_q := h_q) (h_σ := h_σ) (h_noise_memLp := h_noise_memLp)
      (h_noise_meanZero := h_noise_meanZero)
      (h_noise_modeVariance := h_noise_modeVariance)
      (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
      (h_tsvd := h_tsvd) (h_estOptimal := h_estOptimal)
      h_vanishingNullspaceComponent
  -- Bundle the benchmark identity and the eventual interiority into the single
  -- transport fact used by the GCV comparison route.
  filter_upwards [h_eq, h_interior] with n hn_eq hn_interior
  exact ⟨hn_eq, hn_interior.1, hn_interior.2⟩

/-- Helper for Theorem 7.30: Theorem 7.16 eventually places the benchmark
`optimalIndex b c p q σ n` inside the denominator-valid GCV admissible set. -/
lemma optimalIndex_eventually_mem_gcvAdmissible
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (K : ℕ → H →L[ℝ] F)
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
    (h_length : ∀ n, (S n).length = ⊤)
    (fTrue : H)
    (b c p q σ : ℝ)
    (η : ℕ → Ω → F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (mE : ℕ → ℕ)
    (h_b : 0 < b)
    (h_c : 0 < c)
    (h_p : 1 < p)
    (h_q : 1 < q)
    (h_σ : 0 < σ)
    (h_noise_memLp : ∀ n, MeasureTheory.MemLp (η n) 2 μ)
    (h_noise_meanZero : ∀ n, ∫ ω, η n ω ∂μ = 0)
    (h_noise_modeVariance :
      ∀ n i,
        ∫ ω,
          (inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) i) : F) (η n ω)) ^ 2 ∂μ =
            σ ^ 2 / (n : ℝ))
    (h_singularDecay :
      ∀ n, (S n).HasAlgebraicSingularValueSquareDecay (h_length n) c p)
    (h_fourierDecay :
      ∀ n, (S n).HasAlgebraicFourierCoefficientSquareDecay (h_length n) fTrue b q)
    (h_tsvd : IsTsvdReconstructionFamily K S h_length Rtsvd)
    (h_vanishingNullspaceComponent :
      FilterRegularization.HasVanishingNullspaceComponent K fTrue)
    (h_estOptimal :
      ParameterChoice.IsOptimalParameterFamily
        (expectedSqErrorObjective μ K Rtsvd fTrue η)
        𝒵
        mE) :
    ∀ᶠ n in Filter.atTop, optimalIndex b c p q σ n ∈ TsvdGcv.gcvAdmissibleIndexSet n := by
  have h_est_bridge :
      ∀ᶠ n in Filter.atTop, mE n = optimalIndex b c p q σ n ∧ 0 < mE n ∧ mE n < n :=
    estimationOptimalFamily_eventually_eq_optimalIndex_andInterior
      (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
      (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η)
      (Rtsvd := Rtsvd) (mE := mE) (h_b := h_b) (h_c := h_c) (h_p := h_p)
      (h_q := h_q) (h_σ := h_σ) (h_noise_memLp := h_noise_memLp)
      (h_noise_meanZero := h_noise_meanZero)
      (h_noise_modeVariance := h_noise_modeVariance)
      (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
      (h_tsvd := h_tsvd)
      (h_vanishingNullspaceComponent := h_vanishingNullspaceComponent)
      (h_estOptimal := h_estOptimal)
  -- Transport the eventual interiority of `mE` across its eventual equality
  -- with the benchmark floor formula.
  filter_upwards [h_est_bridge] with n hn
  rw [TsvdGcv.mem_gcvAdmissibleIndexSet_iff]
  refine ⟨?_, ?_⟩
  · exact ⟨Nat.zero_le _, Nat.le_of_lt <| by simpa [hn.1] using hn.2.2⟩
  · simpa [hn.1] using hn.2.2

/-- Helper for Theorem 7.30: the eventual GCV minimizer is asymptotically
equivalent to the estimation-optimal family once both are compared to the same
benchmark `optimalIndex b c p q σ`. -/
lemma gcvOptimalFamily_isEquivalent_estimationOptimalFamily
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (K : ℕ → H →L[ℝ] F)
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
    (h_length : ∀ n, (S n).length = ⊤)
    (fTrue : H)
    (b c p q σ : ℝ)
    (η : ℕ → Ω → F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (mV mE : ℕ → ℕ)
    (h_b : 0 < b)
    (h_c : 0 < c)
    (h_p : 1 < p)
    (h_q : 1 < q)
    (h_σ : 0 < σ)
    (h_noise_memLp : ∀ n, MeasureTheory.MemLp (η n) 2 μ)
    (h_noise_meanZero : ∀ n, ∫ ω, η n ω ∂μ = 0)
    (h_noise_modeVariance :
      ∀ n i,
        ∫ ω,
          (inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) i) : F) (η n ω)) ^ 2 ∂μ =
            σ ^ 2 / (n : ℝ))
    (h_singularDecay :
      ∀ n, (S n).HasAlgebraicSingularValueSquareDecay (h_length n) c p)
    (h_fourierDecay :
      ∀ n, (S n).HasAlgebraicFourierCoefficientSquareDecay (h_length n) fTrue b q)
    (h_tsvd : IsTsvdReconstructionFamily K S h_length Rtsvd)
    (h_vanishingNullspaceComponent :
      FilterRegularization.HasVanishingNullspaceComponent K fTrue)
    (h_gcvOptimal : TsvdGcv.IsOptimalFamilyEventually μ K Rtsvd fTrue η mV)
    (h_estOptimal :
      ParameterChoice.IsOptimalParameterFamily
        (expectedSqErrorObjective μ K Rtsvd fTrue η)
        𝒵
        mE) :
    Asymptotics.IsEquivalent Filter.atTop
      (fun n ↦ (mV n : ℝ))
      (fun n ↦ (mE n : ℝ)) := by
  have h_est_bridge :
      ∀ᶠ n in Filter.atTop, mE n = optimalIndex b c p q σ n ∧ 0 < mE n ∧ mE n < n :=
    estimationOptimalFamily_eventually_eq_optimalIndex_andInterior
      (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
      (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η)
      (Rtsvd := Rtsvd) (mE := mE) (h_b := h_b) (h_c := h_c) (h_p := h_p)
      (h_q := h_q) (h_σ := h_σ) (h_noise_memLp := h_noise_memLp)
      (h_noise_meanZero := h_noise_meanZero)
      (h_noise_modeVariance := h_noise_modeVariance)
      (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
      (h_tsvd := h_tsvd)
      (h_vanishingNullspaceComponent := h_vanishingNullspaceComponent)
      (h_estOptimal := h_estOptimal)
  have h_optimalIndex_mem :
      ∀ᶠ n in Filter.atTop, optimalIndex b c p q σ n ∈ TsvdGcv.gcvAdmissibleIndexSet n :=
    optimalIndex_eventually_mem_gcvAdmissible
      (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
      (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η)
      (Rtsvd := Rtsvd) (mE := mE) (h_b := h_b) (h_c := h_c) (h_p := h_p)
      (h_q := h_q) (h_σ := h_σ) (h_noise_memLp := h_noise_memLp)
      (h_noise_meanZero := h_noise_meanZero)
      (h_noise_modeVariance := h_noise_modeVariance)
      (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
      (h_tsvd := h_tsvd)
      (h_vanishingNullspaceComponent := h_vanishingNullspaceComponent)
      (h_estOptimal := h_estOptimal)
  have h_mV_profile :
      Asymptotics.IsEquivalent Filter.atTop
        (fun n ↦ (mV n : ℝ))
        (optimalIndexProfile b c p q σ) :=
    gcvOptimalFamily_ratio_tendsto_one
      (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
      (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η)
      (Rtsvd := Rtsvd) (mV := mV) (h_b := h_b) (h_c := h_c) (h_p := h_p)
      (h_q := h_q) (h_σ := h_σ) (h_noise_memLp := h_noise_memLp)
      (h_noise_meanZero := h_noise_meanZero)
      (h_noise_modeVariance := h_noise_modeVariance)
      (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
      (h_tsvd := h_tsvd) (h_gcvOptimal := h_gcvOptimal)
      (h_optimalIndex_mem := h_optimalIndex_mem)
  have h_mV_beta :
      Asymptotics.IsEquivalent Filter.atTop
        (fun n ↦ (mV n : ℝ))
        (fun n ↦ (optimalIndex b c p q σ n : ℝ)) :=
    h_mV_profile.trans
      (optimalIndexCast_isEquivalent_profile b c p q σ h_b h_c h_p h_q h_σ).symm
  have h_mE_eq_beta :
      (fun n ↦ (mE n : ℝ)) =ᶠ[Filter.atTop]
        (fun n ↦ (optimalIndex b c p q σ n : ℝ)) := by
    filter_upwards [h_est_bridge] with n hn
    simp [hn.1]
  -- Transport the common benchmark profile back to the estimation-optimal
  -- family using Theorem 7.16's eventual equality.
  exact h_mV_beta.trans_eventuallyEq h_mE_eq_beta.symm

/-- Theorem 7.30 (GCV for TSVD Regularization). Main labeled
source-facing entry.

Under the Chapter 7 positivity, semistochastic white-noise, algebraic decay,
vanishing-nullspace, and TSVD reconstruction hypotheses, if `mV` is an
eventually optimal family for the expected TSVD GCV objective on the
denominator-valid truncation-index set and `mE` minimizes the expected squared
estimation-error objective on `𝒵(n)`, then `mV` is asymptotically equivalent
to `mE` as `n → ∞`; here the vanishing-nullspace assumption is the Chapter 7
side condition that identifies the estimation-error minimizer with the
benchmark formula `(7.63)`. -/
theorem isAsymptoticallyOptimal_of_gcvOptimalFamily
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (K : ℕ → H →L[ℝ] F)
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
    (h_length : ∀ n, (S n).length = ⊤)
    (fTrue : H) (b c p q σ : ℝ)
    (η : ℕ → Ω → F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (mV mE : ℕ → ℕ)
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q) (h_σ : 0 < σ)
    (h_noise_memLp : ∀ n, MeasureTheory.MemLp (η n) 2 μ)
    (h_noise_meanZero : ∀ n, ∫ ω, η n ω ∂μ = 0)
    (h_noise_modeVariance :
      ∀ n i,
        ∫ ω,
          (inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) i) : F) (η n ω)) ^ 2 ∂μ =
            σ ^ 2 / (n : ℝ))
    (h_singularDecay :
      ∀ n, (S n).HasAlgebraicSingularValueSquareDecay (h_length n) c p)
    (h_fourierDecay :
      ∀ n, (S n).HasAlgebraicFourierCoefficientSquareDecay (h_length n) fTrue b q)
    (h_tsvd : IsTsvdReconstructionFamily K S h_length Rtsvd)
    (h_vanishingNullspaceComponent :
      FilterRegularization.HasVanishingNullspaceComponent K fTrue)
    (h_gcvOptimal : TsvdGcv.IsOptimalFamilyEventually μ K Rtsvd fTrue η mV)
    (h_estOptimal :
      ParameterChoice.IsOptimalParameterFamily
        (expectedSqErrorObjective μ K Rtsvd fTrue η)
        𝒵
        mE) :
    ParameterChoice.IsAsymptoticallyOptimal
      (fun n ↦ mV n)
      (fun n ↦ mE n) := by
  have h_equiv :
      Asymptotics.IsEquivalent Filter.atTop
        (fun n ↦ (mV n : ℝ))
        (fun n ↦ (mE n : ℝ)) :=
    gcvOptimalFamily_isEquivalent_estimationOptimalFamily
      (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
      (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η)
      (Rtsvd := Rtsvd) (mV := mV) (mE := mE) (h_b := h_b) (h_c := h_c)
      (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
      (h_noise_memLp := h_noise_memLp)
      (h_noise_meanZero := h_noise_meanZero)
      (h_noise_modeVariance := h_noise_modeVariance)
      (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
      (h_tsvd := h_tsvd)
      (h_vanishingNullspaceComponent := h_vanishingNullspaceComponent)
      (h_gcvOptimal := h_gcvOptimal) (h_estOptimal := h_estOptimal)
  -- Route correction: the file now imports the canonical Remark 7.17 bridge
  -- directly, so the final step is just the owner-level API application.
  exact parameterChoiceIsAsymptoticallyOptimalOfIsEquivalent h_equiv

end

end TsvdEstimation

end
