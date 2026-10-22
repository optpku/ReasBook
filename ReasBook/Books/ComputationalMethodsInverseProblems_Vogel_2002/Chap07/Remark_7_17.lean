/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Definition_7_33
import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_17.AsymptoticOptimalBridge
import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_17.OptimalIndexProfile
import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_17.OptimalParameter
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-- Helper for Remark 7.17: package a positive constant and the corresponding
equivalence as `ParameterChoice.IsOrderOptimalWith`. -/
theorem parameterChoiceIsOrderOptimalWithOf
    {r : ℝ} {α αopt : ℕ → ℝ}
    (h : 0 < r ∧ Asymptotics.IsEquivalent Filter.atTop α (fun n ↦ r * αopt n)) :
    ParameterChoice.IsOrderOptimalWith r α αopt := by
  -- Use the exposed owner-facing equivalence instead of reopening the wrapper
  -- definition in this downstream file.
  exact (ParameterChoice.IsOrderOptimalWith_iff r α αopt).2 h

section

noncomputable section

namespace TsvdEstimation

/-- Helper for Remark 7.17: the TSVD index profile is pointwise nonnegative. -/
private theorem optimalIndexProfile_nonneg
    (b c p q σ : ℝ)
    (h_b : 0 < b) (h_c : 0 < c) (h_σ : 0 < σ) :
    ∀ n, 0 ≤ optimalIndexProfile b c p q σ n := by
  -- Both factors in the explicit profile are nonnegative real powers of nonnegative bases.
  intro n
  change 0 ≤ ((b * c) ^ (1 / (p + q))) * (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q))))
  positivity

/-- Helper for Remark 7.17: the transported power-law profile matches the owned
benchmark sequence exactly. -/
private theorem optimalFilterProfile_eq_parameterBenchmark
    (b c p q σ : ℝ)
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q)
    (n : ℕ) :
    c * (optimalIndexProfile b c p q σ n ^ (-p)) =
      parameterBenchmark b c p q σ n := by
  have hpq_pos : 0 < p + q := by
    linarith
  have hpq_ne : p + q ≠ 0 := ne_of_gt hpq_pos
  have h_profile_base_nonneg : 0 ≤ ((b * c) ^ (1 / (p + q))) := by
    positivity
  have h_ratio_nonneg : 0 ≤ ((σ ^ 2) / (n : ℝ)) := by
    positivity
  have h_ratio_power_nonneg : 0 ≤ (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q)))) := by
    positivity
  have hb_nonneg : 0 ≤ b := le_of_lt h_b
  have hc_nonneg : 0 ≤ c := le_of_lt h_c
  -- Normalize the explicit profile to the owned benchmark constant and rate.
  rw [parameterBenchmark_def, parameterConstant_def, optimalIndexProfile]
  calc
    c * ((((b * c) ^ (1 / (p + q))) * (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q))))) ^ (-p))
        =
          c *
            (((b * c) ^ (1 / (p + q))) ^ (-p) *
              (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q)))) ^ (-p)) := by
          congr 1
          exact Real.mul_rpow h_profile_base_nonneg h_ratio_power_nonneg
    _ =
          c *
            ((b * c) ^ ((1 / (p + q)) * (-p)) *
              ((σ ^ 2) / (n : ℝ)) ^ ((-(1 / (p + q))) * (-p))) := by
          congr 1
          rw [← Real.rpow_mul (x := b * c) (by positivity) (1 / (p + q)) (-p)]
          rw [← Real.rpow_mul (x := (σ ^ 2) / (n : ℝ)) h_ratio_nonneg (-(1 / (p + q))) (-p)]
    _ =
          c *
            ((b * c) ^ (-(p / (p + q))) *
              ((σ ^ 2) / (n : ℝ)) ^ (p / (p + q))) := by
          congr 2
          · congr 1
            field_simp [hpq_ne]
          · congr 1
            field_simp [hpq_ne]
    _ =
          c *
            (b ^ (-(p / (p + q))) * c ^ (-(p / (p + q))) *
              ((σ ^ 2) / (n : ℝ)) ^ (p / (p + q))) := by
          rw [Real.mul_rpow hb_nonneg hc_nonneg]
    _ =
          (c * c ^ (-(p / (p + q))) * b ^ (-(p / (p + q)))) *
            ((σ ^ 2) / (n : ℝ)) ^ (p / (p + q)) := by
          ring
    _ =
          (c ^ (q / (p + q)) * b ^ (-(p / (p + q)))) *
            ((σ ^ 2) / (n : ℝ)) ^ (p / (p + q)) := by
          congr 1
          calc
            c * c ^ (-(p / (p + q))) * b ^ (-(p / (p + q)))
                = (c ^ (1 : ℝ) * c ^ (-(p / (p + q)))) * b ^ (-(p / (p + q))) := by
                    rw [Real.rpow_one]
            _ = c ^ ((1 : ℝ) + -(p / (p + q))) * b ^ (-(p / (p + q))) := by
                    rw [← Real.rpow_add h_c]
            _ = c ^ (q / (p + q)) * b ^ (-(p / (p + q))) := by
                    have hexp : (1 : ℝ) + -(p / (p + q)) = q / (p + q) := by
                      field_simp [hpq_ne]
                      ring_nf
                    rw [hexp]
    _ =
          ((c ^ q / b ^ p) ^ (1 / (p + q))) *
            ((σ ^ 2) / (n : ℝ)) ^ (p / (p + q)) := by
          congr 1
          calc
            c ^ (q / (p + q)) * b ^ (-(p / (p + q)))
                = c ^ (q * (1 / (p + q))) * b ^ (-(p / (p + q))) := by
                    congr 1
                    ring
            _ = (c ^ q) ^ (1 / (p + q)) * b ^ (-(p / (p + q))) := by
                    rw [← Real.rpow_mul hc_nonneg]
            _ = (c ^ q) ^ (1 / (p + q)) / (b ^ p) ^ (1 / (p + q)) := by
                    have hdiv :
                        (c ^ q) ^ (1 / (p + q)) / b ^ (p * (1 / (p + q))) =
                          (c ^ q) ^ (1 / (p + q)) * (b ^ (p * (1 / (p + q))))⁻¹ := by
                      rw [div_eq_mul_inv]
                    rw [← Real.rpow_mul hb_nonneg]
                    have hneg :
                        b ^ (-(p / (p + q))) = (b ^ (p * (1 / (p + q))))⁻¹ := by
                      rw [show p / (p + q) = p * (1 / (p + q)) by ring]
                      simpa using (Real.rpow_neg hb_nonneg (p * (1 / (p + q))))
                    rw [hneg]
                    exact hdiv.symm
            _ = (c ^ q / b ^ p) ^ (1 / (p + q)) := by
                    rw [← Real.div_rpow (by positivity) (by positivity)]

/-- Helper for Remark 7.17: the explicit TSVD benchmark constant is positive. -/
private theorem parameterConstant_pos
    (b c p q : ℝ)
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q) :
    0 < parameterConstant b c p q := by
  -- Expand the constant and use positivity of the base of the real power.
  have hpq_pos : 0 < p + q := by
    linarith
  rw [parameterConstant_def]
  positivity

/-- Remark 7.17. Because `α ≈ c * m^(-p)` and the optimal truncation index is
given by `(7.63)`, the TSVD optimal filter parameter is asymptotically
optimal relative to the explicit benchmark sequence from `(7.65)`. -/
theorem optimalFilterParameter_isAsymptoticallyOptimal
    (b c p q σ : ℝ)
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q) (h_σ : 0 < σ) :
    ParameterChoice.IsAsymptoticallyOptimal
      (optimalFilterParameter b c p q σ)
      (parameterBenchmark b c p q σ) := by
  have h_profile_nonneg :
      0 ≤ optimalIndexProfile b c p q σ := by
    exact optimalIndexProfile_nonneg b c p q σ h_b h_c h_σ
  have h_index_profile :
      Asymptotics.IsEquivalent Filter.atTop
        (fun n ↦ (optimalIndex b c p q σ n : ℝ))
        (optimalIndexProfile b c p q σ) :=
    optimalIndexCast_isEquivalent_profile b c p q σ h_b h_c h_p h_q h_σ
  have h_power_profile :
      Asymptotics.IsEquivalent Filter.atTop
        (fun n ↦ ((optimalIndex b c p q σ n : ℝ) ^ (-p)))
        (fun n ↦ optimalIndexProfile b c p q σ n ^ (-p)) :=
    Asymptotics.IsEquivalent.rpow h_profile_nonneg h_index_profile
  have h_scaled_profile :
      Asymptotics.IsEquivalent Filter.atTop
        (((fun _ : ℕ ↦ c) * fun n ↦ (optimalIndex b c p q σ n : ℝ) ^ (-p)))
        (((fun _ : ℕ ↦ c) * fun n ↦ optimalIndexProfile b c p q σ n ^ (-p))) := by
    -- Multiply the powered asymptotic by the prefactor `c` appearing in the TSVD filter law.
    have h_const :
        Asymptotics.IsEquivalent Filter.atTop (fun _ : ℕ ↦ c) (fun _ : ℕ ↦ c) :=
      Asymptotics.IsEquivalent.refl
    exact h_const.mul h_power_profile
  have h_core :
      Asymptotics.IsEquivalent Filter.atTop
        (fun n ↦ c * ((optimalIndex b c p q σ n : ℝ) ^ (-p)))
        (parameterBenchmark b c p q σ) :=
    (h_scaled_profile.congr_left <|
      Filter.Eventually.of_forall fun n ↦ rfl).congr_right <|
        Filter.Eventually.of_forall
          (optimalFilterProfile_eq_parameterBenchmark b c p q σ h_b h_c h_p h_q)
  have h_def :
      optimalFilterParameter b c p q σ =ᶠ[Filter.atTop]
        (fun n ↦ c * ((optimalIndex b c p q σ n : ℝ) ^ (-p))) := by
    exact Filter.Eventually.of_forall (optimalFilterParameter_def b c p q σ)
  have h_result :
      Asymptotics.IsEquivalent Filter.atTop
        (optimalFilterParameter b c p q σ)
        (parameterBenchmark b c p q σ) := by
    -- Replace the left-hand side by the owned TSVD filter-parameter definition.
    exact (h_core.symm.trans_eventuallyEq h_def.symm).symm
  exact parameterChoiceIsAsymptoticallyOptimalOfIsEquivalent h_result

/-- Companion form of `optimalFilterParameter_isAsymptoticallyOptimal` using
the underlying asymptotic-equivalence owner. -/
theorem optimalFilterParameter_isEquivalent_benchmark
    (b c p q σ : ℝ)
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q) (h_σ : 0 < σ) :
    Asymptotics.IsEquivalent Filter.atTop
      (optimalFilterParameter b c p q σ)
      (parameterBenchmark b c p q σ) := by
  exact ParameterChoice.IsAsymptoticallyOptimal.isEquivalent
    (optimalFilterParameter_isAsymptoticallyOptimal b c p q σ h_b h_c h_p h_q h_σ)

/-- The TSVD optimal filter parameter is order-optimal with constant
`parameterConstant b c p q` relative to the power-law rate
`fun n ↦ ((σ ^ 2) / (n : ℝ)) ^ (p / (p + q))`. -/
theorem optimalFilterParameter_isOrderOptimalWith
    (b c p q σ : ℝ)
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q) (h_σ : 0 < σ) :
    ParameterChoice.IsOrderOptimalWith
      (parameterConstant b c p q)
      (optimalFilterParameter b c p q σ)
      (fun n ↦ ((σ ^ 2) / (n : ℝ)) ^ (p / (p + q))) := by
  have hOrder :
      0 < parameterConstant b c p q ∧
        Asymptotics.IsEquivalent Filter.atTop
          (optimalFilterParameter b c p q σ)
          (fun n ↦ parameterConstant b c p q * (((σ ^ 2) / (n : ℝ)) ^ (p / (p + q)))) := by
    -- Pair the positive TSVD constant with the already-established benchmark equivalence.
    refine ⟨parameterConstant_pos b c p q h_b h_c h_p h_q, ?_⟩
    have h_benchmark :
        Asymptotics.IsEquivalent Filter.atTop
          (optimalFilterParameter b c p q σ)
          (parameterBenchmark b c p q σ) :=
      optimalFilterParameter_isEquivalent_benchmark b c p q σ h_b h_c h_p h_q h_σ
    have h_benchmark_def :
        parameterBenchmark b c p q σ =ᶠ[Filter.atTop]
          (fun n ↦ parameterConstant b c p q * (((σ ^ 2) / (n : ℝ)) ^ (p / (p + q)))) := by
      exact Filter.Eventually.of_forall (parameterBenchmark_def b c p q σ)
    exact h_benchmark.trans_eventuallyEq h_benchmark_def
  exact parameterChoiceIsOrderOptimalWithOf hOrder

end TsvdEstimation

end

end
