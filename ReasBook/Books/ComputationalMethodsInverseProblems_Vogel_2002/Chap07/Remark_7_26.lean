/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Definition_7_33
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_15.OptimalIndex
import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_17.OptimalIndexProfile
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_25.Benchmark
public import Mathlib.Analysis.Asymptotics.Theta

open scoped Asymptotics

public section

noncomputable section

namespace TsvdEstimation

/-- Helper for the discrepancy comparison: the explicit optimal-index profile is
the discrepancy benchmark scaled by the factor `(p + q - 1) ^ (1 / (p + q))`. -/
private theorem optimalIndexProfile_eq_scaled_discrepancyBenchmark
    (b c p q σ : ℝ)
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q) :
    optimalIndexProfile b c p q σ =
      fun n ↦
        ((p + q - 1) ^ (1 / (p + q))) *
          TsvdDiscrepancy.indexBenchmark b c p q σ n := by
  have hpq_sub_pos : 0 < p + q - 1 := by
    linarith
  have hbc_nonneg : 0 ≤ b * c := by
    positivity
  ext n
  rw [optimalIndexProfile_def]
  rw [TsvdDiscrepancy.indexBenchmark_def, TsvdDiscrepancy.indexConstant_def]
  calc
    ((b * c) ^ (1 / (p + q))) * (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q))))
        =
          ((((p + q - 1) ^ (1 / (p + q))) * (((b * c) / (p + q - 1)) ^ (1 / (p + q)))) *
            (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q))))) := by
          congr 1
          symm
          calc
            (p + q - 1) ^ (1 / (p + q)) * ((b * c) / (p + q - 1)) ^ (1 / (p + q))
                = ((p + q - 1) * ((b * c) / (p + q - 1))) ^ (1 / (p + q)) := by
                    symm
                    exact Real.mul_rpow (show 0 ≤ p + q - 1 by positivity) (by positivity)
            _ = (b * c) ^ (1 / (p + q)) := by
                    congr 1
                    field_simp [show p + q - 1 ≠ 0 by linarith]
    _ =
          ((p + q - 1) ^ (1 / (p + q))) *
            (((b * c) / (p + q - 1)) ^ (1 / (p + q)) *
              (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q))))) := by
          ring

/-- Remark 7.26. The estimation-error minimizing TSVD truncation index from
`(7.63)` is order-optimal with factor `(p + q - 1) ^ (1 / (p + q))` relative
to the discrepancy-principle benchmark from `(7.89)`, for `p, q > 1`. The
source commentary about smaller truncation and an overly smooth regularized
solution is retained as prose rather than formalized as an additional theorem. -/
theorem optimalIndex_isOrderOptimalWith_discrepancyBenchmark
    (b c p q σ : ℝ)
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q) (h_σ : 0 < σ) :
    ParameterChoice.IsOrderOptimalWith
      ((p + q - 1) ^ (1 / (p + q)))
      (fun n ↦ (optimalIndex b c p q σ n : ℝ))
      (TsvdDiscrepancy.indexBenchmark b c p q σ) := by
  have h_factor_pos : 0 < (p + q - 1) ^ (1 / (p + q)) := by
    have hpq_sub_pos : 0 < p + q - 1 := by
      linarith
    positivity
  refine (ParameterChoice.IsOrderOptimalWith_iff _ _ _).2 ?_
  refine ⟨h_factor_pos, ?_⟩
  have h_profile :
      Asymptotics.IsEquivalent Filter.atTop
        (fun n ↦ (optimalIndex b c p q σ n : ℝ))
        (optimalIndexProfile b c p q σ) :=
    optimalIndexCast_isEquivalent_profile b c p q σ h_b h_c h_p h_q h_σ
  have h_scaled :
      optimalIndexProfile b c p q σ =ᶠ[Filter.atTop]
        (fun n ↦
          ((p + q - 1) ^ (1 / (p + q))) * TsvdDiscrepancy.indexBenchmark b c p q σ n) := by
    exact Filter.Eventually.of_forall
      (congrFun
        (optimalIndexProfile_eq_scaled_discrepancyBenchmark b c p q σ h_b h_c h_p h_q))
  exact h_profile.trans_eventuallyEq h_scaled

/-- The estimation-error minimizing TSVD truncation index from `(7.63)` has the
same raw `=Θ` rate as the discrepancy-principle benchmark from `(7.89)`. -/
theorem optimalIndex_isTheta_discrepancyBenchmark
    (b c p q σ : ℝ)
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q) (h_σ : 0 < σ) :
    (fun n ↦ (optimalIndex b c p q σ n : ℝ)) =Θ[Filter.atTop]
      TsvdDiscrepancy.indexBenchmark b c p q σ := by
  have h_order :
      ParameterChoice.IsOrderOptimalWith
        ((p + q - 1) ^ (1 / (p + q)))
        (fun n ↦ (optimalIndex b c p q σ n : ℝ))
        (TsvdDiscrepancy.indexBenchmark b c p q σ) :=
    optimalIndex_isOrderOptimalWith_discrepancyBenchmark b c p q σ h_b h_c h_p h_q h_σ
  have h_scaled :
      (fun n ↦ (optimalIndex b c p q σ n : ℝ)) =Θ[Filter.atTop]
        (fun n ↦ ((p + q - 1) ^ (1 / (p + q))) * TsvdDiscrepancy.indexBenchmark b c p q σ n) :=
    (ParameterChoice.IsOrderOptimalWith.isEquivalent h_order).isTheta
  have h_const_ne : ((p + q - 1) ^ (1 / (p + q))) ≠ 0 := ne_of_gt <| by
    have hpq_sub_pos : 0 < p + q - 1 := by
      linarith
    positivity
  exact (Asymptotics.isTheta_const_mul_right h_const_ne).1 h_scaled

end TsvdEstimation

end
