/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Definition_15_40
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Lemma_15_30

-- This item file is kept standalone so it does not inherit the current Chapter 15 CLT breakages.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology

universe u

noncomputable section

variable {Ω : Type u} [MeasurableSpace Ω]

namespace RealRandomVariableArray

section

variable (A : RealRandomVariableArray Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable [A.IsCentered μ] [A.IsNormed μ]

/-- Lemma 15.45: for every row `n` and every `t : ℝ`, the summed entry characteristic-function
defects satisfy `∑ i, ‖charFun (μ.map (A n i)) t - 1‖ ≤ t^2 / 2`. -/
theorem sumNormEntryCharFunSubOne_le_halfSq
    (n : ℕ) (t : ℝ) :
    ∑ i : Fin (A.rowLength n), ‖charFun (μ.map (A n i)) t - 1‖ ≤ t ^ (2 : ℕ) / 2 := by
  -- Proof comment: bound each entry defect by the quadratic Taylor remainder and then sum the
  -- resulting variance contributions across the row.
  calc
    ∑ i : Fin (A.rowLength n), ‖charFun (μ.map (A n i)) t - 1‖
        ≤ ∑ i : Fin (A.rowLength n), (t ^ (2 : ℕ) / 2) * Var[A n i; μ] := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          have hExpKernelMeas :
              Measurable (fun ω ↦ Complex.exp (t * A n i ω * Complex.I)) := by
            refine Complex.measurable_exp.comp ?_
            simpa using
              (Complex.measurable_ofReal.comp ((A.measurable_entry n i).const_mul t)).mul_const
                Complex.I
          have hExpInt :
              Integrable (fun ω ↦ Complex.exp (t * A n i ω * Complex.I) - 1) μ := by
            refine Integrable.of_bound (hExpKernelMeas.sub measurable_const).aestronglyMeasurable
              2 ?_
            filter_upwards with ω
            have htri :
                ‖Complex.exp (t * A n i ω * Complex.I) - 1‖ ≤
                  ‖Complex.exp (t * A n i ω * Complex.I)‖ + ‖(1 : ℂ)‖ := by
              simpa using norm_sub_le (Complex.exp (t * A n i ω * Complex.I)) (1 : ℂ)
            have hexp_norm : ‖Complex.exp (t * A n i ω * Complex.I)‖ = 1 := by
              simpa [mul_assoc, mul_left_comm, mul_comm] using
                Complex.norm_exp_ofReal_mul_I (t * A n i ω)
            have hbound : ‖Complex.exp (t * A n i ω * Complex.I)‖ + ‖(1 : ℂ)‖ ≤ 2 := by
              norm_num [hexp_norm]
            exact le_trans htri hbound
          have hEntryInt :
              Integrable (fun ω ↦ (A n i ω : ℂ)) μ :=
            (RealRandomVariableArray.IsCentered.integrable (A := A) (μ := μ) n i).ofReal
          have hLinearInt :
              Integrable (fun ω ↦ Complex.I * (t * A n i ω : ℝ)) μ := by
            have hConst :
                Integrable (fun ω ↦ (Complex.I * (t : ℂ)) * (A n i ω : ℂ)) μ :=
              hEntryInt.const_mul (Complex.I * (t : ℂ))
            simpa [mul_assoc, mul_left_comm, mul_comm] using hConst
          have hMeanZero :
              ∫ ω, Complex.I * (t * A n i ω : ℝ) ∂μ = 0 := by
            have hOfReal :
                ∫ ω, (A n i ω : ℂ) ∂μ = ((∫ ω, A n i ω ∂μ : ℝ) : ℂ) := by
              simpa using (integral_ofReal (μ := μ) (f := fun ω ↦ A n i ω))
            calc
              ∫ ω, Complex.I * (t * A n i ω : ℝ) ∂μ =
                  ∫ ω, (Complex.I * (t : ℂ)) * (A n i ω : ℂ) ∂μ := by
                    congr with ω
                    simp [mul_assoc]
              _ = (Complex.I * (t : ℂ)) * ∫ ω, (A n i ω : ℂ) ∂μ := by
                    simpa using
                      (integral_const_mul (μ := μ) (Complex.I * (t : ℂ))
                        (fun ω ↦ (A n i ω : ℂ)))
              _ = (Complex.I * (t : ℂ)) * ((∫ ω, A n i ω ∂μ : ℝ) : ℂ) := by
                    rw [hOfReal]
              _ = 0 := by
                    simp [RealRandomVariableArray.IsCentered.expectation_eq_zero
                      (A := A) (μ := μ) n i]
          have hExpKernelInt :
              Integrable (fun ω ↦ Complex.exp (t * A n i ω * Complex.I)) μ := by
            refine Integrable.of_bound hExpKernelMeas.aestronglyMeasurable 1 ?_
            exact Filter.Eventually.of_forall fun ω ↦ by
              simpa [mul_assoc, mul_left_comm, mul_comm] using
                (Complex.norm_exp_ofReal_mul_I (t * A n i ω)).le
          have hKernelMap :
              AEStronglyMeasurable (fun x : ℝ ↦ Complex.exp (t * x * Complex.I))
                (Measure.map (A n i) μ) := by
            refine (Complex.measurable_exp.comp ?_).aestronglyMeasurable
            simpa using
              (Complex.measurable_ofReal.comp (measurable_const.mul measurable_id)).mul_const
                Complex.I
          have hRemainderEq :
              charFun (μ.map (A n i)) t - 1 =
                ∫ ω,
                  (Complex.exp (t * A n i ω * Complex.I) - 1 -
                    Complex.I * (t * A n i ω : ℝ)) ∂μ := by
            calc
              charFun (μ.map (A n i)) t - 1 =
                  ∫ ω, Complex.exp (t * A n i ω * Complex.I) ∂μ - 1 := by
                    rw [MeasureTheory.charFun_apply_real]
                    rw [integral_map (A.measurable_entry n i).aemeasurable hKernelMap]
              _ = ∫ ω, Complex.exp (t * A n i ω * Complex.I) ∂μ - ∫ x, (1 : ℂ) ∂μ := by
                    rw [integral_const]
                    simp
              _ = ∫ ω, (Complex.exp (t * A n i ω * Complex.I) - 1) ∂μ := by
                    symm
                    rw [integral_sub hExpKernelInt (integrable_const 1)]
              _ =
                  ∫ ω, (Complex.exp (t * A n i ω * Complex.I) - 1) ∂μ -
                    ∫ ω, Complex.I * (t * A n i ω : ℝ) ∂μ := by
                      rw [hMeanZero, sub_zero]
              _ = ∫ ω,
                    (Complex.exp (t * A n i ω * Complex.I) - 1 -
                      Complex.I * (t * A n i ω : ℝ)) ∂μ := by
                      symm
                      rw [integral_sub hExpInt hLinearInt]
          rw [hRemainderEq]
          let g : Ω → ℝ := fun ω ↦ |t * A n i ω| ^ (2 : ℕ) / 2
          have hg_eq :
              g = fun ω ↦ (t ^ (2 : ℕ) / 2) * (A n i ω) ^ (2 : ℕ) := by
            funext ω
            dsimp [g]
            have hsq :
                |t * A n i ω| ^ (2 : ℕ) = t ^ (2 : ℕ) * (A n i ω) ^ (2 : ℕ) := by
              rw [abs_mul, mul_pow, sq_abs, sq_abs]
            exact by
              simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
                congrArg (fun x : ℝ ↦ x / 2) hsq
          have hg : Integrable g μ := by
            rw [hg_eq]
            have hsqInt : Integrable (fun ω ↦ (A n i ω) ^ (2 : ℕ)) μ := by
              simpa using
                (RealRandomVariableArray.IsNormed.memLp_two (A := A) (μ := μ) n i).integrable_sq
            exact hsqInt.const_mul _
          have hpointwise :
              ∀ᵐ ω ∂μ,
                ‖Complex.exp (t * A n i ω * Complex.I) - 1 -
                    Complex.I * (t * A n i ω : ℝ)‖ ≤
                  g ω := by
            refine Filter.Eventually.of_forall fun ω ↦ ?_
            dsimp [g]
            simpa [Finset.sum_range_succ, pow_two, sub_eq_add_neg, add_assoc, add_left_comm,
              add_comm, mul_assoc, mul_left_comm, mul_comm] using
              norm_exp_mul_I_sub_taylor_sum_le (t := t * A n i ω) (n := 2)
          calc
            ‖∫ ω,
                (Complex.exp (t * A n i ω * Complex.I) - 1 -
                  Complex.I * (t * A n i ω : ℝ)) ∂μ‖
                ≤ ∫ ω, g ω ∂μ := by
                  exact MeasureTheory.norm_integral_le_of_norm_le hg hpointwise
            _ = (t ^ (2 : ℕ) / 2) * ∫ ω, (A n i ω) ^ (2 : ℕ) ∂μ := by
                  rw [hg_eq, integral_const_mul]
            _ = (t ^ (2 : ℕ) / 2) * Var[A n i; μ] := by
                  congr 1
                  exact
                    (ProbabilityTheory.variance_of_integral_eq_zero
                      (A.measurable_entry n i).aemeasurable
                      (RealRandomVariableArray.IsCentered.expectation_eq_zero
                        (A := A) (μ := μ) n i)).symm
    _ = (t ^ (2 : ℕ) / 2) * ∑ i : Fin (A.rowLength n), Var[A n i; μ] := by
          rw [Finset.mul_sum]
    _ = t ^ (2 : ℕ) / 2 := by
          rw [RealRandomVariableArray.IsNormed.variance_sum_eq_one (A := A) (μ := μ) n, mul_one]

end

end RealRandomVariableArray
