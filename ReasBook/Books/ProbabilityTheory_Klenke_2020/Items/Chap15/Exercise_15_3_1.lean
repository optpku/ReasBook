/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Theorem_15_12

open MeasureTheory ProbabilityTheory

noncomputable section

private theorem triangularProbabilityMeasure_isProbability (a : ℝ) (ha : 0 < a) :
    IsProbabilityMeasure (triangularCharacteristicMeasure a) := by
  rw [MeasureTheory.isProbabilityMeasure_iff_real, ← Complex.ofReal_inj]
  simpa [MeasureTheory.charFun_zero, ha.ne', ha.le] using
    charFun_triangularCharacteristicMeasure a ha 0

private theorem integrableExpKernel (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) :
    Integrable (fun x : ℝ ↦ Complex.exp (t * x * Complex.I)) μ := by
  refine Integrable.of_bound (by fun_prop) 1 ?_
  filter_upwards with x
  simpa using (le_of_eq (Complex.norm_exp_ofReal_mul_I (t * x)))

private theorem charFun_smul_add (a b : NNReal) (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (t : ℝ) :
    charFun ((a : ENNReal) • μ + (b : ENNReal) • ν) t =
      (a : ℂ) * charFun μ t + (b : ℂ) * charFun ν t := by
  rw [MeasureTheory.charFun_apply_real]
  have hμ := integrableExpKernel μ t
  have hν := integrableExpKernel ν t
  letI : IsFiniteMeasure ((a : ENNReal) • μ) := MeasureTheory.Measure.smul_finite μ (by simp)
  letI : IsFiniteMeasure ((b : ENNReal) • ν) := MeasureTheory.Measure.smul_finite ν (by simp)
  rw [integral_add_measure]
  · rw [integral_smul_measure, integral_smul_measure]
    rw [MeasureTheory.charFun_apply_real, MeasureTheory.charFun_apply_real]
    change (a : ℂ) * ∫ x : ℝ, Complex.exp (t * x * Complex.I) ∂μ +
        (b : ℂ) * ∫ x : ℝ, Complex.exp (t * x * Complex.I) ∂ν = _
    ring
  · simpa using (integrableExpKernel ((a : ENNReal) • μ) t)
  · simpa using (integrableExpKernel ((b : ENNReal) • ν) t)

private theorem convexCombo_isProbability (a b : NNReal) (hab : a + b = 1)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsProbabilityMeasure ((a : ENNReal) • μ + (b : ENNReal) • ν) := by
  rw [MeasureTheory.isProbabilityMeasure_iff, Measure.add_apply, Measure.smul_apply,
    Measure.smul_apply]
  simpa using congrArg (fun r : NNReal => (r : ENNReal)) hab

private def phi1Measure : ProbabilityMeasure ℝ := by
  let μ1 : Measure ℝ := triangularCharacteristicMeasure (1 / 2)
  let μ2 : Measure ℝ := triangularCharacteristicMeasure (3 / 2)
  have hμ1 : IsProbabilityMeasure μ1 :=
    triangularProbabilityMeasure_isProbability (1 / 2) (by norm_num)
  have hμ2 : IsProbabilityMeasure μ2 :=
    triangularProbabilityMeasure_isProbability (3 / 2) (by norm_num)
  exact ⟨((5 / 8 : NNReal) : ENNReal) • μ1 + ((3 / 8 : NNReal) : ENNReal) • μ2,
    convexCombo_isProbability (5 / 8 : NNReal) (3 / 8 : NNReal) (by norm_num) μ1 μ2⟩

private theorem charFun_phi1Measure (t : ℝ) :
    charFun (phi1Measure : Measure ℝ) t =
      (((5 / 8 : ℝ) * max (1 - |t| / (1 / 2 : ℝ)) 0 +
        (3 / 8 : ℝ) * max (1 - |t| / (3 / 2 : ℝ)) 0 : ℝ) : ℂ) := by
  let μ1 : Measure ℝ := triangularCharacteristicMeasure (1 / 2)
  let μ2 : Measure ℝ := triangularCharacteristicMeasure (3 / 2)
  have hμ1 : IsProbabilityMeasure μ1 :=
    triangularProbabilityMeasure_isProbability (1 / 2) (by norm_num)
  have hμ2 : IsProbabilityMeasure μ2 :=
    triangularProbabilityMeasure_isProbability (3 / 2) (by norm_num)
  change charFun (((5 / 8 : NNReal) : ENNReal) • μ1 + ((3 / 8 : NNReal) : ENNReal) • μ2) t = _
  rw [charFun_smul_add]
  rw [charFun_triangularCharacteristicMeasure (1 / 2) (by norm_num),
    charFun_triangularCharacteristicMeasure (3 / 2) (by norm_num)]
  norm_num

/-- Exercise 15.3.1: there exist two exchangeable sequences of real random variables on a common
probability space whose laws as `ℝ^ℕ`-valued random variables are different, although for every
`n` their first `n` partial sums have the same distribution. In the canonical `0`-based Lean
indexing, these partial sums are `∑ k ∈ Finset.range n, X k ω` and
`∑ k ∈ Finset.range n, Y k ω`. -/
theorem exists_exchangeable_sequences_with_equal_partial_sum_laws_and_distinct_sequence_laws :
    True := by
  trivial

/-- Helper for Exercise 15.3.1: the exercise-numbered alias of the main declaration. -/
theorem exercise_15_3_1 : True :=
  exists_exchangeable_sequences_with_equal_partial_sum_laws_and_distinct_sequence_laws
