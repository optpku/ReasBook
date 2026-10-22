/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Example_8_32
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

namespace IsBrownianMotion

-- Proof sketch: write `B 1 = B T + (B 1 - B T)` with `0 < T < 1`. By the Brownian-motion axioms,
-- `B T` and `B 1 - B T` are independent centered Gaussians with variances `T` and `1 - T`.
-- Apply the Gaussian conditional-distribution formula from Example 8.32 to the pair
-- `(B T, B 1 - B T)` and simplify the resulting conditional mean and variance.
/-- Exercise 21.5.2: in kernel form, for `T ∈ (0,1)`, the regular conditional distribution of
`W_T` given `W_1` is, for `μ.map (B 1)`-almost every `x`, the Gaussian law with mean `Tx` and
variance `T(1 - T)`. -/
theorem condDistrib_timeValue_given_terminalValue_ae_eq
    {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B) (T : Set.Ioo (0 : NNReal) 1) :
    letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
    condDistrib (B T) (B 1) μ =ᵐ[μ.map (B 1)]
      fun x ↦ gaussianReal ((T : ℝ) * x) ((T : NNReal) * (1 - (T : NNReal))) := by
  have hlawT' : HasLaw (B T)
      (gaussianReal 0 ⟨((NNReal.sqrt (T : NNReal) : ℝ) ^ 2), sq_nonneg _⟩) μ := by
    have hlawT : HasLaw (B T) (gaussianReal 0 (T : NNReal)) μ := hB.gaussian_marginal T.2.1
    simpa using hlawT
  have hinc' : HasLaw (fun ω ↦ B 1 ω - B T ω)
      (gaussianReal 0 ⟨((NNReal.sqrt (1 - (T : NNReal)) : ℝ) ^ 2), sq_nonneg _⟩) μ := by
    have hinc : HasLaw (fun ω ↦ B 1 ω - B T ω) (gaussianReal 0 (1 - (T : NNReal))) μ := by
      let U : NNReal := 1 - (T : NNReal)
      have hU_pos : 0 < U := by
        simpa [U] using T.2.2
      have hlawU : HasLaw (B U) (gaussianReal 0 U) μ := hB.gaussian_marginal hU_pos
      have hlawInc : HasLaw (fun ω ↦ B U ω - B 0 ω) (gaussianReal 0 U) μ := by
        refine hlawU.congr ?_
        simp [hB.zero]
      have hlawInc' : HasLaw (fun ω ↦ B (U + 0) ω - B 0 ω) (gaussianReal 0 U) μ := by
        simpa using hlawInc
      have hstationary := hB.stationaryIncrements 0 U T
      have hsum : (T : NNReal) + (1 - (T : NNReal)) = 1 := by
        exact add_tsub_cancel_of_le T.2.2.le
      simpa [U, hsum, add_comm, add_left_comm, add_assoc] using hstationary.symm.hasLaw hlawInc'
    simpa using hinc
  have hindep : (B T) ⟂ᵢ[μ] (fun ω ↦ B 1 ω - B T ω) := by
    have hzero : ∀ᵐ ω ∂μ, B 0 ω = 0 := by
      simp [hB.zero]
    simpa using hB.indepIncrements.indepFun_eval_sub T.2.1.le T.2.2.le hzero
  have hmain := condDistrib_gaussian_left_given_sum_ae_eq μ 0 0
    (NNReal.sqrt (T : NNReal)) (NNReal.sqrt (1 - (T : NNReal))) hlawT' hinc' hindep
  have hsum_fun : (B T + fun ω ↦ -B T ω + B 1 ω) = B 1 := by
    funext ω
    change B T ω + (-B T ω + B 1 ω) = B 1 ω
    ring
  have hsum_real : (T : ℝ) + ((1 - (T : NNReal) : NNReal) : ℝ) = 1 := by
    exact_mod_cast add_tsub_cancel_of_le T.2.2.le
  simpa [hsum_fun, hsum_real, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc,
    mul_left_comm, mul_comm] using hmain

/-- Pointwise form of `condDistrib_timeValue_given_terminalValue_ae_eq`. -/
theorem condDistrib_timeValue_given_terminalValue_ae_eq_apply
    {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B) (T : Set.Ioo (0 : NNReal) 1) :
    letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
    ∀ᵐ x ∂μ.map (B 1),
      condDistrib (B T) (B 1) μ x =
        gaussianReal ((T : ℝ) * x) ((T : NNReal) * (1 - (T : NNReal))) := by
  simpa using condDistrib_timeValue_given_terminalValue_ae_eq hB T

end IsBrownianMotion

end ProbabilityTheory
