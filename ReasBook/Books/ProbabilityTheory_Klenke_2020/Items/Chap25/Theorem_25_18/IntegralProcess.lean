/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_66
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Remark_21_67
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_11
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_9
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_18.Compensator

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

noncomputable section

namespace ProbabilityTheory

universe u

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {ℱ : Filtration NNReal mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ]

private abbrev Process (Ω : Type u) := NNReal → Ω → ℝ

/-- Source-facing finite-energy hypothesis for the Brownian-Itô martingale result below: `H` is
progressively measurable, and the compensator `ω ↦ ∫_0^T H_s(ω)^2 ds` has finite expectation on
every positive finite horizon. -/
structure HasFiniteExpectedEnergy
    (ℱ : Filtration NNReal mΩ) (μ : Measure Ω) (H : Process Ω) : Prop where
  progMeasurable : MeasureTheory.ProgMeasurable ℱ H
  interval_square_integrable :
    ∀ ⦃T : NNReal⦄, ∀ᵐ ω ∂μ,
      IntegrableOn (fun s : ℝ ↦ (H s.toNNReal ω) ^ 2) (Set.Icc (0 : ℝ) (T : ℝ))
  const_stop_closure :
    ∀ T : NNReal,
      MeasureTheory.MemPredictableStepProcessClosure ℱ μ
        (processBeforeStoppingTime H (fun _ : Ω ↦ (T : ENNReal)))
  finite_expectation :
    ∀ ⦃T : NNReal⦄, 0 < T → Integrable (MeasureTheory.secondMomentCompensator H T) μ

/-- The Brownian-Itô process `t ↦ ∫_0^t H_s dW_s` attached to a finite-energy integrand `H`,
realized by applying the Brownian-Itô map to the deterministic cutoff of `H` at the matching
horizon `t`. -/
noncomputable def brownianItoIntegralProcess
    (W : Process Ω)
    [hIto : BrownianItoIntegral μ ℱ W]
    {H : Process Ω}
    (hH : HasFiniteExpectedEnergy ℱ μ H) : Process Ω :=
  fun t ω ↦
    hIto.toContinuousLinearMap
      (MeasureTheory.MemPredictableStepProcessClosure.toClosure
        (hH.const_stop_closure t)) ω

/-- Evaluating `brownianItoIntegralProcess` at time `t` uses the Brownian-Itô image of the
deterministic cutoff of `H` at that same horizon. -/
theorem brownianItoIntegralProcess_apply
    (W : Process Ω)
    [hIto : BrownianItoIntegral μ ℱ W]
    {H : Process Ω}
    (hH : HasFiniteExpectedEnergy ℱ μ H) (t : NNReal) (ω : Ω) :
    brownianItoIntegralProcess W hH t ω =
      hIto.toContinuousLinearMap
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure
          (hH.const_stop_closure t)) ω :=
  rfl

end ProbabilityTheory
