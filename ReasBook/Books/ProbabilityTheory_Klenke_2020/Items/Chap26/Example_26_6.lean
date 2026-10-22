/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_30
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Definition_26_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology

noncomputable section

namespace ProbabilityTheory

local notation "State" => Fin 1 → ℝ
local notation "PathSpace" => BrownianPathSpace
local notation "NoisePath" => EuclideanPathSpace 1

private abbrev stateEquivReal : State ≃ₜ ℝ :=
  (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).toHomeomorph

private abbrev pathSpaceEquivNoisePath : PathSpace ≃ NoisePath :=
  (Homeomorph.refl NNReal).continuousMapCongr stateEquivReal.symm

/- Domain-style sampling for Example 26.6:
* primary domain: one-dimensional strong solutions of SDEs driven by continuous Brownian paths;
* sampled owner declarations in this domain: `StrongSolutionOperator`,
  `StrongSolutionOperator.realization`, `CoordinateProcess.toEuclidean`, and
  `ornsteinUhlenbeckStrongSolutionOperator`;
* owner abstraction: the chapter organizes pathwise strong solutions around
  `StrongSolutionOperator`, with scalar-path formulas appearing only as bridge/view declarations;
* primitive data: the scalar drift and diffusion coefficients and the pointwise geometric-Brownian
  path formula;
* derived API: the canonical one-dimensional strong-solution operator and its scalar-path bridge.

Layer triage:
* source-facing: `geometricBrownianDiffusion` and `geometricBrownianDrift`;
* core/canonical: `geometricBrownianStrongSolutionOperator`;
* bridge/view: `geometricBrownianSolutionPath`. -/

/-- The linear diffusion coefficient `σ(t, x) = α x` of the geometric Brownian motion example. -/
def geometricBrownianDiffusion (α : ℝ) (_ : NNReal) (x : ℝ) : ℝ :=
  α * x

-- Proof sketch: unfold `geometricBrownianDiffusion`; the coefficient is constant in time and
-- linear in the state variable.
/-- Evaluating the geometric-Brownian diffusion coefficient gives `α x`. -/
theorem geometricBrownianDiffusion_apply (α : ℝ) (t : NNReal) (x : ℝ) :
    geometricBrownianDiffusion α t x = α * x :=
  rfl

/-- The linear drift coefficient `b(t, x) = β x` of the geometric Brownian motion example. -/
def geometricBrownianDrift (β : ℝ) (_ : NNReal) (x : ℝ) : ℝ :=
  β * x

-- Proof sketch: unfold `geometricBrownianDrift`; the coefficient is constant in time and linear
-- in the state variable.
/-- Evaluating the geometric-Brownian drift coefficient gives `β x`. -/
theorem geometricBrownianDrift_apply (β : ℝ) (t : NNReal) (x : ℝ) :
    geometricBrownianDrift β t x = β * x :=
  rfl

private def geometricBrownianStrongSolutionValue (α β : ℝ) (x : State) (w : NoisePath)
    (t : NNReal) : State :=
  fun _ ↦ x 0 * Real.exp (α * w t 0 + (β - α ^ (2 : ℕ) / 2) * (t : ℝ))

-- Proof sketch: `w` is continuous, multiplication by constants preserves continuity, the time map
-- `t ↦ (t : ℝ)` is continuous, sums of continuous functions are continuous, and `Real.exp`
-- preserves continuity of the exponent.
/-- The geometric-Brownian sample-path formula defines a continuous path for every continuous
driver `w : PathSpace`. -/
theorem geometricBrownianStrongSolution_continuous
    (α β : ℝ) (x : State) (w : NoisePath) :
    Continuous (geometricBrownianStrongSolutionValue α β x w) := by
  have hw : Continuous fun t : NNReal ↦ w t (0 : Fin 1) :=
    (continuous_apply (0 : Fin 1)).comp w.continuous
  exact continuous_pi fun _ ↦
    continuous_const.mul <|
      Real.continuous_exp.comp <|
        (continuous_const.mul hw).add (continuous_const.mul continuous_subtype_val)

/-- Example 26.6, core/canonical layer: the geometric-Brownian path formula packages as the
one-dimensional strong-solution operator from Definition 26.1. -/
def geometricBrownianStrongSolutionOperator (α β : ℝ) : StrongSolutionOperator 1 1 where
  toFun x w :=
    { toFun := geometricBrownianStrongSolutionValue α β x w
      continuous_toFun := geometricBrownianStrongSolution_continuous α β x w }
  measurable_up_to t := by
    refine Measurable.of_comap_le ?_
    simp_rw [generatedFiltrationSpace, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp,
      Function.comp_def]
    refine iSup_le fun s ↦ iSup_le fun hs ↦ ?_
    letI : MeasurableSpace NoisePath :=
      generatedFiltrationSpace (fun r (ω : NoisePath) ↦ ω r) t
    letI : MeasurableSpace (State × NoisePath) :=
      MeasurableSpace.prod (inferInstance : MeasurableSpace State) inferInstance
    rw [← measurable_iff_comap_le]
    refine measurable_pi_lambda _ fun i ↦ ?_
    have hs_eval : Measurable fun w : NoisePath ↦ w s := by
      refine Measurable.of_comap_le ?_
      change MeasurableSpace.comap (fun w : NoisePath ↦ w s) inferInstance ≤
        generatedFiltrationSpace (fun r (ω : NoisePath) ↦ ω r) t
      rw [generatedFiltrationSpace]
      exact le_iSup_of_le s <| le_iSup_of_le hs le_rfl
    have hx : Measurable fun xw : State × NoisePath ↦ xw.1 0 :=
      Measurable.eval measurable_fst
    have hw : Measurable fun xw : State × NoisePath ↦ xw.2 s 0 :=
      (Measurable.eval hs_eval).comp measurable_snd
    simpa [geometricBrownianStrongSolutionValue] using
      hx.mul <| Real.measurable_exp.comp <|
        (measurable_const.mul hw).add measurable_const

/-- Evaluating the canonical geometric-Brownian strong-solution operator gives the closed-form
path formula in the unique coordinate. -/
theorem geometricBrownianStrongSolutionOperator_apply
    (α β : ℝ) (x : State) (w : NoisePath) (t : NNReal) (i : Fin 1) :
    geometricBrownianStrongSolutionOperator α β x w t i =
      x 0 * Real.exp (α * w t 0 + (β - α ^ (2 : ℕ) / 2) * (t : ℝ)) :=
  rfl

/-- Example 26.6, bridge/view layer: evaluating the canonical one-dimensional strong-solution
operator on scalar initial data and scalar driving paths recovers the textbook scalar path map. -/
abbrev geometricBrownianSolutionPath
    (α β x : ℝ) (w : PathSpace) : PathSpace :=
  pathSpaceEquivNoisePath.symm
    (geometricBrownianStrongSolutionOperator α β (stateEquivReal.symm x)
      (pathSpaceEquivNoisePath w))

-- Proof sketch: unfold `geometricBrownianSolutionPath`; its value at time `t` is exactly the
-- displayed exponential expression.
/-- Evaluating the geometric-Brownian strong-solution map gives the closed-form path formula. -/
theorem geometricBrownianSolutionPath_apply
    (α β x : ℝ) (w : PathSpace) (t : NNReal) :
    geometricBrownianSolutionPath α β x w t =
      x * Real.exp (α * w t + (β - α ^ (2 : ℕ) / 2) * (t : ℝ)) := by
  simpa [geometricBrownianSolutionPath, pathSpaceEquivNoisePath, stateEquivReal] using
    (geometricBrownianStrongSolutionOperator_apply α β (stateEquivReal.symm x)
      (pathSpaceEquivNoisePath w) t 0)

-- Proof sketch: evaluate the explicit formula at `t = 0`, use the hypothesis `w 0 = 0`, and
-- simplify the exponential factor to `exp 0 = 1`.
/-- If the driving path starts at `0`, then the geometric-Brownian strong-solution path starts at
its initial value `x`. -/
theorem geometricBrownianSolutionPath_zero
    (α β x : ℝ) {w : PathSpace} (hw : w 0 = 0) :
    geometricBrownianSolutionPath α β x w 0 = x := by
  rw [geometricBrownianSolutionPath_apply]
  simp [hw]

end ProbabilityTheory
