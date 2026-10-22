/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.StandardBrownianMotionVector
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Definition_26_1

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u

namespace ProbabilityTheory

variable {n m : ℕ}

local notation "State" => Fin n → ℝ
local notation "StatePath" => EuclideanPathSpace n
local notation "NoisePath" => EuclideanPathSpace m

/- Domain-style sampling for Remark 26.3:
* primary domain: pathwise strong solutions of SDEs on filtered spaces carrying Brownian drivers;
* sampled owner declarations: `StrongSolutionOperator`, `StrongSolution`,
  `strongSolution_iff_exists_solver`, and `Function.toEuclidean`;
* core/canonical owner: `StrongSolution` with realized paths coming from
  `StrongSolutionOperator.realization`;
* bridge/view layer here: transfer a pathwise solver hypothesis on arbitrary Brownian realizations
  into the canonical `StrongSolution` owner;
* primitive data: the Brownian/adaptedness/independence/initial measurability hypotheses together
  with the equation-solving clause for `F.realization`;
* derived API: the resulting `StrongSolution` witness.
-/
/-- Remark 26.3: a pathwise strong-solution operator produces, on every filtered space carrying an
independent Brownian driver and initial datum, a realized strong solution of the same integral
equation. -/
theorem realization_isStrongSolution_on_any_brownian_realization
    {F : StrongSolutionOperator n m}
    {Equation : {Ω : Type u} → [MeasurableSpace Ω] →
      (Ω → State) → (Ω → NoisePath) → (Ω → StatePath) → Prop}
    (hF : ∀ {Ω : Type u} [MeasurableSpace Ω]
      (ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω))
      (μ : Measure Ω) (ξ : Ω → State) (W : Ω → NoisePath),
      IsStandardBrownianMotionVector μ (Function.toEuclidean (fun t ω ↦ W ω t)) →
      Adapted ℱ (fun t ω ↦ W ω t) →
      IndepFun ξ W μ →
      Measurable[ℱ 0] ξ →
      Equation ξ W (F.realization ξ W))
    {Ω : Type u} [MeasurableSpace Ω]
    (ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (μ : Measure Ω) (ξ : Ω → State) (W : Ω → NoisePath)
    (hW : IsStandardBrownianMotionVector μ (Function.toEuclidean (fun t ω ↦ W ω t)))
    (hW_adapted : Adapted ℱ (fun t ω ↦ W ω t))
    (hξW : IndepFun ξ W μ)
    (hξ : Measurable[ℱ 0] ξ) :
    StrongSolution n m Equation ξ W (F.realization ξ W) := by
  refine strongSolution_iff_exists_solver.2 ?_
  exact ⟨F, rfl, hF ℱ μ ξ W hW hW_adapted hξW hξ⟩

end ProbabilityTheory
