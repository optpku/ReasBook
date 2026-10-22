/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Definition_26_1

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped Topology

universe u

namespace ProbabilityTheory

variable {n m : ℕ}

local notation "State" => Fin n → ℝ
local notation "StatePath" => EuclideanPathSpace n
local notation "NoisePath" => EuclideanPathSpace m

variable
    (IsBrownianMotion : {Ω : Type u} → [MeasurableSpace Ω] → Measure Ω →
      Filtration NNReal (inferInstance : MeasurableSpace Ω) → (Ω → NoisePath) → Prop)
    (IsSolution : {Ω : Type u} → [MeasurableSpace Ω] → Measure Ω →
      Filtration NNReal (inferInstance : MeasurableSpace Ω) → (Ω → State) →
        (Ω → NoisePath) → (Ω → StatePath) → Prop)

/-- Auxiliary witness predicate for Definition 26.4: a strong-solution operator `F` realizes the
source-facing unique-strong-solution property for initial law `μ` when it solves the SDE on every
Brownian input with that initial law and every other solution with the same input data agrees
pathwise with the realization produced by `F`. -/
def StrongSolutionOperator.IsUniqueStrongSolution
    (F : StrongSolutionOperator n m) (μ : Measure State) : Prop :=
  (∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
      (ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω))
      (ξ : Ω → State) (W : Ω → NoisePath),
      IsBrownianMotion P ℱ W →
      Measurable[ℱ 0] ξ →
      IndepFun ξ W P →
      HasLaw ξ μ P →
      IsSolution P ℱ ξ W (F.realization ξ W)) ∧
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
      (ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω))
      (ξ : Ω → State) (W : Ω → NoisePath) (X : Ω → StatePath),
      IsBrownianMotion P ℱ W →
      Measurable[ℱ 0] ξ →
      IndepFun ξ W P →
      HasLaw ξ μ P →
      IsSolution P ℱ ξ W X →
      X = F.realization ξ W

/-- Definition 26.4: the SDE has a unique strong solution for the initial law `μ` if there exists
a strong-solution operator `F` whose realization solves the SDE on every Brownian input with that
initial law and every other such solution agrees pathwise with the realization obtained from `F`.
-/
def HasUniqueStrongSolution (μ : Measure State) : Prop :=
  ∃ F : StrongSolutionOperator n m, F.IsUniqueStrongSolution IsBrownianMotion IsSolution μ

theorem StrongSolutionOperator.IsUniqueStrongSolution.solves_all_inputs
    {F : StrongSolutionOperator n m} {μ : Measure State}
    (hF : F.IsUniqueStrongSolution μ IsBrownianMotion IsSolution)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (ξ : Ω → State) (W : Ω → NoisePath) :
    IsBrownianMotion P ℱ W →
    Measurable[ℱ 0] ξ →
    IndepFun ξ W P →
    HasLaw ξ μ P →
    IsSolution P ℱ ξ W (F.realization ξ W) :=
  hF.1 P ℱ ξ W

theorem StrongSolutionOperator.IsUniqueStrongSolution.pathwise_unique
    {F : StrongSolutionOperator n m} {μ : Measure State}
    (hF : F.IsUniqueStrongSolution μ IsBrownianMotion IsSolution)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (ξ : Ω → State) (W : Ω → NoisePath) (X : Ω → StatePath) :
    IsBrownianMotion P ℱ W →
    Measurable[ℱ 0] ξ →
    IndepFun ξ W P →
    HasLaw ξ μ P →
    IsSolution P ℱ ξ W X →
    X = F.realization ξ W :=
  hF.2 P ℱ ξ W X

end ProbabilityTheory
