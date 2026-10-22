/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Theorem_24_21.Construction
import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Corollary_24_18

open MeasureTheory ProbabilityTheory
open MeasureTheory.ProbabilityMeasure
open scoped ENNReal

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]

/-- Helper for Theorem 24.21: the Laplace kernel on `ℝ≥0∞`, extended by `0` at `∞`. -/
private def ennrealExpNeg (t : ℝ≥0∞) : ℝ :=
  if t = ∞ then 0 else Real.exp (-t.toReal)

/-- A nonnegative extended-valued random variable has deterministic part `α` and Lévy measure `ν`
when its Laplace transform has the subordinator Lévy--Khinchin form, allowing the value `∞`. This
is the source-facing owner used for Theorem 24.21 (4). -/
def HasEvaluationLevyMeasure
    (P : ProbabilityMeasure Ω) (Z : Ω → ℝ≥0∞) (α : ℝ≥0∞) (ν : Measure NNReal) : Prop :=
  ∀ t : NNReal,
    ∫ ω, ennrealExpNeg (ENNReal.ofReal (t : ℝ) * Z ω) ∂(P : Measure Ω) =
      ennrealExpNeg
        (ENNReal.ofReal (t : ℝ) * α +
          ∫⁻ x, ENNReal.ofReal (1 - Real.exp (-((t : ℝ) * (x : ℝ)))) ∂ν)

/-- Companion to Theorem 24.21 (4): for every bounded measurable `A`, the evaluation law of
`Y(A)` has deterministic part `α(A)` and Lévy measure `ν(· × A)`. -/
theorem HasEvaluationLevyMeasure.of_isBounded
    {P : ProbabilityMeasure Ω} {ν : BoundedlyFiniteMeasure (PositiveNNReal × E)}
    {α : BoundedlyFiniteMeasure E}
    {X : Ω → Measure (PositiveNNReal × E)} {A : Set E}
    (hν : HasFiniteTruncatedFirstMomentOnBoundedSets (ν : Measure (PositiveNNReal × E)))
    (hX : IsPoissonPointProcess (ν : Measure (PositiveNNReal × E)) P X)
    (hA : MeasurableSet A) (hA_bdd : Bornology.IsBounded A) :
    ∃ μA : ProbabilityMeasure NNReal,
      HasLaw (fun ω ↦ (poissonDrivenRandomMeasure α X ω A).toNNReal)
        (μA : Measure NNReal) (P : Measure Ω) ∧
        MeasureTheory.FiniteMeasure.HasSubordinatorLevyKhinchinRepresentation μA
          (((α : Measure E) A).toNNReal)
          (restrictedLevyMeasure (ν : Measure (PositiveNNReal × E)) A) := sorry

end ProbabilityTheory
