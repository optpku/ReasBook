/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Theorem_24_21.Construction
import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Theorem_24_21.Evaluation
import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Definition_24_20

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open MeasureTheory.ProbabilityMeasure
open scoped ENNReal

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]

-- Proof sketch: Theorems 24.16 and 24.17 supply the infinite-divisibility, independent-increment,
-- and evaluation Lévy-measure consequences below.
/-- Helper theorem: the Poisson construction is a random measure. -/
theorem poissonDrivenRandomMeasure_isRandomMeasure
    {P : ProbabilityMeasure Ω} {ν : BoundedlyFiniteMeasure (PositiveNNReal × E)}
    {α : BoundedlyFiniteMeasure E}
    {X : Ω → Measure (PositiveNNReal × E)}
    (hν : HasFiniteTruncatedFirstMomentOnBoundedSets (ν : Measure (PositiveNNReal × E)))
    (hX : IsPoissonPointProcess (ν : Measure (PositiveNNReal × E)) P X) :
    IsRandomMeasure P (poissonDrivenRandomMeasure α X) := sorry

/-- Helper theorem: the Poisson construction has independent increments. -/
theorem poissonDrivenRandomMeasure_hasIndependentIncrements
    {P : ProbabilityMeasure Ω} {ν : BoundedlyFiniteMeasure (PositiveNNReal × E)}
    {α : BoundedlyFiniteMeasure E}
    {X : Ω → Measure (PositiveNNReal × E)}
    (hν : HasFiniteTruncatedFirstMomentOnBoundedSets (ν : Measure (PositiveNNReal × E)))
    (hX : IsPoissonPointProcess (ν : Measure (PositiveNNReal × E)) P X) :
    HasIndependentIncrements P (poissonDrivenRandomMeasure α X) := sorry

/-- Auxiliary bounded-evaluation packaging for the Poisson construction. -/
def HasInfinitelyDivisibleBoundedEvaluations
    (P : ProbabilityMeasure Ω) (ν : BoundedlyFiniteMeasure (PositiveNNReal × E))
    (α : BoundedlyFiniteMeasure E) (X : Ω → Measure (PositiveNNReal × E)) : Prop :=
  ∀ ⦃A : Set E⦄, MeasurableSet A → Bornology.IsBounded A →
    ∃ μA : ProbabilityMeasure NNReal,
      HasLaw (fun ω ↦ (poissonDrivenRandomMeasure α X ω A).toNNReal)
        (μA : Measure NNReal) (P : Measure Ω) ∧
        MeasureTheory.FiniteMeasure.HasSubordinatorLevyKhinchinRepresentation μA
          (((α : Measure E) A).toNNReal)
          (restrictedLevyMeasure (ν : Measure (PositiveNNReal × E)) A)

/-- The Poisson construction has infinitely divisible bounded evaluations. -/
theorem poissonDrivenRandomMeasure_hasInfinitelyDivisibleBoundedEvaluations
    {P : ProbabilityMeasure Ω} {ν : BoundedlyFiniteMeasure (PositiveNNReal × E)}
    {α : BoundedlyFiniteMeasure E}
    {X : Ω → Measure (PositiveNNReal × E)}
    (hν : HasFiniteTruncatedFirstMomentOnBoundedSets (ν : Measure (PositiveNNReal × E)))
    (hX : IsPoissonPointProcess (ν : Measure (PositiveNNReal × E)) P X) :
    HasInfinitelyDivisibleBoundedEvaluations P ν α X := sorry

/-- Theorem 24.21: the Poisson construction is an infinitely divisible random measure with
independent increments. In this construction, `ν` is the canonical measure and `α` is the
deterministic part. The bounded-evaluation and measurable-set Lévy-measure consequences are
recorded separately in
`poissonDrivenRandomMeasure_hasInfinitelyDivisibleBoundedEvaluations` and
`poissonDrivenRandomMeasure_eval_hasLevyMeasure`. -/
theorem poissonDrivenRandomMeasure_isInfinitelyDivisible
    {P : ProbabilityMeasure Ω} {ν : BoundedlyFiniteMeasure (PositiveNNReal × E)}
    {α : BoundedlyFiniteMeasure E}
    {X : Ω → Measure (PositiveNNReal × E)}
    (hν : HasFiniteTruncatedFirstMomentOnBoundedSets (ν : Measure (PositiveNNReal × E)))
    (hX : IsPoissonPointProcess (ν : Measure (PositiveNNReal × E)) P X) :
    IsInfinitelyDivisibleRandomMeasure P (poissonDrivenRandomMeasure α X) ∧
      HasIndependentIncrements P (poissonDrivenRandomMeasure α X) := sorry

/-- Auxiliary bridge: the law of the Poisson construction is infinitely divisible. -/
theorem poissonDrivenRandomMeasure_law_isInfinitelyDivisible
    {P : ProbabilityMeasure Ω} {ν : BoundedlyFiniteMeasure (PositiveNNReal × E)}
    {α : BoundedlyFiniteMeasure E}
    {X : Ω → Measure (PositiveNNReal × E)}
    (hν : HasFiniteTruncatedFirstMomentOnBoundedSets (ν : Measure (PositiveNNReal × E)))
    (hX : IsPoissonPointProcess (ν : Measure (PositiveNNReal × E)) P X) :
    MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible
      (ProbabilityMeasure.map P
        ((poissonDrivenRandomMeasure_isRandomMeasure hν hX :
            IsRandomMeasure P (poissonDrivenRandomMeasure α X)).measurable.aemeasurable)) := sorry

/-- Every bounded measurable evaluation of the Poisson construction has the corresponding
subordinator Lévy--Khinchin representation. -/
theorem poissonDrivenRandomMeasure.boundedEval_hasLevyKhinchinRepresentation
    {P : ProbabilityMeasure Ω} {ν : BoundedlyFiniteMeasure (PositiveNNReal × E)}
    {α : BoundedlyFiniteMeasure E}
    {X : Ω → Measure (PositiveNNReal × E)}
    (hν : HasFiniteTruncatedFirstMomentOnBoundedSets (ν : Measure (PositiveNNReal × E)))
    (hX : IsPoissonPointProcess (ν : Measure (PositiveNNReal × E)) P X) :
    ∀ ⦃A : Set E⦄, MeasurableSet A → Bornology.IsBounded A →
      ∃ μA : ProbabilityMeasure NNReal,
        HasLaw (fun ω ↦ (poissonDrivenRandomMeasure α X ω A).toNNReal)
          (μA : Measure NNReal) (P : Measure Ω) ∧
          MeasureTheory.FiniteMeasure.HasSubordinatorLevyKhinchinRepresentation μA
            (((α : Measure E) A).toNNReal)
            (restrictedLevyMeasure (ν : Measure (PositiveNNReal × E)) A) := sorry

/-- For every measurable `A`, the evaluation `Y(A)` has deterministic part `α(A)` and Lévy
measure `ν(· × A)`. -/
theorem poissonDrivenRandomMeasure_eval_hasLevyMeasure
    {P : ProbabilityMeasure Ω} {ν : BoundedlyFiniteMeasure (PositiveNNReal × E)}
    {α : BoundedlyFiniteMeasure E}
    {X : Ω → Measure (PositiveNNReal × E)} {A : Set E}
    (hν : HasFiniteTruncatedFirstMomentOnBoundedSets (ν : Measure (PositiveNNReal × E)))
    (hX : IsPoissonPointProcess (ν : Measure (PositiveNNReal × E)) P X)
    (hA : MeasurableSet A) :
    HasEvaluationLevyMeasure P
      (fun ω ↦ poissonDrivenRandomMeasure α X ω A)
      ((α : Measure E) A)
      (restrictedLevyMeasure (ν : Measure (PositiveNNReal × E)) A) := sorry

end ProbabilityTheory
