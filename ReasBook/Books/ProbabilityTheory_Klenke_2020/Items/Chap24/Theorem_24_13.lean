/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Definition_24_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Definition_24_10

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [PseudoMetricSpace E] [MeasurableSpace E]

/-- A random measure has count-valued evaluations when every measurable-set count is almost surely
in `ℕ₀ ∪ {∞}`. -/
def HasCountValuedEvaluations
    (P : ProbabilityMeasure Ω) (X : Ω → Measure E) : Prop :=
  ∀ ⦃A : Set E⦄, MeasurableSet A →
    ∀ᵐ ω ∂(P : Measure Ω),
      X ω A ∈ Set.range (fun n : ℕ ↦ (n : ENNReal)) ∪ ({∞} : Set ENNReal)

/-- A random measure has no double points when every singleton carries mass at most `1`
almost surely. -/
def HasNoDoublePoints
    (P : ProbabilityMeasure Ω) (X : Ω → Measure E) : Prop :=
  ∀ᵐ ω ∂(P : Measure Ω), ∀ x : E, X ω ({x} : Set E) ≤ 1

/-- A random measure has the textbook void probabilities with intensity `μ` when every bounded
measurable-set emptiness event has mass `exp (-μ A)`. -/
def HasPoissonVoidProbabilities
    (μ : BoundedlyFiniteMeasure E) (P : ProbabilityMeasure Ω) (X : Ω → Measure E) : Prop :=
  ∀ ⦃A : Set E⦄, MeasurableSet A → Bornology.IsBounded A →
    (P : Measure Ω) {ω | X ω A = 0} =
      ENNReal.ofReal (Real.exp (-(((μ : Measure E) A).toReal)))

/-- Theorem 24.13: for an atom-free boundedly finite intensity `μ` and a random measure `X` whose
measurable-set evaluations are almost surely in `ℕ₀ ∪ {∞}`, the Poisson point-process property is
equivalent to having no double points and the Poisson void probabilities on bounded measurable
sets. -/
def poissonPointProcess_iff_noDoublePoints_and_voidProbabilities
    (μ : BoundedlyFiniteMeasure E) [NoAtoms (μ : Measure E)]
    (P : ProbabilityMeasure Ω) (X : Ω → Measure E) : Prop :=
  IsRandomMeasure P X →
    HasCountValuedEvaluations P X →
      (IsPoissonPointProcess (μ : Measure E) P X ↔
        HasNoDoublePoints P X ∧ HasPoissonVoidProbabilities μ P X)

end ProbabilityTheory
