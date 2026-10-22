/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Corollary_24_9
import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Definition_24_3

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E] [TopologicalSpace E] [Bornology E]

/-- Definition 24.10: a Poisson point process on `E` with intensity measure `μ` under `P` is a
random measure with independent increments such that every bounded measurable-set evaluation has the
Poisson law of parameter `μ A`, viewed on `ℝ≥0∞` through the natural-number embedding. -/
def IsPoissonPointProcess
    (μ : Measure E) (P : ProbabilityMeasure Ω) (X : Ω → Measure E) : Prop :=
  IsRandomMeasure P X ∧
  HasIndependentIncrements P X ∧
  IsLocallyFiniteMeasure μ ∧
  ∀ ⦃A : Set E⦄, MeasurableSet A → Bornology.IsBounded A → (μ A) ≠ ⊤ →
    HasLaw (fun ω ↦ X ω A)
      (Measure.map (fun n : ℕ ↦ (n : ENNReal)) (poissonMeasure (μ A).toNNReal))
      (P : Measure Ω)

-- Proof sketch: unfold `IsPoissonPointProcess`; the statement is exactly the conjunction of the
-- random-measure condition, the independent-increments condition, local finiteness of the
-- intensity, and the Poisson marginal law on bounded measurable sets.
/-- A random measure is a Poisson point process with intensity `μ` exactly when it has independent
increments and each bounded measurable-set evaluation has the corresponding Poisson law. -/
theorem isPoissonPointProcess_iff
    (μ : Measure E) (P : ProbabilityMeasure Ω) (X : Ω → Measure E) :
    IsPoissonPointProcess μ P X ↔
      IsRandomMeasure P X ∧
      HasIndependentIncrements P X ∧
      IsLocallyFiniteMeasure μ ∧
      ∀ ⦃A : Set E⦄, MeasurableSet A → Bornology.IsBounded A → (μ A) ≠ ⊤ →
        HasLaw (fun ω ↦ X ω A)
          (Measure.map (fun n : ℕ ↦ (n : ENNReal)) (poissonMeasure (μ A).toNNReal))
          (P : Measure Ω) := by
  -- The theorem is the direct unfolding of the defining conjunction.
  rfl

/-- The law `PPP_μ` attached to a Poisson point process is the pushforward of the ambient
probability law along the random measure. -/
noncomputable def poissonPointProcessLaw
    (μ : Measure E) (P : ProbabilityMeasure Ω) (X : Ω → Measure E)
    (hX : IsPoissonPointProcess μ P X) : ProbabilityMeasure (Measure E) :=
  P.map hX.1.measurable.aemeasurable

-- Proof sketch: unfold `poissonPointProcessLaw`; it is defined to be the pushforward
-- probability measure `P_X` of `P` along the random measure `X`.
/-- The companion law `PPP_μ` is the pushforward probability measure of `P` by the Poisson point
process `X`. -/
theorem poissonPointProcessLaw_def
    (μ : Measure E) (P : ProbabilityMeasure Ω) (X : Ω → Measure E)
    (hX : IsPoissonPointProcess μ P X) :
    poissonPointProcessLaw μ P X hX = P.map hX.1.measurable.aemeasurable := by
  -- The companion law is defined as this pushforward probability measure.
  rfl

end ProbabilityTheory
