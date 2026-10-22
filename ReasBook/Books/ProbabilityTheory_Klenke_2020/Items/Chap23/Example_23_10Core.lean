/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The partial sum `X₁ + ⋯ + Xₙ` of a real-valued sequence of random variables, written with the
chapter's `0`-based indexing as the sum of `X 0, …, X (n - 1)`. -/
def partialRealSum (X : ℕ → Ω → ℝ) (n : ℕ+) : Ω → ℝ :=
  fun ω ↦ ∑ i ∈ Finset.range (n : ℕ), X i ω

/-- The Legendre-transform rate function associated with the cumulant-generating function of `X`
under the measure `P`. -/
def legendreCgfRateFunction (X : Ω → ℝ) (P : Measure Ω) (x : ℝ) : EReal :=
  sSup (Set.range fun t : ℝ ↦ ((t * x - cgf X P t : ℝ) : EReal))

/-- The law of the normalized partial sum `n⁻¹ (X₁ + ⋯ + Xₙ)`. -/
def normalizedPartialSumLaw (X : ℕ → Ω → ℝ) (P : Measure Ω) (n : ℕ+) : Measure ℝ :=
  Measure.map (fun ω ↦ partialRealSum X n ω / (n : ℝ)) P

/-- The large-deviation upper bound for a sequence of probability laws on `ℝ` with speed `n` and
rate function `I`, tested on closed sets. -/
def HasLargeDeviationUpperBound (μ : ℕ+ → Measure ℝ) (I : ℝ → EReal) : Prop :=
  ∀ s : Set ℝ, IsClosed s →
    Filter.limsup (fun n : ℕ+ ↦ ENNReal.log (μ n s) / (n : EReal)) atTop ≤ -sInf (I '' s)

/-- The large-deviation lower bound for a sequence of probability laws on `ℝ` with speed `n` and
rate function `I`, tested on open sets. -/
def HasLargeDeviationLowerBound (μ : ℕ+ → Measure ℝ) (I : ℝ → EReal) : Prop :=
  ∀ s : Set ℝ, IsOpen s →
    -sInf (I '' s) ≤ Filter.liminf (fun n : ℕ+ ↦ ENNReal.log (μ n s) / (n : EReal)) atTop

/-- A sequence of laws on `ℝ` satisfies the large deviation principle with speed `n` and rate
function `I` if it satisfies the standard closed-set upper bound and open-set lower bound. -/
def SatisfiesLargeDeviationPrinciple (μ : ℕ+ → Measure ℝ) (I : ℝ → EReal) : Prop :=
  HasLargeDeviationUpperBound μ I ∧ HasLargeDeviationLowerBound μ I

-- Proof comment: the upper bound is exactly the first component of the defining conjunction.
/-- Extract the closed-set upper bound from a large deviation principle. -/
theorem SatisfiesLargeDeviationPrinciple.upper
    {μ : ℕ+ → Measure ℝ} {I : ℝ → EReal}
    (h : SatisfiesLargeDeviationPrinciple μ I) :
    HasLargeDeviationUpperBound μ I := by
  exact h.1

-- Proof comment: the lower bound is exactly the second component of the defining conjunction.
/-- Extract the open-set lower bound from a large deviation principle. -/
theorem SatisfiesLargeDeviationPrinciple.lower
    {μ : ℕ+ → Measure ℝ} {I : ℝ → EReal}
    (h : SatisfiesLargeDeviationPrinciple μ I) :
    HasLargeDeviationLowerBound μ I := by
  exact h.2

end ProbabilityTheory
