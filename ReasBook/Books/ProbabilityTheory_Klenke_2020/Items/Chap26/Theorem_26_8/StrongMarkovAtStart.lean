/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_12
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Theorem_26_8.CoefficientConditions

open MeasureTheory ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {n : ℕ}

/-- Shared support API for Theorem 26.8: the fixed-start strong-Markov property for an
`n`-dimensional realization. After an almost surely finite stopping time, the conditional law of
the future path depends only on the stopped state. -/
def HasStrongMarkovPropertyAtStartNDim
    {Ω : Type u} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω)
    (X : NNReal → Ω → SDEState n)
    (κ : Kernel (SDEState n) (NNReal → SDEState n)) : Prop :=
  ∀ (τ : Ω → WithTop NNReal)
    (hτ : IsStoppingTime (processFiltration X) τ),
    (∀ᵐ ω ∂(P : Measure Ω), τ ω ≠ ⊤) →
    ∀ (f : (NNReal → SDEState n) → ℝ),
      Measurable f →
      (∃ C : ℝ, ∀ y, |f y| ≤ C) →
      (P : Measure Ω)[fun ω ↦ f (futurePathAfterStoppingTime X τ ω) | hτ.measurableSpace] =ᵐ[
        (P : Measure Ω)] fun ω ↦ ∫ y, f y ∂ κ (stoppedValue X τ ω)

end ProbabilityTheory
