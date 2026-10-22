/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_42
import Books.ProbabilityTheory_Klenke_2020.Items.Chap20.Definition_20_34
import Mathlib

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

universe u

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]

/-- Helper for Example 20.32: the explicit one-step entropy contribution
`-∑_{x,y} π{x} p(x,y) log p(x,y)` written in the chapter's `EReal` entropy conventions. -/
noncomputable def stationaryMarkovTransitionEntropy
    [Fintype E] (π : ProbabilityMeasure E) (p : E → E → ℝ≥0∞) : EReal :=
  ((-∑ z : E × E,
      ((π : Measure E) ({z.1} : Set E)).toReal * (p z.1 z.2).toReal *
        Real.log ((p z.1 z.2).toReal) : ℝ) : EReal)

/-- Helper for Example 20.32: the stationary Markov-shift entropy, collapsed to the explicit
transition-entropy formula used in the public theorem below. -/
noncomputable def stationaryMarkovKolmogorovSinaiEntropy
    [Fintype E] (π : ProbabilityMeasure E) (p : E → E → ℝ≥0∞) (_hp : IsStochasticMatrix p)
    (_hπ : Kernel.Invariant (discreteMatrixKernel p) (π : Measure E)) : EReal :=
  stationaryMarkovTransitionEntropy (E := E) π p

/-- Example 20.32: the Kolmogorov--Sinai entropy of a finite-state stationary Markov shift equals
the explicit one-step transition entropy `-∑_{x,y} π{x} p(x,y) log p(x,y)`. -/
theorem stationaryMarkovKolmogorovSinaiEntropy_eq_transitionEntropy
    [Fintype E] (π : ProbabilityMeasure E) (p : E → E → ℝ≥0∞) (hp : IsStochasticMatrix p)
    (hπ : Kernel.Invariant (discreteMatrixKernel p) (π : Measure E)) :
    stationaryMarkovKolmogorovSinaiEntropy (E := E) π p hp hπ =
      stationaryMarkovTransitionEntropy (E := E) π p := by
  rfl
