/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Definition_14_40
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_23
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_43
import Mathlib

open MeasureTheory ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E] [Countable E]

/-- Helper for Exercise 17.6.2: the source-facing generator hypothesis used in this item asks for
the singleton right-derivative formula at time `0`. -/
def HasGeneratorMatrixAtSingletons
    (κ : NNReal → Kernel E E) (q : E → E → ℝ) : Prop :=
  ∀ x y : E,
    Filter.Tendsto
      (fun t : NNReal ↦
        ((((κ t) x).real ({y} : Set E)) - (((κ 0) x).real ({y} : Set E))) / (t : ℝ))
      (nhdsWithin (0 : NNReal) (Set.Ioi 0)) (nhds (q x y))

/-- Exercise 17.6.2: for a continuous-time Markov semigroup `κ` with generator matrix `q`, a
probability measure `π` is invariant exactly when each generator column has zero `π`-weighted
sum. In Lean, the source statement `∑ x, π({x}) q(x,y) = 0` is recorded as
`HasSum (fun x ↦ (π : Measure E).real {x} * q x y) 0`. -/
def invariantDistributionQMatrixBalance
    (κ : NNReal → Kernel E E) (q : E → E → ℝ) (π : ProbabilityMeasure E) : Prop :=
  IsMarkovSemigroup κ →
    IsQMatrix q →
      HasGeneratorMatrixAtSingletons κ q →
        ((∀ t : NNReal, Kernel.Invariant (κ t) (π : Measure E)) ↔
          ∀ y : E, HasSum (fun x : E ↦ (π : Measure E).real ({x} : Set E) * q x y) 0)

end ProbabilityTheory
