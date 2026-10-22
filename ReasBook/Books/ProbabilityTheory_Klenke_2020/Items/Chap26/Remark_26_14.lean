/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Remark_26_3

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {n m : ℕ}

local notation "TimeFiltration" => Filtration NNReal mΩ
local notation "State" => Fin n → ℝ
local notation "StatePath" => EuclideanPathSpace n
local notation "StateProcess" => NNReal → Ω → State
local notation "BrownianProcess" => NNReal → Ω → Fin m → ℝ
local notation "NoisePath" => EuclideanPathSpace m

/-- The state process obtained by evaluating a solver functional on the initial state and the
sample Brownian path. -/
def transportedProcess
    (F : State → (NNReal → Fin m → ℝ) → NNReal → State)
    (ξ : Ω → State) (W : BrownianProcess) : StateProcess :=
  fun t ω ↦ F (ξ ω) (fun s ↦ W s ω) t

/-- A weak-solution realization of an `n`-dimensional SDE consists of a state process `X` with
progressively measurable continuous coordinates, together with the ambient driver condition and the
chosen SDE-solving relation. -/
def HasWeakSolutionRealization
    (NoiseCondition : BrownianProcess → Prop)
    (SolvesSDE : (Ω → State) → BrownianProcess → StateProcess → Prop)
    (ℱ : TimeFiltration) (ξ : Ω → State) (W : BrownianProcess) (X : StateProcess) : Prop :=
  (∀ i : Fin n, ProgMeasurable ℱ (fun t ω ↦ X t ω i)) ∧
  (∀ i : Fin n, ∀ ω : Ω, Continuous fun t ↦ X t ω i) ∧
    NoiseCondition W ∧
    SolvesSDE ξ W X

/-- A pathwise strong-solution realization is a weak-solution realization whose state process and
Brownian driver admit continuous-path lifts realizing the canonical `StrongSolution` owner from
Definition 26.1. -/
def HasPathwiseStrongSolutionRealization
    (NoiseCondition : BrownianProcess → Prop)
    (SolvesSDE : (Ω → State) → BrownianProcess → StateProcess → Prop)
    (ℱ : TimeFiltration) (ξ : Ω → State) (W : BrownianProcess) (X : StateProcess) : Prop :=
  HasWeakSolutionRealization NoiseCondition SolvesSDE ℱ ξ W X ∧
    ∃ Wpath : Ω → NoisePath,
      W = (fun t ω ↦ Wpath ω t) ∧
        ∃ Xpath : Ω → StatePath,
          X = (fun t ω ↦ Xpath ω t) ∧
            StrongSolution n m
              (fun ξ' W' X' ↦
                SolvesSDE ξ' (fun t ω ↦ W' ω t) (fun t ω ↦ X' ω t))
              ξ Wpath Xpath

-- Proof sketch: the hypotheses already contain the weak-solution realization clauses. The extra
-- `StrongSolution` witness records the Definition 26.1 pathwise-strong content and is discarded.
/-- Remark 26.14: every strong-solution realization of the `n`-dimensional SDE is also a
weak-solution realization; the following example shows that the converse fails in general. -/
theorem pathwiseStrongSolutionRealization_isWeakSolutionRealization
    {NoiseCondition : BrownianProcess → Prop}
    {SolvesSDE : (Ω → State) → BrownianProcess → StateProcess → Prop}
    {ℱ : TimeFiltration} {ξ : Ω → State} {W : BrownianProcess} {X : StateProcess}
    (hX : HasPathwiseStrongSolutionRealization NoiseCondition SolvesSDE ℱ ξ W X) :
    HasWeakSolutionRealization NoiseCondition SolvesSDE ℱ ξ W X :=
  hX.1

/-- The SDE-solving clause carried by a weak-solution realization. -/
theorem HasWeakSolutionRealization.solvesSDE
    {NoiseCondition : BrownianProcess → Prop}
    {SolvesSDE : (Ω → State) → BrownianProcess → StateProcess → Prop}
    {ℱ : TimeFiltration} {ξ : Ω → State} {W : BrownianProcess} {X : StateProcess}
    (hX : HasWeakSolutionRealization NoiseCondition SolvesSDE ℱ ξ W X) :
    SolvesSDE ξ W X :=
  hX.2.2.2

/-- The SDE-solving clause carried by a pathwise strong-solution realization. -/
theorem HasPathwiseStrongSolutionRealization.solvesSDE
    {NoiseCondition : BrownianProcess → Prop}
    {SolvesSDE : (Ω → State) → BrownianProcess → StateProcess → Prop}
    {ℱ : TimeFiltration} {ξ : Ω → State} {W : BrownianProcess} {X : StateProcess}
    (hX : HasPathwiseStrongSolutionRealization NoiseCondition SolvesSDE ℱ ξ W X) :
    SolvesSDE ξ W X :=
  (pathwiseStrongSolutionRealization_isWeakSolutionRealization hX).solvesSDE

end ProbabilityTheory
