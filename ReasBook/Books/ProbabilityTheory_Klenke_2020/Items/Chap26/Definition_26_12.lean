/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_22
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Definition_26_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Remark_26_3

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {n m : ℕ}

local notation "State" => Fin n → ℝ
local notation "PathSpace" => EuclideanPathSpace n

/-- Definition 26.12: a weak solution of the `n`-dimensional SDE with initial distribution `μ₀`
consists of a filtered probability space, a continuous state-path random variable `X`, and an
`m`-dimensional Brownian driver `W` such that `X₀` has law `μ₀` and `X` satisfies the ambient SDE
relation driven by `W`. -/
structure WeakSDESolution (n m : ℕ) (μ₀ : Measure State) [IsProbabilityMeasure μ₀]
    (SolvesSDE : {Ω : Type u} → [MeasurableSpace Ω] →
      Filtration NNReal (inferInstance : MeasurableSpace Ω) → Measure Ω →
      (Ω → PathSpace) → (NNReal → Ω → Fin m → ℝ) → Prop) where
  Ω : Type u
  instMeasurableSpace : MeasurableSpace Ω
  μ : Measure Ω
  instIsProbabilityMeasure : IsProbabilityMeasure μ
  ℱ : Filtration NNReal instMeasurableSpace
  instUsualConditions : Filtration.UsualConditions ℱ μ
  X : Ω → PathSpace
  W : NNReal → Ω → Fin m → ℝ
  brownian : IsStandardBrownianMotionVector μ (CoordinateProcess.toEuclidean W) ∧ Adapted ℱ W
  coordinate_martingale : ∀ i : Fin m, Martingale (fun t ω ↦ W t ω i) ℱ μ
  adapted : Adapted ℱ (fun t ω ↦ X ω t)
  initialLaw : HasLaw (fun ω ↦ X ω 0) μ₀ μ
  solves_sde : SolvesSDE ℱ μ X W

attribute [instance] WeakSDESolution.instMeasurableSpace WeakSDESolution.instIsProbabilityMeasure
  WeakSDESolution.instUsualConditions

/-- A weak SDE solution is callable as its underlying continuous state-path random variable. -/
instance weakSDESolutionCoeFun {μ₀ : Measure State} [IsProbabilityMeasure μ₀]
    {SolvesSDE : {Ω : Type u} → [MeasurableSpace Ω] →
      Filtration NNReal (inferInstance : MeasurableSpace Ω) → Measure Ω →
      (Ω → PathSpace) → (NNReal → Ω → Fin m → ℝ) → Prop} :
    CoeFun (WeakSDESolution n m μ₀ SolvesSDE) (fun L ↦ L.Ω → PathSpace) where
  coe := WeakSDESolution.X

/-- The law of the continuous state-path random variable carried by a weak SDE solution. -/
abbrev WeakSDESolution.statePathLaw {μ₀ : Measure State} [IsProbabilityMeasure μ₀]
    {SolvesSDE : {Ω : Type u} → [MeasurableSpace Ω] →
      Filtration NNReal (inferInstance : MeasurableSpace Ω) → Measure Ω →
      (Ω → PathSpace) → (NNReal → Ω → Fin m → ℝ) → Prop}
    (L : WeakSDESolution n m μ₀ SolvesSDE) :
    Measure PathSpace :=
  L.μ.map L.X

/-- A weak solution is weakly unique if every other weak solution with the same initial
distribution induces the same law on the continuous state-path space. -/
def WeakSDESolution.IsWeaklyUnique {μ₀ : Measure State} [IsProbabilityMeasure μ₀]
    {SolvesSDE : {Ω : Type u} → [MeasurableSpace Ω] →
      Filtration NNReal (inferInstance : MeasurableSpace Ω) → Measure Ω →
      (Ω → PathSpace) → (NNReal → Ω → Fin m → ℝ) → Prop}
    (L : WeakSDESolution n m μ₀ SolvesSDE) : Prop :=
  ∀ L' : WeakSDESolution n m μ₀ SolvesSDE, L'.statePathLaw = L.statePathLaw

end ProbabilityTheory
