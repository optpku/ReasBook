/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap23.Definition_23_6

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped Topology

noncomputable section

universe u v

namespace ProbabilityTheory

/-- The positive parameter space `ε > 0` used in Definition 23.7. -/
abbrev PositiveParameter := Set.Ioi (0 : ℝ)

/-- A family of probability measures indexed by positive parameters. -/
abbrev PositiveProbabilityFamily (E : Type u) [MeasurableSpace E] :=
  PositiveParameter → ProbabilityMeasure E

/-- The filter describing the regime `ε ↓ 0` on the positive parameter space. -/
def positiveParameterFilter : Filter PositiveParameter :=
  Filter.comap ((↑) : PositiveParameter → ℝ) (𝓝[>] (0 : ℝ))

variable {E : Type u} [MeasurableSpace E]

/-- The scaled logarithmic mass `εᵢ log μᵢ(s)` associated with a reindexing `i ↦ εᵢ > 0`. -/
def scaledLogMassAlong {ι : Type v}
    (μ : ι → Measure E) (ε : ι → PositiveParameter) (s : Set E) (i : ι) : EReal :=
  ((ε i : ℝ) : EReal) * ENNReal.log ((μ i) s)

/-- Unfolding `scaledLogMassAlong` gives the reindexed scaled logarithmic mass `εᵢ log μᵢ(s)`. -/
theorem scaledLogMassAlong_def {ι : Type v}
    (μ : ι → Measure E) (ε : ι → PositiveParameter) (s : Set E) (i : ι) :
    scaledLogMassAlong μ ε s i = ((ε i : ℝ) : EReal) * ENNReal.log ((μ i) s) := rfl

variable [TopologicalSpace E]

/-- The core/canonical large deviations owner: a family of probability measures indexed by `ι`,
with positive speed parameters `ε i`, satisfies the large deviations principle along the ambient
filter `l` with rate function `I` if `I` is lower semicontinuous and the lower/upper bounds hold
for the logarithmic asymptotics `εᵢ log μᵢ(·)` along `l`. -/
class HasLargeDeviationsPrincipleAlong {ι : Type v}
    (μ : outParam (ι → ProbabilityMeasure E)) (ε : outParam (ι → PositiveParameter))
    (l : outParam (Filter ι)) (I : E → ENNReal) : Prop where
  /-- The candidate rate function is lower semicontinuous. -/
  lowerSemicontinuous : LowerSemicontinuous I
  /-- The logarithmic lower bound holds on every open set. -/
  open_lower_bound :
    ∀ ⦃U : Set E⦄, IsOpen U →
      -sInf ((fun x ↦ (I x : EReal)) '' U) ≤
        liminf (scaledLogMassAlong (fun i ↦ (μ i : Measure E)) ε U) l
  /-- The logarithmic upper bound holds on every closed set. -/
  closed_upper_bound :
    ∀ ⦃C : Set E⦄, IsClosed C →
      limsup (scaledLogMassAlong (fun i ↦ (μ i : Measure E)) ε C) l ≤
        -sInf ((fun x ↦ (I x : EReal)) '' C)

/-- Definition 23.7: the source-facing `ε ↓ 0` large deviations principle is the specialization of
`HasLargeDeviationsPrincipleAlong` to the positive-parameter family `μ : ε ↦ μ_ε` along the
canonical filter `positiveParameterFilter`. -/
abbrev HasLargeDeviationsPrinciple
    (μ : outParam (PositiveProbabilityFamily E)) (I : E → ENNReal) : Prop :=
  HasLargeDeviationsPrincipleAlong μ id positiveParameterFilter I

end ProbabilityTheory
