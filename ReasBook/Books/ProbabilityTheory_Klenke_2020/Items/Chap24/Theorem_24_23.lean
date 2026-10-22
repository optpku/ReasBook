/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Definition_24_10

open MeasureTheory

noncomputable section

universe u v w

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E] [TopologicalSpace E] [Bornology E]
variable {F : Type w} [MeasurableSpace F] [TopologicalSpace F] [Bornology F]

/-- Helper for Theorem 24.23: the colored point process obtained by pushing `X ω` forward along
`x ↦ (x, Y x ω)`. -/
def coloredPointProcess
    (X : Ω → Measure E) (Y : E → Ω → F) : Ω → Measure (E × F) :=
  fun ω ↦ Measure.map (fun x ↦ (x, Y x ω)) (X ω)

/-- Theorem 24.23 (Coloring theorem): source-facing statement asserting that the colored point
process built from `X` and the mark field `Y` is a Poisson point process on `E × F` with
intensity `(μ : Measure E).prod (ν : Measure F)`. -/
def coloredPointProcess_isPoissonPointProcess
    (P : ProbabilityMeasure Ω) (μ : Measure E) (ν : ProbabilityMeasure F)
    (X : Ω → Measure E) (Y : E → Ω → F) : Prop :=
  IsPoissonPointProcess ((μ : Measure E).prod (ν : Measure F)) P (coloredPointProcess X Y)

/-- Unfolding `coloredPointProcess_isPoissonPointProcess` gives exactly the Poisson point-process
statement for `coloredPointProcess X Y` with product intensity `(μ : Measure E).prod (ν : Measure
F)`. -/
theorem coloredPointProcess_isPoissonPointProcess_iff
    (P : ProbabilityMeasure Ω) (μ : Measure E) (ν : ProbabilityMeasure F)
    (X : Ω → Measure E) (Y : E → Ω → F) :
    coloredPointProcess_isPoissonPointProcess P μ ν X Y ↔
      IsPoissonPointProcess ((μ : Measure E).prod (ν : Measure F)) P
        (coloredPointProcess X Y) := by
  rfl

end ProbabilityTheory
