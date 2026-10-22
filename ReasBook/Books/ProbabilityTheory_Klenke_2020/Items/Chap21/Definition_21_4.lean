/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_12

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

noncomputable section

universe u v w

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {I : Type v} [TopologicalSpace I]
variable {E : Type w} [TopologicalSpace E]

/-- Definition 21.4: an `I`-indexed stochastic process has almost surely continuous paths if for
almost every sample point `ω`, the path `t ↦ X t ω` is continuous. -/
def HasAlmostSurelyContinuousPaths (μ : Measure Ω) (X : I → Ω → E) : Prop :=
  ∀ᵐ ω ∂μ, Continuous (processPath X ω)

/-- A process has almost surely continuous paths exactly when almost every sample path is
continuous. -/
theorem hasAlmostSurelyContinuousPaths_iff (μ : Measure Ω) (X : I → Ω → E) :
    HasAlmostSurelyContinuousPaths μ X ↔
      ∀ᵐ ω ∂μ, Continuous (processPath X ω) :=
  Iff.rfl

end ProbabilityTheory
