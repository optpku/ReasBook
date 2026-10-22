/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open MeasureTheory Measure

variable {α : Type u} [TopologicalSpace α] [MeasurableSpace α]
variable {μ : Measure α}

/- Definition 13.3 (1): on a Borel space, the textbook "Borel measure" condition is expressed by
the canonical owner predicate `IsLocallyFiniteMeasure`. -/
recall IsLocallyFiniteMeasure

/- Definition 13.3 (2): inner regularity is the canonical owner predicate
`InnerRegular`. -/
recall InnerRegular

/- Definition 13.3 (3): outer regularity is the canonical owner predicate
`OuterRegular`. -/
recall OuterRegular

/-- Definition 13.3 (4): for measures on the Borel `σ`-algebra, the textbook notion "μ is
regular" means that `μ` is `σ`-finite and both inner regular and outer regular. -/
def IsRegularMeasure (μ : Measure α) : Prop :=
  SigmaFinite μ ∧ InnerRegular μ ∧ OuterRegular μ

/-- Definition 13.3 (5): for measures on the Borel `σ`-algebra, the textbook notion of a Radon
measure means that `μ` is `σ`-finite, inner regular, and locally finite. -/
def IsRadonMeasure (μ : Measure α) : Prop :=
  SigmaFinite μ ∧ InnerRegular μ ∧ IsLocallyFiniteMeasure μ

namespace IsRegularMeasure

theorem of_owner (μ : Measure α) [SigmaFinite μ] [InnerRegular μ] [OuterRegular μ] :
    IsRegularMeasure μ :=
  ⟨inferInstance, inferInstance, inferInstance⟩

theorem sigmaFinite (hμ : IsRegularMeasure μ) : SigmaFinite μ := by
  rcases hμ with ⟨hσ, -, -⟩
  exact hσ

theorem innerRegular (hμ : IsRegularMeasure μ) : InnerRegular μ := by
  rcases hμ with ⟨-, hinner, -⟩
  exact hinner

theorem outerRegular (hμ : IsRegularMeasure μ) : OuterRegular μ := by
  rcases hμ with ⟨-, -, houter⟩
  exact houter

end IsRegularMeasure

namespace IsRadonMeasure

theorem of_owner (μ : Measure α) [SigmaFinite μ] [InnerRegular μ]
    [IsLocallyFiniteMeasure μ] :
    IsRadonMeasure μ :=
  ⟨inferInstance, inferInstance, inferInstance⟩

theorem sigmaFinite (hμ : IsRadonMeasure μ) : SigmaFinite μ := by
  rcases hμ with ⟨hσ, -, -⟩
  exact hσ

theorem innerRegular (hμ : IsRadonMeasure μ) : InnerRegular μ := by
  rcases hμ with ⟨-, hinner, -⟩
  exact hinner

theorem locallyFinite (hμ : IsRadonMeasure μ) : IsLocallyFiniteMeasure μ := by
  rcases hμ with ⟨-, -, hloc⟩
  exact hloc

end IsRadonMeasure

/- Auxiliary owner recall: mathlib also provides the bundled class `Measure.Regular μ`, which is
organized around finiteness on compact sets, outer regularity, and compact approximation of open
sets. This is not the main source-facing owner for Definition 13.3, but it remains the canonical
stronger bridge for later results. -/
recall Regular
