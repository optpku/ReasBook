/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open MeasureTheory

variable {E : Type u} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace.PseudoMetrizableSpace E] [SigmaCompactSpace E]

-- Proof sketch: the forward implication extracts local finiteness from `IsRadonMeasure μ` and
-- then uses the owner instance `isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure`.
-- Conversely, the explicit source-facing local finiteness hypothesis combines with
-- `IsFiniteMeasureOnCompacts μ` to give `σ`-finiteness and, via the owner regularity API
-- `Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure`, inner regularity.
/-- Exercise 13.1.8: on a `σ`-compact pseudometrizable Borel space, a locally finite Borel measure
is Radon exactly when it is finite on compact sets, i.e. exactly when it satisfies
`IsFiniteMeasureOnCompacts`. -/
theorem isRadonMeasure_iff_isFiniteMeasureOnCompacts (μ : Measure E)
    (hμloc : IsLocallyFiniteMeasure μ) :
    IsRadonMeasure μ ↔ IsFiniteMeasureOnCompacts μ := by
  constructor
  · intro hμ
    letI : IsLocallyFiniteMeasure μ := hμ.locallyFinite
    infer_instance
  · intro hμ
    letI : IsLocallyFiniteMeasure μ := hμloc
    letI : IsFiniteMeasureOnCompacts μ := hμ
    exact IsRadonMeasure.of_owner μ
