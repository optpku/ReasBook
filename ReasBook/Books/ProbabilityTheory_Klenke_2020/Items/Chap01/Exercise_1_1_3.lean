/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {Ω₁ : Type u} {Ω₂ : Type v}
  [MetricSpace Ω₁] [MeasurableSpace Ω₁] [BorelSpace Ω₁] [MetricSpace Ω₂]

-- Proof sketch: The set `{x | ContinuousAt f x}` is a `Gδ` set in a metrizable domain with
-- pseudometrizable codomain, hence it is Borel measurable by
-- `measurableSet_of_continuousAt`. The discontinuity set is its complement.
/-- Exercise 1.1.3: For a map between metric spaces, the set of points at which the map is
discontinuous is a Borel subset of the domain. -/
theorem discontinuity_set_measurable (f : Ω₁ → Ω₂) :
    MeasurableSet {x : Ω₁ | ¬ ContinuousAt f x} := by
  simpa [Set.compl_setOf] using (measurableSet_of_continuousAt f).compl
