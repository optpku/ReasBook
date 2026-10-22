/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set

universe u

/- Remark 13.32: every singleton family of finite measures is weakly compact in the ambient weak
topology on `FiniteMeasure E`, so the converse direction of Prohorov's theorem cannot force
tightness without an additional hypothesis; the Polish hypothesis supplies that extra input. This
compactness part is the general theorem `isCompact_singleton`. -/
recall isCompact_singleton

variable {E : Type u} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E] [PolishSpace E]

/- The Polish-space tightness input is the canonical owner theorem
`MeasureTheory.isTightMeasureSet_singleton`; applied to a finite measure `μ`, it yields tightness
of `{(μ : Measure E)}` in `Measure E`. -/
recall MeasureTheory.isTightMeasureSet_singleton
