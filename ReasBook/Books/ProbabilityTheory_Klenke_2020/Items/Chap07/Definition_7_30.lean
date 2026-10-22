/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 7.30: For measures `μ` and `ν` on a measurable space, the textbook relation
`ν ≪ μ` of absolute continuity is the canonical mathlib predicate
`MeasureTheory.Measure.AbsolutelyContinuous ν μ`. Equivalent measures are characterized by mutual
absolute continuity, equivalently by equality of the almost-everywhere filters `ae μ = ae ν`, and
singularity is the canonical predicate `μ ⟂ₘ ν`. -/
recall MeasureTheory.Measure.AbsolutelyContinuous

open MeasureTheory
open scoped MeasureTheory

universe u

namespace MeasureTheory
namespace Measure

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Two measures are equivalent exactly when they induce the same almost-everywhere filter. -/
theorem ae_eq_iff {μ ν : Measure Ω} : ae μ = ae ν ↔ μ ≪ ν ∧ ν ≪ μ := by
  rw [le_antisymm_iff, ae_le_iff_absolutelyContinuous, ae_le_iff_absolutelyContinuous]

end Measure
end MeasureTheory

/- The textbook notion that `μ` is singular with respect to `ν` is the canonical mathlib
predicate `MeasureTheory.Measure.MutuallySingular`, written `μ ⟂ₘ ν` in the `MeasureTheory`
locale. -/
recall MeasureTheory.Measure.MutuallySingular
