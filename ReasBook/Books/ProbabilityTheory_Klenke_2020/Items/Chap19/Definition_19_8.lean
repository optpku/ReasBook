/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

module

public import Mathlib.Data.ENNReal.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

-- Declarations for this item will be appended below by the statement pipeline.

public section

open MeasureTheory
open scoped ENNReal

noncomputable section

universe u

namespace ProbabilityTheory

section

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]

/- Layering for Definition 19.8:
- `source-facing`: the singleton detailed-balance equation for `p` with respect to a measure `π`,
  and the plain notion that such a `π` exists.
- `core/canonical`: mathlib's owner `Kernel.IsReversible (discreteMatrixKernel p) π`.
- `bridge/view`: `SatisfiesDetailedBalance p π` is the raw singleton equation and
  `IsReversibleWithRespectTo p π` is a thin alias for that equation.
  The source definition does not identify this with the setwise owner on arbitrary discrete
  spaces, so no owner-level equivalence is part of the main item surface here.
  Countable or atomic hypotheses needed to upgrade singleton balance to setwise reversibility
  belong in later companion results, not in Definition 19.8 itself. -/
-- Semantic recall note: `lean_leansearch` points to the canonical owner
-- `ProbabilityTheory.Kernel.IsReversible`; local chapter files upgrade singleton detailed
-- balance to that setwise notion only under extra countability hypotheses, so this definition
-- stays at the source-faithful pointwise level.

/-- Helper for Definition 19.8: the equation of detailed balance is the singleton identity
`π {x} * p x y = π {y} * p y x` for all `x, y : E`. -/
def SatisfiesDetailedBalance (p : E → E → ℝ≥0∞) (π : Measure E) : Prop :=
  ∀ x y : E, p x y * π {x} = p y x * π {y}

/-- Definition 19.8: `p` is reversible with respect to the measure `π` if it satisfies the
detailed balance identities `π {x} * p x y = π {y} * p y x` for all `x, y : E`. -/
abbrev IsReversibleWithRespectTo (p : E → E → ℝ≥0∞) (π : Measure E) : Prop :=
  SatisfiesDetailedBalance p π

/-- Helper for Definition 19.8: a discrete matrix is reversible when there exists a measure with
respect to which the detailed balance identities hold. -/
def isReversible (p : E → E → ℝ≥0∞) : Prop :=
  ∃ π : Measure E, IsReversibleWithRespectTo p π

end

/-- The helper predicate `SatisfiesDetailedBalance p π` is exactly the singleton detailed-balance
equation. -/
theorem satisfiesDetailedBalance_iff
    {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]
    {p : E → E → ℝ≥0∞} {π : Measure E} :
    SatisfiesDetailedBalance p π ↔
      ∀ x y : E, p x y * π {x} = p y x * π {y} := by
  -- Unfold the source-facing predicate to expose the detailed-balance equation verbatim.
  rfl

/-- The source-facing reversibility predicate is exactly the singleton detailed-balance equation. -/
theorem isReversibleWithRespectTo_iff
    {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]
    {p : E → E → ℝ≥0∞} {π : Measure E} :
    IsReversibleWithRespectTo p π ↔
      ∀ x y : E, p x y * π {x} = p y x * π {y} := by
  -- Expand the abbreviation and reduce to the detailed-balance predicate companion theorem.
  rfl

/-- A discrete matrix is reversible exactly when it admits a measure satisfying the detailed
balance identities from Definition 19.8. -/
theorem isReversible_iff_exists_measure
    {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]
    {p : E → E → ℝ≥0∞} :
    isReversible p ↔
      ∃ π : Measure E, IsReversibleWithRespectTo p π := by
  -- Unfold the existential source-facing definition of reversibility.
  rfl

end ProbabilityTheory
