/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u} [TopologicalSpace H] [AddCommGroup H] [Module ℝ H]

/-- The lower semicontinuous convex minorants of an extended-real-valued function. -/
def lowerSemicontinuousConvexMinorants (f : H → EReal) : Set (H → EReal) :=
  {g | LowerSemicontinuous g ∧ Convex ℝ (epigraph g) ∧ g ≤ f}

/-- A function is a lower semicontinuous convex minorant of `f` exactly when it is lower
semicontinuous, has convex epigraph, and is pointwise dominated by `f`. -/
-- Proof sketch: unfold `lowerSemicontinuousConvexMinorants`; membership in the defining set is
-- exactly the displayed conjunction.
theorem mem_lowerSemicontinuousConvexMinorants_iff (f g : H → EReal) :
    g ∈ lowerSemicontinuousConvexMinorants f ↔
      LowerSemicontinuous g ∧ Convex ℝ (epigraph g) ∧ g ≤ f := by
  -- Unfolding the defining set shows that membership is exactly the displayed conjunction.
  rfl

/-- Definition 9.7: the lower semicontinuous convex envelope of `f` is the supremum, in the
function lattice, of all lower semicontinuous convex minorants of `f`. -/
noncomputable def lowerSemicontinuousConvexEnvelope (f : H → EReal) : H → EReal :=
  sSup (lowerSemicontinuousConvexMinorants f)

/-- The lower semicontinuous convex envelope is computed pointwise as the supremum of the values of
all lower semicontinuous convex minorants of `f` at that point. -/
-- Proof sketch: rewrite the function-lattice supremum pointwise using
-- `sSup_apply_eq_sSup_image`.
theorem lowerSemicontinuousConvexEnvelope_apply (f : H → EReal) (x : H) :
    lowerSemicontinuousConvexEnvelope f x =
      sSup ((fun g : H → EReal ↦ g x) '' lowerSemicontinuousConvexMinorants f) := by
  -- Evaluate the supremum in the function lattice at `x` and rewrite it as a supremum of values.
  change sSup (lowerSemicontinuousConvexMinorants f) x =
    sSup ((fun g : H → EReal ↦ g x) '' lowerSemicontinuousConvexMinorants f)
  exact sSup_apply_eq_sSup_image

end ERealFunction
