/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap18.Proposition_18_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

section SymmetricSecondDifferences

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

/- Source/core/bridge triage:
- `source-facing`: Proposition 18.2 packages the source set `S_ε`.
- `core/canonical`: Proposition 18.1 already owns the pointwise predicate
  `HasSymmetricSecondDifferenceBound f x ε`.
- `bridge/view`: this file turns that pointwise owner into the set-valued surface `S_ε`.
-/

/-- The source-defined set `S_ε`: continuity points `x ∈ cont f` for which some positive symmetric
second-difference quotient has unit-sphere supremum strictly below `ε`. -/
noncomputable def symmetricSecondDifferenceSublevelSet
    (f : H → Set.Ioi (⊥ : EReal)) (ε : Set.Ioi (0 : ℝ)) : Set H :=
  {x | x ∈ cont f ∧ HasSymmetricSecondDifferenceBound f x ε}

-- Proof sketch: unfold the defining set-builder for `S_ε`.
/-- Membership in `S_ε` means source continuity `x ∈ cont f` together with the Chapter 18
symmetric second-difference bound at tolerance `ε`. -/
@[simp] theorem mem_symmetricSecondDifferenceSublevelSet_iff
    (f : H → Set.Ioi (⊥ : EReal)) (ε : Set.Ioi (0 : ℝ)) (x : H) :
    x ∈ symmetricSecondDifferenceSublevelSet f ε ↔
      x ∈ cont f ∧ HasSymmetricSecondDifferenceBound f x ε :=
  Iff.rfl

end SymmetricSecondDifferences

section EkelandLebourgTheorem

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

-- Proof sketch: for `x ∈ S_ε`, fix a witness `η > 0` with symmetric second-difference supremum
-- `σ < ε`. The source continuity datum `x ∈ cont f` already provides a ball contained in
-- `effectiveDomain f` and ambient continuity of the finite-valued representative there, so the
-- convex continuity theorem gives a Lipschitz bound on a smaller ball. Then Proposition 9.27
-- controls the same symmetric second-difference quotient at nearby points by `σ` plus a Lipschitz
-- error term, so a smaller ball around `x` remains in `S_ε`.
/-- Proposition 18.2: for a convex `]-∞,+∞]`-valued function, the set `S_ε` of continuity points
`x ∈ cont f` admitting some positive symmetric second-difference radius whose unit-sphere
supremum is strictly below `ε` is open. -/
theorem isOpen_symmetricSecondDifferenceSublevelSet
    (f : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn f (effectiveDomain f)) (ε : Set.Ioi (0 : ℝ)) :
    IsOpen (symmetricSecondDifferenceSublevelSet f ε) := sorry

end EkelandLebourgTheorem

end ERealFunction
