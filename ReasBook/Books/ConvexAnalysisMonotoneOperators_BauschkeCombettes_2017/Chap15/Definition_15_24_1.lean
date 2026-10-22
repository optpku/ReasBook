/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace Set

section RealNormedSpace

variable {H : Type u} [SeminormedAddCommGroup H] [NormedSpace ℝ H]

/-- A closed half-space is cut out by a continuous linear functional and a real offset. -/
def closedHalfspace (ℓ : H →L[ℝ] ℝ) (η : ℝ) : Set H :=
  ℓ ⁻¹' Set.Iic η

/-- Membership in a closed half-space means satisfying the defining affine inequality. -/
theorem mem_closedHalfspace_iff {ℓ : H →L[ℝ] ℝ} {η : ℝ} {x : H} :
    x ∈ closedHalfspace ℓ η ↔ ℓ x ≤ η :=
  Iff.rfl

/-- Definition 15.24.1 (1): a subset of `H` is polyhedral when it is a finite intersection of
closed half-spaces. -/
def IsPolyhedral (C : Set H) : Prop :=
  ∃ t : Finset ((H →L[ℝ] ℝ) × ℝ), C = ⋂ p ∈ t, closedHalfspace p.1 p.2

/-- A set is polyhedral exactly when it can be written as a finite intersection of closed
half-spaces. -/
theorem isPolyhedral_iff {C : Set H} :
    IsPolyhedral C ↔
      ∃ t : Finset ((H →L[ℝ] ℝ) × ℝ),
        C = ⋂ p ∈ t, closedHalfspace p.1 p.2 :=
  Iff.rfl

end RealNormedSpace

end Set

namespace ERealFunction

section RealNormedSpace

variable {H : Type u} [SeminormedAddCommGroup H] [NormedSpace ℝ H]

/-- Definition 15.24.1 (2): an extended-real-valued function on `H` is polyhedral when its
epigraph is a polyhedral subset of `H × ℝ`. -/
def Polyhedral (f : H → EReal) : Prop :=
  (epigraph f).IsPolyhedral

/-- A function is polyhedral exactly when its epigraph is a polyhedral set. -/
theorem polyhedral_iff {f : H → EReal} :
    Polyhedral f ↔ (epigraph f).IsPolyhedral :=
  Iff.rfl

end RealNormedSpace

end ERealFunction
