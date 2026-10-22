/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Definition_20_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/- Source/core/bridge triage:
- `source-facing`: Definition 20.51 directly defines the Fitzpatrick function `F_A` as the
  supremum over graph points of `A`.
- `core/canonical`: the owner abstractions reused here are the chapter's `SetValuedOperator.graph`
  on the source side and the ambient `EReal` supremum function space on the codomain side.
- `bridge/view`: the infimum reformulation below is a companion identity for the same owner, not a
  replacement owner. -/

/-- Definition 20.51: the Fitzpatrick function attached to a set-valued operator `A`; for
monotone `A`, this is the textbook Fitzpatrick function. It is the extended-real-valued function
on `H × H` obtained by taking the supremum of `⟪y, u⟫ + ⟪x, v⟫ - ⟪y, v⟫` over graph points
`(y, v) ∈ gra A`. The Lean surface notation for the textbook symbol `F_A` is `F[A]`. -/
noncomputable def fitzpatrickFunction (A : SetValuedOperator H H) : H × H → EReal :=
  fun (x, u) ↦
    ⨆ p : gra A, ((⟪p.1.1, u⟫_ℝ + ⟪x, p.1.2⟫_ℝ - ⟪p.1.1, p.1.2⟫_ℝ : ℝ) : EReal)

/- Lean cannot parse an arbitrary term as a literal subscript, so we use the bracketed surface
`F[A]` as the direct notation for the textbook Fitzpatrick function `F_A`. -/
scoped notation:max "F[" A:max "]" => fitzpatrickFunction A

open scoped SetValuedOperator

-- Proof sketch: for each graph point `(y, v)`, expand
-- `⟪y, u⟫ + ⟪x, v⟫ - ⟪y, v⟫ = ⟪x, u⟫ - ⟪x - y, u - v⟫`; then the first display is the
-- supremum of `⟪x, u⟫ - ...` over `gra A`, which is `⟪x, u⟫` minus the infimum term.
/-- Evaluating `F[A]` at `(x, u)` gives the pairing `⟪x, u⟫` minus the infimum
of `⟪x - y, u - v⟫` over `gra A`. -/
theorem fitzpatrickFunction_apply_eq_inner_sub_iInf (A : SetValuedOperator H H) (x u : H) :
    F[A] (x, u) =
      (⟪x, u⟫_ℝ : EReal) -
        ⨅ p : gra A, ((⟪x - p.1.1, u - p.1.2⟫_ℝ : ℝ) : EReal) := sorry

end SetValuedOperator
