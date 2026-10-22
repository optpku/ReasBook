/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_21
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Function InnerProductSpace Pointwise SetValuedOperator

universe u

namespace ERealFunction

noncomputable section

open SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/- Source/core/bridge triage:
- `source-facing`: Example 16.54 states the reflected-function subdifferential formula.
- `core/canonical`: the owner abstractions are the subdifferential `∂ f`, function reversal `fᵛ`,
  operator reversal `Aᵛ`, and pointwise operator negation.
- `bridge/view`: this file identifies the source-facing reflected subdifferential with the
  canonical composite owner `-(∂ f)ᵛ`.
-/

-- Proof sketch: unfold membership in the two subdifferentials and rewrite the defining affine
-- minorant inequality for `fᵛ` by substituting `z = -y`; the inner-product term then becomes
-- `⟪z - (-x), -u⟫`, which is exactly the subgradient condition for membership in the canonical
-- reflected operator `-(∂ f)ᵛ` at `x`.
/-- Membership in the subdifferential of the reflected function is exactly membership in the
canonical reflected operator `-(∂ f)ᵛ`. Here the reflected
`EReal`-valued owner of the function is `(f.asEReal)ᵛ`. -/
@[simp] theorem mem_subdifferential_reverse_iff
    (f : H → Set.Ioi (⊥ : EReal)) (x u : H) :
    u ∈ (∂ fᵛ) x ↔ u ∈ (-((∂ f : SetValuedOperator H H)ᵛ)) x := by
  constructor
  · intro hu
    rw [mem_subdifferential_iff] at hu
    change
      ∀ z : H, (⟪z - x, u⟫_ℝ : EReal) + (f (-x) : EReal) ≤ (f (-z) : EReal) at hu
    change u ∈ -((((∂ f : SetValuedOperator H H)ᵛ) x))
    rw [Set.mem_neg, mem_reverse_iff, mem_subdifferential_iff]
    change
      ∀ y : H, (⟪y - (-x), -u⟫_ℝ : EReal) + (f (-x) : EReal) ≤ (f y : EReal)
    intro y
    specialize hu (-y)
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, inner_add_left,
      inner_add_right, inner_neg_left, inner_neg_right] using hu
  · intro hu
    rw [mem_subdifferential_iff]
    change u ∈ -((((∂ f : SetValuedOperator H H)ᵛ) x)) at hu
    rw [Set.mem_neg, mem_reverse_iff, mem_subdifferential_iff] at hu
    change
      ∀ z : H, (⟪z - (-x), -u⟫_ℝ : EReal) + (f (-x) : EReal) ≤ (f z : EReal) at hu
    change
      ∀ y : H, (⟪y - x, u⟫_ℝ : EReal) + (f (-x) : EReal) ≤ (f (-y) : EReal)
    intro y
    specialize hu (-y)
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, inner_add_left,
      inner_add_right, inner_neg_left, inner_neg_right] using hu

-- Proof sketch: extensionality on `H` reduces the operator identity to pointwise equality of
-- value sets, and the previous membership characterization identifies each side with the same
-- condition `u ∈ (-(∂ f)ᵛ) x`.
/-- Example 16.54: for the reflected function `fᵛ` (the textbook `f^∨`, i.e. `(f.asEReal)ᵛ` at
the `EReal` layer), the subdifferential is the negative of the reflected subdifferential operator
`(∂ f)ᵛ`. -/
theorem subdifferential_reverse_eq_neg_reverse
    (f : H → Set.Ioi (⊥ : EReal)) :
    ∂ fᵛ = (-((((∂ f : SetValuedOperator H H)ᵛ) : SetValuedOperator H H)) :
      SetValuedOperator H H) := by
  ext x u
  exact mem_subdifferential_reverse_iff f x u

end

end ERealFunction
