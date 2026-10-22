/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Example_9_36

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H]

/-- The quadratic kernel `x ↦ (1 / (2γ)) ‖x‖^2` used in the definition of the Moreau envelope. -/
noncomputable def moreauQuadraticKernel (γ : Set.Ioi (0 : ℝ)) : H → Set.Ioi (⊥ : EReal) :=
  (fun x : H ↦ (1 / (2 * (γ : ℝ))) * ‖x‖ ^ 2).toEReal

/-- Coercing the Moreau quadratic kernel to `EReal` recovers the function
`x ↦ (1 / (2γ)) ‖x‖^2`. -/
@[simp]
theorem moreauQuadraticKernel_apply (γ : Set.Ioi (0 : ℝ)) (x : H) :
    (moreauQuadraticKernel γ x : EReal) = (((1 / (2 * (γ : ℝ))) * ‖x‖ ^ 2 : ℝ) : EReal) := by
  simp [moreauQuadraticKernel]

/-- The quadratic function `x ↦ ‖x‖² / 2`, viewed as a positive extended-real-valued function. -/
noncomputable abbrev halfSquaredNorm : H → Set.Ioi (⊥ : EReal) :=
  moreauQuadraticKernel ⟨(1 : ℝ), Set.mem_Ioi.2 zero_lt_one⟩

/-- Coercing `halfSquaredNorm` to `EReal` recovers the quadratic function `x ↦ ‖x‖² / 2`. -/
@[simp] theorem halfSquaredNorm_apply (x : H) :
    (halfSquaredNorm x : EReal) = ((((‖x‖ ^ 2) / 2 : ℝ) : EReal)) := sorry

end ERealFunction
