/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_10
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section SubdifferentialCalculus

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: for each `ε > 0`, Corollary 11.16 gives a
-- minimizer `z` of `x ↦ f x + ε * ‖x‖`. Fermat's rule from Theorem 16.3 yields
-- `0 ∈ (∂ (pointwiseAdd f (ε • normFunctionIoi))) z`, Corollary 16.48 splits this
-- subdifferential as a sum, and Example 16.32 identifies the norm subdifferential with the closed
-- unit ball. Hence for every `ε > 0` there is `u ∈ SetValuedOperator.range (∂ f)` with
-- `‖u‖ ≤ ε`, which implies `0 ∈ closure (SetValuedOperator.range (∂ f))`.
/- Source/core/bridge triage:
- `source-facing`: the printed proof and surrounding prose for Corollary 16.52 only justify the
  closure statement `0 ∈ closure (ran ∂ f)`, so the numbered entry must live directly at
  `closure (SetValuedOperator.range (∂ f))`.
- `core/canonical`: the owner objects are `∂ f`, `SetValuedOperator.range`, `closure`, and the
  canonical `EReal` coercion `f.asEReal`.
- `bridge/view`: no extra bridge owner is needed; the source-facing statement is already expressed
  directly in the canonical owner language.
-/
/-- Corollary 16.52: if `f ∈ Γ₀(H)` is bounded below, then `0` belongs to the closure of the
range of its subdifferential. -/
theorem zero_mem_closure_range_subdifferential_of_mem_gammaZero_of_bddBelow
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (hbounded : BddBelow (Set.range f)) :
    (0 : H) ∈ closure (SetValuedOperator.range (∂ f)) := sorry

end SubdifferentialCalculus

end ERealFunction
