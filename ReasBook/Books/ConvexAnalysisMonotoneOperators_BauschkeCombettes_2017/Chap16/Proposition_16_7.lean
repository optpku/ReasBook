/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Remark_9_37
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace ERealFunction

section Subdifferentials

variable {I : Type v} [Finite I]
variable {H : I → Type u}
variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]

-- Proof sketch: if `u ∈ ∂ f x`, then the subgradient inequality for `f` at `x` can be tested on
-- the slice `coordinateSlice x i yi`; this yields the subgradient inequality for the scalar slice
-- function `f ∘ coordinateSlice x i` at `x i` with slope `u i`, for every `i`.
/-- Proposition 16.7: every subgradient of a function on a finite Hilbert direct sum yields
coordinatewise subgradients of the slice functions obtained by freezing all but one coordinate. -/
theorem subdifferential_subset_coordinatewise_subdifferential
    {f : lp H 2 → Set.Ioi (⊥ : EReal)} {x : lp H 2} :
    (∂ f) x ⊆ {u | ∀ i, u i ∈ (∂ (f ∘ coordinateSlice x i)) (x i)} := sorry

end Subdifferentials

end ERealFunction
