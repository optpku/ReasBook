/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Remark_9_37
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Proposition_16_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace ERealFunction

section Subdifferentials

variable {I : Type v} [Fintype I]
variable {H : I → Type u}
variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]

-- Proof sketch: for the forward inclusion, specialize Proposition 16.7 to the direct-sum
-- function and identify each coordinate slice with the corresponding summand up to an additive
-- constant. For the reverse inclusion, choose one effective-domain point in every frozen
-- coordinate, expand the coordinate subgradient inequalities, and sum them to obtain the global
-- subgradient inequality for `directSumFunction f`.
/-- Proposition 16.9: for a finite family of `]-∞,+∞]`-valued functions with nonempty effective
domains, the subdifferential of the direct-sum function is the coordinatewise Cartesian product of
the subdifferentials of the summands. -/
theorem subdifferential_directSumFunction_eq_coordinatewise
    (f : ∀ i, H i → Set.Ioi (⊥ : EReal))
    (hdom : ∀ i, (effectiveDomain (f i)).Nonempty)
    (x : lp H 2) :
    (∂ (directSumFunction f)) x = {u : lp H 2 | ∀ i, u i ∈ (∂ (f i)) (x i)} := sorry

end Subdifferentials

end ERealFunction
