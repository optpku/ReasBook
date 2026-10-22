/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_30
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Definition_16_1

open Filter
open scoped Topology

universe u

namespace ERealFunction

section SubdifferentialCalculus

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- On the real-height graph of `f`, adding the indicator of `dom (∂ f)` simply cuts out the graph
-- points whose base point is subdifferentiable.
omit [CompleteSpace H] in
@[simp] theorem mem_graph_add_indicator_subdifferentiabilityDomain_iff
    {f : H → Set.Ioi (⊥ : EReal)} (p : graph f.asEReal) :
    ((p : H × ℝ) ∈ graph ((f + ι[SetValuedOperator.dom (∂ f)]).asEReal)) ↔
      SubdifferentiableAt f p.1.1 := by
  rcases p with ⟨⟨x, ξ⟩, hp⟩
  rw [subdifferentiableAt_iff_mem_dom]
  by_cases hx : x ∈ SetValuedOperator.dom (∂ f)
  · simpa [add_apply, indicator_apply, hx] using hp
  · have hfx_ne_bot : (f x : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
    have hsum : ((f x : EReal) + ⊤) = ⊤ := EReal.add_top_of_ne_bot hfx_ne_bot
    simp [add_apply, indicator_apply, hx, hsum]

-- Proof sketch: the constrained graph from the textbook is exactly the subgraph cut out by the
-- owner predicate `SubdifferentiableAt`, so density can be stated directly on `graph f.asEReal`.
-- Proposition 9.19 then approximates each finite graph point `(x, (f x).toReal)` by graph points
-- above subdifferentiability points.
/-- Proposition 16.38: for `f ∈ Γ₀(H)`, the graph of the constrained function
`f + ι[dom (∂ f)]` is dense in the graph of `f`. -/
theorem graph_subdifferentiableAt_dense_in_graph_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    Dense {p : graph f.asEReal | SubdifferentiableAt f p.1.1} := sorry

-- Proof sketch: apply the graph-density theorem to the point `(x, (f x).toReal)` of
-- `graph f.asEReal`, then use the metric-space characterization of closure in the graph subtype to
-- extract nearby graph points above subdifferentiability points.
/-- A point of the effective domain can be approximated by subdifferentiability points with both
base points and function values converging. -/
theorem exists_subdifferentiableAt_sequence_tendsto_of_mem_effectiveDomain_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x : H} (hx : x ∈ effectiveDomain f) :
    ∃ xSeq : ℕ → H,
      (∀ n : ℕ, SubdifferentiableAt f (xSeq n)) ∧
      Tendsto xSeq atTop (𝓝 x) ∧
      Tendsto (fun n : ℕ ↦ (f (xSeq n) : EReal).toReal) atTop (𝓝 ((f x : EReal).toReal)) := sorry

end SubdifferentialCalculus

end ERealFunction
