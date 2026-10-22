/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open SetValuedOperator
open scoped InnerProductSpace

universe u

namespace ERealFunction

section SubdifferentialGraphClosedness

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/- Source/core/bridge triage:
- `source-facing`: Proposition 16.36 states mixed weak/strong sequential closedness for `gra ∂ f`.
- `core/canonical`: the owner object is the subdifferential `∂ f` with canonical graph
  `(∂ f).graph`.
- `bridge/view`: the weak-strong and strong-weak product topologies are expressed by the
  coordinatewise transports `Prod.map (toWeakSpace ℝ H) id` and `Prod.map id (toWeakSpace ℝ H)`.

The refinement therefore keeps `(∂ f).graph` as the public core and treats the strong-weak clause
as the swapped/inverse view of the same graph-closure phenomenon, not as a parallel owner. -/

-- Proof sketch: apply Theorem 16.29 to each graph point `(xₙ, uₙ)` to rewrite membership in
-- `gra ∂ f` as Fenchel--Young equality. Lower semicontinuity of `f` under weak convergence of the
-- first coordinate and of `f*` under strong convergence of the second coordinate force equality in
-- the limit, so Theorem 16.29 puts `(x, u)` back in `gra ∂ f`.
/-- Proposition 16.36: for `f ∈ Γ₀(H)`, the graph of the subdifferential is sequentially closed in
the mixed weak-strong product topology, encoded as sequential closedness of its image in
`WeakSpace ℝ H × H`. -/
theorem graph_subdifferential_isSeqClosed_weakStrong_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    IsSeqClosed ((Prod.map (toWeakSpace ℝ H) id) '' (∂ f).graph) := sorry

-- Proof sketch: apply the weak-strong statement to the Fenchel conjugate `f*`, use Corollary
-- 16.30 to rewrite `(∂ f)⁻¹` as `∂ f*`, and then swap the graph coordinates. This presents the
-- strong-weak statement as the inverse/swap view of the weak-strong closure theorem.
/-- The graph of the subdifferential of a `Γ₀(H)` function is also sequentially closed in the
mixed strong-weak product topology, encoded as sequential closedness of its image in
`H × WeakSpace ℝ H`. -/
theorem graph_subdifferential_isSeqClosed_strongWeak_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    IsSeqClosed ((Prod.map id (toWeakSpace ℝ H)) '' (∂ f).graph) := sorry

end SubdifferentialGraphClosedness

end ERealFunction
