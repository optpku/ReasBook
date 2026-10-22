/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Proposition_20_58

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped InnerProductSpace SetValuedOperator Topology

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

section WeakGraphSequences

variable {A : SetValuedOperator H H} (hA : Maximal IsMonotone A)
variable {xSeq uSeq : ℕ → H} {x u : H}
variable (hgraph : ∀ n, (xSeq n, uSeq n) ∈ gra A)
variable (hxSeq : Tendsto (fun n ↦ toWeakSpace ℝ H (xSeq n)) atTop (𝓝 (toWeakSpace ℝ H x)))
variable (huSeq : Tendsto (fun n ↦ toWeakSpace ℝ H (uSeq n)) atTop (𝓝 (toWeakSpace ℝ H u)))

-- Proof sketch: apply weak lower semicontinuity of the Fitzpatrick function to the sequence
-- `(xSeq n, uSeq n)`, use Proposition 20.58 to bound `⟪x, u⟫` by `F_A(x, u)`, and rewrite
-- `F_A(xSeq n, uSeq n)` as `⟪xSeq n, uSeq n⟫` because every term lies in `gra A`.
/-- Corollary 20.59 (1): if graph points `(x_n, u_n)` of a maximally monotone operator converge
weakly to `(x, u)`, then the pairing is weakly lower semicontinuous along the sequence:
`⟪x, u⟫ ≤ liminf_n ⟪x_n, u_n⟫`. -/
theorem Maximal.inner_le_liminf_inner_of_tendsto_weakly_seq
    : ⟪x, u⟫_ℝ ≤ liminf (fun n ↦ ⟪xSeq n, uSeq n⟫_ℝ) atTop := sorry

-- Proof sketch: combine clause (1) with the assumed equality of the liminf and the limit pairing
-- to obtain `F_A(x, u) = ⟪x, u⟫`, then apply Proposition 20.58 to identify the graph with the
-- pairing-contact set of the Fitzpatrick function.
/-- Corollary 20.59 (2): if the weakly convergent graph sequence satisfies
`liminf_n ⟪x_n, u_n⟫ = ⟪x, u⟫`, then the weak limit pair still belongs to `gra A`. -/
theorem Maximal.mem_graph_of_liminf_inner_eq_of_tendsto_weakly_seq
    (hliminf : liminf (fun n ↦ ⟪xSeq n, uSeq n⟫_ℝ) atTop = ⟪x, u⟫_ℝ) :
    (x, u) ∈ gra A := sorry

-- Proof sketch: clause (1) gives the matching lower bound on the liminf, while the hypothesis
-- bounds the limsup above by `⟪x, u⟫`; squeezing liminf and limsup yields convergence of the real
-- pairing sequence, and clause (2) then gives graph membership of the weak limit pair.
/-- Corollary 20.59 (3): if moreover `limsup_n ⟪x_n, u_n⟫ ≤ ⟪x, u⟫`, then
`⟪x_n, u_n⟫ → ⟪x, u⟫` and the weak limit pair belongs to `gra A`. -/
theorem Maximal.tendsto_inner_and_mem_graph_of_limsup_inner_le_of_tendsto_weakly_seq
    (hlimsup : limsup (fun n ↦ ⟪xSeq n, uSeq n⟫_ℝ) atTop ≤ ⟪x, u⟫_ℝ) :
    Tendsto (fun n ↦ ⟪xSeq n, uSeq n⟫_ℝ) atTop (𝓝 ⟪x, u⟫_ℝ) ∧ (x, u) ∈ gra A := sorry

end WeakGraphSequences

end SetValuedOperator
