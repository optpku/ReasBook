/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Definition_3_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_19
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Corollary_20_59

-- Declarations for this item will be appended below by the statement pipeline.

open EuclideanGeometry
open Filter
open scoped InnerProductSpace SetValuedOperator Topology

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

section

variable {C D : AffineSubspace ℝ H}
variable (hC_nonempty : (C : Set H).Nonempty) (hC_closed : IsClosed (C : Set H))
variable (hD_nonempty : (D : Set H).Nonempty) (hD_closed : IsClosed (D : Set H))

local notation "hC" =>
  isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed C.convex

local notation "hD" =>
  isChebyshev_of_nonempty_isClosed_convex hD_nonempty hD_closed D.convex

/- Source/core/bridge triage:
- `source-facing`: Proposition 20.60 itself is the strong-convergence graph statement from the
  source text.
- `core/canonical`: the owner abstraction is maximal monotonicity `Maximal IsMonotone A` together
  with graph membership in `gra A`.
- `bridge/view`: weak-space transport via `toWeakSpace ℝ H` is auxiliary proof/API structure; the
  weak-sequence theorem below is a companion variant, not the main source-facing entry. -/

-- Proof sketch: first use `Corollary 3.35` on the strongly convergent shadow sequences
-- `fun n ↦ P[(C : Set H), hC] (xSeq n)` and
-- `fun n ↦ P[(D : Set H), hD] (uSeq n)` to obtain `x ∈ C` and `u ∈ D`. Then
-- use weak continuity of these metric projection maps from
-- `Proposition 4.19`, together with
-- `Lemma 2.51 (3)`, to prove the pairing convergence. This gives the `limsup` bound needed to
-- apply `Corollary 20.59 (3)`, yielding `(x, u) ∈ gra A`; together with `x ∈ C` and `u ∈ D`,
-- this gives the claimed membership in `((C : Set H) ×ˢ (D : Set H)) ∩ gra A`.
/-- Proposition 20.60: if graph points of a maximally monotone operator converge strongly and their
residuals with respect to the canonical metric projectors `P[(C : Set H), hC]` and
`P[(D : Set H), hD]` onto nonempty closed affine subspaces `C` and `D` with
`D.direction = C.directionᗮ` converge strongly to `0`, then the pairings converge to `⟪x, u⟫`
and the limit pair belongs to `((C : Set H) ×ˢ (D : Set H)) ∩ gra A`. -/
theorem
    Maximal.tendsto_inner_and_mem_prod_inter_graph_of_strong_graph_seq_of_projection_residual_zero
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A)
    (hCD : D.direction = C.directionᗮ)
    {xSeq uSeq : ℕ → H} {x u : H}
    (hgraph : ∀ n, (xSeq n, uSeq n) ∈ gra A)
    (hxSeq : Tendsto xSeq atTop (𝓝 x))
    (huSeq : Tendsto uSeq atTop (𝓝 u))
    (hCproj : Tendsto (fun n ↦ xSeq n - P[(C : Set H), hC] (xSeq n))
      atTop (𝓝 (0 : H)))
    (hDproj : Tendsto (fun n ↦ uSeq n - P[(D : Set H), hD] (uSeq n))
      atTop (𝓝 (0 : H))) :
    Tendsto (fun n ↦ ⟪xSeq n, uSeq n⟫_ℝ) atTop (𝓝 ⟪x, u⟫_ℝ) ∧
      (x, u) ∈ ((C : Set H) ×ˢ (D : Set H)) ∩ gra A := sorry

/-- Weak-convergence companion to Proposition 20.60: the same conclusion holds if the graph points
converge weakly and the projection residuals converge strongly to `0`. -/
theorem
    Maximal.tendsto_inner_and_mem_prod_inter_graph_of_weak_graph_seq_of_projection_residual_zero
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A)
    (hCD : D.direction = C.directionᗮ)
    {xSeq uSeq : ℕ → H} {x u : H}
    (hgraph : ∀ n, (xSeq n, uSeq n) ∈ gra A)
    (hxSeq : Tendsto (fun n ↦ toWeakSpace ℝ H (xSeq n)) atTop (𝓝 (toWeakSpace ℝ H x)))
    (huSeq : Tendsto (fun n ↦ toWeakSpace ℝ H (uSeq n)) atTop (𝓝 (toWeakSpace ℝ H u)))
    (hCproj : Tendsto (fun n ↦ xSeq n - P[(C : Set H), hC] (xSeq n))
      atTop (𝓝 (0 : H)))
    (hDproj : Tendsto (fun n ↦ uSeq n - P[(D : Set H), hD] (uSeq n))
      atTop (𝓝 (0 : H))) :
    Tendsto (fun n ↦ ⟪xSeq n, uSeq n⟫_ℝ) atTop (𝓝 ⟪x, u⟫_ℝ) ∧
      (x, u) ∈ ((C : Set H) ×ˢ (D : Set H)) ∩ gra A := sorry

end

end SetValuedOperator
