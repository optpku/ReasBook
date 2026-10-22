/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_3_24

/-!
Chapter01 Corollary 1.3.25 lives in convex separation.

Domain sampling:
* mathlib's closed-point separation theorem `geometric_hahn_banach_closed_point`;
* the chapter's source-facing supporting-sunYuanHyperplane theorem
  `existsSupportingHyperplaneAt_of_mem_frontier`;
* the chapter bridge/view `existsNonzeroSupportingVectorOnClosure`.

Best owner abstraction:
* the core/canonical proof engine is Hahn-Banach separation in the dual;
* the chapter owner for the frontier case is the oriented half-space bridge
  `existsNonzeroSupportingVectorOnClosure`;
* this corollary itself stays `source-facing`, because the textbook statement is exactly the
  anchored inequality on `closure S`.

Primitive data:
* `S`, `hS_nonempty`, `hS_convex`, `xbar`, `hxbar`.

Derived API:
* a nonzero vector `p` with `⟪p, x - xbar⟫ ≤ 0` for all `x ∈ closure S`.
-/

section Corollary1325

open Set
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Chapter01 Corollary 1.3.25: if `S` is a nonempty convex subset of a complete real
inner-product space and `xbar ∉ S`, then there exists a nonzero vector `p` such that
`⟪p, x - xbar⟫ ≤ 0` for every `x ∈ closure S`. The source states this on `ℝ^n`; the abstract
Hilbert-space statement is the canonical owner level because the proof uses Hahn-Banach
separation on `closure S` together with the Fréchet-Riesz identification. -/
theorem existsNonzeroSupportingVectorOnClosureOfNotMem
    (S : Set E) (hS_nonempty : S.Nonempty) (hS_convex : Convex ℝ S)
    (xbar : E) (hxbar : xbar ∉ S) :
    ∃ p : E, p ≠ 0 ∧ ∀ x ∈ closure S, ⟪p, x - xbar⟫ ≤ (0 : ℝ) := by
  by_cases hxbar_closure : xbar ∈ closure S
  · have hxbar_frontier : xbar ∈ frontier S := by
      rw [frontier, mem_sdiff]
      exact ⟨hxbar_closure, fun hx ↦ hxbar (interior_subset hx)⟩
    obtain ⟨p, hp, hp_supports⟩ :=
      existsNonzeroSupportingVectorOnClosure S hS_convex xbar hxbar_frontier
    refine ⟨p, hp, ?_⟩
    intro x hx
    have hx_halfspace : x ∈ closedLowerHalfSpace p ⟪p, xbar⟫ := hp_supports hx
    simpa [closedLowerHalfSpace, inner_sub_right, sub_nonpos] using hx_halfspace
  · obtain ⟨f, α, hclosure_lt, hαxbar⟩ :=
      geometric_hahn_banach_closed_point hS_convex.closure isClosed_closure hxbar_closure
    let p : E := (InnerProductSpace.toDual ℝ E).symm f
    have hp : p ≠ 0 := by
      intro hp
      have hf : f = 0 := by
        simpa [p] using congrArg (InnerProductSpace.toDual ℝ E) hp
      rcases hS_nonempty with ⟨x, hx⟩
      have hx' : (0 : ℝ) < α := by
        simpa [hf] using hclosure_lt x (subset_closure hx)
      have hxbar' : α < 0 := by
        simpa [hf] using hαxbar
      linarith
    refine ⟨p, hp, ?_⟩
    intro x hx
    have hx_lt : ⟪p, x⟫ < ⟪p, xbar⟫ := by
      have hx_lt' : f x < f xbar := (hclosure_lt x hx).trans hαxbar
      simpa [p, InnerProductSpace.toDual_symm_apply] using hx_lt'
    simpa [inner_sub_right, sub_nonpos] using hx_lt.le

end Corollary1325
