/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_3_7

-- Domain-style sampling for this item:
-- `epigraph` in `Definition_1_3_7` is the source-facing owner/view.
-- `ConvexOn.convex_epigraph`, `convexOn_iff_convex_epigraph`, and
-- `convexOn_of_convex_epigraph` in mathlib are the core/canonical API.

section Theorem138

variable {𝕜 E β : Type*}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E]
variable [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β]
variable [Module 𝕜 β] [PosSMulMono 𝕜 β]

/-- Chapter01 Theorem 1.3.8: a function is convex on `s` if and only if its
epigraph `epigraph s f` is convex. This is the source-facing `epigraph` bridge
for mathlib's canonical `convexOn_iff_convex_epigraph`; the book's ambient
specialization to `S ⊆ ℝ^n` and `f : S → ℝ` is a special case, and the extra
source hypothesis `S.Nonempty` does not affect this equivalence. -/
theorem convexOn_iff_convex_epigraph_over (s : Set E) (f : E → β) :
    ConvexOn 𝕜 s f ↔ Convex 𝕜 (epigraph s f) := by
  simpa [epigraph] using
    (convexOn_iff_convex_epigraph :
      ConvexOn 𝕜 s f ↔ Convex 𝕜 {p : E × β | p.1 ∈ s ∧ f p.1 ≤ p.2})

end Theorem138
