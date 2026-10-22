/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Proposition_11_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u} [TopologicalSpace H] [AddCommGroup H] [Module ℝ H]
  [IsTopologicalAddGroup H] [ContinuousSMul ℝ H]

/-- Proposition 11.5: if `x` minimizes a convex extended-real-valued function over a set `C`,
lies in the effective domain, and belongs to `interior C`, then `x` is a global minimizer. -/
-- Proof sketch: `x ∈ interior C` promotes the constrained argmin witness to a neighborhood argmin
-- witness, so Proposition 11.4 applies directly.
theorem mem_argmin_of_mem_argminOn_of_mem_interior_of_convexOn_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn f (effectiveDomain f))
    {C : Set H} {x : H} (hx : x ∈ effectiveDomain f)
    (hargmin : x ∈ Argmin[C] f.asEReal) (hxint : x ∈ interior C) :
    x ∈ Argmin f.asEReal :=
  mem_argmin_of_isLocalMin_of_convexOn_effectiveDomain f hconv hx <|
    (mem_argminOn_iff.mp hargmin).2.isLocalMin (mem_interior_iff_mem_nhds.mp hxint)

end ERealFunction
