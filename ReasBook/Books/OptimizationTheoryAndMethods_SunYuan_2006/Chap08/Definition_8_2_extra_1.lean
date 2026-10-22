/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_4_3

section Chapter08Definition82Extra1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Chapter08 Definition 8.2-extra-1 is a bridge/view: the source uses the set of all descent
directions at a point, while the project already owns the underlying notion through
`IsDescentDirectionAt`. This file keeps the source-facing set-valued presentation and derives it
from that owner instead of duplicating the gradient-pairing predicate. -/

/-- Chapter08 Definition 8.2-extra-1: `descentDirections f xStar` is the set of descent
directions of `f` at `xStar`. -/
def descentDirections (f : E → ℝ) (xStar : E) : Set E :=
  {d | IsDescentDirectionAt f xStar d}

/-- Membership in `descentDirections f xStar` is exactly the strict negativity of the gradient
pairing `inner ℝ d (gradient f xStar)`. -/
theorem mem_descentDirections_iff (f : E → ℝ) (xStar d : E) :
    d ∈ descentDirections f xStar ↔ inner ℝ d (gradient f xStar) < 0 := by
  simp [descentDirections, isDescentDirectionAt_iff]

end Chapter08Definition82Extra1
