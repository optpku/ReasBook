/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Data.Set.Basic

-- Semantic recall hits verified for this item:
-- `ConvexOn.convex_epigraph`, `convexOn_iff_convex_epigraph`,
-- `ConcaveOn.convex_hypograph`, `concaveOn_iff_convex_hypograph`.

universe u v

section Definition137

variable {E : Type u} {α : Type v} [LE α]

/-- Chapter01 Definition 1.3.7 (1): the epigraph of `f` over `s`.

The source states this for a nonempty set `S ⊆ ℝ^n`, but the defining set itself does not depend
on nonemptiness. -/
def epigraph (s : Set E) (f : E → α) : Set (E × α) :=
  {p | p.1 ∈ s ∧ f p.1 ≤ p.2}

/-- Chapter01 Definition 1.3.7 (2): the hypograph of `f` over `s`.

Again, the source's ambient nonemptiness hypothesis does not affect the defining set. -/
def hypograph (s : Set E) (f : E → α) : Set (E × α) :=
  {p | p.1 ∈ s ∧ p.2 ≤ f p.1}

end Definition137
