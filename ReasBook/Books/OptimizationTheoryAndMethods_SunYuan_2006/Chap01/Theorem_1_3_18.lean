/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.PiL2

-- Semantic recall hits verified for this item: `ConvexOn.convex_le`.

section Theorem1318

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

/-
Chapter01 Theorem 1.3.18: if `f : Point → ℝ` is convex on `S ⊆ ℝ^n`, then each lower level set
`{x ∈ S | f x ≤ α}` is convex. This is the direct `Point = ℝ^n` specialization of mathlib's
canonical owner theorem `ConvexOn.convex_le`, so this file records the item as a recall block
instead of keeping a parallel local wrapper for the lower level set.
-/
#check fun {S : Set Point} {f : Point → ℝ} (hf : ConvexOn ℝ S f) (α : ℝ) ↦
  (hf.convex_le α : Convex ℝ {x ∈ S | f x ≤ α})

end Theorem1318
