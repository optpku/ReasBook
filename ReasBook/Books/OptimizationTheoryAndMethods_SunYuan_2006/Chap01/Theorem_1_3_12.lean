/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.InnerProductSpace.PiL2

-- Semantic recall hits verified for this item:
-- `ConvexOn.continuousOn`, `ConvexOn.subset`.

section Theorem1312

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

/- Chapter01 Theorem 1.3.12: if `S ⊆ D ⊆ ℝ^n`, `S` is open and convex, and `f` is convex on
`D`, then `f` is continuous on `S`. This is the canonical composite of mathlib's
`ConvexOn.subset` and `ConvexOn.continuousOn`, specialized here to `Point = ℝ^n`. -/

#check fun {D S : Set Point} {f : Point → ℝ}
    (hSD : S ⊆ D) (hS_open : IsOpen S) (hS_convex : Convex ℝ S) (hf : ConvexOn ℝ D f) ↦
      (hf.subset hSD hS_convex).continuousOn hS_open

end Theorem1312
