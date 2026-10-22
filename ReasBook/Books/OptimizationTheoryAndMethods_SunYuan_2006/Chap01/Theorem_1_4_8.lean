/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Convex.Extrema
import Mathlib.Analysis.InnerProductSpace.PiL2

section Chapter01Theorem148

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

-- Semantic recall hits verified for this item: `IsMinOn.of_isLocalMinOn_of_convexOn` is the
-- canonical owner for the convex case, while `StrictConvexOn.eq_of_isMinOn` is the canonical
-- uniqueness lemma for the strict-convex companion.

/- Chapter01 Theorem 1.4.8 (1): let `S ⊆ ℝⁿ` be a nonempty convex set, let `f : Point → ℝ`, and
let `xStar ∈ S` be a local minimizer of `f` on `S`. If `f` is convex on `S`, then `xStar` is a
global minimizer of `f` on `S`. This is the direct `Point = ℝ^n` specialization of the canonical
mathlib owner theorem `IsMinOn.of_isLocalMinOn_of_convexOn`; the source hypothesis `S.Nonempty`
is redundant once `xStar ∈ S`.
-/
#check fun {S : Set Point} {f : Point → ℝ} {xStar : Point} (hxStar : xStar ∈ S)
    (hmin : IsLocalMinOn f S xStar) (hf : ConvexOn ℝ S f) ↦
  IsMinOn.of_isLocalMinOn_of_convexOn hxStar hmin hf

/-- Chapter01 Theorem 1.4.8 (2): under the same source hypotheses, if `f` is strictly convex on
`S`, then `xStar` is the unique global minimizer on `S`, equivalently `f xStar < f x` for every
`x ∈ S` with `x ≠ xStar`. The source assumptions `S.Nonempty` and `Convex ℝ S` are absorbed by
`hxStar : xStar ∈ S` and `hf : StrictConvexOn ℝ S f`. -/
theorem lt_of_ne_of_mem_of_isLocalMinOn_of_strictConvexOn
    {S : Set Point} {f : Point → ℝ} {xStar x : Point}
    (hxStar : xStar ∈ S) (hf : StrictConvexOn ℝ S f) (hmin : IsLocalMinOn f S xStar)
    (hx : x ∈ S) (hxx : x ≠ xStar) :
    f xStar < f x := by
  have hminStar : IsMinOn f S xStar :=
    IsMinOn.of_isLocalMinOn_of_convexOn hxStar hmin hf.convexOn
  by_contra hlt
  have hle : f x ≤ f xStar := le_of_not_gt hlt
  have hminX : IsMinOn f S x := fun y hy ↦ le_trans hle (hminStar hy)
  exact hxx (hf.eq_of_isMinOn hminStar hminX hxStar hx).symm

end Chapter01Theorem148
