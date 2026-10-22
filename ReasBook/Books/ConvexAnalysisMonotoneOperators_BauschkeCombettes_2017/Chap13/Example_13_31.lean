/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap07.Exercise_7_9
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Example_13_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_30

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ENNReal InnerProductSpace

namespace ERealFunction

noncomputable section

-- Proof sketch: identify `ℝ^N` with the finite Hilbert direct sum of `N` copies of `ℝ`, apply
-- Example 13.2 coordinatewise to the scalar summand `t ↦ |t|^p / p`, and then use Proposition
-- 13.30 to pass the Fenchel conjugate through the finite direct sum. The coordinate `ℓ^p` norm is
-- the Chapter 7 owner `EuclideanSpace.lpNorm`, written `‖x‖_[p]`, so no separate local wrapper is
-- needed.
/-- Example 13.31: on `ℝ^N`, for `p ∈ ]1,+∞[`, the Fenchel conjugate of `x ↦ ‖x‖_p^p / p` is
`u ↦ ‖u‖_{p*}^{p*} / p*`, where `p* = Real.conjExponent p = p / (p - 1)`. -/
theorem fenchelConjugate_lpNormPowerDivided_eq_lpNormPowerDivided_conjExponent
    (N : ℕ) (p : ℝ) (hp : 1 < p) :
    (fun x : EuclideanSpace ℝ (Fin N) ↦
      ((‖x‖_[ENNReal.ofReal p] ^ p / p : ℝ) : EReal))∗ =
      fun u : EuclideanSpace ℝ (Fin N) ↦
        ((‖u‖_[ENNReal.ofReal (Real.conjExponent p)] ^ Real.conjExponent p /
          Real.conjExponent p : ℝ) : EReal) := sorry

end

end ERealFunction
