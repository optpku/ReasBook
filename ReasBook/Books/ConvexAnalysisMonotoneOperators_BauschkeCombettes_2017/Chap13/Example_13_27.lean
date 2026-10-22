/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Example_12_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Example_13_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Example_13_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Example_13_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_24

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace
open Metric

universe u

namespace ERealFunction

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: rewrite `Metric.infDist` through the source-facing distance decomposition from
-- Example 12.2, then apply Proposition 13.24(i), Example 13.3(i), and Example 13.3(v). The
-- resulting support function already depends only on the underlying set `C`.
/-- Example 13.27 (1): if `C` is a nonempty subset of `H`, then the Fenchel
conjugate of the distance function `d_C` is the support function `σ[C]` plus the indicator of the
closed unit ball `B(0;1)`. -/
theorem fenchelConjugate_infDist_eq_supportFunction_add_indicator_closedUnitBall
    (C : Set H) (hC_nonempty : C.Nonempty) :
    (fun x : H ↦ Metric.infDist x C).toEReal.asEReal∗ =
      σ[C] + (ι[closedBall (0 : H) 1]).asEReal := sorry

-- Proof sketch: specialize clause (1) to the underlying set of `V`, rewrite the support function
-- using Example 13.3(iii), and combine the two indicators into the indicator of the intersection
-- `Vᗮ ∩ B(0;1)`.
/-- Example 13.27 (2): if `V` is a linear subspace of `H`, then the Fenchel conjugate of
the distance function `d_V` is the indicator of `Vᗮ ∩ B(0;1)`. -/
theorem fenchelConjugate_infDist_submodule_eq_indicator_orthogonal_inter_closedUnitBall
    (V : Submodule ℝ H) :
    (fun x : H ↦ Metric.infDist x (↑V : Set H)).toEReal.asEReal∗ =
      (ι[((↑Vᗮ : Set H) ∩ closedBall (0 : H) 1)]).asEReal := sorry

-- Proof sketch: combine the distance-to-set infimal-convolution identity from Example 12.2 with
-- Proposition 13.24(i), Example 13.3(i), and the scalar/radial conjugacy formulas from
-- Example 13.2(i) and Example 13.8.
/-- Example 13.27 (3): if `C` is a nonempty subset of `H` and `p ∈ ]1,+∞[`, then
the Fenchel conjugate of `x ↦ d(x,C)^p / p` is `σ[C] + ‖·‖^(p*) / p*`, where
`p* = Real.conjExponent p = p / (p - 1)`. -/
theorem fenchelConjugate_infDistPowerDivided_eq_supportFunction_add_normPowerDivided
    (C : Set H) (hC_nonempty : C.Nonempty) (p : ℝ) (hp : 1 < p) :
    (fun x : H ↦ Metric.infDist x C ^ p / p).toEReal.asEReal∗ =
      σ[C] + (fun u : H ↦ ‖u‖ ^ p.conjExponent / p.conjExponent).toEReal.asEReal := sorry

-- Proof sketch: specialize clause (3) to the singleton `{0}` and use `Metric.infDist x {0} = ‖x‖`
-- to identify the distance-to-singleton formula with the norm-power formula.
/-- Example 13.27 (4): for `p ∈ ]1,+∞[`, the Fenchel conjugate of `x ↦ ‖x‖^p / p` is
`u ↦ ‖u‖^(p*) / p*`, where `p* = Real.conjExponent p = p / (p - 1)`. -/
theorem fenchelConjugate_normPowerDivided_eq_normPowerDivided_conjugateExponent
    (p : ℝ) (hp : 1 < p) :
    (fun x : H ↦ ‖x‖ ^ p / p).toEReal.asEReal∗ =
      (fun u : H ↦ ‖u‖ ^ p.conjExponent / p.conjExponent).toEReal.asEReal := sorry

end Conjugation

end ERealFunction
