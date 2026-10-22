/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_22
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap07.Definition_7_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Set
open Metric

universe u

namespace ERealFunction

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: expand `conjugate` for the complement indicator of `C`. On `C` the indicator
-- term vanishes, and outside `C` it contributes `⊤`, so only points of `C` survive in the
-- defining supremum; what remains is exactly the support function `σ[C]`.
/-- Example 13.3 (1): clause (i). The conjugate of the indicator `ι[C]` is the support
function `σ[C]`. -/
theorem conjugate_indicator_eq_supportFunction
    (C : Set H) :
    ((ι[C]).asEReal)∗ = σ[C] := sorry

-- Proof sketch: combine clause (i) with the cone-specific identity that the support function of a
-- nonempty cone is the indicator of its polar cone.
/-- Example 13.3 (2): clause (ii). If `K` is a nonempty cone, then the conjugate of `ι[K]` is the
indicator `ι[Kᵒ⊖]`. -/
theorem conjugate_indicator_eq_indicator_polarCone_of_nonempty_isCone
    (K : Set H) (hK_nonempty : K.Nonempty) (hK_cone : IsCone K) :
    ((ι[K]).asEReal)∗ = (ι[Kᵒ⊖]).asEReal := sorry

-- Proof sketch: apply clause (ii) to the cone underlying the submodule `V`, then identify the
-- polar cone of a linear subspace with its orthogonal complement.
/-- Example 13.3 (3): clause (iii). If `V` is a linear subspace, then the conjugate of `ι[V]` is
the indicator `ι[Vᗮ]`. -/
theorem conjugate_indicator_submodule_eq_indicator_orthogonal
    (V : Submodule ℝ H) :
    ((ι[(V : Set H)]).asEReal)∗ = (ι[(Vᗮ : Set H)]).asEReal := sorry

-- Proof sketch: use clause (i) for the closed unit ball and identify its support function with
-- the norm via Cauchy--Schwarz and the extremal choice of the normalized vector.
/-- Example 13.3 (4): clause (iv). The conjugate of the indicator `ι[B(0;1)]` is the norm. -/
theorem conjugate_indicator_closedUnitBall_eq_norm :
    ((ι[closedBall (0 : H) 1]).asEReal)∗ =
      fun u : H ↦ (‖u‖ : EReal) := sorry

-- Proof sketch: compute the conjugate of the norm by splitting on whether `‖u‖ ≤ 1`; the
-- Cauchy--Schwarz inequality gives the finite value `0` on the closed unit ball, while testing on
-- rays `x = λu` makes the defining supremum diverge to `⊤` when `‖u‖ > 1`.
/-- Example 13.3 (5): clause (v). The conjugate of the norm is the indicator `ι[B(0;1)]`. -/
theorem conjugate_norm_eq_indicator_closedUnitBall :
    (fun x : H ↦ (‖x‖ : EReal))∗ =
      (ι[closedBall (0 : H) 1]).asEReal := sorry

end Conjugation

end ERealFunction
