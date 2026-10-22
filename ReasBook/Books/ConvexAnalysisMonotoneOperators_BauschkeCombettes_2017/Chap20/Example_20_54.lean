/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Example_17_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Definition_20_51

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContinuousLinearMap ERealFunction InnerProduct InnerProductSpace SetValuedOperator

universe u

namespace ContinuousLinearMap

noncomputable section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

variable [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: Example 20.54 identifies the Fitzpatrick function of the singleton-valued
  operator induced by a bounded linear map.
- `core/canonical`: the owner abstractions are `F[_]` for Fitzpatrick functions and `q[_]` for
  quadratic potentials.
- `bridge/view`: `A.toSetValuedOperator` is the thin continuous-linear-map bridge to the canonical
  function-level singleton-valued operator owner. -/

-- Proof sketch: expand the Fitzpatrick supremum for the singleton-valued operator induced by `A`.
-- At a graph point `(y, A y)`, the supremand becomes
-- `⟪y, u⟫_ℝ + ⟪x, A y⟫_ℝ - ⟪y, A y⟫_ℝ = 2 * (⟪y, (u + A† x) / 2⟫_ℝ - q[A] y)`.
-- The remaining supremum is exactly twice the conjugate of `q_A` at
-- `(1 / 2) • u + (1 / 2) • A† x`.
/-- Example 20.54: for a bounded linear operator `A`, the Fitzpatrick function of the
singleton-valued operator induced by `A` is `2 q_A^* ((u + A† x) / 2)`. -/
theorem fitzpatrickFunction_eq_two_mul_conjugate_quadraticPotential
    (A : H →L[ℝ] H) (x u : H) :
    F[A.toSetValuedOperator] (x, u) =
      ((2 : ℝ) : EReal) * ((q[A]).toEReal.asEReal∗)
        (((1 / 2 : ℝ) • u) + ((1 / 2 : ℝ) • (A†) x)) := sorry

end

end ContinuousLinearMap
