/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Text_8_0_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

section ClosedLevelSet

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

-- Proof sketch: the inclusion `C ⊆ lowerLevelSet (m[C]) 1` comes from the defining infimum of the
-- gauge. For the reverse inclusion, separate a point `x ∉ C` from the closed convex set `C` by a
-- continuous linear functional and use the resulting strict supporting inequality to force
-- `m[C] x > 1`.
/-- Corollary 14.13 (1): clause (i). If `C` is closed, convex, and contains `0`, then `C` is
exactly the lower level set `{x | m[C] x ≤ 1}` of its Minkowski gauge. -/
theorem lowerLevelSet_minkowskiGauge_one_eq_of_isClosed_of_convex_of_zero_mem
    (C : Set H) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (h0C : (0 : H) ∈ C) :
    lowerLevelSet (m[C]) 1 = C := sorry

end ClosedLevelSet

section GaugeBridge

variable {H : Type u} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H]
  [IsTopologicalAddGroup H] [ContinuousSMul ℝ H]

-- Proof sketch: when `0 ∈ interior C`, the set of positive scalars used to define `m[C] x` is
-- nonempty for every `x`, so the source-facing `EReal`-valued gauge is exactly mathlib's canonical
-- real-valued `gauge C`, viewed in `EReal`.
/-- Bridge for Corollary 14.13 (2): if `0 ∈ interior C`, then the source-facing Minkowski gauge
`m[C]` agrees pointwise with mathlib's canonical owner `gauge C`, viewed in `EReal`. -/
theorem minkowskiGauge_eq_coe_gauge_of_zero_mem_interior
    (C : Set H) (h0C : (0 : H) ∈ interior C) :
    m[C] = fun x ↦ (gauge C x : EReal) := sorry

-- Proof sketch: rewrite the source-facing gauge `m[C]` to the canonical owner `gauge C` through
-- `minkowskiGauge_eq_coe_gauge_of_zero_mem_interior`, then apply mathlib's
-- `gauge_lt_one_eq_interior`.
/-- Corollary 14.13 (2): clause (ii). If `C` is convex and `0` lies in its interior, then the
strict lower level set `{x | m[C] x < 1}` of the Minkowski gauge is exactly `interior C`. -/
theorem strictLowerLevelSet_minkowskiGauge_one_eq_interior_of_convex_of_zero_mem_interior
    (C : Set H) (hC_convex : Convex ℝ C) (h0C : (0 : H) ∈ interior C) :
    strictLowerLevelSet (m[C]) 1 = interior C := by
  calc
    strictLowerLevelSet (m[C]) 1 = {x | gauge C x < 1} := by
      ext x
      rw [mem_strictLowerLevelSet_iff, minkowskiGauge_eq_coe_gauge_of_zero_mem_interior C h0C,
        EReal.coe_lt_coe_iff]
      change gauge C x < 1 ↔ gauge C x < 1
      rfl
    _ = interior C :=
      gauge_lt_one_eq_interior hC_convex (mem_interior_iff_mem_nhds.mp h0C)

end GaugeBridge

end ERealFunction
