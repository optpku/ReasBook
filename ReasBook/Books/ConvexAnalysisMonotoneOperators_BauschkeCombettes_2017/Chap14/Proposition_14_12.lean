/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap07.Definition_7_14
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Text_8_0_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Example_13_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise Set

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: the canonical owner here is the support function `σ`. For a convex set containing
-- `0`, the gauge `m[C]` agrees with the support function of the polar set `σ[Cᵒ⊙]`; this is the
-- bridge from the source-facing gauge to the Chapter 7 owner abstraction. Proposition 14.12 then
-- identifies the conjugate of that source-facing gauge with the indicator of the same polar set.
/-- Bridge for Proposition 14.12: if `C` is convex and contains `0`, then its Minkowski gauge is
the support function of the polar set `Cᵒ⊙`. -/
theorem minkowskiGauge_eq_supportFunction_polarSet
    (C : Set H) (hC_convex : Convex ℝ C) (h0C : (0 : H) ∈ C) :
    m[C] = σ[Cᵒ⊙] := sorry

-- Proof sketch: first pass from the source-facing gauge `m[C]` to the canonical support-function
-- owner via `minkowskiGauge_eq_supportFunction_polarSet`. Then apply the polar characterization to
-- show that the Fenchel conjugate is `0` on `Cᵒ⊙` and `⊤` off `Cᵒ⊙`.
/-- Proposition 14.12: if `C` is convex and contains `0`, then the Fenchel conjugate of the
Minkowski gauge `m[C]` is the indicator of the polar set `Cᵒ⊙`. -/
theorem conjugate_minkowskiGauge_eq_indicator_polarSet
    (C : Set H) (hC_convex : Convex ℝ C) (h0C : (0 : H) ∈ C) :
    (m[C])∗ = (ι[Cᵒ⊙]).asEReal := sorry

end ERealFunction
