/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Example_12_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_20

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H]

/-- Example 12.21: the `γ`-Moreau envelope of the indicator `ι[C]` is the scaled squared
extended-distance function `x ↦ d(x, C)^2 / (2γ)`, with value `⊤` when `C = ∅`. -/
-- Proof sketch: unfold `{}^[γ] ι[C]`; on points of `C` the indicator contributes `0`, outside
-- `C` it contributes `⊤`, so the infimum reduces to minimizing `‖x - y‖² / (2γ)` over `y ∈ C`.
-- The resulting `EReal`-valued function is the square of the canonical extended distance
-- `Metric.infEDist · C`, scaled by `1 / (2γ)`.
theorem indicator_moreauEnvelope_eq_scaled_sq_infEDist (C : Set H) (γ : Set.Ioi (0 : ℝ)) :
    {}^[γ] ι[C] =
      fun x : H ↦ (Metric.infEDist x C : EReal) ^ 2 / (2 * (γ : ℝ) : EReal) := sorry

end ERealFunction
