/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Proposition_12_6

-- Declarations for this item will be appended below by the statement pipeline.

namespace ERealFunction

/-- Example 12.7: for `f(ξ) = ξ` and `g = -f` on `ℝ`, the infimal convolution `f □ g` is
identically `-∞`, so the conclusion of Proposition 12.6(i) can fail without the common-minorant
hypothesis. -/
-- Proof sketch: for fixed `x`, the defining summand is
-- `y + (-(x - y)) = 2y - x`. Taking `y = -n` sends this quantity to `-∞`,
-- so the infimum over all `y` is `⊥` for every `x`.
theorem id_infimalConvolution_neg_id_eq_bot :
    infimalConvolution id.toEReal.asEReal (-id).toEReal.asEReal = (⊥ : ℝ → EReal) := by
  ext x
  change (⨅ y : ℝ, (id.toEReal y : EReal) + (((-id).toEReal (x - y) : EReal))) = (⊥ : EReal)
  refine (EReal.eq_bot_iff_forall_lt _).2 ?_
  intro r
  let y : ℝ := (x + r - 1) / 2
  refine lt_of_le_of_lt (iInf_le _ y) ?_
  dsimp [y]
  exact_mod_cast (show ((x + r - 1) / 2) - (x - ((x + r - 1) / 2)) < r by linarith)

end ERealFunction
