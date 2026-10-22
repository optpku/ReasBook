/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped translate
open ERealFunction

universe u

namespace ERealFunction

variable {H : Type u} [AddCommGroup H]

-- Proof sketch: unfold the defining infimum for `ι[{y}] □ f`. The singleton indicator is `0`
-- exactly at `y` and `⊤` elsewhere, so the only finite contribution comes from the decomposition
-- using `y`, yielding the translate of the canonical `EReal` view `f.asEReal`.
/-- Example 12.4: the infimal convolution of the singleton indicator at `y` with `f` is the
translate of `f` by `y`. -/
theorem indicator_singleton_infimalConvolution_eq_translate
    (f : H → Set.Ioi (⊥ : EReal)) (y : H) :
    infimalConvolution (ι[{y}]).asEReal f.asEReal = τ y f.asEReal := sorry

end ERealFunction
