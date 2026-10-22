/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_31
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_32

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open EReal

namespace ERealFunction

variable {X : Type u}

/-- A point belongs to the effective domain of the textbook pointwise sum exactly when it belongs
to the effective domains of both summands. -/
lemma mem_effectiveDom_pointwiseSum_iff (f g : X → EReal) (x : X) :
    x ∈ effectiveDom (pointwiseSum f g) ↔ x ∈ effectiveDom f ∧ x ∈ effectiveDom g := by
  rw [mem_effectiveDom_iff_exists_real, pointwiseSum_apply, exists_real_eq_sumWithTopBotAsTop_iff,
    mem_effectiveDom_iff_exists_real, mem_effectiveDom_iff_exists_real]

/-- Text 1.0.33: the effective domain of the textbook pointwise sum of two extended-real-valued
functions is the intersection of their effective domains. -/
theorem effectiveDom_pointwiseSum_eq_inter (f g : X → EReal) :
    effectiveDom (pointwiseSum f g) = effectiveDom f ∩ effectiveDom g := by
  ext x
  rw [Set.mem_inter_iff, mem_effectiveDom_pointwiseSum_iff]

end ERealFunction
