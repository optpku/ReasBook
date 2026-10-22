/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_31

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {X : Type u} [TopologicalSpace X]

/-- Text 1.0.55: the points where an `EReal`-valued function takes a real value and is continuous
are exactly the points in its effective domain at which it is continuous. -/
theorem mem_effectiveDom_inter_continuousAt_iff_exists_real (f : X → EReal) (x : X) :
    x ∈ effectiveDom f ∩ {y | ContinuousAt f y} ↔
      (∃ r : ℝ, f x = (r : EReal)) ∧ ContinuousAt f x := by
  rw [Set.mem_inter_iff, Set.mem_setOf_eq, mem_effectiveDom_iff_exists_real]

end ERealFunction
