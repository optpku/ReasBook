/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_8

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

universe u v

namespace SetValuedOperator

variable {X : Type u} {Y : Type v} [AddCommGroup Y] [Module ℝ Y]

/-- Text 1.0.16: for set-valued operators `A B : X → Set Y` and a real scalar `c`
(`λ` in the text), the linear combination `A + λ B` is the pointwise operator satisfying
`(A + c • B) x = A x + c • B x`. -/
@[simp] theorem add_smul_apply (A B : SetValuedOperator X Y) (c : ℝ) (x : X) :
    (A + c • B) x = A x + c • B x :=
  rfl

end SetValuedOperator
