/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_9
import Mathlib.Order.ConditionallyCompleteLattice.Finset

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

-- Proof sketch: unfold `support_function` and identify the `sSup` of the
-- finite image set `(fun b ↦ (y b : EReal)) '' (s : Set E)` with the nonempty finset supremum
-- `s.sup' hs (fun b ↦ (y b : EReal))` via `Finset.sup'_eq_csSup_image`.
/-- Definition 2.10: if `C` is represented by a nonempty finite set `s`, then the support
function of `C` at `y` is the maximum of the finitely many values `y b` for `b ∈ s`. -/
theorem support_function_finset_eq_sup' (s : Finset E) (hs : s.Nonempty) (y : Module.Dual ℝ E) :
    support_function (s : Set E) y = s.sup' hs (fun b ↦ (y b : EReal)) := by
  rw [support_function_apply, ← Finset.sup'_eq_csSup_image s hs]

end
