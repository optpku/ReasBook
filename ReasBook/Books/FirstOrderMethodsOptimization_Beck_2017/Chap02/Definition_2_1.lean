/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u}

/-- Definition 2.1: The effective domain of an extended real-valued function `f : E → EReal` is
the set of points where `f` takes a finite value, equivalently where `f x < ∞`. -/
def effective_domain (f : E → EReal) : Set E := {x | f x < ⊤}

-- Proof sketch: Unfold `effective_domain`; membership in the defining set is exactly the
-- inequality `f x < ⊤`.
/-- A point belongs to the effective domain exactly when the function value is strictly less than
`∞`. -/
@[simp] lemma mem_effective_domain {f : E → EReal} {x : E} :
    x ∈ effective_domain f ↔ f x < ⊤ :=
  Iff.rfl

end
