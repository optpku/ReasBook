/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]
variable {n : ℕ} (v : Fin n → E)

/- Definition 1.2: a finite family of vectors in a real vector space is linearly independent
exactly when it is the canonical mathlib predicate `LinearIndependent ℝ v`. -/
#check (LinearIndependent ℝ v)

/- For a finite family, the textbook vanishing-linear-combination criterion is the canonical
mathlib theorem `Fintype.linearIndependent_iff`. -/
recall Fintype.linearIndependent_iff

end
