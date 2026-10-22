/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

/- Proposition 1.12 is recall-only at the chapter's source-facing bidual layer.
By Definition 1.43, the bidual is `E** = Module.Dual ℝ (Module.Dual ℝ E)`, and in finite
dimension the owner equivalence identifying `E` with that bidual is `Module.evalEquiv ℝ E`. -/
#check (Module.evalEquiv ℝ E)

/- The forward map of `Module.evalEquiv ℝ E` is the canonical bidual evaluation map
`Module.Dual.eval ℝ E`. -/
recall Module.Dual.eval_apply

end
