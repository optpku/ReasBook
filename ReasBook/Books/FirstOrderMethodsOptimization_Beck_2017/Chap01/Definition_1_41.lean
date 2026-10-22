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

/- Definition 1.41 is recall-only: the primitive notion is the canonical type of real linear maps
`E →ₗ[ℝ] ℝ`, and the dual space is organized by the owner abstraction `Module.Dual`. -/
#check (E →ₗ[ℝ] ℝ)

/- The dual space `E*` is the canonical owner declaration `Module.Dual`, specialized here to real
vector spaces. -/
recall Module.Dual

end
