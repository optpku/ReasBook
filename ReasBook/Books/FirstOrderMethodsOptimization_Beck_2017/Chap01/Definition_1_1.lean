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

/- Definition 1.1 is recall-only: Lean does not introduce a separate public `RealVectorSpace`
structure. The textbook notion is formalized by the owner pair `[AddCommGroup E] [Module ℝ E]`. -/

/- The additive data of a real vector space is the canonical typeclass `AddCommGroup E`. -/
#check AddCommGroup E

/- Scalar multiplication by real numbers, together with its compatibility with the additive
structure, is the canonical owner typeclass `Module ℝ E`. -/
#check Module ℝ E

end
