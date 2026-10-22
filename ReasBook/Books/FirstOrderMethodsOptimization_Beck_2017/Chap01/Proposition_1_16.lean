/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_34

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Matrix

variable {m n : ℕ}
variable (a b : ENNReal) [Fact (1 ≤ a)] [Fact (1 ≤ b)]
variable (A : Matrix (Fin m) (Fin n) ℝ)

/- Proposition 1.16 is recall-only: in the chapter owner setup from Definition 1.34, the induced
`(a,b)`-norm of a real matrix is exactly the canonical operator norm `‖A‖[a,b]`. -/
#check (‖A‖[a,b] : ℝ)
