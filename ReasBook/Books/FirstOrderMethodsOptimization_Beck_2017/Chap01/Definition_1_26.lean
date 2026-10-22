/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {n : ℕ}

/- Definition 1.26: for a vector `x` in `ℝ^n`, modeled as `Fin n → ℝ`, the vector `|x|` is the
coordinatewise absolute-value vector, given canonically by `Pi.abs_def`. -/
#check (Pi.abs_def : ∀ x : Fin n → ℝ, |x| = fun i ↦ |x i|)

end
