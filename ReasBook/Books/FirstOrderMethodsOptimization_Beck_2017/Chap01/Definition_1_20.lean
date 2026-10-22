/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 1.20: on `ℝ^n`, modeled as `Fin n → ℝ`, the canonical norm is the `l_infty`-norm,
given by the supremum, equivalently the maximum, of the coordinate absolute values; this is the
specialization of the standard finite-product sup-norm formula `Pi.norm_def`. -/
section

variable {n : ℕ}

#check (Pi.norm_def : ∀ x : Fin n → ℝ, ‖x‖ = ↑(Finset.univ.sup fun i ↦ ‖x i‖₊))

end
