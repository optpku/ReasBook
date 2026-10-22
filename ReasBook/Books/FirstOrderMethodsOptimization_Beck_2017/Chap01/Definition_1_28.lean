/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {n : ℕ}

/- Definition 1.28: for vectors in `ℝ^n`, modeled as `Fin n → ℝ`, the Hadamard product is the
canonical pointwise multiplication on the function space `Fin n → ℝ`. -/
#check ((· * ·) : (Fin n → ℝ) → (Fin n → ℝ) → Fin n → ℝ)

/- The coordinates of the Hadamard product are given by the canonical `Pi.mul_apply` formula. -/
#check (Pi.mul_apply : ∀ a b : Fin n → ℝ, ∀ i : Fin n, (a * b) i = a i * b i)

end
