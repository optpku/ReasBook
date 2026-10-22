/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_34

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix WithLp
open scoped Matrix

section

variable {m n : ℕ}

/-- Proposition 1.1 (`source-facing`; `core/canonical` owner:
`ContinuousLinearMap.le_opNorm`; `bridge/view`: `Matrix.toLpLin`): for every real vector `x`, the
induced `(a,b)`-norm of a real matrix `A` bounds the `b`-norm of `A x` by
`‖A x‖_b ≤ ‖A‖_{a,b} ‖x‖_a`. In the project notation from Definition 1.34, this is the
source-facing `WithLp` coordinate form of the canonical operator-norm estimate defining
`‖A‖[a,b]`. -/
theorem norm_mulVec_le_opNorm_toLpLin_mul_norm
    (a b : ENNReal) [Fact (1 ≤ a)] [Fact (1 ≤ b)]
    (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) :
    ‖toLp b (A *ᵥ x)‖ ≤ ‖A‖[a,b] * ‖toLp a x‖ := by
  simpa [toLpLin_toLp] using (A.toLpLin a b).toContinuousLinearMap.le_opNorm (toLp a x)

end
