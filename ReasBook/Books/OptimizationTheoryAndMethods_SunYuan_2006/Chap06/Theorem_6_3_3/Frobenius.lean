/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Definition_6_3_1

noncomputable section

section

variable {n : ℕ}

namespace ThirdOrderTensor

/-- The canonical nested `PiLp` Hilbert-space owner for flattening a third-order tensor into its
full coordinate array. This is the source-faithful Frobenius owner used by Theorem 6.3.3. -/
abbrev Flattened (n : ℕ) :=
  PiLp 2 fun _ : Fin n ↦ PiLp 2 fun _ : Fin n ↦ PiLp 2 fun _ : Fin n ↦ ℝ

/-- Flatten a third-order tensor into the canonical nested `PiLp` Hilbert-space owner carrying
the source Frobenius norm on all `n^3` coordinates. -/
def flatten (T : ThirdOrderTensor n) : Flattened n :=
  WithLp.toLp 2 fun i : Fin n ↦
    WithLp.toLp 2 fun j : Fin n ↦
      WithLp.toLp 2 fun k : Fin n ↦ T i j k

/-- The source Frobenius norm `‖T‖_F` of a third-order tensor is the norm of its fully flattened
coordinate vector. -/
def fullFrobeniusNorm (T : ThirdOrderTensor n) : ℝ :=
  ‖flatten T‖

/-- Unfolding `T.fullFrobeniusNorm` gives the norm of the fully flattened coordinate vector. -/
theorem fullFrobeniusNorm_eq_flatten_norm (T : ThirdOrderTensor n) :
    T.fullFrobeniusNorm = ‖flatten T‖ := rfl

end ThirdOrderTensor

end
