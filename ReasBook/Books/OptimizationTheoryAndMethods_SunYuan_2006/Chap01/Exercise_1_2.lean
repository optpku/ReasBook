/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_2_3

variable {n : ℕ}

/-
Chapter01 Exercise 1.2

Domain sampling for this item:
- primitive data: the `lpNorm` owner and the standard vector-norm notation
  `‖·‖₁`, `‖·‖₂`, `‖·‖∞` live in `Definition_1_2_1.lean`;
- chapter owner abstraction: the six canonical vector-norm comparison inequalities already live in
  `Definition_1_2_3.lean` as
  `vectorTwoNorm_le_vectorOneNorm`,
  `vectorOneNorm_le_sqrt_mul_vectorTwoNorm`,
  `vectorInfNorm_le_vectorTwoNorm`,
  `vectorTwoNorm_le_sqrt_mul_vectorInfNorm`,
  `vectorInfNorm_le_vectorOneNorm`, and
  `vectorOneNorm_le_nat_mul_vectorInfNorm`.

This exercise therefore stays recall-only: it adds no new source-facing owner beyond those
existing chapter theorems.
-/

#check vectorTwoNorm_le_vectorOneNorm
#check vectorOneNorm_le_sqrt_mul_vectorTwoNorm
#check vectorInfNorm_le_vectorTwoNorm
#check vectorTwoNorm_le_sqrt_mul_vectorInfNorm
#check vectorInfNorm_le_vectorOneNorm
#check vectorOneNorm_le_nat_mul_vectorInfNorm
