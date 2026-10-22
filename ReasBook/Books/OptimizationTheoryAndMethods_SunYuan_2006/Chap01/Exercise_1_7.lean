/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_2_6

-- Domain sampling pass: the ambient owner abstractions here are the chapter-local matrix-norm
-- classes `IsMatrixNorm` and `MatrixNormSubmultiplicative` from `Definition_1_2_2`, and the
-- source-facing perturbation theorem owner in `Theorem_1_2_6.lean` is
-- `vonNeumannLemma_isUnit_and_inv_norm_le_of_norm_sub_le`.

/-
Chapter01 Exercise 1.7

Recall-only entry: this exercise asks for Theorem 1.2.6, whose owner declaration is
`vonNeumannLemma_isUnit_and_inv_norm_le_of_norm_sub_le`.
-/
#check vonNeumannLemma_isUnit_and_inv_norm_le_of_norm_sub_le
