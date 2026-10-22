/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_2_6

/-
Chapter01 Exercise 1.4

Domain sampling for this item:
- primitive data: a matrix norm `N : Matrix (Fin n) (Fin n) ℝ → ℝ`, its matrix-norm hypothesis
  `IsMatrixNorm N`, its submultiplicativity hypothesis `MatrixNormSubmultiplicative N`, and the
  perturbation data `A`, `B`, `α`, `β`;
- chapter owner abstractions: `IsMatrixNorm` and `MatrixNormSubmultiplicative` already live in
  `Definition_1_2_2.lean`;
- derived API already available upstream:
  `vonNeumannLemma_isUnit_and_inv_norm_le_of_norm_sub_le`,
  `vonNeumannLemma_isUnit_of_norm_sub_le`,
  `vonNeumannLemma_inv_norm_le_of_norm_sub_le`
  from `Theorem_1_2_6.lean`.

This exercise is therefore recall-only: the source-facing inverse-norm estimate `(1.2.45)` is
already stated canonically by `vonNeumannLemma_inv_norm_le_of_norm_sub_le`, so this file keeps no
parallel local matrix-norm owners and no renamed wrapper theorem.
-/

#check vonNeumannLemma_inv_norm_le_of_norm_sub_le
