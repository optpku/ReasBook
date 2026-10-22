/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 7.16: the textbook diagonal-matrix construction `dg(v)` is the canonical mathlib
owner `Matrix.diagonal`, which sends a vector `v` to the square matrix whose diagonal entries are
given by `v` and whose off-diagonal entries are zero. -/
recall Matrix.diagonal

/- The textbook entrywise formula for `dg(v)` is the canonical pointwise statement
`Matrix.diagonal_apply`. -/
recall Matrix.diagonal_apply
