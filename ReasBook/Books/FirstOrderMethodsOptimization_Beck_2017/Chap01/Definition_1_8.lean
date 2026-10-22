/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 1.8: an inner product on a real vector space is the canonical source-facing mathlib
data `InnerProductSpace.Core`; specialized to `ℝ`, this encodes the textbook symmetry, linearity,
and positive-definiteness axioms for the pairing. -/
recall InnerProductSpace.Core

/- The canonical bridge from this source-facing core data to the ambient owner abstraction
`InnerProductSpace` is `InnerProductSpace.ofCore`. -/
recall InnerProductSpace.ofCore
