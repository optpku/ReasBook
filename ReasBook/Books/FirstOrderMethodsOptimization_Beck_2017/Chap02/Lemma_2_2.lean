/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

/- Lemma 2.2: the Minkowski sum is the canonical pointwise addition of sets in scope
`Pointwise`; the owner declaration `Set.image2_add` identifies it with the binary image
`Set.image2 (· + ·)`. -/
recall Set.image2_add

/- Membership in the Minkowski sum is the canonical owner theorem `Set.mem_add`. -/
recall Set.mem_add
