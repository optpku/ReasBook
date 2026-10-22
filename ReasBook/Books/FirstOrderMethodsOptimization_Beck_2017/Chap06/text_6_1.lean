/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap06.Example_6_10

-- Declarations for this item will be appended below by the statement pipeline.

/- Text 6.1 is `bridge/view`: the source-facing scalar penalties are Chapter 2's canonical
`l0Indicator` and Example 6.10's `hardThresholdPenalty`, while the chapter owner for proximal
mappings is `prox[...]` from Definition 6.1. The owner-level constant-shift invariance theorem is
already `prox_add_const`, and Example 6.10 now owns the scalar bridge used in the text. -/

/- text 6.1: the weighted scalar `ℓ₀` penalty `t ↦ λ l₀(t)` and the shifted penalty `J` from
Example 6.10 have the same proximal mapping. This bridge is already owned by the source-facing
penalty file. -/
recall prox_mul_l0Indicator_eq_hardThresholdPenalty
