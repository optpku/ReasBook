/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Proposition_12_0_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open Bornology

/- Theorem 12.0.4 is `source-facing`: the textbook object is the partial-sum sequence
`s_m = ∑_{n=1}^m 1 / n^2`. Domain sampling shows that the owner abstraction is the chapter's
summability theorem `one_div_nat_sq_summable_from_one`, together with mathlib's canonical
derived API `Summable.hasSum`, `HasSum.tendsto_sum_nat`, and
`CauchySeq.isBounded_range`. The primitive data are only the summable sequence
`n ↦ 1 / ((n + 1 : ℕ) : ℝ)^2`; boundedness of its partial sums is derived API. -/

/-- Theorem 12.0.4: the sequence `s_m = ∑_{n=1}^m 1 / n^2` is bounded. -/
theorem one_div_nat_sq_partialSums_isBounded :
    IsBounded
      (Set.range (fun m : ℕ ↦ ∑ n ∈ Finset.range m, 1 / ((n + 1 : ℕ) : ℝ) ^ (2 : ℕ))) := by
  simpa using
    one_div_nat_sq_summable_from_one.hasSum.tendsto_sum_nat.cauchySeq.isBounded_range
