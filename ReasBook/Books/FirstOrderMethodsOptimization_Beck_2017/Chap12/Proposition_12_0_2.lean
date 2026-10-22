/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Proposition 12.0.2 is a `bridge/view` item: the source-facing series starts at `n = 1`,
while the core owner abstraction is the mathlib `p`-series theorem
`Real.summable_one_div_nat_pow`, stated on `n : ℕ` starting at `0`. The proposition is the
canonical shift-by-one specialization of that owner. -/
recall summable_nat_add_iff
recall Real.summable_one_div_nat_pow

/-- Proposition 12.0.2: the series `∑_{n=1}^{\infty} 1 / n^2` converges. -/
theorem one_div_nat_sq_summable_from_one :
    Summable (fun n : ℕ ↦ 1 / ((n + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by
  -- The owner result is the `p`-series theorem at exponent `2`.
  have hpow : 1 < (2 : ℕ) := by
    decide
  have hsummable : Summable (fun n : ℕ ↦ 1 / (n : ℝ) ^ (2 : ℕ)) :=
    Real.summable_one_div_nat_pow.mpr hpow
  -- Shifting the summation index from `0` to `1` matches the textbook series.
  simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using
    (summable_nat_add_iff 1).2 hsummable
