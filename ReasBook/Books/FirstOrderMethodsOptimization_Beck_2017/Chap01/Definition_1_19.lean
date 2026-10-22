/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

section

variable {n : ℕ} {p : ℝ}

/- Definition 1.19 is organized around the canonical owner `PiLp`: for `p ≥ 1`, the textbook
`l_p` norm on `ℝ^n` is the `PiLp` norm on the `WithLp` copy of `Fin n → ℝ`, and the source-facing
coordinate formula below is the real-valued specialization of `PiLp.norm_eq_sum`. -/
recall PiLp.norm_eq_sum

-- Proof sketch: apply `PiLp.norm_eq_sum` to `WithLp.toLp (ENNReal.ofReal p) x`, then simplify the
-- coordinates using `PiLp.toLp_apply`, `Real.norm_eq_abs`, and `ENNReal.toReal_ofReal` under the
-- hypothesis `1 ≤ p`.
/-- The canonical `PiLp` norm on `Fin n → ℝ` is the textbook `l_p` coordinate formula. -/
theorem norm_toLp_eq_sum_abs_rpow (hp : 1 ≤ p) (x : Fin n → ℝ) :
    ‖WithLp.toLp (ENNReal.ofReal p) x‖ = (∑ i, |x i| ^ p) ^ (1 / p) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  simpa [PiLp.toLp_apply, Real.norm_eq_abs, ENNReal.toReal_ofReal hp0.le] using
    (PiLp.norm_eq_sum
      (by simpa [ENNReal.toReal_ofReal hp0.le] using hp0)
      (WithLp.toLp (ENNReal.ofReal p) x))

end
