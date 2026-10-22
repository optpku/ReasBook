/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped BigOperators

section

variable {m : ℕ} {p : ℝ}
variable {E : Fin m → Type u}
variable [∀ i, NormedAddCommGroup (E i)]

/- Definition 1.36: the composite `l_p` norm on a finite Cartesian product of normed vector
spaces is the canonical `PiLp` construction, i.e. the `L^p` norm on the `WithLp` copy of the
finite product. -/
recall PiLp.norm_eq_sum

-- Proof sketch: apply `PiLp.norm_eq_sum` to the element `WithLp.toLp (ENNReal.ofReal p) u`, then
-- simplify the exponent `((ENNReal.ofReal p).toReal)` to `p` using `ENNReal.toReal_ofReal` under
-- the hypothesis `1 ≤ p`.
/-- The canonical `PiLp` norm on a finite family of normed spaces is the textbook composite `l_p`
norm formula. -/
theorem norm_toLp_eq_sum_component_norm_rpow (hp : 1 ≤ p) (u : ∀ i : Fin m, E i) :
    ‖WithLp.toLp (ENNReal.ofReal p) u‖ = (∑ i, ‖u i‖ ^ p) ^ (1 / p) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  simpa [PiLp.toLp_apply, ENNReal.toReal_ofReal hp0.le] using
    (PiLp.norm_eq_sum
      (by simpa [ENNReal.toReal_ofReal hp0.le] using hp0)
      (WithLp.toLp (ENNReal.ofReal p) u))

end
