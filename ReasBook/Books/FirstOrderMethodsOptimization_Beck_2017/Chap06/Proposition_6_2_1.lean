/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

variable {E : Type u} [NormedAddCommGroup E]

/- Proposition 6.2.1 is `source-facing` in the Chapter 6 proximal-operator API. Domain sampling in
the minimal closure identifies the owner abstractions already upstream:

- `prox[...]` and `proximal_objective` from Definition 6.1 as the `core/canonical` owners,
- `mem_proximal_mapping_iff` as the canonical minimizer-set view,
- `prox_add_const` as the owner-level theorem showing additive real constants are derived data for
  proximal mappings.

The public source-facing data are only the constant value `c` and the base point `x`. The
zero-objective computation is the canonical special case of that source-facing statement, so it
should appear as a small companion theorem rather than as a parallel wrapper API. -/

-- Proof sketch: rewrite proximal membership for the zero function as global minimality of the
-- quadratic term. Evaluating at `x` forces the quadratic value at `u` to vanish, hence `u = x`;
-- conversely, the quadratic term is always nonnegative, so `x` is a minimizer.
/-- The proximal mapping of the zero function is the singleton containing the base point. -/
theorem prox_zero_eq_singleton (x : E) :
    prox[0] x = {x} := by
  rw [Set.eq_singleton_iff_unique_mem]
  constructor
  · rw [mem_proximal_mapping_iff, isMinOn_univ_iff]
    intro y
    have hy : 0 ≤ (1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ) := by
      positivity
    have hy' : (0 : EReal) ≤ ((((1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
      exact_mod_cast hy
    simpa [proximal_objective] using hy'
  · intro u hu
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hu
    have hux' : ((((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ)) : ℝ) : EReal) ≤ 0 := by
      simpa [proximal_objective] using hu x
    have hux : (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) ≤ 0 := by
      exact_mod_cast hux'
    have hnonneg : 0 ≤ (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) := by
      positivity
    have hnorm_sq : ‖u - x‖ ^ (2 : ℕ) = 0 := by
      have hquad : (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) = 0 := le_antisymm hux hnonneg
      nlinarith
    exact sub_eq_zero.mp (norm_eq_zero.mp (eq_zero_of_pow_eq_zero hnorm_sq))

-- Proof sketch: remove the additive constant from the objective via the owner theorem
-- `prox_add_const`, then apply the zero-function computation above.
/-- Proposition 6.2.1: if `f` is the constant function with value `c`, then the proximal mapping
at `x` is the singleton `{x}`. Equivalently, the proximal operator of a constant function is the
identity map. -/
@[simp]
theorem prox_const_eq_singleton (c : ℝ) (x : E) :
    prox[fun _ ↦ (c : EReal)] x = {x} := by
  calc
    prox[fun _ ↦ (c : EReal)] x = prox[0] x := by
      simpa using congrFun (prox_add_const (0 : E → EReal) c) x
    _ = {x} := prox_zero_eq_singleton x

end
