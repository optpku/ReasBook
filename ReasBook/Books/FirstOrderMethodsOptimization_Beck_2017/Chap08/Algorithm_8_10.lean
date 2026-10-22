/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_12

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

noncomputable section

section

variable {E : Type u} {Ω : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Algorithm 8.10 is `source-facing`: the textbook specifies the stochastic projected subgradient
iteration itself, not a packaged stochastic oracle. The canonical owner for the projection step is
the chapter map `metricProjection`, while the stochastic direction choice is most naturally modeled
pathwise by an `E`-valued sample rule `g : ℕ → C → Ω → E`. This keeps the public API on the
iterate sequence and avoids a noncanonical wrapper around the randomness. -/

/-- Algorithm 8.10: for a nonempty closed convex feasible set `C`, a feasible initial point `x0`,
stepsizes `t_k`, and a sample-indexed direction rule `g`, the stochastic projected subgradient
method generates the pathwise iterate sequence
`x^{k+1}(ω) = P_C (x^k(ω) - t_k g_k(x^k(ω), ω))`. -/
def stochastic_projected_subgradient_method (C : Set E)
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (g : ℕ → C → Ω → E) (t : ℕ → ℝ) (x0 : C) : ℕ → Ω → C
  | 0 => fun _ ↦ x0
  | k + 1 =>
      let xk := stochastic_projected_subgradient_method C hC_nonempty hC_closed hC_convex g t x0 k
      fun ω ↦
        metricProjection C hC_nonempty hC_closed hC_convex
          ((xk ω : E) - t k • g k (xk ω) ω)

/-- A stepsize rule for the stochastic projected subgradient method is admissible when every
stepsize is strictly positive. -/
def stochastic_projected_subgradient_stepsizes_positive (t : ℕ → ℝ) : Prop :=
  ∀ k, 0 < t k

/-- The ambient-space iterate sequence associated to
`stochastic_projected_subgradient_method`. This is the canonical bridge for objective values,
conditional expectations, and norm estimates, where the iterate is used as an `E`-valued random
variable rather than as a point of `C`. -/
abbrev stochastic_projected_subgradient_method_iterate (C : Set E)
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (g : ℕ → C → Ω → E) (t : ℕ → ℝ) (x0 : C) : ℕ → Ω → E :=
  fun k ω ↦
    (stochastic_projected_subgradient_method
      C hC_nonempty hC_closed hC_convex g t x0 k ω : E)

section

variable (C : Set E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
variable (g : ℕ → C → Ω → E) (t : ℕ → ℝ) (x0 : C)

local notation "x[" k "]" =>
  stochastic_projected_subgradient_method C hC_nonempty hC_closed hC_convex g t x0 k

-- Proof sketch: unfold the recursive definition of `stochastic_projected_subgradient_method` at
-- `0`; the initial random iterate is the constant path with value `x0`.
/-- The stochastic projected-subgradient sequence starts from the prescribed feasible initial
point at every sample `ω`. -/
theorem stochastic_projected_subgradient_method_zero (ω : Ω) :
    x[0] ω = x0 := by
  -- Unfold the zero branch of the recursive algorithm; the initial iterate is constant.
  rfl

-- Proof sketch: unfold the recursive definition of `stochastic_projected_subgradient_method` at
-- `k + 1` and evaluate the resulting function at the sample `ω`.
/-- One stochastic projected-subgradient step applies the metric projection onto `C` to the
current sample iterate minus the current stepsize times the sampled direction. -/
theorem stochastic_projected_subgradient_method_succ (k : ℕ) (ω : Ω) :
    x[k + 1] ω =
      metricProjection C hC_nonempty hC_closed hC_convex
        ((x[k] ω : E) - t k • g k (x[k] ω) ω) := by
  -- Unfold the successor branch; the local `let xk := ...` reduces to the current iterate `x[k]`.
  rfl

-- Proof sketch: unfold `stochastic_projected_subgradient_method_iterate` at `0`; this is the
-- ambient-space coercion of `stochastic_projected_subgradient_method_zero`.
/-- The ambient-space stochastic iterate sequence starts from the prescribed initial point. -/
@[simp] theorem stochastic_projected_subgradient_method_iterate_zero :
    stochastic_projected_subgradient_method_iterate C hC_nonempty hC_closed hC_convex g t x0 0 =
      fun _ ↦ (x0 : E) := by
  rfl

-- Proof sketch: unfold `stochastic_projected_subgradient_method_iterate` at `k + 1`; this is the
-- ambient-space version of `stochastic_projected_subgradient_method_succ`.
/-- One stochastic projected-subgradient step in ambient space applies the metric projection to the
current iterate minus the sampled stochastic direction. -/
theorem stochastic_projected_subgradient_method_iterate_succ (k : ℕ) (ω : Ω) :
    stochastic_projected_subgradient_method_iterate
        C hC_nonempty hC_closed hC_convex g t x0 (k + 1) ω =
      metricProjection C hC_nonempty hC_closed hC_convex
        (stochastic_projected_subgradient_method_iterate
          C hC_nonempty hC_closed hC_convex g t x0 k ω -
          t k • g k (x[k] ω) ω) := by
  rfl

-- Proof sketch: unfold `stochastic_projected_subgradient_stepsizes_positive` and specialize the
-- defining condition at the index `k`.
/-- Under the positivity condition, the stepsize chosen at iteration `k` is strictly positive. -/
theorem stochastic_projected_subgradient_stepsize_pos
    (h : stochastic_projected_subgradient_stepsizes_positive t) (k : ℕ) :
    0 < t k := by
  -- Specialize the defining positivity predicate at the current index.
  exact h k

end

end
