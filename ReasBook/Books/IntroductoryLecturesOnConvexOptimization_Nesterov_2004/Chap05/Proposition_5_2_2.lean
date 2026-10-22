/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_21
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_2_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_15

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

open scoped NewtonDecrement
open scoped BigOperators
open scoped SelfConcordantAuxiliaryFunction

/- Proposition 5.2.2 lies in the Chapter 5 self-concordant two-stage-strategy domain.

Sampled owner declarations:
* `DampedNewton.Method.IsSelfConcordant` in `Definition_5_2_1`, the Chapter 5 refinement of the
  recursive damped Newton owner;
* `NewtonDecrement.ofDetNeZero` and the source-facing notation
  `ndec(f, x, Mf, hx, hH)` in `Definition_5_0_24`, the canonical Newton-decrement owner at a
  domain point with nondegenerate Hessian;
* `selfConcordantTwoStageStrategy` and `selfConcordantTwoStageStrategy_eq_damped_iff` in
  `Definition_5_2_2`, the source-facing two-stage owner and its threshold bridge;
* `IsMinOn` in mathlib, the canonical minimizer owner reused throughout Chapter 5.

Best owner abstraction:
* source-facing: the assertion that the first `N` iterates of the damped Newton method remain in
  Stage 1 of the two-stage strategy;
* core/canonical: `DampedNewton.Method.IsSelfConcordant`, `ndec(f, x, Mf, hx, hH)`,
  `selfConcordantTwoStageStrategy`, and `IsMinOn f dom xStar`;
* bridge/view: the threshold inequality
  `1 / (2 M_f) ≤ NewtonDecrement.ofDetNeZero ...`.

Primitive data:
* the damped self-concordant Newton method;
* the objective `f` and domain `dom`;
* the positive self-concordance parameter `Mf`;
* the canonical Newton decrement at each iterate, read through the chapter notation
  `ndec(f, method k, Mf, hmethod.iterates_mem k, method.hessian_nondegenerate k)`;
* the Stage-1 membership condition for the first `N` iterates;
* the canonical minimizer owner `IsMinOn f dom xStar`.

Derived API:
* the pointwise threshold characterization of Stage 1 from
  `selfConcordantTwoStageStrategy_eq_damped_iff`;
* the lower bound `f xStar ≤ f (method k)` obtained by applying `IsMinOn` to any iterate in `dom`;
* the Stage-1 damped-step decrease estimate obtained at each iterate from the canonical one-step
  damped Newton owner.

This file stays source-facing at the level of the Stage-1 segment length, but removes the parallel
free decrement sequence and instead reads Stage 1 directly from the canonical Newton decrement
along the damped self-concordant Newton method. -/

namespace DampedNewton.Method.IsSelfConcordant

section

variable {dom : Set E} {f : E → ℝ} {Mf : NNRealˣ}
variable [IsSelfConcordantOnWith dom (Mf : NNReal) f]
variable {x0 : E}

-- Proof sketch: record Stage 1 directly through the canonical Newton decrement of the damped
-- method and then use `selfConcordantTwoStageStrategy_eq_damped_iff`.
/-- `method.IsStageOneUpTo N` means that the first `N` iterates of the damped self-concordant
Newton method remain in Stage 1 of the two-stage strategy from Definition 5.2.2. -/
def IsStageOneUpTo
    {method : DampedNewton.Method f x0}
    (hmethod : method.IsSelfConcordant dom (Mf : NNReal) SelfConcordantNewtonVariant.damped)
    (N : ℕ) : Prop :=
  ∀ k : ℕ, k < N →
    selfConcordantTwoStageStrategy Mf
        (ndec(
          f, (method k), (Mf : NNReal), (hmethod.iterates_mem k),
          (method.hessian_nondegenerate k))) =
      .damped

-- Proof sketch: unfold `DampedNewton.Method.IsSelfConcordant.IsStageOneUpTo` and apply
-- `selfConcordantTwoStageStrategy_eq_damped_iff` at each iterate.
/-- Expanding `method.IsStageOneUpTo N` says that every index `k < N` satisfies the Stage 1
threshold inequality `1 / (2 M_f) ≤ λ_f(x_k)` for the canonical Newton decrement of `method`. -/
theorem isStageOneUpTo_iff
    {method : DampedNewton.Method f x0}
    (hmethod : method.IsSelfConcordant dom (Mf : NNReal) SelfConcordantNewtonVariant.damped)
    {N : ℕ} :
    hmethod.IsStageOneUpTo N ↔
      ∀ k : ℕ, k < N →
        1 / (2 * (Mf : ℝ)) ≤
          ndec(
            f, (method k), (Mf : NNReal), (hmethod.iterates_mem k),
            (method.hessian_nondegenerate k)) := by
  constructor
  · intro h k hk
    exact
      (selfConcordantTwoStageStrategy_eq_damped_iff Mf
        (ndec(
          f, (method k), (Mf : NNReal), (hmethod.iterates_mem k),
          (method.hessian_nondegenerate k)))).1
        (h k hk)
  · intro h k hk
    exact
      (selfConcordantTwoStageStrategy_eq_damped_iff Mf
        (ndec(
          f, (method k), (Mf : NNReal), (hmethod.iterates_mem k),
          (method.hessian_nondegenerate k)))).2
        (h k hk)

end

end DampedNewton.Method.IsSelfConcordant

section

variable {dom : Set E} {f : E → ℝ} {Mf : NNRealˣ}
variable [IsSelfConcordantOnWith dom (Mf : NNReal) f]

-- Proof sketch: rewrite `ω(1 / 2)` explicitly and compare `log (3 / 2)` with `1 / 2` using the
-- standard bound `log x < x - 1`.
/-- Helper for Proposition 5.2.2: the textbook constant `ω(1 / 2)` is strictly positive. -/
theorem selfConcordantOmegaAtOneHalf_pos :
    0 < selfConcordantOmegaAtOneHalf := by
  -- Rewriting `ω(1 / 2)` reduces the claim to the scalar inequality
  -- `log (3 / 2) < 1 / 2`.
  rw [selfConcordantOmegaAtOneHalf, selfConcordantOmega_apply, coe_selfConcordantOmegaOneHalfArg]
  have hthreeHalf_pos : 0 < (3 / 2 : ℝ) := by
    norm_num
  have hthreeHalf_ne : (3 / 2 : ℝ) ≠ 1 := by
    norm_num
  have hlog_lt : Real.log (3 / 2 : ℝ) < (1 / 2 : ℝ) := by
    have hlog_lt' : Real.log (3 / 2 : ℝ) < (3 / 2 : ℝ) - 1 := by
      exact Real.log_lt_sub_one_of_pos hthreeHalf_pos hthreeHalf_ne
    norm_num at hlog_lt' ⊢
    exact hlog_lt'
  have hlog_lt_half : Real.log (1 + (1 / 2 : ℝ)) < (1 / 2 : ℝ) := by
    convert hlog_lt using 1 <;> norm_num
  exact sub_pos.mpr hlog_lt_half

-- Proof sketch: compare `ω(t)` with `ω(1 / 2)` through the ratio
-- `((1 + t) / (3 / 2))`, then apply `log z ≤ z - 1` and the Stage-1 lower bound `1 / 2 ≤ t`.
/-- Helper for Proposition 5.2.2: once `t ≥ 1 / 2`, the auxiliary function `ω` is bounded below
by `ω(1 / 2)`. -/
theorem selfConcordantOmegaAtOneHalf_le_of_half_le
    (t : Set.Ioi (-1 : ℝ)) (ht : (1 / 2 : ℝ) ≤ (t : ℝ)) :
    selfConcordantOmegaAtOneHalf ≤ ω t := by
  -- Rewriting both `ω` terms turns the desired monotonicity statement into a logarithmic
  -- comparison for the normalized ratio `(1 + t) / (3 / 2)`.
  rw [selfConcordantOmegaAtOneHalf, selfConcordantOmega_apply, coe_selfConcordantOmegaOneHalfArg,
    selfConcordantOmega_apply]
  have hthreeHalf_pos : 0 < (3 / 2 : ℝ) := by
    norm_num
  have ht_pos : 0 < 1 + (t : ℝ) := by
    linarith [t.2]
  have hratio_pos : 0 < (1 + (t : ℝ)) / (3 / 2 : ℝ) := by
    exact div_pos ht_pos hthreeHalf_pos
  have hlog_le :
      Real.log ((1 + (t : ℝ)) / (3 / 2 : ℝ)) ≤
        ((1 + (t : ℝ)) / (3 / 2 : ℝ)) - 1 := by
    exact Real.log_le_sub_one_of_pos hratio_pos
  have hratio_le : ((1 + (t : ℝ)) / (3 / 2 : ℝ)) - 1 ≤ (t : ℝ) - 1 / 2 := by
    nlinarith
  have hlog_div :
      Real.log ((1 + (t : ℝ)) / (3 / 2 : ℝ)) =
        Real.log (1 + (t : ℝ)) - Real.log (3 / 2 : ℝ) := by
    exact Real.log_div ht_pos.ne' (by norm_num)
  have hbridge : Real.log (1 + (t : ℝ)) - Real.log (3 / 2 : ℝ) ≤ (t : ℝ) - 1 / 2 := by
    rw [← hlog_div]
    exact le_trans hlog_le hratio_le
  linarith

end

namespace DampedNewton.Method.IsSelfConcordant

section

variable {dom : Set E} {f : E → ℝ} {Mf : NNRealˣ}
variable [IsSelfConcordantOnWith dom (Mf : NNReal) f]
variable {x0 : E} {method : DampedNewton.Method f x0}
variable (hmethod : method.IsSelfConcordant dom (Mf : NNReal) SelfConcordantNewtonVariant.damped)

-- Proof sketch: the Stage-1 threshold gives `M_f λ_k ≥ 1 / 2`; Theorem 5.1.15 then yields the
-- damped one-step decrease with `ω(M_f λ_k)`, and the scalar helper replaces it by the uniform
-- lower bound `ω(1 / 2)`.
/-- Helper for Proposition 5.2.2: every Stage-1 damped step decreases the objective by at least
`M_f⁻² ω(1 / 2)`. -/
theorem stageOne_value_drop_ge_omega_half
    {N k : ℕ} (hstage : hmethod.IsStageOneUpTo N) (hk : k < N) :
    selfConcordantOmegaAtOneHalf / (Mf : ℝ) ^ (2 : ℕ) ≤
      f (method k) - f (method (k + 1)) := by
  let δk :=
    ndec(
      f, (method k), (Mf : NNReal), (hmethod.iterates_mem k),
      (method.hessian_nondegenerate k))
  let ωargk :=
    NewtonDecrement.omegaArgOfDetNeZero
      (Mf : NNReal) f (hmethod.iterates_mem k) (method.hessian_nondegenerate k)
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hMf_sq_pos : 0 < (Mf : ℝ) ^ (2 : ℕ) := by
    positivity
  have hMf_sq_nonneg : 0 ≤ (1 / (Mf : ℝ) ^ (2 : ℕ)) := by
    positivity
  have hMf_ne_zero : (Mf : NNReal) ≠ 0 := by
    exact_mod_cast Units.ne_zero Mf
  -- The Stage-1 owner equivalence gives the threshold `1 / (2 M_f) ≤ λ_k`.
  have hthreshold :
      1 / (2 * (Mf : ℝ)) ≤ δk := by
    exact (isStageOneUpTo_iff hmethod).1 hstage k hk
  have hmul :
      (Mf : ℝ) * (1 / (2 * (Mf : ℝ))) ≤ (Mf : ℝ) * δk := by
    exact mul_le_mul_of_nonneg_left hthreshold hMf_pos.le
  have hleft : (Mf : ℝ) * (1 / (2 * (Mf : ℝ))) = (1 / 2 : ℝ) := by
    field_simp [ne_of_gt hMf_pos]
  have hhalf :
      (1 / 2 : ℝ) ≤ (Mf : ℝ) * δk := by
    simpa [δk, hleft] using hmul
  have hωarg_ge :
      (1 / 2 : ℝ) ≤ (ωargk : ℝ) := by
    simpa [ωargk, δk, NewtonDecrement.coe_omegaArgOfDetNeZero, mul_comm] using hhalf
  -- The damped one-step decrease is the canonical per-iterate drop estimate from Theorem 5.1.15.
  have hstep :
      f (method (k + 1)) ≤
        f (method k) -
          ((1 / (Mf : ℝ) ^ (2 : ℕ)) * ω ωargk) := by
    simpa [ωargk, δk, hmethod.succ_eq_nextPoint k, hMf_ne_zero] using
      (selfConcordant_dampedNewtonStep_value_decrease
        (Mf := (Mf : NNReal)) (f := f)
        (x := method k) (hmethod.iterates_mem k) (method.hessian_nondegenerate k))
  have hωmono : selfConcordantOmegaAtOneHalf ≤ ω ωargk := by
    exact selfConcordantOmegaAtOneHalf_le_of_half_le ωargk hωarg_ge
  have hscaled :
      (1 / (Mf : ℝ) ^ (2 : ℕ)) * selfConcordantOmegaAtOneHalf ≤
        (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω ωargk := by
    exact mul_le_mul_of_nonneg_left hωmono hMf_sq_nonneg
  have hdrop :
      (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω ωargk ≤
        f (method k) - f (method (k + 1)) := by
    linarith
  -- Reordering the scalar factor recovers the source-facing Stage-1 decrease amount.
  calc
    selfConcordantOmegaAtOneHalf / (Mf : ℝ) ^ (2 : ℕ)
        = (1 / (Mf : ℝ) ^ (2 : ℕ)) * selfConcordantOmegaAtOneHalf := by
          ring_nf
    _ ≤ (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω ωargk := hscaled
    _ ≤ f (method k) - f (method (k + 1)) := hdrop

-- Proof sketch: sum the uniform Stage-1 decrease over `k = 0, ..., N - 1` and telescope the
-- resulting objective differences.
/-- Helper for Proposition 5.2.2: summing the uniform Stage-1 decrease bounds yields a telescope
from `x₀` to `x_N`. -/
theorem stageOne_telescope
    {N : ℕ} (hstage : hmethod.IsStageOneUpTo N) :
    (N : ℝ) * selfConcordantOmegaAtOneHalf / (Mf : ℝ) ^ (2 : ℕ) ≤
      f x0 - f (method N) := by
  have hsum_const :
      Finset.sum (Finset.range N)
        (fun _ : ℕ ↦ selfConcordantOmegaAtOneHalf / (Mf : ℝ) ^ (2 : ℕ)) =
        (N : ℝ) * (selfConcordantOmegaAtOneHalf / (Mf : ℝ) ^ (2 : ℕ)) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hsum_le :
      Finset.sum (Finset.range N)
        (fun _ : ℕ ↦ selfConcordantOmegaAtOneHalf / (Mf : ℝ) ^ (2 : ℕ)) ≤
      Finset.sum (Finset.range N) (fun k ↦ f (method k) - f (method (k + 1))) := by
    refine Finset.sum_le_sum ?_
    intro k hk
    exact hmethod.stageOne_value_drop_ge_omega_half hstage (Finset.mem_range.mp hk)
  have htel :
      Finset.sum (Finset.range N) (fun k ↦ f (method k) - f (method (k + 1))) =
        f (method 0) - f (method N) := by
    simpa using (Finset.sum_range_sub' (fun k ↦ f (method k)) N)
  -- Replacing the telescoped left endpoint by `x0` gives the source-facing terminal gap.
  calc
    (N : ℝ) * selfConcordantOmegaAtOneHalf / (Mf : ℝ) ^ (2 : ℕ)
        = (N : ℝ) * (selfConcordantOmegaAtOneHalf / (Mf : ℝ) ^ (2 : ℕ)) := by
            ring_nf
    _ = Finset.sum (Finset.range N)
          (fun _ : ℕ ↦ selfConcordantOmegaAtOneHalf / (Mf : ℝ) ^ (2 : ℕ)) := by
            rw [hsum_const]
    _ ≤ Finset.sum (Finset.range N) (fun k ↦ f (method k) - f (method (k + 1))) := hsum_le
    _ = f (method 0) - f (method N) := htel
    _ = f x0 - f (method N) := by
      simpa [method.zero_eq]

end

end DampedNewton.Method.IsSelfConcordant

-- Proof sketch: use the Stage 1 hypothesis to justify the uniform decrease estimate
-- `f(x_{k + 1}) ≤ f(x_k) - M_f⁻² ω(M_f λ_f(x_k))` for every `k < N`. The Stage 1 hypothesis gives
-- `1 / 2 ≤ M_f λ_f(x_k)`, so monotonicity of `ω` yields the uniform lower bound
-- `M_f⁻² ω(1 / 2)`. Summing these `N` inequalities gives
-- `f(x_N) ≤ f(x_0) - N * M_f⁻² ω(1 / 2)`. Since `xStar` minimizes `f` on `dom` and the method
-- stays in `dom`, we have `f xStar ≤ f(x_N)`, and rearranging yields the stated estimate.
/-- Proposition 5.2.2: if the first `N` iterates of the damped segment of the two-stage
self-concordant Newton method remain in Stage 1, then
`N ≤ M_f^2 (f(x_0) - f(x_f^*)) / ω(1 / 2)`, where `x_f^*` minimizes `f` on the domain. -/
theorem selfConcordantTwoStage_stageOneLength_le
    {dom : Set E} {f : E → ℝ} {Mf : NNRealˣ} [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    {x0 : E}
    (method : DampedNewton.Method f x0)
    (hmethod : method.IsSelfConcordant dom (Mf : NNReal) SelfConcordantNewtonVariant.damped)
    {xStar : E} {N : ℕ}
    (hmin : IsMinOn f dom xStar)
    (hstage : hmethod.IsStageOneUpTo N) :
    (N : ℝ) ≤
      (Mf : ℝ) ^ (2 : ℕ) * (f x0 - f xStar) /
        selfConcordantOmegaAtOneHalf := by
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hMf_sq_pos : 0 < (Mf : ℝ) ^ (2 : ℕ) := by
    simpa [pow_two] using sq_pos_of_pos hMf_pos
  have hω_pos : 0 < selfConcordantOmegaAtOneHalf := by
    exact selfConcordantOmegaAtOneHalf_pos
  -- The Stage-1 telescope controls the terminal gap `f x0 - f (method N)`.
  have htel :
      (N : ℝ) * selfConcordantOmegaAtOneHalf / (Mf : ℝ) ^ (2 : ℕ) ≤
        f x0 - f (method N) := by
    exact hmethod.stageOne_telescope hstage
  -- Comparing the terminal iterate with the minimizer upgrades the telescope to the full gap.
  have hminN : f xStar ≤ f (method N) := by
    exact (isMinOn_iff.mp hmin) (method N) (hmethod.iterates_mem N)
  have hgap :
      f x0 - f (method N) ≤ f x0 - f xStar := by
    simpa using sub_le_sub_left hminN (f x0)
  have hbound :
      (N : ℝ) * selfConcordantOmegaAtOneHalf / (Mf : ℝ) ^ (2 : ℕ) ≤
        f x0 - f xStar := by
    exact htel.trans hgap
  have hscaled :
      (N : ℝ) * selfConcordantOmegaAtOneHalf ≤
        (f x0 - f xStar) * (Mf : ℝ) ^ (2 : ℕ) := by
    exact (div_le_iff₀ hMf_sq_pos).1 hbound
  -- Dividing by the positive constant `ω(1 / 2)` yields the claimed Stage-1 length bound.
  exact (le_div_iff₀ hω_pos).2 <| by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled

end
