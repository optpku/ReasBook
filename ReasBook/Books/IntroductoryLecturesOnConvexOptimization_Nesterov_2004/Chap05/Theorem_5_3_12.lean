/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_20
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_5_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Lemma_5_3_3

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open HessianDualLocalNorm
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 5.3.12 lies in the Chapter 5 auxiliary-central-path / analytic-center / local-dual-norm
domain.

Sampled owner declarations:
* `dualLocalNorm` in `Definition_5_0_20`, the chapter owner for the Hessian-metric dual local
  norm of a covector;
* `HessianDualLocalNorm.ofPosDefMem` in `Definition_5_0_20`, the canonical domain-level bridge
  from positive-definite Hessians to that dual norm;
* `IsMinOn` as recalled in `Definition_5_3_3`, the neighboring chapter owner surface for analytic
  centers;
* `IsCentralPath` in `Definition_5_3_6_1`, the chapter owner for the auxiliary central path;
* `dualLocalNorm_gradient_auxiliaryCentralPath_le_barrierParameter_add_two_sqrt_mul_initial` in
  `Lemma_5_3_3`, the chapter bridge that bounds the iterate gradient norm by the analytic-center
  norm `‖∇ F(y₀)‖*_{x_F^*}`;
* `StoppedIntermediateSelfConcordantNewtonMethod` in `Definition_5_3_5_1`, the source-facing
  owner for the stopped intermediate Newton preprocessing method.

Best owner abstraction:
* source-facing: the stopping estimate for a
  `StoppedIntermediateSelfConcordantNewtonMethod`, stated with the auxiliary central path based at
  `y₀` and the analytic center `x_F^*` of the barrier;
* core/canonical: the stopped-method owner
  `StoppedIntermediateSelfConcordantNewtonMethod F y0 (β + γ)` together with the dual local norm
  bridge `HessianDualLocalNorm.ofPosDefMem F xFStar.2 (toDual ℝ E (∇ F (y0 : E)))`;
* bridge/view: the scalar logarithmic helper obtained by abstracting the dual norm and the
  auxiliary decay profile to scalar data.

Primitive data:
* the stopped intermediate Newton method;
* the auxiliary central path `yStar`;
* the analytic center `xFStar`;
* the discrete auxiliary-path parameters `t`;
* the positive-definite-Hessian owner on `dom`, used to form the dual local norm at `xFStar`;
* the positive complexity parameters `γ` and `β + √ν`;
* the exponential decay estimate for `t`;
* the comparison bound of the iterate decrement by the auxiliary-central-path residual norm.

Derived API:
* the stopping index `method.stopIndex`;
* the ordinary Newton decrement `method.decrement k`;
* the logarithmic stopping bound built from the analytic-center norm `‖∇ F(y₀)‖*_{x_F^*}`.

This file therefore keeps the stopped-method owner, the auxiliary central path, and the
analytic-center hypothesis on the public surface, while demoting only the scalar logarithmic
estimate to a private proof helper. -/

section

variable {dom : Set E} {F : E → ℝ} {ν : NNReal} [IsSelfConcordantBarrierOnWith dom ν F]
variable {y0 : dom} {β γ : ℝ}

-- Proof sketch: use the positivity of `γ` and `β + √ν` so that the exponential decay rate and the
-- logarithmic denominator have their textbook sign, then combine the exponential decay estimate
-- for `t_k` with the bound
-- `λ_F(y_k) ≤ β + t_k (ν + 2 √ν) R` for a scalar reference norm `R`.
-- Since `method` stops when the ordinary Newton decrement drops below `β + γ`, solving the
-- resulting scalar inequality for `k` yields the stated natural-ceiling bound.
/-- Auxiliary scalarized stopping estimate: if an auxiliary path-following scheme satisfies the
generic decrement bound `λ_F(y_k) ≤ β + t_k (ν + 2 √ν) R` and the geometric decay estimate for
`t_k`, then the stopping index is bounded by the corresponding logarithmic expression in `R`. -/
private theorem stopIndex_le_natCeil_of_referenceDualNorm
    (method : StoppedIntermediateSelfConcordantNewtonMethod F y0 (β + γ))
    (t : ℕ → ℝ)
    (referenceDualNorm : ℝ)
    (hreferenceNonneg : 0 ≤ referenceDualNorm)
    (hγ : 0 < γ)
    (hβsqrt : 0 < β + Real.sqrt (ν : ℝ))
    (ht :
      ∀ k : ℕ,
        t k ≤ Real.exp (-γ * (k : ℝ) / (β + Real.sqrt (ν : ℝ))))
    (hdecrement :
      ∀ k : ℕ,
        method.decrement k ≤
          β + t k * (((ν : ℝ) + 2 * Real.sqrt (ν : ℝ)) * referenceDualNorm)) :
    method.stopIndex ≤
      ⌈((β + Real.sqrt (ν : ℝ)) / γ) *
          Real.log
            ((((ν : ℝ) + 2 * Real.sqrt (ν : ℝ)) * referenceDualNorm) / γ)⌉₊ := by
  let B := β + Real.sqrt (ν : ℝ)
  let C := (((ν : ℝ) + 2 * Real.sqrt (ν : ℝ)) * referenceDualNorm)
  have hBPos : 0 < B := hβsqrt
  have hscaleNonneg : 0 ≤ (ν : ℝ) + 2 * Real.sqrt (ν : ℝ) := by
    positivity
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg hscaleNonneg hreferenceNonneg
  by_cases hstop : method.stopIndex = 0
  · -- If the method already stops at the initial iterate, the ceiling bound is automatic.
    simp [hstop]
  · have hstopPos : 0 < method.stopIndex := Nat.pos_of_ne_zero hstop
    have hcontinue0 : β + γ < method.decrement 0 :=
      method.beta_lt_decrement_of_lt_stopIndex hstopPos
    have hstep0 : β + γ < β + t 0 * C := by
      have hbound0 := hdecrement 0
      dsimp [C] at hbound0
      exact lt_of_lt_of_le hcontinue0 hbound0
    have ht0 : t 0 ≤ 1 := by
      simpa [B] using ht 0
    have hbound0 : β + t 0 * C ≤ β + C := by
      have hmul : t 0 * C ≤ C := by
        simpa using mul_le_mul_of_nonneg_right ht0 hCnonneg
      linarith
    have hγC : γ < C := by
      linarith
    have hCdivPos : 0 < C / γ := by
      exact div_pos (lt_trans hγ hγC) hγ
    let k : ℕ := method.stopIndex - 1
    have hk : k < method.stopIndex := by
      dsimp [k]
      omega
    have hcontinuek : β + γ < method.decrement k :=
      method.beta_lt_decrement_of_lt_stopIndex hk
    have hstepk : β + γ < β + t k * C := by
      have hboundk := hdecrement k
      dsimp [C] at hboundk
      exact lt_of_lt_of_le hcontinuek hboundk
    have hboundk : β + t k * C ≤ β + Real.exp (-γ * (k : ℝ) / B) * C := by
      have hmul : t k * C ≤ Real.exp (-γ * (k : ℝ) / B) * C := by
        exact mul_le_mul_of_nonneg_right (by simpa [B] using ht k) hCnonneg
      linarith
    have hcore : γ < Real.exp (-γ * (k : ℝ) / B) * C := by
      linarith
    let a : ℝ := γ * (k : ℝ) / B
    have hmul : γ * Real.exp a < C := by
      have hcore' : γ < C / Real.exp a := by
        simpa [a, Real.exp_neg, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hcore
      exact (lt_div_iff₀ (Real.exp_pos a)).1 hcore'
    have hexp : Real.exp a < C / γ := by
      exact (lt_div_iff₀ hγ).2 (by simpa [mul_comm] using hmul)
    have hlog : a < Real.log (C / γ) := by
      exact (Real.lt_log_iff_exp_lt hCdivPos).2 hexp
    have hkReal : (k : ℝ) < (B / γ) * Real.log (C / γ) := by
      have hmulLog : γ * (k : ℝ) < Real.log (C / γ) * B := by
        exact (div_lt_iff₀ hBPos).1 (by simpa [a] using hlog)
      have hdivLog : (k : ℝ) < (Real.log (C / γ) * B) / γ := by
        exact (lt_div_iff₀ hγ).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmulLog)
      simpa [B, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdivLog
    have hsuc : k + 1 = method.stopIndex := by
      simpa [k, Nat.add_comm] using Nat.succ_pred_eq_of_pos hstopPos
    have hceil : k + 1 ≤ ⌈(B / γ) * Real.log (C / γ)⌉₊ := by
      exact Nat.add_one_le_ceil_iff.2 hkReal
    simpa [B, C, hsuc] using hceil

-- Proof sketch: apply the auxiliary-central-path gradient estimate from `Lemma_5_3_3` at the
-- path points `yStar (t k)` and the analytic center `xFStar`, turning the source-facing
-- decrement comparison into the scalar bound required by
-- `stopIndex_le_natCeil_of_referenceDualNorm`. The logarithmic stopping estimate then follows
-- with the analytic-center norm `‖∇ F(y₀)‖*_{x_F^*}` on the theorem surface.
/-- Theorem 5.3.12: let `x_F^*` be an analytic center of a `ν`-self-concordant barrier `F`, and
let `y*(t)` be the auxiliary central path based at `y₀`. If a stopped intermediate Newton method
started at `y₀` has decrement bounded along the iterates by
`β + ‖∇ F(y*(t_k))‖*_{y*(t_k)}` for a nonnegative parameter sequence `t_k` that decays like
`exp (-γ k / (β + √ν))`, then the stopping index is at most
`⌈((β + √ν) / γ) log (((ν + 2 √ν) ‖∇ F(y₀)‖*_{x_F^*}) / γ)⌉₊`, provided `γ > 0` and
`β + √ν > 0`. -/
theorem auxiliaryPathFollowing_stopIndex_le_natCeil_terminationBound
    (method : StoppedIntermediateSelfConcordantNewtonMethod F y0 (β + γ))
    [HasPositiveDefiniteHessianOn dom F]
    (yStar : Set.Ici (0 : ℝ) → dom)
    (xFStar : dom)
    (hxFStar : IsMinOn F dom (xFStar : E))
    (hpath : IsCentralPath dom (-∇ F (y0 : E)) F yStar)
    (t : ℕ → Set.Ici (0 : ℝ))
    (hγ : 0 < γ)
    (hβsqrt : 0 < β + Real.sqrt (ν : ℝ))
    (ht :
      ∀ k : ℕ,
        (t k : ℝ) ≤ Real.exp (-γ * (k : ℝ) / (β + Real.sqrt (ν : ℝ))))
    (hdecrement :
      ∀ k : ℕ,
        method.decrement k ≤
          β + ofPosDefMem F (yStar (t k)).2 (toDual ℝ E (∇ F (yStar (t k) : E)))) :
    method.stopIndex ≤
      ⌈((β + Real.sqrt (ν : ℝ)) / γ) *
          Real.log
            ((((ν : ℝ) + 2 * Real.sqrt (ν : ℝ)) *
                ofPosDefMem F xFStar.2 (toDual ℝ E (∇ F (y0 : E)))) / γ)⌉₊ := by
  let referenceDualNorm := ofPosDefMem F xFStar.2 (toDual ℝ E (∇ F (y0 : E)))
  have hreferenceNonneg : 0 ≤ referenceDualNorm := by
    -- The analytic-center reference norm is a Hessian dual local norm, hence nonnegative.
    dsimp [referenceDualNorm]
    exact
      dualLocalNorm_nonneg F (xFStar : E)
        (HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem xFStar.2)
        (hessian_isInvertible_of_det_ne_zero
          (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem xFStar.2))
        (toDual ℝ E (∇ F (y0 : E)))
  refine
    stopIndex_le_natCeil_of_referenceDualNorm
      method
      (fun k ↦ (t k : ℝ))
      referenceDualNorm
      hreferenceNonneg
      hγ hβsqrt ht ?_
  intro k
  -- Route correction: normalize the auxiliary-central-path estimate before composing it with the
  -- decrement hypothesis, rather than asking `linarith` and `ring` to recover the scalar shape.
  have hF : IsSelfConcordantBarrierOnWith dom ν F := inferInstance
  -- Reorder Lemma 5.3.3 into the multiplication order expected by the scalar stopping theorem.
  have hpathBoundOrdered :
      ofPosDefMem F (yStar (t k)).2 (toDual ℝ E (∇ F (yStar (t k) : E))) ≤
        (t k : ℝ) * (((ν : ℝ) + 2 * Real.sqrt (ν : ℝ)) * referenceDualNorm) := by
    simpa [referenceDualNorm, mul_comm, mul_left_comm, mul_assoc] using
      hF.dualLocalNorm_gradient_auxiliaryCentralPath_le_barrierParameter_add_two_sqrt_mul_initial
        y0 yStar xFStar hxFStar hpath (t k)
  -- Add `β` on both sides and normalize the additive order to match `hdecrement`.
  have hpathBoundWithBeta :
      β + ofPosDefMem F (yStar (t k)).2 (toDual ℝ E (∇ F (yStar (t k) : E))) ≤
        β + (t k : ℝ) * (((ν : ℝ) + 2 * Real.sqrt (ν : ℝ)) * referenceDualNorm) := by
    simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hpathBoundOrdered β
  -- The decrement hypothesis now composes directly with the normalized path estimate.
  exact le_trans (hdecrement k) hpathBoundWithBeta

end

end
