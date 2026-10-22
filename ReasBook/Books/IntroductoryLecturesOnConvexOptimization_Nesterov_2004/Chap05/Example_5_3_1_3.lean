/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Example_5_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Example_5_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Proposition_5_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient HessianLocalNorm

noncomputable section

/- Example 5.3.1.3 lies in the scalar self-concordant-barrier domain.

Sampled owner-style declarations in this domain:
* `negLog_isStandardSelfConcordantOn` in `Example_5_1_3`, the chapter owner for the standard
  self-concordance of `x ↦ -log x` on `(0, ∞)`;
* `IsSelfConcordantBarrierOnWith` in `Definition_5_3_2`, the chapter owner for a
  `ν`-self-concordant barrier;
* `gradient_eq_deriv'` in mathlib, the one-dimensional bridge from the Euclidean gradient to the
  usual scalar derivative;
* `deriv_log` in mathlib, the canonical logarithmic derivative formula used only at proof level.

Source/core/bridge triage:
* source-facing: the logarithmic barrier for the nonnegative ray, expressed on its open domain
  `(0, ∞)`;
* core/canonical: `IsSelfConcordantBarrierOnWith (Set.Ioi (0 : ℝ)) 1`;
* bridge/view: `negLog_isStandardSelfConcordantOn`, which supplies the standard
  self-concordance part of the barrier owner.

Primitive data:
* the scalar logarithmic barrier `x ↦ -log x`;
* the open barrier domain `(0, ∞)`;
* the barrier parameter `ν = 1`.

Derived API:
* standard self-concordance on `(0, ∞)`, reused from `negLog_isStandardSelfConcordantOn`;
* the scalar identities `F'(x) = -1 / x` and `F''(x) = 1 / x^2`, used only to discharge the
  barrier-parameter inequality.

This refinement therefore keeps the source-facing barrier theorem, but removes the impression that
the file owns a second self-concordance proof for `-log`. The core owner is the barrier class,
and the standard-self-concordance input is reused directly from the upstream chapter theorem. -/

-- Proof sketch: reuse `negLog_isStandardSelfConcordantOn` for the self-concordance part of the
-- owner. For the barrier inequality, use the scalar derivative formulas
-- `F'(x) = -1 / x` and `F''(x) = 1 / x^2`; then the one-dimensional identity
-- `(F'(x))^2 / F''(x) = 1` shows that the sharp barrier parameter is `ν = 1`.
/-- Example 5.3.1.3: the logarithmic barrier `x ↦ -log x`, defined on `(0, ∞)`, is a
`1`-self-concordant barrier for the nonnegative ray `{x : ℝ | 0 ≤ x}`. -/
theorem negLog_isSelfConcordantBarrierOnWith_nonnegativeRay :
    IsSelfConcordantBarrierOnWith (Set.Ioi (0 : ℝ)) 1 (fun x : ℝ ↦ -Real.log x) := by
  let f : ℝ → ℝ := quadraticAffineObjective 0 (-1 : ℝ) (0 : ℝ →L[ℝ] ℝ)
  have hf : f = fun x : ℝ ↦ -x := by
    funext x
    have hinner : inner ℝ (-1 : ℝ) x = -x := by
      convert (RCLike.inner_apply (-1 : ℝ) x) using 1
      simp
    rw [show f x = quadraticAffineObjective 0 (-1 : ℝ) (0 : ℝ →L[ℝ] ℝ) x by rfl]
    rw [quadraticAffineObjective_apply, ContinuousLinearMap.zero_apply]
    simp [hinner]
  have hdom : {x : ℝ | f x < 0} = Set.Ioi (0 : ℝ) := by
    ext x
    rw [Set.mem_setOf_eq, Set.mem_Ioi]
    rw [hf]
    constructor <;> intro hx <;> linarith
  have hbarrier_eq : sublevelLogBarrier f 0 = fun x : ℝ ↦ -Real.log x := by
    funext x
    rw [sublevelLogBarrier_apply, hf]
    congr 1
    simp
  have hstd :
      IsStandardSelfConcordantOn {x : ℝ | f x < 0} (sublevelLogBarrier f 0) := by
    simpa [hdom, hbarrier_eq] using negLog_isStandardSelfConcordantOn
  have hf_self : IsSelfConcordantOnWith (Set.univ : Set ℝ) 0 f := by
    simpa [f] using
      quadraticAffineObjective_isSelfConcordantOnWith_zero 0 (-1 : ℝ)
        (0 : ℝ →L[ℝ] ℝ) ContinuousLinearMap.isPositive_zero
  have hbarrier :
      IsSelfConcordantBarrierOnWith {x : ℝ | f x < 0} 1 (sublevelLogBarrier f 0) := by
    refine
      { toIsStandardSelfConcordantOn := hstd
        barrier_parameter_bound := ?_ }
    intro x hx u
    have hF_pos : (hessian (sublevelLogBarrier f 0) x).IsPositive :=
      hstd.hessian_isPositive hx
    have hbarrier_one :
        ∀ v : ℝ,
          2 * inner ℝ (∇ (sublevelLogBarrier f 0) x) v -
              inner ℝ v (hessian (sublevelLogBarrier f 0) x v) ≤ (1 : ℝ) := by
      have hiff :
          (∀ v : ℝ,
            2 * inner ℝ (∇ (sublevelLogBarrier f 0) x) v -
                inner ℝ v (hessian (sublevelLogBarrier f 0) x v) ≤ (1 : ℝ)) ↔
            ∀ v : ℝ,
              (inner ℝ (∇ (sublevelLogBarrier f 0) x) v) ^ (2 : ℕ) ≤
                (1 : ℝ) * ‖v‖[sublevelLogBarrier f 0; x] ^ (2 : ℕ) := by
        simpa using
          (show
            (∀ v : ℝ,
              2 * inner ℝ (∇ (sublevelLogBarrier f 0) x) v -
                  inner ℝ v (hessian (sublevelLogBarrier f 0) x v) ≤ ((1 : NNReal) : ℝ)) ↔
              ∀ v : ℝ,
                (inner ℝ (∇ (sublevelLogBarrier f 0) x) v) ^ (2 : ℕ) ≤
                  ((1 : NNReal) : ℝ) * ‖v‖[sublevelLogBarrier f 0; x] ^ (2 : ℕ) from
            barrier_parameter_bound_iff_gradient_inner_sq_le hF_pos)
      refine hiff.2 ?_
      intro v
      calc
        (inner ℝ (∇ (sublevelLogBarrier f 0) x) v) ^ (2 : ℕ) ≤
            ‖v‖[sublevelLogBarrier f 0; x] ^ (2 : ℕ) := by
          simpa using hf_self.sublevelLogBarrier_gradient_inner_sq_le 0 (by simp) hx
        _ = (1 : ℝ) * ‖v‖[sublevelLogBarrier f 0; x] ^ (2 : ℕ) := by
          ring
    exact hbarrier_one u
  simpa [hdom, hbarrier_eq] using hbarrier
