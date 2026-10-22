/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient HessianLocalNorm

noncomputable section

universe u

/- Theorem 5.1.4 lies in the Chapter 5 self-concordance / logarithmic-barrier domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantOnWith` from `Definition_5_1_1`, the constant-bearing chapter owner for
  self-concordance on a domain;
* `IsSelfConcordantOnWith.hessian_isPositive` from `Definition_5_1_1`, the chapter bridge from
  self-concordance to the pointwise Hessian-positivity owner;
* `hessianLocalNorm` from `Definition_5_1_1`, the chapter owner for the Hessian-induced local
  norm used by later barrier-parameter APIs;
* `IsSelfConcordantBarrierOnWith` from `Definition_5_3_2`, the barrier analogue used downstream;
* `hessian` from `Chap01/Definition_1_4_16`, the canonical second-order owner;
* `convexOn_iff_hessian_isPositive` from `Chap02/Theorem_2_4`, the local owner-level Hessian
  positivity criterion for convex `C²` data.

Source/core/bridge triage:
* source-facing: the logarithmic barrier `x ↦ -log (β - f x)`;
* core/canonical: `ContinuousLinearMap.IsPositive (hessian f x)` for the Hessian comparison
  clause, and `IsSelfConcordantOnWith dom Mf f` for the quantitative self-concordance clause;
* bridge/view: the textbook positivity estimate `0 < β - f x` on that strict sublevel set.

Primitive data:
* the function `f`;
* the threshold `β`;
* the ambient domain `dom`;
* the self-concordance owner `IsSelfConcordantOnWith dom Mf f`, which supplies the `C³`
  regularity and pointwise Hessian positivity needed for clauses (2) and (3).

Derived API:
* the strict sublevel set itself, expressed directly by the canonical set-builder rather than a
  second packaged owner;
* the barrier-gradient square estimate on the owner surface `‖h‖[sublevelLogBarrier f β; x]`,
  stated directly on `IsSelfConcordantOnWith dom Mf f` so that the required differential
  regularity remains explicit in the public API;
* the self-concordance constant formula, used directly in the main theorem rather than through a
  one-off wrapper.

This file therefore keeps the barrier as the source-facing owner and deletes the duplicate-wheel
derived wrappers around its natural domain and parameter formula. -/

variable {E : Type u}

/-- The logarithmic barrier associated with the strict sublevel set `{x | f x < β}` is
`x ↦ -log (β - f x)`. -/
def sublevelLogBarrier (f : E → ℝ) (β : ℝ) : E → ℝ :=
  fun x ↦ -Real.log (β - f x)

/-- Evaluating `sublevelLogBarrier f β` recovers the textbook formula `-log (β - f x)`. -/
@[simp]
theorem sublevelLogBarrier_apply (f : E → ℝ) (β : ℝ) (x : E) :
    sublevelLogBarrier f β x = -Real.log (β - f x) :=
  rfl

/-- Theorem 5.1.4 (1): on the strict sublevel set `{x | f x < β}`, the logarithmic barrier
`x ↦ -log (β - f x)` is well defined because its argument is positive. -/
-- Proof sketch: if `f x < β`, then `0 < β - f x`; this is exactly the positivity needed for
-- `Real.log (β - f x)`.
theorem sublevelLogBarrier_arg_pos_of_mem_domain
    (f : E → ℝ) (β : ℝ) {x : E} (hx : f x < β) :
    0 < β - f x := by
  -- The strict sublevel condition is exactly the positivity of the logarithmic slack.
  exact sub_pos.mpr hx

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section SublevelLogBarrier

variable {dom : Set E} {Mf : NNReal} {f : E → ℝ}

namespace IsSelfConcordantOnWith

/-- Helper for Theorem 5.1.4: a `C²` field has a differentiable gradient at the base point. -/
private theorem differentiableAt_gradient_of_contDiffAt_two
    {g : E → ℝ} {x : E} (hg : ContDiffAt ℝ 2 g x) :
    DifferentiableAt ℝ (∇ g) x := by
  -- Rewrite the gradient through the Riesz map so the chain rule applies to `fderiv`.
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ g) x := by
    exact
      (hg.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))).differentiableAt
        one_ne_zero
  change DifferentiableAt ℝ (fun y ↦ D (fderiv ℝ g y)) x
  exact (D.hasFDerivAt.comp x hfdiff.hasFDerivAt).differentiableAt

/-- Helper for Theorem 5.1.4: the one-dimensional slack slice
`σ(t) = β - f (x + t • h)` carries the derivative data needed for the logarithmic composition. -/
private theorem sublevel_slack_slice_data
    (hself : IsSelfConcordantOnWith dom Mf f) (β : ℝ) {x h : E} (hx : x ∈ dom) :
    let σ : ℝ → ℝ := fun t ↦ β - directionalSlice f x h t
    ContDiffAt ℝ 3 σ 0 ∧
      σ 0 = β - f x ∧
      deriv σ 0 = -inner ℝ (∇ f x) h ∧
      iteratedDeriv 2 σ 0 = -secondDirectionalDerivative f x h ∧
      iteratedDeriv 3 σ 0 = -thirdDirectionalDerivative f x h := by
  let σ : ℝ → ℝ := fun t ↦ β - directionalSlice f x h t
  have hfx3 : ContDiffAt ℝ 3 f x := hself.contDiffOn.contDiffAt (hself.isOpen_domain.mem_nhds hx)
  have hfx2 : ContDiffAt ℝ 2 f x := hfx3.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hdiff : DifferentiableAt ℝ f x := hfx3.differentiableAt (by norm_num)
  have hline3 : ContDiffAt ℝ 3 (fun t : ℝ ↦ x + t • h) 0 := by
    simpa using (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const) :
      ContDiffAt ℝ 3 (fun t : ℝ ↦ x + t • h) 0)
  have hslice3 : ContDiffAt ℝ 3 (directionalSlice f x h) 0 := by
    have hfx3' : ContDiffAt ℝ 3 f (x + (0 : ℝ) • h) := by
      simpa using hfx3
    simpa [directionalSlice] using hfx3'.comp 0 hline3
  have hσ3 : ContDiffAt ℝ 3 σ 0 := by
    simpa [σ] using contDiffAt_const.sub hslice3
  have hσ0 : σ 0 = β - f x := by
    simp [σ, directionalSlice]
  have hσ_deriv : deriv σ 0 = -inner ℝ (∇ f x) h := by
    -- Differentiate the slack slice once and rewrite the line derivative through the gradient.
    calc
      deriv σ 0 = -(deriv (directionalSlice f x h) 0) := by
        simpa [σ] using (deriv_const_sub (c := β) (f := directionalSlice f x h) (x := 0))
      _ = -(lineDeriv ℝ f x h) := by
        rfl
      _ = -(fderiv ℝ f x h) := by
        rw [hdiff.lineDeriv_eq_fderiv]
      _ = -inner ℝ (∇ f x) h := by
        rw [← inner_gradient_left (y := h) hdiff]
  have hσ_second : iteratedDeriv 2 σ 0 = -secondDirectionalDerivative f x h := by
    -- Only the outer subtraction contributes at second order.
    calc
      iteratedDeriv 2 σ 0 = iteratedDeriv 2 (-directionalSlice f x h) 0 := by
        simpa [σ] using (iteratedDeriv_const_sub (n := 2) (by norm_num) (c := β) (f := directionalSlice f x h) (x := 0))
      _ = -iteratedDeriv 2 (directionalSlice f x h) 0 := by
        simp
      _ = -secondDirectionalDerivative f x h := by
        rfl
  have hσ_third : iteratedDeriv 3 σ 0 = -thirdDirectionalDerivative f x h := by
    -- Only the outer subtraction contributes at third order as well.
    calc
      iteratedDeriv 3 σ 0 = iteratedDeriv 3 (-directionalSlice f x h) 0 := by
        simpa [σ] using (iteratedDeriv_const_sub (n := 3) (by norm_num) (c := β) (f := directionalSlice f x h) (x := 0))
      _ = -iteratedDeriv 3 (directionalSlice f x h) 0 := by
        simp
      _ = -thirdDirectionalDerivative f x h := by
        rfl
  exact ⟨hσ3, hσ0, hσ_deriv, hσ_second, hσ_third⟩

/-- Helper for Theorem 5.1.4: composing `-log` with a positive slack slice gives the expected
second iterated derivative at the base point. -/
private theorem negLog_comp_iteratedDeriv_two
    {σ : ℝ → ℝ} {s delta b : ℝ}
    (hσ3 : ContDiffAt ℝ 3 σ 0)
    (hσ0 : σ 0 = s)
    (hs : 0 < s)
    (hσ_deriv : deriv σ 0 = delta)
    (hσ_second : iteratedDeriv 2 σ 0 = -b) :
    iteratedDeriv 2 (fun a : ℝ ↦ -Real.log (σ a)) 0 =
      b / s + delta ^ (2 : ℕ) / s ^ (2 : ℕ) := by
  have hlog_cont : ContDiffAt ℝ 3 Real.log (σ 0) := by
    -- Positivity of the slack keeps `log` away from its singularity.
    simpa [hσ0] using (Real.contDiffAt_log.2 hs.ne')
  have hderiv_log : deriv Real.log = fun y : ℝ ↦ y⁻¹ := by
    -- Make the scalar logarithm derivative explicit before applying the chain rule.
    ext y
    rw [Real.deriv_log]
  have hsecond_log :
      iteratedDeriv 2 Real.log s = -(s ^ (2 : ℕ))⁻¹ := by
    -- The second derivative of `log` is the negative inverse square.
    calc
      iteratedDeriv 2 Real.log s = deriv (deriv Real.log) s := by
        simp [iteratedDeriv_succ]
      _ = deriv (fun y : ℝ ↦ y⁻¹) s := by
        rw [hderiv_log]
      _ = -(s ^ (2 : ℕ))⁻¹ := by
        rw [deriv_inv]
  have hcomp_two :
      iteratedDeriv 2 (fun a : ℝ ↦ Real.log (σ a)) 0 =
        iteratedDeriv 2 Real.log (σ 0) * deriv σ 0 ^ (2 : ℕ) +
          deriv Real.log (σ 0) * iteratedDeriv 2 σ 0 := by
    -- Apply the scalar second-order chain rule to `log ∘ σ`.
    simpa [Function.comp] using
      (iteratedDeriv_comp_two
        (g := Real.log)
        (f := σ)
        (x := 0)
        (hlog_cont.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
        (hσ3.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)))
  calc
    iteratedDeriv 2 (fun a : ℝ ↦ -Real.log (σ a)) 0
        = -iteratedDeriv 2 (fun a : ℝ ↦ Real.log (σ a)) 0 := by
            simp
    _ = -(iteratedDeriv 2 Real.log (σ 0) * deriv σ 0 ^ (2 : ℕ) +
            deriv Real.log (σ 0) * iteratedDeriv 2 σ 0) := by
          rw [hcomp_two]
    _ = -(-(s ^ (2 : ℕ))⁻¹ * delta ^ (2 : ℕ) + s⁻¹ * (-b)) := by
          rw [hσ0, hsecond_log, hderiv_log, hσ_deriv, hσ_second]
    _ = b / s + delta ^ (2 : ℕ) / s ^ (2 : ℕ) := by
          field_simp [hs.ne']
          ring

/-- Helper for Theorem 5.1.4: composing `-log` with a positive slack slice gives the expected
third iterated derivative at the base point. -/
private theorem negLog_comp_iteratedDeriv_three
    {σ : ℝ → ℝ} {s delta b c : ℝ}
    (hσ3 : ContDiffAt ℝ 3 σ 0)
    (hσ0 : σ 0 = s)
    (hs : 0 < s)
    (hσ_deriv : deriv σ 0 = delta)
    (hσ_second : iteratedDeriv 2 σ 0 = -b)
    (hσ_third : iteratedDeriv 3 σ 0 = -c) :
    iteratedDeriv 3 (fun a : ℝ ↦ -Real.log (σ a)) 0 =
      c / s - 3 * b * delta / s ^ (2 : ℕ) - 2 * delta ^ (3 : ℕ) / s ^ (3 : ℕ) := by
  have hlog_cont : ContDiffAt ℝ 3 Real.log (σ 0) := by
    -- Positivity of the slack keeps `log` away from its singularity.
    simpa [hσ0] using (Real.contDiffAt_log.2 hs.ne')
  have hderiv_log : deriv Real.log = fun y : ℝ ↦ y⁻¹ := by
    -- Make the scalar logarithm derivative explicit before applying the chain rule.
    ext y
    rw [Real.deriv_log]
  have hsecond_log :
      iteratedDeriv 2 Real.log s = -(s ^ (2 : ℕ))⁻¹ := by
    -- The second derivative of `log` is the negative inverse square.
    calc
      iteratedDeriv 2 Real.log s = deriv (deriv Real.log) s := by
        simp [iteratedDeriv_succ]
      _ = deriv (fun y : ℝ ↦ y⁻¹) s := by
        rw [hderiv_log]
      _ = -(s ^ (2 : ℕ))⁻¹ := by
        rw [deriv_inv]
  have hthird_log :
      iteratedDeriv 3 Real.log s = 2 * (s ^ (3 : ℕ))⁻¹ := by
    -- The third derivative of `log` is the positive inverse cube with coefficient `2`.
    calc
      iteratedDeriv 3 Real.log s = iteratedDeriv 2 (deriv Real.log) s := by
        simp [iteratedDeriv_succ']
      _ = iteratedDeriv 2 (fun y : ℝ ↦ y⁻¹) s := by
        rw [hderiv_log]
      _ = deriv^[2] Inv.inv s := by
        rw [iteratedDeriv_eq_iterate]
      _ = 2 * s ^ (-3 : ℤ) := by
        simpa using iter_deriv_inv 2 s
      _ = 2 * (s ^ (3 : ℕ))⁻¹ := by
        rw [zpow_neg]
        field_simp [hs.ne']
  have hcomp_three :
      iteratedDeriv 3 (fun a : ℝ ↦ Real.log (σ a)) 0 =
        iteratedDeriv 3 Real.log (σ 0) * deriv σ 0 ^ (3 : ℕ) +
          3 * iteratedDeriv 2 Real.log (σ 0) * iteratedDeriv 2 σ 0 * deriv σ 0 +
          deriv Real.log (σ 0) * iteratedDeriv 3 σ 0 := by
    -- Apply the scalar third-order chain rule to `log ∘ σ`.
    simpa [Function.comp] using
      (iteratedDeriv_comp_three
        (g := Real.log)
        (f := σ)
        (x := 0)
        hlog_cont
        hσ3)
  calc
    iteratedDeriv 3 (fun a : ℝ ↦ -Real.log (σ a)) 0
        = -iteratedDeriv 3 (fun a : ℝ ↦ Real.log (σ a)) 0 := by
            simp
    _ = -(iteratedDeriv 3 Real.log (σ 0) * deriv σ 0 ^ (3 : ℕ) +
            3 * iteratedDeriv 2 Real.log (σ 0) * iteratedDeriv 2 σ 0 * deriv σ 0 +
            deriv Real.log (σ 0) * iteratedDeriv 3 σ 0) := by
          rw [hcomp_three]
    _ = -(2 * (s ^ (3 : ℕ))⁻¹ * delta ^ (3 : ℕ) +
            3 * (-(s ^ (2 : ℕ))⁻¹) * (-b) * delta +
            s⁻¹ * (-c)) := by
          rw [hσ0, hthird_log, hsecond_log, hderiv_log, hσ_deriv, hσ_second, hσ_third]
    _ = c / s - 3 * b * delta / s ^ (2 : ℕ) - 2 * delta ^ (3 : ℕ) / s ^ (3 : ℕ) := by
          field_simp [hs.ne']
          ring

/-- Theorem 5.1.4 (2): at every point of the strict sublevel set `{x | f x < β}` inside the
domain of a self-concordant function, the Hessian quadratic form of `x ↦ -log (β - f x)`
dominates the square of the gradient pairing. -/
-- Proof sketch: `hself.contDiffOn` supplies the second-order regularity needed to differentiate
-- `τ ↦ -log (β - f (x + τ • h))` twice, while `hself.hessian_isPositive hx` makes the Hessian
-- contribution nonnegative.
theorem sublevelLogBarrier_hessian_quadraticForm_ge_gradient_sq
    (hself : IsSelfConcordantOnWith dom Mf f) (β : ℝ) {x h : E}
    (hx : x ∈ dom) (hβ : f x < β) :
    inner ℝ h (hessian (sublevelLogBarrier f β) x h) ≥
      (inner ℝ (∇ (sublevelLogBarrier f β) x) h) ^ (2 : ℕ) := by
  let σ : ℝ → ℝ := fun t ↦ β - directionalSlice f x h t
  have hσ :
      ContDiffAt ℝ 3 σ 0 ∧
        σ 0 = β - f x ∧
        deriv σ 0 = -inner ℝ (∇ f x) h ∧
        iteratedDeriv 2 σ 0 = -secondDirectionalDerivative f x h ∧
        iteratedDeriv 3 σ 0 = -thirdDirectionalDerivative f x h :=
    sublevel_slack_slice_data hself β hx
  rcases hσ with ⟨hσ3, hσ0, hσ_deriv, hσ_second, _hσ_third⟩
  have hs : 0 < σ 0 := by
    -- The strict sublevel condition is exactly the positivity of the slack at the basepoint.
    rw [hσ0]
    exact sublevelLogBarrier_arg_pos_of_mem_domain f β hβ
  have hfx3 : ContDiffAt ℝ 3 f x := hself.contDiffOn.contDiffAt (hself.isOpen_domain.mem_nhds hx)
  have hfx2 : ContDiffAt ℝ 2 f x := hfx3.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hdiff : DifferentiableAt ℝ f x := hfx3.differentiableAt (by norm_num)
  have hgrad : DifferentiableAt ℝ (∇ f) x := differentiableAt_gradient_of_contDiffAt_two hfx2
  have hbarrier2 : ContDiffAt ℝ 2 (sublevelLogBarrier f β) x := by
    -- Compose the positive slack with `-log` on the ambient space.
    have hslack2 : ContDiffAt ℝ 2 (fun y : E ↦ β - f y) x := by
      simpa using contDiffAt_const.sub hfx2
    have hlog2 : ContDiffAt ℝ 2 (fun s : ℝ ↦ -Real.log s) (β - f x) := by
      have hsx : 0 < β - f x := sublevelLogBarrier_arg_pos_of_mem_domain f β hβ
      simpa using (Real.contDiffAt_log.2 hsx.ne').neg
    simpa [sublevelLogBarrier] using hlog2.comp x hslack2
  have hbarrier_diff : DifferentiableAt ℝ (sublevelLogBarrier f β) x :=
    hbarrier2.differentiableAt (by norm_num)
  have hbarrier_grad : DifferentiableAt ℝ (∇ (sublevelLogBarrier f β)) x :=
    differentiableAt_gradient_of_contDiffAt_two hbarrier2
  have hbarrier_slice_deriv :
      deriv (directionalSlice (sublevelLogBarrier f β) x h) 0 =
        inner ℝ (∇ (sublevelLogBarrier f β) x) h := by
    -- Rewrite the slice derivative through the ambient Fréchet derivative and the gradient.
    calc
      deriv (directionalSlice (sublevelLogBarrier f β) x h) 0
          = lineDeriv ℝ (sublevelLogBarrier f β) x h := by
              rfl
      _ = fderiv ℝ (sublevelLogBarrier f β) x h := by
            rw [hbarrier_diff.lineDeriv_eq_fderiv]
      _ = inner ℝ (∇ (sublevelLogBarrier f β) x) h := by
            rw [← inner_gradient_left (y := h) hbarrier_diff]
  have hbarrier_second :
      secondDirectionalDerivative (sublevelLogBarrier f β) x h =
        secondDirectionalDerivative f x h / (β - f x) +
          (-inner ℝ (∇ f x) h) ^ (2 : ℕ) / (β - f x) ^ (2 : ℕ) := by
    -- Compute the second derivative of `-log ∘ σ` by the scalar chain rule.
    have hslice_eq :
        directionalSlice (sublevelLogBarrier f β) x h = fun a : ℝ ↦ -Real.log (σ a) := by
      funext a
      simp [σ, sublevelLogBarrier, directionalSlice]
    calc
      secondDirectionalDerivative (sublevelLogBarrier f β) x h
          = iteratedDeriv 2 (fun a : ℝ ↦ -Real.log (σ a)) 0 := by
              rw [secondDirectionalDerivative, hslice_eq]
      _ = secondDirectionalDerivative f x h / (β - f x) +
            (-inner ℝ (∇ f x) h) ^ (2 : ℕ) / (β - f x) ^ (2 : ℕ) := by
              simpa [hσ0] using
                negLog_comp_iteratedDeriv_two
                  (s := β - f x) hσ3 hσ0 (by simpa [hσ0] using hs) hσ_deriv hσ_second
  have hsecond_eq :
      secondDirectionalDerivative f x h = inner ℝ h (hessian f x h) := by
    exact secondDirectionalDerivative_eq_hessian_quadratic_form hfx2
  have hbarrier_second_eq :
      secondDirectionalDerivative (sublevelLogBarrier f β) x h =
        inner ℝ h (hessian (sublevelLogBarrier f β) x h) := by
    exact secondDirectionalDerivative_eq_hessian_quadratic_form hbarrier2
  have hslack_nonneg :
      0 ≤ inner ℝ h (hessian f x h) / (β - f x) := by
    -- The original self-concordant Hessian is positive semidefinite on the domain.
    have hquad : 0 ≤ inner ℝ h (hessian f x h) := hself.hessian_posSemidef hx h
    have hsx : 0 < β - f x := sublevelLogBarrier_arg_pos_of_mem_domain f β hβ
    exact div_nonneg hquad (le_of_lt hsx)
  have hgrad_sq :
      (inner ℝ (∇ (sublevelLogBarrier f β) x) h) ^ (2 : ℕ) =
        (-inner ℝ (∇ f x) h) ^ (2 : ℕ) / (β - f x) ^ (2 : ℕ) := by
    -- Identify the barrier gradient pairing with the first derivative of the barrier slice.
    have hσ_hasDeriv : HasDerivAt σ (deriv σ 0) 0 := by
      exact (hσ3.differentiableAt (by norm_num)).hasDerivAt
    have hlog_hasDeriv :
        HasDerivAt Real.log ((σ 0)⁻¹) (σ 0) := by
      simpa using Real.hasDerivAt_log hs.ne'
    have hcomp_deriv :
        deriv (fun a : ℝ ↦ -Real.log (σ a)) 0 = -((σ 0)⁻¹ * deriv σ 0) := by
      have hcomp_log :
          deriv (fun a : ℝ ↦ Real.log (σ a)) 0 = (σ 0)⁻¹ * deriv σ 0 := by
        simpa [Function.comp] using (hlog_hasDeriv.comp 0 hσ_hasDeriv).deriv
      calc
        deriv (fun a : ℝ ↦ -Real.log (σ a)) 0
            = -deriv (fun a : ℝ ↦ Real.log (σ a)) 0 := by
                simpa using (deriv.neg (f := fun a : ℝ ↦ Real.log (σ a)) (x := 0))
        _ = -((σ 0)⁻¹ * deriv σ 0) := by
              rw [hcomp_log]
    have hslice_eq :
        directionalSlice (sublevelLogBarrier f β) x h = fun a : ℝ ↦ -Real.log (σ a) := by
      funext a
      simp [σ, sublevelLogBarrier, directionalSlice]
    calc
      (inner ℝ (∇ (sublevelLogBarrier f β) x) h) ^ (2 : ℕ)
          = (deriv (directionalSlice (sublevelLogBarrier f β) x h) 0) ^ (2 : ℕ) := by
              rw [hbarrier_slice_deriv]
      _ = (deriv (fun a : ℝ ↦ -Real.log (σ a)) 0) ^ (2 : ℕ) := by
            rw [hslice_eq]
      _ = (-((σ 0)⁻¹ * deriv σ 0)) ^ (2 : ℕ) := by
            rw [hcomp_deriv]
      _ = (-inner ℝ (∇ f x) h) ^ (2 : ℕ) / (β - f x) ^ (2 : ℕ) := by
            rw [hσ0, hσ_deriv]
            field_simp [hs.ne']
  calc
    inner ℝ h (hessian (sublevelLogBarrier f β) x h)
        = secondDirectionalDerivative (sublevelLogBarrier f β) x h := by
            rw [← hbarrier_second_eq]
    _ = inner ℝ h (hessian f x h) / (β - f x) +
          (-inner ℝ (∇ f x) h) ^ (2 : ℕ) / (β - f x) ^ (2 : ℕ) := by
            rw [hbarrier_second, hsecond_eq]
    _ ≥ (-inner ℝ (∇ f x) h) ^ (2 : ℕ) / (β - f x) ^ (2 : ℕ) := by
          linarith
    _ = (inner ℝ (∇ (sublevelLogBarrier f β) x) h) ^ (2 : ℕ) := by
          rw [← hgrad_sq]

/-- Theorem 5.1.4 (2), owner-level bridge: for a self-concordant input, the square of the
gradient pairing of `x ↦ -log (β - f x)` is bounded by the square of the canonical Hessian local
norm. -/
theorem sublevelLogBarrier_gradient_inner_sq_le
    (hself : IsSelfConcordantOnWith dom Mf f) (β : ℝ) {x h : E}
    (hx : x ∈ dom) (hβ : f x < β) :
    (inner ℝ (∇ (sublevelLogBarrier f β) x) h) ^ (2 : ℕ) ≤
      ‖h‖[sublevelLogBarrier f β; x] ^ (2 : ℕ) := by
  -- Rewrite the squared local norm as the barrier Hessian quadratic form.
  have hquad :
      inner ℝ h (hessian (sublevelLogBarrier f β) x h) ≥
        (inner ℝ (∇ (sublevelLogBarrier f β) x) h) ^ (2 : ℕ) :=
    hself.sublevelLogBarrier_hessian_quadraticForm_ge_gradient_sq β hx hβ
  have hnonneg : 0 ≤ inner ℝ h (hessian (sublevelLogBarrier f β) x h) := by
    have hsq_nonneg :
        0 ≤ (inner ℝ (∇ (sublevelLogBarrier f β) x) h) ^ (2 : ℕ) := by
      positivity
    exact le_trans hsq_nonneg hquad
  have hsq :
      ‖h‖[sublevelLogBarrier f β; x] ^ (2 : ℕ) =
        inner ℝ h (hessian (sublevelLogBarrier f β) x h) := by
    -- Square the canonical local norm representation.
    rw [hessianLocalNorm_def]
    simpa using Real.sq_sqrt hnonneg
  rw [hsq]
  exact hquad

/-- Helper for Theorem 5.1.4: the squared local norm of the sublevel barrier is the normalized
sum of the source Hessian term and the squared normalized gradient pairing. -/
theorem sublevel_barrier_local_norm_sq
    (hself : IsSelfConcordantOnWith dom Mf f) (β : ℝ) {x u : E}
    (hx : x ∈ dom) (hβ : f x < β) :
    ‖u‖[sublevelLogBarrier f β; x] ^ (2 : ℕ) =
      secondDirectionalDerivative f x u / (β - f x) +
        (inner ℝ (∇ f x) u) ^ (2 : ℕ) / (β - f x) ^ (2 : ℕ) := by
  let σ : ℝ → ℝ := fun t ↦ β - directionalSlice f x u t
  have hσ :
      ContDiffAt ℝ 3 σ 0 ∧
        σ 0 = β - f x ∧
        deriv σ 0 = -inner ℝ (∇ f x) u ∧
        iteratedDeriv 2 σ 0 = -secondDirectionalDerivative f x u ∧
        iteratedDeriv 3 σ 0 = -thirdDirectionalDerivative f x u :=
    sublevel_slack_slice_data hself β hx
  rcases hσ with ⟨hσ3, hσ0, hσ_deriv, hσ_second, _hσ_third⟩
  have hs : 0 < σ 0 := by
    -- The strict sublevel condition is exactly the positivity of the barrier slack.
    rw [hσ0]
    exact sublevelLogBarrier_arg_pos_of_mem_domain f β hβ
  have hfx3 : ContDiffAt ℝ 3 f x := hself.contDiffOn.contDiffAt (hself.isOpen_domain.mem_nhds hx)
  have hfx2 : ContDiffAt ℝ 2 f x := hfx3.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hbarrier2 : ContDiffAt ℝ 2 (sublevelLogBarrier f β) x := by
    -- Compose the positive slack with `-log` on the ambient space.
    have hslack2 : ContDiffAt ℝ 2 (fun y : E ↦ β - f y) x := by
      simpa using contDiffAt_const.sub hfx2
    have hlog2 : ContDiffAt ℝ 2 (fun s : ℝ ↦ -Real.log s) (β - f x) := by
      have hsx : 0 < β - f x := sublevelLogBarrier_arg_pos_of_mem_domain f β hβ
      simpa using (Real.contDiffAt_log.2 hsx.ne').neg
    simpa [sublevelLogBarrier] using hlog2.comp x hslack2
  have hbarrier_diff : DifferentiableAt ℝ (sublevelLogBarrier f β) x :=
    hbarrier2.differentiableAt (by norm_num)
  have hbarrier_grad : DifferentiableAt ℝ (∇ (sublevelLogBarrier f β)) x :=
    differentiableAt_gradient_of_contDiffAt_two hbarrier2
  have hbarrier_second :
      secondDirectionalDerivative (sublevelLogBarrier f β) x u =
        secondDirectionalDerivative f x u / (β - f x) +
          (-inner ℝ (∇ f x) u) ^ (2 : ℕ) / (β - f x) ^ (2 : ℕ) := by
    have hslice_eq :
        directionalSlice (sublevelLogBarrier f β) x u = fun a : ℝ ↦ -Real.log (σ a) := by
      funext a
      simp [σ, sublevelLogBarrier, directionalSlice]
    -- The second-order chain rule gives the normalized Hessian formula.
    calc
      secondDirectionalDerivative (sublevelLogBarrier f β) x u
          = iteratedDeriv 2 (fun a : ℝ ↦ -Real.log (σ a)) 0 := by
              rw [secondDirectionalDerivative, hslice_eq]
      _ = secondDirectionalDerivative f x u / (β - f x) +
            (-inner ℝ (∇ f x) u) ^ (2 : ℕ) / (β - f x) ^ (2 : ℕ) := by
            simpa [hσ0] using
              negLog_comp_iteratedDeriv_two
                (s := β - f x) hσ3 hσ0 (by simpa [hσ0] using hs) hσ_deriv hσ_second
  have hbarrier_second_eq :
      secondDirectionalDerivative (sublevelLogBarrier f β) x u =
        inner ℝ u (hessian (sublevelLogBarrier f β) x u) := by
    exact secondDirectionalDerivative_eq_hessian_quadratic_form hbarrier2
  have hbarrier_quad_nonneg :
      0 ≤ inner ℝ u (hessian (sublevelLogBarrier f β) x u) := by
    -- Clause (2) already implies barrier Hessian positivity on the strict sublevel set.
    have hineq :
        inner ℝ u (hessian (sublevelLogBarrier f β) x u) ≥
          (inner ℝ (∇ (sublevelLogBarrier f β) x) u) ^ (2 : ℕ) := by
      exact hself.sublevelLogBarrier_hessian_quadraticForm_ge_gradient_sq β hx hβ
    have hsq_nonneg :
        0 ≤ (inner ℝ (∇ (sublevelLogBarrier f β) x) u) ^ (2 : ℕ) := by
      positivity
    exact le_trans hsq_nonneg hineq
  -- Rewrite the local norm through the barrier Hessian, then simplify the square term.
  calc
    ‖u‖[sublevelLogBarrier f β; x] ^ (2 : ℕ)
        = inner ℝ u (hessian (sublevelLogBarrier f β) x u) := by
            rw [hessianLocalNorm_def]
            simpa using Real.sq_sqrt hbarrier_quad_nonneg
    _ = secondDirectionalDerivative (sublevelLogBarrier f β) x u := by
          rw [← hbarrier_second_eq]
    _ = secondDirectionalDerivative f x u / (β - f x) +
          (-inner ℝ (∇ f x) u) ^ (2 : ℕ) / (β - f x) ^ (2 : ℕ) := by
          rw [hbarrier_second]
    _ = secondDirectionalDerivative f x u / (β - f x) +
          (inner ℝ (∇ f x) u) ^ (2 : ℕ) / (β - f x) ^ (2 : ℕ) := by
          ring

/-- Helper for Theorem 5.1.4: the third directional derivative of the sublevel barrier is the
normalized cubic combination of the source gradient, Hessian, and third derivative data. -/
theorem sublevel_barrier_third_deriv_formula
    (hself : IsSelfConcordantOnWith dom Mf f) (β : ℝ) {x u : E}
    (hx : x ∈ dom) (hβ : f x < β) :
    thirdDirectionalDerivative (sublevelLogBarrier f β) x u =
      thirdDirectionalDerivative f x u / (β - f x) +
        3 * (inner ℝ (∇ f x) u / (β - f x)) *
          (secondDirectionalDerivative f x u / (β - f x)) +
        2 * (inner ℝ (∇ f x) u / (β - f x)) ^ (3 : ℕ) := by
  let σ : ℝ → ℝ := fun t ↦ β - directionalSlice f x u t
  have hσ :
      ContDiffAt ℝ 3 σ 0 ∧
        σ 0 = β - f x ∧
        deriv σ 0 = -inner ℝ (∇ f x) u ∧
        iteratedDeriv 2 σ 0 = -secondDirectionalDerivative f x u ∧
        iteratedDeriv 3 σ 0 = -thirdDirectionalDerivative f x u :=
    sublevel_slack_slice_data hself β hx
  rcases hσ with ⟨hσ3, hσ0, hσ_deriv, hσ_second, hσ_third⟩
  have hs : 0 < σ 0 := by
    -- The strict sublevel condition is exactly the positivity of the barrier slack.
    rw [hσ0]
    exact sublevelLogBarrier_arg_pos_of_mem_domain f β hβ
  have hslice_eq :
      directionalSlice (sublevelLogBarrier f β) x u = fun a : ℝ ↦ -Real.log (σ a) := by
    funext a
    simp [σ, sublevelLogBarrier, directionalSlice]
  -- The third-order chain rule yields the normalized cubic barrier expression.
  calc
    thirdDirectionalDerivative (sublevelLogBarrier f β) x u
        = iteratedDeriv 3 (fun a : ℝ ↦ -Real.log (σ a)) 0 := by
            rw [thirdDirectionalDerivative, hslice_eq]
    _ = thirdDirectionalDerivative f x u / (β - f x) -
          3 * secondDirectionalDerivative f x u * (-inner ℝ (∇ f x) u) /
            (β - f x) ^ (2 : ℕ) -
          2 * (-inner ℝ (∇ f x) u) ^ (3 : ℕ) / (β - f x) ^ (3 : ℕ) := by
          simpa [hσ0] using
            negLog_comp_iteratedDeriv_three
              (s := β - f x)
              hσ3
              hσ0
              (by simpa [hσ0] using hs)
              hσ_deriv
              hσ_second
              hσ_third
    _ = thirdDirectionalDerivative f x u / (β - f x) +
          3 * (inner ℝ (∇ f x) u / (β - f x)) *
            (secondDirectionalDerivative f x u / (β - f x)) +
          2 * (inner ℝ (∇ f x) u / (β - f x)) ^ (3 : ℕ) := by
          field_simp [hs.ne']
          ring

/-- Helper for Theorem 5.1.4: dividing the source self-concordance bound by the positive slack
controls the normalized third derivative by the normalized curvature term. -/
theorem sublevel_barrier_remainder_bound
    (hself : IsSelfConcordantOnWith dom Mf f) (β : ℝ) {x u : E}
    (hx : x ∈ dom) (hβ : f x < β) :
    |thirdDirectionalDerivative f x u / (β - f x)| ≤
      2 * ((Mf : ℝ) * Real.sqrt (β - f x)) *
        (Real.sqrt (secondDirectionalDerivative f x u / (β - f x))) ^ (3 : ℕ) := by
  have hs : 0 < β - f x := sublevelLogBarrier_arg_pos_of_mem_domain f β hβ
  have hfx3 : ContDiffAt ℝ 3 f x := hself.contDiffOn.contDiffAt (hself.isOpen_domain.mem_nhds hx)
  have hfx2 : ContDiffAt ℝ 2 f x := hfx3.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hdiff : DifferentiableAt ℝ f x := hfx3.differentiableAt (by norm_num)
  have hgrad : DifferentiableAt ℝ (∇ f) x := differentiableAt_gradient_of_contDiffAt_two hfx2
  have hsecond_eq :
      secondDirectionalDerivative f x u = inner ℝ u (hessian f x u) := by
    exact secondDirectionalDerivative_eq_hessian_quadratic_form hfx2
  have hsecond_nonneg : 0 ≤ secondDirectionalDerivative f x u := by
    rw [hsecond_eq]
    exact hself.hessian_posSemidef hx u
  have hnorm_eq :
      ‖u‖[f; x] = Real.sqrt (secondDirectionalDerivative f x u) := by
    rw [hessianLocalNorm_def, hsecond_eq]
  -- Divide the source cubic bound by the positive slack and rewrite the local norm.
  calc
    |thirdDirectionalDerivative f x u / (β - f x)|
        = |thirdDirectionalDerivative f x u| / (β - f x) := by
            rw [abs_div, abs_of_pos hs]
    _ ≤ 2 * (Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ) / (β - f x) := by
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
            (div_le_div_of_nonneg_right (hself.third_deriv_bound hx u) hs.le)
    _ = 2 * (Mf : ℝ) * Real.sqrt (β - f x) *
          (Real.sqrt (secondDirectionalDerivative f x u / (β - f x))) ^ (3 : ℕ) := by
          rw [hnorm_eq, Real.sqrt_div hsecond_nonneg (β - f x)]
          have hsqrt_ne : Real.sqrt (β - f x) ≠ 0 := Real.sqrt_ne_zero'.2 hs
          field_simp [hsqrt_ne]
          rw [Real.sq_sqrt hs.le]
    _ = 2 * ((Mf : ℝ) * Real.sqrt (β - f x)) *
          (Real.sqrt (secondDirectionalDerivative f x u / (β - f x))) ^ (3 : ℕ) := by
          ring

end IsSelfConcordantOnWith

/-- Helper for Theorem 5.1.4: the barrier cubic core and the curvature cube fit into the exact
square estimate required by the normalized slack argument. -/
private theorem normalized_cubic_core_sq_le
    {ω1 ω2 : ℝ} (_hω2 : 0 ≤ ω2) :
    (2 * ω1 ^ (3 : ℕ) + 3 * ω1 * ω2) ^ (2 : ℕ) + 4 * ω2 ^ (3 : ℕ) ≤
      4 * (ω1 ^ (2 : ℕ) + ω2) ^ (3 : ℕ) := by
  have hpoly :
      4 * (ω1 ^ (2 : ℕ) + ω2) ^ (3 : ℕ) -
        ((2 * ω1 ^ (3 : ℕ) + 3 * ω1 * ω2) ^ (2 : ℕ) + 4 * ω2 ^ (3 : ℕ)) =
      3 * ω1 ^ (2 : ℕ) * ω2 ^ (2 : ℕ) := by
    ring
  have hnonneg : 0 ≤ 3 * ω1 ^ (2 : ℕ) * ω2 ^ (2 : ℕ) := by
    positivity
  -- The gap is the visibly nonnegative polynomial `3 ω₁² ω₂²`.
  nlinarith [hpoly]

/-- Helper for Theorem 5.1.4: a square-sum bound and a weighted control on `z` give the sharp
`sqrt (1 + λ²)` estimate for `|a + z|`. -/
private theorem abs_add_le_sqrt_mul_of_sq_add_sq_le
    {a b c lam z : ℝ}
    (hlam : 0 ≤ lam) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hsq : a ^ (2 : ℕ) + b ^ (2 : ℕ) ≤ c ^ (2 : ℕ))
    (hz : |z| ≤ lam * b) :
    |a + z| ≤ Real.sqrt (1 + lam ^ (2 : ℕ)) * c := by
  have habs_sq : |a| ^ (2 : ℕ) = a ^ (2 : ℕ) := by
    simpa using (sq_abs a)
  have hcross :
      2 * lam * |a| * b ≤ lam ^ (2 : ℕ) * a ^ (2 : ℕ) + b ^ (2 : ℕ) := by
    simpa [pow_two, sq_abs, mul_assoc, mul_left_comm, mul_comm] using
      (two_mul_le_add_sq (lam * |a|) b)
  have htri : |a + z| ≤ |a| + lam * b := by
    -- First separate `z` by the triangle inequality, then insert the weighted hypothesis.
    calc
      |a + z| ≤ |a| + |z| := abs_add_le _ _
      _ ≤ |a| + lam * b := by
            simpa using add_le_add_left hz |a|
  have hsum_sq :
      (|a| + lam * b) ^ (2 : ℕ) ≤ (1 + lam ^ (2 : ℕ)) * (a ^ (2 : ℕ) + b ^ (2 : ℕ)) := by
    -- This is the two-dimensional Cauchy estimate after expanding the cross term.
    nlinarith [habs_sq, hcross]
  have hfactor_nonneg : 0 ≤ 1 + lam ^ (2 : ℕ) := by
    positivity
  have hsum_bound :
      (|a| + lam * b) ^ (2 : ℕ) ≤ (1 + lam ^ (2 : ℕ)) * c ^ (2 : ℕ) := by
    exact le_trans hsum_sq (mul_le_mul_of_nonneg_left hsq hfactor_nonneg)
  have hright_sq :
      (Real.sqrt (1 + lam ^ (2 : ℕ)) * c) ^ (2 : ℕ) = (1 + lam ^ (2 : ℕ)) * c ^ (2 : ℕ) := by
    rw [show (Real.sqrt (1 + lam ^ (2 : ℕ)) * c) ^ (2 : ℕ) =
          (Real.sqrt (1 + lam ^ (2 : ℕ))) ^ (2 : ℕ) * c ^ (2 : ℕ) by ring]
    rw [Real.sq_sqrt hfactor_nonneg]
  have htri_rhs_nonneg : 0 ≤ |a| + lam * b := by
    positivity
  have htri_sq :
      |a + z| ^ (2 : ℕ) ≤ (|a| + lam * b) ^ (2 : ℕ) := by
    nlinarith [abs_nonneg (a + z), htri_rhs_nonneg, htri]
  have hsq_bound :
      |a + z| ^ (2 : ℕ) ≤ (Real.sqrt (1 + lam ^ (2 : ℕ)) * c) ^ (2 : ℕ) := by
    exact le_trans htri_sq (by simpa [hright_sq] using hsum_bound)
  have hright_nonneg : 0 ≤ Real.sqrt (1 + lam ^ (2 : ℕ)) * c := by
    positivity
  -- Compare nonnegative square roots to recover the original absolute-value bound.
  nlinarith [abs_nonneg (a + z), hright_nonneg, hsq_bound]

/-- Helper for Theorem 5.1.4: the normalized cubic core and the normalized source remainder merge
into the final barrier cubic estimate with coefficient `sqrt (1 + λ²)`. -/
private theorem sublevel_cubic_merge_bound
    {ω1 ω2 z lam : ℝ}
    (hω2 : 0 ≤ ω2) (hlam : 0 ≤ lam)
    (hz : |z| ≤ 2 * lam * (Real.sqrt ω2) ^ (3 : ℕ)) :
    |2 * ω1 ^ (3 : ℕ) + 3 * ω1 * ω2 + z| ≤
      2 * Real.sqrt (1 + lam ^ (2 : ℕ)) * (Real.sqrt (ω1 ^ (2 : ℕ) + ω2)) ^ (3 : ℕ) := by
  let a : ℝ := 2 * ω1 ^ (3 : ℕ) + 3 * ω1 * ω2
  let b : ℝ := 2 * (Real.sqrt ω2) ^ (3 : ℕ)
  let c : ℝ := 2 * (Real.sqrt (ω1 ^ (2 : ℕ) + ω2)) ^ (3 : ℕ)
  have hω_total_nonneg : 0 ≤ ω1 ^ (2 : ℕ) + ω2 := by
    nlinarith [sq_nonneg ω1, hω2]
  have hb_nonneg : 0 ≤ b := by
    dsimp [b]
    positivity
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hz' : |z| ≤ lam * b := by
    simpa [b, mul_assoc, mul_left_comm, mul_comm] using hz
  have hsq :
      a ^ (2 : ℕ) + b ^ (2 : ℕ) ≤ c ^ (2 : ℕ) := by
    have hb_sq :
        b ^ (2 : ℕ) = 4 * ω2 ^ (3 : ℕ) := by
      dsimp [b]
      calc
        (2 * (Real.sqrt ω2) ^ (3 : ℕ)) ^ (2 : ℕ)
            = 4 * ((Real.sqrt ω2) ^ (2 : ℕ)) ^ (3 : ℕ) := by
                ring
        _ = 4 * ω2 ^ (3 : ℕ) := by
              rw [Real.sq_sqrt hω2]
    have hc_sq :
        c ^ (2 : ℕ) = 4 * (ω1 ^ (2 : ℕ) + ω2) ^ (3 : ℕ) := by
      dsimp [c]
      calc
        (2 * (Real.sqrt (ω1 ^ (2 : ℕ) + ω2)) ^ (3 : ℕ)) ^ (2 : ℕ)
            = 4 * ((Real.sqrt (ω1 ^ (2 : ℕ) + ω2)) ^ (2 : ℕ)) ^ (3 : ℕ) := by
                ring
        _ = 4 * (ω1 ^ (2 : ℕ) + ω2) ^ (3 : ℕ) := by
              rw [Real.sq_sqrt hω_total_nonneg]
    dsimp [a]
    rw [hb_sq, hc_sq]
    exact normalized_cubic_core_sq_le hω2
  have hmerge :=
    abs_add_le_sqrt_mul_of_sq_add_sq_le
      (a := a) (b := b) (c := c) (lam := lam) (z := z) hlam hb_nonneg hc_nonneg hsq hz'
  -- Feed the exact square estimate into the Cauchy adapter and then unfold the normalizations.
  simpa [a, c, mul_assoc, mul_left_comm, mul_comm] using hmerge

/-- Theorem 5.1.4 (3): if `f` is bounded below on `dom` by `f*`, then the barrier
`x ↦ -log (β - f x)` is self-concordant on `{x ∈ dom | f x < β}` with constant
`sqrt (1 + M_f^2 * (β - f*))`. -/
-- Proof sketch: compute the third directional derivative of `x ↦ -log (β - f x)` and rewrite it
-- in terms of the Hessian quadratic form and gradient pairing of `f`. Use the self-concordance
-- inequality for `f`, the quadratic-form lower bound from the previous clause applied to the
-- pointwise Hessian-positivity owner furnished by `hself.hessian_isPositive hx`, and the estimate
-- `β - f x ≤ β - f*` coming from the lower bound hypothesis to obtain the stated constant; when
-- `β ≤ f*`, the strict sublevel domain is empty, so the same statement remains valid without a
-- separate positivity hypothesis on `β - f*`.
theorem sublevelLogBarrier_isSelfConcordantOnWith
    (hself : IsSelfConcordantOnWith dom Mf f) (β fStar : ℝ)
    (h_lower : ∀ ⦃x : E⦄, x ∈ dom → fStar ≤ f x) :
    IsSelfConcordantOnWith
      {x : E | x ∈ dom ∧ f x < β}
      (NNReal.sqrt (1 + Mf ^ (2 : ℕ) * Real.toNNReal (β - fStar)))
      (sublevelLogBarrier f β) := by
  -- Route correction: the open-domain, `C³`, and convexity fields follow directly from the
  -- strict-sublevel slack and clause (2); the remaining blocker is the cubic merge estimate for
  -- the third derivative.
  refine
    { isOpen_domain := ?_
      contDiffOn := ?_
      convexOn := ?_
      third_deriv_bound := ?_ }
  · -- The strict sublevel set is the intersection of the open domain with the open slack set.
    have hcont : ContinuousOn f dom := hself.contDiffOn.continuousOn
    have hopen_lt : IsOpen {x : E | x ∈ dom ∧ f x < β} := by
      simpa [Set.setOf_and] using
        hcont.isOpen_inter_preimage hself.isOpen_domain isOpen_Iio
    exact hopen_lt
  · intro x hx
    rcases hx with ⟨hx_dom, hxβ⟩
    -- Compose the positive slack with `-log` on the domain.
    have hfx3 : ContDiffAt ℝ 3 f x := hself.contDiffOn.contDiffAt (hself.isOpen_domain.mem_nhds hx_dom)
    have hslack3 : ContDiffAt ℝ 3 (fun y : E ↦ β - f y) x := by
      simpa using contDiffAt_const.sub hfx3
    have hlog3 : ContDiffAt ℝ 3 (fun s : ℝ ↦ -Real.log s) (β - f x) := by
      have hsx : 0 < β - f x := sublevelLogBarrier_arg_pos_of_mem_domain f β hxβ
      simpa using (Real.contDiffAt_log.2 hsx.ne').neg
    have hbarrier3 : ContDiffAt ℝ 3 (sublevelLogBarrier f β) x := by
      simpa [sublevelLogBarrier] using hlog3.comp x hslack3
    exact hbarrier3.contDiffWithinAt
  · -- Use the Hessian positivity criterion on the strict sublevel domain.
    have hC2 : ContDiffOn ℝ 2 (sublevelLogBarrier f β) {x : E | x ∈ dom ∧ f x < β} := by
      intro x hx
      rcases hx with ⟨hx_dom, hxβ⟩
      have hfx2 : ContDiffAt ℝ 2 f x :=
        (hself.contDiffOn.contDiffAt (hself.isOpen_domain.mem_nhds hx_dom)).of_le
          (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
      have hslack2 : ContDiffAt ℝ 2 (fun y : E ↦ β - f y) x := by
        simpa using contDiffAt_const.sub hfx2
      have hlog2 : ContDiffAt ℝ 2 (fun s : ℝ ↦ -Real.log s) (β - f x) := by
        have hsx : 0 < β - f x := sublevelLogBarrier_arg_pos_of_mem_domain f β hxβ
        simpa using (Real.contDiffAt_log.2 hsx.ne').neg
      have hbarrier2 : ContDiffAt ℝ 2 (sublevelLogBarrier f β) x := by
        simpa [sublevelLogBarrier] using hlog2.comp x hslack2
      exact hbarrier2.contDiffWithinAt
    apply
      (convexOn_iff_hessian_quadratic_form_nonneg
        (by
          have hcont : ContinuousOn f dom := hself.contDiffOn.continuousOn
          simpa [Set.setOf_and] using
            hcont.isOpen_inter_preimage hself.isOpen_domain isOpen_Iio)
        (hself.convexOn.convex_lt β)
        hC2).2
    intro x hx h
    have hineq :
        inner ℝ h (hessian (sublevelLogBarrier f β) x h) ≥
          (inner ℝ (∇ (sublevelLogBarrier f β) x) h) ^ (2 : ℕ) := by
      exact hself.sublevelLogBarrier_hessian_quadraticForm_ge_gradient_sq β hx.1 hx.2
    have hsq_nonneg :
        0 ≤ (inner ℝ (∇ (sublevelLogBarrier f β) x) h) ^ (2 : ℕ) := by
      positivity
    rw [real_inner_comm]
    exact le_trans hsq_nonneg hineq
  · intro x hx u
    let s : ℝ := β - f x
    let ω1 : ℝ := inner ℝ (∇ f x) u / s
    let ω2 : ℝ := secondDirectionalDerivative f x u / s
    let z : ℝ := thirdDirectionalDerivative f x u / s
    let lam : ℝ := (Mf : ℝ) * Real.sqrt s
    have hs : 0 < s := by
      -- The strict sublevel condition is exactly the positivity of the barrier slack.
      dsimp [s]
      exact sublevelLogBarrier_arg_pos_of_mem_domain f β hx.2
    have hω2_nonneg : 0 ≤ ω2 := by
      -- The source Hessian is positive semidefinite on the original domain.
      have hfx3 : ContDiffAt ℝ 3 f x := hself.contDiffOn.contDiffAt (hself.isOpen_domain.mem_nhds hx.1)
      have hfx2 : ContDiffAt ℝ 2 f x := hfx3.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
      have hdiff : DifferentiableAt ℝ f x := hfx3.differentiableAt (by norm_num)
      have hgrad : DifferentiableAt ℝ (∇ f) x :=
        IsSelfConcordantOnWith.differentiableAt_gradient_of_contDiffAt_two hfx2
      have hsecond_eq :
          secondDirectionalDerivative f x u = inner ℝ u (hessian f x u) := by
        exact secondDirectionalDerivative_eq_hessian_quadratic_form hfx2
      dsimp [ω2, s]
      rw [hsecond_eq]
      exact div_nonneg (hself.hessian_posSemidef hx.1 u) hs.le
    have hlam_nonneg : 0 ≤ lam := by
      dsimp [lam]
      positivity
    have hthird_formula :
        thirdDirectionalDerivative (sublevelLogBarrier f β) x u =
          2 * ω1 ^ (3 : ℕ) + 3 * ω1 * ω2 + z := by
      -- Route correction: keep the source slack-slice proof and rewrite only the final cubic core.
      simpa [ω1, ω2, z, s, add_comm, add_left_comm, add_assoc, mul_assoc, mul_left_comm, mul_comm]
        using hself.sublevel_barrier_third_deriv_formula β hx.1 hx.2
    have hz_bound : |z| ≤ 2 * lam * (Real.sqrt ω2) ^ (3 : ℕ) := by
      -- The source self-concordance bound becomes the normalized remainder estimate after dividing
      -- by the positive slack.
      simpa [z, lam, ω2, s, mul_assoc, mul_left_comm, mul_comm] using
        hself.sublevel_barrier_remainder_bound β hx.1 hx.2
          (u := u)
    have hnorm_sq :
        ‖u‖[sublevelLogBarrier f β; x] ^ (2 : ℕ) = ω1 ^ (2 : ℕ) + ω2 := by
      -- Clause (2) identifies the barrier local norm with the normalized scalar radius.
      calc
        ‖u‖[sublevelLogBarrier f β; x] ^ (2 : ℕ)
            = secondDirectionalDerivative f x u / s +
                (inner ℝ (∇ f x) u) ^ (2 : ℕ) / s ^ (2 : ℕ) := by
                  simpa [s] using hself.sublevel_barrier_local_norm_sq β hx.1 hx.2 (u := u)
        _ = ω1 ^ (2 : ℕ) + ω2 := by
              dsimp [ω1, ω2]
              field_simp [hs.ne']
              ring
    have hω_total_nonneg : 0 ≤ ω1 ^ (2 : ℕ) + ω2 := by
      nlinarith [sq_nonneg ω1, hω2_nonneg]
    have hsqrt_norm :
        Real.sqrt (ω1 ^ (2 : ℕ) + ω2) = ‖u‖[sublevelLogBarrier f β; x] := by
      have hsq :
          (Real.sqrt (ω1 ^ (2 : ℕ) + ω2)) ^ (2 : ℕ) =
            ‖u‖[sublevelLogBarrier f β; x] ^ (2 : ℕ) := by
        rw [Real.sq_sqrt hω_total_nonneg, hnorm_sq]
      have hsqrt_nonneg : 0 ≤ Real.sqrt (ω1 ^ (2 : ℕ) + ω2) := by
        exact Real.sqrt_nonneg _
      have hnorm_nonneg : 0 ≤ ‖u‖[sublevelLogBarrier f β; x] := by
        exact hessianLocalNorm_nonneg (sublevelLogBarrier f β) x u
      apply le_antisymm
      · exact le_of_sq_le_sq (by simpa using le_of_eq hsq) hnorm_nonneg
      · exact le_of_sq_le_sq (by simpa using le_of_eq hsq.symm) hsqrt_nonneg
    have hβ_star_nonneg : 0 ≤ β - fStar := by
      linarith [h_lower hx.1, hx.2]
    have hs_le : s ≤ β - fStar := by
      dsimp [s]
      linarith [h_lower hx.1]
    have hlam_sq : lam ^ (2 : ℕ) = (Mf : ℝ) ^ (2 : ℕ) * s := by
      dsimp [lam]
      calc
        ((Mf : ℝ) * Real.sqrt s) ^ (2 : ℕ) = (Mf : ℝ) ^ (2 : ℕ) * (Real.sqrt s) ^ (2 : ℕ) := by
            ring
        _ = (Mf : ℝ) ^ (2 : ℕ) * s := by
              rw [Real.sq_sqrt hs.le]
    have hcoeff_le :
        Real.sqrt (1 + lam ^ (2 : ℕ)) ≤
          ((NNReal.sqrt (1 + Mf ^ (2 : ℕ) * Real.toNNReal (β - fStar)) : NNReal) : ℝ) := by
      rw [Real.coe_sqrt]
      apply Real.sqrt_le_sqrt
      rw [hlam_sq, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_pow]
      have htoNN :
          s ≤ ((β - fStar).toNNReal : ℝ) := by
        simpa [Real.coe_toNNReal', hβ_star_nonneg] using hs_le
      have hmul :
          (Mf : ℝ) ^ (2 : ℕ) * s ≤
            (Mf : ℝ) ^ (2 : ℕ) * ((β - fStar).toNNReal : ℝ) := by
        exact mul_le_mul_of_nonneg_left htoNN (by positivity)
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hmul 1
    have hmerge :
        |2 * ω1 ^ (3 : ℕ) + 3 * ω1 * ω2 + z| ≤
          2 * Real.sqrt (1 + lam ^ (2 : ℕ)) * (Real.sqrt (ω1 ^ (2 : ℕ) + ω2)) ^ (3 : ℕ) := by
      exact sublevel_cubic_merge_bound hω2_nonneg hlam_nonneg hz_bound
    have hpow_nonneg :
        0 ≤ (Real.sqrt (ω1 ^ (2 : ℕ) + ω2)) ^ (3 : ℕ) := by
      positivity
    have hcoeff_mul :
        Real.sqrt (1 + lam ^ (2 : ℕ)) * (Real.sqrt (ω1 ^ (2 : ℕ) + ω2)) ^ (3 : ℕ) ≤
          ((NNReal.sqrt (1 + Mf ^ (2 : ℕ) * Real.toNNReal (β - fStar)) : NNReal) : ℝ) *
            (Real.sqrt (ω1 ^ (2 : ℕ) + ω2)) ^ (3 : ℕ) := by
      exact mul_le_mul_of_nonneg_right hcoeff_le hpow_nonneg
    -- Combine the normalized cubic bound with the monotonicity of the coefficient.
    calc
      |thirdDirectionalDerivative (sublevelLogBarrier f β) x u|
          = |2 * ω1 ^ (3 : ℕ) + 3 * ω1 * ω2 + z| := by
              rw [hthird_formula]
      _ ≤ 2 * Real.sqrt (1 + lam ^ (2 : ℕ)) * (Real.sqrt (ω1 ^ (2 : ℕ) + ω2)) ^ (3 : ℕ) := by
            exact hmerge
      _ ≤ 2 *
            ((NNReal.sqrt (1 + Mf ^ (2 : ℕ) * Real.toNNReal (β - fStar)) : NNReal) : ℝ) *
              (Real.sqrt (ω1 ^ (2 : ℕ) + ω2)) ^ (3 : ℕ) := by
            nlinarith
      _ = 2 *
            ((NNReal.sqrt (1 + Mf ^ (2 : ℕ) * Real.toNNReal (β - fStar)) : NNReal) : ℝ) *
              ‖u‖[sublevelLogBarrier f β; x] ^ (3 : ℕ) := by
            rw [hsqrt_norm]

end SublevelLogBarrier

end
