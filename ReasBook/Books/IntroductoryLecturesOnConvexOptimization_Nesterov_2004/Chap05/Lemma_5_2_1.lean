/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_17
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_12
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Corollary_5_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_21
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_24
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_2_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Lemma_5_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Proposition_5_0_15

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient HessianDualLocalNorm HessianLocalNorm NewtonDecrement
open scoped SelfConcordantAuxiliaryFunction
open SelfConcordantNewtonVariant

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Lemma 5.2.1 lies in the Chapter 5 self-concordant intermediate-Newton domain.

Sampled owner declarations:
* `selfConcordantNewtonNextPoint` in `Definition_5_2_1`, the Chapter 5 owner for one-step
  self-concordant Newton updates;
* `NewtonDecrement.ofDetNeZero` in `Definition_5_0_24`, the Chapter 5 owner for the Newton
  decrement at a domain point with nondegenerate Hessian;
* `DampedNewton.Method.IsSelfConcordant` in `Definition_5_2_1`, the Chapter 5 refinement of the
  recursive damped Newton iterate sequence;
* `selfConcordant_dampedNewtonStep_value_decrease` in `Theorem_5_1_15`, the nearby one-step
  value-decrease owner for the damped variant.

Best owner abstraction:
* source-facing: the value drop along the intermediate Newton iterates;
* core/canonical: the one-step update `selfConcordantNewtonNextPoint` together with
  `NewtonDecrement.ofDetNeZero`;
* bridge/view: the recursive method step `x_{k+1}` obtained from the method package.

Primitive data:
* a self-concordant function `f` on `dom` with parameter `Mf`;
* a point `x ∈ dom`;
* Hessian nondegeneracy at `x`.

Derived API:
* the one-step intermediate update
  `selfConcordantNewtonNextPoint f Mf .intermediate x hx hH`;
* the Newton decrement `NewtonDecrement.ofDetNeZero Mf f hx hH`;
* the method-level successor `method (k + 1)`, recovered from the canonical one-step owner.

This refinement keeps the iterate-level textbook lemma, but no longer treats the recursive method
package as primitive data for the inequality itself. The file now centers the one-step owner
surface and derives the method statement from it. -/

section

variable {dom : Set E} {Mf : NNReal} {f : E → ℝ}
variable [IsSelfConcordantOnWith dom Mf f]

/-- Helper for Lemma 5.2.1: a `C²` objective has a differentiable gradient field at the base
point. -/
private theorem differentiableAt_gradient_of_contDiffAt_two
    {g : E → ℝ} {x : E} (hg : ContDiffAt ℝ 2 g x) :
    DifferentiableAt ℝ (∇ g) x := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ g) x := by
    exact
      (hg.fderiv_right
        (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))).differentiableAt
        one_ne_zero
  change DifferentiableAt ℝ (fun y ↦ D (fderiv ℝ g y)) x
  exact (D.hasFDerivAt.comp x hfdiff.hasFDerivAt).differentiableAt

/-- Helper for Lemma 5.2.1: a `C³` objective has a differentiable Hessian field at each point. -/
private theorem hessian_hasFDerivAt_of_contDiffAt_three
    {g : E → ℝ} {x : E} (hg : ContDiffAt ℝ 3 g x) :
    HasFDerivAt (hessian g) (fderiv ℝ (hessian g) x) x := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfderiv_C2 : ContDiffAt ℝ 2 (fderiv ℝ g) x := by
    -- Differentiate `g` once and keep the remaining two derivatives.
    exact hg.fderiv_right (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)
  have hgrad_C2 : ContDiffAt ℝ 2 (∇ g) x := by
    -- Rewrite the gradient through the Riesz map before differentiating again.
    simpa [gradient, D] using D.contDiff.contDiffAt.comp x hfderiv_C2
  have hhessian_C1 : ContDiffAt ℝ 1 (hessian g) x := by
    -- One more derivative of the gradient is exactly the Hessian owner.
    simpa [hessian] using
      hgrad_C2.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  exact (hhessian_C1.hasStrictFDerivAt one_ne_zero).hasFDerivAt

/-- Helper for Lemma 5.2.1: when `M_f = 0`, self-concordance forces the Hessian to be constant on
the convex domain. -/
private theorem zeroSelfConcordant_hessian_eq
    {g : E → ℝ} [IsSelfConcordantOnWith dom Mf g]
    {x y : E} (hMf0 : Mf = 0) (hx : x ∈ dom) (hy : y ∈ dom) :
    hessian g x = hessian g y := by
  let hself : IsSelfConcordantOnWith dom Mf g := inferInstance
  have hhess_diff : DifferentiableOn ℝ (hessian g) dom := by
    intro z hz
    -- A self-concordant function is `C³`, so its Hessian field is differentiable on `dom`.
    have hhess_z : DifferentiableAt ℝ (hessian g) z :=
      (hessian_hasFDerivAt_of_contDiffAt_three
        (hself.contDiffOn.contDiffAt (hself.isOpen_domain.mem_nhds hz))).differentiableAt
    exact hhess_z.differentiableWithinAt
  have hhess_zero :
      ∀ z ∈ dom, fderivWithin ℝ (hessian g) dom z = 0 := by
    intro z hz
    rw [fderivWithin_of_isOpen hself.isOpen_domain hz]
    apply ContinuousLinearMap.ext
    intro u
    -- The third derivative bound with `u` and `-u` collapses to zero when `M_f = 0`.
    have hle : fderiv ℝ (hessian g) z u ≤ 0 := by
      simpa [hMf0] using hself.thirdDerivative_operator_le hz u
    have hneg_le : -(fderiv ℝ (hessian g) z u) ≤ 0 := by
      simpa [map_neg, hMf0] using hself.thirdDerivative_operator_le hz (-u)
    have hge : 0 ≤ fderiv ℝ (hessian g) z u := by
      simpa [ContinuousLinearMap.le_def] using hneg_le
    exact le_antisymm hle hge
  exact hself.convex_domain.is_const_of_fderivWithin_eq_zero hhess_diff hhess_zero hx hy

/-- Helper for Lemma 5.2.1: when `M_f = 0`, the gradient is affine with constant Hessian on the
whole domain. -/
private theorem zeroSelfConcordant_gradient_affine
    {g : E → ℝ} [IsSelfConcordantOnWith dom Mf g]
    {x y : E} (hMf0 : Mf = 0) (hx : x ∈ dom) (hy : y ∈ dom) :
    ∇ g y = ∇ g x + hessian g x (y - x) := by
  let hself : IsSelfConcordantOnWith dom Mf g := inferInstance
  let A : E →L[ℝ] E := hessian g x
  let model : E → E := fun z ↦ (∇ g x - A x) + A z
  have hgrad_diff : DifferentiableOn ℝ (∇ g) dom := by
    intro z hz
    -- A self-concordant function is `C²`, so its gradient field is differentiable on `dom`.
    have hgrad_z : DifferentiableAt ℝ (∇ g) z :=
      differentiableAt_gradient_of_contDiffAt_two
        ((hself.contDiffOn.of_le (by norm_num)).contDiffAt (hself.isOpen_domain.mem_nhds hz))
    exact hgrad_z.differentiableWithinAt
  have hmodel_diff : DifferentiableOn ℝ model dom := by
    intro z hz
    -- The comparison field is affine, so its derivative is the frozen Hessian `A`.
    have hmodel_deriv : HasFDerivAt model A z := by
      simpa [model] using (A.hasFDerivAt.const_add (∇ g x - A x))
    exact hmodel_deriv.differentiableAt.differentiableWithinAt
  have hderiv_eq :
      dom.EqOn (fderivWithin ℝ (∇ g) dom) (fderivWithin ℝ model dom) := by
    intro z hz
    rw [fderivWithin_of_isOpen hself.isOpen_domain hz]
    rw [fderivWithin_of_isOpen hself.isOpen_domain hz]
    calc
      fderiv ℝ (∇ g) z = hessian g z := by rw [hessian]
      _ = A := by
        simpa [A] using zeroSelfConcordant_hessian_eq (dom := dom) (Mf := Mf) (g := g) hMf0 hz hx
      _ = fderiv ℝ model z := by
        symm
        simp [model]
  have hmodel_eqOn :
      dom.EqOn (∇ g) model :=
    hself.convex_domain.eqOn_of_fderivWithin_eq hgrad_diff hmodel_diff
      hself.isOpen_domain.uniqueDiffOn hderiv_eq hx (by simp [model])
  calc
    ∇ g y = model y := hmodel_eqOn hy
    _ = ∇ g x + hessian g x (y - x) := by
      dsimp [model, A]
      rw [ContinuousLinearMap.map_sub]
      abel

/-- Helper for Lemma 5.2.1: when `M_f = 0`, the objective agrees with its frozen quadratic
Taylor model on the whole domain. -/
private theorem zeroSelfConcordant_eq_secondOrderTaylorModelAt
    {x y : E} (hMf0 : Mf = 0) (hx : x ∈ dom) (hy : y ∈ dom) :
    f y = secondOrderTaylorModelAt f x y := by
  let hself : IsSelfConcordantOnWith dom Mf f := inferInstance
  let hPos : (hessian f x).IsPositive :=
    IsSelfConcordantOnWith.hessian_isPositive_of_mem Mf hx
  have hA_self : IsSelfAdjoint (hessian f x) := hPos.isSelfAdjoint
  have hf_diff : DifferentiableOn ℝ f dom := by
    intro z hz
    -- Self-concordance supplies `C¹` regularity on the whole domain.
    exact
      (hself.contDiffOn.contDiffAt (hself.isOpen_domain.mem_nhds hz)).differentiableAt
        (by norm_num)
        |>.differentiableWithinAt
  have hmodel_diff : DifferentiableOn ℝ (secondOrderTaylorModelAt f x) dom := by
    intro z hz
    -- The frozen quadratic Taylor model has the expected affine gradient everywhere.
    exact
      (hasGradientAt_secondOrderTaylorModelAt_of_isSelfAdjoint
        (f := f) (x := x) (y := z) hA_self).differentiableAt.differentiableWithinAt
  have hderiv_eq :
      dom.EqOn (fderivWithin ℝ f dom)
        (fderivWithin ℝ (secondOrderTaylorModelAt f x) dom) := by
    intro z hz
    rw [fderivWithin_of_isOpen hself.isOpen_domain hz]
    rw [fderivWithin_of_isOpen hself.isOpen_domain hz]
    -- Compare both derivatives through their gradient covectors.
    have hf_fderiv :
        fderiv ℝ f z = (InnerProductSpace.toDual ℝ E) (∇ f z) := by
      have hzDiff : DifferentiableAt ℝ f z :=
        (hself.contDiffOn.contDiffAt (hself.isOpen_domain.mem_nhds hz)).differentiableAt
          (by norm_num)
      simpa [gradient] using hzDiff.hasGradientAt.hasFDerivAt.fderiv.symm
    have hmodel_fderiv :
        fderiv ℝ (secondOrderTaylorModelAt f x) z =
          (InnerProductSpace.toDual ℝ E) (∇ f x + hessian f x (z - x)) := by
      simpa [gradient] using
        (hasGradientAt_secondOrderTaylorModelAt_of_isSelfAdjoint
          (f := f) (x := x) (y := z) hA_self).hasFDerivAt.fderiv
    calc
      fderiv ℝ f z = (InnerProductSpace.toDual ℝ E) (∇ f z) := hf_fderiv
      _ = (InnerProductSpace.toDual ℝ E) (∇ f x + hessian f x (z - x)) := by
        rw [zeroSelfConcordant_gradient_affine (dom := dom) (Mf := Mf) (g := f) hMf0 hx hz]
      _ = fderiv ℝ (secondOrderTaylorModelAt f x) z := hmodel_fderiv.symm
  have hvalue_eq :
      dom.EqOn f (secondOrderTaylorModelAt f x) :=
    hself.convex_domain.eqOn_of_fderivWithin_eq hf_diff hmodel_diff
      hself.isOpen_domain.uniqueDiffOn hderiv_eq hx (by simp)
  simpa using hvalue_eq hy

/-- Helper for Lemma 5.2.1: nonnegative scalar dilations scale the Hessian local norm at a point
with positive Hessian. -/
private theorem hessianLocalNorm_smul_of_nonneg
    {x u : E} (hPos : (hessian f x).IsPositive)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    ‖τ • u‖[f; x] = τ * ‖u‖[f; x] := by
  have hquad : 0 ≤ inner ℝ u (hessian f x u) := hPos.inner_nonneg_right u
  -- Expand the local norm and pull the nonnegative scalar through the square root.
  calc
    ‖τ • u‖[f; x] = Real.sqrt ((τ * τ) * inner ℝ u (hessian f x u)) := by
      rw [hessianLocalNorm_def]
      congr 1
      simp [inner_smul_left, inner_smul_right, mul_assoc]
    _ = Real.sqrt (inner ℝ u (hessian f x u)) * Real.sqrt (τ * τ) := by
      rw [mul_comm, Real.sqrt_mul hquad]
    _ = τ * ‖u‖[f; x] := by
      rw [show τ * τ = τ ^ (2 : ℕ) by ring, Real.sqrt_sq_eq_abs, abs_of_nonneg hτ,
        hessianLocalNorm_def]
      ring

/-- Helper for Lemma 5.2.1: the inverse-Hessian gradient pairing is nonnegative. -/
private theorem inverseHessianGradientPairing_nonneg
    (hself : IsSelfConcordantOnWith dom Mf f)
    {x : E} (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0) :
    0 ≤ inner ℝ (∇ f x) ((hessian f x).inverse (∇ f x)) := by
  let v := (hessian f x).inverse (∇ f x)
  let hPos : (hessian f x).IsPositive := hself.hessian_isPositive hx
  let hInv : (hessian f x).IsInvertible :=
    hessian_isInvertible_of_det_ne_zero hH
  have hquad : 0 ≤ inner ℝ v (hessian f x v) := hPos.inner_nonneg_right v
  have hHv : hessian f x v = ∇ f x := hInv.self_apply_inverse (∇ f x)
  -- Rewrite the positive quadratic form of the Newton direction back to the gradient pairing.
  calc
    0 ≤ inner ℝ v (hessian f x v) := hquad
    _ = inner ℝ (∇ f x) v := by rw [hHv, real_inner_comm]
    _ = inner ℝ (∇ f x) ((hessian f x).inverse (∇ f x)) := by
      rfl

/-- Helper for Lemma 5.2.1: the intermediate step size has the textbook rational form
`(1 + M_f λ) / (1 + M_f λ + M_f² λ²)`. -/
private theorem intermediateStep_stepSize_eq
    {x : E} (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0) :
    let δ := NewtonDecrement.ofDetNeZero Mf f hx hH
    selfConcordantNewtonStepSize f Mf .intermediate x hx hH =
      (1 + (Mf : ℝ) * δ) /
        (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ)) := by
  let δ := NewtonDecrement.ofDetNeZero Mf f hx hH
  have hδ_nonneg : 0 ≤ δ := NewtonDecrement.ofDetNeZero_nonneg Mf f hx hH
  have hshift_den_pos : 0 < 1 + (Mf : ℝ) * δ := by
    positivity
  -- Expand the intermediate shift and normalize the rational expression once.
  rw [selfConcordantNewtonStepSize]
  simp [selfConcordantNewtonShift]
  field_simp [hshift_den_pos.ne']

/-- Helper for Lemma 5.2.1: subtracting the current point from the intermediate update exposes
the inverse-Hessian Newton direction. -/
private theorem intermediateStep_sub_eq_neg_smul
    {x : E} (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0) :
    let α := selfConcordantNewtonStepSize f Mf .intermediate x hx hH
    selfConcordantNewtonNextPoint f Mf .intermediate x hx hH - x =
      -(α • (hessian f x).inverse (∇ f x)) := by
  dsimp [selfConcordantNewtonStepSize]
  -- Subtract the base point from the explicit one-step formula.
  rw [selfConcordantNewtonNextPoint_def]
  simp [sub_eq_add_neg, add_left_comm, add_comm]

/-- Helper for Lemma 5.2.1: the intermediate-step displacement has base local norm
`λ (1 + M_f λ) / (1 + M_f λ + M_f² λ²)`. -/
private theorem intermediateStep_localNorm_eq
    {x : E} (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0) :
    let δ := NewtonDecrement.ofDetNeZero Mf f hx hH
    ‖selfConcordantNewtonNextPoint f Mf .intermediate x hx hH - x‖[f; x] =
      δ * (1 + (Mf : ℝ) * δ) /
        (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ)) := by
  let δ := NewtonDecrement.ofDetNeZero Mf f hx hH
  let α := selfConcordantNewtonStepSize f Mf .intermediate x hx hH
  let v : E := (hessian f x).inverse (∇ f x)
  let hPos : (hessian f x).IsPositive :=
    IsSelfConcordantOnWith.hessian_isPositive_of_mem Mf hx
  let hInv : (hessian f x).IsInvertible :=
    hessian_isInvertible_of_det_ne_zero hH
  have hα_nonneg : 0 ≤ α := by
    exact le_of_lt (selfConcordantNewtonStepSize_pos f Mf .intermediate x hx hH)
  have hv_eq : hessian f x v = ∇ f x := hInv.self_apply_inverse (∇ f x)
  have hv_norm : ‖v‖[f; x] = δ := by
    -- The local norm of the inverse-Hessian gradient direction is the Newton decrement.
    rw [hessianLocalNorm_def]
    calc
      Real.sqrt (inner ℝ v (hessian f x v))
          = Real.sqrt (inner ℝ (∇ f x) v) := by rw [hv_eq, real_inner_comm]
      _ = δ := by
        simpa [δ, v] using (NewtonDecrement.ofDetNeZero_def Mf f hx hH).symm
  -- Rewrite the displacement and then scale the local norm by the positive step size.
  calc
    ‖selfConcordantNewtonNextPoint f Mf .intermediate x hx hH - x‖[f; x]
        = ‖α • v‖[f; x] := by
            rw [intermediateStep_sub_eq_neg_smul (Mf := Mf) (f := f) hx hH]
            rw [hessianLocalNorm_neg]
    _ = α * ‖v‖[f; x] := hessianLocalNorm_smul_of_nonneg (f := f) hPos hα_nonneg
    _ = α * δ := by rw [hv_norm]
    _ = δ * (1 + (Mf : ℝ) * δ) /
          (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ)) := by
      rw [show α =
          (1 + (Mf : ℝ) * δ) /
            (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ)) by
        simpa [δ] using (intermediateStep_stepSize_eq (Mf := Mf) (f := f) hx hH)]
      field_simp

/-- Helper for Lemma 5.2.1: the affine Taylor term along the intermediate Newton direction is
`-λ² (1 + M_f λ) / (1 + M_f λ + M_f² λ²)`. -/
private theorem intermediateStep_gradient_pairing_eq
    {x : E} (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0) :
    let δ := NewtonDecrement.ofDetNeZero Mf f hx hH
    inner ℝ (∇ f x) (selfConcordantNewtonNextPoint f Mf .intermediate x hx hH - x) =
      -(δ ^ (2 : ℕ) * (1 + (Mf : ℝ) * δ) /
        (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ))) := by
  let δ := NewtonDecrement.ofDetNeZero Mf f hx hH
  let α := selfConcordantNewtonStepSize f Mf .intermediate x hx hH
  let v : E := (hessian f x).inverse (∇ f x)
  have hq_nonneg : 0 ≤ inner ℝ (∇ f x) v := by
    simpa [v] using
      (inverseHessianGradientPairing_nonneg (dom := dom) (Mf := Mf) (f := f)
        (inferInstance : IsSelfConcordantOnWith dom Mf f) hx hH)
  have hq_eq : inner ℝ (∇ f x) v = δ ^ (2 : ℕ) := by
    -- Square the defining Newton-decrement identity.
    calc
      inner ℝ (∇ f x) v = (Real.sqrt (inner ℝ (∇ f x) v)) ^ (2 : ℕ) := by
        symm
        simpa using Real.sq_sqrt hq_nonneg
      _ = δ ^ (2 : ℕ) := by
        rw [show Real.sqrt (inner ℝ (∇ f x) v) = δ by
          simpa [δ, v] using (NewtonDecrement.ofDetNeZero_def Mf f hx hH).symm]
  -- Rewrite the displacement and evaluate the gradient pairing on the scaled Newton direction.
  calc
    inner ℝ (∇ f x) (selfConcordantNewtonNextPoint f Mf .intermediate x hx hH - x)
        = inner ℝ (∇ f x) (-(α • v)) := by
            rw [intermediateStep_sub_eq_neg_smul (Mf := Mf) (f := f) hx hH]
    _ = -(α * inner ℝ (∇ f x) v) := by
      simp [inner_smul_right]
    _ = -(α * δ ^ (2 : ℕ)) := by rw [hq_eq]
    _ = -(δ ^ (2 : ℕ) * (1 + (Mf : ℝ) * δ) /
          (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ))) := by
      rw [show α =
          (1 + (Mf : ℝ) * δ) /
            (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ)) by
        simpa [δ] using (intermediateStep_stepSize_eq (Mf := Mf) (f := f) hx hH)]
      field_simp

/-- Helper for Lemma 5.2.1: when `M_f > 0`, the intermediate Newton displacement has local norm
strictly below the reciprocal Dikin threshold. -/
private theorem intermediateStep_localNorm_lt_inv_of_ne_zero
    {x : E} (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0) (hMf : Mf ≠ 0) :
    let δ := NewtonDecrement.ofDetNeZero Mf f hx hH
    ‖selfConcordantNewtonNextPoint f Mf .intermediate x hx hH - x‖[f; x] < 1 / (Mf : ℝ) := by
  let δ := NewtonDecrement.ofDetNeZero Mf f hx hH
  have hδ_nonneg : 0 ≤ δ := by
    simpa [δ] using NewtonDecrement.ofDetNeZero_nonneg Mf f hx hH
  have hMf_pos : 0 < (Mf : ℝ) := by
    have hMf_pos_nn : 0 < Mf := lt_of_le_of_ne Mf.2 (Ne.symm hMf)
    exact_mod_cast hMf_pos_nn
  have hstep_lt :
      δ * (1 + (Mf : ℝ) * δ) /
          (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ)) <
        1 / (Mf : ℝ) := by
    have hden_pos :
        0 <
          1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ) := by
      positivity
    refine (lt_div_iff₀ hMf_pos).2 ?_
    have hscaled_lt :
        (((Mf : ℝ) * δ) * (1 + (Mf : ℝ) * δ)) /
            (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ)) <
          1 := by
      refine (div_lt_iff₀ hden_pos).2 ?_
      nlinarith
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled_lt
  -- Rewrite the local norm to the canonical rational radius and close the scalar comparison.
  rw [show
      ‖selfConcordantNewtonNextPoint f Mf .intermediate x hx hH - x‖[f; x] =
        δ * (1 + (Mf : ℝ) * δ) /
          (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ)) by
    simpa [δ] using (intermediateStep_localNorm_eq (Mf := Mf) (f := f) hx hH)]
  exact hstep_lt

/-- Helper for Lemma 5.2.1: when `M_f > 0`, the intermediate Newton update lies in the admissible
open Dikin ellipsoid centered at the current point. -/
private theorem intermediateStep_mem_openDikinEllipsoid_of_ne_zero
    {x : E} (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0) (hMf : Mf ≠ 0) :
    selfConcordantNewtonNextPoint f Mf .intermediate x hx hH ∈
      openDikinEllipsoid f x (1 / (Mf : ℝ)) := by
  -- The Dikin membership is exactly the reciprocal-radius inequality already proved above.
  refine (mem_openDikinEllipsoid_iff f x
      (selfConcordantNewtonNextPoint f Mf .intermediate x hx hH) (1 / (Mf : ℝ))).2 ?_
  simpa using
    (intermediateStep_localNorm_lt_inv_of_ne_zero (Mf := Mf) (f := f) hx hH hMf)

/-- Helper for Lemma 5.2.1: the normalized scalar gap vanishes at the left endpoint `t = 0`. -/
private theorem intermediateStepPositiveScalarGap_zero :
    (0 : ℝ) * (1 + 0) ^ (2 : ℕ) / (1 + 0 + 0 ^ (2 : ℕ)) -
        Real.log (1 + 0 + 0 ^ (2 : ℕ)) -
        (0 ^ (2 : ℕ) / (2 * (1 + 0 + 0 ^ (2 : ℕ))) +
          0 ^ (3 : ℕ) / (2 * (1 + 0) * (3 + 2 * 0))) = 0 := by
  simp

/-- Helper for Lemma 5.2.1: the scalar gap left after the exact intermediate-step normalization is
nonnegative on `[0, ∞)`. -/
private theorem intermediateStepPositiveScalarGap_nonneg
    {t : ℝ} (ht : 0 ≤ t) :
    t ^ 2 / (2 * (1 + t + t ^ (2 : ℕ))) +
        t ^ 3 / (2 * (1 + t) * (3 + 2 * t)) ≤
      t * (1 + t) ^ (2 : ℕ) / (1 + t + t ^ (2 : ℕ)) - Real.log (1 + t + t ^ (2 : ℕ)) := by
  let a : ℝ := t ^ (2 : ℕ) / (1 + t)
  have ht1_pos : 0 < 1 + t := by positivity
  have hquad_pos : 0 < 1 + t + t ^ (2 : ℕ) := by positivity
  have hmix_pos : 0 < 2 * t ^ (2 : ℕ) + 3 * t + 3 := by positivity
  have ha_nonneg : 0 ≤ a := by
    -- The second `ω` lower bound lives at the scalar `a = t² / (1 + t)`.
    dsimp [a]
    positivity
  have homega_t :
      t ^ 2 / (2 * (1 + (2 / 3 : ℝ) * t)) ≤ t - Real.log (1 + t) :=
    omegaIntermediateLowerBoundRaw ht
  have homega_a :
      a ^ (2 : ℕ) / (2 * (1 + (2 / 3 : ℝ) * a)) ≤ a - Real.log (1 + a) := by
    simpa [a] using omegaIntermediateLowerBoundRaw (t := a) ha_nonneg
  have htarget_decomp :
      t * (1 + t) ^ (2 : ℕ) / (1 + t + t ^ (2 : ℕ)) -
          Real.log (1 + t + t ^ (2 : ℕ)) =
        (t - Real.log (1 + t)) + (a - Real.log (1 + a)) -
          t ^ (4 : ℕ) / ((1 + t) * (1 + t + t ^ (2 : ℕ))) := by
    have hquot_pos : 0 < (1 + t + t ^ (2 : ℕ)) / (1 + t) := by
      positivity
    have ha_one : 1 + a = (1 + t + t ^ (2 : ℕ)) / (1 + t) := by
      -- Normalize the second logarithmic factor to the textbook quotient.
      dsimp [a]
      field_simp [ht1_pos.ne']
    have hmul :
        (1 + t) * ((1 + t + t ^ (2 : ℕ)) / (1 + t)) = 1 + t + t ^ (2 : ℕ) := by
      field_simp [ht1_pos.ne']
    calc
      t * (1 + t) ^ (2 : ℕ) / (1 + t + t ^ (2 : ℕ)) -
          Real.log (1 + t + t ^ (2 : ℕ)) =
        t * (1 + t) ^ (2 : ℕ) / (1 + t + t ^ (2 : ℕ)) -
          Real.log ((1 + t) * ((1 + t + t ^ (2 : ℕ)) / (1 + t))) := by
            rw [hmul]
      _ =
        t * (1 + t) ^ (2 : ℕ) / (1 + t + t ^ (2 : ℕ)) -
          (Real.log (1 + t) + Real.log ((1 + t + t ^ (2 : ℕ)) / (1 + t))) := by
            rw [Real.log_mul ht1_pos.ne' hquot_pos.ne']
      _ =
        t * (1 + t) ^ (2 : ℕ) / (1 + t + t ^ (2 : ℕ)) -
          (Real.log (1 + t) + Real.log (1 + a)) := by rw [← ha_one]
      _ =
        (t - Real.log (1 + t)) + (a - Real.log (1 + a)) -
          t ^ (4 : ℕ) / ((1 + t) * (1 + t + t ^ (2 : ℕ))) := by
            dsimp [a]
            field_simp [ht1_pos.ne', hquad_pos.ne']
            ring
  have hcompare :
      t ^ 2 / (2 * (1 + t + t ^ (2 : ℕ))) +
          t ^ 3 / (2 * (1 + t) * (3 + 2 * t)) ≤
        t ^ 2 / (2 * (1 + (2 / 3 : ℝ) * t)) +
          a ^ (2 : ℕ) / (2 * (1 + (2 / 3 : ℝ) * a)) -
            t ^ (4 : ℕ) / ((1 + t) * (1 + t + t ^ (2 : ℕ))) := by
    have hdiff_nonneg :
        0 ≤
          t ^ (6 : ℕ) /
            (2 * (t + 1) * (t ^ (2 : ℕ) + t + 1) * (2 * t ^ (2 : ℕ) + 3 * t + 3)) := by
      positivity
    have hdiff_eq :
        (t ^ 2 / (2 * (1 + (2 / 3 : ℝ) * t)) +
            a ^ (2 : ℕ) / (2 * (1 + (2 / 3 : ℝ) * a)) -
              t ^ (4 : ℕ) / ((1 + t) * (1 + t + t ^ (2 : ℕ)))) -
          (t ^ 2 / (2 * (1 + t + t ^ (2 : ℕ))) +
            t ^ 3 / (2 * (1 + t) * (3 + 2 * t))) =
          t ^ (6 : ℕ) /
            (2 * (t + 1) * (t ^ (2 : ℕ) + t + 1) * (2 * t ^ (2 : ℕ) + 3 * t + 3)) := by
      -- Clear the positive denominators; the remainder is a polynomial identity.
      dsimp [a]
      field_simp [ht1_pos.ne', hquad_pos.ne', hmix_pos.ne']
      ring
    linarith
  have htarget :
      t ^ 2 / (2 * (1 + t + t ^ (2 : ℕ))) +
          t ^ 3 / (2 * (1 + t) * (3 + 2 * t)) ≤
        t * (1 + t) ^ (2 : ℕ) / (1 + t + t ^ (2 : ℕ)) -
          Real.log (1 + t + t ^ (2 : ℕ)) := by
    -- Combine the two `ω` lower bounds with the exact scalar decomposition of the target.
    rw [htarget_decomp]
    linarith
  exact htarget

/-- Helper for Lemma 5.2.1: after rewriting the intermediate-step Taylor bound through the
canonical local norm and gradient-pairing identities, the positive branch becomes an exact scalar
drop formula. -/
private theorem intermediateStepGradientContribution_eq
    {x : E} (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0) (hMf : Mf ≠ 0) :
    let δ := NewtonDecrement.ofDetNeZero Mf f hx hH
    let xPlus := selfConcordantNewtonNextPoint f Mf .intermediate x hx hH
    let t : ℝ := (Mf : ℝ) * δ
    inner ℝ (∇ f x) (xPlus - x) =
      -((1 / (Mf : ℝ) ^ (2 : ℕ)) *
        (t ^ (2 : ℕ) * (1 + t) / (1 + t + t ^ (2 : ℕ)))) := by
  dsimp
  let δ := NewtonDecrement.ofDetNeZero Mf f hx hH
  let xPlus := selfConcordantNewtonNextPoint f Mf .intermediate x hx hH
  let t : ℝ := (Mf : ℝ) * δ
  have hMf_pos : 0 < (Mf : ℝ) := by
    have hMf_pos_nn : 0 < Mf := lt_of_le_of_ne Mf.2 (Ne.symm hMf)
    exact_mod_cast hMf_pos_nn
  have hMf_ne : (Mf : ℝ) ≠ 0 := ne_of_gt hMf_pos
  -- Rewrite the existing pairing identity into the `M_f⁻²` scalar normal form.
  rw [show
      inner ℝ (∇ f x) (xPlus - x) =
        -(δ ^ (2 : ℕ) * (1 + (Mf : ℝ) * δ) /
          (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ))) by
    simpa [δ, xPlus] using
      (intermediateStep_gradient_pairing_eq (Mf := Mf) (f := f) hx hH)]
  field_simp [hMf_ne]
  ring

/-- Helper for Lemma 5.2.1: the canonical `ω_*` argument at the intermediate step has scalar
value `t (1 + t) / (1 + t + t²)`. -/
private theorem intermediateStepOmegaStarArgValue_eq
    {x : E} (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0) (hMf : Mf ≠ 0) :
    let δ := NewtonDecrement.ofDetNeZero Mf f hx hH
    let xPlus := selfConcordantNewtonNextPoint f Mf .intermediate x hx hH
    let t : ℝ := (Mf : ℝ) * δ
    let rawTau : Set.Iio (1 : ℝ) :=
      selfConcordantOmegaStarArg Mf ‖xPlus - x‖[f; x]
        (mf_mul_lt_one_of_lt_inv <|
          by
            simpa [xPlus] using
              (mem_openDikinEllipsoid_iff f x xPlus (1 / (Mf : ℝ))).1
                (intermediateStep_mem_openDikinEllipsoid_of_ne_zero
                  (Mf := Mf) (f := f) hx hH hMf))
    (rawTau : ℝ) = t * (1 + t) / (1 + t + t ^ (2 : ℕ)) := by
  dsimp
  let δ := NewtonDecrement.ofDetNeZero Mf f hx hH
  let xPlus := selfConcordantNewtonNextPoint f Mf .intermediate x hx hH
  let t : ℝ := (Mf : ℝ) * δ
  let rawTau : Set.Iio (1 : ℝ) :=
    selfConcordantOmegaStarArg Mf ‖xPlus - x‖[f; x]
      (mf_mul_lt_one_of_lt_inv <|
        by
          simpa [xPlus] using
            (mem_openDikinEllipsoid_iff f x xPlus (1 / (Mf : ℝ))).1
              (intermediateStep_mem_openDikinEllipsoid_of_ne_zero
                (Mf := Mf) (f := f) hx hH hMf))
  -- Normalize the owner remainder argument to the scalar `t = M_f δ`.
  calc
    (rawTau : ℝ) = (Mf : ℝ) * ‖xPlus - x‖[f; x] := by
      simp [rawTau]
    _ =
        (Mf : ℝ) *
          (δ * (1 + (Mf : ℝ) * δ) /
            (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ))) := by
          rw [show
              ‖xPlus - x‖[f; x] =
                δ * (1 + (Mf : ℝ) * δ) /
                  (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ)) by
            simpa [δ, xPlus] using
              (intermediateStep_localNorm_eq (Mf := Mf) (f := f) hx hH)]
    _ = t * (1 + t) / (1 + t + t ^ (2 : ℕ)) := by
      dsimp [t]
      ring_nf

/-- Helper for Lemma 5.2.1: once the intermediate-step `ω_*` argument is normalized to the
scalar variable `t = M_f δ`, the remainder term becomes the explicit logarithmic expression used
in the positive branch. -/
private theorem intermediateStepOmegaStarContribution_eq
    {x : E} (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0) (hMf : Mf ≠ 0) :
    let δ := NewtonDecrement.ofDetNeZero Mf f hx hH
    let xPlus := selfConcordantNewtonNextPoint f Mf .intermediate x hx hH
    let t : ℝ := (Mf : ℝ) * δ
    let rawTau : Set.Iio (1 : ℝ) :=
      selfConcordantOmegaStarArg Mf ‖xPlus - x‖[f; x]
        (mf_mul_lt_one_of_lt_inv <|
          by
            simpa [xPlus] using
              (mem_openDikinEllipsoid_iff f x xPlus (1 / (Mf : ℝ))).1
                (intermediateStep_mem_openDikinEllipsoid_of_ne_zero
                  (Mf := Mf) (f := f) hx hH hMf))
    (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω_* rawTau =
      (1 / (Mf : ℝ) ^ (2 : ℕ)) *
        (Real.log (1 + t + t ^ (2 : ℕ)) -
          t * (1 + t) / (1 + t + t ^ (2 : ℕ))) := by
  dsimp
  let δ := NewtonDecrement.ofDetNeZero Mf f hx hH
  let xPlus := selfConcordantNewtonNextPoint f Mf .intermediate x hx hH
  let t : ℝ := (Mf : ℝ) * δ
  let rawTau : Set.Iio (1 : ℝ) :=
    selfConcordantOmegaStarArg Mf ‖xPlus - x‖[f; x]
      (mf_mul_lt_one_of_lt_inv <|
        by
          simpa [xPlus] using
            (mem_openDikinEllipsoid_iff f x xPlus (1 / (Mf : ℝ))).1
              (intermediateStep_mem_openDikinEllipsoid_of_ne_zero
                (Mf := Mf) (f := f) hx hH hMf))
  have hδ_nonneg : 0 ≤ δ := by
    simpa [δ] using NewtonDecrement.ofDetNeZero_nonneg Mf f hx hH
  have ht_nonneg : 0 ≤ t := by
    dsimp [t]
    exact mul_nonneg Mf.2 hδ_nonneg
  have hpoly_pos : 0 < 1 + t + t ^ (2 : ℕ) := by
    positivity
  have htau :
      (rawTau : ℝ) = t * (1 + t) / (1 + t + t ^ (2 : ℕ)) := by
    simpa [δ, xPlus, t, rawTau] using
      (intermediateStepOmegaStarArgValue_eq (Mf := Mf) (f := f) hx hH hMf)
  have hone_sub :
      1 - (rawTau : ℝ) = 1 / (1 + t + t ^ (2 : ℕ)) := by
    rw [htau]
    field_simp [hpoly_pos.ne']
    ring
  have hscaled :
      (Mf : ℝ) * ‖xPlus - x‖[f; x] = t * (1 + t) / (1 + t + t ^ (2 : ℕ)) := by
    simpa [rawTau] using htau
  have hone_sub_scaled :
      1 - t * (1 + t) / (1 + t + t ^ (2 : ℕ)) = 1 / (1 + t + t ^ (2 : ℕ)) := by
    field_simp [hpoly_pos.ne']
    ring
  have hlog_inv :
      Real.log (1 / (1 + t + t ^ (2 : ℕ))) = -Real.log (1 + t + t ^ (2 : ℕ)) := by
    simpa [one_div] using Real.log_inv (1 + t + t ^ (2 : ℕ))
  -- Rewrite only the evaluated remainder and simplify the logarithm once.
  rw [hscaled, hone_sub_scaled, hlog_inv]
  dsimp [t]
  ring

/-- Helper for Lemma 5.2.1: once the Hessian quadratic form is nonnegative, squaring the local
norm recovers that quadratic form exactly. -/
private theorem sq_hessianLocalNorm_eq_inner_of_nonneg
    {z u : E} (hquad : 0 ≤ inner ℝ u (hessian f z u)) :
    ‖u‖[f; z] ^ (2 : ℕ) = inner ℝ u (hessian f z u) := by
  -- Expand the local norm and use `sqrt(x)^2 = x` on the nonnegative Hessian quadratic form.
  simpa [hessianLocalNorm_def] using Real.sq_sqrt hquad

omit [FiniteDimensional ℝ E] in
/-- Helper for Lemma 5.2.1: affine lines have the expected derivative. -/
private theorem line_hasDerivAt
    (z d : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ z + s • d) d t := by
  -- Differentiate the scalar parameter and keep the direction fixed.
  simpa [one_smul] using ((hasDerivAt_id t).smul_const d).const_add z

/-- Helper for Lemma 5.2.1: a pointwise `C²` hypothesis upgrades the gradient to a genuinely
Fréchet-differentiable map with derivative `hessian f z`. -/
private theorem gradient_hasFDerivAt_of_contDiffAt
    {z : E} (hz_C2 : ContDiffAt ℝ 2 f z) :
    HasFDerivAt (∇ f) (hessian f z) z := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfderiv : DifferentiableAt ℝ (fderiv ℝ f) z := by
    have hC1_fderiv : ContDiffAt ℝ 1 (fderiv ℝ f) z :=
      hz_C2.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    exact hC1_fderiv.differentiableAt one_ne_zero
  have hgradDiff : DifferentiableAt ℝ (∇ f) z := by
    -- Rewrite the gradient through the Riesz map before differentiating.
    simpa [gradient, D] using D.differentiableAt.comp z hfderiv
  -- The derivative of the gradient is the Hessian by definition.
  simpa [hessian] using hgradDiff.hasFDerivAt

/-- Helper for Lemma 5.2.1: self-concordance makes the Hessian vary continuously on the open
domain. -/
private theorem hessian_continuousOn :
    let _ : IsSelfConcordantOnWith dom Mf f := inferInstance
    ContinuousOn (hessian f) dom := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  let hself : IsSelfConcordantOnWith dom Mf f := inferInstance
  have hgrad_contDiff : ContDiffOn ℝ 1 (∇ f) dom := by
    have hfd : ContDiffOn ℝ 1 (fderiv ℝ f) dom :=
      hself.contDiffOn.fderiv_of_isOpen hself.isOpen_domain
        (show (1 : WithTop ℕ∞) + 1 ≤ (3 : WithTop ℕ∞) by norm_num)
    simpa [gradient, D] using D.contDiff.comp_contDiffOn hfd
  -- Differentiate the continuous gradient field once more to recover the Hessian map.
  simpa [hessian] using
    (hgrad_contDiff.fderiv_of_isOpen hself.isOpen_domain
      (show (0 : WithTop ℕ∞) + 1 ≤ (1 : WithTop ℕ∞) by norm_num)).continuousOn

/-- Helper for Lemma 5.2.1: differentiating `f` along an affine line recovers the gradient
pairing with the line direction. -/
private theorem value_line_hasDerivAt
    (hself : IsSelfConcordantOnWith dom Mf f := inferInstance)
    {z d : E} {t : ℝ} (hzt : z + t • d ∈ dom) :
    HasDerivAt (fun s : ℝ ↦ f (z + s • d)) (inner ℝ (∇ f (z + t • d)) d) t := by
  have hC1 : ContDiffAt ℝ 1 f (z + t • d) := by
    exact
      (hself.contDiffOn.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3)).contDiffAt
        (hself.isOpen_domain.mem_nhds hzt)
  -- Differentiate the ambient function first and then compose with the affine line.
  simpa using
    ((hC1.differentiableAt one_ne_zero).hasGradientAt.hasFDerivAt.comp t
      (line_hasDerivAt z d t).hasFDerivAt).hasDerivAt

/-- Helper for Lemma 5.2.1: scalarizing the gradient along an affine line differentiates to the
corresponding Hessian pairing. -/
private theorem scalarized_gradient_line_hasDerivAt
    (hself : IsSelfConcordantOnWith dom Mf f := inferInstance)
    {z d w : E} {t : ℝ} (hzt : z + t • d ∈ dom) :
    HasDerivAt (fun s : ℝ ↦ inner ℝ (∇ f (z + s • d)) w)
      (inner ℝ (hessian f (z + t • d) d) w) t := by
  have hz_C2 : ContDiffAt ℝ 2 f (z + t • d) := by
    exact
      (hself.contDiffOn.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).contDiffAt
        (hself.isOpen_domain.mem_nhds hzt)
  have hgradLine :
      HasFDerivAt (fun s : ℝ ↦ ∇ f (z + s • d))
        ((hessian f (z + t • d)).comp
          (ContinuousLinearMap.toSpanSingleton ℝ d)) t := by
    -- Route correction: differentiate the raw scalarized gradient line before subtracting any
    -- endpoint term.
    simpa using
      ((gradient_hasFDerivAt_of_contDiffAt (z := z + t • d) hz_C2).comp t
        (line_hasDerivAt z d t).hasFDerivAt)
  let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) w
  -- Compose the differentiated gradient line with the fixed dual vector `w`.
  simpa [φ, InnerProductSpace.toDual_apply_apply, real_inner_comm] using
    (φ.hasFDerivAt.comp t hgradLine).hasDerivAt

/-- Helper for Lemma 5.2.1: the rational upper transport integrand integrates to the expected
factor `u r² / (1 - u M_f r)`. -/
private theorem integralSqDivEqScaledSqDivSub
    {r u : ℝ} (hu : 0 ≤ u)
    (hden : ∀ t ∈ Set.Icc (0 : ℝ) u, 0 < 1 - (Mf : ℝ) * t * r) :
    ∫ t in 0..u, r ^ (2 : ℕ) / (1 - (Mf : ℝ) * t * r) ^ (2 : ℕ) =
      u * r ^ (2 : ℕ) / (1 - (Mf : ℝ) * u * r) := by
  let a : ℝ := (Mf : ℝ) * r
  have hden' : ∀ t ∈ Set.Icc (0 : ℝ) u, 0 < 1 - t * a := by
    intro t ht
    simpa [a, mul_assoc, mul_left_comm, mul_comm] using hden t ht
  have hnum : ContinuousOn (fun t : ℝ ↦ t * r ^ (2 : ℕ) / (1 - t * a))
      (Set.Icc (0 : ℝ) u) := by
    refine (continuousOn_id.mul continuousOn_const).div ?_ ?_
    · exact (show Continuous (fun t : ℝ ↦ 1 - t * a) by continuity).continuousOn
    · intro t ht
      exact (hden' t ht).ne'
  have hint :
      IntervalIntegrable
        (fun t : ℝ ↦ r ^ (2 : ℕ) / (1 - t * a) ^ (2 : ℕ))
        MeasureTheory.volume 0 u := by
    have hcont :
        ContinuousOn
          (fun t : ℝ ↦ r ^ (2 : ℕ) / (1 - t * a) ^ (2 : ℕ))
          (Set.Icc (0 : ℝ) u) := by
      refine continuousOn_const.div ?_ ?_
      · exact
          (show Continuous (fun t : ℝ ↦ (1 - t * a) ^ (2 : ℕ)) by
            continuity).continuousOn
      · intro t ht
        exact pow_ne_zero 2 (hden' t ht).ne'
    exact hcont.intervalIntegrable_of_Icc hu
  have hderiv :
      ∀ t ∈ Set.Ioo (0 : ℝ) u,
        HasDerivAt
          (fun s : ℝ ↦ s * r ^ (2 : ℕ) / (1 - s * a))
          (r ^ (2 : ℕ) / (1 - t * a) ^ (2 : ℕ)) t := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) u := Set.mem_Icc_of_Ioo ht
    have hden_ne : 1 - t * a ≠ 0 := (hden' t ht').ne'
    have hden_deriv :
        HasDerivAt (fun s : ℝ ↦ 1 - s * a) (-a) t := by
      convert (hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).mul_const a) using 1
      ring
    have hquot :=
      ((hasDerivAt_id t).mul_const (r ^ (2 : ℕ))).div hden_deriv hden_ne
    have hquot_slope :
        ((1 : ℝ) * r ^ (2 : ℕ) * (1 - t * a) - t * r ^ (2 : ℕ) * -a) /
            (1 - t * a) ^ (2 : ℕ) =
          r ^ (2 : ℕ) / (1 - t * a) ^ (2 : ℕ) := by
      field_simp [hden_ne]
      ring
    have hquot' :
        HasDerivAt (fun s : ℝ ↦ (s * r ^ (2 : ℕ)) / (1 - s * a))
          (((1 : ℝ) * r ^ (2 : ℕ) * (1 - t * a) - t * r ^ (2 : ℕ) * -a) /
            (1 - t * a) ^ (2 : ℕ)) t := by
      simpa using hquot
    exact hquot'.congr_deriv hquot_slope
  have hftc :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hu hnum hderiv hint
  calc
    ∫ t in 0..u, r ^ (2 : ℕ) / (1 - (Mf : ℝ) * t * r) ^ (2 : ℕ)
        = ∫ t in 0..u, r ^ (2 : ℕ) / (1 - t * a) ^ (2 : ℕ) := by
            congr with t
            simp [a, mul_left_comm, mul_comm]
    _ = u * r ^ (2 : ℕ) / (1 - u * a) - (0 * r ^ (2 : ℕ) / (1 - 0 * a)) := by
      simpa using hftc
    _ = u * r ^ (2 : ℕ) / (1 - u * a) := by ring
    _ = u * r ^ (2 : ℕ) / (1 - (Mf : ℝ) * u * r) := by
      simp [a, mul_left_comm, mul_comm]

/-- Helper for Lemma 5.2.1: the second scalar integration in the Dikin-step upper Taylor
bound evaluates to the logarithmic `ω_*` remainder. -/
private theorem integralMulSqDivEqOmegaStarAlongDikin
    {r u : ℝ} (hu : 0 ≤ u) (hMf_pos : 0 < (Mf : ℝ))
    (hden : ∀ t ∈ Set.Icc (0 : ℝ) u, 0 < 1 - (Mf : ℝ) * t * r) :
    ∫ t in 0..u, t * r ^ (2 : ℕ) / (1 - (Mf : ℝ) * t * r) =
      (1 / ((Mf : ℝ) ^ (2 : ℕ))) *
        (-(Mf : ℝ) * (u * r) - Real.log (1 - (Mf : ℝ) * (u * r))) := by
  let a : ℝ := (Mf : ℝ)
  have ha_ne : a ≠ 0 := ne_of_gt (by simpa [a] using hMf_pos)
  have hnum :
      ContinuousOn
        (fun t : ℝ ↦ (1 / (a ^ (2 : ℕ))) * (-(a * t * r) - Real.log (1 - a * t * r)))
        (Set.Icc (0 : ℝ) u) := by
    have hlog :
        ContinuousOn (fun t : ℝ ↦ Real.log (1 - a * t * r)) (Set.Icc (0 : ℝ) u) := by
      refine Real.continuousOn_log.comp ?_ ?_
      · exact (show Continuous (fun t : ℝ ↦ 1 - a * t * r) by continuity).continuousOn
      · intro t ht
        simpa [a, mul_assoc, mul_left_comm, mul_comm] using (hden t ht).ne'
    have hlin :
        ContinuousOn (fun t : ℝ ↦ -(a * t * r)) (Set.Icc (0 : ℝ) u) := by
      exact (show Continuous (fun t : ℝ ↦ -(a * t * r)) by continuity).continuousOn
    refine continuousOn_const.mul ?_
    exact hlin.sub hlog
  have hint :
      IntervalIntegrable
        (fun t : ℝ ↦ t * r ^ (2 : ℕ) / (1 - (Mf : ℝ) * t * r))
        MeasureTheory.volume 0 u := by
    have hcont :
        ContinuousOn
          (fun t : ℝ ↦ t * r ^ (2 : ℕ) / (1 - (Mf : ℝ) * t * r))
          (Set.Icc (0 : ℝ) u) := by
      refine (continuousOn_id.mul continuousOn_const).div ?_ ?_
      · exact (show Continuous (fun t : ℝ ↦ 1 - (Mf : ℝ) * t * r) by continuity).continuousOn
      · intro t ht
        exact (hden t ht).ne'
    exact hcont.intervalIntegrable_of_Icc hu
  have hderiv :
      ∀ t ∈ Set.Ioo (0 : ℝ) u,
        HasDerivAt
          (fun s : ℝ ↦
            (1 / (a ^ (2 : ℕ))) * (-(a * s * r) - Real.log (1 - a * s * r)))
          (t * r ^ (2 : ℕ) / (1 - a * t * r)) t := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) u := Set.mem_Icc_of_Ioo ht
    have harg_ne : 1 - a * t * r ≠ 0 := by
      simpa [a, mul_assoc, mul_left_comm, mul_comm] using (hden t ht').ne'
    have harg :
        HasDerivAt (fun s : ℝ ↦ 1 - a * s * r) (-(a * r)) t := by
      convert
        (hasDerivAt_const t (1 : ℝ)).sub ((((hasDerivAt_id t).const_mul a).mul_const r)) using 1
      ring
    have hlog :
        HasDerivAt (fun s : ℝ ↦ Real.log (1 - a * s * r))
          ((-(a * r)) / (1 - a * t * r)) t := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (Real.hasDerivAt_log harg_ne).comp t harg
    have hlin :
        HasDerivAt (fun s : ℝ ↦ -(a * s * r)) (-(a * r)) t := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        ((((hasDerivAt_id t).const_mul a).mul_const r).neg)
    have hbase :
        HasDerivAt
          (fun s : ℝ ↦ -(a * s * r) - Real.log (1 - a * s * r))
          (-(a * r) - ((-(a * r)) / (1 - a * t * r))) t := by
      exact hlin.sub hlog
    have hscaled :
        HasDerivAt
          (fun s : ℝ ↦
            (1 / (a ^ (2 : ℕ))) * (-(a * s * r) - Real.log (1 - a * s * r)))
          ((1 / (a ^ (2 : ℕ))) * (-(a * r) - ((-(a * r)) / (1 - a * t * r)))) t := by
      exact hbase.const_mul (1 / (a ^ (2 : ℕ)))
    have hslope :
        ((1 / (a ^ (2 : ℕ))) * (-(a * r) - ((-(a * r)) / (1 - a * t * r)))) =
          t * r ^ (2 : ℕ) / (1 - a * t * r) := by
      have hfrac :
          (1 - a * t * r)⁻¹ - 1 = (a * t * r) * (1 - a * t * r)⁻¹ := by
        field_simp [harg_ne]
        ring
      calc
        ((1 / (a ^ (2 : ℕ))) * (-(a * r) - ((-(a * r)) / (1 - a * t * r))))
            = (1 / (a ^ (2 : ℕ))) * (a * r) * ((1 - a * t * r)⁻¹ - 1) := by
                ring_nf
        _ = (1 / (a ^ (2 : ℕ))) * (a * r) * ((a * t * r) * (1 - a * t * r)⁻¹) := by
              rw [hfrac]
        _ = t * r ^ (2 : ℕ) / (1 - a * t * r) := by
              field_simp [ha_ne, harg_ne]
    exact hscaled.congr_deriv hslope
  have hftc :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hu hnum hderiv hint
  calc
    ∫ t in 0..u, t * r ^ (2 : ℕ) / (1 - (Mf : ℝ) * t * r)
        = ((1 / (a ^ (2 : ℕ))) * (-(a * u * r) - Real.log (1 - a * u * r))) -
            ((1 / (a ^ (2 : ℕ))) * (-(a * 0 * r) - Real.log (1 - a * 0 * r))) := by
              simpa [a, mul_assoc, mul_left_comm, mul_comm] using hftc
    _ = (1 / (a ^ (2 : ℕ))) * (-(a * u * r) - Real.log (1 - a * u * r)) := by
      simp
    _ = (1 / ((Mf : ℝ) ^ (2 : ℕ))) *
          (-(Mf : ℝ) * (u * r) - Real.log (1 - (Mf : ℝ) * (u * r))) := by
      simp [a, mul_assoc, mul_comm]

omit [FiniteDimensional ℝ E] in
/-- Helper for Lemma 5.2.1: every affine parameter `τ ∈ [0, 1]` produces the corresponding point
`x + τ • (y - x)` on `segment ℝ x y`. -/
private lemma segment_point_mem_segment
    {x y : E} {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    x + τ • (y - x) ∈ segment ℝ x y := by
  -- Rewrite the affine interpolation point into the canonical line-map description of the
  -- segment.
  rw [segment_eq_image_lineMap]
  refine ⟨τ, hτ, ?_⟩
  simp [AffineMap.lineMap_apply_module', add_comm]

/-- Helper for Lemma 5.2.1: every admissible Dikin step satisfies the owner-level upper Taylor
bound with remainder `ω_*`. -/
private theorem segmentHessianPairing_upper_of_memOpenDikinEllipsoid
    {x y : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ openDikinEllipsoid f x (1 / (Mf : ℝ)))
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    let h := y - x
    let r := ‖h‖[f; x]
    inner ℝ h (hessian f (x + τ • h) h) ≤
      r ^ (2 : ℕ) / (1 - (Mf : ℝ) * τ * r) ^ (2 : ℕ) := by
  dsimp
  let hself : IsSelfConcordantOnWith dom Mf f := inferInstance
  let h : E := y - x
  let r : ℝ := ‖h‖[f; x]
  let z : E := x + τ • h
  have hr_nonneg : 0 ≤ r := by
    simpa [h, r] using hessianLocalNorm_nonneg f x (y - x)
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [h, r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy
  have hz : z ∈ dom := by
    exact hself.convex_domain.segment_subset hx hy
      (segment_point_mem_segment (x := x) (y := y) hτ)
  have hz_norm : ‖z - x‖[f; x] = τ * r := by
    have hz_sub : z - x = τ • h := by
      dsimp [z, h]
      abel
    rw [hz_sub, hessianLocalNorm_smul_of_nonneg (f := f) (hself.hessian_isPositive hx) hτ.1]
  let rmid : ℝ := (r + 1 / (Mf : ℝ)) / 2
  have hr_lt_rmid : r < rmid := by
    dsimp [rmid]
    linarith
  have hrmid_lt : rmid < 1 / (Mf : ℝ) := by
    dsimp [rmid]
    linarith
  have hz_mem_rmid : z ∈ openDikinEllipsoid f x rmid := by
    rw [mem_openDikinEllipsoid_iff]
    have hz_norm_le_r : ‖z - x‖[f; x] ≤ r := by
      rw [hz_norm]
      simpa using mul_le_mul_of_nonneg_right hτ.2 hr_nonneg
    exact lt_of_le_of_lt hz_norm_le_r hr_lt_rmid
  have hupper :
      hessian f z ≤
        ((1 - (Mf : ℝ) * ‖z - x‖[f; x]) ^ (2 : ℕ))⁻¹ • hessian f x :=
    (hself.hessian_loewner_bounds_of_exact_local_radius hx hz hrmid_lt hz_mem_rmid).2
  have hgap_nonneg :
      0 ≤
        ((1 - (Mf : ℝ) * ‖z - x‖[f; x]) ^ (2 : ℕ))⁻¹ • hessian f x - hessian f z := by
    simpa [ContinuousLinearMap.le_def] using hupper
  have hgap_pos :
      (((1 - (Mf : ℝ) * ‖z - x‖[f; x]) ^ (2 : ℕ))⁻¹ • hessian f x - hessian f z).IsPositive :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).mp hgap_nonneg
  have hquad :
      0 ≤
        inner ℝ h
          ((((1 - (Mf : ℝ) * ‖z - x‖[f; x]) ^ (2 : ℕ))⁻¹ • hessian f x - hessian f z) h) :=
    hgap_pos.inner_nonneg_right h
  have hbase_sq : inner ℝ h (hessian f x h) = r ^ (2 : ℕ) := by
    symm
    simpa [h, r] using
      sq_hessianLocalNorm_eq_inner_of_nonneg
        (f := f) (z := x) (u := h) ((hself.hessian_isPositive hx).inner_nonneg_right h)
  have hrewrite :
      inner ℝ h
          ((((1 - (Mf : ℝ) * ‖z - x‖[f; x]) ^ (2 : ℕ))⁻¹ • hessian f x - hessian f z) h) =
        ((1 - (Mf : ℝ) * ‖z - x‖[f; x]) ^ (2 : ℕ))⁻¹ * inner ℝ h (hessian f x h) -
          inner ℝ h (hessian f z h) := by
    simp [inner_sub_right, inner_smul_right]
  rw [hrewrite] at hquad
  have hfactor :
      ((1 - (Mf : ℝ) * ‖z - x‖[f; x]) ^ (2 : ℕ))⁻¹ * inner ℝ h (hessian f x h) =
        r ^ (2 : ℕ) / (1 - (Mf : ℝ) * τ * r) ^ (2 : ℕ) := by
    rw [hbase_sq, hz_norm]
    simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  linarith

/-- Helper for Lemma 5.2.1: every admissible Dikin step with endpoint already known to lie in the
domain satisfies the owner-level upper Taylor bound with remainder `ω_*`. -/
private theorem taylorUpperBound_withSelfConcordantOmegaStar_of_memOpenDikinEllipsoid
    {x y : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy : y ∈ openDikinEllipsoid f x (1 / (Mf : ℝ))) :
    let r := ‖y - x‖[f; x]
    let rawTau : Set.Iio (1 : ℝ) := selfConcordantOmegaStarArg Mf r
      (mf_mul_lt_one_of_lt_inv <| by simpa [r] using
        (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy)
    f y ≤
      f x + inner ℝ (∇ f x) (y - x) +
        (1 / ((Mf : ℝ) ^ (2 : ℕ))) * ω_* rawTau := by
  dsimp
  let hself : IsSelfConcordantOnWith dom Mf f := inferInstance
  let h : E := y - x
  let r : ℝ := ‖h‖[f; x]
  let φ : ℝ → ℝ := fun u ↦ f (x + u • h)
  let γ : ℝ → ℝ := fun u ↦ inner ℝ (∇ f (x + u • h)) h
  let ψ : ℝ → ℝ := fun u ↦ inner ℝ (∇ f (x + u • h) - ∇ f x) h
  let Φ : ℝ → ℝ := fun u ↦ f (x + u • h) - f x - u * inner ℝ (∇ f x) h
  let rawTau : Set.Iio (1 : ℝ) := selfConcordantOmegaStarArg Mf r
    (mf_mul_lt_one_of_lt_inv <| by simpa [r] using
      (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy)
  have hr : r < 1 / (Mf : ℝ) := by
    simpa [h, r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy
  have hr_nonneg : 0 ≤ r := by
    simpa [h, r] using hessianLocalNorm_nonneg f x (y - x)
  have hMf_pos : 0 < (Mf : ℝ) := by
    have hMf_nonneg : 0 ≤ (Mf : ℝ) := by exact_mod_cast Mf.2
    by_contra hMf_nonpos
    have hMf_eq_zero : (Mf : ℝ) = 0 := le_antisymm (le_of_not_gt hMf_nonpos) hMf_nonneg
    have hr_neg : r < 0 := by
      simpa [hMf_eq_zero] using hr
    linarith
  have hsegment :
      ∀ {τ : ℝ}, τ ∈ Set.Icc (0 : ℝ) 1 → x + τ • h ∈ dom := by
    intro τ hτ
    exact hself.convex_domain.segment_subset hx hy
      (segment_point_mem_segment (x := x) (y := y) hτ)
  have hden_on :
      ∀ {u t : ℝ}, u ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) u →
        0 < 1 - (Mf : ℝ) * t * r := by
    intro u t hu ht
    have htr_le : t * r ≤ r := by
      have htle1 : t ≤ 1 := le_trans ht.2 hu.2
      simpa using mul_le_mul_of_nonneg_right htle1 hr_nonneg
    have htr_lt : t * r < 1 / (Mf : ℝ) := lt_of_le_of_lt htr_le hr
    have hmfr_lt : (Mf : ℝ) * (t * r) < 1 := mf_mul_lt_one_of_lt_inv (Mf := Mf) htr_lt
    simpa [mul_assoc, mul_left_comm, mul_comm] using sub_pos.2 hmfr_lt
  let θ : ℝ → ℝ := fun u ↦ inner ℝ h (hessian f (x + u • h) h)
  have segment_hessian_quadratic_upper :
      ∀ {u : ℝ}, u ∈ Set.Ioo (0 : ℝ) 1 →
        θ u ≤ r ^ (2 : ℕ) / (1 - (Mf : ℝ) * u * r) ^ (2 : ℕ) := by
    intro u hu
    have hθ :=
      segmentHessianPairing_upper_of_memOpenDikinEllipsoid
        (dom := dom) (Mf := Mf) (f := f) hx hy hxy (τ := u) (Set.mem_Icc_of_Ioo hu)
    simpa [θ, h, r, ContinuousLinearMap.map_sub] using hθ
  have segment_gradient_line_continuousOn :
      ContinuousOn γ (Set.Icc (0 : ℝ) 1) := by
    intro u hu
    have hxu : x + u • h ∈ dom := hsegment hu
    have hcont : ContinuousAt γ u :=
      (scalarized_gradient_line_hasDerivAt
        (hself := hself) (z := x) (d := h) (w := h) hxu).continuousAt
    exact hcont.continuousWithinAt
  have segment_hessian_pairing_intervalIntegrable :
      ∀ {u : ℝ}, u ∈ Set.Icc (0 : ℝ) 1 →
        IntervalIntegrable θ MeasureTheory.volume 0 u := by
    intro u hu
    have hcont :
        ContinuousOn θ (Set.Icc (0 : ℝ) u) := by
      intro t ht
      have hxt : x + t • h ∈ dom := hsegment ⟨ht.1, le_trans ht.2 hu.2⟩
      have hhess_cont : ContinuousAt (hessian f) (x + t • h) := by
        exact (hessian_continuousOn (Mf := Mf) (f := f)).continuousAt
          (hself.isOpen_domain.mem_nhds hxt)
      have hline_cont : ContinuousAt (fun s : ℝ ↦ x + s • h) t :=
        (line_hasDerivAt x h t).continuousAt
      have hhess_line : ContinuousAt (fun s : ℝ ↦ hessian f (x + s • h)) t := by
        exact ContinuousAt.comp hhess_cont hline_cont
      let φh : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) h
      have happly_line : ContinuousAt (fun s : ℝ ↦ hessian f (x + s • h) h) t := by
        simpa using
          ContinuousAt.comp ((ContinuousLinearMap.apply ℝ E h).continuous.continuousAt) hhess_line
      have hinner_cont : ContinuousAt θ t := by
        simpa [θ, φh, InnerProductSpace.toDual_apply_apply, real_inner_comm] using
          ContinuousAt.comp φh.continuous.continuousAt happly_line
      exact hinner_cont.continuousWithinAt
    exact hcont.intervalIntegrable_of_Icc hu.1
  have segment_gradient_pairing_eq_integral :
      ∀ {u : ℝ}, u ∈ Set.Icc (0 : ℝ) 1 →
        ψ u = ∫ s in 0..u, θ s := by
    intro u hu
    have hg_cont :
        ContinuousOn γ (Set.Icc (0 : ℝ) u) :=
      segment_gradient_line_continuousOn.mono
        (by
          intro t ht
          exact ⟨ht.1, le_trans ht.2 hu.2⟩)
    have hderiv :
        ∀ t ∈ Set.Ioo (0 : ℝ) u, HasDerivAt γ (θ t) t := by
      intro t ht
      have hxt : x + t • h ∈ dom :=
        hsegment ⟨ht.1.le, le_of_lt (lt_of_lt_of_le ht.2 hu.2)⟩
      simpa [γ, θ, real_inner_comm] using
        (scalarized_gradient_line_hasDerivAt
          (hself := hself) (z := x) (d := h) (w := h) hxt)
    have hftc :
        ∫ s in 0..u, θ s = γ u - γ 0 := by
      simpa using
        intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
          hu.1 hg_cont hderiv (segment_hessian_pairing_intervalIntegrable hu)
    calc
      ψ u = γ u - γ 0 := by
        simp [ψ, γ, inner_sub_left]
      _ = ∫ s in 0..u, θ s := by
        symm
        exact hftc
  have segment_gradient_pairing_upper :
      ∀ {u : ℝ}, u ∈ Set.Icc (0 : ℝ) 1 →
        ψ u ≤ u * r ^ (2 : ℕ) / (1 - (Mf : ℝ) * u * r) := by
    intro u hu
    have hint_upper :
        IntervalIntegrable
          (fun t : ℝ ↦ r ^ (2 : ℕ) / (1 - (Mf : ℝ) * t * r) ^ (2 : ℕ))
          MeasureTheory.volume 0 u := by
      have hcont :
          ContinuousOn
            (fun t : ℝ ↦ r ^ (2 : ℕ) / (1 - (Mf : ℝ) * t * r) ^ (2 : ℕ))
            (Set.Icc (0 : ℝ) u) := by
        have hden_cont : Continuous (fun t : ℝ ↦ (1 - (Mf : ℝ) * t * r) ^ (2 : ℕ)) := by
          continuity
        refine continuousOn_const.div ?_ ?_
        · exact hden_cont.continuousOn
        · intro t ht
          exact pow_ne_zero 2 (hden_on hu ht).ne'
      exact hcont.intervalIntegrable_of_Icc hu.1
    have hmono :
        ∫ s in 0..u, θ s ≤
          ∫ s in 0..u, r ^ (2 : ℕ) / (1 - (Mf : ℝ) * s * r) ^ (2 : ℕ) := by
      refine intervalIntegral.integral_mono_on_of_le_Ioo hu.1
        (segment_hessian_pairing_intervalIntegrable hu) hint_upper ?_
      intro s hs
      exact segment_hessian_quadratic_upper (u := s) ⟨hs.1, lt_of_lt_of_le hs.2 hu.2⟩
    calc
      ψ u = ∫ s in 0..u, θ s := segment_gradient_pairing_eq_integral hu
      _ ≤ ∫ s in 0..u, r ^ (2 : ℕ) / (1 - (Mf : ℝ) * s * r) ^ (2 : ℕ) := hmono
      _ = u * r ^ (2 : ℕ) / (1 - (Mf : ℝ) * u * r) := by
        exact integralSqDivEqScaledSqDivSub (Mf := Mf) hu.1 (hden := fun t ht ↦ hden_on hu ht)
  have segment_value_line_continuousOn :
      ContinuousOn φ (Set.Icc (0 : ℝ) 1) := by
    intro u hu
    have hxu : x + u • h ∈ dom := hsegment hu
    have hφ_cont : ContinuousAt φ u := by
      simpa [φ] using
        (value_line_hasDerivAt (hself := hself) (z := x) (d := h) hxu).continuousAt
    exact hφ_cont.continuousWithinAt
  have segment_gradient_pairing_continuousOn :
      ContinuousOn ψ (Set.Icc (0 : ℝ) 1) := by
    have hconst : ContinuousOn (fun _ : ℝ ↦ inner ℝ (∇ f x) h) (Set.Icc (0 : ℝ) 1) :=
      continuousOn_const
    simpa [ψ, γ, inner_sub_left] using segment_gradient_line_continuousOn.sub hconst
  have segment_value_remainder_eq_integral :
      ∀ {u : ℝ}, u ∈ Set.Icc (0 : ℝ) 1 →
        Φ u = ∫ s in 0..u, ψ s := by
    intro u hu
    have hφ_cont :
        ContinuousOn φ (Set.Icc (0 : ℝ) u) :=
      segment_value_line_continuousOn.mono
        (by
          intro t ht
          exact ⟨ht.1, le_trans ht.2 hu.2⟩)
    have hderiv :
        ∀ t ∈ Set.Ioo (0 : ℝ) u, HasDerivAt φ (γ t) t := by
      intro t ht
      have hxt : x + t • h ∈ dom :=
        hsegment ⟨ht.1.le, le_of_lt (lt_of_lt_of_le ht.2 hu.2)⟩
      simpa [φ, γ] using (value_line_hasDerivAt (hself := hself) (z := x) (d := h) hxt)
    have hintγ :
        IntervalIntegrable γ MeasureTheory.volume 0 u := by
      exact
        (segment_gradient_line_continuousOn.mono
          (by
            intro t ht
            exact ⟨ht.1, le_trans ht.2 hu.2⟩)).intervalIntegrable_of_Icc hu.1
    have hconst :
        IntervalIntegrable (fun _ : ℝ ↦ γ 0) MeasureTheory.volume 0 u :=
      intervalIntegrable_const
    have hftc :
        ∫ s in 0..u, γ s = φ u - φ 0 := by
      simpa using
        intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hu.1 hφ_cont hderiv hintγ
    calc
      Φ u = φ u - φ 0 - u * γ 0 := by
        simp [Φ, φ, γ]
      _ = (∫ s in 0..u, γ s) - u * γ 0 := by
        rw [hftc]
      _ = (∫ s in 0..u, γ s) - (∫ s in 0..u, γ 0) := by
        rw [intervalIntegral.integral_const]
        ring
      _ = (∫ s in 0..u, (γ s - γ 0)) := by
        symm
        simpa using (intervalIntegral.integral_sub hintγ hconst)
      _ = (∫ s in 0..u, ψ s) := by
        refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
        intro s
        simp [ψ, γ, inner_sub_left]
  have segment_value_upper :
      ∀ {u : ℝ}, u ∈ Set.Icc (0 : ℝ) 1 →
        Φ u ≤
          (1 / ((Mf : ℝ) ^ (2 : ℕ))) *
            (-(Mf : ℝ) * (u * r) - Real.log (1 - (Mf : ℝ) * (u * r))) := by
    intro u hu
    have hintψ :
        IntervalIntegrable ψ MeasureTheory.volume 0 u := by
      exact
        (segment_gradient_pairing_continuousOn.mono
          (by
            intro t ht
            exact ⟨ht.1, le_trans ht.2 hu.2⟩)).intervalIntegrable_of_Icc hu.1
    have hint_upper :
        IntervalIntegrable
          (fun t : ℝ ↦ t * r ^ (2 : ℕ) / (1 - (Mf : ℝ) * t * r))
          MeasureTheory.volume 0 u := by
      have hcont :
          ContinuousOn
            (fun t : ℝ ↦ t * r ^ (2 : ℕ) / (1 - (Mf : ℝ) * t * r))
            (Set.Icc (0 : ℝ) u) := by
        have hden_cont : Continuous (fun t : ℝ ↦ 1 - (Mf : ℝ) * t * r) := by
          exact continuous_const.sub ((continuous_const.mul continuous_id).mul continuous_const)
        refine (continuousOn_id.mul continuousOn_const).div ?_ ?_
        · exact hden_cont.continuousOn
        · intro t ht
          exact (hden_on hu ht).ne'
      exact hcont.intervalIntegrable_of_Icc hu.1
    have hmono :
        ∫ s in 0..u, ψ s ≤
          ∫ s in 0..u, s * r ^ (2 : ℕ) / (1 - (Mf : ℝ) * s * r) := by
      refine intervalIntegral.integral_mono_on hu.1 hintψ hint_upper ?_
      intro s hs
      exact segment_gradient_pairing_upper (u := s) ⟨hs.1, le_trans hs.2 hu.2⟩
    calc
      Φ u = ∫ s in 0..u, ψ s := segment_value_remainder_eq_integral hu
      _ ≤ ∫ s in 0..u, s * r ^ (2 : ℕ) / (1 - (Mf : ℝ) * s * r) := hmono
      _ =
          (1 / ((Mf : ℝ) ^ (2 : ℕ))) *
            (-(Mf : ℝ) * (u * r) - Real.log (1 - (Mf : ℝ) * (u * r))) := by
          exact integralMulSqDivEqOmegaStarAlongDikin
            (Mf := Mf) hu.1 hMf_pos (hden := fun t ht ↦ hden_on hu ht)
  have hvalue_endpoint_raw := segment_value_upper (u := 1) ⟨by norm_num, le_rfl⟩
  have hPhi1 : Φ 1 = f y - f x - inner ℝ (∇ f x) h := by
    dsimp [Φ, φ]
    have hy_line : x + (1 : ℝ) • h = y := by
      dsimp [h]
      simp [sub_eq_add_neg]
    rw [hy_line]
    ring
  have hrem :
      f y - f x - inner ℝ (∇ f x) h ≤
        (1 / ((Mf : ℝ) ^ (2 : ℕ))) *
          (-(Mf : ℝ) * r - Real.log (1 - (Mf : ℝ) * r)) := by
    simpa [hPhi1, one_mul] using hvalue_endpoint_raw
  have hmain :
      f y ≤
        f x + inner ℝ (∇ f x) h +
          (1 / ((Mf : ℝ) ^ (2 : ℕ))) *
            (-(Mf : ℝ) * r - Real.log (1 - (Mf : ℝ) * r)) := by
    linarith
  have hrawTau : (rawTau : ℝ) = (Mf : ℝ) * r := by
    simp [rawTau]
  calc
    f y ≤
        f x + inner ℝ (∇ f x) h +
          (1 / ((Mf : ℝ) ^ (2 : ℕ))) *
            (-(Mf : ℝ) * r - Real.log (1 - (Mf : ℝ) * r)) := hmain
    _ =
        f x + inner ℝ (∇ f x) h +
          (1 / ((Mf : ℝ) ^ (2 : ℕ))) * ω_* rawTau := by
            rw [selfConcordantOmegaStar_apply, hrawTau]
            ring

/-- Helper for Lemma 5.2.1: the intermediate Newton endpoint satisfies the self-concordant
Taylor upper bound with the canonical `ω_*` remainder. -/
private theorem intermediateStepTaylorUpperBoundWithOmegaStar
    {x : E} (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0)
    (hxPlus :
      let xPlus := selfConcordantNewtonNextPoint f Mf .intermediate x hx hH
      xPlus ∈ dom)
    (hMf : Mf ≠ 0) :
    let xPlus := selfConcordantNewtonNextPoint f Mf .intermediate x hx hH
    let rawTau : Set.Iio (1 : ℝ) :=
      selfConcordantOmegaStarArg Mf ‖xPlus - x‖[f; x]
        (mf_mul_lt_one_of_lt_inv <|
          by
            simpa [xPlus] using
              (mem_openDikinEllipsoid_iff f x xPlus (1 / (Mf : ℝ))).1
                (intermediateStep_mem_openDikinEllipsoid_of_ne_zero
                  (Mf := Mf) (f := f) hx hH hMf))
    f xPlus ≤
      f x + inner ℝ (∇ f x) (xPlus - x) +
        (1 / ((Mf : ℝ) ^ (2 : ℕ))) * ω_* rawTau := by
  dsimp
  let xPlus := selfConcordantNewtonNextPoint f Mf .intermediate x hx hH
  let rawTau : Set.Iio (1 : ℝ) :=
    selfConcordantOmegaStarArg Mf ‖xPlus - x‖[f; x]
      (mf_mul_lt_one_of_lt_inv <|
        by
          simpa [xPlus] using
            (mem_openDikinEllipsoid_iff f x xPlus (1 / (Mf : ℝ))).1
              (intermediateStep_mem_openDikinEllipsoid_of_ne_zero
                (Mf := Mf) (f := f) hx hH hMf))
  have hxPlus_mem : xPlus ∈ openDikinEllipsoid f x (1 / (Mf : ℝ)) := by
    -- The intermediate update stays inside the admissible Dikin ellipsoid.
    simpa [xPlus] using
      (intermediateStep_mem_openDikinEllipsoid_of_ne_zero
        (Mf := Mf) (f := f) hx hH hMf)
  have hxPlus_dom : xPlus ∈ dom := by
    simpa [xPlus] using hxPlus
  -- Specialize the generic Dikin-step Taylor bound to the intermediate endpoint.
  simpa [xPlus, rawTau] using
    (taylorUpperBound_withSelfConcordantOmegaStar_of_memOpenDikinEllipsoid
      (Mf := Mf) (f := f) hx hxPlus_dom hxPlus_mem)

private theorem intermediateStepPositiveExactScalarDrop
    {x : E} (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0)
    (hxPlus :
      let xPlus := selfConcordantNewtonNextPoint f Mf .intermediate x hx hH
      xPlus ∈ dom)
    (hMf : Mf ≠ 0) :
    let δ := NewtonDecrement.ofDetNeZero Mf f hx hH
    let xPlus := selfConcordantNewtonNextPoint f Mf .intermediate x hx hH
    let t : ℝ := (Mf : ℝ) * δ
    f x - f xPlus ≥
      (1 / (Mf : ℝ) ^ (2 : ℕ)) *
        (t * (1 + t) ^ (2 : ℕ) / (1 + t + t ^ (2 : ℕ)) -
          Real.log (1 + t + t ^ (2 : ℕ))) := by
  dsimp
  let δ := NewtonDecrement.ofDetNeZero Mf f hx hH
  let xPlus := selfConcordantNewtonNextPoint f Mf .intermediate x hx hH
  let t : ℝ := (Mf : ℝ) * δ
  let rawTau : Set.Iio (1 : ℝ) :=
    selfConcordantOmegaStarArg Mf ‖xPlus - x‖[f; x]
      (mf_mul_lt_one_of_lt_inv <|
        by
          simpa [xPlus] using
            (mem_openDikinEllipsoid_iff f x xPlus (1 / (Mf : ℝ))).1
              (intermediateStep_mem_openDikinEllipsoid_of_ne_zero
                (Mf := Mf) (f := f) hx hH hMf))
  have hupper :
      f xPlus ≤
        f x + inner ℝ (∇ f x) (xPlus - x) +
          (1 / ((Mf : ℝ) ^ (2 : ℕ))) * ω_* rawTau := by
    -- The endpoint Taylor upper bound is now available directly on the intermediate step.
    simpa [xPlus, rawTau] using
      (intermediateStepTaylorUpperBoundWithOmegaStar
        (Mf := Mf) (f := f) hx hH hxPlus hMf)
  have hpair :
      inner ℝ (∇ f x) (xPlus - x) =
        -((1 / (Mf : ℝ) ^ (2 : ℕ)) *
          (t ^ (2 : ℕ) * (1 + t) / (1 + t + t ^ (2 : ℕ)))) := by
    -- Rewrite the affine Taylor term in the normalized scalar variable.
    simpa [δ, xPlus, t] using
      (intermediateStepGradientContribution_eq
        (Mf := Mf) (f := f) hx hH hMf)
  have homega :
      (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω_* rawTau =
        (1 / (Mf : ℝ) ^ (2 : ℕ)) *
          (Real.log (1 + t + t ^ (2 : ℕ)) -
            t * (1 + t) / (1 + t + t ^ (2 : ℕ))) := by
    -- Rewrite only the evaluated `ω_*` remainder, not the subtype owner itself.
    simpa [δ, xPlus, t, rawTau] using
      (intermediateStepOmegaStarContribution_eq
        (Mf := Mf) (f := f) hx hH hMf)
  have hupper' := hupper
  -- Put the upper bound on the common normalized scalar surface.
  rw [hpair, homega] at hupper'
  have hscalar :
      (-(1 / (Mf : ℝ) ^ (2 : ℕ)) *
          (t ^ (2 : ℕ) * (1 + t) / (1 + t + t ^ (2 : ℕ)))) +
        (1 / (Mf : ℝ) ^ (2 : ℕ)) *
          (Real.log (1 + t + t ^ (2 : ℕ)) -
            t * (1 + t) / (1 + t + t ^ (2 : ℕ))) =
      -((1 / (Mf : ℝ) ^ (2 : ℕ)) *
        (t * (1 + t) ^ (2 : ℕ) / (1 + t + t ^ (2 : ℕ)) -
          Real.log (1 + t + t ^ (2 : ℕ)))) := by
    -- Collect the affine and remainder terms into the exact scalar drop formula.
    ring
  have hupper'' :
      f xPlus ≤
        f x -
          (1 / (Mf : ℝ) ^ (2 : ℕ)) *
            (t * (1 + t) ^ (2 : ℕ) / (1 + t + t ^ (2 : ℕ)) -
              Real.log (1 + t + t ^ (2 : ℕ))) := by
    linarith [hupper', hscalar]
  linarith

/-- Helper for Lemma 5.2.1: the remaining positive-parameter branch is the scalar inequality
obtained after the self-concordant Taylor upper bound is rewritten in the intermediate-step
normal form. -/
private theorem intermediateStep_positiveScalarLowerBound
    {x : E} (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0)
    (hxPlus :
      let xPlus := selfConcordantNewtonNextPoint f Mf .intermediate x hx hH
      xPlus ∈ dom)
    (hMf : Mf ≠ 0) :
    let δ := NewtonDecrement.ofDetNeZero Mf f hx hH
    let xPlus := selfConcordantNewtonNextPoint f Mf .intermediate x hx hH
    f x - f xPlus ≥
      δ ^ 2 / (2 * (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ 2 * δ ^ 2)) +
        (Mf : ℝ) * δ ^ 3 / (2 * (1 + (Mf : ℝ) * δ) * (3 + 2 * (Mf : ℝ) * δ)) := by
  dsimp
  let δ := NewtonDecrement.ofDetNeZero Mf f hx hH
  let xPlus := selfConcordantNewtonNextPoint f Mf .intermediate x hx hH
  let t : ℝ := (Mf : ℝ) * δ
  have hδ_nonneg : 0 ≤ δ := by
    simpa [δ] using NewtonDecrement.ofDetNeZero_nonneg Mf f hx hH
  have hMf_pos_nn : 0 < Mf := lt_of_le_of_ne Mf.2 (Ne.symm hMf)
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact_mod_cast hMf_pos_nn
  have hMf_ne : (Mf : ℝ) ≠ 0 := ne_of_gt hMf_pos
  have hexact :
      f x - f xPlus ≥
        (1 / (Mf : ℝ) ^ (2 : ℕ)) *
          (t * (1 + t) ^ (2 : ℕ) / (1 + t + t ^ (2 : ℕ)) -
            Real.log (1 + t + t ^ (2 : ℕ))) := by
    -- First rewrite the positive branch to the exact one-variable drop formula.
    simpa [δ, xPlus, t] using
      (intermediateStepPositiveExactScalarDrop
        (Mf := Mf) (f := f) hx hH hxPlus hMf)
  have hgap :
      t ^ 2 / (2 * (1 + t + t ^ (2 : ℕ))) +
          t ^ 3 / (2 * (1 + t) * (3 + 2 * t)) ≤
        t * (1 + t) ^ (2 : ℕ) / (1 + t + t ^ (2 : ℕ)) -
          Real.log (1 + t + t ^ (2 : ℕ)) := by
    -- The remaining work is the pure scalar inequality on `[0, ∞)`.
    apply intermediateStepPositiveScalarGap_nonneg
    dsimp [t]
    exact mul_nonneg Mf.2 hδ_nonneg
  have hscaledGap :
      (1 / (Mf : ℝ) ^ (2 : ℕ)) *
          (t ^ 2 / (2 * (1 + t + t ^ (2 : ℕ))) +
            t ^ 3 / (2 * (1 + t) * (3 + 2 * t))) ≤
        (1 / (Mf : ℝ) ^ (2 : ℕ)) *
          (t * (1 + t) ^ (2 : ℕ) / (1 + t + t ^ (2 : ℕ)) -
            Real.log (1 + t + t ^ (2 : ℕ))) := by
    -- Scale the scalar inequality by the positive factor `M_f⁻²`.
    exact mul_le_mul_of_nonneg_left hgap (by positivity)
  have hrational :
      (1 / (Mf : ℝ) ^ (2 : ℕ)) *
          (t ^ 2 / (2 * (1 + t + t ^ (2 : ℕ))) +
            t ^ 3 / (2 * (1 + t) * (3 + 2 * t))) =
        δ ^ 2 / (2 * (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ 2 * δ ^ 2)) +
          (Mf : ℝ) * δ ^ 3 /
            (2 * (1 + (Mf : ℝ) * δ) * (3 + 2 * (Mf : ℝ) * δ)) := by
    -- Transport the normalized scalar lower bound back to the original variables.
    dsimp [t]
    field_simp [hMf_ne]
  rw [← hrational]
  linarith

/-- Helper for Lemma 5.2.1: in the degenerate branch `M_f = 0`, the intermediate step is the
undamped Newton step and the value drop should reduce to the exact quadratic decrement
`δ ^ 2 / 2`. -/
private theorem zeroMf_intermediateStep_exactQuadraticDrop
    {x : E} (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0)
    (hxPlus :
      let xPlus := selfConcordantNewtonNextPoint f Mf .intermediate x hx hH
      xPlus ∈ dom)
    (hMf : Mf = 0) :
    let δ := NewtonDecrement.ofDetNeZero Mf f hx hH
    let xPlus := selfConcordantNewtonNextPoint f Mf .intermediate x hx hH
    f x - f xPlus = δ ^ 2 / 2 := by
  dsimp
  let δ := NewtonDecrement.ofDetNeZero Mf f hx hH
  let xPlus := selfConcordantNewtonNextPoint f Mf .intermediate x hx hH
  let v : E := (hessian f x).inverse (∇ f x)
  let hInv : (hessian f x).IsInvertible := hessian_isInvertible_of_det_ne_zero hH
  have hxPlus_mem : xPlus ∈ dom := by
    simpa [xPlus] using hxPlus
  have hxPlus_model : f xPlus = secondOrderTaylorModelAt f x xPlus := by
    simpa [xPlus] using
      (zeroSelfConcordant_eq_secondOrderTaylorModelAt
        (dom := dom) (Mf := Mf) (f := f) (x := x) (y := xPlus) hMf hx hxPlus_mem)
  have hstep_eq :
      selfConcordantNewtonStepSize f Mf .intermediate x hx hH = 1 := by
    -- The intermediate-step shift vanishes when `M_f = 0`.
    rw [show
        selfConcordantNewtonStepSize f Mf .intermediate x hx hH =
          (1 + (Mf : ℝ) * δ) /
            (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ)) by
      simpa [δ] using (intermediateStep_stepSize_eq (Mf := Mf) (f := f) hx hH)]
    simp [hMf]
  have hsub : xPlus - x = -v := by
    -- The intermediate step becomes the full Newton step when the damping shift is zero.
    rw [show xPlus - x =
        -(selfConcordantNewtonStepSize f Mf .intermediate x hx hH • v) by
      simpa [xPlus, v] using (intermediateStep_sub_eq_neg_smul (Mf := Mf) (f := f) hx hH)]
    simp [hstep_eq, v]
  have hq_nonneg : 0 ≤ inner ℝ (∇ f x) v := by
    simpa [v] using
      (inverseHessianGradientPairing_nonneg (dom := dom) (Mf := Mf) (f := f)
        (inferInstance : IsSelfConcordantOnWith dom Mf f) hx hH)
  have hq_eq : inner ℝ (∇ f x) v = δ ^ (2 : ℕ) := by
    -- The inverse-Hessian pairing is exactly the squared Newton decrement.
    calc
      inner ℝ (∇ f x) v = (Real.sqrt (inner ℝ (∇ f x) v)) ^ (2 : ℕ) := by
        symm
        simpa using Real.sq_sqrt hq_nonneg
      _ = δ ^ (2 : ℕ) := by
        rw [show Real.sqrt (inner ℝ (∇ f x) v) = δ by
          simpa [δ, v] using (NewtonDecrement.ofDetNeZero_def Mf f hx hH).symm]
  have hv_eq : hessian f x v = ∇ f x := hInv.self_apply_inverse (∇ f x)
  -- Evaluate the exact quadratic Taylor model at the undamped Newton step.
  calc
    f x - f xPlus = f x - secondOrderTaylorModelAt f x xPlus := by rw [hxPlus_model]
    _ =
        -(inner ℝ (∇ f x) (xPlus - x) +
          (1 / 2 : ℝ) * inner ℝ (hessian f x (xPlus - x)) (xPlus - x)) := by
            rw [secondOrderTaylorModelAt_apply]
            ring
    _ = δ ^ 2 / 2 := by
      rw [hsub, ContinuousLinearMap.map_neg]
      simp [hv_eq, hq_eq]
      ring

private theorem zeroMf_intermediateStep_value_drop
    {x : E} (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0)
    (hxPlus :
      let xPlus := selfConcordantNewtonNextPoint f Mf .intermediate x hx hH
      xPlus ∈ dom)
    (hMf : Mf = 0) :
    let δ := NewtonDecrement.ofDetNeZero Mf f hx hH
    let xPlus := selfConcordantNewtonNextPoint f Mf .intermediate x hx hH
    f x - f xPlus ≥
      δ ^ 2 / (2 * (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ 2 * δ ^ 2)) +
        (Mf : ℝ) * δ ^ 3 / (2 * (1 + (Mf : ℝ) * δ) * (3 + 2 * (Mf : ℝ) * δ)) := by
  -- Replace `f` by its exact quadratic Taylor model and simplify the zero-parameter target.
  simpa [hMf] using
    (zeroMf_intermediateStep_exactQuadraticDrop
      (Mf := Mf) (f := f) hx hH hxPlus hMf).ge

-- Semantic search note: `lean_leansearch` did not return a useful analogue for this Chapter 5
-- owner; local precedent from `Definition_5_2_1` and `Theorem_5_2_2/Common` shows that one-step
-- endpoint estimates must assume the successor point stays in `dom`.
-- Proof sketch: apply the self-concordant upper Taylor bound to the intermediate Newton update
-- `x_{k+1} = x_k - (1 + ξ_k)⁻¹ [∇²f(x_k)]⁻¹ ∇f(x_k)` with
-- `ξ_k = M_f² λ_k² / (1 + M_f λ_k)`, then rewrite the resulting `ω_*` term using the rational
-- lower bound from Lemma 5.1.5 and simplify the scalar expression exactly as in the textbook.
-- The one-step form needs the endpoint side condition `x₊ ∈ dom`; the iterate-level source lemma
-- obtains it from the method data.
/-- The intermediate self-concordant Newton step decreases the objective by at least the explicit
rational function of the Newton decrement. -/
theorem selfConcordant_intermediateNewtonStep_value_drop_lower_bound
    (Mf : NNReal) [IsSelfConcordantOnWith dom Mf f] {x : E}
    (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0)
    (hxPlus :
      let xPlus := selfConcordantNewtonNextPoint f Mf .intermediate x hx hH
      xPlus ∈ dom) :
    let δ := NewtonDecrement.ofDetNeZero Mf f hx hH
    let xPlus := selfConcordantNewtonNextPoint f Mf .intermediate x hx hH
    f x - f xPlus ≥
      δ ^ 2 / (2 * (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ 2 * δ ^ 2)) +
        (Mf : ℝ) * δ ^ 3 / (2 * (1 + (Mf : ℝ) * δ) * (3 + 2 * (Mf : ℝ) * δ)) := by
  dsimp
  -- Split the proof into the rigid zero-parameter branch and the positive-parameter branch.
  by_cases hMf : Mf = 0
  · simpa [hMf] using
      zeroMf_intermediateStep_value_drop (Mf := Mf) (f := f) hx hH hxPlus hMf
  · simpa using
      intermediateStep_positiveScalarLowerBound (Mf := Mf) (f := f) hx hH hxPlus hMf

-- Proof sketch: specialize `selfConcordant_intermediateNewtonStep_value_drop_lower_bound` to the
-- iterate `x_k`, then rewrite the successor `x_{k+1}` through the canonical one-step owner
-- `selfConcordantNewtonNextPoint`. The source-side feasibility of `x_{k+1}` is exactly the method
-- field `hmethod.iterates_mem (k + 1)`.
/-- Lemma 5.2.1: along the intermediate self-concordant Newton method `(5.2.1)C`, the objective
drop from `x_k` to `x_{k+1}` is bounded below by the explicit rational function of the Newton
decrement `λ_k`. This is the textbook inequality `(5.2.2)`. -/
lemma intermediateNewton_value_drop_lower_bound
    {x0 : E}
    (method : DampedNewton.Method f x0)
    (hmethod : method.IsSelfConcordant dom Mf .intermediate)
    (k : ℕ) :
    let δ :=
      NewtonDecrement.ofDetNeZero Mf f (hmethod.iterates_mem k) (method.hessian_nondegenerate k)
    f (method k) - f (method (k + 1)) ≥
      δ ^ 2 / (2 * (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ 2 * δ ^ 2)) +
        (Mf : ℝ) * δ ^ 3 / (2 * (1 + (Mf : ℝ) * δ) * (3 + 2 * (Mf : ℝ) * δ)) := by
  dsimp
  -- Apply the one-step theorem at the `k`th iterate and rewrite the successor canonically.
  simpa [hmethod.succ_eq_nextPoint k] using
    selfConcordant_intermediateNewtonStep_value_drop_lower_bound
      (Mf := Mf) (f := f)
      (x := method k)
      (hx := hmethod.iterates_mem k)
      (hH := method.hessian_nondegenerate k)
      (hxPlus := by
        simpa [hmethod.succ_eq_nextPoint k] using hmethod.iterates_mem (k + 1))

end
