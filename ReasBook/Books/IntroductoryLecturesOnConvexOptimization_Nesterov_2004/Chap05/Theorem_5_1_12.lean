/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.FirstOrderTaylorModel
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_17
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_4_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_29
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_12
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_20
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_21
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Example_5_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Lemma_5_1_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Corollary_5_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_1

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped DikinEllipsoidNotation Gradient HessianDualLocalNorm HessianLocalNorm
  SelfConcordantAuxiliaryFunction

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {dom : Set E} {Mf : NNReal} {f : E → ℝ}
variable [IsSelfConcordantOnWith dom Mf f] [HasPositiveDefiniteHessianOn dom f]

/- Theorem 5.1.12 lies in the Chapter 5 self-concordance / dual-local-norm domain.

Sampled owner declarations:
* `HasPositiveDefiniteHessianOn` from `Definition_5_0_23`, the chapter owner for the
  positive-definite-Hessian regime in which the dual local norm is evaluated from domain
  membership alone;
* `HessianDualLocalNorm.ofPosDefMem` from `Definition_5_0_20`, the canonical domain-level bridge
  to the dual local norm;
* `selfConcordantOmegaArg` and `selfConcordantOmegaStarArg` from `Definition_5_0_21`, the
  canonical Chapter 5 owners of the `ω` and `ω_*` arguments;
* `IsSelfConcordantOnWith` from `Definition_5_1_1`, the owner for quantitative
  self-concordance;
* `firstOrderTaylorModelAt` from `Chap01/FirstOrderTaylorModel`, the canonical affine Taylor
  owner against which the remainder is measured.

Source/core/bridge triage:
* source-facing: the lower and upper value bounds expressed by the dual local norm of
  `∇ f y - ∇ f x` at `y`;
* core/canonical: `IsSelfConcordantOnWith dom Mf f`, `HasPositiveDefiniteHessianOn dom f`,
  `HessianDualLocalNorm.ofPosDefMem`, and the Chapter 5 auxiliary-function owners `ω` and `ω_*`;
* bridge/view: the gradient-difference covector
  `(toDual ℝ E) (∇ f y - ∇ f x)` and the affine Taylor remainder
  `f y - firstOrderTaylorModelAt f x y`.

Primitive data:
* `dom`, `Mf`, `f`, the points `x` and `y`;
* domain membership of `x` and `y`;
* positive definiteness of the Hessian on `dom`.

Derived API:
* the gradient-difference covector at `y`;
* the domain-level dual local norm bridge `HessianDualLocalNorm.ofPosDefMem`;
* the lower `ω` and upper `ω_*` remainder terms, expressed through the canonical subtype owners
  `selfConcordantOmegaArg` and `selfConcordantOmegaStarArg`.

This file stays source-facing. The theorem is not a new owner: it is a derived consequence of the
dual-local-norm owner, the canonical first-order Taylor model, and the Chapter 5 auxiliary
function owners. -/

private theorem gradientDifferenceDualLocalNorm_nonneg
    (x y : E) (hy : y ∈ dom) :
    0 ≤
      HessianDualLocalNorm.ofPosDefMem f hy
        ((toDual ℝ E) (∇ f y - ∇ f x)) := by
  simpa [HessianDualLocalNorm.ofPosDefMem] using
    dualLocalNorm_nonneg f y
      (HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem hy)
      (hessian_isInvertible_of_det_ne_zero
        (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hy))
      ((toDual ℝ E) (∇ f y - ∇ f x))

/-- Helper for Theorem 5.1.12: the affine tilt `z ↦ f z - ⟪∇ f x, z⟫`, packaged via the
canonical quadratic-affine owner. -/
private def tiltedObjective (f : E → ℝ) (x : E) : E → ℝ :=
  quadraticAffineObjective 0 (-∇ f x) (0 : E →L[ℝ] E) + f

/-- Helper for Theorem 5.1.12: the Hessian dual local norm of the gradient covector is always
nonnegative on the positive-definite domain. -/
private theorem dualGradientDualLocalNorm_nonneg
    {g : E → ℝ} [HasPositiveDefiniteHessianOn dom g]
    (y : E) (hy : y ∈ dom) :
    0 ≤
      HessianDualLocalNorm.ofPosDefMem g hy
        ((toDual ℝ E) (∇ g y)) := by
  simpa [HessianDualLocalNorm.ofPosDefMem] using
    dualLocalNorm_nonneg g y
      (HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem hy)
      (hessian_isInvertible_of_det_ne_zero
        (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hy))
      ((toDual ℝ E) (∇ g y))

/-- Helper for Theorem 5.1.12: on an open domain where both summands are `C²`, the Hessian of the
sum is the sum of the Hessians at the base point. -/
private theorem differentiableAt_gradient_of_contDiffAt_two
    {g : E → ℝ} {x : E} (hg : ContDiffAt ℝ 2 g x) :
    DifferentiableAt ℝ (∇ g) x := by
  -- Rewrite the gradient through the Riesz isomorphism so differentiability follows from the
  -- differentiability of the Fréchet derivative field.
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ g) x := by
    exact
      (hg.fderiv_right
        (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))).differentiableAt
        one_ne_zero
  change DifferentiableAt ℝ (fun y ↦ D (fderiv ℝ g y)) x
  exact (D.hasFDerivAt.comp x hfdiff.hasFDerivAt).differentiableAt

/-- Helper for Theorem 5.1.12: a `C³` objective has a genuinely differentiable Hessian field at
each point of the open domain. -/
private theorem hessian_hasFDerivAt_of_contDiffAt_three
    {g : E → ℝ} {x : E} (hg : ContDiffAt ℝ 3 g x) :
    HasFDerivAt (hessian g) (fderiv ℝ (hessian g) x) x := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfderiv_C2 : ContDiffAt ℝ 2 (fderiv ℝ g) x := by
    -- Differentiate `g` once and keep the two remaining derivatives.
    exact hg.fderiv_right (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)
  have hgrad_C2 : ContDiffAt ℝ 2 (∇ g) x := by
    -- Rewrite the gradient through the Riesz map before differentiating again.
    simpa [gradient, D] using D.contDiff.contDiffAt.comp x hfderiv_C2
  have hhessian_C1 : ContDiffAt ℝ 1 (hessian g) x := by
    -- One more derivative of the gradient is exactly the Hessian owner.
    simpa [hessian] using
      hgrad_C2.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  -- Convert the `C¹` regularity of the Hessian map into the required Fréchet derivative.
  exact (hhessian_C1.hasStrictFDerivAt one_ne_zero).hasFDerivAt

/-- Helper for Theorem 5.1.12: on an open domain where both summands are `C²`, the Hessian of the
sum is the sum of the Hessians at the base point. -/
private theorem hessian_add_eq_of_contDiffOn
    {g₁ g₂ : E → ℝ} {x : E}
    (hg₁ : ContDiffOn ℝ 2 g₁ dom) (hg₂ : ContDiffOn ℝ 2 g₂ dom)
    (hopen : IsOpen dom) (hx : x ∈ dom) :
    hessian (g₁ + g₂) x = hessian g₁ x + hessian g₂ x := by
  have hgrad_nhds :
      (fun y ↦ ∇ (g₁ + g₂) y) =ᶠ[nhds x] fun y ↦ ∇ g₁ y + ∇ g₂ y := by
    -- Near `x`, both summands are differentiable, so the gradient of the sum is pointwise
    -- additive on that neighborhood.
    filter_upwards [hopen.mem_nhds hx] with y hy
    have hg₁y : DifferentiableAt ℝ g₁ y := by
      exact (hg₁.contDiffAt (hopen.mem_nhds hy)).differentiableAt (by norm_num)
    have hg₂y : DifferentiableAt ℝ g₂ y := by
      exact (hg₂.contDiffAt (hopen.mem_nhds hy)).differentiableAt (by norm_num)
    rw [gradient, fderiv_add hg₁y hg₂y]
    simp [gradient]
  have hgrad₁ : DifferentiableAt ℝ (∇ g₁) x := by
    -- A `C²` function has a differentiable gradient field on the open domain.
    exact differentiableAt_gradient_of_contDiffAt_two (hg₁.contDiffAt (hopen.mem_nhds hx))
  have hgrad₂ : DifferentiableAt ℝ (∇ g₂) x := by
    -- The same `C²` argument applies to the second summand.
    exact differentiableAt_gradient_of_contDiffAt_two (hg₂.contDiffAt (hopen.mem_nhds hx))
  -- Differentiate the neighborhood identity for the gradient at the base point.
  rw [hessian, hgrad_nhds.fderiv_eq, fderiv_fun_add hgrad₁ hgrad₂]

omit [HasPositiveDefiniteHessianOn dom f] in
/-- Helper for Theorem 5.1.12: the affine tilt has the expected shifted gradient on `dom`. -/
private theorem gradient_tiltedObjective_eq_sub
    {M : NNReal} [IsSelfConcordantOnWith dom M f]
    (x y : E) (hy : y ∈ dom) :
    ∇ (tiltedObjective f x) y = ∇ f y - ∇ f x := by
  let q : E → ℝ := quadraticAffineObjective 0 (-∇ f x) (0 : E →L[ℝ] E)
  let hself : IsSelfConcordantOnWith dom M f := inferInstance
  have hq_contDiff : ContDiff ℝ 2 q := by
    simpa [q] using (quadraticAffineObjective_contDiff 0 (-∇ f x) (0 : E →L[ℝ] E)).of_le
      (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hq_diff : DifferentiableAt ℝ q y := by
    exact (hq_contDiff.contDiffAt).differentiableAt (by norm_num)
  have hf_diff : DifferentiableAt ℝ f y := by
    exact (hself.contDiffOn.contDiffAt (hself.isOpen_domain.mem_nhds hy)).differentiableAt
      (by norm_num)
  have hq_grad :
      ∇ q y = -∇ f x := by
    have hzero_selfAdjoint :
        IsSelfAdjoint (0 : E →L[ℝ] E) := by
      simp
    have hq_grad_global :
        ∇ q = fun z ↦ -∇ f x + (0 : E →L[ℝ] E) z :=
      quadraticAffineObjective_gradient_eq 0 (-∇ f x) (0 : E →L[ℝ] E) hzero_selfAdjoint
    simpa [q] using congrFun hq_grad_global y
  have hsum :
      ∇ (tiltedObjective f x) y = ∇ q y + ∇ f y := by
    rw [tiltedObjective, gradient, fderiv_add hq_diff hf_diff]
    simp [gradient]
  -- Rewrite the linear tilt contribution as the constant vector `-∇ f x`.
  calc
    ∇ (tiltedObjective f x) y = ∇ q y + ∇ f y := hsum
    _ = ∇ f y - ∇ f x := by
      rw [hq_grad]
      abel

omit [HasPositiveDefiniteHessianOn dom f] in
/-- Helper for Theorem 5.1.12: the affine tilt keeps the Hessian unchanged on `dom`. -/
private theorem hessian_tiltedObjective_eq
    {M : NNReal} [IsSelfConcordantOnWith dom M f]
    (x y : E) (hy : y ∈ dom) :
    hessian (tiltedObjective f x) y = hessian f y := by
  let q : E → ℝ := quadraticAffineObjective 0 (-∇ f x) (0 : E →L[ℝ] E)
  let hself : IsSelfConcordantOnWith dom M f := inferInstance
  have hq_C2 : ContDiffOn ℝ 2 q dom := by
    exact ((by
      simpa [q] using (quadraticAffineObjective_contDiff 0 (-∇ f x) (0 : E →L[ℝ] E)).of_le
        (by norm_num : (2 : WithTop ℕ∞) ≤ 3)) : ContDiff ℝ 2 q).contDiffOn
  have hf_C2 : ContDiffOn ℝ 2 f dom := by
    exact hself.contDiffOn.of_le (by norm_num)
  have hsum :
      hessian (tiltedObjective f x) y = hessian q y + hessian f y := by
    simpa [tiltedObjective, q] using
      hessian_add_eq_of_contDiffOn hq_C2 hf_C2 hself.isOpen_domain hy
  have hzero_selfAdjoint :
      IsSelfAdjoint (0 : E →L[ℝ] E) := by
    simp
  have hq_hessian : hessian q y = 0 := by
    simpa [q] using
      quadraticAffineObjective_hessian_eq 0 (-∇ f x) (0 : E →L[ℝ] E) hzero_selfAdjoint y
  -- The linear perturbation has zero Hessian, so only the original Hessian remains.
  calc
    hessian (tiltedObjective f x) y = hessian q y + hessian f y := hsum
    _ = hessian f y := by simp [hq_hessian]

omit [HasPositiveDefiniteHessianOn dom f] in
/-- Helper for Theorem 5.1.12: affine tilting preserves self-concordance on the same domain. -/
private theorem tiltedObjective_selfConcordant
    (x : E) :
    IsSelfConcordantOnWith dom Mf (tiltedObjective f x) := by
  have hzero_pos : (0 : E →L[ℝ] E).IsPositive := ContinuousLinearMap.isPositive_zero
  -- Add the zero-self-concordant affine objective to `f`.
  simpa [tiltedObjective, add_comm] using
    (quadraticAffineObjective_isSelfConcordantOnWith_zero
      0 (-∇ f x) (0 : E →L[ℝ] E) hzero_pos).add
      (inferInstance : IsSelfConcordantOnWith dom Mf f)

/-- Helper for Theorem 5.1.12: affine tilting preserves positive-definite Hessians on `dom`. -/
private theorem tiltedObjective_hasPositiveDefiniteHessianOn
    {M : NNReal} [IsSelfConcordantOnWith dom M f]
    (x : E) :
    HasPositiveDefiniteHessianOn dom (tiltedObjective f x) := by
  refine ⟨?_, ?_⟩
  · intro y hy
    -- The affine tilt has the same Hessian at every domain point, so positivity transports
    -- directly from the ambient owner for `f`.
    simpa [hessian_tiltedObjective_eq (M := M) x y hy] using
      (HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem (dom := dom) (f := f) hy)
  · intro y hy u hu
    -- The same Hessian identity transports the strict quadratic-form positivity.
    simpa [hessian_tiltedObjective_eq (M := M) x y hy] using
      (HasPositiveDefiniteHessianOn.posdef (dom := dom) (f := f) hy hu)

/-- Helper for Theorem 5.1.12: every minimizer on the open self-concordant domain is stationary.
-/
private theorem gradient_eq_zero_of_isMinOn
    {g : E → ℝ} [IsSelfConcordantOnWith dom Mf g]
    (xStar : dom) (hmin : IsMinOn g dom (xStar : E)) :
    ∇ g (xStar : E) = 0 := by
  -- Convert the constrained minimizer into an ambient local minimizer using openness of `dom`.
  let hself : IsSelfConcordantOnWith dom Mf g := inferInstance
  have hlocal : IsLocalMin g (xStar : E) :=
    hmin.isLocalMin (hself.isOpen_domain.mem_nhds xStar.2)
  exact isLocalMin_gradient_eq_zero hlocal

/-- Helper for Theorem 5.1.12: every feasible stationary point minimizes a self-concordant
objective on its convex domain. -/
private theorem isMinOn_of_gradient_eq_zero
    {g : E → ℝ} [IsSelfConcordantOnWith dom Mf g]
    {xStar : E} (hxStar : xStar ∈ dom)
    (hgrad : ∇ g xStar = 0) :
    IsMinOn g dom xStar := by
  let hself : IsSelfConcordantOnWith dom Mf g := inferInstance
  have hdiff : DifferentiableAt ℝ g xStar := by
    exact (hself.contDiffOn.contDiffAt (hself.isOpen_domain.mem_nhds hxStar)).differentiableAt
      (by norm_num)
  -- Convert stationarity into the first-order variational inequality on the convex domain.
  exact
    (hself.convexOn.isMinOn_iff_gradient_variational_inequality hxStar hdiff).2 <| by
      intro z hz
      simp [hgrad]

/-- Helper for Theorem 5.1.12: when `M_f = 0`, the Chapter 5 operator inequality forces the
Hessian to be constant on the convex domain. -/
private theorem hessian_eq_of_zeroSelfConcordant
    {g : E → ℝ} [IsSelfConcordantOnWith dom Mf g]
    {x y : E} (hMf0 : Mf = 0) (hx : x ∈ dom) (hy : y ∈ dom) :
    hessian g x = hessian g y := by
  let hself : IsSelfConcordantOnWith dom Mf g := inferInstance
  have hhess_diff : DifferentiableOn ℝ (hessian g) dom := by
    intro z hz
    -- A self-concordant function is `C³`, so its Hessian field is differentiable on the open
    -- domain.
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
    -- The operator inequality with `u` and `-u` forces the directional Hessian derivative to
    -- vanish when `M_f = 0`.
    have hle : fderiv ℝ (hessian g) z u ≤ 0 := by
      simpa [hMf0] using hself.thirdDerivative_operator_le hz u
    have hneg_le : -(fderiv ℝ (hessian g) z u) ≤ 0 := by
      simpa [map_neg, hMf0] using hself.thirdDerivative_operator_le hz (-u)
    have hge : 0 ≤ fderiv ℝ (hessian g) z u := by
      simpa [ContinuousLinearMap.le_def] using hneg_le
    exact le_antisymm hle hge
  -- Apply the convex mean-value theorem to the Hessian field on the convex domain.
  exact hself.convex_domain.is_const_of_fderivWithin_eq_zero hhess_diff hhess_zero hx hy

/-- Helper for Theorem 5.1.12: when `M_f = 0`, the gradient is affine with constant Hessian on the
whole domain. -/
private theorem gradient_eq_zeroParameterAffineModel
    {g : E → ℝ} [IsSelfConcordantOnWith dom Mf g]
    {xStar y : E} (hMf0 : Mf = 0) (hxStar : xStar ∈ dom) (hy : y ∈ dom) :
    ∇ g y = ∇ g xStar + hessian g xStar (y - xStar) := by
  let hself : IsSelfConcordantOnWith dom Mf g := inferInstance
  let A : E →L[ℝ] E := hessian g xStar
  let model : E → E := fun z ↦ (∇ g xStar - A xStar) + A z
  have hgrad_diff : DifferentiableOn ℝ (∇ g) dom := by
    intro z hz
    -- A self-concordant function is `C²`, hence its gradient field is differentiable on `dom`.
    have hgrad_z : DifferentiableAt ℝ (∇ g) z :=
      differentiableAt_gradient_of_contDiffAt_two
        ((hself.contDiffOn.of_le (by norm_num)).contDiffAt (hself.isOpen_domain.mem_nhds hz))
    exact hgrad_z.differentiableWithinAt
  have hmodel_diff : DifferentiableOn ℝ model dom := by
    intro z hz
    -- The comparison field is affine, so its derivative is the constant Hessian `A`.
    have hmodel_deriv : HasFDerivAt model A z := by
      simpa [model] using (A.hasFDerivAt.const_add (∇ g xStar - A xStar))
    exact hmodel_deriv.differentiableAt.differentiableWithinAt
  have hderiv_eq :
      dom.EqOn (fderivWithin ℝ (∇ g) dom) (fderivWithin ℝ model dom) := by
    intro z hz
    rw [fderivWithin_of_isOpen hself.isOpen_domain hz]
    rw [fderivWithin_of_isOpen hself.isOpen_domain hz]
    -- The gradient derivative is the Hessian, which is constant on the zero-parameter branch.
    calc
      fderiv ℝ (∇ g) z = hessian g z := by rw [hessian]
      _ = A := by
        simpa [A] using
          hessian_eq_of_zeroSelfConcordant (dom := dom) (Mf := Mf) (g := g) hMf0 hz hxStar
      _ = fderiv ℝ model z := by
        symm
        simp [model]
  have hmodel_eqOn :
      dom.EqOn (∇ g) model :=
    hself.convex_domain.eqOn_of_fderivWithin_eq hgrad_diff hmodel_diff
      hself.isOpen_domain.uniqueDiffOn hderiv_eq hxStar (by simp [model])
  -- Evaluate the affine comparison field at `y` and rewrite it as the textbook `y - xStar`
  -- model.
  calc
    ∇ g y = model y := hmodel_eqOn hy
    _ = ∇ g xStar + hessian g xStar (y - xStar) := by
      dsimp [model, A]
      rw [ContinuousLinearMap.map_sub]
      abel

/-- Helper for Theorem 5.1.12: in the degenerate `M_f = 0` regime, a feasible minimizer sees the
exact quadratic gap `(1 / 2) δ²` in the dual local norm. -/
private theorem zeroParameterSuboptimality_eq_halfDualGradientNormSq_atMinimizer
    {g : E → ℝ} [IsSelfConcordantOnWith dom Mf g] [HasPositiveDefiniteHessianOn dom g]
    {xStar y : E} (hMf0 : Mf = 0) (hxStar : xStar ∈ dom)
    (hmin : IsMinOn g dom xStar) (hy : y ∈ dom) :
    let δ := HessianDualLocalNorm.ofPosDefMem g hy ((toDual ℝ E) (∇ g y))
    g y = g xStar + δ ^ (2 : ℕ) / 2 := by
  dsimp
  let hself : IsSelfConcordantOnWith dom Mf g := inferInstance
  have hgradStar : ∇ g xStar = 0 := by
    -- A feasible minimizer is stationary on the open self-concordant domain.
    exact
      gradient_eq_zero_of_isMinOn (dom := dom) (Mf := Mf) (g := g)
        ⟨xStar, hxStar⟩ hmin
  have hA_pos : (hessian g xStar).IsPositive :=
    HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem (dom := dom) (f := g) hxStar
  have hA_self : IsSelfAdjoint (hessian g xStar) := hA_pos.isSelfAdjoint
  have hg_diff : DifferentiableOn ℝ g dom := by
    intro z hz
    -- Self-concordance supplies `C¹` regularity on the whole domain.
    exact
      (hself.contDiffOn.contDiffAt (hself.isOpen_domain.mem_nhds hz)).differentiableAt
        (by norm_num)
        |>.differentiableWithinAt
  have hmodel_diff : DifferentiableOn ℝ (secondOrderTaylorModelAt g xStar) dom := by
    intro z hz
    -- The second-order Taylor model has the expected affine gradient everywhere.
    exact
      (hasGradientAt_secondOrderTaylorModelAt_of_isSelfAdjoint
        (f := g) (x := xStar) (y := z) hA_self).differentiableAt.differentiableWithinAt
  have hderiv_eq :
      dom.EqOn (fderivWithin ℝ g dom)
        (fderivWithin ℝ (secondOrderTaylorModelAt g xStar) dom) := by
    intro z hz
    rw [fderivWithin_of_isOpen hself.isOpen_domain hz]
    rw [fderivWithin_of_isOpen hself.isOpen_domain hz]
    -- The zero-parameter affine gradient formula matches the gradient of the frozen quadratic
    -- Taylor model.
    have hgrad_eq :
        ∇ g z = ∇ (secondOrderTaylorModelAt g xStar) z := by
      calc
        ∇ g z = ∇ g xStar + hessian g xStar (z - xStar) := by
          exact
            gradient_eq_zeroParameterAffineModel (dom := dom) (Mf := Mf) (g := g)
              hMf0 hxStar hz
        _ = ∇ (secondOrderTaylorModelAt g xStar) z := by
          have hgrad_model :
              ∇ (secondOrderTaylorModelAt g xStar) =
                fun w ↦ ∇ g xStar + hessian g xStar (w - xStar) := by
            exact gradient_eq <| fun w ↦
              hasGradientAt_secondOrderTaylorModelAt_of_isSelfAdjoint
                (f := g) (x := xStar) (y := w) hA_self
          rw [hgrad_model]
    simpa [gradient] using congrArg (toDual ℝ E) hgrad_eq
  have hvalue_eq :
      dom.EqOn g (secondOrderTaylorModelAt g xStar) :=
    hself.convex_domain.eqOn_of_fderivWithin_eq hg_diff hmodel_diff
      hself.isOpen_domain.uniqueDiffOn hderiv_eq hxStar (by simp)
  have hgrad_quadratic :
      hessian g xStar (y - xStar) = ∇ g y := by
    -- After stationarity at `xStar`, the affine gradient model collapses to the quadratic term.
    calc
      hessian g xStar (y - xStar) = ∇ g xStar + hessian g xStar (y - xStar) := by
        simp [hgradStar]
      _ = ∇ g y := by
        symm
        exact
          gradient_eq_zeroParameterAffineModel (dom := dom) (Mf := Mf) (g := g)
            hMf0 hxStar hy
  have hgrad_quadratic_y :
      ∇ g y = hessian g y (y - xStar) := by
    -- The constant-Hessian bridge transports the quadratic gradient identity to the base point `y`.
    calc
      ∇ g y = hessian g xStar (y - xStar) := hgrad_quadratic.symm
      _ = hessian g y (y - xStar) := by
        rw [hessian_eq_of_zeroSelfConcordant (dom := dom) (Mf := Mf) (g := g) hMf0 hy hxStar]
  have hInvY :
      (hessian g y).IsInvertible :=
    hessian_isInvertible_of_det_ne_zero
      (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem (dom := dom) (f := g) hy)
  have hv_eq :
      (hessian g y).inverse (∇ g y) = y - xStar := by
    -- Apply the inverse Hessian to the quadratic gradient identity.
    apply hInvY.injective
    calc
      hessian g y ((hessian g y).inverse (∇ g y)) = ∇ g y := by
        exact hInvY.self_apply_inverse (∇ g y)
      _ = hessian g y (y - xStar) := hgrad_quadratic_y
  have hpair :
      inner ℝ (∇ g y) (y - xStar) =
        (HessianDualLocalNorm.ofPosDefMem g hy ((toDual ℝ E) (∇ g y))) ^ (2 : ℕ) := by
    -- The inverse-Hessian direction is exactly the displacement to the minimizer in the rigid
    -- zero-parameter regime.
    let v : E := (hessian g y).inverse (∇ g y)
    let hPosY : (hessian g y).IsPositive :=
      HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem (dom := dom) (f := g) hy
    have hHv : hessian g y v = ∇ g y := hInvY.self_apply_inverse (∇ g y)
    have hpair_nonneg : 0 ≤ inner ℝ (∇ g y) v := by
      have hquad : 0 ≤ inner ℝ v (hessian g y v) := hPosY.inner_nonneg_right v
      simpa [v, hHv, real_inner_comm] using hquad
    calc
      inner ℝ (∇ g y) (y - xStar) = inner ℝ (∇ g y) v := by simp [v, hv_eq]
      _ = (Real.sqrt (inner ℝ (∇ g y) v)) ^ (2 : ℕ) := by
        symm
        simpa using Real.sq_sqrt hpair_nonneg
      _ =
          (HessianDualLocalNorm.ofPosDefMem g hy ((toDual ℝ E) (∇ g y))) ^ (2 : ℕ) := by
            rw [show
              Real.sqrt (inner ℝ (∇ g y) v) =
                  HessianDualLocalNorm.ofPosDefMem g hy ((toDual ℝ E) (∇ g y)) by
              simp [HessianDualLocalNorm.ofPosDefMem_def, v]]
  -- Evaluate the exact quadratic Taylor model at `y` and rewrite its quadratic term through the
  -- dual local norm.
  calc
    g y = secondOrderTaylorModelAt g xStar y := hvalue_eq hy
    _ = g xStar + (1 / 2 : ℝ) * inner ℝ (∇ g y) (y - xStar) := by
      rw [secondOrderTaylorModelAt_apply, hgradStar, hgrad_quadratic]
      simp
    _ = g xStar +
          (HessianDualLocalNorm.ofPosDefMem g hy ((toDual ℝ E) (∇ g y))) ^ (2 : ℕ) / 2 := by
      rw [hpair]
      ring

omit [HasPositiveDefiniteHessianOn dom f] in
/-- Helper for Theorem 5.1.12: the affine tilt is stationary at its base point. -/
private theorem gradient_tiltedObjective_eq_zero_at_base
    {M : NNReal} [IsSelfConcordantOnWith dom M f]
    (x : E) (hx : x ∈ dom) :
    ∇ (tiltedObjective f x) x = 0 := by
  -- Specialize the shifted-gradient formula at the base point and cancel the difference.
  simpa using gradient_tiltedObjective_eq_sub (M := M) x x hx

/-- Helper for Theorem 5.1.12: the affine tilt gap is exactly the first-order Taylor remainder. -/
private theorem tiltedGap_eq_taylorGap
    (x y : E) :
    tiltedObjective f x y - tiltedObjective f x x =
      f y - firstOrderTaylorModelAt f x y := by
  -- Expand the affine tilt at the endpoint and at the base point, then regroup the linear term.
  simp [tiltedObjective, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, inner_add_right]

/-- Helper for Theorem 5.1.12: the dual local norm of the tilted gradient at `y` is the original
dual local norm of `∇ f y - ∇ f x`. -/
private theorem tiltedGradientDualLocalNorm_eq_gradientDifference
    {M : NNReal} [IsSelfConcordantOnWith dom M f]
    (x y : E) (hy : y ∈ dom)
    [HasPositiveDefiniteHessianOn dom (tiltedObjective f x)] :
    HessianDualLocalNorm.ofPosDefMem (tiltedObjective f x) hy
        ((toDual ℝ E) (∇ (tiltedObjective f x) y)) =
      HessianDualLocalNorm.ofPosDefMem f hy
        ((toDual ℝ E) (∇ f y - ∇ f x)) := by
  -- Route correction: this bridge is a pure owner-level rewrite. The affine tilt changes the
  -- gradient by subtraction, but it leaves the Hessian metric itself unchanged.
  rw [gradient_tiltedObjective_eq_sub (M := M) x y hy]
  rw [HessianDualLocalNorm.ofPosDefMem_def, HessianDualLocalNorm.ofPosDefMem_def]
  simp [hessian_tiltedObjective_eq (M := M) x y hy]

/-- Helper for Theorem 5.1.12: at a positive-definite domain point, the inverse-Hessian gradient
direction has local norm equal to the dual local norm of the gradient covector, and its pairing
with the gradient is the corresponding square. -/
private theorem inverseHessianGradient_localNorm_and_pairing
    {g : E → ℝ} [HasPositiveDefiniteHessianOn dom g]
    {y : E} (hy : y ∈ dom) :
    let δ := HessianDualLocalNorm.ofPosDefMem g hy ((toDual ℝ E) (∇ g y))
    let v := (hessian g y).inverse (∇ g y)
    hessianLocalNorm g y v = δ ∧ inner ℝ (∇ g y) v = δ ^ (2 : ℕ) := by
  dsimp
  let v : E := (hessian g y).inverse (∇ g y)
  let hPos : (hessian g y).IsPositive :=
    HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem (dom := dom) (f := g) hy
  let hInv : (hessian g y).IsInvertible :=
    hessian_isInvertible_of_det_ne_zero
      (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem (dom := dom) (f := g) hy)
  have hHv : hessian g y v = ∇ g y := hInv.self_apply_inverse (∇ g y)
  have hpair_nonneg : 0 ≤ inner ℝ (∇ g y) v := by
    have hquad : 0 ≤ inner ℝ v (hessian g y v) := hPos.inner_nonneg_right v
    -- Rewrite the positive Hessian quadratic form of the Newton direction as the gradient pairing.
    simpa [v, hHv, real_inner_comm] using hquad
  have hv_norm :
      hessianLocalNorm g y v =
        HessianDualLocalNorm.ofPosDefMem g hy ((toDual ℝ E) (∇ g y)) := by
    -- Both norms expand to the same inverse-Hessian quadratic form.
    rw [hessianLocalNorm_def, HessianDualLocalNorm.ofPosDefMem_def]
    simp [v, hHv, real_inner_comm]
  have hpair :
      inner ℝ (∇ g y) v =
        (HessianDualLocalNorm.ofPosDefMem g hy ((toDual ℝ E) (∇ g y))) ^ (2 : ℕ) := by
    -- Square the shared square-root expression to recover the pairing.
    calc
      inner ℝ (∇ g y) v = (Real.sqrt (inner ℝ (∇ g y) v)) ^ (2 : ℕ) := by
        symm
        simpa using Real.sq_sqrt hpair_nonneg
      _ =
          (HessianDualLocalNorm.ofPosDefMem g hy ((toDual ℝ E) (∇ g y))) ^ (2 : ℕ) := by
            rw [show
              Real.sqrt (inner ℝ (∇ g y) v) =
                  HessianDualLocalNorm.ofPosDefMem g hy ((toDual ℝ E) (∇ g y)) by
              simp [HessianDualLocalNorm.ofPosDefMem_def, v]]
  exact ⟨hv_norm, hpair⟩

/-- Helper for Theorem 5.1.12: at a positive-definite domain point, nonnegative scalar dilations
scale the Hessian local norm linearly. -/
private theorem hessianLocalNorm_smul_of_nonneg_ofPosDefMem
    {g : E → ℝ} [HasPositiveDefiniteHessianOn dom g]
    {y d : E} (hy : y ∈ dom) {t : ℝ} (ht : 0 ≤ t) :
    ‖t • d‖[g; y] = t * ‖d‖[g; y] := by
  let hPos : (hessian g y).IsPositive :=
    HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem (dom := dom) (f := g) hy
  have hquad : 0 ≤ inner ℝ d (hessian g y d) := hPos.inner_nonneg_right d
  -- Expand the local norm and simplify the square root of `t²` times the Hessian quadratic form.
  calc
    ‖t • d‖[g; y] = Real.sqrt ((t * t) * inner ℝ d (hessian g y d)) := by
      rw [hessianLocalNorm_def]
      congr 1
      simp [inner_smul_left, inner_smul_right, mul_assoc]
    _ = Real.sqrt (inner ℝ d (hessian g y d)) * Real.sqrt (t * t) := by
      rw [mul_comm, Real.sqrt_mul hquad]
    _ = t * ‖d‖[g; y] := by
      rw [show t * t = t ^ (2 : ℕ) by ring, Real.sqrt_sq_eq_abs, abs_of_nonneg ht,
        hessianLocalNorm_def]
      ring

/-- Helper for Theorem 5.1.12: the damped inverse-Hessian probe from `y` has the textbook local
norm `δ / (1 + M_f δ)`. -/
private theorem dampedDualGradientProbe_localNorm_eq
    {g : E → ℝ} [HasPositiveDefiniteHessianOn dom g]
    {y : E} (hy : y ∈ dom) :
    let δ := HessianDualLocalNorm.ofPosDefMem g hy ((toDual ℝ E) (∇ g y))
    let α := 1 / (1 + (Mf : ℝ) * δ)
    let v := (hessian g y).inverse (∇ g y)
    let yPlus := y - α • v
    ‖yPlus - y‖[g; y] = δ / (1 + (Mf : ℝ) * δ) := by
  let δ := HessianDualLocalNorm.ofPosDefMem g hy ((toDual ℝ E) (∇ g y))
  let α : ℝ := 1 / (1 + (Mf : ℝ) * δ)
  let v : E := (hessian g y).inverse (∇ g y)
  let yPlus : E := y - α • v
  have hδ_nonneg : 0 ≤ δ :=
    dualGradientDualLocalNorm_nonneg (dom := dom) (g := g) y hy
  have hα_nonneg : 0 ≤ α := by
    dsimp [α]
    have hMf_nonneg : 0 ≤ (Mf : ℝ) := by
      exact_mod_cast Mf.2
    have hden_nonneg : 0 ≤ 1 + (Mf : ℝ) * δ := by
      nlinarith
    exact one_div_nonneg.mpr hden_nonneg
  have hv_norm : ‖v‖[g; y] = δ := by
    -- The Newton direction already has local norm `δ` by the inverse-Hessian bridge.
    simpa [δ, v] using
      (inverseHessianGradient_localNorm_and_pairing (dom := dom) (g := g) (y := y) hy).1
  -- Rewrite the probe displacement and then scale the local norm through the positive scalar `α`.
  calc
    ‖yPlus - y‖[g; y] = ‖α • v‖[g; y] := by
      rw [show yPlus - y = -(α • v) by
        dsimp [yPlus]
        abel]
      rw [hessianLocalNorm_neg]
    _ = α * ‖v‖[g; y] :=
      hessianLocalNorm_smul_of_nonneg_ofPosDefMem (dom := dom) (g := g) hy hα_nonneg
    _ = α * δ := by rw [hv_norm]
    _ = δ / (1 + (Mf : ℝ) * δ) := by
      simp [α, div_eq_mul_inv, mul_comm]

/-- Helper for Theorem 5.1.12: the affine term of the damped inverse-Hessian probe is
`-δ² / (1 + M_f δ)`. -/
private theorem dampedDualGradientProbe_gradient_pairing_eq
    {g : E → ℝ} [HasPositiveDefiniteHessianOn dom g]
    {y : E} (hy : y ∈ dom) :
    let δ := HessianDualLocalNorm.ofPosDefMem g hy ((toDual ℝ E) (∇ g y))
    let α := 1 / (1 + (Mf : ℝ) * δ)
    let v := (hessian g y).inverse (∇ g y)
    let yPlus := y - α • v
    inner ℝ (∇ g y) (yPlus - y) =
      -(δ ^ (2 : ℕ) / (1 + (Mf : ℝ) * δ)) := by
  let δ := HessianDualLocalNorm.ofPosDefMem g hy ((toDual ℝ E) (∇ g y))
  let α : ℝ := 1 / (1 + (Mf : ℝ) * δ)
  let v : E := (hessian g y).inverse (∇ g y)
  let yPlus : E := y - α • v
  have hpair :
      inner ℝ (∇ g y) v = δ ^ (2 : ℕ) := by
    -- The inverse-Hessian bridge also identifies the gradient pairing with `δ²`.
    simpa [δ, v] using
      (inverseHessianGradient_localNorm_and_pairing (dom := dom) (g := g) (y := y) hy).2
  -- Rewrite the displacement and evaluate the pairing on the scaled Newton direction.
  calc
    inner ℝ (∇ g y) (yPlus - y) = inner ℝ (∇ g y) (-(α • v)) := by
      rw [show yPlus - y = -(α • v) by
        dsimp [yPlus]
        abel]
    _ = -(α * inner ℝ (∇ g y) v) := by
      simp [inner_smul_right, mul_comm]
    _ = -(α * δ ^ (2 : ℕ)) := by rw [hpair]
    _ = -(δ ^ (2 : ℕ) / (1 + (Mf : ℝ) * δ)) := by
      simp [α, div_eq_mul_inv, mul_comm]

/-- Helper for Theorem 5.1.12: when `M_f > 0`, the damped inverse-Hessian probe lies in the
admissible Dikin ellipsoid around `y`. -/
private theorem dampedDualGradientProbe_mem_openDikinEllipsoid
    {g : E → ℝ} [HasPositiveDefiniteHessianOn dom g]
    {y : E} (hy : y ∈ dom) (hMf : Mf ≠ 0) :
    let δ := HessianDualLocalNorm.ofPosDefMem g hy ((toDual ℝ E) (∇ g y))
    let α := 1 / (1 + (Mf : ℝ) * δ)
    let v := (hessian g y).inverse (∇ g y)
    let yPlus := y - α • v
    yPlus ∈ W⁰[g; y](1 / (Mf : ℝ)) := by
  let δ := HessianDualLocalNorm.ofPosDefMem g hy ((toDual ℝ E) (∇ g y))
  let α : ℝ := 1 / (1 + (Mf : ℝ) * δ)
  let v : E := (hessian g y).inverse (∇ g y)
  let yPlus : E := y - α • v
  have hδ_nonneg : 0 ≤ δ :=
    dualGradientDualLocalNorm_nonneg (dom := dom) (g := g) y hy
  have hMf_pos_nn : 0 < Mf := lt_of_le_of_ne Mf.2 (Ne.symm hMf)
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact_mod_cast hMf_pos_nn
  have hstep_lt : δ / (1 + (Mf : ℝ) * δ) < 1 / (Mf : ℝ) := by
    refine (lt_div_iff₀ hMf_pos).2 ?_
    have hfrac_lt : ((Mf : ℝ) * δ) / (1 + (Mf : ℝ) * δ) < 1 := by
      have hden_pos : 0 < 1 + (Mf : ℝ) * δ := by positivity
      refine (div_lt_iff₀ hden_pos).2 ?_
      nlinarith
    simpa [δ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hfrac_lt
  -- The probe local norm is exactly the Dikin-radius condition.
  refine (mem_openDikinEllipsoid_iff g y yPlus (1 / (Mf : ℝ))).2 ?_
  rw [show ‖yPlus - y‖[g; y] = δ / (1 + (Mf : ℝ) * δ) by
    simpa [δ, α, v, yPlus] using
      dampedDualGradientProbe_localNorm_eq (dom := dom) (Mf := Mf) (g := g) hy]
  exact hstep_lt

/-- Helper for Theorem 5.1.12: along the segment from `y` to `z`, the fixed direction `z - y`
keeps the forward local-norm lower transport bound supplied by self-concordance. -/
private theorem forwardLocalNormLowerBoundAlongSegment
    {g : E → ℝ} [IsSelfConcordantOnWith dom Mf g] [HasPositiveDefiniteHessianOn dom g]
    {y z : E} (hy : y ∈ dom) (hz : z ∈ dom)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    let h := z - y
    let r := ‖h‖[g; y]
    r / (1 + t * ((Mf : ℝ) * r)) ≤ ‖h‖[g; y + t • h] := by
  let hself : IsSelfConcordantOnWith dom Mf g := inferInstance
  dsimp
  by_cases ht_zero : t = 0
  · -- The zero segment parameter collapses both sides to the same local norm.
    subst ht_zero
    simp
  · have ht_pos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht_zero)
    have hseg :
        y + t • (z - y) ∈ dom := by
      -- Rewrite the segment point as a convex combination and use convexity of the domain.
      have hrewrite : y + t • (z - y) = (1 - t) • y + t • z := by
        rw [smul_sub]
        rw [show (1 - t : ℝ) • y = y - t • y by rw [sub_smul, one_smul]]
        abel
      have h1t : 0 ≤ 1 - t := by linarith
      have hsum : (1 - t) + t = 1 := by ring
      rw [hrewrite]
      exact hself.convex_domain hy hz h1t ht0 hsum
    have hdisp :
        ‖(y + t • (z - y)) - y‖[g; y + t • (z - y)] ≥
          ‖(y + t • (z - y)) - y‖[g; y] /
            (1 + (Mf : ℝ) * ‖(y + t • (z - y)) - y‖[g; y]) :=
      IsSelfConcordantOnWith.displacement_localNorm_lower_bound
        (hself := hself) (x := y) (y := y + t • (z - y)) hy hseg
    have hsub : (y + t • (z - y)) - y = t • (z - y) := by
      abel
    rw [hsub,
      hessianLocalNorm_smul_of_nonneg_ofPosDefMem (dom := dom) (g := g) hseg ht0,
      hessianLocalNorm_smul_of_nonneg_ofPosDefMem (dom := dom) (g := g) hy ht0] at hdisp
    have hscaled :
        t * (‖z - y‖[g; y] / (1 + t * ((Mf : ℝ) * ‖z - y‖[g; y]))) ≤
          t * ‖z - y‖[g; y + t • (z - y)] := by
      -- Pull the positive factor `t` out of the transport inequality before canceling it.
      simpa [div_eq_mul_inv, ht_zero, mul_assoc, mul_left_comm, mul_comm] using hdisp
    exact le_of_mul_le_mul_left hscaled ht_pos

/-- Helper for Theorem 5.1.12: convexity of the self-concordant domain keeps every intermediate
segment point inside `dom`. -/
private theorem segmentPoint_mem
    {g : E → ℝ} [IsSelfConcordantOnWith dom Mf g] {y z : E}
    (hy : y ∈ dom) (hz : z ∈ dom) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    y + t • (z - y) ∈ dom := by
  let hself : IsSelfConcordantOnWith dom Mf g := inferInstance
  -- Rewrite the affine interpolation point as the standard convex combination of `y` and `z`.
  have hrewrite : y + t • (z - y) = (1 - t) • y + t • z := by
    rw [smul_sub]
    rw [show (1 - t : ℝ) • y = y - t • y by rw [sub_smul, one_smul]]
    abel
  have h1t : 0 ≤ 1 - t := by linarith
  have hsum : (1 - t) + t = 1 := by ring
  rw [hrewrite]
  exact hself.convex_domain hy hz h1t ht0 hsum

/-- Helper for Theorem 5.1.12: once the Hessian quadratic form is nonnegative, squaring the local
norm recovers that quadratic form exactly. -/
private theorem sq_hessianLocalNorm_eq_inner_of_nonneg
    {g : E → ℝ} {z u : E} (hquad : 0 ≤ inner ℝ u (hessian g z u)) :
    ‖u‖[g; z] ^ (2 : ℕ) = inner ℝ u (hessian g z u) := by
  -- Expand the local norm and use `sqrt(x)^2 = x` on the nonnegative Hessian quadratic form.
  simpa [hessianLocalNorm_def] using Real.sq_sqrt hquad

omit [FiniteDimensional ℝ E] in
/-- Helper for Theorem 5.1.12: affine lines have the expected derivative. -/
private theorem line_hasDerivAt
    (z d : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ z + s • d) d t := by
  -- Differentiate the scalar parameter and keep the direction fixed.
  simpa [one_smul] using ((hasDerivAt_id t).smul_const d).const_add z

/-- Helper for Theorem 5.1.12: a pointwise `C²` hypothesis upgrades the gradient to a genuinely
Fréchet-differentiable map with derivative `hessian g z`. -/
private theorem gradient_hasFDerivAt_of_contDiffAt
    {g : E → ℝ} {z : E} (hz_C2 : ContDiffAt ℝ 2 g z) :
    HasFDerivAt (∇ g) (hessian g z) z := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfderiv : DifferentiableAt ℝ (fderiv ℝ g) z := by
    have hC1_fderiv : ContDiffAt ℝ 1 (fderiv ℝ g) z :=
      hz_C2.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    exact hC1_fderiv.differentiableAt one_ne_zero
  have hgradDiff : DifferentiableAt ℝ (∇ g) z := by
    -- Rewrite the gradient through the Riesz map before differentiating.
    simpa [gradient, D] using D.differentiableAt.comp z hfderiv
  -- The derivative of the gradient is the Hessian by definition.
  simpa [hessian] using hgradDiff.hasFDerivAt

/-- Helper for Theorem 5.1.12: self-concordance makes the Hessian vary continuously on the open
domain. -/
private theorem hessian_continuousOn
    {g : E → ℝ} [IsSelfConcordantOnWith dom Mf g] :
    ContinuousOn (hessian g) dom := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  let hself : IsSelfConcordantOnWith dom Mf g := inferInstance
  have hgrad_contDiff : ContDiffOn ℝ 1 (∇ g) dom := by
    have hfd : ContDiffOn ℝ 1 (fderiv ℝ g) dom :=
      hself.contDiffOn.fderiv_of_isOpen hself.isOpen_domain
        (show (1 : WithTop ℕ∞) + 1 ≤ (3 : WithTop ℕ∞) by norm_num)
    simpa [gradient, D] using D.contDiff.comp_contDiffOn hfd
  -- Differentiate the continuous gradient field once more to recover the Hessian map.
  simpa [hessian] using
    (hgrad_contDiff.fderiv_of_isOpen hself.isOpen_domain
      (show (0 : WithTop ℕ∞) + 1 ≤ (1 : WithTop ℕ∞) by norm_num)).continuousOn

/-- Helper for Theorem 5.1.12: differentiating `g` along an affine line recovers the gradient
pairing with the line direction. -/
private theorem value_line_hasDerivAt
    {g : E → ℝ} [IsSelfConcordantOnWith dom Mf g]
    {z d : E} {t : ℝ} (hzt : z + t • d ∈ dom) :
    HasDerivAt (fun s : ℝ ↦ g (z + s • d)) (inner ℝ (∇ g (z + t • d)) d) t := by
  let hself : IsSelfConcordantOnWith dom Mf g := inferInstance
  have hC1 : ContDiffAt ℝ 1 g (z + t • d) := by
    exact
      (hself.contDiffOn.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3)).contDiffAt
        (hself.isOpen_domain.mem_nhds hzt)
  -- Differentiate the ambient function first and then compose with the affine line.
  simpa using
    ((hC1.differentiableAt one_ne_zero).hasGradientAt.hasFDerivAt.comp t
      (line_hasDerivAt z d t).hasFDerivAt).hasDerivAt

/-- Helper for Theorem 5.1.12: scalarizing the gradient along an affine line differentiates to
the corresponding Hessian pairing. -/
private theorem scalarized_gradient_line_hasDerivAt
    {g : E → ℝ} [IsSelfConcordantOnWith dom Mf g]
    {z d w : E} {t : ℝ} (hzt : z + t • d ∈ dom) :
    HasDerivAt (fun s : ℝ ↦ inner ℝ (∇ g (z + s • d)) w)
      (inner ℝ (hessian g (z + t • d) d) w) t := by
  let hself : IsSelfConcordantOnWith dom Mf g := inferInstance
  have hz_C2 : ContDiffAt ℝ 2 g (z + t • d) := by
    exact
      (hself.contDiffOn.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).contDiffAt
        (hself.isOpen_domain.mem_nhds hzt)
  have hgradLine :
      HasFDerivAt (fun s : ℝ ↦ ∇ g (z + s • d))
        ((hessian g (z + t • d)).comp
          (ContinuousLinearMap.toSpanSingleton ℝ d)) t := by
    -- Route correction: differentiate the raw scalarized gradient line before subtracting any
    -- endpoint term.
    simpa using
      ((gradient_hasFDerivAt_of_contDiffAt (g := g) hz_C2).comp t
        (line_hasDerivAt z d t).hasFDerivAt)
  let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) w
  have hscalar :
      HasFDerivAt (fun s : ℝ ↦ φ (∇ g (z + s • d)))
        (φ.comp ((hessian g (z + t • d)).comp
          (ContinuousLinearMap.toSpanSingleton ℝ d))) t := by
    -- Postcompose with the scalar functional `v ↦ ⟪v, w⟫`.
    simpa [φ] using ((φ.hasFDerivAt).comp t hgradLine)
  simpa [φ, InnerProductSpace.toDual_apply_apply, real_inner_comm] using hscalar.hasDerivAt

/-- Helper for Theorem 5.1.12: the rational lower integrand integrates to the expected transport
factor `u r² / (1 + u a)`. -/
private theorem integralSqDivEqScaledSqDivAdd
    {a r u : ℝ} (hu : 0 ≤ u)
    (hden : ∀ t ∈ Set.Icc (0 : ℝ) u, 0 < 1 + t * a) :
    ∫ t in 0..u, r ^ (2 : ℕ) / (1 + t * a) ^ (2 : ℕ) =
      u * r ^ (2 : ℕ) / (1 + u * a) := by
  have hnum :
      ContinuousOn (fun t : ℝ ↦ t * r ^ (2 : ℕ) / (1 + t * a))
        (Set.Icc (0 : ℝ) u) := by
    refine (continuousOn_id.mul continuousOn_const).div ?_ ?_
    · exact (show Continuous (fun t : ℝ ↦ 1 + t * a) by continuity).continuousOn
    · intro t ht
      exact (hden t ht).ne'
  have hint :
      IntervalIntegrable
        (fun t : ℝ ↦ r ^ (2 : ℕ) / (1 + t * a) ^ (2 : ℕ))
        MeasureTheory.volume 0 u := by
    have hcont :
      ContinuousOn
        (fun t : ℝ ↦ r ^ (2 : ℕ) / (1 + t * a) ^ (2 : ℕ))
        (Set.Icc (0 : ℝ) u) := by
      refine continuousOn_const.div ?_ ?_
      · exact
          (show Continuous (fun t : ℝ ↦ (1 + t * a) ^ (2 : ℕ)) by
            continuity).continuousOn
      · intro t ht
        exact pow_ne_zero 2 (hden t ht).ne'
    exact hcont.intervalIntegrable_of_Icc hu
  have hderiv :
      ∀ t ∈ Set.Ioo (0 : ℝ) u,
        HasDerivAt
          (fun s : ℝ ↦ s * r ^ (2 : ℕ) / (1 + s * a))
          (r ^ (2 : ℕ) / (1 + t * a) ^ (2 : ℕ)) t := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) u := Set.mem_Icc_of_Ioo ht
    have hden_ne : 1 + t * a ≠ 0 := (hden t ht').ne'
    have hden_deriv :
        HasDerivAt (fun s : ℝ ↦ 1 + s * a) a t := by
      convert (hasDerivAt_const t (1 : ℝ)).add ((hasDerivAt_id t).mul_const a) using 1
      ring
    have hquot :=
      ((hasDerivAt_id t).mul_const (r ^ (2 : ℕ))).div hden_deriv hden_ne
    have hslope :
        ((1 : ℝ) * r ^ (2 : ℕ) * (1 + t * a) - t * r ^ (2 : ℕ) * a) /
            (1 + t * a) ^ (2 : ℕ) =
          r ^ (2 : ℕ) / (1 + t * a) ^ (2 : ℕ) := by
      field_simp [hden_ne]
      ring
    have hquot' :
        HasDerivAt
          (fun s : ℝ ↦ s * r ^ (2 : ℕ) / (1 + s * a))
          (((1 : ℝ) * r ^ (2 : ℕ) * (1 + t * a) - t * r ^ (2 : ℕ) * a) /
            (1 + t * a) ^ (2 : ℕ))
          t := by
      simpa using hquot
    exact hquot'.congr_deriv hslope
  have hftc :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hu hnum hderiv hint
  calc
    ∫ t in 0..u, r ^ (2 : ℕ) / (1 + t * a) ^ (2 : ℕ)
        = u * r ^ (2 : ℕ) / (1 + u * a) - (0 * r ^ (2 : ℕ) / (1 + 0 * a)) := by
            simpa using hftc
    _ = u * r ^ (2 : ℕ) / (1 + u * a) := by ring

/-- Helper for Theorem 5.1.12: along the segment from `y` to `z`, the scalarized gradient
increment dominates the source transport factor at the base point `y`. -/
private theorem segmentGradientIncrementLowerBoundAtBase
    {g : E → ℝ} [IsSelfConcordantOnWith dom Mf g] [HasPositiveDefiniteHessianOn dom g]
    {y z : E} (hy : y ∈ dom) (hz : z ∈ dom)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    let h := z - y
    let r := ‖h‖[g; y]
    inner ℝ (∇ g (y + u • h) - ∇ g y) h ≥
      u * r ^ (2 : ℕ) / (1 + u * ((Mf : ℝ) * r)) := by
  let h := z - y
  let r : ℝ := ‖h‖[g; y]
  let γ : ℝ → ℝ := fun t ↦ inner ℝ (∇ g (y + t • h)) h
  let θ : ℝ → ℝ := fun t ↦ inner ℝ h (hessian g (y + t • h) h)
  have hr_nonneg : 0 ≤ r := by
    simpa [r, h] using hessianLocalNorm_nonneg g y (z - y)
  have segment_gradient_line_continuousOn :
      ContinuousOn γ (Set.Icc (0 : ℝ) u) := by
    intro t ht
    have hyt : y + t • h ∈ dom := by
      exact
        segmentPoint_mem (dom := dom) (Mf := Mf) (g := g) hy hz
          ht.1 (le_trans ht.2 hu1)
    have hγ_cont : ContinuousAt γ t := by
      -- Bind the exact scalarized-gradient line before converting to a within-set continuity fact.
      simpa [γ] using
        (scalarized_gradient_line_hasDerivAt
          (dom := dom) (Mf := Mf) (g := g) (z := y) (d := h) (w := h) hyt).continuousAt
    exact hγ_cont.continuousWithinAt
  have segment_hessian_pairing_intervalIntegrable :
      IntervalIntegrable θ MeasureTheory.volume 0 u := by
    have hcont :
        ContinuousOn θ (Set.Icc (0 : ℝ) u) := by
      intro t ht
      have hyt : y + t • h ∈ dom := by
        exact
          segmentPoint_mem (dom := dom) (Mf := Mf) (g := g) hy hz
            ht.1 (le_trans ht.2 hu1)
      have hhess_on : ContinuousOn (hessian g) dom := hessian_continuousOn (dom := dom) (Mf := Mf)
      have hhess_cont : ContinuousAt (hessian g) (y + t • h) := by
        exact
          hhess_on.continuousAt
            ((inferInstance : IsSelfConcordantOnWith dom Mf g).isOpen_domain.mem_nhds hyt)
      have hline_cont : ContinuousAt (fun s : ℝ ↦ y + s • h) t :=
        (line_hasDerivAt y h t).continuousAt
      have hhess_line : ContinuousAt (fun s : ℝ ↦ hessian g (y + s • h)) t := by
        exact ContinuousAt.comp hhess_cont hline_cont
      let φh : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) h
      have happly_line : ContinuousAt (fun s : ℝ ↦ hessian g (y + s • h) h) t := by
        simpa using
          ContinuousAt.comp ((ContinuousLinearMap.apply ℝ E h).continuous.continuousAt) hhess_line
      have hinner_cont : ContinuousAt θ t := by
        simpa [θ, φh, InnerProductSpace.toDual_apply_apply, real_inner_comm] using
          ContinuousAt.comp φh.continuous.continuousAt happly_line
      exact hinner_cont.continuousWithinAt
    exact hcont.intervalIntegrable_of_Icc hu0
  have segment_gradient_pairing_eq_integral :
      inner ℝ (∇ g (y + u • h) - ∇ g y) h = ∫ s in 0..u, θ s := by
    have hderiv :
        ∀ t ∈ Set.Ioo (0 : ℝ) u, HasDerivAt γ (θ t) t := by
      intro t ht
      have hyt : y + t • h ∈ dom := by
        exact
          segmentPoint_mem (dom := dom) (Mf := Mf) (g := g) hy hz
            ht.1.le (le_trans (le_of_lt ht.2) hu1)
      simpa [γ, θ, real_inner_comm] using
        (scalarized_gradient_line_hasDerivAt
          (dom := dom) (Mf := Mf) (g := g) (z := y) (d := h) (w := h) hyt)
    have hftc :
        ∫ s in 0..u, θ s = γ u - γ 0 := by
      simpa using
        intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
          hu0 segment_gradient_line_continuousOn hderiv segment_hessian_pairing_intervalIntegrable
    -- Rewrite the endpoint difference of the scalarized gradient line as the desired pairing.
    calc
      inner ℝ (∇ g (y + u • h) - ∇ g y) h = γ u - γ 0 := by
        simp [γ, inner_sub_left]
      _ = ∫ s in 0..u, θ s := by
        symm
        exact hftc
  have hden_pos :
      ∀ t ∈ Set.Icc (0 : ℝ) u, 0 < 1 + t * ((Mf : ℝ) * r) := by
    intro t ht
    have hmul_nonneg : 0 ≤ t * ((Mf : ℝ) * r) := by
      exact mul_nonneg ht.1 (mul_nonneg Mf.2 hr_nonneg)
    linarith
  have segment_hessian_quadratic_lower_of_transport :
      ∀ t ∈ Set.Ioo (0 : ℝ) u,
        r ^ (2 : ℕ) / (1 + t * ((Mf : ℝ) * r)) ^ (2 : ℕ) ≤ θ t := by
    intro t ht
    have hyt : y + t • h ∈ dom := by
      exact
        segmentPoint_mem (dom := dom) (Mf := Mf) (g := g) hy hz
          ht.1.le (le_trans (le_of_lt ht.2) hu1)
    have hlower : r / (1 + t * ((Mf : ℝ) * r)) ≤ ‖h‖[g; y + t • h] := by
      simpa [r, h] using
        forwardLocalNormLowerBoundAlongSegment
          (dom := dom) (Mf := Mf) (g := g) hy hz
          (t := t) ht.1.le (le_trans (le_of_lt ht.2) hu1)
    have hlocal_nonneg : 0 ≤ ‖h‖[g; y + t • h] := hessianLocalNorm_nonneg g (y + t • h) h
    have hlhs_nonneg : 0 ≤ r / (1 + t * ((Mf : ℝ) * r)) := by
      exact div_nonneg hr_nonneg (le_of_lt (hden_pos t (Set.mem_Icc_of_Ioo ht)))
    have hsq :
        (r / (1 + t * ((Mf : ℝ) * r))) ^ (2 : ℕ) ≤ ‖h‖[g; y + t • h] ^ (2 : ℕ) := by
      nlinarith [hlower, hlhs_nonneg, hlocal_nonneg]
    have htheta_nonneg :
        0 ≤ inner ℝ h (hessian g (y + t • h) h) := by
      exact
        (HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem
          (dom := dom) (f := g) hyt).inner_nonneg_right h
    calc
      r ^ (2 : ℕ) / (1 + t * ((Mf : ℝ) * r)) ^ (2 : ℕ)
          = (r / (1 + t * ((Mf : ℝ) * r))) ^ (2 : ℕ) := by
              rw [div_pow]
      _ ≤ ‖h‖[g; y + t • h] ^ (2 : ℕ) := hsq
      _ = θ t := by
            simp [θ, sq_hessianLocalNorm_eq_inner_of_nonneg htheta_nonneg]
  have hint_lower :
      IntervalIntegrable
        (fun t : ℝ ↦ r ^ (2 : ℕ) / (1 + t * ((Mf : ℝ) * r)) ^ (2 : ℕ))
        MeasureTheory.volume 0 u := by
    have hcont :
        ContinuousOn
          (fun t : ℝ ↦ r ^ (2 : ℕ) / (1 + t * ((Mf : ℝ) * r)) ^ (2 : ℕ))
          (Set.Icc (0 : ℝ) u) := by
      have hden_cont : Continuous (fun t : ℝ ↦ (1 + t * ((Mf : ℝ) * r)) ^ (2 : ℕ)) := by
        continuity
      refine continuousOn_const.div ?_ ?_
      · exact hden_cont.continuousOn
      · intro t ht
        exact pow_ne_zero 2 (hden_pos t ht).ne'
    exact hcont.intervalIntegrable_of_Icc hu0
  have hmono :
      ∫ s in 0..u, r ^ (2 : ℕ) / (1 + s * ((Mf : ℝ) * r)) ^ (2 : ℕ) ≤
        ∫ s in 0..u, θ s := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo hu0 hint_lower
      segment_hessian_pairing_intervalIntegrable ?_
    intro s hs
    exact segment_hessian_quadratic_lower_of_transport s hs
  have hbound :
      u * r ^ (2 : ℕ) / (1 + u * ((Mf : ℝ) * r)) ≤
        inner ℝ (∇ g (y + u • h) - ∇ g y) h := by
    calc
      u * r ^ (2 : ℕ) / (1 + u * ((Mf : ℝ) * r))
          = ∫ s in 0..u, r ^ (2 : ℕ) / (1 + s * ((Mf : ℝ) * r)) ^ (2 : ℕ) := by
              symm
              simpa [r, mul_assoc, mul_left_comm, mul_comm] using
                integralSqDivEqScaledSqDivAdd
                  (u := u) (a := (Mf : ℝ) * r) (r := r) hu0 hden_pos
      _ ≤ ∫ s in 0..u, θ s := hmono
      _ = inner ℝ (∇ g (y + u • h) - ∇ g y) h := by
            symm
            exact segment_gradient_pairing_eq_integral
  simpa [h, r] using hbound

/-- Helper for Theorem 5.1.12: the first-order Taylor remainder along the segment from `y` to `z`
is the integral of the scalarized gradient increment. -/
private theorem segmentTaylorRemainderEqIntegral
    {g : E → ℝ} [IsSelfConcordantOnWith dom Mf g]
    {y z : E} (hy : y ∈ dom) (hz : z ∈ dom) :
    let h := z - y
    g z - g y - inner ℝ (∇ g y) h =
      ∫ u in 0..1, inner ℝ (∇ g (y + u • h) - ∇ g y) h := by
  let h := z - y
  let φ : ℝ → ℝ := fun u ↦ g (y + u • h)
  let γ : ℝ → ℝ := fun u ↦ inner ℝ (∇ g (y + u • h)) h
  have segment_value_line_continuousOn :
      ContinuousOn φ (Set.Icc (0 : ℝ) 1) := by
    intro u hu
    have huy : y + u • h ∈ dom := by
      exact segmentPoint_mem (dom := dom) (Mf := Mf) (g := g) hy hz hu.1 hu.2
    have hcont : ContinuousAt φ u :=
      (value_line_hasDerivAt (dom := dom) (Mf := Mf) (g := g) (z := y) (d := h) huy).continuousAt
    exact hcont.continuousWithinAt
  have segment_gradient_line_continuousOn :
      ContinuousOn γ (Set.Icc (0 : ℝ) 1) := by
    intro u hu
    have huy : y + u • h ∈ dom := by
      exact segmentPoint_mem (dom := dom) (Mf := Mf) (g := g) hy hz hu.1 hu.2
    have hcont : ContinuousAt γ u :=
      (scalarized_gradient_line_hasDerivAt
        (dom := dom) (Mf := Mf) (g := g) (z := y) (d := h) (w := h) huy).continuousAt
    exact hcont.continuousWithinAt
  have hintγ :
      IntervalIntegrable γ MeasureTheory.volume 0 1 := by
    exact segment_gradient_line_continuousOn.intervalIntegrable_of_Icc (by norm_num)
  have hderiv :
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt φ (γ t) t := by
    intro t ht
    have hyt : y + t • h ∈ dom := by
      exact segmentPoint_mem (dom := dom) (Mf := Mf) (g := g) hy hz ht.1.le (le_of_lt ht.2)
    simpa [φ, γ] using
      (value_line_hasDerivAt (dom := dom) (Mf := Mf) (g := g) (z := y) (d := h) hyt)
  have hftc :
      ∫ s in 0..1, γ s = φ 1 - φ 0 := by
    simpa using
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
        (show (0 : ℝ) ≤ 1 by norm_num) segment_value_line_continuousOn hderiv hintγ
  have hconst :
      IntervalIntegrable (fun _ : ℝ ↦ inner ℝ (∇ g y) h) MeasureTheory.volume 0 1 :=
    intervalIntegrable_const
  have hφ1 : φ 1 = g z := by
    -- The endpoint `u = 1` reaches `z`.
    dsimp [φ, h]
    simp [sub_eq_add_neg]
  have hφ0 : φ 0 = g y := by
    simp [φ]
  calc
    g z - g y - inner ℝ (∇ g y) h = (φ 1 - φ 0) - (1 : ℝ) * inner ℝ (∇ g y) h := by
      rw [hφ1, hφ0]
      ring
    _ = (∫ s in 0..1, γ s) - ∫ s in 0..1, inner ℝ (∇ g y) h := by
      rw [hftc, intervalIntegral.integral_const]
      ring
    _ = ∫ s in 0..1, (γ s - inner ℝ (∇ g y) h) := by
      symm
      simpa using (intervalIntegral.integral_sub hintγ hconst)
    _ = ∫ u in 0..1, inner ℝ (∇ g (y + u • h) - ∇ g y) h := by
      refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
      intro s
      simp [γ, inner_sub_left]

/-- Helper for Theorem 5.1.12: the second scalar integration in the lower Taylor proof evaluates
to the Chapter 5 auxiliary function `ω`. -/
private theorem integralMulSqDivEqOmega_baseDistance
    {r : ℝ} (hMf : Mf ≠ 0) (hr : 0 ≤ r) :
    let tω := selfConcordantOmegaArg Mf r (neg_one_lt_mf_mul_of_nonneg hr)
    ∫ t in 0..1, t * r ^ (2 : ℕ) / (1 + t * ((Mf : ℝ) * r)) =
      (1 / ((Mf : ℝ) ^ (2 : ℕ))) * ω tω := by
  let a : ℝ := (Mf : ℝ)
  let tω : Set.Ioi (-1 : ℝ) := selfConcordantOmegaArg Mf r (neg_one_lt_mf_mul_of_nonneg hr)
  have ha_pos_nn : 0 < Mf := lt_of_le_of_ne Mf.2 (Ne.symm hMf)
  have ha_pos : 0 < a := by
    exact_mod_cast ha_pos_nn
  have ha_ne : a ≠ 0 := ha_pos.ne'
  have hnum :
      ContinuousOn
        (fun t : ℝ ↦ (1 / (a ^ (2 : ℕ))) * (a * t * r - Real.log (1 + a * t * r)))
        (Set.Icc (0 : ℝ) 1) := by
    have hlog :
        ContinuousOn (fun t : ℝ ↦ Real.log (1 + a * t * r)) (Set.Icc (0 : ℝ) 1) := by
      refine Real.continuousOn_log.comp ?_ ?_
      · exact (show Continuous (fun t : ℝ ↦ 1 + a * t * r) by continuity).continuousOn
      · intro t ht
        have harg_nonneg : 0 ≤ a * t * r := by
          exact mul_nonneg (mul_nonneg ha_pos.le ht.1) hr
        have harg_pos : 0 < 1 + a * t * r := by
          linarith
        simpa [mul_assoc, mul_left_comm, mul_comm] using harg_pos.ne'
    have hlin :
        ContinuousOn (fun t : ℝ ↦ a * t * r) (Set.Icc (0 : ℝ) 1) := by
      exact (show Continuous (fun t : ℝ ↦ a * t * r) by continuity).continuousOn
    -- Keep the antiderivative in the exact `ω` normal form used at the endpoint.
    refine continuousOn_const.mul ?_
    exact hlin.sub hlog
  have hint :
      IntervalIntegrable
        (fun t : ℝ ↦ t * r ^ (2 : ℕ) / (1 + t * (Mf : ℝ) * r))
        MeasureTheory.volume 0 1 := by
    have hcont :
        ContinuousOn
          (fun t : ℝ ↦ t * r ^ (2 : ℕ) / (1 + t * (Mf : ℝ) * r))
          (Set.Icc (0 : ℝ) 1) := by
      refine (continuousOn_id.mul continuousOn_const).div ?_ ?_
      · exact (show Continuous (fun t : ℝ ↦ 1 + t * (Mf : ℝ) * r) by continuity).continuousOn
      · intro t ht
        have harg_nonneg : 0 ≤ t * ((Mf : ℝ) * r) := by
          exact mul_nonneg ht.1 (mul_nonneg ha_pos.le hr)
        have harg_pos : 0 < 1 + t * ((Mf : ℝ) * r) := by
          linarith
        simpa [mul_assoc, mul_left_comm, mul_comm] using harg_pos.ne'
    exact hcont.intervalIntegrable_of_Icc (by norm_num)
  have hderiv :
      ∀ t ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt
          (fun s : ℝ ↦ (1 / (a ^ (2 : ℕ))) * (a * s * r - Real.log (1 + a * s * r)))
          (t * r ^ (2 : ℕ) / (1 + t * a * r)) t := by
    intro t ht
    have harg_ne : 1 + a * t * r ≠ 0 := by
      have harg_nonneg : 0 ≤ a * t * r := by
        exact mul_nonneg (mul_nonneg ha_pos.le ht.1.le) hr
      have harg_pos : 0 < 1 + a * t * r := by
        linarith
      simpa [mul_assoc, mul_left_comm, mul_comm] using harg_pos.ne'
    have harg :
        HasDerivAt (fun s : ℝ ↦ 1 + a * s * r) (a * r) t := by
      convert
        (hasDerivAt_const t (1 : ℝ)).add ((((hasDerivAt_id t).const_mul a).mul_const r)) using 1
      ring
    have hlog :
        HasDerivAt (fun s : ℝ ↦ Real.log (1 + a * s * r))
          ((a * r) / (1 + a * t * r)) t := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (Real.hasDerivAt_log harg_ne).comp t harg
    have hlin :
        HasDerivAt (fun s : ℝ ↦ a * s * r) (a * r) t := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (((hasDerivAt_id t).const_mul a).mul_const r)
    have hcore :
        HasDerivAt
          (fun s : ℝ ↦ a * s * r - Real.log (1 + a * s * r))
          (a * r - (a * r) / (1 + a * t * r)) t := by
      simpa using hlin.sub hlog
    have hslope :
        (1 / (a ^ (2 : ℕ))) * (a * r - (a * r) / (1 + a * t * r)) =
          t * r ^ (2 : ℕ) / (1 + t * a * r) := by
      have hfactor :
          a * r - (a * r) / (1 + a * t * r) =
            (a ^ (2 : ℕ)) * (r ^ (2 : ℕ) * t) / (1 + a * t * r) := by
        have hcore :
            r - r * (1 + a * t * r)⁻¹ =
              r ^ (2 : ℕ) * a * t * (1 + a * t * r)⁻¹ := by
          have hfrac : 1 - (1 + a * t * r)⁻¹ = (a * t * r) * (1 + a * t * r)⁻¹ := by
            field_simp [harg_ne]
            ring
          calc
            r - r * (1 + a * t * r)⁻¹ = r * (1 - (1 + a * t * r)⁻¹) := by ring
            _ = r * ((a * t * r) * (1 + a * t * r)⁻¹) := by rw [hfrac]
            _ = r ^ (2 : ℕ) * a * t * (1 + a * t * r)⁻¹ := by ring
        calc
          a * r - (a * r) / (1 + a * t * r) =
              a * (r - r * (1 + a * t * r)⁻¹) := by
            field_simp [harg_ne]
          _ = a * (r ^ (2 : ℕ) * a * t * (1 + a * t * r)⁻¹) := by rw [hcore]
          _ = (a ^ (2 : ℕ)) * (r ^ (2 : ℕ) * t) / (1 + a * t * r) := by
            field_simp [harg_ne]
      calc
        (1 / (a ^ (2 : ℕ))) * (a * r - (a * r) / (1 + a * t * r))
            =
              (1 / (a ^ (2 : ℕ))) *
                ((a ^ (2 : ℕ)) * (r ^ (2 : ℕ) * t) / (1 + a * t * r)) := by
                rw [hfactor]
        _ = t * r ^ (2 : ℕ) / (1 + t * a * r) := by
          field_simp [ha_ne, harg_ne]
    have hscaled :
        HasDerivAt
          (fun s : ℝ ↦ (1 / (a ^ (2 : ℕ))) * (a * s * r - Real.log (1 + a * s * r)))
          ((1 / (a ^ (2 : ℕ))) * (a * r - (a * r) / (1 + a * t * r))) t := by
      simpa using (hasDerivAt_const t (1 / (a ^ (2 : ℕ)))).mul hcore
    exact hscaled.congr_deriv hslope
  have hftc :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (show (0 : ℝ) ≤ 1 by norm_num) hnum hderiv hint
  calc
    ∫ t in 0..1, t * r ^ (2 : ℕ) / (1 + t * ((Mf : ℝ) * r))
        = (1 / (a ^ (2 : ℕ))) * (a * 1 * r - Real.log (1 + a * 1 * r)) -
            (1 / (a ^ (2 : ℕ))) * (a * 0 * r - Real.log (1 + a * 0 * r)) := by
            simpa [a, mul_assoc, mul_left_comm, mul_comm] using hftc
    _ = (1 / (a ^ (2 : ℕ))) * (a * r - Real.log (1 + a * r)) := by
      simp [Real.log_one]
    _ = (1 / ((Mf : ℝ) ^ (2 : ℕ))) * ω tω := by
      simp [a, tω, selfConcordantOmega_apply, mul_comm]

/-- Helper for Theorem 5.1.12: the Taylor remainder from the base point `y` to `z` dominates the
canonical `ω` term built from the base local distance `‖z - y‖[g; y]`. -/
private theorem taylorLowerBound_fromBaseByLocalDistance_nonzero
    {g : E → ℝ} [IsSelfConcordantOnWith dom Mf g] [HasPositiveDefiniteHessianOn dom g]
    {y z : E} (hMf : Mf ≠ 0) (hy : y ∈ dom) (hz : z ∈ dom) :
    let h := z - y
    let r := ‖h‖[g; y]
    let tω := selfConcordantOmegaArg Mf r
      (neg_one_lt_mf_mul_of_nonneg (hessianLocalNorm_nonneg g y h))
    g z ≥
      g y + inner ℝ (∇ g y) h + (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω tω := by
  let h := z - y
  let r := ‖h‖[g; y]
  let tω : Set.Ioi (-1 : ℝ) :=
    selfConcordantOmegaArg Mf r
      (neg_one_lt_mf_mul_of_nonneg (hessianLocalNorm_nonneg g y h))
  let ψ : ℝ → ℝ := fun u ↦ inner ℝ (∇ g (y + u • h) - ∇ g y) h
  have hr_nonneg : 0 ≤ r := by
    simpa [r, h] using hessianLocalNorm_nonneg g y (z - y)
  have hMf_pos_nn : 0 < Mf := lt_of_le_of_ne Mf.2 (Ne.symm hMf)
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact_mod_cast hMf_pos_nn
  have hrem :
      g z - g y - inner ℝ (∇ g y) h = ∫ u in 0..1, ψ u := by
    -- The first FTC layer rewrites the Taylor remainder as the integral of the scalarized
    -- gradient increment along the segment from `y` to `z`.
    simpa [h, ψ] using
      segmentTaylorRemainderEqIntegral (dom := dom) (Mf := Mf) (g := g) hy hz
  have hψ_cont :
      ContinuousOn ψ (Set.Icc (0 : ℝ) 1) := by
    intro u hu
    have huy : y + u • h ∈ dom := by
      exact segmentPoint_mem (dom := dom) (Mf := Mf) (g := g) hy hz hu.1 hu.2
    have hγ_cont :
        ContinuousAt (fun s : ℝ ↦ inner ℝ (∇ g (y + s • h)) h) u := by
      exact
        (scalarized_gradient_line_hasDerivAt
          (dom := dom) (Mf := Mf) (g := g) (z := y) (d := h) (w := h) huy).continuousAt
    -- Subtract the base-point scalar pairing to match the integrand in the remainder identity.
    have hψ_cont_at : ContinuousAt ψ u := by
      have hconst_cont :
          ContinuousAt (fun _ : ℝ ↦ inner ℝ (∇ g y) h) u := continuousAt_const
      have hψ_eq :
          ψ = fun s : ℝ ↦ inner ℝ (∇ g (y + s • h)) h - inner ℝ (∇ g y) h := by
        funext s
        simp [ψ, inner_sub_left]
      rw [hψ_eq]
      exact hγ_cont.sub hconst_cont
    exact hψ_cont_at.continuousWithinAt
  have hintψ :
      IntervalIntegrable ψ MeasureTheory.volume 0 1 := by
    exact hψ_cont.intervalIntegrable_of_Icc (by norm_num)
  have hint_lower :
      IntervalIntegrable
        (fun u : ℝ ↦ u * r ^ (2 : ℕ) / (1 + u * ((Mf : ℝ) * r)))
        MeasureTheory.volume 0 1 := by
    have hcont :
      ContinuousOn
        (fun u : ℝ ↦ u * r ^ (2 : ℕ) / (1 + u * ((Mf : ℝ) * r)))
        (Set.Icc (0 : ℝ) 1) := by
      refine (continuousOn_id.mul continuousOn_const).div ?_ ?_
      · exact
          (show Continuous (fun u : ℝ ↦ 1 + u * ((Mf : ℝ) * r)) by
            continuity).continuousOn
      · intro u hu
        have hden_nonneg : 0 ≤ u * ((Mf : ℝ) * r) := by
          exact mul_nonneg hu.1 (mul_nonneg hMf_pos.le hr_nonneg)
        have hden_pos : 0 < 1 + u * ((Mf : ℝ) * r) := by
          linarith
        exact hden_pos.ne'
    exact hcont.intervalIntegrable_of_Icc (by norm_num)
  have hmono :
      ∫ u in 0..1, u * r ^ (2 : ℕ) / (1 + u * ((Mf : ℝ) * r)) ≤
        ∫ u in 0..1, ψ u := by
    refine intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ 1 by norm_num) hint_lower hintψ ?_
    intro u hu
    -- The segment-wise gradient increment lower bound is the pointwise integrand estimate.
    simpa [h, r, ψ] using
      segmentGradientIncrementLowerBoundAtBase
        (dom := dom) (Mf := Mf) (g := g) hy hz
        (u := u) hu.1 hu.2
  have hgap :
      (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω tω ≤
        g z - g y - inner ℝ (∇ g y) h := by
    calc
      (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω tω
          = ∫ u in 0..1, u * r ^ (2 : ℕ) / (1 + u * ((Mf : ℝ) * r)) := by
              symm
              simpa [r, tω, mul_assoc, mul_left_comm, mul_comm] using
                integralMulSqDivEqOmega_baseDistance
                  (Mf := Mf) (r := r) hMf hr_nonneg
      _ ≤ ∫ u in 0..1, ψ u := hmono
      _ = g z - g y - inner ℝ (∇ g y) h := by
            symm
            exact hrem
  -- Add the lower remainder term back to the affine Taylor model at the base point `y`.
  linarith

/-- Helper for Theorem 5.1.12: a quadratic family bounded above by `c` forces the discriminant
estimate `a² ≤ b c`. -/
private theorem sq_le_mul_of_quadratic_family
    {a b c : ℝ} (hb : 0 ≤ b)
    (hline : ∀ t : ℝ, 2 * t * a - t ^ (2 : ℕ) * b ≤ c) :
    a ^ (2 : ℕ) ≤ b * c := by
  -- Route correction: use the stable discriminant argument already employed in the later Chapter 5
  -- Hessian-duality files instead of growing a target-local algebra chain.
  by_cases hb_zero : b = 0
  · by_cases ha_zero : a = 0
    · simp [ha_zero, hb_zero]
    · have htest := hline ((|c| + 1) / a)
      have hcontr : 2 * (|c| + 1) ≤ c := by
        have hrew : 2 * ((|c| + 1) / a) * a ≤ c := by
          simpa [hb_zero] using htest
        field_simp [ha_zero] at hrew
        linarith
      nlinarith [hcontr, le_abs_self c, abs_nonneg c]
  · have hb_pos : 0 < b := lt_of_le_of_ne hb (by simpa [eq_comm] using hb_zero)
    have htest := hline (a / b)
    have hrewrite :
        2 * (a / b) * a - (a / b) ^ (2 : ℕ) * b = a ^ (2 : ℕ) / b := by
      field_simp [hb_zero]
      ring
    have hquot : a ^ (2 : ℕ) / b ≤ c := by
      simpa [hrewrite] using htest
    simpa [mul_comm] using (div_le_iff₀ hb_pos).1 hquot

/-- Helper for Theorem 5.1.12: the base-point gradient pairing is controlled by the Hessian dual
local norm times the base local distance to the comparison point. -/
private theorem gradientPairing_le_dualLocalNorm_mul_baseDistance
    {g : E → ℝ} [HasPositiveDefiniteHessianOn dom g]
    {y z : E} (hy : y ∈ dom) :
    let δ := HessianDualLocalNorm.ofPosDefMem g hy ((toDual ℝ E) (∇ g y))
    inner ℝ (∇ g y) (y - z) ≤ δ * ‖z - y‖[g; y] := by
  dsimp
  let H := hessian g y
  let w := H.inverse (∇ g y)
  have hPos : H.IsPositive := HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem hy
  have hInv : H.IsInvertible := hessian_isInvertible_of_det_ne_zero
    (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hy)
  have hHw : H w = ∇ g y := by
    dsimp [w, H]
    exact hInv.self_apply_inverse (∇ g y)
  have hquad : 0 ≤ inner ℝ (y - z) (H (y - z)) := hPos.inner_nonneg_right (y - z)
  have hpair_nonneg : 0 ≤ inner ℝ (∇ g y) w := by
    -- The inverse-Hessian pairing is a positive quadratic form at `w`.
    calc
      0 ≤ inner ℝ w (H w) := hPos.inner_nonneg_right w
      _ = inner ℝ (∇ g y) w := by rw [hHw, real_inner_comm]
  have hline :
      ∀ t : ℝ,
        2 * t * inner ℝ (∇ g y) (y - z) -
            t ^ (2 : ℕ) * inner ℝ (y - z) (H (y - z)) ≤
          inner ℝ (∇ g y) w := by
    intro t
    have hnonneg : 0 ≤ inner ℝ (t • (y - z) - w) (H (t • (y - z) - w)) :=
      hPos.inner_nonneg_right (t • (y - z) - w)
    have hcross :
        inner ℝ w (H (y - z)) = inner ℝ (∇ g y) (y - z) := by
      calc
        inner ℝ w (H (y - z)) = inner ℝ (H w) (y - z) := by
          simpa [real_inner_comm] using hPos.isSymmetric (y - z) w
        _ = inner ℝ (∇ g y) (y - z) := by rw [hHw]
    have hrewrite :
        inner ℝ (t • (y - z) - w) (H (t • (y - z) - w)) =
          t ^ (2 : ℕ) * inner ℝ (y - z) (H (y - z)) -
            2 * t * inner ℝ (∇ g y) (y - z) + inner ℝ (∇ g y) w := by
      -- Expand the quadratic form and rewrite the mixed terms using `H w = ∇ g y`.
      have hleft :
          inner ℝ (t • (y - z)) (H w) = t * inner ℝ (∇ g y) (y - z) := by
        rw [hHw, real_inner_comm, inner_smul_right]
      have hright :
          inner ℝ w (t • H (y - z)) = t * inner ℝ (∇ g y) (y - z) := by
        rw [inner_smul_right, hcross]
      have hdiag :
          inner ℝ w (H w) = inner ℝ (∇ g y) w := by
        rw [hHw, real_inner_comm]
      rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right]
      rw [ContinuousLinearMap.map_smul, inner_smul_left, inner_smul_right]
      rw [hleft, hright, hdiag]
      have hstar_t : (starRingEnd ℝ) t = t := by simp
      rw [hstar_t]
      ring_nf
    rw [hrewrite] at hnonneg
    nlinarith
  have hsq_raw :
      (inner ℝ (∇ g y) (y - z)) ^ (2 : ℕ) ≤
        inner ℝ (y - z) (H (y - z)) * inner ℝ (∇ g y) w := by
    have hsq :=
      sq_le_mul_of_quadratic_family
        (a := inner ℝ (∇ g y) (y - z))
        (b := inner ℝ (y - z) (H (y - z)))
        (c := inner ℝ (∇ g y) w)
        hquad hline
    simpa [mul_comm] using hsq
  have hdual_sq :
      (HessianDualLocalNorm.ofPosDefMem g hy ((toDual ℝ E) (∇ g y))) ^ (2 : ℕ) =
        inner ℝ (∇ g y) w := by
    rw [HessianDualLocalNorm.ofPosDefMem_def]
    simpa [w, H, pow_two, real_inner_comm, InnerProductSpace.toDual_apply_apply] using
      Real.sq_sqrt hpair_nonneg
  have hlocal_sq : ‖y - z‖[g; y] ^ (2 : ℕ) = inner ℝ (y - z) (H (y - z)) := by
    rw [hessianLocalNorm_def]
    simpa [H] using Real.sq_sqrt hquad
  have hsq_abs :
      |inner ℝ (∇ g y) (y - z)| ^ (2 : ℕ) ≤
        (HessianDualLocalNorm.ofPosDefMem g hy ((toDual ℝ E) (∇ g y)) *
          ‖y - z‖[g; y]) ^ (2 : ℕ) := by
    calc
      |inner ℝ (∇ g y) (y - z)| ^ (2 : ℕ) =
          (inner ℝ (∇ g y) (y - z)) ^ (2 : ℕ) := by
            rw [sq_abs]
      _ ≤ inner ℝ (y - z) (H (y - z)) * inner ℝ (∇ g y) w := hsq_raw
      _ =
          (HessianDualLocalNorm.ofPosDefMem g hy ((toDual ℝ E) (∇ g y))) ^ (2 : ℕ) *
            ‖y - z‖[g; y] ^ (2 : ℕ) := by
              rw [hdual_sq, hlocal_sq, mul_comm]
      _ =
          (HessianDualLocalNorm.ofPosDefMem g hy ((toDual ℝ E) (∇ g y)) *
            ‖y - z‖[g; y]) ^ (2 : ℕ) := by
              ring
  have hdual_nonneg :
      0 ≤ HessianDualLocalNorm.ofPosDefMem g hy ((toDual ℝ E) (∇ g y)) := by
    rw [HessianDualLocalNorm.ofPosDefMem_def]
    exact Real.sqrt_nonneg _
  have hbound_abs :
      |inner ℝ (∇ g y) (y - z)| ≤
        HessianDualLocalNorm.ofPosDefMem g hy ((toDual ℝ E) (∇ g y)) * ‖y - z‖[g; y] := by
    exact le_of_sq_le_sq hsq_abs
      (mul_nonneg hdual_nonneg (hessianLocalNorm_nonneg g y (y - z)))
  calc
    inner ℝ (∇ g y) (y - z) ≤ |inner ℝ (∇ g y) (y - z)| := le_abs_self _
    _ ≤
        HessianDualLocalNorm.ofPosDefMem g hy ((toDual ℝ E) (∇ g y)) *
          ‖y - z‖[g; y] := hbound_abs
    _ = HessianDualLocalNorm.ofPosDefMem g hy ((toDual ℝ E) (∇ g y)) * ‖z - y‖[g; y] := by
      rw [show y - z = -(z - y) by abel, hessianLocalNorm_neg]

/-- Helper for Theorem 5.1.12: the scalar Fenchel--Young inequality eliminates the remaining base
distance in favor of the canonical `ω_*` term. -/
private theorem fenchelEliminate_baseDistance
    {r δ : ℝ} (hMf : Mf ≠ 0) (hr : 0 ≤ r) (hδ : δ < 1 / (Mf : ℝ)) :
    let tω := selfConcordantOmegaArg Mf r (neg_one_lt_mf_mul_of_nonneg hr)
    let τω := selfConcordantOmegaStarArg Mf δ (mf_mul_lt_one_of_lt_inv hδ)
    δ * r - (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω tω ≤
      (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω_* τω := by
  let tω := selfConcordantOmegaArg Mf r (neg_one_lt_mf_mul_of_nonneg hr)
  let τω := selfConcordantOmegaStarArg Mf δ (mf_mul_lt_one_of_lt_inv hδ)
  have hMf_pos_nn : 0 < Mf := lt_of_le_of_ne Mf.2 (Ne.symm hMf)
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact_mod_cast hMf_pos_nn
  have hcore :
      ω tω + ω_* τω ≥ ((Mf : ℝ) * δ) * ((Mf : ℝ) * r) := by
    -- Normalize the chapter-scale arguments to the unit-scale Fenchel--Young inequality.
    simpa [tω, τω, mul_assoc, mul_left_comm, mul_comm] using
      (selfConcordantOmega_add_selfConcordantOmegaStar_ge_mul
        (t := (Mf : ℝ) * r) (τ := (Mf : ℝ) * δ)
        (by exact mul_nonneg Mf.2 hr) (mf_mul_lt_one_of_lt_inv hδ))
  have hscale : 0 < 1 / (Mf : ℝ) ^ (2 : ℕ) := by
    positivity
  have hscaled :
      (1 / (Mf : ℝ) ^ (2 : ℕ)) * (((Mf : ℝ) * δ) * ((Mf : ℝ) * r)) ≤
        (1 / (Mf : ℝ) ^ (2 : ℕ)) * (ω tω + ω_* τω) := by
    exact mul_le_mul_of_nonneg_left hcore hscale.le
  have hrewrite :
      (1 / (Mf : ℝ) ^ (2 : ℕ)) * (((Mf : ℝ) * δ) * ((Mf : ℝ) * r)) = δ * r := by
    field_simp [hMf_pos.ne']
  linarith [hscaled, hrewrite]

/-- Helper for Theorem 5.1.12: the open-Dikin hypothesis rewrites to the corresponding strict
local-norm inequality at the base point. -/
private theorem localNorm_lt_inv_of_memOpenDikinEllipsoid
    {g : E → ℝ} {x y : E}
    (hxy : y ∈ W⁰[g; x](1 / (Mf : ℝ))) :
    ‖y - x‖[g; x] < 1 / (Mf : ℝ) := by
  simpa using (mem_openDikinEllipsoid_iff g x y (1 / (Mf : ℝ))).1 hxy

/-- Helper for Theorem 5.1.12: membership in the reciprocal-radius Dikin ellipsoid forces
`M_f > 0`. -/
private theorem mf_pos_of_memOpenDikinEllipsoid
    {g : E → ℝ} {x y : E}
    (hxy : y ∈ W⁰[g; x](1 / (Mf : ℝ))) :
    0 < (Mf : ℝ) := by
  let r := ‖y - x‖[g; x]
  have hr : r < 1 / (Mf : ℝ) := by
    simpa [r] using localNorm_lt_inv_of_memOpenDikinEllipsoid (Mf := Mf) (g := g) hxy
  have hr_nonneg : 0 ≤ r := by
    simpa [r] using hessianLocalNorm_nonneg g x (y - x)
  have hMf_nonneg : 0 ≤ (Mf : ℝ) := by
    exact_mod_cast Mf.2
  by_contra hMf_nonpos
  have hMf_eq_zero : (Mf : ℝ) = 0 := le_antisymm (le_of_not_gt hMf_nonpos) hMf_nonneg
  have hr_neg : r < 0 := by
    simpa [hMf_eq_zero] using hr
  linarith

/-- Helper for Theorem 5.1.12: the rational upper transport integrand integrates to the expected
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

/-- Helper for Theorem 5.1.12: the second scalar integration in the Dikin-step upper Taylor
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

/-- Helper for Theorem 5.1.12: every admissible Dikin step satisfies the owner-level upper Taylor
bound with remainder `ω_*`. -/
private theorem taylorUpperBound_withSelfConcordantOmegaStar_of_memOpenDikinEllipsoid
    {g : E → ℝ} [IsSelfConcordantOnWith dom Mf g] [HasPositiveDefiniteHessianOn dom g]
    {x y : E} (hx : x ∈ dom) (hxy : y ∈ W⁰[g; x](1 / (Mf : ℝ))) :
    let r := ‖y - x‖[g; x]
    let τω := selfConcordantOmegaStarArg Mf r
      (mf_mul_lt_one_of_lt_inv (localNorm_lt_inv_of_memOpenDikinEllipsoid (Mf := Mf) (g := g) hxy))
    g y ≤
      g x + inner ℝ (∇ g x) (y - x) +
        (1 / ((Mf : ℝ) ^ (2 : ℕ))) * ω_* τω := by
  dsimp
  let hself : IsSelfConcordantOnWith dom Mf g := inferInstance
  let h : E := y - x
  let r : ℝ := ‖h‖[g; x]
  let φ : ℝ → ℝ := fun u ↦ g (x + u • h)
  let γ : ℝ → ℝ := fun u ↦ inner ℝ (∇ g (x + u • h)) h
  let ψ : ℝ → ℝ := fun u ↦ inner ℝ (∇ g (x + u • h) - ∇ g x) h
  let Φ : ℝ → ℝ := fun u ↦ g (x + u • h) - g x - u * inner ℝ (∇ g x) h
  let τω : Set.Iio (1 : ℝ) := selfConcordantOmegaStarArg Mf r
    (mf_mul_lt_one_of_lt_inv (localNorm_lt_inv_of_memOpenDikinEllipsoid (Mf := Mf) (g := g) hxy))
  have hr : r < 1 / (Mf : ℝ) := by
    simpa [h, r] using localNorm_lt_inv_of_memOpenDikinEllipsoid (Mf := Mf) (g := g) hxy
  have hr_nonneg : 0 ≤ r := by
    simpa [h, r] using hessianLocalNorm_nonneg g x (y - x)
  have hMf_pos : 0 < (Mf : ℝ) := mf_pos_of_memOpenDikinEllipsoid (Mf := Mf) (g := g) hxy
  have hsegment :
      ∀ {τ : ℝ}, τ ∈ Set.Icc (0 : ℝ) 1 →
        x + τ • h ∈ dom ∧
          ‖τ • h‖[g; x + τ • h] ≤ (τ * r) / (1 - (Mf : ℝ) * τ * r) := by
    intro τ hτ
    have hτ_nonneg : 0 ≤ τ := hτ.1
    have hτr_le_r : τ * r ≤ r := by
      simpa using mul_le_mul_of_nonneg_right hτ.2 hr_nonneg
    have hτr_lt : τ * r < 1 / (Mf : ℝ) := lt_of_le_of_lt hτr_le_r hr
    have hscaled_lt : ‖τ • h‖[g; x] < 1 / (Mf : ℝ) := by
      rw [hessianLocalNorm_smul_of_nonneg_ofPosDefMem
        (dom := dom) (g := g) (y := x) hx hτ_nonneg]
      exact hτr_lt
    have hstep_mem : x + τ • h ∈ dom := by
      exact
        (IsSelfConcordantOnWith.openDikinEllipsoid_inv_constant_subset
          (domain := dom) (Mf := Mf) (f := g) hself hx)
          ((mem_openDikinEllipsoid_iff g x (x + τ • h) (1 / (Mf : ℝ))).2 <|
            by
              have hsub : (x + τ • h) - x = τ • h := by abel
              simpa [hsub] using hscaled_lt)
    have htransport :=
      IsSelfConcordantOnWith.displacement_localNorm_upper_bound
        (hself := hself) (x := x) (y := x + τ • h) hx hstep_mem
        (by
          have hsub : (x + τ • h) - x = τ • h := by abel
          simpa [hsub] using hscaled_lt)
    constructor
    · exact hstep_mem
    · have hsub : (x + τ • h) - x = τ • h := by abel
      simpa [h, r, hsub,
        hessianLocalNorm_smul_of_nonneg_ofPosDefMem
          (dom := dom) (g := g) (y := x) hx hτ_nonneg,
        mul_assoc, mul_left_comm, mul_comm] using htransport
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
  let θ : ℝ → ℝ := fun u ↦ inner ℝ h (hessian g (x + u • h) h)
  have segment_hessian_quadratic_upper_of_transport :
      ∀ {u : ℝ}, u ∈ Set.Ioo (0 : ℝ) 1 →
        θ u ≤ r ^ (2 : ℕ) / (1 - (Mf : ℝ) * u * r) ^ (2 : ℕ) := by
    intro u hu
    have huIcc : u ∈ Set.Icc (0 : ℝ) 1 := Set.mem_Icc_of_Ioo hu
    have hxu : x + u • h ∈ dom := (hsegment huIcc).1
    have hu_nonneg : 0 ≤ u := hu.1.le
    have hlocal_bound :
        ‖u • h‖[g; x + u • h] ≤ (u * r) / (1 - (Mf : ℝ) * u * r) := (hsegment huIcc).2
    have hquad_scaled :
        0 ≤ inner ℝ (u • h) (hessian g (x + u • h) (u • h)) := by
      exact
        (HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem
          (dom := dom) (f := g) hxu).inner_nonneg_right (u • h)
    have hnorm_sq_bound :
        ‖u • h‖[g; x + u • h] ^ (2 : ℕ) ≤
          ((u * r) / (1 - (Mf : ℝ) * u * r)) ^ (2 : ℕ) := by
      have hright_nonneg : 0 ≤ (u * r) / (1 - (Mf : ℝ) * u * r) := by
        exact div_nonneg (mul_nonneg hu_nonneg hr_nonneg) (hden_on huIcc ⟨hu.1.le, le_rfl⟩).le
      nlinarith [hessianLocalNorm_nonneg g (x + u • h) (u • h), hlocal_bound, hright_nonneg]
    have hsq_eq :
        ‖u • h‖[g; x + u • h] ^ (2 : ℕ) =
          inner ℝ (u • h) (hessian g (x + u • h) (u • h)) := by
      simpa using
        sq_hessianLocalNorm_eq_inner_of_nonneg
          (g := g) (z := x + u • h) (u := u • h) hquad_scaled
    have hscaled_ineq :
        inner ℝ (u • h) (hessian g (x + u • h) (u • h)) ≤
          ((u * r) / (1 - (Mf : ℝ) * u * r)) ^ (2 : ℕ) := by
      calc
        inner ℝ (u • h) (hessian g (x + u • h) (u • h)) =
            ‖u • h‖[g; x + u • h] ^ (2 : ℕ) := by
              symm
              exact hsq_eq
        _ ≤ ((u * r) / (1 - (Mf : ℝ) * u * r)) ^ (2 : ℕ) := hnorm_sq_bound
    have hscaled_ineq' :
        (u ^ (2 : ℕ)) * θ u ≤
          (u ^ (2 : ℕ)) * (r ^ (2 : ℕ) / (1 - (Mf : ℝ) * u * r) ^ (2 : ℕ)) := by
      simpa [θ, pow_two, inner_smul_left, inner_smul_right, mul_assoc, mul_left_comm, mul_comm,
        div_eq_mul_inv] using hscaled_ineq
    have hfinal :
        θ u ≤ r ^ (2 : ℕ) / (1 - (Mf : ℝ) * u * r) ^ (2 : ℕ) := by
      have husq_pos : 0 < u ^ (2 : ℕ) := by
        nlinarith [hu.1]
      nlinarith [hscaled_ineq', husq_pos]
    exact hfinal
  have segment_gradient_line_continuousOn :
      ContinuousOn γ (Set.Icc (0 : ℝ) 1) := by
    intro u hu
    have hxu : x + u • h ∈ dom := (hsegment hu).1
    have hcont : ContinuousAt γ u :=
      (scalarized_gradient_line_hasDerivAt
        (dom := dom) (Mf := Mf) (g := g) (z := x) (d := h) (w := h) hxu).continuousAt
    exact hcont.continuousWithinAt
  have segment_hessian_pairing_intervalIntegrable :
      ∀ {u : ℝ}, u ∈ Set.Icc (0 : ℝ) 1 →
        IntervalIntegrable θ MeasureTheory.volume 0 u := by
    intro u hu
    have hcont :
        ContinuousOn θ (Set.Icc (0 : ℝ) u) := by
      intro t ht
      have hxt : x + t • h ∈ dom := (hsegment ⟨ht.1, le_trans ht.2 hu.2⟩).1
      have hhess_on : ContinuousOn (hessian g) dom := hessian_continuousOn (dom := dom) (Mf := Mf)
      have hhess_cont : ContinuousAt (hessian g) (x + t • h) := by
        exact hhess_on.continuousAt (hself.isOpen_domain.mem_nhds hxt)
      have hline_cont : ContinuousAt (fun s : ℝ ↦ x + s • h) t :=
        (line_hasDerivAt x h t).continuousAt
      have hhess_line : ContinuousAt (fun s : ℝ ↦ hessian g (x + s • h)) t := by
        exact ContinuousAt.comp hhess_cont hline_cont
      let φh : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) h
      have happly_line : ContinuousAt (fun s : ℝ ↦ hessian g (x + s • h) h) t := by
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
        (hsegment ⟨ht.1.le, le_of_lt (lt_of_lt_of_le ht.2 hu.2)⟩).1
      simpa [γ, θ, real_inner_comm] using
        (scalarized_gradient_line_hasDerivAt
          (dom := dom) (Mf := Mf) (g := g) (z := x) (d := h) (w := h) hxt)
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
  have segment_gradient_pairing_upper_of_transport :
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
      exact
        segment_hessian_quadratic_upper_of_transport
          (u := s) ⟨hs.1, lt_of_lt_of_le hs.2 hu.2⟩
    calc
      ψ u = ∫ s in 0..u, θ s := segment_gradient_pairing_eq_integral hu
      _ ≤ ∫ s in 0..u, r ^ (2 : ℕ) / (1 - (Mf : ℝ) * s * r) ^ (2 : ℕ) := hmono
      _ = u * r ^ (2 : ℕ) / (1 - (Mf : ℝ) * u * r) := by
        exact integralSqDivEqScaledSqDivSub (Mf := Mf) hu.1 (hden := fun t ht ↦ hden_on hu ht)
  have segment_value_line_continuousOn :
      ContinuousOn φ (Set.Icc (0 : ℝ) 1) := by
    intro u hu
    have hxu : x + u • h ∈ dom := (hsegment hu).1
    have hφ_cont : ContinuousAt φ u := by
      -- Bind the exact value-line map before moving to the segment-restricted continuity goal.
      simpa [φ] using
        (value_line_hasDerivAt
          (dom := dom) (Mf := Mf) (g := g) (z := x) (d := h) hxu).continuousAt
    exact hφ_cont.continuousWithinAt
  have segment_gradient_pairing_continuousOn :
      ContinuousOn ψ (Set.Icc (0 : ℝ) 1) := by
    have hconst : ContinuousOn (fun _ : ℝ ↦ inner ℝ (∇ g x) h) (Set.Icc (0 : ℝ) 1) :=
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
        (hsegment ⟨ht.1.le, le_of_lt (lt_of_lt_of_le ht.2 hu.2)⟩).1
      simpa [φ, γ] using
        (value_line_hasDerivAt
          (dom := dom) (Mf := Mf) (g := g) (z := x) (d := h) hxt)
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
  have segment_value_upper_of_transport :
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
      exact segment_gradient_pairing_upper_of_transport (u := s) ⟨hs.1, le_trans hs.2 hu.2⟩
    calc
      Φ u = ∫ s in 0..u, ψ s := segment_value_remainder_eq_integral hu
      _ ≤ ∫ s in 0..u, s * r ^ (2 : ℕ) / (1 - (Mf : ℝ) * s * r) := hmono
      _ =
          (1 / ((Mf : ℝ) ^ (2 : ℕ))) *
            (-(Mf : ℝ) * (u * r) - Real.log (1 - (Mf : ℝ) * (u * r))) := by
              exact integralMulSqDivEqOmegaStarAlongDikin
                (Mf := Mf) hu.1 hMf_pos (hden := fun t ht ↦ hden_on hu ht)
  have hvalue_endpoint_raw := segment_value_upper_of_transport (u := 1) ⟨by norm_num, le_rfl⟩
  have hPhi1 : Φ 1 = g y - g x - inner ℝ (∇ g x) h := by
    dsimp [Φ, φ]
    have hy_line : x + (1 : ℝ) • h = y := by
      dsimp [h]
      simp [sub_eq_add_neg]
    rw [hy_line]
    ring
  have hrem :
      g y - g x - inner ℝ (∇ g x) h ≤
        (1 / ((Mf : ℝ) ^ (2 : ℕ))) *
          (-(Mf : ℝ) * r - Real.log (1 - (Mf : ℝ) * r)) := by
    simpa [hPhi1, one_mul] using hvalue_endpoint_raw
  have hmain :
      g y ≤
        g x + inner ℝ (∇ g x) h +
          (1 / ((Mf : ℝ) ^ (2 : ℕ))) *
            (-(Mf : ℝ) * r - Real.log (1 - (Mf : ℝ) * r)) := by
    linarith
  have hτω : (τω : ℝ) = (Mf : ℝ) * r := by
    simp [τω]
  calc
    g y ≤
        g x + inner ℝ (∇ g x) h +
          (1 / ((Mf : ℝ) ^ (2 : ℕ))) *
            (-(Mf : ℝ) * r - Real.log (1 - (Mf : ℝ) * r)) := hmain
    _ =
        g x + inner ℝ (∇ g x) h +
          (1 / ((Mf : ℝ) ^ (2 : ℕ))) * ω_* τω := by
            rw [selfConcordantOmegaStar_apply, hτω]
            ring

/-- Helper for Theorem 5.1.12: once a self-concordant objective is minimized at `xStar`, its
suboptimality at `y` admits the lower `ω` bound in terms of the dual local norm of `∇ g(y)`. -/
private theorem suboptimalityLowerBound_ofDualGradientNorm_atMinimizer
    {g : E → ℝ} [IsSelfConcordantOnWith dom Mf g] [HasPositiveDefiniteHessianOn dom g]
    {xStar y : E} (hxStar : xStar ∈ dom) (hmin : IsMinOn g dom xStar) (hy : y ∈ dom) :
    let δ := HessianDualLocalNorm.ofPosDefMem g hy ((toDual ℝ E) (∇ g y))
    let tω := selfConcordantOmegaArg Mf δ
      (neg_one_lt_mf_mul_of_nonneg
        (dualGradientDualLocalNorm_nonneg (dom := dom) (g := g) y hy))
    g y ≥
      g xStar +
        (if Mf = 0 then
          δ ^ (2 : ℕ) / 2
        else
          (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω tω) := by
  dsimp
  by_cases hMf0 : Mf = 0
  · have hzeroEq :
        g y =
          g xStar +
            (HessianDualLocalNorm.ofPosDefMem g hy ((toDual ℝ E) (∇ g y))) ^ (2 : ℕ) / 2 := by
      simpa using
        zeroParameterSuboptimality_eq_halfDualGradientNormSq_atMinimizer
          (dom := dom) (Mf := Mf) (g := g) hMf0 hxStar hmin hy
    simpa [hMf0] using hzeroEq.ge
  · let δ := HessianDualLocalNorm.ofPosDefMem g hy ((toDual ℝ E) (∇ g y))
    let tω : Set.Ioi (-1 : ℝ) := selfConcordantOmegaArg Mf δ
      (neg_one_lt_mf_mul_of_nonneg
        (dualGradientDualLocalNorm_nonneg (dom := dom) (g := g) y hy))
    let α : ℝ := 1 / (1 + (Mf : ℝ) * δ)
    let v : E := (hessian g y).inverse (∇ g y)
    let yPlus : E := y - α • v
    let τω : Set.Iio (1 : ℝ) :=
      selfConcordantOmegaStarArg 1 (ω' tω) (by
        simpa using selfConcordantOmegaDeriv_lt_one tω)
    have hMf_ne : (Mf : ℝ) ≠ 0 := by
      exact_mod_cast hMf0
    have hyPlus_mem : yPlus ∈ W⁰[g; y](1 / (Mf : ℝ)) := by
      simpa [δ, α, v, yPlus] using
        dampedDualGradientProbe_mem_openDikinEllipsoid
          (dom := dom) (Mf := Mf) (g := g) hy hMf0
    have hyPlus_dom : yPlus ∈ dom := by
      exact
        (IsSelfConcordantOnWith.openDikinEllipsoid_inv_constant_subset
          (domain := dom) (Mf := Mf) (f := g) inferInstance hy) hyPlus_mem
    have hupper_raw :=
      taylorUpperBound_withSelfConcordantOmegaStar_of_memOpenDikinEllipsoid
        (dom := dom) (Mf := Mf) (g := g) hy hyPlus_mem
    have hωStar_transport :
        ω_* (selfConcordantOmegaStarArg Mf ‖yPlus - y‖[g; y]
          (mf_mul_lt_one_of_lt_inv
            (localNorm_lt_inv_of_memOpenDikinEllipsoid
              (Mf := Mf) (g := g) hyPlus_mem))) =
          ω_* τω := by
      have hstep :
          ‖yPlus - y‖[g; y] = δ / (1 + (Mf : ℝ) * δ) := by
        simpa [δ, α, v, yPlus] using
          dampedDualGradientProbe_localNorm_eq (dom := dom) (Mf := Mf) (g := g) hy
      have hτvalue : (τω : ℝ) = (Mf : ℝ) * (δ / (1 + (Mf : ℝ) * δ)) := by
        rw [show (τω : ℝ) = ω' tω by simp [τω]]
        rw [selfConcordantOmegaDeriv_apply]
        simp [tω]
        field_simp [hMf_ne]
      -- Rewrite only the evaluated `ω_*` remainder, not the subtype owner.
      simp [selfConcordantOmegaStar_apply, hstep, hτvalue]
    have hstep :
        ‖yPlus - y‖[g; y] = δ / (1 + (Mf : ℝ) * δ) := by
      simpa [δ, α, v, yPlus] using
        dampedDualGradientProbe_localNorm_eq (dom := dom) (Mf := Mf) (g := g) hy
    have hτvalue : (τω : ℝ) = (Mf : ℝ) * (δ / (1 + (Mf : ℝ) * δ)) := by
      rw [show (τω : ℝ) = ω' tω by simp [τω]]
      rw [selfConcordantOmegaDeriv_apply]
      simp [tω]
      field_simp [hMf_ne]
    have hupper :
        g yPlus ≤
          g y + inner ℝ (∇ g y) (yPlus - y) +
            (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω_* τω := by
      rw [← hωStar_transport]
      exact hupper_raw
    have hpair :
        inner ℝ (∇ g y) (yPlus - y) =
          -(δ ^ (2 : ℕ) / (1 + (Mf : ℝ) * δ)) := by
      simpa [δ, α, v, yPlus] using
        dampedDualGradientProbe_gradient_pairing_eq (dom := dom) (Mf := Mf) (g := g) hy
    have hpair_scalar :
        δ ^ (2 : ℕ) / (1 + (Mf : ℝ) * δ) =
          (1 / (Mf : ℝ) ^ (2 : ℕ)) * ((tω : ℝ) * ω' tω) := by
      rw [selfConcordantOmegaDeriv_apply]
      simp [tω]
      field_simp [hMf_ne]
    have hfenchel :
        ω tω = (tω : ℝ) * ω' tω - ω_* τω := by
      -- Evaluate the unit-scale Fenchel identity directly on the scalar arguments.
      simpa [tω, τω, selfConcordantOmega_apply, selfConcordantOmegaStar_apply] using
        (selfConcordantOmega_eq_mul_selfConcordantOmegaDeriv_sub_selfConcordantOmegaStar
          (t := (tω : ℝ)) tω.2)
    have hscalar :
        -(δ ^ (2 : ℕ) / (1 + (Mf : ℝ) * δ)) +
            (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω_* τω =
          -((1 / (Mf : ℝ) ^ (2 : ℕ)) * ω tω) := by
      rw [hpair_scalar, hfenchel]
      ring
    have hmin_value : g xStar ≤ g yPlus := (isMinOn_iff.mp hmin) yPlus hyPlus_dom
    have hmain : g y ≥ g xStar + (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω tω := by
      calc
        g y ≥ g yPlus + (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω tω := by
          linarith [hupper, hpair, hscalar]
        _ ≥ g xStar + (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω tω := by
          linarith
    simpa [hMf0, δ, tω] using hmain

/-- Helper for Theorem 5.1.12: once a self-concordant objective is minimized at `xStar`, its
suboptimality at `y` admits the upper `ω_*` bound in terms of the dual local norm of `∇ g(y)`
under the small-dual-gradient hypothesis. -/
private theorem suboptimalityUpperBound_ofDualGradientNorm_atMinimizer
    {g : E → ℝ} [IsSelfConcordantOnWith dom Mf g] [HasPositiveDefiniteHessianOn dom g]
    {xStar y : E} (hxStar : xStar ∈ dom) (hmin : IsMinOn g dom xStar) (hy : y ∈ dom) :
    let δ := HessianDualLocalNorm.ofPosDefMem g hy ((toDual ℝ E) (∇ g y))
    if Mf = 0 then
      g y ≤
        g xStar +
          δ ^ (2 : ℕ) / 2
    else
      ∀ hδ : δ < 1 / (Mf : ℝ),
        let τω := selfConcordantOmegaStarArg Mf δ (mf_mul_lt_one_of_lt_inv hδ)
        g y ≤
          g xStar +
            (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω_* τω := by
  -- Route correction: do not route this branch through a Dikin-membership claim for the
  -- minimizer. The remaining proof must stay in dual-gradient-norm form, using the minimizer
  -- stationarity and a direct `ω_*` argument rather than the false intermediate
  -- `y ∈ W⁰[g; xStar](1 / (Mf : ℝ))`.
  dsimp
  by_cases hMf0 : Mf = 0
  · -- The degenerate branch is the same exact quadratic model used in the lower theorem.
    have hzeroEq :
        g y =
          g xStar +
            (HessianDualLocalNorm.ofPosDefMem g hy ((toDual ℝ E) (∇ g y))) ^ (2 : ℕ) / 2 := by
      simpa using
          zeroParameterSuboptimality_eq_halfDualGradientNormSq_atMinimizer
          (dom := dom) (Mf := Mf) (g := g) hMf0 hxStar hmin hy
    simpa [hMf0] using hzeroEq.le
  · have hbranch :
        ∀ hδ : HessianDualLocalNorm.ofPosDefMem g hy ((toDual ℝ E) (∇ g y)) < 1 / (Mf : ℝ),
          let τω := selfConcordantOmegaStarArg Mf
            (HessianDualLocalNorm.ofPosDefMem g hy ((toDual ℝ E) (∇ g y)))
            (mf_mul_lt_one_of_lt_inv hδ)
          g y ≤ g xStar + (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω_* τω := by
      intro hδ
      let h : E := xStar - y
      let r : ℝ := ‖h‖[g; y]
      let δ := HessianDualLocalNorm.ofPosDefMem g hy ((toDual ℝ E) (∇ g y))
      have hδ' : δ < 1 / (Mf : ℝ) := by
        simpa [δ] using hδ
      let τω : Set.Iio (1 : ℝ) :=
        selfConcordantOmegaStarArg Mf δ (mf_mul_lt_one_of_lt_inv hδ')
      have hTaylor :
          g xStar ≥
            g y + inner ℝ (∇ g y) h +
              (1 / (Mf : ℝ) ^ (2 : ℕ)) *
                ω (selfConcordantOmegaArg Mf r
                  (neg_one_lt_mf_mul_of_nonneg (hessianLocalNorm_nonneg g y h))) := by
        simpa [h, r] using
          taylorLowerBound_fromBaseByLocalDistance_nonzero
            (dom := dom) (Mf := Mf) (g := g) hMf0 hy hxStar
      have hpair :
          inner ℝ (∇ g y) (y - xStar) ≤ δ * r := by
        simpa [h, r, δ] using
          gradientPairing_le_dualLocalNorm_mul_baseDistance
            (dom := dom) (g := g) (y := y) (z := xStar) hy
      have hfenchel :
          δ * r -
              (1 / (Mf : ℝ) ^ (2 : ℕ)) *
                ω (selfConcordantOmegaArg Mf r
                  (neg_one_lt_mf_mul_of_nonneg (hessianLocalNorm_nonneg g y h))) ≤
            (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω_* τω := by
        simpa [δ, r, τω] using
          fenchelEliminate_baseDistance
            (Mf := Mf) (r := r) (δ := δ) hMf0
            (by simpa [r] using hessianLocalNorm_nonneg g y h) hδ'
      have hmain : g y ≤ g xStar + (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω_* τω := by
        have hTaylor' :
            g y - g xStar ≤
              inner ℝ (∇ g y) (y - xStar) -
                (1 / (Mf : ℝ) ^ (2 : ℕ)) *
                  ω (selfConcordantOmegaArg Mf r
                    (neg_one_lt_mf_mul_of_nonneg (hessianLocalNorm_nonneg g y h))) := by
          have hTaylor'' :
              g y - g xStar ≤
                -inner ℝ (∇ g y) h -
                  (1 / (Mf : ℝ) ^ (2 : ℕ)) *
                    ω (selfConcordantOmegaArg Mf r
                      (neg_one_lt_mf_mul_of_nonneg (hessianLocalNorm_nonneg g y h))) := by
            linarith
          have hsign : inner ℝ (∇ g y) (y - xStar) = -inner ℝ (∇ g y) h := by
            rw [show y - xStar = -h by
              dsimp [h]
              abel]
            simp
          calc
            g y - g xStar ≤
                -inner ℝ (∇ g y) h -
                  (1 / (Mf : ℝ) ^ (2 : ℕ)) *
                    ω (selfConcordantOmegaArg Mf r
                      (neg_one_lt_mf_mul_of_nonneg (hessianLocalNorm_nonneg g y h))) := hTaylor''
            _ = inner ℝ (∇ g y) (y - xStar) -
                  (1 / (Mf : ℝ) ^ (2 : ℕ)) *
                    ω (selfConcordantOmegaArg Mf r
                      (neg_one_lt_mf_mul_of_nonneg (hessianLocalNorm_nonneg g y h))) := by
                  rw [hsign]
        linarith
      simpa [δ, τω, selfConcordantOmegaStar_apply] using hmain
    simpa [hMf0, selfConcordantOmegaStar_apply] using hbranch

-- Proof sketch: compare `f y` to the first-order Taylor model at `x`, write the remainder in
-- terms of the gradient-difference covector at `y`, and express the resulting lower and upper
-- self-concordant remainders through the canonical Chapter 5 subtype owners
-- `selfConcordantOmegaArg` and `selfConcordantOmegaStarArg`. The only local helper retained here
-- is the nonnegativity witness needed to build the `ω` argument from the domain-level dual local
-- norm bridge.
/-- Helper for Theorem 5.1.12: the lower source-facing value bound after transporting through the
affine tilt at `x`. -/
private theorem valueLowerBound_of_dualLocalNorm_gradientDifference
    {x y : E} (hx : x ∈ dom) (hy : y ∈ dom) :
    let δ :=
      HessianDualLocalNorm.ofPosDefMem f hy
        ((toDual ℝ E) (∇ f y - ∇ f x))
    let taylor := firstOrderTaylorModelAt f x y
    let tω := selfConcordantOmegaArg Mf δ
      (neg_one_lt_mf_mul_of_nonneg (gradientDifferenceDualLocalNorm_nonneg x y hy))
    f y ≥
      taylor +
        (if Mf = 0 then
          δ ^ (2 : ℕ) / 2
        else
          (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω tω) := by
  dsimp
  let g : E → ℝ := tiltedObjective f x
  have hself_g : IsSelfConcordantOnWith dom Mf g := by
    simpa [g] using tiltedObjective_selfConcordant (dom := dom) (Mf := Mf) (f := f) x
  have hpos_g : HasPositiveDefiniteHessianOn dom g := by
    simpa [g] using
      tiltedObjective_hasPositiveDefiniteHessianOn (dom := dom) (f := f) (M := Mf) x
  let _ : IsSelfConcordantOnWith dom Mf g := hself_g
  let _ : HasPositiveDefiniteHessianOn dom g := hpos_g
  have hgrad_gx : ∇ g x = 0 := by
    simpa [g] using gradient_tiltedObjective_eq_zero_at_base (dom := dom) (M := Mf) (f := f) x hx
  have hmin_g : IsMinOn g dom x := by
    exact isMinOn_of_gradient_eq_zero (dom := dom) (Mf := Mf) (g := g) hx hgrad_gx
  have hδeq :
      HessianDualLocalNorm.ofPosDefMem g hy ((toDual ℝ E) (∇ g y)) =
        HessianDualLocalNorm.ofPosDefMem f hy
          ((toDual ℝ E) (∇ f y - ∇ f x)) := by
    simpa [g] using
      tiltedGradientDualLocalNorm_eq_gradientDifference
        (dom := dom) (M := Mf) (f := f) x y hy
  have hgap :
      g y - g x = f y - firstOrderTaylorModelAt f x y := by
    simpa [g] using tiltedGap_eq_taylorGap (f := f) x y
  have hlower_g :
      g y ≥
        g x +
          (if hMf : Mf = 0 then
            (HessianDualLocalNorm.ofPosDefMem g hy ((toDual ℝ E) (∇ g y))) ^ (2 : ℕ) / 2
          else
            (1 / (Mf : ℝ) ^ (2 : ℕ)) *
              ω (selfConcordantOmegaArg Mf
                (HessianDualLocalNorm.ofPosDefMem g hy ((toDual ℝ E) (∇ g y)))
                (neg_one_lt_mf_mul_of_nonneg
                  (dualGradientDualLocalNorm_nonneg (dom := dom) (g := g) y hy)))) := by
    simpa using
      suboptimalityLowerBound_ofDualGradientNorm_atMinimizer
        (dom := dom) (Mf := Mf) (g := g) hx hmin_g hy
  let δg := HessianDualLocalNorm.ofPosDefMem g hy ((toDual ℝ E) (∇ g y))
  let δf :=
    HessianDualLocalNorm.ofPosDefMem f hy
      ((toDual ℝ E) (∇ f y - ∇ f x))
  have hlower_gap :
      g y - g x ≥
        (if hMf : Mf = 0 then
          δg ^ (2 : ℕ) / 2
        else
          (1 / (Mf : ℝ) ^ (2 : ℕ)) *
            ω (selfConcordantOmegaArg Mf
              δg
              (neg_one_lt_mf_mul_of_nonneg
                (dualGradientDualLocalNorm_nonneg (dom := dom) (g := g) y hy)))) := by
    linarith
  have hδeq' : δg = δf := by
    simpa [δg, δf] using hδeq
  have hlower_rhs :
      (if hMf : Mf = 0 then
        δg ^ (2 : ℕ) / 2
      else
        (1 / (Mf : ℝ) ^ (2 : ℕ)) *
          ω (selfConcordantOmegaArg Mf
            δg
            (neg_one_lt_mf_mul_of_nonneg
              (dualGradientDualLocalNorm_nonneg (dom := dom) (g := g) y hy)))) =
      (if hMf : Mf = 0 then
        δf ^ (2 : ℕ) / 2
      else
        (1 / (Mf : ℝ) ^ (2 : ℕ)) *
          ω (selfConcordantOmegaArg Mf
            δf
            (neg_one_lt_mf_mul_of_nonneg
              (gradientDifferenceDualLocalNorm_nonneg x y hy)))) := by
    by_cases hMf0 : Mf = 0
    · simp [hMf0, hδeq']
    · simp [hMf0, selfConcordantOmega_apply, hδeq']
  have hlower_gap' :
      f y - firstOrderTaylorModelAt f x y ≥
        (if hMf : Mf = 0 then
          δf ^ (2 : ℕ) / 2
        else
          (1 / (Mf : ℝ) ^ (2 : ℕ)) *
            ω (selfConcordantOmegaArg Mf
              δf
              (neg_one_lt_mf_mul_of_nonneg
                (gradientDifferenceDualLocalNorm_nonneg x y hy)))) := by
    have hlower_gapf := hlower_gap
    rw [hlower_rhs] at hlower_gapf
    rw [← hgap]
    exact hlower_gapf
  have hlower_target :
      f y ≥
        firstOrderTaylorModelAt f x y +
          (if hMf : Mf = 0 then
            δf ^ (2 : ℕ) / 2
          else
            (1 / (Mf : ℝ) ^ (2 : ℕ)) *
              ω (selfConcordantOmegaArg Mf
                δf
                (neg_one_lt_mf_mul_of_nonneg
                  (gradientDifferenceDualLocalNorm_nonneg x y hy)))) := by
    linarith
  simpa [δf] using hlower_target

/-- Helper for Theorem 5.1.12: the upper source-facing value bound after transporting through the
affine tilt at `x`. -/
private theorem valueUpperBound_of_dualLocalNorm_gradientDifference
    {x y : E} (hx : x ∈ dom) (hy : y ∈ dom) :
    let δ :=
      HessianDualLocalNorm.ofPosDefMem f hy
        ((toDual ℝ E) (∇ f y - ∇ f x))
    let taylor := firstOrderTaylorModelAt f x y
    if Mf = 0 then
      f y ≤
        taylor +
          δ ^ (2 : ℕ) / 2
    else
      ∀ hδ : δ < 1 / (Mf : ℝ),
        let τω := selfConcordantOmegaStarArg Mf δ (mf_mul_lt_one_of_lt_inv hδ)
        f y ≤
          taylor +
            (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω_* τω := by
  dsimp
  let g : E → ℝ := tiltedObjective f x
  have hself_g : IsSelfConcordantOnWith dom Mf g := by
    simpa [g] using tiltedObjective_selfConcordant (dom := dom) (Mf := Mf) (f := f) x
  have hpos_g : HasPositiveDefiniteHessianOn dom g := by
    simpa [g] using
      tiltedObjective_hasPositiveDefiniteHessianOn (dom := dom) (f := f) (M := Mf) x
  let _ : IsSelfConcordantOnWith dom Mf g := hself_g
  let _ : HasPositiveDefiniteHessianOn dom g := hpos_g
  have hgrad_gx : ∇ g x = 0 := by
    simpa [g] using gradient_tiltedObjective_eq_zero_at_base (dom := dom) (M := Mf) (f := f) x hx
  have hmin_g : IsMinOn g dom x := by
    exact isMinOn_of_gradient_eq_zero (dom := dom) (Mf := Mf) (g := g) hx hgrad_gx
  have hδeq :
      HessianDualLocalNorm.ofPosDefMem g hy ((toDual ℝ E) (∇ g y)) =
        HessianDualLocalNorm.ofPosDefMem f hy
          ((toDual ℝ E) (∇ f y - ∇ f x)) := by
    simpa [g] using
      tiltedGradientDualLocalNorm_eq_gradientDifference
        (dom := dom) (M := Mf) (f := f) x y hy
  have hgap :
      g y - g x = f y - firstOrderTaylorModelAt f x y := by
    simpa [g] using tiltedGap_eq_taylorGap (f := f) x y
  by_cases hMf0 : Mf = 0
  · have hupper_g0 :
        g y ≤
          g x +
            (HessianDualLocalNorm.ofPosDefMem g hy ((toDual ℝ E) (∇ g y))) ^ (2 : ℕ) / 2 := by
      simpa [hMf0] using
        suboptimalityUpperBound_ofDualGradientNorm_atMinimizer
          (dom := dom) (Mf := Mf) (g := g) hx hmin_g hy
    let δg := HessianDualLocalNorm.ofPosDefMem g hy ((toDual ℝ E) (∇ g y))
    let δf :=
      HessianDualLocalNorm.ofPosDefMem f hy
        ((toDual ℝ E) (∇ f y - ∇ f x))
    have hupper_gap0 :
        g y - g x ≤ δg ^ (2 : ℕ) / 2 := by
      linarith
    have hupper_gap0' :
        f y - firstOrderTaylorModelAt f x y ≤ δf ^ (2 : ℕ) / 2 := by
      have hδeq' : δg = δf := by
        simpa [δg, δf] using hδeq
      have hupper_gap0f : g y - g x ≤ δf ^ (2 : ℕ) / 2 := by
        simpa [hδeq'] using hupper_gap0
      rw [← hgap]
      exact hupper_gap0f
    have hupper_target0 :
        f y ≤
          firstOrderTaylorModelAt f x y +
            δf ^ (2 : ℕ) / 2 := by
      linarith
    simpa [hMf0, δf] using hupper_target0
  · have hbranch :
      ∀ hδ :
          HessianDualLocalNorm.ofPosDefMem f hy
            ((toDual ℝ E) (∇ f y - ∇ f x)) < 1 / (Mf : ℝ),
        let τω := selfConcordantOmegaStarArg Mf
          (HessianDualLocalNorm.ofPosDefMem f hy
            ((toDual ℝ E) (∇ f y - ∇ f x)))
          (mf_mul_lt_one_of_lt_inv hδ)
        f y ≤
          firstOrderTaylorModelAt f x y +
            (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω_* τω := by
      have hupper_g :
          ∀ hδg :
              HessianDualLocalNorm.ofPosDefMem g hy ((toDual ℝ E) (∇ g y)) < 1 / (Mf : ℝ),
            let τω := selfConcordantOmegaStarArg Mf
              (HessianDualLocalNorm.ofPosDefMem g hy ((toDual ℝ E) (∇ g y)))
              (mf_mul_lt_one_of_lt_inv hδg)
            g y ≤ g x + (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω_* τω := by
        simpa [hMf0] using
          suboptimalityUpperBound_ofDualGradientNorm_atMinimizer
            (dom := dom) (Mf := Mf) (g := g) hx hmin_g hy
      intro hδ
      let δg := HessianDualLocalNorm.ofPosDefMem g hy ((toDual ℝ E) (∇ g y))
      let δf :=
        HessianDualLocalNorm.ofPosDefMem f hy
          ((toDual ℝ E) (∇ f y - ∇ f x))
      have hδf : δf < 1 / (Mf : ℝ) := by
        simpa [δf] using hδ
      have hδg :
          δg < 1 / (Mf : ℝ) := by
        rw [show δg = δf by simpa [δg, δf] using hδeq]
        exact hδf
      have hωStar_transport :
          ω_* (selfConcordantOmegaStarArg Mf
              δg
              (mf_mul_lt_one_of_lt_inv hδg)) =
            ω_* (selfConcordantOmegaStarArg Mf
              δf
              (mf_mul_lt_one_of_lt_inv hδf)) := by
        have hδeq' : δg = δf := by
          simpa [δg, δf] using hδeq
        simp [selfConcordantOmegaStar_apply, hδeq']
      have hupper_g' :
          g y - g x ≤
            (1 / (Mf : ℝ) ^ (2 : ℕ)) *
              ω_* (selfConcordantOmegaStarArg Mf
                δg
                (mf_mul_lt_one_of_lt_inv hδg)) := by
        have hupper_raw := hupper_g hδg
        linarith
      have hupper_gap' :
          f y - firstOrderTaylorModelAt f x y ≤
            (1 / (Mf : ℝ) ^ (2 : ℕ)) *
              ω_* (selfConcordantOmegaStarArg Mf
                δf
                (mf_mul_lt_one_of_lt_inv hδf)) := by
        have hupper_g'' := hupper_g'
        rw [hωStar_transport] at hupper_g''
        rw [← hgap]
        exact hupper_g''
      have hupper_target :
          f y ≤
            firstOrderTaylorModelAt f x y +
              (1 / (Mf : ℝ) ^ (2 : ℕ)) *
                ω_* (selfConcordantOmegaStarArg Mf δf (mf_mul_lt_one_of_lt_inv hδf)) := by
        linarith
      simpa [δf, selfConcordantOmegaStar_apply] using hupper_target
    simpa [hMf0, selfConcordantOmegaStar_apply] using hbranch

/-- Theorem 5.1.12: if `f` is self-concordant on `dom` with constant `M_f`, then the
value at `y` is bounded below by the affine Taylor model at `x` plus the remainder term
`M_f⁻² ω(M_f ‖∇ f(y) - ∇ f(x)‖*_y)`, interpreted as
`(1 / 2) ‖∇ f(y) - ∇ f(x)‖*²_y` when `M_f = 0`. In the same zero-parameter limit, the
upper branch also reduces to the quadratic remainder `(1 / 2) ‖∇ f(y) - ∇ f(x)‖*²_y`;
otherwise, if the dual local norm of the gradient difference at `y` is smaller than `1 / M_f`,
then `f y` is bounded above by the affine model plus
`M_f⁻² ω_*(M_f ‖∇ f(y) - ∇ f(x)‖*_y)`. -/
theorem selfConcordant_value_bounds_of_dualLocalNorm_gradient_sub
    {x y : E} (hx : x ∈ dom) (hy : y ∈ dom) :
    let δ :=
      HessianDualLocalNorm.ofPosDefMem f hy
        ((toDual ℝ E) (∇ f y - ∇ f x))
    let taylor := firstOrderTaylorModelAt f x y
    let tω := selfConcordantOmegaArg Mf δ
      (neg_one_lt_mf_mul_of_nonneg (gradientDifferenceDualLocalNorm_nonneg x y hy))
    f y ≥
        taylor +
          (if Mf = 0 then
            δ ^ (2 : ℕ) / 2
          else
            (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω tω) ∧
      (if Mf = 0 then
        f y ≤
          taylor +
            δ ^ (2 : ℕ) / 2
      else
        ∀ hδ : δ < 1 / (Mf : ℝ),
          let τω := selfConcordantOmegaStarArg Mf δ (mf_mul_lt_one_of_lt_inv hδ)
          f y ≤
            taylor +
              (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω_* τω) := by
  constructor
  · exact
      valueLowerBound_of_dualLocalNorm_gradientDifference
        (dom := dom) (Mf := Mf) (f := f) hx hy
  · exact
      valueUpperBound_of_dualLocalNorm_gradientDifference
        (dom := dom) (Mf := Mf) (f := f) hx hy
