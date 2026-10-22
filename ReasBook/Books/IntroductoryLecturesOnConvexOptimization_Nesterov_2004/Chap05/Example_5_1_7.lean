/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_16
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

/-- Helper for Example 5.1.7: the directional slice of `f` at `x` along `u` is the scalar map
`t ↦ f (x + t * u)`. -/
def directionalSlice (f : ℝ → ℝ) (x u : ℝ) : ℝ → ℝ :=
  fun t ↦ f (x + t * u)

/-- Helper for Example 5.1.7: evaluating the directional slice recovers the scalar affine-line
formula. -/
@[simp] theorem directionalSlice_apply (f : ℝ → ℝ) (x u t : ℝ) :
    directionalSlice f x u t = f (x + t * u) :=
  rfl

/-- Helper for Example 5.1.7: the third directional derivative is the third iterated derivative of
the directional slice at `0`. -/
def thirdDirectionalDerivative (f : ℝ → ℝ) (x u : ℝ) : ℝ :=
  iteratedDeriv 3 (directionalSlice f x u) 0

/-- Helper for Example 5.1.7: the Hessian local norm is the square root of the Hessian quadratic
form. -/
def hessianLocalNorm (f : ℝ → ℝ) (x u : ℝ) : ℝ :=
  Real.sqrt (inner ℝ u (hessian f x u))

namespace HessianLocalNorm

/-- Helper for Example 5.1.7: notation for the Hessian local norm. -/
scoped notation:max "‖" u "‖[" f "; " x "]" => hessianLocalNorm f x u

end HessianLocalNorm

/-- Helper for Example 5.1.7: expanding `‖u‖[f; x]` gives the square root of the Hessian
quadratic form. -/
theorem hessianLocalNorm_def (f : ℝ → ℝ) (x u : ℝ) :
    hessianLocalNorm f x u = Real.sqrt (inner ℝ u (hessian f x u)) :=
  rfl

/-- Helper for Example 5.1.7: self-concordance on `dom` with constant `Mf` consists of openness,
`C³` regularity, convexity, and the standard cubic directional-derivative bound. -/
class IsSelfConcordantOnWith (dom : Set ℝ) (Mf : NNReal) (f : ℝ → ℝ) : Prop where
  /-- Helper for Example 5.1.7: the domain is open. -/
  isOpen_domain : IsOpen dom
  /-- Helper for Example 5.1.7: the objective is `C³` on the domain. -/
  contDiffOn : ContDiffOn ℝ 3 f dom
  /-- Helper for Example 5.1.7: the objective is convex on the domain. -/
  convexOn : ConvexOn ℝ dom f
  /-- Helper for Example 5.1.7: the cubic derivative is controlled by the cube of the local
  Hessian norm. -/
  third_deriv_bound {x : ℝ} (hx : x ∈ dom) (u : ℝ) :
      |thirdDirectionalDerivative f x u| ≤
        2 * (Mf : ℝ) * hessianLocalNorm f x u ^ (3 : ℕ)

/-- Example 5.1.7: the standard self-concordant condition is the case `Mf = 1`. -/
abbrev IsStandardSelfConcordantOn (dom : Set ℝ) (f : ℝ → ℝ) : Prop :=
  IsSelfConcordantOnWith dom 1 f

/-- Helper for Example 5.1.7: the Hessian is positive definite on `dom` when it is positive and
strictly positive on every nonzero direction at each feasible point. -/
class HasPositiveDefiniteHessianOn (dom : Set ℝ) (f : ℝ → ℝ) : Prop where
  /-- Helper for Example 5.1.7: the Hessian operator is positive at each feasible point. -/
  isPositive {x : ℝ} (hx : x ∈ dom) :
    (hessian f x).IsPositive
  /-- Helper for Example 5.1.7: the Hessian quadratic form is strictly positive on every nonzero
  direction at each feasible point. -/
  posdef {x : ℝ} (hx : x ∈ dom) {u : ℝ} (hu : u ≠ 0) :
    0 < inner ℝ u (hessian f x u)

/-- Helper for Example 5.1.7: the Newton decrement is the inverse-Hessian quadratic form of the
gradient, written through the canonical square root. -/
abbrev newtonDecrement (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.sqrt (inner ℝ (∇ f x) ((hessian f x).inverse (∇ f x)))

namespace NewtonDecrement

/-- Helper for Example 5.1.7: on a domain with positive-definite Hessian, the source-facing
Newton decrement notation specializes `newtonDecrement`. -/
abbrev ofPosDefMem (f : ℝ → ℝ) (x : ℝ) {dom : Set ℝ}
    [HasPositiveDefiniteHessianOn dom f] (_hx : x ∈ dom) : ℝ :=
  newtonDecrement f x

/-- Helper for Example 5.1.7: notation for the Newton decrement at a feasible point. -/
scoped notation:max "λ[" f "; " x " | " hx "]" =>
  ofPosDefMem f x hx

/-- Helper for Example 5.1.7: expanding the domain-based Newton decrement notation gives the
inverse-Hessian gradient pairing formula. -/
theorem ofPosDefMem_def (f : ℝ → ℝ) (x : ℝ) {dom : Set ℝ}
    [HasPositiveDefiniteHessianOn dom f] (hx : x ∈ dom) :
    λ[f; x | hx] = Real.sqrt (inner ℝ (∇ f x) ((hessian f x).inverse (∇ f x))) :=
  rfl

end NewtonDecrement

open scoped HessianLocalNorm NewtonDecrement
open NewtonDecrement

/- Example 5.1.7 lies in the scalar self-concordance / Newton-decrement domain.

Sampled owner-style declarations:
* `IsStandardSelfConcordantOn` from `Definition_5_1_1`, the Chapter 5 owner for standard
  self-concordance;
* `HasPositiveDefiniteHessianOn` from `Definition_5_0_23`, the chapter owner for domain-level
  positive-definite Hessians;
* `quadraticAffineObjective_isSelfConcordantOnWith_zero` from `Example_5_1_2`, the canonical
  affine-quadratic perturbation input, specialized here to zero quadratic part;
* `negLog_isStandardSelfConcordantOn` from `Example_5_1_3`, the canonical `-log` owner on
  `(0, ∞)`;
* `NewtonDecrement.ofPosDefMem` together with the notation `λ[f; x | hx]` from
  `Definition_5_0_24`, the canonical positive-definite-Hessian domain bridge and its
  source-facing theorem surface for Newton decrements.

Source/core/bridge triage:
* source-facing: the scalar barrier `x ↦ ε x - log x`;
* core/canonical: `IsStandardSelfConcordantOn (Set.Ioi (0 : ℝ))` and
  `newtonDecrement`;
* bridge/view: the explicit derivative formulas and the closed-form Newton-decrement evaluation.

Primitive data:
* the scalar perturbation parameter `ε`.

Derived API:
* the evaluation formula for `affinePerturbedLogBarrier`;
* the first- and second-derivative formulas on `(0, ∞)`;
* the standard self-concordance statement on `(0, ∞)`;
* positive definiteness of the scalar Hessian on `(0, ∞)`;
* Hessian nondegeneracy on `(0, ∞)`, derived from that owner;
* the explicit Newton-decrement formula `λ[affinePerturbedLogBarrier ε; x | hx] = |1 - ε x|`.

The source-facing barrier itself is not duplicated upstream, so it remains the owner in this file.
The Newton decrement is already owned by `newtonDecrement`, and this file uses the Chapter 5
source-facing notation `λ[f; x | hx]` on the theorem surface instead of restating the
self-concordance constant in a parallel local decrement view.
-/

/-- The affine perturbation `x ↦ ε x - log x` of the logarithmic barrier on `(0, ∞)`. -/
def affinePerturbedLogBarrier (ε : ℝ) : ℝ → ℝ :=
  fun x ↦ ε * x - Real.log x

/-- Evaluating `affinePerturbedLogBarrier ε` recovers the textbook formula `ε x - log x`. -/
-- Proof sketch: unfold `affinePerturbedLogBarrier`.
@[simp]
theorem affinePerturbedLogBarrier_apply (ε x : ℝ) :
    affinePerturbedLogBarrier ε x = ε * x - Real.log x :=
  rfl

/-- Helper for Example 5.1.7: on `(0, ∞)`, the affine-log barrier has derivative `ε - 1 / x`. -/
private theorem hasDerivAt_affinePerturbedLogBarrier_onIoi
    {ε x : ℝ} (hx : x ∈ Set.Ioi (0 : ℝ)) :
    HasDerivAt (affinePerturbedLogBarrier ε) (ε - 1 / x) x := by
  have hx0 : 0 < x := hx
  -- Differentiate the affine part and the logarithmic part separately.
  have haffine : HasDerivAt (fun y : ℝ ↦ ε * y) ε x := by
    simpa using (hasDerivAt_id x).const_mul ε
  have hlog : HasDerivAt (fun y : ℝ ↦ -Real.log y) (-(1 / x)) x := by
    simpa using (Real.hasDerivAt_log hx0.ne').neg
  -- Reassemble the barrier as the sum `ε * x + (-log x)`.
  simpa [affinePerturbedLogBarrier, sub_eq_add_neg] using haffine.add hlog

-- Proof sketch: differentiate the affine term `x ↦ ε x` and the logarithmic term separately on
-- `(0, ∞)`, then combine the resulting scalar formulas.
/-- The first derivative of `x ↦ ε x - log x` on `(0, ∞)` is `ε - 1 / x`. -/
theorem deriv_affinePerturbedLogBarrier_on_Ioi (ε x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    deriv (affinePerturbedLogBarrier ε) x = ε - 1 / x := by
  -- Read the derivative from the pointwise `HasDerivAt` witness.
  simpa using (hasDerivAt_affinePerturbedLogBarrier_onIoi (ε := ε) hx).deriv

-- Proof sketch: differentiate `deriv_affinePerturbedLogBarrier_on_Ioi` once more on `(0, ∞)` and
-- simplify the rational expression.
/-- The second derivative of `x ↦ ε x - log x` on `(0, ∞)` is `1 / x^2`. -/
theorem secondDeriv_affinePerturbedLogBarrier_on_Ioi (ε x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    iteratedDeriv 2 (affinePerturbedLogBarrier ε) x = 1 / x ^ 2 := by
  have hx0 : 0 < x := hx
  -- Near a positive point, the first derivative is the explicit rational function `ε - 1 / y`.
  calc
    iteratedDeriv 2 (affinePerturbedLogBarrier ε) x
        = deriv (deriv (affinePerturbedLogBarrier ε)) x := by
            simp [iteratedDeriv_succ]
    _ = deriv (fun y : ℝ ↦ ε - 1 / y) x := by
          apply Filter.EventuallyEq.deriv_eq
          filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
          simpa using deriv_affinePerturbedLogBarrier_on_Ioi ε y hy
    _ = 1 / x ^ 2 := by
          -- Differentiate the reciprocal explicitly and simplify the signs.
          rw [show (fun y : ℝ ↦ ε - 1 / y) = fun y : ℝ ↦ ε - y⁻¹ by
            funext y
            simp [one_div]]
          rw [deriv_const_sub]
          rw [show deriv (fun y : ℝ ↦ y⁻¹) x = -(x ^ (2 : ℕ))⁻¹ by
            simp [deriv_inv]]
          field_simp [hx0.ne']

/-- Helper for Example 5.1.7: the derivative of the pure logarithmic directional slice is the
expected affine-inverse expression. -/
private theorem negLog_directionalSlice_deriv (x u t : ℝ) :
    deriv (directionalSlice (fun y : ℝ ↦ -Real.log y) x u) t = -u * (u * t + x)⁻¹ := by
  -- Differentiate the shifted-and-scaled logarithm, then carry the outer minus sign.
  change deriv (-fun s : ℝ ↦ Real.log (x + s * u)) t = -u * (u * t + x)⁻¹
  calc
    deriv (-fun s : ℝ ↦ Real.log (x + s * u)) t
        = -deriv (fun s : ℝ ↦ Real.log (x + s * u)) t := by
            simp
    _ = -deriv (fun s : ℝ ↦ Real.log (u * s + x)) t := by
          congr 1
          exact congrArg (fun h : ℝ → ℝ ↦ deriv h t) (by
            funext s
            ring)
    _ = -(u * deriv (fun s : ℝ ↦ Real.log (s + x)) (u * t)) := by
          congr 1
          simpa [Function.comp] using
            deriv_comp_mul_left u (fun s : ℝ ↦ Real.log (s + x)) t
    _ = -(u * (u * t + x)⁻¹) := by rw [deriv_comp_add_const, Real.deriv_log]
    _ = -u * (u * t + x)⁻¹ := by ring

/-- Helper for Example 5.1.7: the Hessian quadratic form of the affine-log barrier at a positive
point is `u^2 / x^2`. -/
private theorem affinePerturbedLogBarrier_hessianQuadraticForm_eq
    (ε x u : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    inner ℝ u (hessian (affinePerturbedLogBarrier ε) x u) = u ^ (2 : ℕ) / x ^ (2 : ℕ) := by
  have hgradEq : ∇ (affinePerturbedLogBarrier ε) = deriv (affinePerturbedLogBarrier ε) := by
    funext y
    exact gradient_eq_deriv'
  have hhess :
      hessian (affinePerturbedLogBarrier ε) x u =
        iteratedDeriv 2 (affinePerturbedLogBarrier ε) x * u := by
    rw [hessian, hgradEq, fderiv_eq_deriv_mul]
    simp [iteratedDeriv_succ, mul_comm]
  calc
    inner ℝ u (hessian (affinePerturbedLogBarrier ε) x u)
        = inner ℝ u (iteratedDeriv 2 (affinePerturbedLogBarrier ε) x * u) := by
            rw [hhess]
    _ = inner ℝ u ((1 / x ^ 2 : ℝ) * u) := by
          rw [secondDeriv_affinePerturbedLogBarrier_on_Ioi ε x hx]
    _ = u ^ (2 : ℕ) / x ^ (2 : ℕ) := by
          have hinner : inner ℝ u ((1 / x ^ 2 : ℝ) * u) = ((1 / x ^ 2 : ℝ) * u) * u :=
            RCLike.inner_apply u ((1 / x ^ 2 : ℝ) * u)
          rw [hinner]
          ring_nf

/-- Helper for Example 5.1.7: the third directional derivative of `x ↦ -log x` at a positive
point is `-2 * u^3 / x^3`. -/
private theorem negLog_thirdDirectionalDerivative_eq
    (x u : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    thirdDirectionalDerivative (fun y : ℝ ↦ -Real.log y) x u = -2 * u ^ (3 : ℕ) / x ^ (3 : ℕ) := by
  have hx0 : 0 < x := hx
  have hinv :
      iteratedDeriv 2 (fun t : ℝ ↦ (u * t + x)⁻¹) 0 = 2 * u ^ (2 : ℕ) * x ^ (-3 : ℤ) := by
    rw [iteratedDeriv_eq_iterate]
    simpa [pow_two] using congrArg (fun f : ℝ → ℝ ↦ f 0) (iter_deriv_inv_linear 2 u x)
  calc
    thirdDirectionalDerivative (fun y : ℝ ↦ -Real.log y) x u
        = iteratedDeriv 2 (deriv (directionalSlice (fun y : ℝ ↦ -Real.log y) x u)) 0 := by
            simp [thirdDirectionalDerivative, iteratedDeriv_succ']
    _ = iteratedDeriv 2 (fun t : ℝ ↦ -u * (u * t + x)⁻¹) 0 := by
          congr 1
          ext t
          rw [negLog_directionalSlice_deriv]
    _ = -u * iteratedDeriv 2 (fun t : ℝ ↦ (u * t + x)⁻¹) 0 := by
          exact
            iteratedDeriv_const_mul_field (n := 2) (-u) (fun t : ℝ ↦ (u * t + x)⁻¹) (x := 0)
    _ = -u * (2 * u ^ (2 : ℕ) * x ^ (-3 : ℤ)) := by rw [hinv]
    _ = -2 * u ^ (3 : ℕ) / x ^ (3 : ℕ) := by
          rw [zpow_neg]
          field_simp [hx0.ne']

/-- Helper for Example 5.1.7: the Hessian local norm of the affine-log barrier at a positive
point is `|u| / x`. -/
private theorem affinePerturbedLogBarrier_hessianLocalNorm_eq_abs_div
    (ε x u : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    ‖u‖[affinePerturbedLogBarrier ε; x] = |u| / x := by
  have hx0 : 0 < x := hx
  rw [hessianLocalNorm_def, affinePerturbedLogBarrier_hessianQuadraticForm_eq ε x u hx, ← div_pow,
    Real.sqrt_sq_eq_abs, abs_div, abs_of_pos hx0]

/-- Helper for Example 5.1.7: the third directional derivative of the affine-log barrier at a
positive point is `-2 * u^3 / x^3`. -/
private theorem affinePerturbedLogBarrier_thirdDirectionalDerivative_eq
    (ε x u : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    thirdDirectionalDerivative (affinePerturbedLogBarrier ε) x u =
      -2 * u ^ (3 : ℕ) / x ^ (3 : ℕ) := by
  have hslice :
      directionalSlice (affinePerturbedLogBarrier ε) x u =
        fun t : ℝ ↦ ε * x + (ε * u) * t + directionalSlice (fun y : ℝ ↦ -Real.log y) x u t := by
    funext t
    simp [directionalSlice, affinePerturbedLogBarrier, sub_eq_add_neg]
    ring
  have hlinZero : iteratedDeriv 3 (fun t : ℝ ↦ ε * x + (ε * u) * t) 0 = 0 := by
    rw [iteratedDeriv_const_add (n := 3) (x := 0) (f := fun t : ℝ ↦ (ε * u) * t)
      (hn := by norm_num) (c := ε * x)]
    simpa [iteratedDeriv_fun_id] using
      (iteratedDeriv_const_mul_field (n := 3) (ε * u) (fun t : ℝ ↦ t) (x := 0))
  have hx0 : 0 < x := hx
  have hneg : ContDiffAt ℝ 3 (directionalSlice (fun y : ℝ ↦ -Real.log y) x u) 0 := by
    have hbase : ContDiffAt ℝ 3 (fun y : ℝ ↦ -Real.log y) x := by
      simpa using (Real.contDiffAt_log.2 hx0.ne').neg
    have hline : ContDiffAt ℝ 3 (fun t : ℝ ↦ x + t * u) 0 := by
      fun_prop
    have hcomp :
        ContDiffAt ℝ 3 ((fun y : ℝ ↦ -Real.log y) ∘ fun t : ℝ ↦ x + t * u) 0 := by
      have hbase' : ContDiffAt ℝ 3 (fun y : ℝ ↦ -Real.log y) (x + 0 * u) := by
        simpa [zero_mul] using hbase
      simpa using hbase'.comp 0 hline
    simpa [directionalSlice, Function.comp] using hcomp
  have hlin : ContDiffAt ℝ 3 (fun t : ℝ ↦ ε * x + (ε * u) * t) 0 := by
    fun_prop
  rw [thirdDirectionalDerivative, hslice]
  calc
    iteratedDeriv 3
        (fun t : ℝ ↦ ε * x + (ε * u) * t + directionalSlice (fun y : ℝ ↦ -Real.log y) x u t)
        0
        = iteratedDeriv 3 (fun t : ℝ ↦ ε * x + (ε * u) * t) 0 +
            iteratedDeriv 3 (directionalSlice (fun y : ℝ ↦ -Real.log y) x u) 0 := by
              simpa [Pi.add_apply] using iteratedDeriv_add hlin hneg
    _ = thirdDirectionalDerivative (fun y : ℝ ↦ -Real.log y) x u := by
          simp [thirdDirectionalDerivative, hlinZero]
    _ = -2 * u ^ (3 : ℕ) / x ^ (3 : ℕ) := negLog_thirdDirectionalDerivative_eq x u hx

-- Proof sketch: verify the standard self-concordance conditions directly from the explicit
-- derivative, Hessian-local-norm, and third-directional-derivative formulas on `(0, ∞)`.
/-- Example 5.1.7: for every real parameter `ε`, the affine perturbation
`x ↦ ε x - log x` is standard self-concordant on `(0, ∞)`. -/
theorem affinePerturbedLogBarrier_isStandardSelfConcordantOn (ε : ℝ) :
    IsStandardSelfConcordantOn (Set.Ioi (0 : ℝ)) (affinePerturbedLogBarrier ε) := by
  refine
    { isOpen_domain := isOpen_Ioi
      contDiffOn := ?_
      convexOn := ?_
      third_deriv_bound := ?_ }
  · intro x hx
    have hx0 : 0 < x := hx
    have hAffine : ContDiffAt ℝ 3 (fun y : ℝ ↦ ε * y) x := by
      simpa using contDiffAt_const.mul contDiffAt_id
    have hLog : ContDiffAt ℝ 3 (fun y : ℝ ↦ -Real.log y) x := by
      simpa using (Real.contDiffAt_log.2 hx0.ne').neg
    simpa [affinePerturbedLogBarrier, sub_eq_add_neg] using (hAffine.add hLog).contDiffWithinAt
  · have hC2 : ContDiffOn ℝ 2 (affinePerturbedLogBarrier ε) (Set.Ioi (0 : ℝ)) := by
      intro x hx
      have hx0 : 0 < x := hx
      have hAffine : ContDiffAt ℝ 2 (fun y : ℝ ↦ ε * y) x := by
        simpa using contDiffAt_const.mul contDiffAt_id
      have hLog : ContDiffAt ℝ 2 (fun y : ℝ ↦ -Real.log y) x := by
        simpa using (Real.contDiffAt_log.2 hx0.ne').neg
      simpa [affinePerturbedLogBarrier, sub_eq_add_neg] using (hAffine.add hLog).contDiffWithinAt
    apply (convexOn_iff_hessian_quadratic_form_nonneg isOpen_Ioi (convex_Ioi (0 : ℝ)) hC2).2
    intro x hx u
    rw [real_inner_comm, affinePerturbedLogBarrier_hessianQuadraticForm_eq ε x u hx]
    positivity
  · intro x hx u
    rw [affinePerturbedLogBarrier_thirdDirectionalDerivative_eq ε x u hx,
      affinePerturbedLogBarrier_hessianLocalNorm_eq_abs_div ε x u hx]
    have hx0 : 0 < x := hx
    have habs :
        |(-2 : ℝ) * u ^ (3 : ℕ) / x ^ (3 : ℕ)| = 2 * (|u| / x) ^ (3 : ℕ) := by
      have hx3 : 0 < x ^ (3 : ℕ) := by positivity
      calc
        |(-2 : ℝ) * u ^ (3 : ℕ) / x ^ (3 : ℕ)|
            = |(-2 : ℝ) * u ^ (3 : ℕ)| / |x ^ (3 : ℕ)| := by rw [abs_div]
        _ = 2 * (|u| ^ (3 : ℕ) / x ^ (3 : ℕ)) := by
              rw [abs_mul, abs_pow, abs_of_pos hx3, mul_div_assoc]
              norm_num
        _ = 2 * (|u| / x) ^ (3 : ℕ) := by
              congr 1
              rw [← div_pow]
    simpa [mul_assoc] using habs.le

attribute [instance] affinePerturbedLogBarrier_isStandardSelfConcordantOn

/-- Helper for Example 5.1.7: on `(0, ∞)`, the Hessian is the scalar operator
`(1 / x^2) • 1`. -/
private theorem hessian_affinePerturbedLogBarrier_eq_smulId
    (ε x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    hessian (affinePerturbedLogBarrier ε) x = (1 / x ^ 2 : ℝ) • (1 : ℝ →L[ℝ] ℝ) := by
  apply ContinuousLinearMap.ext
  intro u
  have hhess :
      hessian (affinePerturbedLogBarrier ε) x u =
        iteratedDeriv 2 (affinePerturbedLogBarrier ε) x * u := by
    have hgradEq : ∇ (affinePerturbedLogBarrier ε) = deriv (affinePerturbedLogBarrier ε) := by
      funext y
      exact gradient_eq_deriv'
    rw [hessian, hgradEq, fderiv_eq_deriv_mul]
    simp [iteratedDeriv_succ, mul_comm]
  -- In one dimension, the Hessian acts by multiplication by the ordinary second derivative.
  calc
    hessian (affinePerturbedLogBarrier ε) x u
        = iteratedDeriv 2 (affinePerturbedLogBarrier ε) x * u := by
            rw [hhess]
    _ = (1 / x ^ 2) * u := by
          rw [secondDeriv_affinePerturbedLogBarrier_on_Ioi ε x hx]
    _ = ((1 / x ^ 2 : ℝ) • (1 : ℝ →L[ℝ] ℝ)) u := by
          simp

/-- Helper for Example 5.1.7: on `(0, ∞)`, the inverse Hessian is the scalar operator
`x^2 • 1`. -/
private theorem hessian_affinePerturbedLogBarrier_inverse_eq_smulId
    (ε x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    (hessian (affinePerturbedLogBarrier ε) x).inverse = (x ^ 2 : ℝ) • (1 : ℝ →L[ℝ] ℝ) := by
  have hx0 : 0 < x := hx
  have hscale :
      (1 / x ^ 2 : ℝ) * x ^ 2 = 1 := by
    field_simp [pow_ne_zero 2 hx0.ne']
  -- Identify the inverse by checking the two-sided composition equations.
  rw [hessian_affinePerturbedLogBarrier_eq_smulId ε x hx]
  apply ContinuousLinearMap.inverse_eq
  · apply ContinuousLinearMap.ext
    intro u
    simp
    field_simp [pow_ne_zero 2 hx0.ne']
  · apply ContinuousLinearMap.ext
    intro u
    simp
    field_simp [pow_ne_zero 2 hx0.ne']

-- Proof sketch: on `(0, ∞)`, the scalar Hessian is `1 / x^2`, so every nonzero direction `u`
-- satisfies `⟪u, hessian f x u⟫ = (1 / x^2) * u^2 > 0`.
/-- On `(0, ∞)`, the Hessian of `x ↦ ε x - log x` is positive definite. -/
theorem affinePerturbedLogBarrier_hasPositiveDefiniteHessianOn
    (ε : ℝ) :
    HasPositiveDefiniteHessianOn (Set.Ioi (0 : ℝ)) (affinePerturbedLogBarrier ε) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    -- The Hessian is a nonnegative scalar multiple of the identity at every positive point.
    rw [hessian_affinePerturbedLogBarrier_eq_smulId ε x hx]
    exact ContinuousLinearMap.isPositive_one.smul_of_nonneg (by positivity)
  · intro x hx u hu
    have hx0 : 0 < x := hx
    have hu_factor : 0 < u ^ (2 : ℕ) := by
      nlinarith [sq_pos_of_ne_zero hu]
    -- The scalar quadratic form is exactly `(1 / x^2) * u^2`.
    rw [affinePerturbedLogBarrier_hessianQuadraticForm_eq ε x u hx]
    exact div_pos hu_factor (by positivity)

attribute [instance] affinePerturbedLogBarrier_hasPositiveDefiniteHessianOn

-- Proof sketch: substitute the first- and second-derivative formulas on `(0, ∞)` and simplify
-- using `x > 0`, so `sqrt (1 / x^2) = 1 / x`, and identify the scalar formula with the canonical
-- Chapter 5 positive-definite-Hessian Newton-decrement bridge.
/-- On `(0, ∞)`, the canonical Newton decrement of `x ↦ ε x - log x` is `|1 - ε x|`. -/
theorem affinePerturbedLogBarrierNewtonDecrement_eq_abs_one_sub_mul
    (ε x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    λ[affinePerturbedLogBarrier ε; x | hx] = |1 - ε * x| := by
  have hx0 : 0 < x := hx
  -- Rewrite the decrement through the explicit inverse Hessian and scalar gradient formulas.
  rw [NewtonDecrement.ofPosDefMem_def]
  rw [gradient_eq_deriv']
  rw [deriv_affinePerturbedLogBarrier_on_Ioi ε x hx]
  rw [hessian_affinePerturbedLogBarrier_inverse_eq_smulId ε x hx]
  have hsquare :
      inner ℝ (ε - 1 / x) (((x ^ 2 : ℝ) • (1 : ℝ →L[ℝ] ℝ)) (ε - 1 / x)) =
        (1 - ε * x) ^ (2 : ℕ) := by
    calc
      inner ℝ (ε - 1 / x) (((x ^ 2 : ℝ) • (1 : ℝ →L[ℝ] ℝ)) (ε - 1 / x))
          = inner ℝ (ε - 1 / x) (x ^ 2 * (ε - 1 / x)) := by
              simp
      _ = (x ^ 2 * (ε - 1 / x)) * (ε - 1 / x) := by
            have hinner :
                inner ℝ (ε - 1 / x) (x ^ 2 * (ε - 1 / x)) =
                  (x ^ 2 * (ε - 1 / x)) * (ε - 1 / x) :=
              RCLike.inner_apply (ε - 1 / x) (x ^ 2 * (ε - 1 / x))
            rw [hinner]
      _ = (1 - ε * x) ^ (2 : ℕ) := by
            field_simp [hx0.ne']
            ring
  rw [hsquare, Real.sqrt_sq_eq_abs]

-- Proof sketch: specialize
-- `affinePerturbedLogBarrierNewtonDecrement_eq_abs_one_sub_mul` to `ε = 0` and simplify.
/-- For `ε = 0`, the canonical Newton decrement of the logarithmic barrier is identically `1` on
`(0, ∞)`. -/
theorem affinePerturbedLogBarrierNewtonDecrement_zero_eq_one
    (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    λ[affinePerturbedLogBarrier 0; x | hx] = 1 := by
  -- The closed form collapses to `|1|`.
  simpa using affinePerturbedLogBarrierNewtonDecrement_eq_abs_one_sub_mul 0 x hx

-- Proof sketch: evaluate the objective along a sequence `x_k → ∞` inside `(0, ∞)`; the
-- logarithmic term grows without bound, so the barrier values on the domain image tend to `-∞`.
/-- The pure logarithmic barrier `x ↦ -log x` is unbounded below on its natural domain `(0, ∞)`. -/
theorem affinePerturbedLogBarrier_zero_not_bddBelow :
    ¬ BddBelow (affinePerturbedLogBarrier 0 '' Set.Ioi (0 : ℝ)) := by
  intro hbdd
  rcases hbdd with ⟨m, hm⟩
  let x : ℝ := Real.exp (1 - m)
  have hx : x ∈ Set.Ioi (0 : ℝ) := by
    change 0 < x
    dsimp [x]
    positivity
  have hm_eval : m ≤ affinePerturbedLogBarrier 0 x := by
    exact hm ⟨x, hx, rfl⟩
  have hvalue : affinePerturbedLogBarrier 0 x = m - 1 := by
    -- The exponential witness makes the logarithm evaluate exactly.
    dsimp [x, affinePerturbedLogBarrier]
    rw [Real.log_exp]
    ring
  linarith

-- Proof sketch: the derivative vanishes exactly at `x = 1 / ε`, and the second derivative is
-- positive on `(0, ∞)`, so strict convexity identifies that stationary point as the global
-- minimizer over the domain.
/-- If `ε > 0`, then the global minimizer of `x ↦ ε x - log x` on `(0, ∞)` is `1 / ε`. -/
theorem isMinOn_affinePerturbedLogBarrier_inv
    {ε : ℝ} (hε : 0 < ε) :
    IsMinOn (affinePerturbedLogBarrier ε) (Set.Ioi (0 : ℝ)) (1 / ε) := by
  have hbase : 1 / ε ∈ Set.Ioi (0 : ℝ) := by
    exact one_div_pos.mpr hε
  have hderivZero : HasDerivAt (affinePerturbedLogBarrier ε) 0 (1 / ε) := by
    -- The stationary point is the unique positive zero of the derivative formula.
    convert hasDerivAt_affinePerturbedLogBarrier_onIoi (ε := ε) hbase using 1
    field_simp [hε.ne']
    ring
  let g : ℝ := (InnerProductSpace.toDual ℝ ℝ).symm ((InnerProductSpace.toDual ℝ ℝ) 0)
  have hg : g = 0 := by
    apply (InnerProductSpace.toDual ℝ ℝ).injective
    simp [g]
  have hgradWithin :
      HasGradientWithinAt
        (affinePerturbedLogBarrier ε) g (Set.Ioi (0 : ℝ)) (1 / ε) := by
    -- Repackage the scalar derivative as a within-set gradient witness at the open-domain point.
    change HasGradientWithinAt (affinePerturbedLogBarrier ε) _ (Set.Ioi (0 : ℝ)) (1 / ε)
    exact hderivZero.hasGradientAt'.hasFDerivAt.hasFDerivWithinAt.hasGradientWithinAt
  have hsupport :
      ∀ x ∈ Set.Ioi (0 : ℝ),
        affinePerturbedLogBarrier ε (1 / ε) ≤ affinePerturbedLogBarrier ε x := by
    have hself := affinePerturbedLogBarrier_isStandardSelfConcordantOn ε
    have hconv : ConvexOn ℝ (Set.Ioi (0 : ℝ)) (affinePerturbedLogBarrier ε) :=
      hself.convexOn
    intro x hx
    -- Convexity from self-concordance turns the stationary point into a supporting point.
    have hplane :
        affinePerturbedLogBarrier ε x ≥
          affinePerturbedLogBarrier ε (1 / ε) +
            inner ℝ g (x - 1 / ε) := by
      exact
        hconv.lower_tangent_plane_of_hasGradientWithinAt (1 / ε) hbase g hgradWithin x hx
    simpa [g, hg] using hplane
  exact isMinOn_iff.mpr hsupport

end
