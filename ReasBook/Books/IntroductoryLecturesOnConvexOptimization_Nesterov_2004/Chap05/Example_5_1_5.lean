/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Example_5_1_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Filter
open scoped Topology Gradient HessianLocalNorm

/- Example 5.1.5 lies in the scalar self-concordance / reciprocal-power barrier domain.

Sampled owner-style declarations:
* `IsSelfConcordantOnWith` from `Definition_5_1_1`, the Chapter 5 owner for self-concordance with
  constant `Mf`;
* `quadraticAffineObjective` from `Example_5_1_2`, the chapter source-facing owner for the
  quadratic term `(1 / 2) x^2`;
* `negLog_isStandardSelfConcordantOn` from `Example_5_1_3`, the scalar logarithmic barrier model
  for the `p → 0⁺` limit;
* `powerBarrier` from `Chap01/Proposition_1_10_17`, the earlier project owner for reciprocal-power
  barriers on strict constraint loci.

Source/core/bridge triage:
* source-facing: the scalar regularized power barrier family
  `x ↦ (1 / 2) x^2 + 1 / (p x^p) - 1 / p`;
* core/canonical: `IsSelfConcordantOnWith (Set.Ioi (0 : ℝ))`;
* bridge/view: the pointwise `p → 0⁺` limit to `x ↦ (1 / 2) x^2 - log x`.

Primitive data:
* the scalar parameter `p`.

Derived API:
* the evaluation formula for `regularizedPowerBarrier p`;
* the self-concordance statement with constant `1 + p / 2` on `(0, ∞)`;
* the pointwise limit as `p → 0⁺`.

There is no upstream owner for this exact regularized scalar family, so the local definition
remains the source-facing owner. The file is refined only to the canonical Chapter 5
self-concordance surface, and its quadratic core is reused directly from
`quadraticAffineObjective` rather than restated as a parallel local formula.
-/

/-- The regularized univariate power barrier `x ↦ (1 / 2) x^2 + 1 / (p x^p) - 1 / p`. -/
def regularizedPowerBarrier (p : ℝ) : ℝ → ℝ :=
  fun x ↦ quadraticAffineObjective 0 0 1 x + 1 / (p * Real.rpow x p) - 1 / p

-- Proof sketch: evaluate the quadratic owner with `quadraticAffineObjective_apply` and simplify in
-- the scalar Hilbert space `ℝ`.
/-- Evaluating `regularizedPowerBarrier p` returns the textbook formula for `f_p`. -/
@[simp]
theorem regularizedPowerBarrier_apply (p x : ℝ) :
    regularizedPowerBarrier p x =
      (1 / 2 : ℝ) * x ^ (2 : ℕ) + 1 / (p * Real.rpow x p) - 1 / p :=
  by
    rw [regularizedPowerBarrier, quadraticAffineObjective_apply]
    simp [pow_two]

/-- Helper for Example 5.1.5: on the positive half-line, the reciprocal-power term can be
rewritten as a scaled inverse power. -/
private theorem regularizedPowerBarrier_eq_quadratic_add_scaled_inverse_power
    {p x : ℝ} (hx : 0 < x) :
    regularizedPowerBarrier p x =
      (1 / 2 : ℝ) * x ^ (2 : ℕ) + p⁻¹ * x ^ (-p) - p⁻¹ := by
  have hx0 : 0 ≤ x := le_of_lt hx
  -- Rewrite the reciprocal term through `x ^ (-p)` so the derivative formulas match the text.
  calc
    regularizedPowerBarrier p x
        = (1 / 2 : ℝ) * x ^ (2 : ℕ) + 1 / (p * Real.rpow x p) - p⁻¹ := by
            simp [one_div, regularizedPowerBarrier_apply]
    _ = (1 / 2 : ℝ) * x ^ (2 : ℕ) + p⁻¹ * (x ^ p)⁻¹ - p⁻¹ := by
          by_cases hp0 : p = 0
          · simp [hp0]
          · have hxpow_ne : x ^ p ≠ 0 := by
                exact (Real.rpow_pos_of_pos hx p).ne'
            field_simp [hp0, hxpow_ne]
            rw [show x.rpow p = x ^ p by rfl]
            ring
    _ = (1 / 2 : ℝ) * x ^ (2 : ℕ) + p⁻¹ * x ^ (-p) - p⁻¹ := by
          rw [← Real.rpow_neg hx0]

/-- Helper for Example 5.1.5: on the positive half-line, the reciprocal-power term can be
rewritten as the logarithmic quotient base `x⁻¹`. -/
private theorem regularizedPowerBarrier_eq_quadratic_add_scaled_rpow_sub_one
    {p x : ℝ} (hx : 0 < x) :
    regularizedPowerBarrier p x =
      (1 / 2 : ℝ) * x ^ (2 : ℕ) + p⁻¹ * ((x⁻¹) ^ p - 1) := by
  have hx0 : 0 ≤ x := le_of_lt hx
  -- This is the exact normalization needed for the `p → 0⁺` logarithmic limit.
  calc
    regularizedPowerBarrier p x
        = (1 / 2 : ℝ) * x ^ (2 : ℕ) + p⁻¹ * x ^ (-p) - p⁻¹ :=
      regularizedPowerBarrier_eq_quadratic_add_scaled_inverse_power (p := p) hx
    _ = (1 / 2 : ℝ) * x ^ (2 : ℕ) + p⁻¹ * (x⁻¹) ^ p - p⁻¹ := by
          rw [Real.rpow_neg hx0, ← Real.inv_rpow hx0]
    _ = (1 / 2 : ℝ) * x ^ (2 : ℕ) + p⁻¹ * ((x⁻¹) ^ p - 1) := by
          ring

/-- Helper for Example 5.1.5: at every positive point, the regularized power barrier is smooth of
all finite orders needed in this file. -/
private theorem regularizedPowerBarrier_contDiffAt
    {p x : ℝ} (hx : 0 < x) {n : ℕ} :
    ContDiffAt ℝ n (regularizedPowerBarrier p) x := by
  have hmodel :
      ContDiffAt ℝ n
        (fun y : ℝ ↦ (1 / 2 : ℝ) * y ^ (2 : ℕ) + p⁻¹ * y ^ (-p) - p⁻¹) x := by
    -- Positive points avoid the singularity of the inverse power, so arithmetic closure applies.
    have hquad :
        ContDiffAt ℝ n (fun y : ℝ ↦ (1 / 2 : ℝ) * y ^ (2 : ℕ)) x := by
      simpa [smul_eq_mul] using (contDiffAt_id.pow 2).const_smul (1 / 2 : ℝ)
    have hinvpow :
        ContDiffAt ℝ n (fun y : ℝ ↦ p⁻¹ * y ^ (-p)) x := by
      simpa [smul_eq_mul] using
        (Real.contDiffAt_rpow_const_of_ne (x := x) (p := -p) (n := (n : WithTop ℕ∞)) hx.ne').const_smul
          (p⁻¹ : ℝ)
    exact (hquad.add hinvpow).sub contDiffAt_const
  have hEq :
      regularizedPowerBarrier p =ᶠ[𝓝 x]
        (fun y : ℝ ↦ (1 / 2 : ℝ) * y ^ (2 : ℕ) + p⁻¹ * y ^ (-p) - p⁻¹) := by
    have hpos : ∀ᶠ y in 𝓝 x, 0 < y := isOpen_Ioi.mem_nhds hx
    filter_upwards [hpos] with y hy
    simpa using regularizedPowerBarrier_eq_quadratic_add_scaled_inverse_power (p := p) hy
  exact hmodel.congr_of_eventuallyEq hEq

/-- Helper for Example 5.1.5: a `C²` scalar field has a differentiable gradient at the point. -/
private theorem differentiableAt_gradient_of_contDiffAt_two
    {f : ℝ → ℝ} {x : ℝ} (hf : ContDiffAt ℝ 2 f x) :
    DifferentiableAt ℝ (∇ f) x := by
  let D : StrongDual ℝ ℝ →L[ℝ] ℝ :=
    (InnerProductSpace.toDual ℝ ℝ).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ f) x := by
    -- A `C²` scalar field has a differentiable first derivative.
    exact
      (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))).differentiableAt
        one_ne_zero
  -- Rewrite the gradient through the Riesz map so the chain rule is immediate.
  change DifferentiableAt ℝ (fun y ↦ D (fderiv ℝ f y)) x
  exact (D.hasFDerivAt.comp x hfdiff.hasFDerivAt).differentiableAt

/-- Helper for Example 5.1.5: the affine scalar slice `t ↦ u t + x` has derivative `u`. -/
private theorem affineLine_hasDerivAt (u x t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ u * s + x) u t := by
  simpa [mul_comm, add_comm, add_left_comm, add_assoc] using
    (((hasDerivAt_id t).mul_const u).add_const x)

/-- Helper for Example 5.1.5: positivity of the affine slice persists in a neighborhood of a
positive point. -/
private theorem affineLine_eventually_pos
    {x u t : ℝ} (hxt : 0 < u * t + x) :
    ∀ᶠ s in 𝓝 t, 0 < u * s + x := by
  have hcont : Continuous fun s : ℝ ↦ u * s + x := by
    fun_prop
  -- Continuity transports the positive half-line neighborhood back to the slice parameter.
  simpa using hcont.continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds hxt)

/-- Helper for Example 5.1.5: differentiating the affine slice once yields the textbook formula
`u * (z - z^(-p-1))` with `z = u t + x`. -/
private theorem regularizedPowerBarrier_directionalSlice_deriv
    {p x u t : ℝ} (hp : 0 < p) (hxt : 0 < u * t + x) :
    deriv (directionalSlice (regularizedPowerBarrier p) x u) t =
      u * ((u * t + x) - (u * t + x) ^ (-p - 1)) := by
  let model : ℝ → ℝ :=
    fun s ↦ (1 / 2 : ℝ) * (u * s + x) ^ (2 : ℕ) + p⁻¹ * (u * s + x) ^ (-p) - p⁻¹
  have hEq :
      directionalSlice (regularizedPowerBarrier p) x u =ᶠ[𝓝 t] model := by
    have hpos : ∀ᶠ s in 𝓝 t, 0 < u * s + x := affineLine_eventually_pos hxt
    filter_upwards [hpos] with s hs
    simpa [model, directionalSlice, mul_comm, add_comm, add_left_comm, add_assoc] using
      regularizedPowerBarrier_eq_quadratic_add_scaled_inverse_power (p := p) hs
  rw [Filter.EventuallyEq.deriv_eq hEq]
  have hlin : HasDerivAt (fun s : ℝ ↦ u * s + x) u t := affineLine_hasDerivAt u x t
  have hquad :
      HasDerivAt (fun s : ℝ ↦ (1 / 2 : ℝ) * (u * s + x) ^ (2 : ℕ))
        (u * (u * t + x)) t := by
    -- Differentiate the quadratic core explicitly.
    have hpow :
        HasDerivAt (fun s : ℝ ↦ (u * s + x) ^ (2 : ℕ))
          (2 * (u * t + x) * u) t := by
      simpa using (hlin.pow 2)
    convert hpow.const_mul (1 / 2 : ℝ) using 1 <;> ring
  have hinvpow :
      HasDerivAt (fun s : ℝ ↦ p⁻¹ * (u * s + x) ^ (-p))
        (-(u * (u * t + x) ^ (-p - 1))) t := by
    -- Differentiate the inverse-power term using the `rpow` chain rule at a positive point.
    have hpow :
        HasDerivAt (fun s : ℝ ↦ (u * s + x) ^ (-p))
          ((-p) * (u * t + x) ^ (-p - 1) * u) t := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        hlin.rpow_const (p := -p) (Or.inl hxt.ne')
    have hscaled :
        HasDerivAt (fun s : ℝ ↦ p⁻¹ * (u * s + x) ^ (-p))
          (p⁻¹ * (((-p) * (u * t + x) ^ (-p - 1) * u))) t := by
      simpa [mul_assoc] using hpow.const_mul (p⁻¹ : ℝ)
    have hscaled' :
        HasDerivAt (fun s : ℝ ↦ p⁻¹ * (u * s + x) ^ (-p))
          (-(u * (u * t + x) ^ (-p - 1))) t := by
      convert hscaled using 1
      field_simp [hp.ne']
    exact hscaled'
  -- Add the differentiated pieces and simplify the scalar algebra.
  have hsum := hquad.add (hinvpow.add (hasDerivAt_const t (-p⁻¹ : ℝ)))
  have hderiv :
      deriv model t = u * (u * t + x) + -(u * (u * t + x) ^ (-p - 1)) := by
    simpa [model, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum.deriv
  ring_nf at hderiv ⊢
  exact hderiv

/-- Helper for Example 5.1.5: differentiating the slice derivative once more yields the scalar
second-derivative coefficient. -/
private theorem regularizedPowerBarrier_directionalSlice_second_deriv
    {p x u t : ℝ} (hxt : 0 < u * t + x) :
    deriv (fun s : ℝ ↦ u * ((u * s + x) - (u * s + x) ^ (-p - 1))) t =
      u ^ (2 : ℕ) * (1 + (p + 1) * (u * t + x) ^ (-p - 2)) := by
  have hlin : HasDerivAt (fun s : ℝ ↦ u * s + x) u t := affineLine_hasDerivAt u x t
  -- Differentiate the affine part and the inverse-power correction separately.
  have hpow :
      HasDerivAt (fun s : ℝ ↦ (u * s + x) ^ (-p - 1))
        (u * ((-p - 1) * (u * t + x) ^ (-p - 1 - 1))) t := by
    simpa [mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg, add_assoc, add_left_comm] using
      hlin.rpow_const (p := -p - 1) (Or.inl hxt.ne')
  have hinside :
      HasDerivAt (fun s : ℝ ↦ (u * s + x) - (u * s + x) ^ (-p - 1))
        (u - u * ((-p - 1) * (u * t + x) ^ (-p - 1 - 1))) t := by
    exact hlin.sub hpow
  have hscaled :
      HasDerivAt (fun s : ℝ ↦ u * ((u * s + x) - (u * s + x) ^ (-p - 1)))
        (u * (u - u * ((-p - 1) * (u * t + x) ^ (-p - 1 - 1)))) t := by
    simpa [mul_assoc] using hinside.const_mul u
  convert hscaled.deriv using 1 <;> ring

/-- Helper for Example 5.1.5: the third slice derivative has the textbook cubic coefficient. -/
private theorem regularizedPowerBarrier_directionalSlice_third_deriv
    {p x u t : ℝ} (hxt : 0 < u * t + x) :
    deriv (fun s : ℝ ↦ u ^ (2 : ℕ) * (1 + (p + 1) * (u * s + x) ^ (-p - 2))) t =
      -((p + 1) * (p + 2)) * u ^ (3 : ℕ) * (u * t + x) ^ (-p - 3) := by
  have hlin : HasDerivAt (fun s : ℝ ↦ u * s + x) u t := affineLine_hasDerivAt u x t
  -- Only the inverse-power correction contributes at third order.
  have hpow :
      HasDerivAt (fun s : ℝ ↦ (u * s + x) ^ (-p - 2))
        (u * ((-p - 2) * (u * t + x) ^ (-p - 2 - 1))) t := by
    simpa [mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg, add_assoc, add_left_comm] using
      hlin.rpow_const (p := -p - 2) (Or.inl hxt.ne')
  have hscaled :
      HasDerivAt (fun s : ℝ ↦ (p + 1) * (u * s + x) ^ (-p - 2))
        ((p + 1) * (u * ((-p - 2) * (u * t + x) ^ (-p - 2 - 1)))) t := by
    simpa [mul_assoc] using hpow.const_mul (p + 1 : ℝ)
  have hinside :
      HasDerivAt (fun s : ℝ ↦ 1 + (p + 1) * (u * s + x) ^ (-p - 2))
        (0 + (p + 1) * (u * ((-p - 2) * (u * t + x) ^ (-p - 2 - 1)))) t := by
    exact (hasDerivAt_const t (1 : ℝ)).add hscaled
  have houter :
      HasDerivAt (fun s : ℝ ↦ u ^ (2 : ℕ) * (1 + (p + 1) * (u * s + x) ^ (-p - 2)))
        (u ^ (2 : ℕ) * (0 + (p + 1) * (u * ((-p - 2) * (u * t + x) ^ (-p - 2 - 1))))) t := by
    simpa [mul_assoc] using hinside.const_mul (u ^ (2 : ℕ) : ℝ)
  convert houter.deriv using 1 <;> ring

/-- Helper for Example 5.1.5: the Hessian quadratic form of the regularized power barrier is the
explicit scalar second derivative from the textbook. -/
theorem regularizedPowerBarrier_hessian_quadratic_form_eq
    {p x u : ℝ} (hp : 0 < p) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    inner ℝ u (hessian (regularizedPowerBarrier p) x u) =
      u ^ (2 : ℕ) * (1 + (p + 1) / x ^ (p + 2)) := by
  have hx0 : 0 < x := hx
  have hcont : ContDiffAt ℝ 2 (regularizedPowerBarrier p) x :=
    regularizedPowerBarrier_contDiffAt (p := p) hx0
  have hdiff : DifferentiableAt ℝ (regularizedPowerBarrier p) x :=
    hcont.differentiableAt (by norm_num)
  have hgrad : DifferentiableAt ℝ (∇ (regularizedPowerBarrier p)) x :=
    differentiableAt_gradient_of_contDiffAt_two hcont
  have hpos : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < u * t + x := by
    simpa using affineLine_eventually_pos (x := x) (u := u) (t := (0 : ℝ)) (by simpa using hx0)
  have hEq :
      deriv (directionalSlice (regularizedPowerBarrier p) x u) =ᶠ[𝓝 (0 : ℝ)]
        fun t : ℝ ↦ u * ((u * t + x) - (u * t + x) ^ (-p - 1)) := by
    filter_upwards [hpos] with t ht
    exact regularizedPowerBarrier_directionalSlice_deriv (p := p) (x := x) (u := u) (t := t) hp ht
  have hsecond :
      secondDirectionalDerivative (regularizedPowerBarrier p) x u =
        u ^ (2 : ℕ) * (1 + (p + 1) * x ^ (-p - 2)) := by
    -- Differentiate the slice once, then evaluate its derivative at the base point.
    calc
      secondDirectionalDerivative (regularizedPowerBarrier p) x u
          = deriv (deriv (directionalSlice (regularizedPowerBarrier p) x u)) 0 := by
              simp [secondDirectionalDerivative, iteratedDeriv_succ]
      _ = deriv (fun t : ℝ ↦ u * ((u * t + x) - (u * t + x) ^ (-p - 1))) 0 := by
            exact Filter.EventuallyEq.deriv_eq hEq
      _ = u ^ (2 : ℕ) * (1 + (p + 1) * x ^ (-p - 2)) := by
            simpa using
              regularizedPowerBarrier_directionalSlice_second_deriv
                (p := p) (x := x) (u := u) (t := (0 : ℝ)) (by simpa using hx0)
  -- Bridge the scalar slice computation back to the intrinsic Hessian owner.
  calc
    inner ℝ u (hessian (regularizedPowerBarrier p) x u)
        = secondDirectionalDerivative (regularizedPowerBarrier p) x u := by
            symm
            exact secondDirectionalDerivative_eq_hessian_quadratic_form hdiff hgrad
    _ = u ^ (2 : ℕ) * (1 + (p + 1) * x ^ (-p - 2)) := hsecond
    _ = u ^ (2 : ℕ) * (1 + (p + 1) / x ^ (p + 2)) := by
          have hneg : x ^ (-p - 2) = (x ^ (p + 2))⁻¹ := by
            have hexp : -p - 2 = -(p + 2) := by ring
            rw [hexp, Real.rpow_neg (le_of_lt hx0)]
          rw [hneg]
          simp [div_eq_mul_inv]

/-- Helper for Example 5.1.5: the Hessian local norm is the absolute direction scaled by the
square root of the scalar second derivative. -/
theorem regularizedPowerBarrier_hessianLocalNorm_eq
    {p x u : ℝ} (hp : 0 < p) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    ‖u‖[regularizedPowerBarrier p; x] =
      |u| * Real.sqrt (1 + (p + 1) / x ^ (p + 2)) := by
  have hx0 : 0 < x := hx
  have hcoeff : 0 ≤ 1 + (p + 1) / x ^ (p + 2) := by
    positivity
  -- Expand the local norm and collapse the square root of the quadratic factor.
  calc
    ‖u‖[regularizedPowerBarrier p; x]
        = Real.sqrt (u ^ (2 : ℕ) * (1 + (p + 1) / x ^ (p + 2))) := by
            rw [hessianLocalNorm_def, regularizedPowerBarrier_hessian_quadratic_form_eq hp hx]
    _ = Real.sqrt (u ^ (2 : ℕ)) * Real.sqrt (1 + (p + 1) / x ^ (p + 2)) := by
          rw [Real.sqrt_mul (show 0 ≤ u ^ (2 : ℕ) by positivity)]
    _ = |u| * Real.sqrt (1 + (p + 1) / x ^ (p + 2)) := by
          rw [pow_two, Real.sqrt_mul_self_eq_abs]

/-- Helper for Example 5.1.5: the third directional derivative matches the scalar cubic formula
from the textbook. -/
theorem regularizedPowerBarrier_thirdDirectionalDerivative_eq
    {p x u : ℝ} (hp : 0 < p) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    thirdDirectionalDerivative (regularizedPowerBarrier p) x u =
      -((p + 1) * (p + 2)) * u ^ (3 : ℕ) / x ^ (p + 3) := by
  have hx0 : 0 < x := hx
  have hpos : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < u * t + x := by
    simpa using affineLine_eventually_pos (x := x) (u := u) (t := (0 : ℝ)) (by simpa using hx0)
  have hEq1 :
      deriv (directionalSlice (regularizedPowerBarrier p) x u) =ᶠ[𝓝 (0 : ℝ)]
        fun t : ℝ ↦ u * ((u * t + x) - (u * t + x) ^ (-p - 1)) := by
    filter_upwards [hpos] with t ht
    exact regularizedPowerBarrier_directionalSlice_deriv (p := p) (x := x) (u := u) (t := t) hp ht
  have hEq2 :
      deriv (fun t : ℝ ↦ u * ((u * t + x) - (u * t + x) ^ (-p - 1))) =ᶠ[𝓝 (0 : ℝ)]
        fun t : ℝ ↦ u ^ (2 : ℕ) * (1 + (p + 1) * (u * t + x) ^ (-p - 2)) := by
    filter_upwards [hpos] with t ht
    exact regularizedPowerBarrier_directionalSlice_second_deriv (p := p) (x := x) (u := u) (t := t) ht
  -- Differentiate the slice twice after the first explicit derivative formula is in place.
  calc
    thirdDirectionalDerivative (regularizedPowerBarrier p) x u
        = iteratedDeriv 2 (deriv (directionalSlice (regularizedPowerBarrier p) x u)) 0 := by
            simp [thirdDirectionalDerivative, iteratedDeriv_succ']
    _ = iteratedDeriv 2 (fun t : ℝ ↦ u * ((u * t + x) - (u * t + x) ^ (-p - 1))) 0 := by
          exact Filter.EventuallyEq.iteratedDeriv_eq 2 hEq1
    _ = deriv (deriv (fun t : ℝ ↦ u * ((u * t + x) - (u * t + x) ^ (-p - 1)))) 0 := by
          simp [iteratedDeriv_succ]
    _ = deriv (fun t : ℝ ↦ u ^ (2 : ℕ) * (1 + (p + 1) * (u * t + x) ^ (-p - 2))) 0 := by
          exact Filter.EventuallyEq.deriv_eq hEq2
    _ = -((p + 1) * (p + 2)) * u ^ (3 : ℕ) * x ^ (-p - 3) := by
          simpa using
            regularizedPowerBarrier_directionalSlice_third_deriv
              (p := p) (x := x) (u := u) (t := (0 : ℝ)) (by simpa using hx0)
    _ = -((p + 1) * (p + 2)) * u ^ (3 : ℕ) / x ^ (p + 3) := by
          have hneg : x ^ (-p - 3) = (x ^ (p + 3))⁻¹ := by
            have hexp : -p - 3 = -(p + 3) := by ring
            rw [hexp, Real.rpow_neg (le_of_lt hx0)]
          rw [hneg]
          simp [div_eq_mul_inv, mul_assoc]

/-- Helper for Example 5.1.5: the textbook split `x ≥ 1` versus `x ≤ 1` yields the cubic
self-concordance estimate with coefficient `p + 2`. -/
private theorem regularizedPowerBarrier_cubic_bound
    {p x u : ℝ} (hp : 0 < p) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    |thirdDirectionalDerivative (regularizedPowerBarrier p) x u| ≤
      (p + 2) * ‖u‖[regularizedPowerBarrier p; x] ^ (3 : ℕ) := by
  have hx0 : 0 < x := hx
  let A : ℝ := 1 + (p + 1) / x ^ (p + 2)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hxpow3_pos : 0 < x ^ (p + 3) := Real.rpow_pos_of_pos hx0 _
  have habs :
      |(-((p + 1) * (p + 2)) : ℝ) * u ^ (3 : ℕ) / x ^ (p + 3)| =
        (p + 2) * |u| ^ (3 : ℕ) * ((p + 1) / x ^ (p + 3)) := by
    calc
      |(-((p + 1) * (p + 2)) : ℝ) * u ^ (3 : ℕ) / x ^ (p + 3)|
          = ((p + 1) * (p + 2)) * |u| ^ (3 : ℕ) / x ^ (p + 3) := by
              rw [abs_div, abs_mul, abs_neg, abs_pow, abs_of_pos hxpow3_pos,
                abs_of_nonneg]
              positivity
      _ = (p + 2) * |u| ^ (3 : ℕ) * ((p + 1) / x ^ (p + 3)) := by
            field_simp [hxpow3_pos.ne']
  have hcube :
      (|u| * Real.sqrt A) ^ (3 : ℕ) = |u| ^ (3 : ℕ) * A * Real.sqrt A := by
    -- Collapse the quadratic square root before comparing scalar coefficients.
    calc
      (|u| * Real.sqrt A) ^ (3 : ℕ)
          = (|u| * Real.sqrt A) ^ (2 : ℕ) * (|u| * Real.sqrt A) := by
              simp [pow_succ]
      _ = (|u| ^ (2 : ℕ) * (Real.sqrt A) ^ (2 : ℕ)) * (|u| * Real.sqrt A) := by
            ring
      _ = (|u| ^ (2 : ℕ) * A) * (|u| * Real.sqrt A) := by
            rw [pow_two, Real.sq_sqrt hA_nonneg]
      _ = |u| ^ (3 : ℕ) * A * Real.sqrt A := by
            ring
  have hcoeff :
      (p + 1) / x ^ (p + 3) ≤ A * Real.sqrt A := by
    rcases le_or_gt 1 x with hx1 | hx1
    · -- On `x ≥ 1`, the extra `1 / x` factor is harmless and `A ≥ 1`.
      have hxpow :
          x ^ (p + 3) = x ^ (p + 2) * x := by
        rw [show p + 3 = (p + 2) + 1 by ring, Real.rpow_add hx0, Real.rpow_one]
      have hstep1 : (p + 1) / x ^ (p + 3) ≤ (p + 1) / x ^ (p + 2) := by
        have hxpow2_pos : 0 < x ^ (p + 2) := Real.rpow_pos_of_pos hx0 _
        rw [hxpow]
        field_simp [hxpow2_pos.ne', hx0.ne']
        nlinarith
      have hstep2 : (p + 1) / x ^ (p + 2) ≤ A := by
        dsimp [A]
        nlinarith
      have hA_ge_one : 1 ≤ A := by
        have hnonneg : 0 ≤ (p + 1) / x ^ (p + 2) := by positivity
        dsimp [A]
        nlinarith
      have hsqrtA_ge_one : 1 ≤ Real.sqrt A := by
        nlinarith [Real.sq_sqrt hA_nonneg, Real.sqrt_nonneg A, hA_ge_one]
      have hstep3 : A ≤ A * Real.sqrt A := by
        calc
          A = A * 1 := by ring
          _ ≤ A * Real.sqrt A := by
                gcongr
      exact hstep1.trans (hstep2.trans hstep3)
    · -- On `x ≤ 1`, the source proof compares against the dominant inverse-power part.
      have hx1' : x ≤ 1 := le_of_lt hx1
      let B : ℝ := (p + 1) / x ^ (p + 2)
      have hB_nonneg : 0 ≤ B := by
        dsimp [B]
        positivity
      have hxpow_split :
          x ^ (p + 2) = x ^ p * x ^ (2 : ℕ) := by
        simpa using (Real.rpow_add hx0 p (2 : ℝ))
      have hxpow_le_one : x ^ p ≤ 1 := Real.rpow_le_one (le_of_lt hx0) hx1' hp.le
      have hratio_ge_one : 1 ≤ (p + 1) / x ^ p := by
        have hxpow_pos : 0 < x ^ p := Real.rpow_pos_of_pos hx0 _
        have hp1 : 1 ≤ p + 1 := by
          linarith
        exact (le_div_iff₀ hxpow_pos).2 (by nlinarith)
      have hB_lower : 1 / x ^ (2 : ℕ) ≤ B := by
        have hx2_pos : 0 < x ^ (2 : ℕ) := by positivity
        have hxpow_pos : 0 < x ^ p := Real.rpow_pos_of_pos hx0 _
        dsimp [B]
        rw [hxpow_split]
        field_simp [hx2_pos.ne', hxpow_pos.ne']
        nlinarith
      have hsqrtB : 1 / x ≤ Real.sqrt B := by
        have hsq : (1 / x) ^ (2 : ℕ) ≤ B := by
          simpa [pow_two] using hB_lower
        exact (Real.le_sqrt (by positivity) hB_nonneg).2 hsq
      have hxpow :
          x ^ (p + 3) = x ^ (p + 2) * x := by
        rw [show p + 3 = (p + 2) + 1 by ring, Real.rpow_add hx0, Real.rpow_one]
      have hcoreB :
          (p + 1) / x ^ (p + 3) ≤ B * Real.sqrt B := by
        have hleft :
            (p + 1) / x ^ (p + 3) = B * (1 / x) := by
          dsimp [B]
          rw [hxpow]
          field_simp [Real.rpow_pos_of_pos hx0 (p + 2), hx0.ne']
        calc
          (p + 1) / x ^ (p + 3) = B * (1 / x) := hleft
          _ ≤ B * Real.sqrt B := by
                gcongr
      have hBA : B ≤ A := by
        dsimp [A, B]
        nlinarith
      have hsqrtBA : Real.sqrt B ≤ Real.sqrt A := Real.sqrt_le_sqrt hBA
      calc
        (p + 1) / x ^ (p + 3) ≤ B * Real.sqrt B := hcoreB
        _ ≤ A * Real.sqrt A := by
              gcongr
  -- Rewrite both sides to a common scalar coefficient and apply the case split estimate above.
  rw [regularizedPowerBarrier_thirdDirectionalDerivative_eq hp hx,
    regularizedPowerBarrier_hessianLocalNorm_eq hp hx, habs]
  calc
    (p + 2) * |u| ^ (3 : ℕ) * ((p + 1) / x ^ (p + 3))
        ≤ (p + 2) * |u| ^ (3 : ℕ) * (A * Real.sqrt A) := by
            gcongr
    _ = (p + 2) * (|u| * Real.sqrt A) ^ (3 : ℕ) := by
          rw [hcube]
          ring

-- Proof sketch: use the explicit derivative formulas from the textbook on `(0, ∞)`, verify the
-- Hessian positivity, and check the cubic self-concordance bound separately on `x ≥ 1` and on
-- `0 < x ≤ 1`; the larger of the two resulting constants is `1 + p / 2`.
/-- Example 5.1.5: for `p > 0`, the regularized power barrier
`f_p(x) = (1 / 2) x^2 + 1 / (p x^p) - 1 / p` is self-concordant on `(0, ∞)` with
self-concordance constant `M_f = 1 + p / 2`. -/
theorem regularizedPowerBarrier_isSelfConcordantOnWith
    {p : ℝ} (hp : 0 < p) :
    IsSelfConcordantOnWith (Set.Ioi (0 : ℝ)) (Real.toNNReal (1 + p / 2))
      (regularizedPowerBarrier p) := by
  refine
    { isOpen_domain := isOpen_Ioi
      contDiffOn := ?_
      convexOn := ?_
      third_deriv_bound := ?_ }
  · intro x hx
    -- Positive points avoid the singularity at `0`, so the inverse-power term is smooth.
    exact (regularizedPowerBarrier_contDiffAt (p := p) (x := x) hx).contDiffWithinAt
  · -- Route correction: use the explicit positive Hessian quadratic form instead of a generic
    -- strong-convexity detour, which would obscure the source proof's scalar structure.
    have hC2 : ContDiffOn ℝ 2 (regularizedPowerBarrier p) (Set.Ioi (0 : ℝ)) := by
      intro x hx
      exact (regularizedPowerBarrier_contDiffAt (p := p) (x := x) hx).contDiffWithinAt
    apply
      (convexOn_iff_hessian_quadratic_form_nonneg isOpen_Ioi (convex_Ioi (0 : ℝ)) hC2).2
    intro x hx u
    have hx0 : 0 < x := hx
    rw [real_inner_comm, regularizedPowerBarrier_hessian_quadratic_form_eq hp hx]
    have hcoeff : 0 ≤ 1 + (p + 1) / x ^ (p + 2) := by positivity
    nlinarith [sq_nonneg u, hcoeff]
  · intro x hx u
    have hMf :
        2 * (Real.toNNReal (1 + p / 2) : ℝ) = p + 2 := by
      have hnonneg : 0 ≤ 1 + p / 2 := by
        nlinarith
      simpa [Real.toNNReal_of_nonneg hnonneg] using
        (show 2 * (1 + p / 2) = p + 2 by ring)
    -- After rewriting the Chapter 5 coefficient, the remaining estimate is exactly the textbook
    -- cubic bound proved above.
    rw [hMf]
    exact regularizedPowerBarrier_cubic_bound hp hx

-- Proof sketch: rewrite
-- `1 / (p * x^p) - 1 / p = (((1 / x)^p) - 1) / p`, express `((1 / x)^p)` as
-- `exp (p * log (1 / x))`, and identify the right-hand derivative at `p = 0`.
/-- As `p → 0⁺`, the regularized power barrier converges pointwise on `(0, ∞)` to
`x ↦ (1 / 2) x^2 - log x`. -/
theorem tendsto_regularizedPowerBarrier_at_zero
    {x : ℝ} (hx : 0 < x) :
    Tendsto (fun p : ℝ ↦ regularizedPowerBarrier p x)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds ((1 / 2 : ℝ) * x ^ (2 : ℕ) - Real.log x)) := by
  have hxinv : 0 < x⁻¹ := inv_pos.mpr hx
  have hmodel :
      Tendsto (fun p : ℝ ↦ (1 / 2 : ℝ) * x ^ (2 : ℕ) + p⁻¹ * ((x⁻¹) ^ p - 1))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
        (nhds ((1 / 2 : ℝ) * x ^ (2 : ℕ) + Real.log (x⁻¹))) := by
    -- The singular quotient converges to the logarithm of the positive base `x⁻¹`.
    exact tendsto_const_nhds.add (tendsto_rpow_sub_one_log (x := x⁻¹) hxinv)
  have hEq :
      (fun p : ℝ ↦ regularizedPowerBarrier p x) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))]
        fun p : ℝ ↦ (1 / 2 : ℝ) * x ^ (2 : ℕ) + p⁻¹ * ((x⁻¹) ^ p - 1) := by
    exact Filter.Eventually.of_forall fun p =>
      regularizedPowerBarrier_eq_quadratic_add_scaled_rpow_sub_one (p := p) hx
  -- Replace the model limit `log (x⁻¹)` by `-log x`.
  have hmain :
      Tendsto (fun p : ℝ ↦ regularizedPowerBarrier p x)
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
        (nhds ((1 / 2 : ℝ) * x ^ (2 : ℕ) + Real.log (x⁻¹))) :=
    hmodel.congr' hEq.symm
  simpa [sub_eq_add_neg] using hmain
