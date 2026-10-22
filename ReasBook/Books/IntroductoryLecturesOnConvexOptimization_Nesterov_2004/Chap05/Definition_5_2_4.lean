/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_24
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_2_3

open InnerProductSpace
open scoped Gradient NewtonDecrement

noncomputable section

/- Definition 5.2.4 lies in the Chapter 5 self-concordant path-following / tilted-objective
Newton-decrement domain.

Source/core/bridge triage:
* source-facing: the shifted-objective decrement `λ_{ψ(t; ·)}(y)`
* core/canonical: `newtonDecrement (auxiliaryCentralPathObjective f y₀ t) y`
* bridge/view: the shifted-gradient/Hessian identities and the determinant-based Hessian
  invertibility bridge

Mandatory domain-style sampling before refinement:
* `auxiliaryCentralPathObjective` in `Chap05/Definition_5_2_3`, the chapter owner for the tilted
  objective `ψ(t; ·)`
* `newtonDecrement` in `Chap05/Definition_5_0_24`, the chapter owner for Newton decrements
* `newtonDecrement_def` in `Chap05/Definition_5_0_24`, the canonical inverse-Hessian pairing
  expansion of the Newton-decrement owner
* `HessianDualLocalNorm.ofDetNeZero` / `HessianDualLocalNorm.ofDetNeZero_def` in
  `Chap05/Definition_5_0_20`, the determinant bridge for the shifted gradient covector

Best owner abstraction:
* source-facing: the Newton decrement of the tilted objective `ψ(t; ·)`
* core/canonical: `newtonDecrement` applied to `auxiliaryCentralPathObjective f y₀ t`
* bridge/view: the shifted-gradient formula and the determinant-nondegeneracy specialization

Primitive data:
* a function `f`
* a base point `y₀`
* a path parameter `t`
* an evaluation point `y`
* Hessian positivity and nondegeneracy at `y`

Derived API:
* the source-facing notation `λψ[f; y₀; t; y](hPos; hHy)`
* the bridge to `newtonDecrement (auxiliaryCentralPathObjective f y₀ t) y`
* the shifted-gradient and Hessian identities for the tilted objective
* the inverse-Hessian pairing formula and determinant-dual-norm specialization

This refinement makes the mathematical owner explicit: Definition 5.2.4 is a specialization of
the Chapter 5 Newton-decrement owner to the tilted objective `ψ(t; ·)`. The determinant witness
survives only in the thin bridge layer that supplies the tilted objective's Hessian
invertibility from the unchanged Hessian of `f`. -/

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section

/- Definition 5.2.4 recalls the Chapter 5 Newton-decrement owner specialized to the tilted
objective `auxiliaryCentralPathObjective f y₀ t`. -/
recall newtonDecrement

/-- Helper for Definition 5.2.4: gradients of scalar fields subtract by subtracting their gradient
vectors. -/
private theorem hasGradientAt_sub
    {f g : E → ℝ} {u v : E} {x : E}
    (hf : HasGradientAt f u x) (hg : HasGradientAt g v x) :
    HasGradientAt (fun y : E ↦ f y - g y) (u - v) x := by
  -- Rewrite the scalar subtraction at the Fréchet-derivative level and then transport back
  -- through the Riesz isomorphism.
  have hsub :
      HasFDerivAt (fun y : E ↦ f y - g y)
        ((InnerProductSpace.toDual ℝ E) u - (InnerProductSpace.toDual ℝ E) v) x := by
    exact hf.hasFDerivAt.sub hg.hasFDerivAt
  have hgrad :
      HasGradientAt (fun y : E ↦ f y - g y)
        ((InnerProductSpace.toDual ℝ E).symm
          ((InnerProductSpace.toDual ℝ E) u - (InnerProductSpace.toDual ℝ E) v)) x := by
    exact hsub.hasGradientAt
  convert hgrad using 1
  rw [map_sub]
  simp

/-- Helper for Definition 5.2.4: the linear tilt `z ↦ t * ⟪c, z⟫` has constant gradient
`(t : ℝ) • c`. -/
private theorem linearTilt_hasGradientAt
    {c : E} (t : ℝ) {y : E} :
    HasGradientAt (fun z : E ↦ t * inner ℝ c z) ((t : ℝ) • c) y := by
  -- The tilt is the scalar continuous linear map `((t : ℝ) • innerSL ℝ c)`.
  rw [hasGradientAt_iff_hasFDerivAt]
  simpa using (((t : ℝ) • innerSL ℝ c).hasFDerivAt :
    HasFDerivAt (fun z : E ↦ ((t : ℝ) • innerSL ℝ c) z) ((t : ℝ) • innerSL ℝ c) y)

/-- Helper for Definition 5.2.4: a `C²` scalar field has a differentiable gradient map. -/
private theorem differentiableAt_gradient_ofContDiffAtTwo
    {g : E → ℝ} {x : E} (hg : ContDiffAt ℝ 2 g x) :
    DifferentiableAt ℝ (∇ g) x := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  -- Rewrite the gradient through the Riesz map so differentiability reduces to the derivative
  -- field of `g`.
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ g) x := by
    exact
      (hg.fderiv_right
        (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))).differentiableAt
        one_ne_zero
  change DifferentiableAt ℝ (fun y ↦ D (fderiv ℝ g y)) x
  exact (D.hasFDerivAt.comp x hfdiff.hasFDerivAt).differentiableAt

/-- Helper for Definition 5.2.4: on an open neighborhood where both scalar fields are `C²`, the
Hessian of their difference is the difference of their Hessians. -/
private theorem hessian_sub_eq_ofContDiffOn
    {s : Set E} {f g : E → ℝ} {x : E}
    (hf : ContDiffOn ℝ 2 f s) (hg : ContDiffOn ℝ 2 g s)
    (hs_open : IsOpen s) (hx : x ∈ s) :
    hessian (fun y ↦ f y - g y) x = hessian f x - hessian g x := by
  have hgrad_nhds :
      (fun y ↦ ∇ (fun z : E ↦ f z - g z) y) =ᶠ[nhds x] fun y ↦ ∇ f y - ∇ g y := by
    -- Near `x`, both fields are differentiable, so the gradient of the difference is pointwise
    -- subtractive.
    filter_upwards [hs_open.mem_nhds hx] with y hy
    have hfy : DifferentiableAt ℝ f y := by
      exact (hf.contDiffAt (hs_open.mem_nhds hy)).differentiableAt (by norm_num)
    have hgy : DifferentiableAt ℝ g y := by
      exact (hg.contDiffAt (hs_open.mem_nhds hy)).differentiableAt (by norm_num)
    have hfgrad : HasGradientAt f (∇ f y) y := hfy.hasGradientAt
    have hggrad : HasGradientAt g (∇ g y) y := hgy.hasGradientAt
    exact (hasGradientAt_sub hfgrad hggrad).gradient
  have hgradf : DifferentiableAt ℝ (∇ f) x := by
    -- A `C²` scalar field has a differentiable gradient map at the base point.
    exact differentiableAt_gradient_ofContDiffAtTwo (hf.contDiffAt (hs_open.mem_nhds hx))
  have hgradg : DifferentiableAt ℝ (∇ g) x := by
    exact differentiableAt_gradient_ofContDiffAtTwo (hg.contDiffAt (hs_open.mem_nhds hx))
  -- Differentiate the neighborhood identity for the gradient at the base point.
  rw [hessian, hgrad_nhds.fderiv_eq]
  change fderiv ℝ ((∇ f) - (∇ g)) x = hessian f x - hessian g x
  rw [fderiv_sub hgradf hgradg]

/-- Helper for Definition 5.2.4: the linear tilt has zero Hessian. -/
private theorem linearTilt_hessian_eq_zero
    {c : E} (t : ℝ) (y : E) :
    hessian (fun z : E ↦ t * inner ℝ c z) y = 0 := by
  have hgrad :
      ∇ (fun z : E ↦ t * inner ℝ c z) = fun _ : E ↦ (t : ℝ) • c := by
    -- The gradient field of a scalar linear map is constant.
    refine gradient_eq ?_
    intro x
    exact linearTilt_hasGradientAt (c := c) t
  -- Differentiate the constant gradient field.
  rw [hessian, hgrad]
  ext h
  simp

/-- The gradient of the tilted objective `ψ(t; ·)` is the shifted gradient
`∇ f(y) - t ∇ f(y₀)`. -/
theorem auxiliaryCentralPathObjective_gradient_eq
    {dom : Set E} (f : E → ℝ) (y0 : dom) (t : ℝ) (y : E)
    (hf : DifferentiableAt ℝ f y) :
    ∇ (auxiliaryCentralPathObjective f y0 t) y =
      ∇ f y - (t : ℝ) • ∇ f (y0 : E) := by
  -- Route correction: the unguarded gradient identity is false at nondifferentiable points
  -- because `gradient` is totalized by `fderiv`; use the genuine differentiability witness at `y`.
  have hfgrad : HasGradientAt f (∇ f y) y := hf.hasGradientAt
  have htilt :
      HasGradientAt (fun z : E ↦ t * inner ℝ (∇ f (y0 : E)) z)
        ((t : ℝ) • ∇ f (y0 : E)) y := by
    exact linearTilt_hasGradientAt (c := ∇ f (y0 : E)) t
  have hobj :
      HasGradientAt (auxiliaryCentralPathObjective f y0 t)
        (∇ f y - (t : ℝ) • ∇ f (y0 : E)) y := by
    -- Differentiate the objective as `f` minus its linear tilt.
    simpa [auxiliaryCentralPathObjective] using hasGradientAt_sub hfgrad htilt
  exact hobj.gradient

/-- The linear tilt in `ψ(t; ·)` does not change the Hessian. -/
theorem auxiliaryCentralPathObjective_hessian_eq
    {dom : Set E} (f : E → ℝ) (y0 : dom) (t : ℝ) (y : E)
    (hf : ContDiffAt ℝ 2 f y) :
    hessian (auxiliaryCentralPathObjective f y0 t) y = hessian f y := by
  let c : E := ∇ f (y0 : E)
  obtain ⟨u, hu_nhds, hfu⟩ := hf.contDiffOn (m := 2) le_rfl (by simp)
  obtain ⟨s, hs_sub, hs_open, hy_mem⟩ := mem_nhds_iff.mp hu_nhds
  have hfs : ContDiffOn ℝ 2 f s := hfu.mono hs_sub
  have htilt_s : ContDiffOn ℝ 2 (fun z : E ↦ t * inner ℝ c z) s := by
    simpa using (((t : ℝ) • innerSL ℝ c).contDiff.contDiffOn : ContDiffOn ℝ 2
      (fun z : E ↦ ((t : ℝ) • innerSL ℝ c) z) s)
  -- Pass to an open `C²` neighborhood and then remove the zero Hessian of the linear tilt.
  calc
    hessian (auxiliaryCentralPathObjective f y0 t) y =
        hessian (fun z : E ↦ f z - t * inner ℝ c z) y := by
      rfl
    _ = hessian f y - hessian (fun z : E ↦ t * inner ℝ c z) y := by
      exact hessian_sub_eq_ofContDiffOn hfs htilt_s hs_open hy_mem
    _ = hessian f y := by
      simp [linearTilt_hessian_eq_zero]

/-- Hessian positivity for `f` at `y` transfers directly to the tilted objective `ψ(t; ·)` at
the same point. -/
theorem auxiliaryCentralPathObjective_hessian_isPositive
    {dom : Set E} (f : E → ℝ) (y0 : dom) (t : ℝ) (y : E)
    (hf : ContDiffAt ℝ 2 f y)
    (hPos : (hessian f y).IsPositive) :
    (hessian (auxiliaryCentralPathObjective f y0 t) y).IsPositive := by
  simpa [auxiliaryCentralPathObjective_hessian_eq f y0 t y hf] using hPos

/-- Hessian nondegeneracy for `f` at `y` canonically yields Hessian invertibility for the tilted
objective `ψ(t; ·)` at `y`. -/
theorem auxiliaryCentralPathObjective_hessian_isInvertible
    {dom : Set E} (f : E → ℝ) (y0 : dom) (t : ℝ) (y : E)
    (hf : ContDiffAt ℝ 2 f y)
    (hHy : (hessian f y).det ≠ 0) :
    (hessian (auxiliaryCentralPathObjective f y0 t) y).IsInvertible := by
  simpa [auxiliaryCentralPathObjective_hessian_eq f y0 t y hf] using
    (hessian_isInvertible_of_det_ne_zero hHy : (hessian f y).IsInvertible)

namespace AuxiliaryCentralPathNewtonDecrement

/-- Source-facing notation for the Newton decrement `λ_{ψ(t; ·)}(y)` of the tilted objective,
read through the determinant-based Hessian bridge at `y`. -/
scoped notation:max "λψ[" f "; " y0 "; " t "; " y "](" hf "; " hPos "; " hHy ")" =>
  newtonDecrement (auxiliaryCentralPathObjective f y0 t) y
    (auxiliaryCentralPathObjective_hessian_isPositive f y0 t y hf hPos)
    (auxiliaryCentralPathObjective_hessian_isInvertible f y0 t y hf hHy)

end AuxiliaryCentralPathNewtonDecrement

open scoped AuxiliaryCentralPathNewtonDecrement

/-- The notation `λψ[f; y₀; t; y](hPos; hHy)` is exactly the Chapter 5 Newton-decrement owner
applied to the tilted objective `ψ(t; ·)`. -/
@[simp] theorem auxiliaryCentralPathNewtonDecrement_eq_newtonDecrement
    {dom : Set E} (f : E → ℝ) (y0 : dom) (t : ℝ)
    (y : E) (hf : ContDiffAt ℝ 2 f y)
    (hPos : (hessian f y).IsPositive) (hHy : (hessian f y).det ≠ 0) :
    λψ[f; y0; t; y](hf; hPos; hHy) =
      newtonDecrement (auxiliaryCentralPathObjective f y0 t) y
        (auxiliaryCentralPathObjective_hessian_isPositive f y0 t y hf hPos)
        (auxiliaryCentralPathObjective_hessian_isInvertible f y0 t y hf hHy) := by
  rfl

/-- Expanding `λψ[f; y₀; t; y](hPos; hHy)` through the tilted-objective Newton-decrement owner
gives the inverse-Hessian pairing formula for the shifted gradient of `ψ(t; ·)`. -/
@[simp] theorem auxiliaryCentralPathNewtonDecrement_def
    {dom : Set E} (f : E → ℝ) (y0 : dom) (t : ℝ)
    (y : E) (hf : ContDiffAt ℝ 2 f y)
    (hPos : (hessian f y).IsPositive) (hHy : (hessian f y).det ≠ 0) :
    λψ[f; y0; t; y](hf; hPos; hHy) =
      Real.sqrt
        (inner ℝ (∇ f y - (t : ℝ) • ∇ f (y0 : E))
          ((hessian f y).inverse (∇ f y - (t : ℝ) • ∇ f (y0 : E)))) := by
  have hdiff : DifferentiableAt ℝ f y := hf.differentiableAt (by norm_num)
  -- Expand the tilted-objective Newton decrement and then rewrite its gradient and Hessian data.
  rw [auxiliaryCentralPathNewtonDecrement_eq_newtonDecrement f y0 t y hf hPos hHy]
  rw [newtonDecrement_def]
  rw [auxiliaryCentralPathObjective_gradient_eq f y0 t y hdiff]
  rw [auxiliaryCentralPathObjective_hessian_eq f y0 t y hf]

/-- Definition 5.2.4: the source-facing tilted-objective Newton decrement agrees with the
determinant bridge `HessianDualLocalNorm.ofDetNeZero` applied to the shifted gradient covector. -/
@[simp] theorem auxiliaryCentralPathNewtonDecrement_eq_ofDetNeZero
    {dom : Set E} (f : E → ℝ) (y0 : dom) (t : ℝ)
    (y : E) (hf : ContDiffAt ℝ 2 f y)
    (hPos : (hessian f y).IsPositive) (hHy : (hessian f y).det ≠ 0) :
    λψ[f; y0; t; y](hf; hPos; hHy) =
      HessianDualLocalNorm.ofDetNeZero f y hPos hHy
        ((toDual ℝ E) (∇ f y - (t : ℝ) • ∇ f (y0 : E))) := by
  -- Normalize both owners to the same inverse-Hessian pairing formula.
  rw [auxiliaryCentralPathNewtonDecrement_def f y0 t y hf hPos hHy]
  rw [HessianDualLocalNorm.ofDetNeZero_def]
  congr 1
  simp [InnerProductSpace.toDual_apply_apply, inner_sub_left, real_inner_smul_left]

end

end
