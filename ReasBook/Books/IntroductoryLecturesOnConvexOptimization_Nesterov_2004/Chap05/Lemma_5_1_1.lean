/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient HessianLocalNorm

noncomputable section

universe u v

/- Lemma 5.1.1 is the affine-precomposition bridge for the Chapter 5 self-concordance data.

Primary domain:
- affine pullbacks in the Chapter 5 self-concordance / differential-calculus layer

Sampled owner-style declarations in this domain:
- `hessian`
- `hessianLocalNorm`
- `secondDirectionalDerivative_eq_hessian_quadratic_form`
- `thirdDirectionalDerivative`
- `ContinuousAffineMap`
- `IsSelfConcordantOnWith`

Source/core/bridge triage:
- source-facing: the Chapter 5.1 affine change-of-variables formulas
- core/canonical: the continuous affine pullback `g : E →ᴬ[ℝ] E₁` together with `hessian`,
  `thirdDirectionalDerivative`, and the Chapter 5 local-norm owner from `Definition_5_1_1`
- bridge/view: the textbook presentation `x ↦ A x + b`, recovered from
  `A.toContinuousAffineMap + ContinuousAffineMap.const ℝ E b`

Primitive data:
- the objective `f`
- the continuous affine map `g`
- the Hessian operator and third Fréchet derivative

Derived API:
- the linear part `g.contLinear`
- `‖u‖[f; x]`
- the self-concordance transfer theorem proved downstream in `Theorem_5_1_2`

This file therefore records only the affine-precomposition identities for the Chapter 5 owner
data, reusing the existing upstream owners instead of introducing another parallel wrapper API.
The previous `(A, b)` surface was too low-level for the Fréchet-calculus owners `hessian` and
`hessianLocalNorm`, because those identities are naturally statements about continuous affine
pullbacks. The textbook `A x + b` presentation is a thin view of this owner abstraction rather
than the primitive public data. -/

private theorem directionalSlice_comp_affine
    {E : Type u} {E₁ : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    (f : E₁ → ℝ) (g : E →ᴬ[ℝ] E₁) (x u : E) :
    directionalSlice (f ∘ g) x u = directionalSlice f (g x) (g.contLinear u) := by
  funext t
  simpa [directionalSlice, vadd_eq_add, add_comm, add_left_comm, add_assoc] using
    congrArg f (g.map_vadd x (t • u))

section Hilbert

variable {E : Type u} {E₁ : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]

private theorem differentiableAt_gradient_of_contDiffAt_two
    {f : E₁ → ℝ} {x : E₁} (hf : ContDiffAt ℝ 2 f x) :
    DifferentiableAt ℝ (∇ f) x := by
  let D : StrongDual ℝ E₁ →L[ℝ] E₁ :=
    (InnerProductSpace.toDual ℝ E₁).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ f) x := by
    exact
      (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))).differentiableAt
        one_ne_zero
  change DifferentiableAt ℝ (fun y ↦ D (fderiv ℝ f y)) x
  exact (D.hasFDerivAt.comp x hfdiff.hasFDerivAt).differentiableAt

/-- Lemma 5.1.1, owner form: the Hessian quadratic form of a continuous affine pullback `f ∘ g` at
`x` in the direction `u` is the Hessian quadratic form of `f` at `g x` in the image direction
`g.contLinear u`, provided `f` is `C²` at `g x`. -/
theorem hessianQuadraticForm_comp_affine
    (f : E₁ → ℝ) (g : E →ᴬ[ℝ] E₁) (x u : E) (hf : ContDiffAt ℝ 2 f (g x)) :
    inner ℝ u (hessian (f ∘ g) x u) =
      inner ℝ (g.contLinear u) (hessian f (g x) (g.contLinear u)) := by
  have hcomp : ContDiffAt ℝ 2 (f ∘ g) x := hf.comp x g.contDiff.contDiffAt
  have hdiff_comp : DifferentiableAt ℝ (f ∘ g) x := hcomp.differentiableAt (by norm_num)
  have hgrad_comp : DifferentiableAt ℝ (∇ (f ∘ g)) x :=
    differentiableAt_gradient_of_contDiffAt_two hcomp
  have hdiff_f : DifferentiableAt ℝ f (g x) := hf.differentiableAt (by norm_num)
  have hgrad_f : DifferentiableAt ℝ (∇ f) (g x) :=
    differentiableAt_gradient_of_contDiffAt_two hf
  calc
    inner ℝ u (hessian (f ∘ g) x u) = secondDirectionalDerivative (f ∘ g) x u := by
      symm
      exact secondDirectionalDerivative_eq_hessian_quadratic_form hcomp
    _ = secondDirectionalDerivative f (g x) (g.contLinear u) := by
      simp [secondDirectionalDerivative, directionalSlice_comp_affine]
    _ = inner ℝ (g.contLinear u) (hessian f (g x) (g.contLinear u)) := by
      exact secondDirectionalDerivative_eq_hessian_quadratic_form hf

/-- Lemma 5.1.1, local-norm form: the Hessian local norm of a continuous affine pullback `f ∘ g`
at `x` in the direction `u` is the Hessian local norm of `f` at `g x` in the image direction
`g.contLinear u`, provided `f` is `C²` at `g x`. -/
theorem hessianLocalNorm_comp_affine
    (f : E₁ → ℝ) (g : E →ᴬ[ℝ] E₁) (x u : E) (hf : ContDiffAt ℝ 2 f (g x)) :
    ‖u‖[f ∘ g; x] = ‖g.contLinear u‖[f; g x] := by
  rw [hessianLocalNorm_def, hessianLocalNorm_def, hessianQuadraticForm_comp_affine f g x u hf]

end Hilbert

section Normed

variable {E : Type u} {E₁ : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]

/-- Lemma 5.1.1, third-derivative form: the third directional derivative of a continuous affine
pullback `f ∘ g` at `x` along `u` is the third directional derivative of `f` at `g x` along
`g.contLinear u`. -/
theorem thirdDirectionalDerivative_comp_affine
    (f : E₁ → ℝ) (g : E →ᴬ[ℝ] E₁) (x u : E) :
    thirdDirectionalDerivative (f ∘ g) x u =
      thirdDirectionalDerivative f (g x) (g.contLinear u) := by
  simp [thirdDirectionalDerivative, directionalSlice_comp_affine]

end Normed

end
