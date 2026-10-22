/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.InnerProductSpace.ProdL2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_6_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_6_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u v w

variable {E₁ : Type u} {E₂ : Type v} {E₃ : Type w}

/- Theorem 5.4.6.5 lies in the chapter's composed directional-differentiation domain.

Sampled owner declarations:
* `secondDirectionalDerivative` from `Definition_5_0_10`, the chapter owner for scalar second
  directional derivatives;
* `vectorSecondDirectionalDerivative` from `Definition_5_4_6_2`, the chapter owner for
  `D²ξ(x)[d, d]`;
* `hessian` from `Chap01/Definition_1_4_16`, the canonical Hessian owner;
* `compositionPotential` from `Definition_5_4_6_6`, the source-facing owner for
  `ψ(x, z) = Φ(ξ(x), z)`.

Source/core/bridge triage:
* source-facing: the decomposition `Δ₂ = σ₁ + σ₂` for `ψ(x, z) = Φ(ξ(x), z)`;
* core/canonical: `secondDirectionalDerivative`, `vectorSecondDirectionalDerivative`, and
  `hessian`;
* bridge/view: the fixed-`z` slice `fun x' ↦ compositionPotential Φ ξ (x', z)` together with the
  canonical lifted pair `(fderiv ℝ ξ x d, 0)`.

Primitive data:
* `Φ`, `ξ`, `x`, `z`, `d`.

Derived API:
* the Hessian term `compositionPotentialSigmaOne`;
* the mixed term `compositionPotentialSigmaTwo`.

The previous raw `iteratedFDeriv` duplicate for `Δ₂` is deleted in favor of the chapter owner
`secondDirectionalDerivative`, and the mixed term now reuses
`vectorSecondDirectionalDerivative` instead of repeating its defining formula. The ambient
product-space calculus is taken in the canonical coordinatewise `L²` structure induced from `E₂`
and `E₃`, so the source directions `(u, 0)` and frozen-`z` slices are literal product
constructions rather than artifacts of an arbitrary unrelated Hilbert structure. -/

section SigmaOne

variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]
variable [NormedAddCommGroup E₃] [InnerProductSpace ℝ E₃] [CompleteSpace E₃]

noncomputable local instance instLocalChap05_Theorem_5_4_6_51 : SeminormedAddCommGroup (E₂ × E₃) :=
  WithLp.seminormedAddCommGroupToProd 2 E₂ E₃

noncomputable local instance instLocalChap05_Theorem_5_4_6_52 : NormedAddCommGroup (E₂ × E₃) :=
  WithLp.normedAddCommGroupToProd 2 E₂ E₃

noncomputable local instance instLocalChap05_Theorem_5_4_6_53 : NormedSpace ℝ (E₂ × E₃) :=
  WithLp.normedSpaceSeminormedAddCommGroupToProd 2 E₂ E₃

noncomputable local instance instInnerProductSpaceChap05_Theorem_5_4_6_51 : InnerProductSpace ℝ (E₂ × E₃) where
  inner x y := inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  norm_sq_eq_re_inner x := by
    rw [WithLp.norm_seminormedAddCommGroupToProd 2 E₂ E₃ x]
    exact InnerProductSpace.norm_sq_eq_re_inner (WithLp.toLp 2 x)
  conj_inner_symm x y := by
    change inner ℝ (WithLp.toLp 2 y) (WithLp.toLp 2 x) =
      inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simpa using real_inner_comm (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  add_left x y z := by
    change inner ℝ (WithLp.toLp 2 x + WithLp.toLp 2 y) (WithLp.toLp 2 z) =
      inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 z) +
        inner ℝ (WithLp.toLp 2 y) (WithLp.toLp 2 z)
    simpa using inner_add_left (WithLp.toLp 2 x) (WithLp.toLp 2 y) (WithLp.toLp 2 z)
  smul_left x y r := by
    change inner ℝ (r • WithLp.toLp 2 x) (WithLp.toLp 2 y) =
      r * inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simpa using real_inner_smul_left (WithLp.toLp 2 x) (WithLp.toLp 2 y) r

noncomputable local instance instLocalChap05_Theorem_5_4_6_54 : CompleteSpace (E₂ × E₃) := inferInstance

/-- The Hessian quadratic term `σ₁ = ⟪∇² Φ(ξ(x), z) l, l⟫` in the decomposition of `Δ₂`. -/
abbrev compositionPotentialSigmaOne
    (Φ : E₂ × E₃ → ℝ) (ξ : E₁ → E₂) (x : E₁) (z : E₃) (d : E₁) : ℝ :=
  let l : E₂ × E₃ := (fderiv ℝ ξ x d, 0)
  inner ℝ l (hessian Φ (ξ x, z) l)

-- Proof sketch: unfold `compositionPotentialSigmaOne`.
/-- Expanding `compositionPotentialSigmaOne Φ ξ x z d` gives the Hessian quadratic form of `Φ`
at `(ξ(x), z)` in the lifted direction `l = (Dξ(x)[d], 0)`. -/
theorem compositionPotentialSigmaOne_def
    (Φ : E₂ × E₃ → ℝ) (ξ : E₁ → E₂) (x : E₁) (z : E₃) (d : E₁) :
    compositionPotentialSigmaOne Φ ξ x z d =
      inner ℝ (fderiv ℝ ξ x d, (0 : E₃))
        (hessian Φ (ξ x, z) (fderiv ℝ ξ x d, (0 : E₃))) :=
  rfl

end SigmaOne

section SigmaTwo

variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]

/-- The mixed term `σ₂ = ⟪∇ᵧ Φ(ξ(x), z), D²ξ(x)[d, d]⟫` in the decomposition of `Δ₂`. -/
abbrev compositionPotentialSigmaTwo
    (Φ : E₂ × E₃ → ℝ) (ξ : E₁ → E₂) (x : E₁) (z : E₃) (d : E₁) : ℝ :=
  inner ℝ (∇ (fun y : E₂ ↦ Φ (y, z)) (ξ x))
    (vectorSecondDirectionalDerivative ξ x d)

-- Proof sketch: unfold `compositionPotentialSigmaTwo`.
/-- Expanding `compositionPotentialSigmaTwo Φ ξ x z d` gives the pairing of the `y`-gradient of
`Φ` with the second directional derivative `D²ξ(x)[d, d]`. -/
theorem compositionPotentialSigmaTwo_def
    (Φ : E₂ × E₃ → ℝ) (ξ : E₁ → E₂) (x : E₁) (z : E₃) (d : E₁) :
    compositionPotentialSigmaTwo Φ ξ x z d =
      inner ℝ (∇ (fun y : E₂ ↦ Φ (y, z)) (ξ x))
        (vectorSecondDirectionalDerivative ξ x d) :=
  rfl

end SigmaTwo

section MainTheorem

variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]
variable [NormedAddCommGroup E₃] [InnerProductSpace ℝ E₃] [CompleteSpace E₃]

noncomputable local instance instLocalChap05_Theorem_5_4_6_55 : SeminormedAddCommGroup (E₂ × E₃) :=
  WithLp.seminormedAddCommGroupToProd 2 E₂ E₃

noncomputable local instance instLocalChap05_Theorem_5_4_6_56 : NormedAddCommGroup (E₂ × E₃) :=
  WithLp.normedAddCommGroupToProd 2 E₂ E₃

noncomputable local instance instLocalChap05_Theorem_5_4_6_57 : NormedSpace ℝ (E₂ × E₃) :=
  WithLp.normedSpaceSeminormedAddCommGroupToProd 2 E₂ E₃

noncomputable local instance instInnerProductSpaceChap05_Theorem_5_4_6_52 : InnerProductSpace ℝ (E₂ × E₃) where
  inner x y := inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  norm_sq_eq_re_inner x := by
    rw [WithLp.norm_seminormedAddCommGroupToProd 2 E₂ E₃ x]
    exact InnerProductSpace.norm_sq_eq_re_inner (WithLp.toLp 2 x)
  conj_inner_symm x y := by
    change inner ℝ (WithLp.toLp 2 y) (WithLp.toLp 2 x) =
      inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simpa using real_inner_comm (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  add_left x y z := by
    change inner ℝ (WithLp.toLp 2 x + WithLp.toLp 2 y) (WithLp.toLp 2 z) =
      inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 z) +
        inner ℝ (WithLp.toLp 2 y) (WithLp.toLp 2 z)
    simpa using inner_add_left (WithLp.toLp 2 x) (WithLp.toLp 2 y) (WithLp.toLp 2 z)
  smul_left x y r := by
    change inner ℝ (r • WithLp.toLp 2 x) (WithLp.toLp 2 y) =
      r * inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simpa using real_inner_smul_left (WithLp.toLp 2 x) (WithLp.toLp 2 y) r

noncomputable local instance instLocalChap05_Theorem_5_4_6_58 : CompleteSpace (E₂ × E₃) := inferInstance

/-- Helper for Theorem 5.4.6.5: the affine line `s ↦ x + s • d` has derivative `d`. -/
private theorem affineLineHasDerivAt
    (x d : E₁) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ x + s • d) d t := by
  -- Differentiate scalar multiplication and then translate by the base point.
  simpa [one_smul] using ((hasDerivAt_id t).smul_const d).const_add x

/-- Helper for Theorem 5.4.6.5: the affine line has vanishing second iterated derivative. -/
private theorem affineLineIteratedDerivTwo
    (x d : E₁) :
    iteratedDeriv 2 (fun s : ℝ ↦ x + s • d) = fun _ : ℝ ↦ (0 : E₁) := by
  -- Differentiate the affine line once to a constant, then differentiate that constant again.
  funext t
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hderiv : deriv (fun s : ℝ ↦ x + s • d) = fun _ : ℝ ↦ d := by
    funext s
    exact (affineLineHasDerivAt x d s).deriv
  rw [hderiv, deriv_const]

/-- Helper for Theorem 5.4.6.5: differentiating the line slice of `ξ` twice recovers
`D²ξ(x)[d, d]`. -/
private theorem lineSliceIteratedDerivTwoEqVectorSecondDirectionalDerivative
    (ξ : E₁ → E₂) (x d : E₁) (hξ : ContDiffAt ℝ 2 ξ x) :
    iteratedDeriv 2 (fun s : ℝ ↦ ξ (x + s • d)) 0 =
      vectorSecondDirectionalDerivative ξ x d := by
  let line : ℝ → E₁ := fun s ↦ x + s • d
  have hline₂ : ContDiffAt ℝ 2 line 0 := by
    fun_prop
  -- Apply the one-dimensional quadratic chain rule to `ξ ∘ line`.
  have hcomp :
      iteratedDeriv 2 (ξ ∘ line) 0 =
        (iteratedFDeriv ℝ 2 ξ (line 0)) (fun _ ↦ deriv line 0) +
          (fderiv ℝ ξ (line 0)) (iteratedDeriv 2 line 0) := by
    simpa [line] using (iteratedDeriv_vcomp_two (by simpa [line] using hξ) hline₂)
  have hline_deriv : deriv line 0 = d := by
    simpa [line] using (affineLineHasDerivAt x d 0).deriv
  simpa [line, Function.comp, hline_deriv, affineLineIteratedDerivTwo,
    vectorSecondDirectionalDerivative] using hcomp

/-- Helper for Theorem 5.4.6.5: a `C²` scalar field on a real Hilbert space has a differentiable
gradient because the gradient is the Fréchet derivative transported through the Riesz
isomorphism. -/
private theorem differentiableAt_gradient_of_contDiffAt_two
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {f : F → ℝ} {y : F} (hf : ContDiffAt ℝ 2 f y) :
    DifferentiableAt ℝ (∇ f) y := by
  -- Rewrite the gradient through the Riesz map so differentiability reduces to that of `fderiv`.
  let D : StrongDual ℝ F →L[ℝ] F :=
    (InnerProductSpace.toDual ℝ F).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ f) y := by
    exact
      (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))).differentiableAt
        one_ne_zero
  change DifferentiableAt ℝ (fun y' ↦ D (fderiv ℝ f y')) y
  exact (D.hasFDerivAt.comp y hfdiff.hasFDerivAt).differentiableAt

/-- Helper for Theorem 5.4.6.5: the first derivative of the source line slice is the directional
derivative `Dξ(x)[d]`. -/
private theorem lineSliceDeriv_eq_fderiv
    (ξ : E₁ → E₂) (x d : E₁) (hξ : ContDiffAt ℝ 2 ξ x) :
    deriv (fun s : ℝ ↦ ξ (x + s • d)) 0 = fderiv ℝ ξ x d := by
  have hline : HasDerivAt (fun s : ℝ ↦ x + s • d) d 0 := by
    -- The affine line contributes the fixed direction `d`.
    simpa using affineLineHasDerivAt x d 0
  have hξdiff : DifferentiableAt ℝ ξ x := hξ.differentiableAt (by norm_num)
  have hcomp :
      HasDerivAt (fun s : ℝ ↦ ξ (x + s • d)) (fderiv ℝ ξ x d) 0 := by
    -- Compose the derivative of `ξ` at `x` with the derivative of the affine line at `0`.
    simpa using hξdiff.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  exact hcomp.deriv

/-- Helper for Theorem 5.4.6.5: for scalar maps, the repeated second Fréchet derivative agrees
with the scalar second directional derivative. -/
private theorem vectorSecondDirectionalDerivative_eq_secondDirectionalDerivative
    {f : E₂ → ℝ} {y u : E₂} (hf : ContDiffAt ℝ 2 f y) :
    iteratedFDeriv ℝ 2 f y (fun _ ↦ u) = secondDirectionalDerivative f y u := by
  -- Compare both owners through the same affine line slice at `y` in direction `u`.
  rw [secondDirectionalDerivative]
  symm
  simpa [directionalSlice, vectorSecondDirectionalDerivative] using
    (lineSliceIteratedDerivTwoEqVectorSecondDirectionalDerivative f y u hf)

/-- Helper for Theorem 5.4.6.5: freezing `z` turns the left slice of `Φ` into the ambient second
directional derivative along `(u, 0)`. -/
private theorem leftSliceSecondDirectionalDerivative_eq_ambient
    {Φ : E₂ × E₃ → ℝ} {y u : E₂} {z : E₃} :
    secondDirectionalDerivative (fun y' : E₂ ↦ Φ (y', z)) y u =
      secondDirectionalDerivative Φ (y, z) (u, (0 : E₃)) := by
  -- Both second directional derivatives differentiate the same affine line after freezing `z`.
  rw [secondDirectionalDerivative, secondDirectionalDerivative]
  congr 1
  funext t
  simp [directionalSlice]

/-- Helper for Theorem 5.4.6.5: the ambient second directional derivative of `Φ` is the Hessian
quadratic form in the lifted direction. -/
private theorem ambientSecondDirectionalDerivative_eq_hessianQuadratic
    {Φ : E₂ × E₃ → ℝ} {p u : E₂ × E₃}
    (hΦ : ContDiffAt ℝ 2 Φ p) :
    secondDirectionalDerivative Φ p u = inner ℝ u (hessian Φ p u) := by
  -- Convert the `C²` hypothesis into the differentiability assumptions required by the Hessian
  -- quadratic-form owner theorem.
  have hdiff : DifferentiableAt ℝ Φ p := hΦ.differentiableAt (by norm_num)
  have hgrad : DifferentiableAt ℝ (∇ Φ) p :=
    differentiableAt_gradient_of_contDiffAt_two hΦ
  simpa using secondDirectionalDerivative_eq_hessian_quadratic_form hΦ

/-- Helper for Theorem 5.4.6.5: ambient `C²` regularity of `Φ` transfers to the fixed-`z`
left slice `y' ↦ Φ (y', z)`. -/
private theorem fixedZSliceContDiffAtTwo
    {Φ : E₂ × E₃ → ℝ} {y : E₂} {z : E₃}
    (hΦ : ContDiffAt ℝ 2 Φ (y, z)) :
    ContDiffAt ℝ 2 (fun y' : E₂ ↦ Φ (y', z)) y := by
  let inl : E₂ →L[ℝ] E₂ × E₃ := ContinuousLinearMap.inl ℝ E₂ E₃
  have hembed : ContDiffAt ℝ 2 (fun y' : E₂ ↦ inl y' + ((0 : E₂), z)) y := by
    -- The fixed-`z` embedding is affine-linear in `y`.
    exact inl.contDiff.contDiffAt.add contDiffAt_const
  have hΦ_embed : ContDiffAt ℝ 2 Φ (inl y + ((0 : E₂), z)) := by
    simpa [inl] using hΦ
  -- Compose `Φ` with the affine embedding `y' ↦ (y', z)`.
  simpa [inl, Function.comp] using ContDiffAt.comp (x := y) hΦ_embed hembed

-- Proof sketch: differentiate the fixed-`z` slice `x' ↦ compositionPotential Φ ξ (x', z)` along
-- the repeated direction `d`. The ambient `C²` regularity of `Φ` at `(ξ x, z)` supplies the
-- gradient and Hessian terms from the source statement, while the chain rule produces the
-- Hessian quadratic term in the lifted direction `l = (Dξ(x)[d], 0)` and the pairing of the
-- `y`-gradient of `Φ` with `D²ξ(x)[d, d]`; the `z`-component contributes nothing because it is
-- constantly zero.
/-- Theorem 5.4.6.5: if `ξ` is `C²` at `x` and `Φ` is `C²` at `(ξ(x), z)`, then for
`ψ(x, z) = Φ(ξ(x), z)`,
`Δ₂ = D² (fun x' ↦ compositionPotential Φ ξ (x', z))(x)[d, d]`,
`σ₁ = ⟪∇² Φ(ξ(x), z) l, l⟫` with `l = (Dξ(x)[d], 0)`,
and `σ₂ = ⟪∇ᵧ Φ(ξ(x), z), D²ξ(x)[d, d]⟫`,
the decomposition `(5.4.24)` reads `Δ₂ = σ₁ + σ₂`. -/
theorem compositionPotential_secondDirectionalDerivative_eq_sigmaOne_add_sigmaTwo
    {Φ : E₂ × E₃ → ℝ} {ξ : E₁ → E₂} {x d : E₁} {z : E₃}
    (hξ : ContDiffAt ℝ 2 ξ x)
    (hΦ : ContDiffAt ℝ 2 Φ (ξ x, z)) :
    secondDirectionalDerivative (fun x' : E₁ ↦ compositionPotential Φ ξ (x', z)) x d =
      compositionPotentialSigmaOne Φ ξ x z d +
        compositionPotentialSigmaTwo Φ ξ x z d := by
  let g : E₂ → ℝ := fun y ↦ Φ (y, z)
  let line : ℝ → E₁ := fun s ↦ x + s • d
  let slice : ℝ → E₂ := fun s ↦ ξ (line s)
  have hg₂ : ContDiffAt ℝ 2 g (ξ x) := by
    -- Freeze `z` first so the outer scalar map is a `C²` function on `E₂`.
    simpa [g] using fixedZSliceContDiffAtTwo (Φ := Φ) (y := ξ x) (z := z) hΦ
  have hline₂ : ContDiffAt ℝ 2 line 0 := by
    -- The affine source line is smooth.
    fun_prop
  have hslice₂ : ContDiffAt ℝ 2 slice 0 := by
    -- Compose `ξ` with the affine line to obtain the one-variable slice used in the chain rule.
    have hξ_line : ContDiffAt ℝ 2 ξ (line 0) := by
      simpa [line] using hξ
    simpa [slice, Function.comp] using ContDiffAt.comp (x := 0) hξ_line hline₂
  have hchain :
      iteratedDeriv 2 (g ∘ slice) 0 =
        iteratedFDeriv ℝ 2 g (slice 0) (fun _ ↦ deriv slice 0) +
          fderiv ℝ g (slice 0) (iteratedDeriv 2 slice 0) := by
    -- Apply the quadratic one-variable chain rule to `g ∘ slice`.
    have hg₂_slice : ContDiffAt ℝ 2 g (slice 0) := by
      simpa [slice, line] using hg₂
    exact iteratedDeriv_vcomp_two hg₂_slice hslice₂
  have hslice_deriv : deriv slice 0 = fderiv ℝ ξ x d := by
    -- The first derivative of the source slice is the directional derivative `Dξ(x)[d]`.
    simpa [slice, line] using lineSliceDeriv_eq_fderiv ξ x d hξ
  have hslice_second :
      iteratedDeriv 2 slice 0 = vectorSecondDirectionalDerivative ξ x d := by
    -- The second derivative of the source slice is the packaged vector second directional
    -- derivative `D²ξ(x)[d, d]`.
    simpa [slice, line] using
      lineSliceIteratedDerivTwoEqVectorSecondDirectionalDerivative ξ x d hξ
  have hgdiff : DifferentiableAt ℝ g (ξ x) := hg₂.differentiableAt (by norm_num)
  -- Route correction: use the fixed-`z` slice `g : E₂ → ℝ` as the outer map, then translate the
  -- resulting quadratic term back to the ambient product space only after the chain rule.
  calc
    secondDirectionalDerivative (fun x' : E₁ ↦ compositionPotential Φ ξ (x', z)) x d
      = iteratedDeriv 2 (g ∘ slice) 0 := by
          -- Normalize the source-facing directional slice to the one-variable composition
          -- `s ↦ g (ξ (x + s • d))`.
          rw [secondDirectionalDerivative]
          congr 1
    _ =
        iteratedFDeriv ℝ 2 g (slice 0) (fun _ ↦ deriv slice 0) +
          fderiv ℝ g (slice 0) (iteratedDeriv 2 slice 0) := hchain
    _ =
        iteratedFDeriv ℝ 2 g (ξ x) (fun _ ↦ fderiv ℝ ξ x d) +
          fderiv ℝ g (ξ x) (vectorSecondDirectionalDerivative ξ x d) := by
            -- Substitute the first and second derivatives of the source slice, then rewrite the
            -- evaluation point `slice 0` back to `ξ x`.
            rw [hslice_deriv, hslice_second]
            simp [slice, line]
    _ =
        secondDirectionalDerivative g (ξ x) (fderiv ℝ ξ x d) +
          fderiv ℝ g (ξ x) (vectorSecondDirectionalDerivative ξ x d) := by
            -- The outer second Fréchet derivative is the scalar second directional derivative.
            rw [vectorSecondDirectionalDerivative_eq_secondDirectionalDerivative
              (f := g) (y := ξ x) (u := fderiv ℝ ξ x d) hg₂]
    _ =
        secondDirectionalDerivative g (ξ x) (fderiv ℝ ξ x d) +
          inner ℝ (∇ g (ξ x)) (vectorSecondDirectionalDerivative ξ x d) := by
            -- Identify the remaining first-derivative term with the gradient pairing.
            rw [← inner_gradient_left (y := vectorSecondDirectionalDerivative ξ x d) hgdiff]
    _ =
        secondDirectionalDerivative Φ (ξ x, z) (fderiv ℝ ξ x d, (0 : E₃)) +
          inner ℝ (∇ g (ξ x)) (vectorSecondDirectionalDerivative ξ x d) := by
            -- Re-express the slice second directional derivative as the ambient one in direction
            -- `(Dξ(x)[d], 0)`.
            rw [show secondDirectionalDerivative g (ξ x) (fderiv ℝ ξ x d) =
                secondDirectionalDerivative Φ (ξ x, z) (fderiv ℝ ξ x d, (0 : E₃)) by
                  simpa [g] using
                    leftSliceSecondDirectionalDerivative_eq_ambient
                      (Φ := Φ) (y := ξ x) (u := fderiv ℝ ξ x d) (z := z)]
    _ =
        inner ℝ (fderiv ℝ ξ x d, (0 : E₃))
          (hessian Φ (ξ x, z) (fderiv ℝ ξ x d, (0 : E₃))) +
            inner ℝ (∇ g (ξ x)) (vectorSecondDirectionalDerivative ξ x d) := by
              -- The ambient second directional derivative is the Hessian quadratic form.
              rw [ambientSecondDirectionalDerivative_eq_hessianQuadratic
                (Φ := Φ) (p := (ξ x, z)) (u := (fderiv ℝ ξ x d, (0 : E₃))) hΦ]
    _ =
        compositionPotentialSigmaOne Φ ξ x z d +
          compositionPotentialSigmaTwo Φ ξ x z d := by
            -- Package the two summands back into the source-facing `σ₁` and `σ₂` owners.
            simp [g, compositionPotentialSigmaOne_def, compositionPotentialSigmaTwo_def]

end MainTheorem

end
