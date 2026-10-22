/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_16
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_4_19
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Lemma_4_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Lemma_4_2_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Text_4_2_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators Gradient CoordinateSubspace CoordinateSymmetricMatrixSubspace

variable {n t i : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "e" => EuclideanSpace.basisFun (Fin n) ℝ

/-- Helper for Lemma 4.3.1: away from the origin, the derivative of the norm is the normalized
inner-product functional. -/
private theorem fderiv_norm_eq_inv_smul_innerSL {x : E} (hx : x ≠ 0) :
    fderiv ℝ (fun y : E ↦ ‖y‖) x = ‖x‖⁻¹ • innerSL ℝ x := by
  have hdiff : DifferentiableAt ℝ (fun y : E ↦ ‖y‖) x :=
    DifferentiableAt.norm (𝕜 := ℝ) (f := fun y : E ↦ y) (x := x) differentiableAt_id hx
  have hsq1 :
      HasFDerivAt (fun y : E ↦ ‖y‖ * ‖y‖)
        (‖x‖ • fderiv ℝ (fun y : E ↦ ‖y‖) x + ‖x‖ • fderiv ℝ (fun y : E ↦ ‖y‖) x) x := by
    simpa using (hdiff.hasFDerivAt.mul hdiff.hasFDerivAt)
  have hsq2 :
      HasFDerivAt (fun y : E ↦ ‖y‖ * ‖y‖) (2 • innerSL ℝ x) x := by
    simpa [pow_two] using ((hasFDerivAt_id x).norm_sq)
  have heq :
      ‖x‖ • fderiv ℝ (fun y : E ↦ ‖y‖) x + ‖x‖ • fderiv ℝ (fun y : E ↦ ‖y‖) x =
        2 • innerSL ℝ x := by
    exact hsq1.unique hsq2
  ext u
  have heq_apply := congrArg (fun T : E →L[ℝ] ℝ ↦ T u) heq
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, innerSL_apply_apply]
    at heq_apply
  have hu_two :
      (2 : ℝ) * (‖x‖ * (fderiv ℝ (fun y : E ↦ ‖y‖) x) u) = 2 * inner ℝ x u := by
    simpa [two_mul, mul_assoc] using heq_apply
  have hu : ‖x‖ * (fderiv ℝ (fun y : E ↦ ‖y‖) x) u = inner ℝ x u := by
    linarith
  have hnorm0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hu' : (fderiv ℝ (fun y : E ↦ ‖y‖) x) u * ‖x‖ = inner ℝ x u := by
    simpa [mul_comm] using hu
  calc
    (fderiv ℝ (fun y : E ↦ ‖y‖) x) u = inner ℝ x u / ‖x‖ := by
      exact (eq_div_iff hnorm0).2 hu'
    _ = (‖x‖⁻¹ • innerSL ℝ x) u := by
      simp [ContinuousLinearMap.smul_apply, innerSL_apply_apply, div_eq_mul_inv, mul_comm]

/-- Helper for Lemma 4.3.1: finite sums of gradients add coordinatewise. -/
private theorem hasGradientAt_finset_sum
    {ι : Type*} (s : Finset ι) {f : ι → E → ℝ} {g : ι → E → E} {x : E}
    (hf : ∀ j ∈ s, HasGradientAt (f j) (g j x) x) :
    HasGradientAt (fun y ↦ ∑ j ∈ s, f j y) (∑ j ∈ s, g j x) x := by
  -- Convert the sum of gradients to the sum of Fréchet derivatives and back.
  have hsum :
      HasFDerivAt (fun y ↦ ∑ j ∈ s, f j y)
        (∑ j ∈ s, (InnerProductSpace.toDual ℝ E) (g j x)) x := by
    exact HasFDerivAt.fun_sum fun j hj ↦ (hf j hj).hasFDerivAt
  have hgrad :
      HasGradientAt (fun y ↦ ∑ j ∈ s, f j y)
        ((InnerProductSpace.toDual ℝ E).symm
          (∑ j ∈ s, (InnerProductSpace.toDual ℝ E) (g j x))) x := by
    exact hsum.hasGradientAt
  convert hgrad using 1
  simpa using map_sum (InnerProductSpace.toDual ℝ E).symm
    (fun j ↦ (InnerProductSpace.toDual ℝ E) (g j x)) s

/-- Helper for Lemma 4.3.1: gradients add by adding their gradient vectors. -/
private theorem hasGradientAt_add
    {f g : E → ℝ} {u v : E} {x : E}
    (hf : HasGradientAt f u x) (hg : HasGradientAt g v x) :
    HasGradientAt (fun y : E ↦ f y + g y) (u + v) x := by
  have hsum :
      HasFDerivAt (fun y : E ↦ f y + g y)
        ((InnerProductSpace.toDual ℝ E) u + (InnerProductSpace.toDual ℝ E) v) x := by
    exact hf.hasFDerivAt.add hg.hasFDerivAt
  have hgrad :
      HasGradientAt (fun y : E ↦ f y + g y)
        ((InnerProductSpace.toDual ℝ E).symm
          ((InnerProductSpace.toDual ℝ E) u + (InnerProductSpace.toDual ℝ E) v)) x := by
    exact hsum.hasGradientAt
  convert hgrad using 1
  simpa using map_add (InnerProductSpace.toDual ℝ E).symm
    ((InnerProductSpace.toDual ℝ E) u) ((InnerProductSpace.toDual ℝ E) v)

/-- Helper for Lemma 4.3.1: gradients subtract by subtracting their gradient vectors. -/
private theorem hasGradientAt_sub
    {f g : E → ℝ} {u v : E} {x : E}
    (hf : HasGradientAt f u x) (hg : HasGradientAt g v x) :
    HasGradientAt (fun y : E ↦ f y - g y) (u - v) x := by
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
  simpa using map_sub (InnerProductSpace.toDual ℝ E).symm
    ((InnerProductSpace.toDual ℝ E) u) ((InnerProductSpace.toDual ℝ E) v)

/-- Helper for Lemma 4.3.1: the Hessian of a finite sum is the sum of the Hessians when each
summand is `C²`. -/
private theorem hessian_finset_sum
    {ι : Type*} (s : Finset ι) (f : ι → E → ℝ)
    (hf : ∀ j ∈ s, ContDiff ℝ 2 (f j)) (x : E) :
    hessian (fun y ↦ ∑ j ∈ s, f j y) x =
      ∑ j ∈ s, hessian (f j) x := by
  have hgrad :
      ∇ (fun y ↦ ∑ j ∈ s, f j y) = fun y : E ↦ ∑ j ∈ s, ∇ (f j) y := by
    -- Identify the gradient of the finite sum before differentiating once more.
    refine gradient_eq ?_
    intro y
    exact
      hasGradientAt_finset_sum s fun j hj =>
        ((hf j hj).contDiffAt.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).hasGradientAt
  rw [hessian, hgrad]
  calc
    fderiv ℝ (fun y : E ↦ ∑ j ∈ s, ∇ (f j) y) x
        = ∑ j ∈ s, fderiv ℝ (fun y : E ↦ ∇ (f j) y) x := by
            exact fderiv_fun_sum fun j hj =>
              differentiableAt_gradient_of_contDiffAt_two (hf j hj).contDiffAt
    _ = ∑ j ∈ s, hessian (f j) x := by
          simp [hessian]

/-- Helper for Lemma 4.3.1: the Hessian is additive for globally `C²` scalar fields. -/
private theorem hessian_add_of_contDiff_two
    {f g : E → ℝ} {x : E} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    hessian (fun y ↦ f y + g y) x = hessian f x + hessian g x := by
  have hgrad :
      ∇ (fun y ↦ f y + g y) = fun y : E ↦ ∇ f y + ∇ g y := by
    -- Rewrite the gradient of the sum pointwise, then differentiate that identity.
    refine gradient_eq ?_
    intro y
    have hfgrad : HasGradientAt f (∇ f y) y :=
      (hf.contDiffAt.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).hasGradientAt
    have hggrad : HasGradientAt g (∇ g y) y :=
      (hg.contDiffAt.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).hasGradientAt
    rw [hasGradientAt_iff_hasFDerivAt]
    simpa using hfgrad.hasFDerivAt.add hggrad.hasFDerivAt
  rw [hessian, hgrad]
  change fderiv ℝ ((∇ f) + (∇ g)) x = hessian f x + hessian g x
  rw [fderiv_add
    (differentiableAt_gradient_of_contDiffAt_two (hf.contDiffAt (x := x)))
    (differentiableAt_gradient_of_contDiffAt_two (hg.contDiffAt (x := x)))]

/-- Helper for Lemma 4.3.1: the Hessian is subtractive for globally `C²` scalar fields. -/
private theorem hessian_sub_of_contDiff_two
    {f g : E → ℝ} {x : E} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    hessian (fun y ↦ f y - g y) x = hessian f x - hessian g x := by
  have hgrad :
      ∇ (fun y ↦ f y - g y) = fun y : E ↦ ∇ f y - ∇ g y := by
    -- Rewrite the gradient of the difference pointwise, then differentiate that identity.
    refine gradient_eq ?_
    intro y
    have hfgrad : HasGradientAt f (∇ f y) y :=
      (hf.contDiffAt.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).hasGradientAt
    have hggrad : HasGradientAt g (∇ g y) y :=
      (hg.contDiffAt.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).hasGradientAt
    rw [hasGradientAt_iff_hasFDerivAt]
    simpa using hfgrad.hasFDerivAt.sub hggrad.hasFDerivAt
  rw [hessian, hgrad]
  change fderiv ℝ ((∇ f) - (∇ g)) x = hessian f x - hessian g x
  rw [fderiv_sub
    (differentiableAt_gradient_of_contDiffAt_two (hf.contDiffAt (x := x)))
    (differentiableAt_gradient_of_contDiffAt_two (hg.contDiffAt (x := x)))]

/-- Helper for Lemma 4.3.1: a scalar continuous linear map has zero Hessian. -/
private theorem hessian_continuousLinearMap_eq_zero
    (A : E →L[ℝ] ℝ) (x : E) :
    hessian (fun y : E ↦ A y) x = 0 := by
  have hgrad :
      ∇ (fun y : E ↦ A y) = fun _ : E ↦ (InnerProductSpace.toDual ℝ E).symm A := by
    -- The gradient of a scalar continuous linear map is its constant Riesz representative.
    refine gradient_eq ?_
    intro y
    rw [hasGradientAt_iff_hasFDerivAt]
    convert A.hasFDerivAt using 1
    ext z
    simp
  rw [hessian, hgrad]
  ext h
  simp

/-- Helper for Lemma 4.3.1: precomposing a scalar field with a continuous linear map pulls back
its gradient by the adjoint. -/
private theorem hasGradientAt_comp_continuousLinearMap
    {m : Type*} [NormedAddCommGroup m] [InnerProductSpace ℝ m] [CompleteSpace m]
    {f : m → ℝ} (A : E →L[ℝ] m) {x : E}
    (hf : DifferentiableAt ℝ f (A x)) :
    HasGradientAt (f ∘ A) (A.adjoint (∇ f (A x))) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  -- Differentiate the scalar field after the linear map, then rewrite through the adjoint.
  have hcomp := (hf.hasGradientAt.hasFDerivAt).comp x A.hasFDerivAt
  convert hcomp using 1
  ext y
  calc
    inner ℝ (A.adjoint (∇ f (A x))) y = inner ℝ y (A.adjoint (∇ f (A x))) := by
      rw [real_inner_comm]
    _ = inner ℝ (A y) (∇ f (A x)) := A.adjoint_inner_right y (∇ f (A x))
    _ = inner ℝ (∇ f (A x)) (A y) := by
      rw [real_inner_comm]

/-- Helper for Lemma 4.3.1: away from the origin, the derivative of `z ↦ ‖z‖ • z` splits into the
identity part and the radial rank-one part. -/
private theorem hasFDerivAt_norm_smul_id {x : E} (hx : x ≠ 0) :
    HasFDerivAt (fun y : E ↦ ‖y‖ • y)
      (‖x‖ • ContinuousLinearMap.id ℝ E + (‖x‖⁻¹ • innerSL ℝ x).smulRight x) x := by
  have hdiff : DifferentiableAt ℝ (fun y : E ↦ ‖y‖) x :=
    DifferentiableAt.norm ℝ differentiableAt_id hx
  have hnorm : HasFDerivAt (fun y : E ↦ ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
    simpa [fderiv_norm_eq_inv_smul_innerSL hx] using hdiff.hasFDerivAt
  -- Apply the product rule to `‖y‖ • y`.
  simpa using hnorm.smul (hasFDerivAt_id x)

/-- Helper for Lemma 4.3.1: at the origin, `z ↦ ‖z‖ • z` has derivative `0`. -/
private theorem hasFDerivAt_norm_smul_id_zero :
    HasFDerivAt (fun y : E ↦ ‖y‖ • y) (0 : E →L[ℝ] E) 0 := by
  -- The map vanishes quadratically at the origin.
  have hbigO :
      (fun y : E ↦ ‖y‖ • y) =O[nhds (0 : E)] fun y ↦ ‖y - (0 : E)‖ ^ (2 : ℕ) := by
    refine Asymptotics.isBigO_iff'.2 ?_
    refine ⟨1, by positivity, ?_⟩
    filter_upwards with y
    simp [norm_smul, pow_two, mul_comm]
  exact hbigO.hasFDerivAt (by norm_num)

/-- Helper for Lemma 4.3.1: the cubic power-distance has the explicit gradient field
`y ↦ ‖y - x₀‖ • (y - x₀)`. -/
private theorem powerDistance_three_gradient_eq (x0 : E) :
    ∇ (powerDistance (3 : ℝ) x0) = fun y : E ↦ ‖y - x0‖ • (y - x0) := by
  -- Specialize the general power-distance gradient formula to the cubic case.
  refine gradient_eq ?_
  intro y
  simpa [show (3 : ℝ) - 2 = 1 by norm_num, Real.rpow_one] using
    hasGradientAt_powerDistance (p := (3 : ℝ)) (by norm_num) x0 y

/-- Helper for Lemma 4.3.1: translating the origin-centered zero-derivative model gives the
centered derivative model at `x₀`. -/
private theorem translated_norm_smul_id_center_comp (x0 : E) :
    HasFDerivAt (fun y : E ↦ ‖y - x0‖ • (y - x0)) (0 : E →L[ℝ] E) x0 := by
  have hsub : HasFDerivAt (fun y : E ↦ y + (-x0)) (1 : E →L[ℝ] E) x0 := by
    simpa using (hasFDerivAt_id x0).add_const (-x0)
  have houter :
      HasFDerivAt (fun y : E ↦ ‖y‖ • y) (0 : E →L[ℝ] E) ((fun y : E ↦ y + (-x0)) x0) := by
    simpa using
      (hasFDerivAt_norm_smul_id_zero :
        HasFDerivAt (fun y : E ↦ ‖y‖ • y) (0 : E →L[ℝ] E) 0)
  -- Translate the origin-centered derivative formula to the center `x₀`.
  simpa [sub_eq_add_neg, Function.comp_def] using (houter.comp x0 hsub)

/-- Helper for Lemma 4.3.1: the gradient field of the cubic power-distance has the explicit
Fréchet derivative. -/
private theorem hasFDerivAt_powerDistance_three_gradient (x0 x : E) :
    HasFDerivAt (fun y : E ↦ ‖y - x0‖ • (y - x0))
      (‖x - x0‖ • ContinuousLinearMap.id ℝ E +
        ((‖x - x0‖)⁻¹ • innerSL ℝ (x - x0)).smulRight (x - x0)) x := by
  by_cases hx : x = x0
  · -- At the center, the translated vector field lands at `0`.
    subst x
    convert translated_norm_smul_id_center_comp x0 using 1
    ext y
    simp [sub_self]
  · -- Away from the center, transport the origin-centered model through `y ↦ y - x₀`.
    have hsub : HasFDerivAt (fun y : E ↦ y - x0) (1 : E →L[ℝ] E) x := by
      simpa using (hasFDerivAt_id x).sub_const x0
    have houter :
        HasFDerivAt (fun z : E ↦ ‖z‖ • z)
          (‖x - x0‖ • ContinuousLinearMap.id ℝ E +
            ((‖x - x0‖)⁻¹ • innerSL ℝ (x - x0)).smulRight (x - x0)) (x - x0) := by
      exact hasFDerivAt_norm_smul_id (by simpa [sub_eq_zero] using hx)
    simpa [Function.comp_def] using (houter.comp x hsub)

/-- Helper for Lemma 4.3.1: the cubic power-distance has the explicit Hessian formula. -/
private theorem powerDistance_three_hessian_formula (x0 x : E) :
    hessian (powerDistance (3 : ℝ) x0) x =
      ‖x - x0‖ • ContinuousLinearMap.id ℝ E +
        ((‖x - x0‖)⁻¹ • innerSL ℝ (x - x0)).smulRight (x - x0) := by
  rw [hessian, powerDistance_three_gradient_eq x0]
  -- Differentiate the explicit gradient model.
  exact (hasFDerivAt_powerDistance_three_gradient x0 x).fderiv

/-- Helper for Lemma 4.3.1: the scalar cubic `t ↦ (1 / 3) |t|^3`. -/
private abbrev scalarCubic : ℝ → ℝ :=
  powerDistance (3 : ℝ) (0 : ℝ)

/-- Helper for Lemma 4.3.1: the scalar cubic has the textbook formula. -/
private theorem scalarCubic_apply (s : ℝ) :
    scalarCubic s = (1 / 3 : ℝ) * |s| ^ (3 : ℕ) := by
  simp [scalarCubic, powerDistance]

/-- Helper for Lemma 4.3.1: the scalar field `s ↦ s * |s|` has derivative `2 |s|`. -/
private theorem hasDerivAt_scalarMulAbs (s : ℝ) :
    HasDerivAt (fun y : ℝ ↦ y * |y|) (2 * |s|) s := by
  by_cases hs : s = 0
  · subst hs
    -- Reuse the established zero-derivative model for `t ↦ t * |t|`.
    simpa using t_mul_abs_hasDerivAt_zero
  · rcases lt_or_gt_of_ne hs with hsneg | hspos
    · have habs : HasDerivAt (fun y : ℝ ↦ |y|) (-1) s := hasDerivAt_abs_neg hsneg
      -- On the negative side, `|s| = -s`, so the product rule gives `-2s = 2 |s|`.
      simpa [abs_of_neg hsneg, two_mul, mul_add, add_assoc, add_left_comm, add_comm] using
        (hasDerivAt_id s).mul habs
    · have habs : HasDerivAt (fun y : ℝ ↦ |y|) 1 s := hasDerivAt_abs_pos hspos
      -- On the positive side, `|s| = s`, so the product rule gives `2s = 2 |s|`.
      simpa [abs_of_pos hspos, two_mul, mul_add, add_assoc, add_left_comm, add_comm] using
        (hasDerivAt_id s).mul habs

/-- Helper for Lemma 4.3.1: the scalar cubic is `C²`. -/
private theorem scalarCubic_contDiff_two :
    ContDiff ℝ 2 scalarCubic := by
  -- Reuse the earlier cubic power-distance `C²` owner specialized to `ℝ` and center `0`.
  simpa [scalarCubic] using
    (powerDistance_three_zero_mem_C22 (E := ℝ)).contDiff

/-- Helper for Lemma 4.3.1: the scalar cubic gradient is `s ↦ s * |s|`. -/
private theorem scalarCubic_gradient_eq :
    ∇ scalarCubic = fun s : ℝ ↦ s * |s| := by
  refine gradient_eq ?_
  intro s
  simpa [scalarCubic, show (3 : ℝ) - 2 = 1 by norm_num, Real.rpow_one, Real.norm_eq_abs,
    sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using
    hasGradientAt_powerDistance (p := (3 : ℝ)) (by norm_num) (0 : ℝ) s

/-- Helper for Lemma 4.3.1: the scalar cubic Hessian on `ℝ` is multiplication by `2 |s|`. -/
private theorem scalarCubic_hessian_eq (s : ℝ) :
    hessian scalarCubic s = (2 * |s|) • ContinuousLinearMap.id ℝ ℝ := by
  have hderiv :
      fderiv ℝ (fun y : ℝ ↦ y * |y|) s = (2 * |s|) • ContinuousLinearMap.id ℝ ℝ := by
    -- Convert the scalar derivative into the corresponding Fréchet derivative.
    convert (hasDerivAt_scalarMulAbs s).hasFDerivAt.fderiv using 1
    ext y
    simp [ContinuousLinearMap.smul_apply]
  rw [hessian, scalarCubic_gradient_eq]
  -- Differentiate the explicit gradient field.
  exact hderiv

/-- Helper for Lemma 4.3.1: composing the scalar cubic with a scalar linear feature gives the
pulled-back gradient formula. -/
private theorem scalarCubicFeature_hasGradientAt
    (A : E →L[ℝ] ℝ) (x : E) :
    HasGradientAt (fun y : E ↦ scalarCubic (A y))
      (A.adjoint ((A x) * |A x|)) x := by
  have hdiff : DifferentiableAt ℝ scalarCubic (A x) := by
    simpa [scalarCubic, Real.norm_eq_abs, sub_eq_add_neg] using
      (hasGradientAt_powerDistance (p := (3 : ℝ)) (by norm_num) (0 : ℝ) (A x)).differentiableAt
  -- Pull back the scalar cubic gradient through the linear feature.
  have hcomp :=
    hasGradientAt_comp_continuousLinearMap (A := A) (f := scalarCubic) hdiff
  have hgrad : ∇ scalarCubic (A x) = (A x) * |A x| := by
    simpa using congrFun scalarCubic_gradient_eq (A x)
  simpa [Function.comp, hgrad] using hcomp

/-- Helper for Lemma 4.3.1: the explicit feature-gradient field differentiates to the expected
rank-one operator. -/
private theorem hasFDerivAt_featureGradientField
    (A : E →L[ℝ] ℝ) (x : E) :
    HasFDerivAt (fun y : E ↦ A.adjoint ((A y) * |A y|))
      ((2 * |A x|) • (A.adjoint.comp A)) x := by
  have hscalar :
      HasFDerivAt (fun y : E ↦ (A y) * |A y|) ((2 * |A x|) • A) x := by
    -- Differentiate the scalar profile first, then transport it through the feature map.
    have hcomp :=
      (hasDerivAt_scalarMulAbs (A x)).hasFDerivAt.comp x A.hasFDerivAt
    convert hcomp using 1
    ext y
    simp [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, mul_comm, mul_left_comm,
      mul_assoc]
  have hadj :
      HasFDerivAt (fun y : E ↦ A.adjoint ((A y) * |A y|))
        ((A.adjoint).comp (((2 * |A x|) • A))) x := by
    -- Postcompose the scalar derivative with the adjoint linear map.
    simpa [Function.comp] using A.adjoint.hasFDerivAt.comp x hscalar
  convert hadj using 1
  ext y
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply]

/-- Helper for Lemma 4.3.1: composing the scalar cubic with a scalar linear feature gives the
rank-one Hessian formula. -/
private theorem scalarCubicFeature_hessian_eq
    (A : E →L[ℝ] ℝ) (x : E) :
    hessian (fun y : E ↦ scalarCubic (A y)) x = (2 * |A x|) • (A.adjoint.comp A) := by
  have hgrad :
      ∇ (fun y : E ↦ scalarCubic (A y)) = fun y : E ↦ A.adjoint ((A y) * |A y|) := by
    -- First rewrite the composed scalar cubic by its explicit feature gradient field.
    refine gradient_eq ?_
    intro y
    exact scalarCubicFeature_hasGradientAt A y
  rw [hessian, hgrad]
  -- Differentiate the explicit feature gradient field.
  exact (hasFDerivAt_featureGradientField A x).fderiv

/-- Helper for Lemma 4.3.1: the positive branch of `fk` keeps the first `t` coordinates inside the
ambient space. -/
private theorem fkPrefixLenLE (ht : 0 < t) (htn : t ≤ n) :
    (t - 1) + 1 ≤ n := by
  omega

/-- Helper for Lemma 4.3.1: the initial linear feature is the first prefix coordinate. -/
private def initialFeature (ht : 0 < t) (htn : t ≤ n) : E →L[ℝ] ℝ :=
  EuclideanSpace.proj (Fin.castLE (fkPrefixLenLE ht htn) (0 : Fin ((t - 1) + 1)))

/-- Helper for Lemma 4.3.1: an edge feature is one adjacent difference in the active prefix. -/
private def edgeFeature (ht : 0 < t) (htn : t ≤ n) (k : Fin (t - 1)) : E →L[ℝ] ℝ :=
  (EuclideanSpace.proj
      (Fin.castLE (fkPrefixLenLE ht htn) (Fin.castSucc k)) : E →L[ℝ] ℝ) -
    (EuclideanSpace.proj
      (Fin.castLE (fkPrefixLenLE ht htn) k.succ) : E →L[ℝ] ℝ)

/-- Helper for Lemma 4.3.1: an edge feature is the difference of two adjacent ambient
coordinates. -/
private theorem edgeFeature_apply_eq_coord_sub
    (ht : 0 < t) (htn : t ≤ n) (k : Fin (t - 1)) (x : E) :
    edgeFeature ht htn k x = x ⟨k.1, by omega⟩ - x ⟨k.1 + 1, by omega⟩ := by
  have hcastSucc :
      (Fin.castLE (fkPrefixLenLE ht htn) (Fin.castSucc k) : Fin n) = ⟨k.1, by omega⟩ := by
    ext
    simp
  have hsucc :
      (Fin.castLE (fkPrefixLenLE ht htn) k.succ : Fin n) = ⟨k.1 + 1, by omega⟩ := by
    ext
    simp
  -- Route correction: rewrite the transported prefix indices once into plain adjacent coordinates.
  simpa [edgeFeature, ContinuousLinearMap.sub_apply, EuclideanSpace.coe_proj, hcastSucc, hsucc]
    using rfl

/-- Helper for Lemma 4.3.1: the terminal feature is the last active prefix coordinate. -/
private def terminalFeature (ht : 0 < t) (htn : t ≤ n) : E →L[ℝ] ℝ :=
  EuclideanSpace.proj (Fin.castLE (fkPrefixLenLE ht htn) (Fin.last (t - 1)))

/-- Helper for Lemma 4.3.1: a tail feature is one coordinate beyond the active prefix. -/
private def tailFeature (htn : t ≤ n) (k : Fin (n - t)) : E →L[ℝ] ℝ :=
  EuclideanSpace.proj (Fin.natAdd_castLEEmb (Nat.sub_le n t) k)

/-- Helper for Lemma 4.3.1: the positive branch of `fk` is the sum of its scalar-cubic features,
its linear initial term, and its tail features. -/
private theorem fk_eq_scalarCubic_features_of_pos (ht : 0 < t) (htn : t ≤ n) :
    fk htn =
      fun x : E ↦
        (∑ k : Fin (t - 1), scalarCubic (edgeFeature ht htn k x)) +
          scalarCubic (terminalFeature ht htn x) -
          initialFeature ht htn x +
          ∑ k : Fin (n - t), scalarCubic (tailFeature htn k x) := by
  ext x
  -- Expand `fk` in the positive branch and rewrite each cubic term through `scalarCubic`.
  simp [fk_apply, ht]
  simp only [scalarCubic_apply, edgeFeature, terminalFeature, initialFeature, tailFeature,
    ContinuousLinearMap.sub_apply, EuclideanSpace.coe_proj]
  simp only [Fin.castLE_castSucc]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  simpa [one_div, add_assoc, add_left_comm, add_comm]

/-- Helper for Lemma 4.3.1: `fk htn` is `C²`. -/
private theorem fk_contDiff_two (htn : t ≤ n) :
    ContDiff ℝ 2 (fk htn) := by
  by_cases ht : 0 < t
  · let edgeTerm : Fin (t - 1) → E → ℝ := fun k z ↦ scalarCubic (edgeFeature ht htn k z)
    let terminalTerm : E → ℝ := fun z ↦ scalarCubic (terminalFeature ht htn z)
    let tailTerm : Fin (n - t) → E → ℝ := fun k z ↦ scalarCubic (tailFeature htn k z)
    have hedgeCont : ∀ k : Fin (t - 1), ContDiff ℝ 2 (edgeTerm k) := by
      intro k
      simpa [edgeTerm] using scalarCubic_contDiff_two.comp (edgeFeature ht htn k).contDiff
    have hterminalCont : ContDiff ℝ 2 terminalTerm := by
      simpa [terminalTerm] using scalarCubic_contDiff_two.comp (terminalFeature ht htn).contDiff
    have htailCont : ∀ k : Fin (n - t), ContDiff ℝ 2 (tailTerm k) := by
      intro k
      simpa [tailTerm] using scalarCubic_contDiff_two.comp (tailFeature htn k).contDiff
    have hedgeSumCont :
        ContDiff ℝ 2 (fun z : E ↦ ∑ k : Fin (t - 1), edgeTerm k z) := by
      simpa using ContDiff.sum (s := Finset.univ) fun k hk ↦ hedgeCont k
    have htailSumCont :
        ContDiff ℝ 2 (fun z : E ↦ ∑ k : Fin (n - t), tailTerm k z) := by
      simpa using ContDiff.sum (s := Finset.univ) fun k hk ↦ htailCont k
    have hinitialCont : ContDiff ℝ 2 (fun z : E ↦ initialFeature ht htn z) := by
      simpa using (initialFeature ht htn).contDiff
    rw [fk_eq_scalarCubic_features_of_pos ht htn]
    -- Assemble the feature-level `C²` regularity back into `fk`.
    simpa [edgeTerm, terminalTerm, tailTerm, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      using ((hedgeSumCont.add hterminalCont).sub hinitialCont).add htailSumCont
  · have ht0 : t = 0 := Nat.eq_zero_of_not_pos ht
    subst ht0
    let coordTerm : Fin n → E → ℝ := fun k x ↦ scalarCubic ((EuclideanSpace.proj k : E →L[ℝ] ℝ) x)
    have hcoordCont : ∀ k : Fin n, ContDiff ℝ 2 (coordTerm k) := by
      intro k
      simpa [coordTerm] using scalarCubic_contDiff_two.comp (EuclideanSpace.proj k).contDiff
    have hfkEq : fk htn = fun x : E ↦ ∑ k : Fin n, coordTerm k x := by
      ext x
      rw [fk_apply]
      simp [coordTerm, scalarCubic_apply, Finset.mul_sum]
    rw [hfkEq]
    exact ContDiff.sum (s := Finset.univ) fun k hk ↦ hcoordCont k

/-- Helper for Lemma 4.3.1: the explicit positive-branch gradient field of `fk`. -/
private def fkPositiveGradientField (ht : 0 < t) (htn : t ≤ n) : E → E :=
  fun x ↦
    (∑ k : Fin (t - 1),
        (edgeFeature ht htn k).adjoint ((edgeFeature ht htn k x) * |edgeFeature ht htn k x|)) +
      (terminalFeature ht htn).adjoint
        ((terminalFeature ht htn x) * |terminalFeature ht htn x|) -
      (initialFeature ht htn).adjoint (1 : ℝ) +
      ∑ k : Fin (n - t),
        (tailFeature htn k).adjoint ((tailFeature htn k x) * |tailFeature htn k x|)

/-- Helper for Lemma 4.3.1: the Riesz-representative gradient of a scalar linear functional is
its adjoint applied to `1`. -/
private theorem scalarLinearMapRiesz_eq_adjoint_one (A : E →L[ℝ] ℝ) :
    (InnerProductSpace.toDual ℝ E).symm A = A.adjoint (1 : ℝ) := by
  -- Compare both candidate vectors through the ambient inner product.
  apply ext_inner_right ℝ
  intro y
  rw [InnerProductSpace.toDual_symm_apply, real_inner_comm, A.adjoint_inner_right]
  calc
    A y = 1 * A y := by simp
    _ = inner ℝ 1 (A y) := by
      simpa using (RCLike.inner_apply' (1 : ℝ) (A y)).symm

/-- Helper for Lemma 4.3.1: the linear initial feature has the constant gradient
`(initialFeature ht htn).adjoint 1`. -/
private theorem hasGradientAt_initialFeature (ht : 0 < t) (htn : t ≤ n) (x : E) :
    HasGradientAt (fun y : E ↦ initialFeature ht htn y) ((initialFeature ht htn).adjoint (1 : ℝ)) x := by
  have hlinear :
      HasGradientAt (fun y : E ↦ initialFeature ht htn y)
        ((InnerProductSpace.toDual ℝ E).symm (initialFeature ht htn)) x := by
    -- Start from the canonical gradient supplied by the Fréchet derivative of the linear feature.
    exact (initialFeature ht htn).hasFDerivAt.hasGradientAt
  -- Transport the canonical Riesz gradient to the explicit adjoint vector once.
  simpa [scalarLinearMapRiesz_eq_adjoint_one] using hlinear

/-- Helper for Lemma 4.3.1: on the positive branch, the gradient of `fk` agrees with the explicit
feature-gradient field. -/
private theorem hasGradientAt_fk_of_pos (ht : 0 < t) (htn : t ≤ n) (x : E) :
    HasGradientAt (fk htn) (fkPositiveGradientField ht htn x) x := by
  let edgeTerm : Fin (t - 1) → E → ℝ := fun k y ↦ scalarCubic (edgeFeature ht htn k y)
  let edgeGrad : Fin (t - 1) → E := fun k ↦
    (edgeFeature ht htn k).adjoint ((edgeFeature ht htn k x) * |edgeFeature ht htn k x|)
  let terminalTerm : E → ℝ := fun y ↦ scalarCubic (terminalFeature ht htn y)
  let terminalGrad : E :=
    (terminalFeature ht htn).adjoint ((terminalFeature ht htn x) * |terminalFeature ht htn x|)
  let tailTerm : Fin (n - t) → E → ℝ := fun k y ↦ scalarCubic (tailFeature htn k y)
  let tailGrad : Fin (n - t) → E := fun k ↦
    (tailFeature htn k).adjoint ((tailFeature htn k x) * |tailFeature htn k x|)
  have hedgeGrad : ∀ k : Fin (t - 1), HasGradientAt (edgeTerm k) (edgeGrad k) x := by
    intro k
    -- Differentiate each adjacent-difference scalar cubic term separately.
    simpa [edgeTerm, edgeGrad] using scalarCubicFeature_hasGradientAt (edgeFeature ht htn k) x
  have hedgeSum :
      HasGradientAt (fun y : E ↦ ∑ k : Fin (t - 1), edgeTerm k y)
        (∑ k : Fin (t - 1), edgeGrad k) x := by
    -- Package the finite edge block into one gradient computation.
    simpa using
      hasGradientAt_finset_sum (s := Finset.univ) (f := edgeTerm) (g := fun k ↦ fun _ ↦ edgeGrad k)
        (x := x) fun k hk ↦ hedgeGrad k
  have hterminalGrad : HasGradientAt terminalTerm terminalGrad x := by
    -- The terminal scalar cubic feature uses the same feature-gradient formula.
    simpa [terminalTerm, terminalGrad] using
      scalarCubicFeature_hasGradientAt (terminalFeature ht htn) x
  have htailGrad : ∀ k : Fin (n - t), HasGradientAt (tailTerm k) (tailGrad k) x := by
    intro k
    -- Differentiate each tail scalar cubic term separately.
    simpa [tailTerm, tailGrad] using scalarCubicFeature_hasGradientAt (tailFeature htn k) x
  have htailSum :
      HasGradientAt (fun y : E ↦ ∑ k : Fin (n - t), tailTerm k y)
        (∑ k : Fin (n - t), tailGrad k) x := by
    -- Package the finite tail block into one gradient computation.
    simpa using
      hasGradientAt_finset_sum (s := Finset.univ) (f := tailTerm) (g := fun k ↦ fun _ ↦ tailGrad k)
        (x := x) fun k hk ↦ htailGrad k
  rw [fk_eq_scalarCubic_features_of_pos ht htn]
  change
    HasGradientAt
      (fun y : E ↦
        ((∑ k : Fin (t - 1), edgeTerm k y) + terminalTerm y - initialFeature ht htn y) +
          ∑ k : Fin (n - t), tailTerm k y)
      (((∑ k : Fin (t - 1), edgeGrad k) + terminalGrad - (initialFeature ht htn).adjoint (1 : ℝ)) +
        ∑ k : Fin (n - t), tailGrad k)
      x
  -- Assemble the feature gradients, then subtract the constant initial-feature gradient once.
  exact hasGradientAt_add
    (hasGradientAt_sub (hasGradientAt_add hedgeSum hterminalGrad)
      (hasGradientAt_initialFeature ht htn x))
    htailSum

/-- Helper for Lemma 4.3.1: the positive-branch gradient of `fk` is the explicit feature field. -/
private theorem fkGradientEqOfPos (ht : 0 < t) (htn : t ≤ n) :
    ∇ (fk htn) = fkPositiveGradientField ht htn := by
  -- Convert the pointwise gradient witnesses into the canonical owner-level equality.
  refine gradient_eq ?_
  intro x
  exact hasGradientAt_fk_of_pos ht htn x

/-- Helper for Lemma 4.3.1: the explicit positive-branch Hessian field of `fk`. -/
private def fkPositiveHessianField (ht : 0 < t) (htn : t ≤ n) (x : E) : E →L[ℝ] E :=
  (∑ k : Fin (t - 1), (2 * |edgeFeature ht htn k x|) •
      ((edgeFeature ht htn k).adjoint.comp (edgeFeature ht htn k))) +
    (2 * |terminalFeature ht htn x|) •
      ((terminalFeature ht htn).adjoint.comp (terminalFeature ht htn)) +
    ∑ k : Fin (n - t), (2 * |tailFeature htn k x|) •
      ((tailFeature htn k).adjoint.comp (tailFeature htn k))

/-- Helper for Lemma 4.3.1: the positive branch of `fk` has the explicit Hessian decomposition
into rank-one feature Hessians. -/
private theorem fk_hessian_eq_of_pos (ht : 0 < t) (htn : t ≤ n) (x : E) :
    hessian (fk htn) x = fkPositiveHessianField ht htn x := by
  let edgeTerm : Fin (t - 1) → E → ℝ := fun k y ↦ scalarCubic (edgeFeature ht htn k y)
  let terminalTerm : E → ℝ := fun y ↦ scalarCubic (terminalFeature ht htn y)
  let initialTerm : E → ℝ := fun y ↦ initialFeature ht htn y
  let tailTerm : Fin (n - t) → E → ℝ := fun k y ↦ scalarCubic (tailFeature htn k y)
  let edgeSum : E → ℝ := fun y ↦ ∑ k : Fin (t - 1), edgeTerm k y
  let tailSum : E → ℝ := fun y ↦ ∑ k : Fin (n - t), tailTerm k y
  let prefixTerm : E → ℝ := fun y ↦ edgeSum y + terminalTerm y
  let nonlinearBody : E → ℝ := fun y ↦ prefixTerm y - initialTerm y
  have hedgeCont : ∀ k : Fin (t - 1), ContDiff ℝ 2 (edgeTerm k) := by
    intro k
    -- Each edge term is a scalar cubic transported through an adjacent-difference feature.
    simpa [edgeTerm] using scalarCubic_contDiff_two.comp (edgeFeature ht htn k).contDiff
  have hterminalCont : ContDiff ℝ 2 terminalTerm := by
    -- The terminal term is the scalar cubic on the last active coordinate.
    simpa [terminalTerm] using scalarCubic_contDiff_two.comp (terminalFeature ht htn).contDiff
  have hinitialCont : ContDiff ℝ 2 initialTerm := by
    -- The initial feature is linear, hence automatically `C²`.
    simpa [initialTerm] using (initialFeature ht htn).contDiff
  have htailCont : ∀ k : Fin (n - t), ContDiff ℝ 2 (tailTerm k) := by
    intro k
    -- Each tail term is the scalar cubic transported through one tail coordinate feature.
    simpa [tailTerm] using scalarCubic_contDiff_two.comp (tailFeature htn k).contDiff
  have hedgeSumCont : ContDiff ℝ 2 edgeSum := by
    -- Package the finite edge block into a single `C²` scalar field.
    simpa [edgeSum] using ContDiff.sum (s := Finset.univ) fun k hk ↦ hedgeCont k
  have htailSumCont : ContDiff ℝ 2 tailSum := by
    -- The same finite-sum regularity handles the tail block.
    simpa [tailSum] using ContDiff.sum (s := Finset.univ) fun k hk ↦ htailCont k
  have hedgeSumHess :
      hessian edgeSum x = ∑ k : Fin (t - 1), hessian (edgeTerm k) x := by
    -- Normalize the edge Hessian block once so the later rewrites stay flat.
    simpa [edgeSum] using
      hessian_finset_sum (s := Finset.univ) (f := edgeTerm) (x := x)
        (fun k hk ↦ hedgeCont k)
  have htailSumHess :
      hessian tailSum x = ∑ k : Fin (n - t), hessian (tailTerm k) x := by
    -- Normalize the tail Hessian block in the same way.
    simpa [tailSum] using
      hessian_finset_sum (s := Finset.univ) (f := tailTerm) (x := x)
        (fun k hk ↦ htailCont k)
  have hprefixCont : ContDiff ℝ 2 prefixTerm := by
    -- The prefix block is the sum of the edge block and the terminal term.
    simpa [prefixTerm] using hedgeSumCont.add hterminalCont
  have hbodyCont : ContDiff ℝ 2 nonlinearBody := by
    -- Subtracting the linear initial term preserves `C²`.
    simpa [nonlinearBody] using hprefixCont.sub hinitialCont
  have hsplitTail :
      hessian
          (fun y : E ↦
            (∑ k : Fin (t - 1), edgeTerm k y) + terminalTerm y - initialTerm y +
              ∑ k : Fin (n - t), tailTerm k y) x =
        hessian nonlinearBody x + hessian tailSum x := by
    change hessian (fun y : E ↦ nonlinearBody y + tailSum y) x =
      hessian nonlinearBody x + hessian tailSum x
    simpa using
      hessian_add_of_contDiff_two (f := nonlinearBody) (g := tailSum)
        (hf := hbodyCont) (hg := htailSumCont) (x := x)
  have hsplitInitial :
      hessian nonlinearBody x = hessian prefixTerm x - hessian initialTerm x := by
    change hessian (fun y : E ↦ prefixTerm y - initialTerm y) x =
      hessian prefixTerm x - hessian initialTerm x
    simpa using
      hessian_sub_of_contDiff_two (f := prefixTerm) (g := initialTerm)
        (hf := hprefixCont) (hg := hinitialCont) (x := x)
  have hsplitPrefix :
      hessian prefixTerm x = hessian edgeSum x + hessian terminalTerm x := by
    change hessian (fun y : E ↦ edgeSum y + terminalTerm y) x =
      hessian edgeSum x + hessian terminalTerm x
    simpa using
      hessian_add_of_contDiff_two (f := edgeSum) (g := terminalTerm)
        (hf := hedgeSumCont) (hg := hterminalCont) (x := x)
  rw [fk_eq_scalarCubic_features_of_pos ht htn]
  calc
    hessian
        (fun y : E ↦
          (∑ k : Fin (t - 1), edgeTerm k y) + terminalTerm y - initialTerm y +
            ∑ k : Fin (n - t), tailTerm k y) x
        =
          hessian nonlinearBody x + hessian tailSum x := hsplitTail
    _ =
          (hessian prefixTerm x - hessian initialTerm x) + hessian tailSum x := by
            rw [hsplitInitial]
    _ =
          ((hessian edgeSum x + hessian terminalTerm x) - hessian initialTerm x) +
            hessian tailSum x := by
            rw [hsplitPrefix]
    _ =
          (∑ k : Fin (t - 1), hessian (edgeTerm k) x) +
            hessian terminalTerm x +
            ∑ k : Fin (n - t), hessian (tailTerm k) x := by
            rw [hedgeSumHess, htailSumHess,
              hessian_continuousLinearMap_eq_zero (initialFeature ht htn) x]
            simp [sub_eq_add_neg, add_assoc]
    _ = fkPositiveHessianField ht htn x := by
          simp [edgeTerm, terminalTerm, tailTerm, fkPositiveHessianField,
            scalarCubicFeature_hessian_eq, add_assoc]

/- Lemma 4.3.1 lies in the Chapter 4 hard-instance / coordinate-support second-order domain.

Sampled owner-style declarations in this domain:
* `coordinateSubspace` and `mem_coordinateSubspace_iff` in `Chap02/Text_2_13`, the chapter owner
  and coordinatewise view for prefix-supported vectors `ℝ^{i,n}`;
* `coordinateSymmetricMatrixSubspace` and `mem_coordinateSymmetricMatrixSubspace_iff` in
  `Definition_4_3_3`, the chapter owner and entrywise view for the symmetric matrix block support
  condition `𝕊^{i,n}`;
* `hessianMatrix` / `∇²` in `Chap01/Definition_1_4_16`, the canonical matrix owner for second
  derivatives on Euclidean space.

Best owner abstraction:
* source-facing: the textbook claim that the gradient/Hessian data of `f_t` at a point in
  `ℝ^{i,n}` only reveal the first `i + 1` coordinates;
* core/canonical: the two atomic memberships `∇ (fk htn) x ∈ ℝ^{i + 1,n}` and
  `∇² (fk htn) x ∈ 𝕊^{i + 1,n}`;
* bridge/view: the packaged product membership
  `(∇ (fk htn) x, ∇² (fk htn) x) ∈ (ℝ^{i + 1,n}).prod 𝕊^{i + 1,n}`.

Primitive data:
* gradient support in the next coordinate subspace;
* Hessian matrix support in the next symmetric coordinate subspace.

Derived API:
* the product-membership theorem bundling those two owner facts.
-/

-- Proof sketch: expand the gradient plus the Hessian matrix `∇² (fk htn) x`
-- coordinatewise. If `x ∈ ℝ^{i,n}`, then `mem_coordinateSubspace_iff` says that
-- the coordinates of `x` vanish from index `i` onward. For `i < t`, the adjacent-difference terms
-- plus tail terms in Definition 4.3.2 involve only coordinates up to `i + 1`. This places the
-- gradient in `ℝ^{i+1,n}`; the same coordinate inspection places the Hessian matrix in
-- `𝕊^{i+1,n}`.
/-- Helper for Lemma 4.3.1: the adjoint of a scalar feature reads coordinates by multiplying the
feature value on the corresponding basis vector. -/
private theorem edgeFeatureEqZeroOfMemCoordinateSubspace
    (ht : 0 < t) (htn : t ≤ n) {x : E} (hx : x ∈ ℝ^{i,n}) {k : Fin (t - 1)}
    (hik : i ≤ k.1) :
    edgeFeature ht htn k x = 0 := by
  have hx0 := mem_coordinateSubspace_iff.mp hx
  -- Route correction: rewrite the edge feature into two ambient coordinates before using the
  -- zero-tail hypothesis.
  rw [edgeFeature_apply_eq_coord_sub ht htn k x]
  have hleft : x ⟨k.1, by omega⟩ = 0 := hx0 ⟨k.1, by omega⟩ hik
  have hright : x ⟨k.1 + 1, by omega⟩ = 0 := by
    exact hx0 ⟨k.1 + 1, by omega⟩ (Nat.le_trans hik (Nat.le_succ _))
  simp [hleft, hright]

/-- Helper for Lemma 4.3.1: the adjoint of a scalar feature reads coordinates by multiplying the
feature value on the corresponding basis vector. -/
private theorem adjoint_apply_eq_mul_basis
    (A : E →L[ℝ] ℝ) (r : ℝ) (j : Fin n) :
    (A.adjoint r) j = r * A (e j) := by
  calc
    (A.adjoint r) j = inner ℝ (e j) (A.adjoint r) := by
      simpa using (EuclideanSpace.basisFun_inner (x := A.adjoint r) (i := j)).symm
    _ = inner ℝ (A (e j)) r := A.adjoint_inner_right (e j) r
    _ = r * A (e j) := by
      rw [real_inner_comm]
      simpa using (RCLike.inner_apply' r (A (e j)))

/-- Helper for Lemma 4.3.1: a rank-one Hessian summand evaluates on basis vectors as the product
of the two scalar feature values. -/
private theorem smulAdjointComp_apply_basis_apply
    (A : E →L[ℝ] ℝ) (r : ℝ) (j a : Fin n) :
    (((r • (A.adjoint.comp A)) (e j)) a) = r * A (e j) * A (e a) := by
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, adjoint_apply_eq_mul_basis,
    mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Lemma 4.3.1: the terminal feature vanishes on points supported in the first `i`
coordinates whenever `i < t`. -/
private theorem terminalFeatureEqZeroOfMemCoordinateSubspace
    (ht : 0 < t) (htn : t ≤ n) {x : E} (hx : x ∈ ℝ^{i,n}) (hit : i < t) :
    terminalFeature ht htn x = 0 := by
  have hx0 := mem_coordinateSubspace_iff.mp hx
  let terminalIndex : Fin n := ⟨t - 1, by omega⟩
  have hterminalIndex :
      (Fin.castLE (fkPrefixLenLE ht htn) (Fin.last (t - 1)) : Fin n) = terminalIndex := by
    ext
    simp [terminalIndex]
  have hcoord : x terminalIndex = 0 := hx0 terminalIndex (by
    dsimp [terminalIndex]
    omega)
  -- Rewrite the terminal feature to the last active ambient coordinate.
  simpa [terminalFeature, EuclideanSpace.coe_proj, hterminalIndex, terminalIndex] using hcoord

/-- Helper for Lemma 4.3.1: every tail feature vanishes on points supported in the first `i`
coordinates whenever `i < t`. -/
private theorem tailFeatureEqZeroOfMemCoordinateSubspace
    (htn : t ≤ n) {x : E} (hx : x ∈ ℝ^{i,n}) (hit : i < t) (k : Fin (n - t)) :
    tailFeature htn k x = 0 := by
  have hx0 := mem_coordinateSubspace_iff.mp hx
  let tailIndex : Fin n := ⟨t + k.1, by omega⟩
  have htailIndex :
      (Fin.natAdd_castLEEmb (Nat.sub_le n t) k : Fin n) = tailIndex := by
    ext
    dsimp [tailIndex]
    omega
  have hcoord : x tailIndex = 0 := hx0 tailIndex (by
    dsimp [tailIndex]
    omega)
  -- Rewrite the tail feature to its ambient tail coordinate once.
  simpa [tailFeature, EuclideanSpace.coe_proj, htailIndex, tailIndex] using hcoord

/-- Helper for Lemma 4.3.1: the initial basis feature vanishes on basis vectors supported strictly
after the first revealed coordinate. -/
private theorem initialFeature_apply_basis_eq_zero_of_tail
    (ht : 0 < t) (htn : t ≤ n) {a : Fin n} (ha : i + 1 ≤ a.1) :
    initialFeature ht htn (e a) = 0 := by
  have ha0 : 0 < a.1 := by
    omega
  have hinitialIndex :
      (Fin.castLE (fkPrefixLenLE ht htn) (0 : Fin ((t - 1) + 1)) : Fin n) = ⟨0, by omega⟩ := by
    ext
    simp
  have hne : (⟨0, by omega⟩ : Fin n) ≠ a := by
    intro hEq
    exact (Nat.ne_of_lt ha0) (congrArg Fin.val hEq)
  -- The first-coordinate feature vanishes on basis vectors supported strictly later.
  simp [initialFeature, hinitialIndex, hne]

/-- Helper for Lemma 4.3.1: early edge features vanish on basis vectors supported past the next
revealed coordinate. -/
private theorem edgeFeature_apply_basis_eq_zero_of_tail
    (ht : 0 < t) (htn : t ≤ n) {k : Fin (t - 1)} {j : Fin n}
    (hk : k.1 < i) (hj : i + 1 ≤ j.1) :
    edgeFeature ht htn k (e j) = 0 := by
  -- Route correction: use the adjacent-coordinate normal form and show neither coordinate hits the
  -- tail-supported basis index `j`.
  rw [edgeFeature_apply_eq_coord_sub ht htn k (e j)]
  have hij : i < j.1 := lt_of_lt_of_le (Nat.lt_succ_self i) hj
  have hleft : (⟨k.1, by omega⟩ : Fin n) ≠ j := by
    intro hEq
    have := congrArg Fin.val hEq
    exact (Nat.ne_of_lt (lt_trans hk hij)) this
  have hright : (⟨k.1 + 1, by omega⟩ : Fin n) ≠ j := by
    intro hEq
    have := congrArg Fin.val hEq
    have hk1_lt_j : k.1 + 1 < j.1 := lt_of_le_of_lt (Nat.succ_le_of_lt hk) hij
    exact (Nat.ne_of_lt hk1_lt_j) this
  simp [hleft, hright]

/-- Helper for Lemma 4.3.1: every tail basis column of the positive-branch Hessian field
vanishes coordinatewise on a point supported in the first `i` coordinates. -/
private theorem fkPositiveHessianField_apply_basis_coordinate_zero_of_tail
    (ht : 0 < t) (htn : t ≤ n) {x : E} (hx : x ∈ ℝ^{i,n}) (hit : i < t) {j a : Fin n}
    (hj : i + 1 ≤ j.1) :
    (fkPositiveHessianField ht htn x (e j)) a = 0 := by
  have hx0 := mem_coordinateSubspace_iff.mp hx
  have hedge :
      (∑ k : Fin (t - 1),
          (2 * |edgeFeature ht htn k x|) * edgeFeature ht htn k (e j) *
            edgeFeature ht htn k (e a)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro k hk
    by_cases hklt : k.1 < i
    · have hbasis : edgeFeature ht htn k (e j) = 0 :=
        edgeFeature_apply_basis_eq_zero_of_tail ht htn hklt hj
      simp [hbasis]
    · have hkge : i ≤ k.1 := Nat.le_of_not_lt hklt
      have hcoeff : edgeFeature ht htn k x = 0 :=
        edgeFeatureEqZeroOfMemCoordinateSubspace ht htn hx hkge
      simp [hcoeff]
  have hterminalCoeff : terminalFeature ht htn x = 0 :=
    terminalFeatureEqZeroOfMemCoordinateSubspace ht htn hx hit
  have htail :
      (∑ k : Fin (n - t),
          (2 * |tailFeature htn k x|) * tailFeature htn k (e j) * tailFeature htn k (e a)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro k hk
    have htailCoeff : tailFeature htn k x = 0 :=
      tailFeatureEqZeroOfMemCoordinateSubspace htn hx hit k
    simp [htailCoeff]
  rw [fkPositiveHessianField]
  simp_rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
    smulAdjointComp_apply_basis_apply]
  rw [hedge, htail]
  simp [hterminalCoeff]

/-- Helper for Lemma 4.3.1: every tail coordinate of the positive-branch gradient field vanishes
at a point supported in the first `i` coordinates. -/
private theorem fkPositiveGradientField_coordinate_zero_of_tail
    (ht : 0 < t) (htn : t ≤ n) {x : E} (hx : x ∈ ℝ^{i,n}) (hit : i < t) {a : Fin n}
    (ha : i + 1 ≤ a.1) :
    (fkPositiveGradientField ht htn x) a = 0 := by
  have hx0 := mem_coordinateSubspace_iff.mp hx
  have hedge :
      (∑ k : Fin (t - 1),
          (edgeFeature ht htn k x * |edgeFeature ht htn k x|) *
            edgeFeature ht htn k (e a)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro k hk
    by_cases hklt : k.1 < i
    · have hbasis : edgeFeature ht htn k (e a) = 0 :=
        edgeFeature_apply_basis_eq_zero_of_tail ht htn hklt ha
      simp [hbasis]
    · have hkge : i ≤ k.1 := Nat.le_of_not_lt hklt
      have hcoeff : edgeFeature ht htn k x = 0 :=
        edgeFeatureEqZeroOfMemCoordinateSubspace ht htn hx hkge
      simp [hcoeff]
  have hterminalCoeff : terminalFeature ht htn x = 0 :=
    terminalFeatureEqZeroOfMemCoordinateSubspace ht htn hx hit
  have hinitialBasis : initialFeature ht htn (e a) = 0 :=
    initialFeature_apply_basis_eq_zero_of_tail ht htn ha
  have htail :
      (∑ k : Fin (n - t),
          (tailFeature htn k x * |tailFeature htn k x|) * tailFeature htn k (e a)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro k hk
    have htailCoeff : tailFeature htn k x = 0 :=
      tailFeatureEqZeroOfMemCoordinateSubspace htn hx hit k
    simp [htailCoeff]
  rw [fkPositiveGradientField]
  simp_rw [Pi.add_apply, Pi.sub_apply, Finset.sum_apply, adjoint_apply_eq_mul_basis]
  rw [hedge, htail]
  simp [hterminalCoeff, hinitialBasis]

/-- If `x ∈ ℝ^{i,n}` with `i < t`, then the gradient of the hard-instance objective `f_t`
belongs to the next coordinate subspace `ℝ^{i+1,n}`. -/
theorem fk_gradient_mem_next_coordinateSubspace
    (htn : t ≤ n) {x : E} (hx : x ∈ ℝ^{i,n}) (hit : i < t) :
    ∇ (fk htn) x ∈ ℝ^{i + 1,n} := by
  have ht : 0 < t := lt_of_le_of_lt (Nat.zero_le i) hit
  have hgradx : ∇ (fk htn) x = fkPositiveGradientField ht htn x := by
    -- The pointwise gradient witness determines the canonical gradient value.
    simpa using HasGradientAt.gradient (hasGradientAt_fk_of_pos ht htn x)
  rw [mem_coordinateSubspace_iff]
  intro a ha
  -- Move to the explicit positive-branch gradient field, then use its tail-coordinate vanishing.
  rw [hgradx]
  exact fkPositiveGradientField_coordinate_zero_of_tail ht htn hx hit ha

/-- If `x ∈ ℝ^{i,n}` with `i < t`, then the Hessian matrix of the hard-instance objective `f_t`
belongs to the next symmetric coordinate subspace `𝕊^{i+1,n}`. -/
theorem fk_hessian_mem_next_coordinateSymmetricMatrixSubspace
    (htn : t ≤ n) {x : E} (hx : x ∈ ℝ^{i,n}) (hit : i < t) :
    ∇² (fk htn) x ∈ 𝕊^{i + 1,n} := by
  have ht : 0 < t := lt_of_le_of_lt (Nat.zero_le i) hit
  have hsymm : (∇² (fk htn) x).IsSymm := by
    exact
      hessianMatrix_isSymm_of_contDiffAt
        ((fk_contDiff_two htn).contDiffAt : ContDiffAt ℝ 2 (fk htn) x)
  have htailEntry {a j : Fin n} (hj : i + 1 ≤ j.1) : ∇² (fk htn) x a j = 0 := by
    rw [hessianMatrix_apply, fk_hessian_eq_of_pos ht htn x]
    -- Read the matrix entry through the intrinsic Hessian action on the basis column `e j`.
    rw [show inner ℝ (e a) (fkPositiveHessianField ht htn x (e j)) =
        (fkPositiveHessianField ht htn x (e j)) a by
          simpa using
            (EuclideanSpace.basisFun_inner (x := fkPositiveHessianField ht htn x (e j))
              (i := a))]
    exact
      fkPositiveHessianField_apply_basis_coordinate_zero_of_tail
        ht htn hx hit (j := j) (a := a) hj
  rw [mem_coordinateSymmetricMatrixSubspace_iff]
  constructor
  · exact hsymm
  · intro a j haj htail
    by_cases hj : i + 1 ≤ j.1
    · exact htailEntry hj
    · have ha : i + 1 ≤ a.1 := by
        omega
      calc
        ∇² (fk htn) x a j = ∇² (fk htn) x j a := by
          exact (hsymm.apply a j).symm
        _ = 0 := htailEntry ha

/-- Lemma 4.3.1: if `x ∈ ℝ^{i,n}` with `i < t`, then for the hard-instance function `f_t`
formalized by `fk`, the pair formed by the gradient and Hessian matrix at `x` belongs to
`ℝ^{i+1,n} × 𝕊^{i+1,n}`. -/
theorem fk_first_second_order_mem_next_coordinate_subspaces
    (htn : t ≤ n) {x : E} (hx : x ∈ ℝ^{i,n}) (hit : i < t) :
    (∇ (fk htn) x, ∇² (fk htn) x) ∈
      (ℝ^{i + 1,n}).prod 𝕊^{i + 1,n} := by
  exact ⟨fk_gradient_mem_next_coordinateSubspace htn hx hit,
    fk_hessian_mem_next_coordinateSymmetricMatrixSubspace htn hx hit⟩
