/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Text_4_2_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_11
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Lemma_4_2_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped DegreeConditioning
open LinearMap

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Text 4.2.7 lies in the Chapter 4 power-distance / degree-conditioning domain.

Sampled owner-style declarations:
* `powerDistance` in `Text_4_2_6`
* `HasIteratedFDerivLipschitzConstantOfDegree` in `Definition_4_2_11`
* `uniformConvexityParameterOfDegree` in `Definition_4_2_11`
* `conditionNumberOfDegree` in `Definition_4_2_11`

Best owner abstraction:
* source-facing: the exact degree-`2` and degree-`3` conditioning identities for the canonical
  power-distance
* core/canonical: the owner `powerDistance p x₀`
* bridge/view: the specialized values of `L[p](f)`, `σ[p](f)`, and `γ[p](f)` at `p = 2, 3`

Primitive data:
* the center `x₀`
* the canonical chapter owner `powerDistance p x₀`

Derived API:
* the finiteness instances needed to form `L[2](powerDistance (2 : ℝ) x₀)` and
  `L[3](powerDistance (3 : ℝ) x₀)`
* in the nontrivial case, the finite-parameter instances needed to form
  `σ[2](powerDistance (2 : ℝ) x₀)` and `σ[3](powerDistance (3 : ℝ) x₀)`
* in the nontrivial case, the positivity instances needed to form
  `γ[2](powerDistance (2 : ℝ) x₀)` and `γ[3](powerDistance (3 : ℝ) x₀)` as genuine real ratios
* the exact source-facing identities for `L`, `σ`, and `γ`

Ambient-level check:
* the owner layer for `powerDistance`, `L[p]`, `σ[p]`, and `γ[p]` does not require completeness;
  the public statements below therefore keep only the inner-product-space assumptions used by the
  `p = 2, 3` identities themselves;
* the sharp exact-value identities require `[Nontrivial E]`, since on the trivial space
  `powerDistance p x₀` is the zero function, so the textbook constants `1`, `2`, `1 / 2`, and
  `1 / 4` are no longer the actual values of `L[p]`, `σ[p]`, and `γ[p]`

The previous local declarations `quadraticPowerFunction` and `cubicPowerFunction` duplicated the
owner `powerDistance` from `Text_4_2_6`. This file now states Text 4.2.7 directly over that
owner instead of keeping parallel special-case wrappers. The support layer is kept minimal:
global instances record only the existence of finite `L[p]`, while the sharper `σ[p]` and `γ[p]`
owners are available only under `[Nontrivial E]`, where the textbook exact constants are
mathematically correct.
-/

section Helpers

variable (x0 : E)

/-- Helper for Text 4 2 7: every nontrivial real inner-product space contains a unit vector. -/
private lemma exists_unit_vector [Nontrivial E] : ∃ u : E, ‖u‖ = 1 := by
  -- Normalize a nonzero vector to get the unit test direction used in the sharp constants.
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  refine ⟨‖x‖⁻¹ • x, ?_⟩
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  calc
    ‖‖x‖⁻¹ • x‖ = |‖x‖⁻¹| * ‖x‖ := norm_smul _ _
    _ = ‖x‖⁻¹ * ‖x‖ := by rw [abs_of_pos (inv_pos.mpr hxnorm)]
    _ = 1 := inv_mul_cancel₀ hxnorm.ne'

/-- Helper for Text 4 2 7: the quadratic form coming from the ambient inner product is positive
definite. -/
private lemma inner_bilin_posDef :
    ((show LinearMap.BilinForm ℝ E from innerₗ E).toQuadraticMap).PosDef := by
  -- The quadratic map is `x ↦ ‖x‖²`, which is strictly positive on nonzero vectors.
  intro x hx
  simpa [real_inner_self_eq_norm_sq] using sq_pos_iff.mpr (norm_ne_zero_iff.mpr hx)

/-- Helper for Text 4 2 7: the ambient inner-product bilinear form is symmetric. -/
private lemma inner_bilin_isSymm :
    (show LinearMap.BilinForm ℝ E from innerₗ E).IsSymm := by
  -- Convert the standard symmetry of `innerₗ E` to the bilinear-form symmetry owner.
  exact (LinearMap.BilinForm.isSymm_iff).2 <| by
    simpa using (isSymm_inner (E := E) : LinearMap.IsSymm (innerₗ E))

/-- Helper for Text 4 2 7: the quadratic power-distance has the explicit derivative
`innerSL ℝ (x - x₀)`. -/
private lemma powerDistance_two_fderiv_eq (x : E) :
    fderiv ℝ (powerDistance (2 : ℝ) x0) x =
      innerSL ℝ (x - x0) := by
  -- Differentiate `‖x - x₀‖²` directly and scale by `1 / 2`.
  have hsub : HasFDerivAt (fun y : E ↦ y - x0) (1 : E →L[ℝ] E) x := by
    simpa using (hasFDerivAt_id x).sub_const x0
  have hpowShift : ((2 : ℝ) - 2) = 0 := by norm_num
  have hsq :
      HasFDerivAt (fun y : E ↦ ‖y - x0‖ ^ (2 : ℝ))
        ((2 : ℝ) • innerSL ℝ (x - x0)) x := by
    simpa [hpowShift] using
      (hasFDerivAt_norm_rpow (x - x0) (by norm_num : (1 : ℝ) < 2)).comp x hsub
  have hscaled :
      HasFDerivAt (fun y : E ↦ (1 / (2 : ℝ)) * ‖y - x0‖ ^ (2 : ℝ))
        ((1 / (2 : ℝ)) • ((2 : ℝ) • innerSL ℝ (x - x0))) x := by
    simpa using hsq.const_mul (1 / (2 : ℝ))
  have hfun :
      powerDistance (2 : ℝ) x0 = fun y : E ↦ ‖y - x0‖ ^ (2 : ℝ) * (1 / (2 : ℝ)) := by
    funext y
    rw [powerDistance_apply, mul_comm]
  simpa [hfun, one_div, Real.rpow_natCast, smul_smul, mul_comm, mul_left_comm, mul_assoc] using
    hscaled.fderiv

/-- Helper for Text 4 2 7: away from the origin, the derivative of the norm is the normalized
inner-product functional. -/
private lemma fderiv_norm_eq_inv_smul_innerSL {x : E} (hx : x ≠ 0) :
    fderiv ℝ (fun y : E ↦ ‖y‖) x = ‖x‖⁻¹ • innerSL ℝ x := by
  -- Compare two derivative computations of `y ↦ ‖y‖²` and solve for the norm derivative.
  have hdiff : DifferentiableAt ℝ (fun y : E ↦ ‖y‖) x :=
    DifferentiableAt.norm ℝ differentiableAt_id hx
  have hsq1 :
      HasFDerivAt (fun y : E ↦ ‖y‖ * ‖y‖)
        (‖x‖ • fderiv ℝ (fun y : E ↦ ‖y‖) x + ‖x‖ • fderiv ℝ (fun y : E ↦ ‖y‖) x) x := by
    -- Differentiate `‖y‖ * ‖y‖` by the product rule.
    simpa using (hdiff.hasFDerivAt.mul hdiff.hasFDerivAt)
  have hsq2 :
      HasFDerivAt (fun y : E ↦ ‖y‖ * ‖y‖) (2 • innerSL ℝ x) x := by
    -- The squared norm has the standard inner-product derivative.
    simpa [pow_two] using ((hasFDerivAt_id x).norm_sq)
  have heq :
      ‖x‖ • fderiv ℝ (fun y : E ↦ ‖y‖) x + ‖x‖ • fderiv ℝ (fun y : E ↦ ‖y‖) x =
        2 • innerSL ℝ x := hsq1.unique hsq2
  ext u
  have heq_apply := congrArg (fun T : E →L[ℝ] ℝ ↦ T u) heq
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, innerSL_apply_apply]
    at heq_apply
  have hu_two :
      (2 : ℝ) * (‖x‖ * (fderiv ℝ (fun y : E ↦ ‖y‖) x) u) =
        2 * inner ℝ x u := by
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

/-- Helper for Text 4 2 7: away from the origin, the derivative of `z ↦ ‖z‖ • z` splits into the
identity part and the radial rank-one part. -/
private lemma hasFDerivAt_norm_smul_id {x : E} (hx : x ≠ 0) :
    HasFDerivAt (fun y : E ↦ ‖y‖ • y)
      (‖x‖ • ContinuousLinearMap.id ℝ E + (‖x‖⁻¹ • innerSL ℝ x).smulRight x) x := by
  -- Differentiate the scalar-vector product after replacing the norm derivative explicitly.
  have hdiff : DifferentiableAt ℝ (fun y : E ↦ ‖y‖) x :=
    DifferentiableAt.norm ℝ differentiableAt_id hx
  have hnorm : HasFDerivAt (fun y : E ↦ ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
    simpa [fderiv_norm_eq_inv_smul_innerSL hx] using hdiff.hasFDerivAt
  -- Then apply the product rule to `‖y‖ • y`.
  simpa using hnorm.smul (hasFDerivAt_id x)

/-- Helper for Text 4 2 7: at the origin, `z ↦ ‖z‖ • z` has derivative `0`. -/
private lemma hasFDerivAt_norm_smul_id_zero :
    HasFDerivAt (fun y : E ↦ ‖y‖ • y) (0 : E →L[ℝ] E) 0 := by
  -- The map vanishes quadratically at the origin, so its derivative there is zero.
  have hbigO :
      (fun y : E ↦ ‖y‖ • y) =O[nhds (0 : E)] fun y ↦ ‖y - (0 : E)‖ ^ (2 : ℕ) := by
    refine Asymptotics.isBigO_iff'.2 ?_
    refine ⟨1, by positivity, ?_⟩
    filter_upwards with y
    simp [norm_smul, pow_two, mul_comm]
  exact hbigO.hasFDerivAt (by norm_num)

/-- Helper for Text 4 2 7: the cubic power-distance has the explicit first derivative
everywhere. -/
private lemma powerDistance_three_fderiv_eq (x : E) :
    fderiv ℝ (powerDistance (3 : ℝ) x0) x =
      ‖x - x0‖ • innerSL ℝ (x - x0) := by
  -- Differentiate `‖x - x₀‖³` directly and scale by `1 / 3`.
  have hsub : HasFDerivAt (fun y : E ↦ y - x0) (1 : E →L[ℝ] E) x := by
    simpa using (hasFDerivAt_id x).sub_const x0
  have hpow :
      HasFDerivAt (fun y : E ↦ ‖y - x0‖ ^ (3 : ℝ))
        (((3 : ℝ) * ‖x - x0‖ ^ ((3 : ℝ) - 2)) • innerSL ℝ (x - x0)) x := by
    simpa using (hasFDerivAt_norm_rpow (x - x0) (by norm_num : (1 : ℝ) < 3)).comp x hsub
  have hscaled :
      HasFDerivAt (fun y : E ↦ (1 / (3 : ℝ)) * ‖y - x0‖ ^ (3 : ℝ))
        ((1 / (3 : ℝ)) • (((3 : ℝ) * ‖x - x0‖ ^ ((3 : ℝ) - 2)) • innerSL ℝ (x - x0))) x := by
    simpa using hpow.const_mul (1 / (3 : ℝ))
  have hfun :
      powerDistance (3 : ℝ) x0 = fun y : E ↦ ‖y - x0‖ ^ (3 : ℝ) * (1 / (3 : ℝ)) := by
    funext y
    rw [powerDistance_apply, mul_comm]
  have hpowShift : ((3 : ℝ) - 2) = 1 := by norm_num
  simpa [hfun, one_div, Real.rpow_one, smul_smul, mul_assoc, mul_comm, mul_left_comm, hpowShift]
    using hscaled.fderiv

/-- Helper for Text 4 2 7: translating `z ↦ ‖z‖ • z` gives the derivative model for
`y ↦ ‖y - x₀‖ • (y - x₀)`. -/
private lemma translatedNormSmulSubCenterHasFDerivAt :
    HasFDerivAt (fun y : E ↦ ‖y - x0‖ • (y - x0)) (0 : E →L[ℝ] E) x0 := by
  -- Compose the origin-centered zero-derivative model with the translation `y ↦ y + (-x₀)`.
  have hsub : HasFDerivAt (fun y : E ↦ y + (-x0)) (1 : E →L[ℝ] E) x0 := by
    simpa using (hasFDerivAt_id x0).add_const (-x0)
  have houter :
      HasFDerivAt (fun y : E ↦ ‖y‖ • y) (0 : E →L[ℝ] E) ((fun y : E ↦ y + (-x0)) x0) := by
    simpa using
      (hasFDerivAt_norm_smul_id_zero :
        HasFDerivAt (fun y : E ↦ ‖y‖ • y) (0 : E →L[ℝ] E) 0)
  simpa [sub_eq_add_neg, Function.comp_def] using (houter.comp x0 hsub)

/-- Helper for Text 4 2 7: translating `z ↦ ‖z‖ • z` gives the derivative model for
`y ↦ ‖y - x₀‖ • (y - x₀)`. -/
private lemma translated_norm_smul_sub_hasFDerivAt (x : E) :
    HasFDerivAt (fun y : E ↦ ‖y - x0‖ • (y - x0))
      (‖x - x0‖ • ContinuousLinearMap.id ℝ E +
        ((‖x - x0‖)⁻¹ • innerSL ℝ (x - x0)).smulRight (x - x0)) x := by
  -- Route correction: split the center case first, then compose the origin-centered model with
  -- the translation `y ↦ y - x₀`.
  by_cases hx : x = x0
  · -- At the center, the translated vector field has derivative `0`.
    subst x
    simpa using translatedNormSmulSubCenterHasFDerivAt x0
  · -- Away from the center, the explicit origin-centered derivative formula transports directly.
    have hsub : HasFDerivAt (fun y : E ↦ y - x0) (1 : E →L[ℝ] E) x := by
      simpa using (hasFDerivAt_id x).sub_const x0
    have houter :
        HasFDerivAt (fun z : E ↦ ‖z‖ • z)
          (‖x - x0‖ • ContinuousLinearMap.id ℝ E +
            ((‖x - x0‖)⁻¹ • innerSL ℝ (x - x0)).smulRight (x - x0)) (x - x0) := by
      exact hasFDerivAt_norm_smul_id (by simpa [sub_eq_zero] using hx)
    simpa [Function.comp_def] using (houter.comp x hsub)

/-- Helper for Text 4 2 7: the second Fréchet derivative of the cubic power-distance is the
Riesz image of the translated `‖z‖ • z` derivative model. -/
private lemma powerDistance_three_sndFDeriv_eq (x : E) :
    fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0)) x =
      (innerSL ℝ).comp
        (‖x - x0‖ • ContinuousLinearMap.id ℝ E +
          ((‖x - x0‖)⁻¹ • innerSL ℝ (x - x0)).smulRight (x - x0)) := by
  -- Rewrite the first derivative as `innerSL ∘ (fun y ↦ ‖y - x₀‖ • (y - x₀))`, then differentiate
  -- through the translated vector-field model.
  have hfun :
      fderiv ℝ (powerDistance (3 : ℝ) x0) =
        fun y : E ↦ (innerSL ℝ) (‖y - x0‖ • (y - x0)) := by
    funext y
    ext z
    simp [powerDistance_three_fderiv_eq]
  rw [hfun]
  exact
    ((innerSL ℝ).hasFDerivAt.comp x (translated_norm_smul_sub_hasFDerivAt x0 x)).fderiv

/-- Helper for Text 4 2 7: the first iterated derivative is isometric to the Fréchet derivative.
-/
private lemma iteratedFDerivOne_normSub_eq_fderiv_normSub
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (x y : E) :
    ‖iteratedFDeriv ℝ 1 f x - iteratedFDeriv ℝ 1 f y‖ = ‖fderiv ℝ f x - fderiv ℝ f y‖ := by
  -- Compare the first iterated derivative with `fderiv` through the canonical currying isometry.
  let e : (E [×1]→L[ℝ] F) ≃ₗᵢ[ℝ] E →L[ℝ] F := continuousMultilinearCurryFin1 ℝ E F
  have hx : e (iteratedFDeriv ℝ 1 f x) = fderiv ℝ f x := by
    ext z
    simp [e]
  have hy : e (iteratedFDeriv ℝ 1 f y) = fderiv ℝ f y := by
    ext z
    simp [e]
  calc
    ‖iteratedFDeriv ℝ 1 f x - iteratedFDeriv ℝ 1 f y‖ =
        ‖e (iteratedFDeriv ℝ 1 f x - iteratedFDeriv ℝ 1 f y)‖ := by
          simpa using (e.norm_map (iteratedFDeriv ℝ 1 f x - iteratedFDeriv ℝ 1 f y)).symm
    _ = ‖fderiv ℝ f x - fderiv ℝ f y‖ := by
          rw [map_sub, hx, hy]

/-- Helper for Text 4 2 7: the first Taylor coefficient of `ftaylorSeries ℝ f` is isometric to
the Fréchet derivative. -/
private lemma ftaylorSeriesCoeffOne_normSub_eq_fderiv_normSub {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) (x y : E) :
    ‖ftaylorSeries ℝ f x 1 - ftaylorSeries ℝ f y 1‖ = ‖fderiv ℝ f x - fderiv ℝ f y‖ := by
  -- Rewrite the canonical Taylor witness to `iteratedFDeriv` and then use the currying isometry.
  have hx : ftaylorSeries ℝ f x 1 = iteratedFDeriv ℝ 1 f x :=
    hf.ftaylorSeries.eq_iteratedFDeriv le_rfl x
  have hy : ftaylorSeries ℝ f y 1 = iteratedFDeriv ℝ 1 f y :=
    hf.ftaylorSeries.eq_iteratedFDeriv le_rfl y
  rw [hx, hy]
  exact iteratedFDerivOne_normSub_eq_fderiv_normSub x y

/-- Helper for Text 4 2 7: the second Taylor coefficient is isometric to the second Fréchet
derivative. -/
private lemma ftaylorSeriesCoeffTwo_normSub_eq_sndFDeriv_normSub {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (x y : E) :
    ‖ftaylorSeries ℝ f x 2 - ftaylorSeries ℝ f y 2‖ =
      ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ := by
  -- Rewrite the Taylor coefficient through `iteratedFDeriv`.
  have hx : ftaylorSeries ℝ f x 2 = iteratedFDeriv ℝ 2 f x :=
    hf.ftaylorSeries.eq_iteratedFDeriv le_rfl x
  have hy : ftaylorSeries ℝ f y 2 = iteratedFDeriv ℝ 2 f y :=
    hf.ftaylorSeries.eq_iteratedFDeriv le_rfl y
  rw [hx, hy]
  let eEquiv : (E [×2]→L[ℝ] ℝ) ≃ₗᵢ[ℝ] (E [×1]→L[ℝ] E →L[ℝ] ℝ) :=
    continuousMultilinearCurryRightEquiv' ℝ 1 E ℝ
  let e : (E [×2]→L[ℝ] ℝ) →ₗᵢ[ℝ] (E [×1]→L[ℝ] E →L[ℝ] ℝ) := eEquiv.toLinearIsometry
  have hx' : e (iteratedFDeriv ℝ 2 f x) = iteratedFDeriv ℝ 1 (fun z ↦ fderiv ℝ f z) x := by
    -- The second iterated derivative is the curried first derivative of `fderiv`.
    rw [iteratedFDeriv_succ_eq_comp_right]
    simp [e, eEquiv]
  have hy' : e (iteratedFDeriv ℝ 2 f y) = iteratedFDeriv ℝ 1 (fun z ↦ fderiv ℝ f z) y := by
    -- The same identification holds at the second base point.
    rw [iteratedFDeriv_succ_eq_comp_right]
    simp [e, eEquiv]
  have hdist :
      dist (iteratedFDeriv ℝ 2 f x) (iteratedFDeriv ℝ 2 f y) =
        dist (iteratedFDeriv ℝ 1 (fun z ↦ fderiv ℝ f z) x)
          (iteratedFDeriv ℝ 1 (fun z ↦ fderiv ℝ f z) y) := by
    simpa [hx', hy'] using (e.dist_map (iteratedFDeriv ℝ 2 f x) (iteratedFDeriv ℝ 2 f y)).symm
  have hiter :
      dist (iteratedFDeriv ℝ 1 (fun z ↦ fderiv ℝ f z) x)
          (iteratedFDeriv ℝ 1 (fun z ↦ fderiv ℝ f z) y) =
        dist (fderiv ℝ (fderiv ℝ f) x) (fderiv ℝ (fderiv ℝ f) y) := by
    let e1 : (E [×1]→L[ℝ] E →L[ℝ] ℝ) ≃ₗᵢ[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
      continuousMultilinearCurryFin1 ℝ E (E →L[ℝ] ℝ)
    have hx1 : e1 (iteratedFDeriv ℝ 1 (fun z ↦ fderiv ℝ f z) x) = fderiv ℝ (fderiv ℝ f) x := by
      ext z
      simp [e1]
    have hy1 : e1 (iteratedFDeriv ℝ 1 (fun z ↦ fderiv ℝ f z) y) = fderiv ℝ (fderiv ℝ f) y := by
      ext z
      simp [e1]
    simpa [hx1, hy1] using
      (e1.dist_map (iteratedFDeriv ℝ 1 (fun z ↦ fderiv ℝ f z) x)
        (iteratedFDeriv ℝ 1 (fun z ↦ fderiv ℝ f z) y)).symm
  calc
    ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ =
        dist (iteratedFDeriv ℝ 2 f x) (iteratedFDeriv ℝ 2 f y) := by
          rw [dist_eq_norm]
    _ = dist (fderiv ℝ (fderiv ℝ f) x) (fderiv ℝ (fderiv ℝ f) y) := hdist.trans hiter
    _ = ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ := by
          exact dist_eq_norm (fderiv ℝ (fderiv ℝ f) x) (fderiv ℝ (fderiv ℝ f) y)

/-- Helper for Text 4 2 7: on the primal space of the ambient inner product, the intrinsic norm is
the ambient norm. -/
private lemma innerPrimalSpace_norm_eq_ambient
    (z : LinearMap.BilinForm.PrimalSpace (show LinearMap.BilinForm ℝ E from innerₗ E)) :
    ‖z‖ = ‖(z : E)‖ := by
  let B : LinearMap.BilinForm ℝ E := innerₗ E
  letI : Fact (B.toQuadraticMap.PosDef) := ⟨by
    simpa [B] using (inner_bilin_posDef (E := E))⟩
  -- Normalize the intrinsic `PrimalSpace` norm through the defining primal seminorm.
  calc
    ‖z‖ = B.primalSeminorm Fact.out (z : B.PrimalSpace) := by
          simp [B]
    _ = Real.sqrt (B (z : E) (z : E)) := by
          exact LinearMap.BilinForm.primalSeminorm_apply B Fact.out (z : B.PrimalSpace)
    _ = ‖(z : E)‖ := by
          simp [B]

/-- Helper for Text 4 2 7: differences in `PrimalSpace (innerₗ E)` have the ambient norm of the
same difference in `E`. -/
private lemma innerPrimalSpace_normSub_eq_ambient
    (x y : LinearMap.BilinForm.PrimalSpace (show LinearMap.BilinForm ℝ E from innerₗ E)) :
    ‖x - y‖ = ‖((x : E) - (y : E))‖ := by
  exact innerPrimalSpace_norm_eq_ambient (x - y)

/-- Helper for Text 4 2 7: the intrinsic uniform-convexity owner for `powerFunction (innerₗ E)`
specializes to the ambient `powerDistance`. -/
private lemma powerDistanceUniformConvexOnInner (p : ℝ) (hp : 2 ≤ p) :
    UniformConvexOn Set.univ
      (uniformConvexPowerModulus (Real.rpow (1 / 2 : ℝ) (p - 2)) p)
      (powerDistance p x0) := by
  -- Route correction: reuse the intrinsic owner theorem pointwise, and only rewrite the function
  -- values and norm term from `PrimalSpace (innerₗ E)` back to the ambient `E` surface.
  let B : LinearMap.BilinForm ℝ E := show LinearMap.BilinForm ℝ E from innerₗ E
  letI : Fact B.IsSymm := ⟨inner_bilin_isSymm (E := E)⟩
  letI : Fact B.toQuadraticMap.PosDef := ⟨inner_bilin_posDef (E := E)⟩
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hnorm_mid :
      ‖((a • x + b • y - x0 : E) : LinearMap.BilinForm.PrimalSpace B)‖ =
        ‖a • x + b • y - x0‖ :=
    innerPrimalSpace_norm_eq_ambient (E := E) (z := (a • x + b • y - x0 : E))
  have hnorm_x :
      ‖((x - x0 : E) : LinearMap.BilinForm.PrimalSpace B)‖ = ‖x - x0‖ :=
    innerPrimalSpace_norm_eq_ambient (E := E) (z := (x - x0 : E))
  have hnorm_y :
      ‖((y - x0 : E) : LinearMap.BilinForm.PrimalSpace B)‖ = ‖y - x0‖ :=
    innerPrimalSpace_norm_eq_ambient (E := E) (z := (y - x0 : E))
  have hnorm_xy :
      √((B x) x - (B x) y - ((B y) x - (B y) y)) = ‖x - y‖ := by
    have hquad :
        (B x) x - (B x) y - ((B y) x - (B y) y) = B (x - y) (x - y) := by
      calc
        (B x) x - (B x) y - ((B y) x - (B y) y) =
            inner ℝ x (x - y) - inner ℝ y (x - y) := by
              calc
                (B x) x - (B x) y - ((B y) x - (B y) y) =
                    inner ℝ x x - inner ℝ x y - (inner ℝ y x - inner ℝ y y) := by
                      simp [B]
                _ = inner ℝ x x - inner ℝ x y - inner ℝ y x + inner ℝ y y := by
                      ring
                _ = inner ℝ x x - inner ℝ x y - inner ℝ x y + inner ℝ y y := by
                      rw [real_inner_comm y x]
                _ = inner ℝ x (x - y) - inner ℝ y (x - y) := by
                      rw [inner_sub_right, inner_sub_right]
                      rw [real_inner_comm y x]
                      ring
        _ = inner ℝ (x - y) (x - y) := by
              rw [inner_sub_left]
    calc
      √((B x) x - (B x) y - ((B y) x - (B y) y)) = √(B (x - y) (x - y)) := by
        rw [hquad]
      _ = ‖x - y‖ := by
        calc
          √(B (x - y) (x - y)) = √(inner ℝ (x - y) (x - y)) := by
            change √(inner ℝ (x - y) (x - y)) = √(inner ℝ (x - y) (x - y))
            rfl
          _ = ‖x - y‖ := by
            simp
  have hinner :
      powerFunction B p x0 (a • x + b • y) ≤
        a • powerFunction B p x0 x + b • powerFunction B p x0 y -
          a * b *
            uniformConvexPowerModulus (Real.rpow (1 / 2 : ℝ) (p - 2)) p ‖x - y‖ := by
    simpa [smul_eq_mul, hnorm_xy] using
      (powerFunction_uniformConvexOn B (inner_bilin_posDef (E := E)) p x0 hp).2
        (by simp : x ∈ (Set.univ : Set E))
        (by simp : y ∈ (Set.univ : Set E))
        ha hb hab
  -- Normalize the intrinsic quadratic forms to ambient squared norms before closing.
  have hmid_inner :
      a * inner ℝ x (a • x + b • y - x0) + b * inner ℝ y (a • x + b • y - x0) -
          inner ℝ x0 (a • x + b • y - x0) =
        inner ℝ (a • x + b • y - x0) (a • x + b • y - x0) := by
    rw [inner_sub_left, inner_add_left]
    simp [inner_smul_left]
  have hx_inner :
      inner ℝ x (x - x0) - inner ℝ x0 (x - x0) = inner ℝ (x - x0) (x - x0) := by
    rw [inner_sub_left]
  have hy_inner :
      inner ℝ y (y - x0) - inner ℝ x0 (y - x0) = inner ℝ (y - x0) (y - x0) := by
    rw [inner_sub_left]
  simpa [B, powerFunction_apply, powerDistance_apply, hnorm_mid, hnorm_x, hnorm_y,
    innerPrimalSpace_normSub_eq_ambient, hmid_inner, hx_inner, hy_inner,
    real_inner_self_eq_norm_sq] using hinner

/-- Helper for Text 4 2 7: the quadratic power-distance has the chapter owner
`𝒞^{1,1}_{1}(Set.univ)`. -/
private lemma powerDistance_two_mem_taylorCoeffLipschitzClass_one :
    powerDistance (2 : ℝ) x0 ∈ 𝒞^{1,1}_{(1 : NNReal)}(Set.univ) := by
  -- Use the canonical Taylor witness `ftaylorSeries` and normalize its first coefficient.
  have hsub : ContDiff ℝ 1 (fun y : E ↦ y - x0) :=
    contDiff_id.sub contDiff_const
  have hcontDiff : ContDiff ℝ 1 (powerDistance (2 : ℝ) x0) := by
    have hfun : powerDistance (2 : ℝ) x0 = fun y : E ↦ (1 / (2 : ℝ)) * ‖y - x0‖ ^ (2 : ℝ) := by
      funext y
      rw [powerDistance_apply]
    simpa [hfun] using ((contDiff_norm_sq ℝ).comp hsub).const_smul (1 / (2 : ℝ))
  refine ⟨by norm_num, ftaylorSeries ℝ (powerDistance (2 : ℝ) x0), ?_, ?_⟩
  · -- `ContDiff` on the whole space gives the required Taylor owner on `Set.univ`.
    rw [hasFTaylorSeriesUpToOn_univ_iff]
    exact hcontDiff.ftaylorSeries
  · -- The first Taylor coefficient is exactly the derivative.
    -- Its difference is `innerSL (x - y)`.
    rw [lipschitzOnWith_iff_norm_sub_le]
    intro x hx y hy
    calc
      ‖ftaylorSeries ℝ (powerDistance (2 : ℝ) x0) x 1 -
          ftaylorSeries ℝ (powerDistance (2 : ℝ) x0) y 1‖ =
          ‖fderiv ℝ (powerDistance (2 : ℝ) x0) x -
            fderiv ℝ (powerDistance (2 : ℝ) x0) y‖ := by
              exact ftaylorSeriesCoeffOne_normSub_eq_fderiv_normSub hcontDiff x y
      _ = ‖x - y‖ := by
            rw [powerDistance_two_fderiv_eq, powerDistance_two_fderiv_eq]
            have hlin : innerSL ℝ (x - x0) - innerSL ℝ (y - x0) = innerSL ℝ (x - y) := by
              ext z
              simp [sub_eq_add_neg, innerSL_apply_apply]
            rw [hlin, innerSL_apply_norm]
      _ ≤ (1 : ℝ) * ‖x - y‖ := by
            simp

/-- Helper for Text 4 2 7: the translated cubic power-distance is uniformly convex with modulus
`(1 / 3) * (1 / 2) * r³`. -/
private lemma powerDistance_three_uniformConvexOn_half :
    UniformConvexOn Set.univ
      (uniformConvexPowerModulus (1 / 2 : ℝ) (3 : ℝ))
      (powerDistance (3 : ℝ) x0) := by
  -- Specialize the ambient-inner-product bridge at exponent `3`.
  have hpow : ((3 : ℝ) - 2) = 1 := by norm_num
  simpa [hpow, Real.rpow_one] using
    powerDistanceUniformConvexOnInner x0 (3 : ℝ) (by norm_num)

/-- Helper for Text 4 2 7: the translated quadratic power-distance is uniformly convex with
modulus `(1 / 2) * r²`. -/
private lemma powerDistance_two_uniformConvexOn_one :
    UniformConvexOn Set.univ
      (uniformConvexPowerModulus (1 : ℝ) (2 : ℝ))
      (powerDistance (2 : ℝ) x0) := by
  -- Specialize the ambient-inner-product bridge at `p = 2`.
  have hpow : Real.rpow (1 / 2 : ℝ) ((2 : ℝ) - 2) = (1 : ℝ) := by norm_num
  simpa [hpow] using powerDistanceUniformConvexOnInner x0 (2 : ℝ) (by norm_num)

/-- Helper for Text 4 2 7: any degree-two uniform-convexity witness for the quadratic
power-distance is at most `1`. -/
private lemma powerDistance_two_uniform_witness_le_one [Nontrivial E]
    {σ : ℝ}
    (_hσ : 0 < σ)
    (huniform :
      UniformConvexOn Set.univ
        (uniformConvexPowerModulus σ (2 : ℝ))
        (powerDistance (2 : ℝ) x0)) :
    σ ≤ 1 := by
  -- Test the midpoint inequality on the symmetric pair `x₀ ± (1 / 2)u`.
  rcases (exists_unit_vector : ∃ u : E, ‖u‖ = 1) with ⟨u, hu⟩
  have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) := by norm_num
  have hhalf_sum : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 := by norm_num
  have hmid :=
    huniform.2
      (by simp : x0 - (1 / 2 : ℝ) • u ∈ (Set.univ : Set E))
      (by simp : x0 + (1 / 2 : ℝ) • u ∈ (Set.univ : Set E))
      hhalf_nonneg
      hhalf_nonneg
      hhalf_sum
  have hmidpoint :
      (1 / 2 : ℝ) • (x0 - (1 / 2 : ℝ) • u) + (1 / 2 : ℝ) • (x0 + (1 / 2 : ℝ) • u) = x0 := by
    have hsum : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 := by ring
    calc
      (1 / 2 : ℝ) • (x0 - (1 / 2 : ℝ) • u) + (1 / 2 : ℝ) • (x0 + (1 / 2 : ℝ) • u) =
          (1 / 2 : ℝ) • x0 + (1 / 2 : ℝ) • x0 := by
            simp [sub_eq_add_neg, smul_add, smul_smul, add_assoc, add_left_comm, add_comm]
      _ = x0 := by
            rw [← add_smul, hsum, one_smul]
  have hnorm :
      ‖(x0 - (1 / 2 : ℝ) • u) - (x0 + (1 / 2 : ℝ) • u)‖ = 1 := by
    have hsum : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 := by ring
    calc
      ‖(x0 - (1 / 2 : ℝ) • u) - (x0 + (1 / 2 : ℝ) • u)‖ =
          ‖-((1 / 2 : ℝ) • u + (1 / 2 : ℝ) • u)‖ := by
            simp [sub_eq_add_neg, add_left_comm, add_comm]
      _ = ‖(1 / 2 : ℝ) • u + (1 / 2 : ℝ) • u‖ := norm_neg _
      _ = ‖u‖ := by
            rw [← add_smul, hsum, one_smul]
      _ = 1 := hu
  have hmod : uniformConvexPowerModulus σ (2 : ℝ)
      ‖(x0 - (1 / 2 : ℝ) • u) - (x0 + (1 / 2 : ℝ) • u)‖ = σ / 2 := by
    rw [uniformConvexPowerModulus, hnorm]
    norm_num
    ring
  have hleft : powerDistance (2 : ℝ) x0 (x0 - (1 / 2 : ℝ) • u) = 1 / 8 := by
    rw [powerDistance_apply]
    have hoff : ‖(x0 - (1 / 2 : ℝ) • u) - x0‖ = 1 / 2 := by
      simp [sub_eq_add_neg, add_left_comm, add_comm, norm_neg, norm_smul, hu]
    rw [hoff]
    norm_num
  have hright : powerDistance (2 : ℝ) x0 (x0 + (1 / 2 : ℝ) • u) = 1 / 8 := by
    rw [powerDistance_apply]
    have hoff : ‖(x0 + (1 / 2 : ℝ) • u) - x0‖ = 1 / 2 := by
      simp [sub_eq_add_neg, add_left_comm, add_comm, norm_smul, hu]
    rw [hoff]
    norm_num
  have hcenter : powerDistance (2 : ℝ) x0 x0 = 0 := by
    rw [powerDistance_apply]
    simp
  have hineq := hmid
  rw [hmidpoint, hleft, hright, hcenter, hmod] at hineq
  norm_num at hineq
  nlinarith

/-- Helper for Text 4 2 7: any degree-three uniform-convexity witness for the cubic
power-distance is at most `1 / 2`. -/
private lemma powerDistance_three_uniform_witness_le_half [Nontrivial E]
    {σ : ℝ}
    (_hσ : 0 < σ)
    (huniform :
      UniformConvexOn Set.univ
        (uniformConvexPowerModulus σ (3 : ℝ))
        (powerDistance (3 : ℝ) x0)) :
    σ ≤ 1 / 2 := by
  -- Test the midpoint inequality on the symmetric pair `x₀ ± (1 / 2)u`.
  rcases (exists_unit_vector : ∃ u : E, ‖u‖ = 1) with ⟨u, hu⟩
  have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) := by norm_num
  have hhalf_sum : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 := by norm_num
  have hmid :=
    huniform.2
      (by simp : x0 - (1 / 2 : ℝ) • u ∈ (Set.univ : Set E))
      (by simp : x0 + (1 / 2 : ℝ) • u ∈ (Set.univ : Set E))
      hhalf_nonneg
      hhalf_nonneg
      hhalf_sum
  have hmidpoint :
      (1 / 2 : ℝ) • (x0 - (1 / 2 : ℝ) • u) + (1 / 2 : ℝ) • (x0 + (1 / 2 : ℝ) • u) = x0 := by
    have hsum : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 := by ring
    calc
      (1 / 2 : ℝ) • (x0 - (1 / 2 : ℝ) • u) + (1 / 2 : ℝ) • (x0 + (1 / 2 : ℝ) • u) =
          (1 / 2 : ℝ) • x0 + (1 / 2 : ℝ) • x0 := by
            simp [sub_eq_add_neg, smul_add, smul_smul, add_assoc, add_left_comm, add_comm]
      _ = x0 := by
            rw [← add_smul, hsum, one_smul]
  have hnorm :
      ‖(x0 - (1 / 2 : ℝ) • u) - (x0 + (1 / 2 : ℝ) • u)‖ = 1 := by
    have hsum : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 := by ring
    calc
      ‖(x0 - (1 / 2 : ℝ) • u) - (x0 + (1 / 2 : ℝ) • u)‖ =
          ‖-((1 / 2 : ℝ) • u + (1 / 2 : ℝ) • u)‖ := by
            simp [sub_eq_add_neg, add_left_comm, add_comm]
      _ = ‖(1 / 2 : ℝ) • u + (1 / 2 : ℝ) • u‖ := norm_neg _
      _ = ‖u‖ := by
            rw [← add_smul, hsum, one_smul]
      _ = 1 := hu
  have hmod : uniformConvexPowerModulus σ (3 : ℝ)
      ‖(x0 - (1 / 2 : ℝ) • u) - (x0 + (1 / 2 : ℝ) • u)‖ = σ / 3 := by
    rw [uniformConvexPowerModulus, hnorm]
    norm_num
    ring
  have hleft : powerDistance (3 : ℝ) x0 (x0 - (1 / 2 : ℝ) • u) = 1 / 24 := by
    rw [powerDistance_apply]
    have hoff : ‖(x0 - (1 / 2 : ℝ) • u) - x0‖ = 1 / 2 := by
      simp [sub_eq_add_neg, add_left_comm, add_comm, norm_neg, norm_smul, hu]
    rw [hoff]
    norm_num
  have hright : powerDistance (3 : ℝ) x0 (x0 + (1 / 2 : ℝ) • u) = 1 / 24 := by
    rw [powerDistance_apply]
    have hoff : ‖(x0 + (1 / 2 : ℝ) • u) - x0‖ = 1 / 2 := by
      simp [sub_eq_add_neg, add_left_comm, add_comm, norm_smul, hu]
    rw [hoff]
    norm_num
  have hcenter : powerDistance (3 : ℝ) x0 x0 = 0 := by
    rw [powerDistance_apply]
    simp
  have hineq := hmid
  rw [hmidpoint, hleft, hright, hcenter, hmod] at hineq
  norm_num at hineq
  nlinarith

/-- Helper for Text 4 2 7: every admissible degree-two witness for `powerDistance (2 : ℝ) x₀`
dominates `1`, so the canonical infimum is at least `1`. -/
private lemma powerDistance_two_lipschitzConstant_ge_one [Nontrivial E]
    [HasIteratedFDerivLipschitzConstantOfDegree 2 (powerDistance (2 : ℝ) x0)] :
    (1 : NNReal) ≤ L[2](powerDistance (2 : ℝ) x0) := by
  -- Test the derivative-Lipschitz inequality on a unit direction to force `L ≥ 1`.
  rcases (exists_unit_vector : ∃ u : E, ‖u‖ = 1) with ⟨u, hu⟩
  let S : Set NNReal := {L : NNReal | powerDistance (2 : ℝ) x0 ∈ 𝒞^{1,1}_{L}(Set.univ)}
  change (1 : NNReal) ≤ sInf S
  refine le_csInf ?_ ?_
  · rcases (inferInstance :
      HasIteratedFDerivLipschitzConstantOfDegree 2 (powerDistance (2 : ℝ) x0)).exists_mem with
      ⟨L, hL⟩
    exact ⟨L, hL⟩
  · intro L hL
    have hL' : powerDistance (2 : ℝ) x0 ∈ 𝒞^{1,1}_{L}(Set.univ) := by
      simpa [S] using hL
    have hLip :
        ‖iteratedFDeriv ℝ 1 (powerDistance (2 : ℝ) x0) (x0 + u) -
            iteratedFDeriv ℝ 1 (powerDistance (2 : ℝ) x0) x0‖ ≤
          (L : ℝ) * ‖(x0 + u) - x0‖ := by
      exact
        @HasIteratedFDerivLipschitzConstantOfDegree.norm_sub_le
          E _ _ L 2 (powerDistance (2 : ℝ) x0) hL' (x0 + u) x0
    have hderiv :
        ‖iteratedFDeriv ℝ 1 (powerDistance (2 : ℝ) x0) (x0 + u) -
            iteratedFDeriv ℝ 1 (powerDistance (2 : ℝ) x0) x0‖ = 1 := by
      rw [iteratedFDerivOne_normSub_eq_fderiv_normSub]
      rw [powerDistance_two_fderiv_eq, powerDistance_two_fderiv_eq]
      have hlin : innerSL ℝ ((x0 + u) - x0) - innerSL ℝ (x0 - x0) = innerSL ℝ u := by
        ext z
        simp [sub_eq_add_neg, innerSL_apply_apply]
      rw [hlin, innerSL_apply_norm, hu]
    have hdist : ‖(x0 + u) - x0‖ = 1 := by
      simp [sub_eq_add_neg, add_assoc, hu]
    have hLreal : (1 : ℝ) ≤ L := by
      rw [hderiv, hdist] at hLip
      simpa using hLip
    exact_mod_cast hLreal

/-- Helper for Text 4 2 7: evaluating the cubic second derivative on two directions gives the
explicit ambient bilinear formula. -/
private lemma powerDistance_three_sndFDeriv_apply_apply (x z w : E) :
    (fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0)) x z) w =
      ‖x - x0‖ * inner ℝ z w +
        ‖x - x0‖⁻¹ * inner ℝ (x - x0) z * inner ℝ (x - x0) w := by
  -- Expand the explicit second-derivative model and evaluate the identity and radial terms
  -- separately on the two test directions.
  let u : E := x - x0
  rw [powerDistance_three_sndFDeriv_eq]
  change inner ℝ ((‖u‖ • ContinuousLinearMap.id ℝ E + (‖u‖⁻¹ • innerSL ℝ u).smulRight u) z) w =
    ‖u‖ * inner ℝ z w + ‖u‖⁻¹ * inner ℝ u z * inner ℝ u w
  have huz : inner ℝ x z - inner ℝ x0 z = inner ℝ u z := by
    dsimp [u]
    rw [inner_sub_left]
  simp [u, huz, inner_add_left, inner_smul_left, mul_comm, mul_left_comm]

/-- Helper for Text 4 2 7: the cubic second derivative is symmetric in its two direction
arguments. -/
private lemma powerDistance_three_sndFDeriv_apply_swap (x z w : E) :
    (fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0)) x z) w =
      (fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0)) x w) z := by
  -- The explicit bilinear formula is unchanged when the two directions are swapped.
  rw [powerDistance_three_sndFDeriv_apply_apply, powerDistance_three_sndFDeriv_apply_apply]
  rw [real_inner_comm z w]
  ring

/-- Helper for Text 4 2 7: along one repeated direction, the cubic second derivative reduces to a
Rayleigh-type scalar expression. -/
private lemma powerDistance_three_sndFDeriv_reApplyInnerSelf (x z : E) :
    (fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0)) x z) z =
      ‖x - x0‖ * ‖z‖ ^ (2 : ℕ) + ‖x - x0‖⁻¹ * (inner ℝ (x - x0) z) ^ (2 : ℕ) := by
  -- Specialize the bilinear formula to `w = z`, then rewrite the diagonal inner products as
  -- squares.
  rw [powerDistance_three_sndFDeriv_apply_apply]
  simp [pow_two, mul_comm, mul_assoc]

/-- Helper for Text 4 2 7: for a nonzero direction, the repeated-direction cubic second
derivative factors through the normalized direction with an explicit `‖z‖²` factor. -/
private lemma powerDistanceThreeSndFDerivDiagonalScale {x z : E} (hz : z ≠ 0) :
    (fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0)) x z) z =
      ‖z‖ ^ (2 : ℕ) *
        (‖x - x0‖ + ‖x - x0‖⁻¹ * (inner ℝ (x - x0) (‖z‖⁻¹ • z)) ^ (2 : ℕ)) := by
  -- Normalize the repeated-direction model to the unit direction `‖z‖⁻¹ • z`.
  have hnorm0 : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  calc
    (fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0)) x z) z =
        ‖x - x0‖ * ‖z‖ ^ (2 : ℕ) + ‖x - x0‖⁻¹ * (inner ℝ (x - x0) z) ^ (2 : ℕ) := by
          rw [powerDistance_three_sndFDeriv_reApplyInnerSelf]
    _ =
        ‖z‖ ^ (2 : ℕ) *
          (‖x - x0‖ + ‖x - x0‖⁻¹ * (inner ℝ (x - x0) (‖z‖⁻¹ • z)) ^ (2 : ℕ)) := by
          rw [inner_smul_right]
          field_simp [pow_two, hnorm0]

/-- Helper for Text 4 2 7: a symmetric operator is controlled in norm by a quadratic-form bound.
-/
private lemma symmetricOpNormLeOfQuadraticBound
    {T : E →L[ℝ] E} {s : ℝ}
    (hT : (T : E →ₗ[ℝ] E).IsSymmetric)
    (hs : 0 ≤ s)
    (hquad : ∀ z : E, |inner ℝ (T z) z| ≤ s * ‖z‖ ^ (2 : ℕ)) :
    ‖T‖ ≤ s := by
  -- Normalize the quadratic-form estimate to the Rayleigh quotient on nonzero directions.
  have hbound : ∀ z : E, |T.rayleighQuotient z| ≤ s := by
    intro z
    by_cases hz : z = 0
    · simpa [hz] using hs
    · have hz_pos : 0 < ‖z‖ ^ (2 : ℕ) := by positivity
      rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply, abs_div,
        abs_of_nonneg (by positivity : 0 ≤ ‖z‖ ^ (2 : ℕ))]
      exact (div_le_iff₀ hz_pos).2 (by simpa using hquad z)
  -- The Rayleigh-quotient characterization turns the diagonal bound into an operator bound.
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient T hT]
  exact ciSup_le hbound

/-- Helper for Text 4 2 7: every affine test of the normalized quadratic model lies below the
exact model. -/
private lemma unitDirectionQuadraticModel_affineLe (u e : E) (t : ℝ) :
    (1 - t ^ (2 : ℕ)) * ‖u‖ + 2 * t * inner ℝ u e ≤
      ‖u‖ + ‖u‖⁻¹ * (inner ℝ u e) ^ (2 : ℕ) := by
  by_cases hu : u = 0
  · -- At the origin, both the affine test and the exact model vanish.
    subst u
    simp
  · -- Away from the origin, complete the square after dividing by `‖u‖`.
    have hnorm0 : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
    have hdiff_nonneg :
        0 ≤
          (‖u‖ + ‖u‖⁻¹ * (inner ℝ u e) ^ (2 : ℕ)) -
            ((1 - t ^ (2 : ℕ)) * ‖u‖ + 2 * t * inner ℝ u e) := by
      have hsquare : 0 ≤ (t * ‖u‖ - inner ℝ u e) ^ (2 : ℕ) / ‖u‖ := by
        positivity
      have hrepr :
          (‖u‖ + ‖u‖⁻¹ * (inner ℝ u e) ^ (2 : ℕ)) -
              ((1 - t ^ (2 : ℕ)) * ‖u‖ + 2 * t * inner ℝ u e) =
            (t * ‖u‖ - inner ℝ u e) ^ (2 : ℕ) / ‖u‖ := by
        field_simp [pow_two, hnorm0]
        ring
      simpa [hrepr] using hsquare
    linarith

/-- Helper for Text 4 2 7: for a unit direction, the normalized quadratic model is `2`-Lipschitz.
-/
private lemma unitDirectionQuadraticModel_subLe
    {e u v : E} (he : ‖e‖ = 1) :
    (‖u‖ + ‖u‖⁻¹ * (inner ℝ u e) ^ (2 : ℕ)) -
        (‖v‖ + ‖v‖⁻¹ * (inner ℝ v e) ^ (2 : ℕ)) ≤
      2 * ‖u - v‖ := by
  let t : ℝ := if hu : ‖u‖ = 0 then 0 else inner ℝ u e / ‖u‖
  have htu_abs : |t| ≤ 1 := by
    by_cases hu : ‖u‖ = 0
    · simp [t, hu]
    · have hnorm0 : ‖u‖ ≠ 0 := hu
      have hinner_le : |inner ℝ u e| ≤ ‖u‖ := by
        calc
          |inner ℝ u e| ≤ ‖u‖ * ‖e‖ := abs_real_inner_le_norm u e
          _ = ‖u‖ := by rw [he, mul_one]
      have hu_vec : u ≠ 0 := by
        simpa [norm_eq_zero] using hnorm0
      have hnorm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_vec
      have hinner_le' : |inner ℝ u e| ≤ 1 * ‖u‖ := by
        simpa using hinner_le
      dsimp [t]
      rw [if_neg hu, abs_div, abs_of_nonneg (norm_nonneg _)]
      exact (div_le_iff₀ hnorm_pos).2 hinner_le'
  have hcoeff_nonneg : 0 ≤ 1 - t ^ (2 : ℕ) := by
    have ht_sq : t ^ (2 : ℕ) ≤ 1 := by
      have habs_sq : |t| ^ (2 : ℕ) = t ^ (2 : ℕ) := by rw [sq_abs]
      nlinarith [htu_abs, abs_nonneg t]
    linarith
  have hcoeff_le : (1 - t ^ (2 : ℕ)) + 2 * |t| ≤ 2 := by
    have hsquare : 0 ≤ (1 - |t|) ^ (2 : ℕ) := by positivity
    have habs_sq : |t| ^ (2 : ℕ) = t ^ (2 : ℕ) := by rw [sq_abs]
    nlinarith
  have hu_eq :
      ‖u‖ + ‖u‖⁻¹ * (inner ℝ u e) ^ (2 : ℕ) =
        (1 - t ^ (2 : ℕ)) * ‖u‖ + 2 * t * inner ℝ u e := by
    by_cases hu : ‖u‖ = 0
    · simp [t, hu]
    · have hnorm0 : ‖u‖ ≠ 0 := hu
      dsimp [t]
      rw [if_neg hu]
      field_simp [pow_two, hnorm0]
      ring
  have hv_test :
      (1 - t ^ (2 : ℕ)) * ‖v‖ + 2 * t * inner ℝ v e ≤
        ‖v‖ + ‖v‖⁻¹ * (inner ℝ v e) ^ (2 : ℕ) :=
    unitDirectionQuadraticModel_affineLe v e t
  have hnorm_term :
      (1 - t ^ (2 : ℕ)) * (‖u‖ - ‖v‖) ≤ (1 - t ^ (2 : ℕ)) * ‖u - v‖ :=
    mul_le_mul_of_nonneg_left (norm_sub_norm_le u v) hcoeff_nonneg
  have hinner_term :
      2 * t * inner ℝ (u - v) e ≤ 2 * |t| * ‖u - v‖ := by
    have habs :
        |2 * t * inner ℝ (u - v) e| ≤ 2 * |t| * ‖u - v‖ := by
      calc
        |2 * t * inner ℝ (u - v) e| = |2 * t| * |inner ℝ (u - v) e| := by
              rw [abs_mul]
        _ ≤ |2 * t| * (‖u - v‖ * ‖e‖) := by
              gcongr
              exact abs_real_inner_le_norm (u - v) e
        _ = 2 * |t| * ‖u - v‖ := by
              rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), he]
              ring
    exact le_trans (le_abs_self _) habs
  -- Use the equality at `u` and the universal affine upper bound at `v`.
  calc
    (‖u‖ + ‖u‖⁻¹ * (inner ℝ u e) ^ (2 : ℕ)) -
        (‖v‖ + ‖v‖⁻¹ * (inner ℝ v e) ^ (2 : ℕ)) ≤
        ((1 - t ^ (2 : ℕ)) * ‖u‖ + 2 * t * inner ℝ u e) -
          ((1 - t ^ (2 : ℕ)) * ‖v‖ + 2 * t * inner ℝ v e) := by
            rw [hu_eq]
            linarith
    _ = (1 - t ^ (2 : ℕ)) * (‖u‖ - ‖v‖) + 2 * t * inner ℝ (u - v) e := by
          rw [inner_sub_left]
          ring
    _ ≤ ((1 - t ^ (2 : ℕ)) + 2 * |t|) * ‖u - v‖ := by
          linarith
    _ ≤ 2 * ‖u - v‖ := by
          gcongr

/-- Helper for Text 4 2 7: for a unit direction, the normalized quadratic model has absolute
variation bounded by `2 * ‖u - v‖`. -/
private lemma unitDirectionQuadraticModel_abs_subLe
    {e u v : E} (he : ‖e‖ = 1) :
    |(‖u‖ + ‖u‖⁻¹ * (inner ℝ u e) ^ (2 : ℕ)) -
        (‖v‖ + ‖v‖⁻¹ * (inner ℝ v e) ^ (2 : ℕ))| ≤
      2 * ‖u - v‖ := by
  refine abs_le.2 ?_
  constructor
  · have hvu := unitDirectionQuadraticModel_subLe (e := e) (u := v) (v := u) he
    have hvu' : (‖v‖ + ‖v‖⁻¹ * (inner ℝ v e) ^ (2 : ℕ)) -
        (‖u‖ + ‖u‖⁻¹ * (inner ℝ u e) ^ (2 : ℕ)) ≤
      2 * ‖u - v‖ := by
      simpa [norm_sub_rev] using hvu
    linarith
  · exact unitDirectionQuadraticModel_subLe (e := e) (u := u) (v := v) he

/-- Helper for Text 4 2 7: the cubic diagonal second-derivative gap is bounded by
`2 * ‖x - y‖ * ‖z‖²`. -/
private lemma powerDistanceThreeSndFDerivQuadraticSubLe (x y z : E) :
    |(fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0)) x z) z -
        (fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0)) y z) z| ≤
      2 * ‖x - y‖ * ‖z‖ ^ (2 : ℕ) := by
  -- Route correction: isolate the `‖z‖⁻¹ • z` normalization in one bridge lemma before applying
  -- the already-proved unit-direction model bound.
  by_cases hz : z = 0
  · -- The zero direction makes both diagonal evaluations vanish.
    subst z
    simp
  · -- Normalize to the unit direction `e = ‖z‖⁻¹ • z`, then factor out `‖z‖²`.
    let e : E := ‖z‖⁻¹ • z
    have he : ‖e‖ = 1 := by
      dsimp [e]
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)
    have hmodel :
        |(‖x - x0‖ + ‖x - x0‖⁻¹ * (inner ℝ (x - x0) e) ^ (2 : ℕ)) -
            (‖y - x0‖ + ‖y - x0‖⁻¹ * (inner ℝ (y - x0) e) ^ (2 : ℕ))| ≤
          2 * ‖x - y‖ := by
      have hxy : (x - x0) - (y - x0) = x - y := by
        abel_nf
      simpa [e, hxy] using
        (unitDirectionQuadraticModel_abs_subLe (e := e) (u := x - x0) (v := y - x0) he)
    have hzsq_nonneg : 0 ≤ ‖z‖ ^ (2 : ℕ) := by positivity
    calc
      |(fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0)) x z) z -
          (fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0)) y z) z| =
          |‖z‖ ^ (2 : ℕ) *
              ((‖x - x0‖ + ‖x - x0‖⁻¹ * (inner ℝ (x - x0) e) ^ (2 : ℕ)) -
                (‖y - x0‖ + ‖y - x0‖⁻¹ * (inner ℝ (y - x0) e) ^ (2 : ℕ)))| := by
            rw [powerDistanceThreeSndFDerivDiagonalScale (x0 := x0) (x := x) hz,
              powerDistanceThreeSndFDerivDiagonalScale (x0 := x0) (x := y) hz]
            congr 1
            ring
      _ = ‖z‖ ^ (2 : ℕ) *
            |(‖x - x0‖ + ‖x - x0‖⁻¹ * (inner ℝ (x - x0) e) ^ (2 : ℕ)) -
                (‖y - x0‖ + ‖y - x0‖⁻¹ * (inner ℝ (y - x0) e) ^ (2 : ℕ))| := by
            rw [abs_mul, abs_of_nonneg hzsq_nonneg]
      _ ≤ ‖z‖ ^ (2 : ℕ) * (2 * ‖x - y‖) := by
            gcongr
      _ = 2 * ‖x - y‖ * ‖z‖ ^ (2 : ℕ) := by ring

/-- Helper for Text 4 2 7: the cubic second derivative is globally `2`-Lipschitz in operator
norm. -/
private lemma powerDistanceThreeSndFDerivNormSubLe (x y : E) :
    ‖fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0)) x -
        fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0)) y‖ ≤
      2 * ‖x - y‖ := by
  -- Route correction: rewrite the second-derivative difference once as `innerSL ∘L T`, prove the
  -- ambient operator `T` is symmetric, and then import the diagonal quadratic bound.
  let modelAt : E → E →L[ℝ] E :=
    fun u ↦
      ‖u - x0‖ • ContinuousLinearMap.id ℝ E +
        ((‖u - x0‖)⁻¹ • innerSL ℝ (u - x0)).smulRight (u - x0)
  let T : E →L[ℝ] E := modelAt x - modelAt y
  have hrepr :
      fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0)) x -
          fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0)) y =
        (innerSL ℝ).comp T := by
    ext z w
    simp [T, modelAt, powerDistance_three_sndFDeriv_eq]
    rfl
  have hdiag :
      ∀ z : E,
        inner ℝ (T z) z =
          (fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0)) x z) z -
            (fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0)) y z) z := by
    intro z
    have hreprzz :
        inner ℝ (T z) z =
          (((fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0)) x) -
              (fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0)) y)) z) z := by
      have hreprz :=
        congrArg (fun S : E →L[ℝ] E →L[ℝ] ℝ ↦ S z) hrepr
      have hreprzz :=
        congrArg (fun l : E →L[ℝ] ℝ ↦ l z) hreprz
      simpa [ContinuousLinearMap.comp_apply, innerSL_apply_apply] using hreprzz.symm
    calc
      inner ℝ (T z) z =
          (((fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0)) x) -
              (fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0)) y)) z) z := hreprzz
      _ =
          (fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0)) x z) z -
            (fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0)) y z) z := by
            simp [ContinuousLinearMap.sub_apply]
  have hsymm : (T : E →ₗ[ℝ] E).IsSymmetric := by
    intro z w
    have hreprzw :
        inner ℝ (T z) w =
          (((fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0)) x) -
              (fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0)) y)) z) w := by
      have hreprz :=
        congrArg (fun S : E →L[ℝ] E →L[ℝ] ℝ ↦ S z) hrepr
      have hreprzw :=
        congrArg (fun l : E →L[ℝ] ℝ ↦ l w) hreprz
      simpa [ContinuousLinearMap.comp_apply, innerSL_apply_apply] using hreprzw.symm
    have hreprwz :
        (((fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0)) x) -
            (fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0)) y)) w) z =
          (((innerSL ℝ).comp T) w) z := by
      have hreprw :=
        congrArg (fun S : E →L[ℝ] E →L[ℝ] ℝ ↦ S w) hrepr
      have hreprwz :=
        congrArg (fun l : E →L[ℝ] ℝ ↦ l z) hreprw
      simpa using hreprwz
    calc
      inner ℝ (T z) w =
          (((fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0)) x) -
              (fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0)) y)) z) w := hreprzw
      _ =
          (((fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0)) x) -
              (fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0)) y)) w) z := by
            simp [ContinuousLinearMap.sub_apply, powerDistance_three_sndFDeriv_apply_swap]
      _ = (((innerSL ℝ).comp T) w) z := hreprwz
      _ = inner ℝ z (T w) := by
            simp [ContinuousLinearMap.comp_apply, innerSL_apply_apply, real_inner_comm]
  have hquad :
      ∀ z : E, |inner ℝ (T z) z| ≤ (2 * ‖x - y‖) * ‖z‖ ^ (2 : ℕ) := by
    intro z
    rw [hdiag z]
    exact powerDistanceThreeSndFDerivQuadraticSubLe (x0 := x0) (x := x) (y := y) (z := z)
  have hTnorm : ‖T‖ ≤ 2 * ‖x - y‖ :=
    symmetricOpNormLeOfQuadraticBound hsymm (by positivity) hquad
  rw [hrepr]
  refine le_trans ?_ hTnorm
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
  intro z
  calc
    ‖((innerSL ℝ).comp T) z‖ = ‖innerSL ℝ (T z)‖ := by
      rfl
    _ = ‖T z‖ := by
      exact innerSL_apply_norm (𝕜 := ℝ) (x := T z)
    _ ≤ ‖T‖ * ‖z‖ := by
      exact T.le_opNorm z

/-- Helper for Text 4 2 7: the cubic power-distance has the explicit first derivative
everywhere. -/
private lemma powerDistance_three_hasFDerivAt (x : E) :
    HasFDerivAt (powerDistance (3 : ℝ) x0)
      (‖x - x0‖ • innerSL ℝ (x - x0)) x := by
  -- Differentiate `‖x - x₀‖³` directly and scale by `1 / 3`.
  have hsub : HasFDerivAt (fun y : E ↦ y - x0) (1 : E →L[ℝ] E) x := by
    simpa using (hasFDerivAt_id x).sub_const x0
  have hpow :
      HasFDerivAt (fun y : E ↦ ‖y - x0‖ ^ (3 : ℝ))
        (((3 : ℝ) * ‖x - x0‖ ^ ((3 : ℝ) - 2)) • innerSL ℝ (x - x0)) x := by
    simpa using (hasFDerivAt_norm_rpow (x - x0) (by norm_num : (1 : ℝ) < 3)).comp x hsub
  have hscaled :
      HasFDerivAt (fun y : E ↦ (1 / (3 : ℝ)) * ‖y - x0‖ ^ (3 : ℝ))
        ((1 / (3 : ℝ)) • (((3 : ℝ) * ‖x - x0‖ ^ ((3 : ℝ) - 2)) • innerSL ℝ (x - x0))) x := by
    simpa using hpow.const_mul (1 / (3 : ℝ))
  have hfun :
      powerDistance (3 : ℝ) x0 = fun y : E ↦ ‖y - x0‖ ^ (3 : ℝ) * (1 / (3 : ℝ)) := by
    funext y
    rw [powerDistance_apply, mul_comm]
  have hpowShift : ((3 : ℝ) - 2) = 1 := by norm_num
  simpa [hfun, one_div, Real.rpow_one, smul_smul, mul_assoc, mul_comm, mul_left_comm, hpowShift]
    using hscaled

/-- Helper for Text 4 2 7: the cubic power-distance is twice continuously differentiable. -/
private lemma powerDistanceThreeContDiffTwo :
    ContDiff ℝ 2 (powerDistance (3 : ℝ) x0) := by
  -- Package the explicit first derivative, then use the global second-derivative Lipschitz bound
  -- to obtain continuity of the derivative map's derivative.
  refine
    (contDiff_succ_iff_fderiv (𝕜 := ℝ) (n := (1 : ℕ∞))
      (f := powerDistance (3 : ℝ) x0)).2 ?_
  refine ⟨?_, ?_, ?_⟩
  · -- The cubic power-distance is differentiable everywhere by the explicit derivative formula.
    intro x
    exact (powerDistance_three_hasFDerivAt (x0 := x0) x).differentiableAt
  · -- The analytic side condition is vacuous because `1 ≠ ∞`.
    intro hω
    cases hω
  · -- The derivative map is differentiable with a globally Lipschitz derivative.
    refine
      (contDiff_one_iff_fderiv (𝕜 := ℝ) (f := fderiv ℝ (powerDistance (3 : ℝ) x0))).2 ?_
    refine ⟨?_, ?_⟩
    · -- Differentiate the explicit derivative field `x ↦ innerSL (‖x - x₀‖ • (x - x₀))`.
      have hfun :
          fderiv ℝ (powerDistance (3 : ℝ) x0) =
            fun y : E ↦ (innerSL ℝ) (‖y - x0‖ • (y - x0)) := by
        funext y
        ext z
        simp [powerDistance_three_fderiv_eq]
      intro x
      have hderivAt :
          HasFDerivAt (fderiv ℝ (powerDistance (3 : ℝ) x0))
            ((innerSL ℝ).comp
              (‖x - x0‖ • ContinuousLinearMap.id ℝ E +
                ((‖x - x0‖)⁻¹ • innerSL ℝ (x - x0)).smulRight (x - x0))) x := by
        convert ((innerSL ℝ).hasFDerivAt.comp x (translated_norm_smul_sub_hasFDerivAt x0 x))
          using 1
      exact hderivAt.differentiableAt
    · -- The second derivative map is globally Lipschitz, hence continuous.
      have hLip :
          LipschitzWith (2 : NNReal)
            (fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0))) := by
        rw [lipschitzWith_iff_norm_sub_le]
        intro x y
        simpa using powerDistanceThreeSndFDerivNormSubLe (x0 := x0) (x := x) (y := y)
      exact hLip.continuous

/-- Helper for Text 4 2 7: the cubic power-distance belongs to
`𝒞^{2,2}_{2}(Set.univ)`. -/
private lemma powerDistance_three_mem_taylorCoeffLipschitzClass_two :
    powerDistance (3 : ℝ) x0 ∈ 𝒞^{2,2}_{(2 : NNReal)}(Set.univ) := by
  -- Route correction: package the explicit ambient second-derivative bound directly, without
  -- passing through the completeness-dependent `C22[2]` owner from Lemma 4.2.4.
  refine ⟨by norm_num, ftaylorSeries ℝ (powerDistance (3 : ℝ) x0), ?_, ?_⟩
  · -- The direct `C²` proof supplies the whole-space Taylor witness.
    rw [hasFTaylorSeriesUpToOn_univ_iff]
    exact powerDistanceThreeContDiffTwo (x0 := x0) |>.ftaylorSeries
  · -- The second Taylor coefficient is exactly the second Fréchet derivative in norm.
    rw [lipschitzOnWith_iff_norm_sub_le]
    intro x hx y hy
    calc
      ‖ftaylorSeries ℝ (powerDistance (3 : ℝ) x0) x 2 -
          ftaylorSeries ℝ (powerDistance (3 : ℝ) x0) y 2‖ =
          ‖fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0)) x -
              fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0)) y‖ := by
              exact
                ftaylorSeriesCoeffTwo_normSub_eq_sndFDeriv_normSub
                  (powerDistanceThreeContDiffTwo (x0 := x0)) x y
      _ ≤ (2 : ℝ) * ‖x - y‖ := powerDistanceThreeSndFDerivNormSubLe (x0 := x0) (x := x) (y := y)

/-- Helper for Text 4 2 7: along a unit direction, the cubic second-derivative gap evaluates to
`2`. -/
private lemma powerDistance_three_iteratedFDeriv_gap_on_unit {u : E} (hu : ‖u‖ = 1) :
    (iteratedFDeriv ℝ 2 (powerDistance (3 : ℝ) x0) (x0 + u) -
        iteratedFDeriv ℝ 2 (powerDistance (3 : ℝ) x0) x0) ![u, u] = 2 := by
  -- Evaluate the explicit second-derivative model at `x₀ + u` and at the center, then subtract.
  have happly :
      ((fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0)) (x0 + u)) u) u -
          ((fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0)) x0) u) u = 2 := by
    rw [powerDistance_three_sndFDeriv_eq, powerDistance_three_sndFDeriv_eq]
    have hshift : (x0 + u) - x0 = u := by simp
    have hcenter :
        (((innerSL ℝ).comp
            (‖x0 - x0‖ • ContinuousLinearMap.id ℝ E +
              ((‖x0 - x0‖)⁻¹ • innerSL ℝ (x0 - x0)).smulRight (x0 - x0))) u) u = 0 := by
      -- The translated cubic Hessian vanishes at the center because both model terms are zero.
      simp
    have hpoint :
        (((innerSL ℝ).comp
            (‖(x0 + u) - x0‖ • ContinuousLinearMap.id ℝ E +
              ((‖(x0 + u) - x0‖)⁻¹ • innerSL ℝ ((x0 + u) - x0)).smulRight ((x0 + u) - x0))) u)
            u = 2 := by
      -- At `x₀ + u`, the identity part and the radial rank-one part each contribute `1`.
      simp [hshift, hu]
      norm_num
    calc
      (((innerSL ℝ).comp
            (‖(x0 + u) - x0‖ • ContinuousLinearMap.id ℝ E +
              ((‖(x0 + u) - x0‖)⁻¹ • innerSL ℝ ((x0 + u) - x0)).smulRight ((x0 + u) - x0))) u)
            u -
          (((innerSL ℝ).comp
            (‖x0 - x0‖ • ContinuousLinearMap.id ℝ E +
              ((‖x0 - x0‖)⁻¹ • innerSL ℝ (x0 - x0)).smulRight (x0 - x0))) u)
            u = 2 - 0 := by
              rw [hpoint, hcenter]
      _ = 2 := by norm_num
  simpa only [iteratedFDeriv_two_apply, ContinuousMultilinearMap.sub_apply] using happly

/-- Helper for Text 4 2 7: the sharp cubic lower bound is the remaining source-faithful blocker.
-/
private lemma powerDistance_three_lipschitzConstant_ge_two [Nontrivial E]
    [HasIteratedFDerivLipschitzConstantOfDegree 3 (powerDistance (3 : ℝ) x0)] :
    (2 : NNReal) ≤ L[3](powerDistance (3 : ℝ) x0) := by
  -- Evaluate the global owner inequality on a unit direction and read the exact gap through the
  -- multilinear operator norm estimate.
  rcases (exists_unit_vector : ∃ u : E, ‖u‖ = 1) with ⟨u, hu⟩
  let S : Set NNReal := {L : NNReal | powerDistance (3 : ℝ) x0 ∈ 𝒞^{2,2}_{L}(Set.univ)}
  change (2 : NNReal) ≤ sInf S
  refine le_csInf ?_ ?_
  · rcases (inferInstance :
      HasIteratedFDerivLipschitzConstantOfDegree 3 (powerDistance (3 : ℝ) x0)).exists_mem with
      ⟨L, hL⟩
    exact ⟨L, hL⟩
  · intro L hL
    have hL' : powerDistance (3 : ℝ) x0 ∈ 𝒞^{2,2}_{L}(Set.univ) := by
      simpa [S] using hL
    have hLip :
        ‖iteratedFDeriv ℝ 2 (powerDistance (3 : ℝ) x0) (x0 + u) -
            iteratedFDeriv ℝ 2 (powerDistance (3 : ℝ) x0) x0‖ ≤
          (L : ℝ) * ‖(x0 + u) - x0‖ := by
      exact
        @HasIteratedFDerivLipschitzConstantOfDegree.norm_sub_le
          E _ _ L 3 (powerDistance (3 : ℝ) x0) hL' (x0 + u) x0
    let D :=
      iteratedFDeriv ℝ 2 (powerDistance (3 : ℝ) x0) (x0 + u) -
        iteratedFDeriv ℝ 2 (powerDistance (3 : ℝ) x0) x0
    have hD : D ![u, u] = 2 := by
      simpa [D] using powerDistance_three_iteratedFDeriv_gap_on_unit x0 hu
    have hnorm_eval :
        ‖D ![u, u]‖ ≤ ‖D‖ := by
      calc
        ‖D ![u, u]‖ ≤ ‖D‖ * ∏ i, ‖![u, u] i‖ := ContinuousMultilinearMap.le_opNorm D ![u, u]
        _ = ‖D‖ := by simp [hu]
    have htwo_le_normD : (2 : ℝ) ≤ ‖D‖ := by
      rw [hD] at hnorm_eval
      norm_num at hnorm_eval
      exact hnorm_eval
    have hdist : ‖(x0 + u) - x0‖ = 1 := by
      simp [sub_eq_add_neg, hu]
    have hLreal : (2 : ℝ) ≤ L := by
      have : (2 : ℝ) ≤ (L : ℝ) * ‖(x0 + u) - x0‖ := le_trans htwo_le_normD hLip
      rw [hdist] at this
      simpa using this
    exact_mod_cast hLreal

end Helpers

section FiniteLipschitz

variable (x0 : E)

instance :
    HasIteratedFDerivLipschitzConstantOfDegree 2 (powerDistance (2 : ℝ) x0) := by
  -- Package the explicit quadratic derivative formula into the canonical degree-two owner.
  exact HasIteratedFDerivLipschitzConstantOfDegree.of_constant
    (powerDistance_two_mem_taylorCoeffLipschitzClass_one x0)

instance :
    HasIteratedFDerivLipschitzConstantOfDegree 3 (powerDistance (3 : ℝ) x0) := by
  -- Reuse the explicit cubic Taylor-coefficient witness.
  exact HasIteratedFDerivLipschitzConstantOfDegree.of_constant
    (powerDistance_three_mem_taylorCoeffLipschitzClass_two x0)

end FiniteLipschitz

section ExactValues

variable [Nontrivial E]
variable (x0 : E)

instance :
    HasUniformConvexityParameterOfDegree 2 (powerDistance (2 : ℝ) x0) := by
  refine ⟨?_, ?_⟩
  · -- The sharp lower witness comes from the ambient-inner-product specialization of
    -- Lemma 4.2.3.
    have hpos : 0 < (1 : ℝ) := by positivity
    refine ⟨1, hpos, powerDistance_two_uniformConvexOn_one x0⟩
  · -- The same antipodal unit test bounds all admissible witnesses by `1`.
    refine ⟨1, ?_⟩
    intro σ hσ
    exact powerDistance_two_uniform_witness_le_one x0 hσ.1 hσ.2

instance :
    HasUniformConvexityParameterOfDegree 3 (powerDistance (3 : ℝ) x0) := by
  refine ⟨?_, ?_⟩
  · -- Specialize Lemma 4.2.3 at exponent `3`.
    have hpos : 0 < (1 / 2 : ℝ) := by positivity
    refine ⟨1 / 2, hpos, powerDistance_three_uniformConvexOn_half x0⟩
  · -- The antipodal midpoint computation is also the sharp cubic upper-bound test.
    refine ⟨1 / 2, ?_⟩
    intro σ hσ
    exact powerDistance_three_uniform_witness_le_half x0 hσ.1 hσ.2

instance :
    HasPositiveIteratedFDerivLipschitzConstantOfDegree 2 (powerDistance (2 : ℝ) x0) := by
  -- Route correction: positivity is a thin corollary of the exact lower bound `L[2] ≥ 1`.
  refine ⟨?_⟩
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    (by exact_mod_cast powerDistance_two_lipschitzConstant_ge_one x0)

instance :
    HasPositiveIteratedFDerivLipschitzConstantOfDegree 3 (powerDistance (3 : ℝ) x0) := by
  -- Route correction: positivity is a thin corollary of the exact lower bound `L[3] ≥ 2`.
  refine ⟨?_⟩
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2)
    (by exact_mod_cast powerDistance_three_lipschitzConstant_ge_two x0)

-- Proof sketch: identify the Hessian of `powerDistance (2 : ℝ) x₀` with the identity map, so the
-- derivative-Lipschitz constant from Definition 4.2.11 is exactly `1`.
/-- Text 4 2 7 (1): on a nontrivial real inner-product space, for
`d₂ = powerDistance (2 : ℝ) x₀`, the degree-`2` Lipschitz constant
satisfies `L₂(d₂) = 1`. -/
theorem powerDistance_two_lipschitzConstant :
    L[2](powerDistance (2 : ℝ) x0) = 1 := by
  -- The local quadratic witness `1` gives the upper bound on the canonical infimum.
  have hupper : L[2](powerDistance (2 : ℝ) x0) ≤ 1 := by
    let S : Set NNReal := {L : NNReal | powerDistance (2 : ℝ) x0 ∈ 𝒞^{1,1}_{L}(Set.univ)}
    change sInf S ≤ 1
    refine csInf_le ?_ ?_
    · exact ⟨0, by intro L hL; exact zero_le L⟩
    · simpa [S] using powerDistance_two_mem_taylorCoeffLipschitzClass_one x0
  -- The unit-direction test gives the matching lower bound.
  exact le_antisymm hupper (powerDistance_two_lipschitzConstant_ge_one x0)

-- Proof sketch: compute the Bregman remainder of `powerDistance (2 : ℝ) x₀` exactly as
-- `(1 / 2) * ‖y - x‖²`, then compare with the definition of
-- `uniformConvexityParameterOfDegree`.
/-- Text 4 2 7 (2): on a nontrivial real inner-product space, for
`d₂ = powerDistance (2 : ℝ) x₀`, the degree-`2` uniform-convexity
parameter satisfies `σ₂(d₂) = 1`. -/
theorem powerDistance_two_uniformConvexityParameter :
    σ[2](powerDistance (2 : ℝ) x0) = 1 := by
  -- The explicit owner witness `σ = 1` gives the lower bound on the canonical supremum.
  have hpos : 0 < (1 : ℝ) := by positivity
  have hlower : (1 : ℝ) ≤ σ[2](powerDistance (2 : ℝ) x0) :=
    HasUniformConvexityParameterOfDegree.le_uniformConvexityParameterOfDegree
      hpos (powerDistance_two_uniformConvexOn_one x0)
  -- Every admissible witness is at most `1`, so the supremum is at most `1`.
  have hupper : σ[2](powerDistance (2 : ℝ) x0) ≤ 1 := by
    let S : Set ℝ := {σ : ℝ |
      0 < σ ∧
        UniformConvexOn Set.univ
          (uniformConvexPowerModulus σ (2 : ℝ))
          (powerDistance (2 : ℝ) x0)}
    change sSup S ≤ 1
    have hnonempty : Set.Nonempty S := HasUniformConvexityParameterOfDegree.nonempty
    refine csSup_le hnonempty ?_
    intro σ hσ
    exact powerDistance_two_uniform_witness_le_one x0 hσ.1 hσ.2
  linarith

-- Proof sketch: combine the previous two identities with the definition
-- `γ₂(d₂) = σ₂(d₂) / L₂(d₂)`.
/-- Text 4 2 7 (3): on a nontrivial real inner-product space, for
`d₂ = powerDistance (2 : ℝ) x₀`, the degree-`2` condition number
satisfies `γ₂(d₂) = 1`. -/
theorem powerDistance_two_conditionNumber :
    γ[2](powerDistance (2 : ℝ) x0) = 1 := by
  -- Expand the definition and substitute the exact quadratic constants.
  rw [conditionNumberOfDegree_eq_ratio, powerDistance_two_uniformConvexityParameter,
    powerDistance_two_lipschitzConstant]
  norm_num

-- Proof sketch: use the cubic Hessian estimate from Lemma 4.2.4, applied to the translated cubic
-- power function centered at `x₀`, to identify the optimal degree-`3` derivative-Lipschitz
-- constant as `2`.
/-- Text 4 2 7 (4): on a nontrivial real inner-product space, for
`d₃ = powerDistance (3 : ℝ) x₀`, the degree-`3` Lipschitz constant
satisfies `L₃(d₃) = 2`. -/
theorem powerDistance_three_lipschitzConstant :
    L[3](powerDistance (3 : ℝ) x0) = 2 := by
  -- The local cubic witness `2` gives the upper bound on the canonical infimum.
  have hupper : L[3](powerDistance (3 : ℝ) x0) ≤ 2 := by
    let S : Set NNReal := {L : NNReal | powerDistance (3 : ℝ) x0 ∈ 𝒞^{2,2}_{L}(Set.univ)}
    change sInf S ≤ 2
    refine csInf_le ?_ ?_
    · exact ⟨0, by intro L hL; exact zero_le L⟩
    · simpa [S] using powerDistance_three_mem_taylorCoeffLipschitzClass_two x0
  -- The sharp unit-direction test gives the matching lower bound.
  exact le_antisymm hupper (powerDistance_three_lipschitzConstant_ge_two x0)

-- Proof sketch: apply the monotonicity estimate for the cubic power function from the preceding
-- chapter lemmas and translate it into the first-order lower support inequality defining
-- `uniformConvexityParameterOfDegree`.
/-- Text 4 2 7 (5): on a nontrivial real inner-product space, for
`d₃ = powerDistance (3 : ℝ) x₀`, the degree-`3` uniform-convexity
parameter satisfies `σ₃(d₃) = 1 / 2`. -/
theorem powerDistance_three_uniformConvexityParameter :
    σ[3](powerDistance (3 : ℝ) x0) = 1 / 2 := by
  -- The specialized cubic owner witness gives the lower bound `1 / 2 ≤ σ[3]`.
  have hpos : 0 < (1 / 2 : ℝ) := by positivity
  have hlower : (1 / 2 : ℝ) ≤ σ[3](powerDistance (3 : ℝ) x0) :=
    HasUniformConvexityParameterOfDegree.le_uniformConvexityParameterOfDegree
      hpos (powerDistance_three_uniformConvexOn_half x0)
  -- The antipodal midpoint test bounds every admissible witness by `1 / 2`.
  have hupper : σ[3](powerDistance (3 : ℝ) x0) ≤ 1 / 2 := by
    let S : Set ℝ := {σ : ℝ |
      0 < σ ∧
        UniformConvexOn Set.univ
          (uniformConvexPowerModulus σ (3 : ℝ))
          (powerDistance (3 : ℝ) x0)}
    change sSup S ≤ 1 / 2
    have hnonempty : Set.Nonempty S := HasUniformConvexityParameterOfDegree.nonempty
    refine csSup_le hnonempty ?_
    intro σ hσ
    exact powerDistance_three_uniform_witness_le_half x0 hσ.1 hσ.2
  linarith

-- Proof sketch: combine the cubic values of `σ₃` and `L₃` with the definition
-- `γ₃(d₃) = σ₃(d₃) / L₃(d₃)`.
/-- Text 4 2 7 (6): on a nontrivial real inner-product space, for
`d₃ = powerDistance (3 : ℝ) x₀`, the degree-`3` condition number
satisfies `γ₃(d₃) = 1 / 4`. -/
theorem powerDistance_three_conditionNumber :
    γ[3](powerDistance (3 : ℝ) x0) = 1 / 4 := by
  -- Expand the definition and substitute the exact cubic constants.
  rw [conditionNumberOfDegree_eq_ratio, powerDistance_three_uniformConvexityParameter,
    powerDistance_three_lipschitzConstant]
  norm_num

end ExactValues
