/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Text_4_2_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Lemma 4.2.4 lies in the Chapter 4 norm-power / Hessian-Lipschitz domain on real Hilbert spaces.

Sampled owner-style declarations:
* `powerDistance` in `Text_4_2_6`
* `hessian` in `Chap01/Definition_1_4_16`
* `HasLipschitzContinuousHessian` in `Definition_4_2_7`
* `HasLipschitzContinuousHessian.norm_sub_le` in `Definition_4_2_7`

Best owner abstraction:
* core/canonical: the global Hessian-Lipschitz owner
  `HasLipschitzContinuousHessian L (powerDistance p x₀)`, written on theorem surfaces as
  `powerDistance p x₀ ∈ C22[L]`

Primitive data:
* the center `x₀ : E`
* the canonical cubic power function `powerDistance (3 : ℝ) x₀`

Derived API:
* the owner membership `powerDistance (3 : ℝ) x₀ ∈ C22[2]`
* the zero-centered specialization `powerDistance (3 : ℝ) (0 : E) ∈ C22[2]`
* the pointwise Hessian estimate obtained from
  `HasLipschitzContinuousHessian.norm_sub_le`

Source/core/bridge triage:
* source-facing: the textbook Hessian estimate for `d₃(x) = (1 / 3) * ‖x‖³`
* core/canonical: the owner assertion
  `powerDistance (3 : ℝ) x₀ ∈ C22[(2 : NNReal)]`
* bridge/view: specialization to `x₀ = 0` and evaluation of the owner inequality at points `x`
  and `y`

The local definition `d3` duplicated the earlier chapter owner `powerDistance`; this file reuses
that owner directly, lifts the Hessian-Lipschitz statement to the intrinsic center parameter `x₀`,
and keeps the textbook zero-centered estimate as a thin specialization.
-/

section
omit [CompleteSpace E]

/-- Helper for Lemma 4.2.4: away from the origin, the derivative of the norm is the normalized
inner-product functional. -/
private theorem fderiv_norm_eq_inv_smul_innerSL {x : E} (hx : x ≠ 0) :
    fderiv ℝ (fun y : E ↦ ‖y‖) x = ‖x‖⁻¹ • innerSL ℝ x := by
  have hdiff : DifferentiableAt ℝ (fun y : E ↦ ‖y‖) x :=
    DifferentiableAt.norm (𝕜 := ℝ) (f := fun y : E ↦ y) (x := x) differentiableAt_id hx
  have hsq1 :
      HasFDerivAt (fun y : E ↦ ‖y‖ * ‖y‖)
        (‖x‖ • fderiv ℝ (fun y : E ↦ ‖y‖) x + ‖x‖ • fderiv ℝ (fun y : E ↦ ‖y‖) x) x := by
    -- Differentiate `‖y‖ * ‖y‖` through the product rule.
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

end

section
omit [CompleteSpace E]

/-- Helper for Lemma 4.2.4: away from the origin, the derivative of `z ↦ ‖z‖ • z` is the sum of
the scalar identity part and the normalized rank-one part. -/
private theorem hasFDerivAt_norm_smul_id {x : E} (hx : x ≠ 0) :
    HasFDerivAt (fun y : E ↦ ‖y‖ • y)
      (‖x‖ • ContinuousLinearMap.id ℝ E + (‖x‖⁻¹ • innerSL ℝ x).smulRight x) x := by
  have hdiff : DifferentiableAt ℝ (fun y : E ↦ ‖y‖) x :=
    DifferentiableAt.norm (𝕜 := ℝ) (f := fun y : E ↦ y) (x := x) differentiableAt_id hx
  have hnorm : HasFDerivAt (fun y : E ↦ ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
    -- Replace the derivative of the norm by the normalized inner-product functional.
    simpa [fderiv_norm_eq_inv_smul_innerSL hx] using hdiff.hasFDerivAt
  -- Then differentiate the scalar-vector product `‖y‖ • y`.
  simpa using hnorm.smul (hasFDerivAt_id x)

end

section
omit [CompleteSpace E]

/-- Helper for Lemma 4.2.4: at the origin, `z ↦ ‖z‖ • z` has derivative `0`. -/
private theorem hasFDerivAt_norm_smul_id_zero :
    HasFDerivAt (fun y : E ↦ ‖y‖ • y) (0 : E →L[ℝ] E) 0 := by
  -- The map vanishes quadratically at the origin, so its derivative there is zero.
  have hbigO :
      (fun y : E ↦ ‖y‖ • y) =O[nhds (0 : E)] fun y ↦ ‖y - (0 : E)‖ ^ (2 : ℕ) := by
    refine Asymptotics.isBigO_iff'.2 ?_
    refine ⟨1, by positivity, ?_⟩
    filter_upwards with y
    simp only [norm_smul, norm_norm, Real.norm_of_nonneg (sq_nonneg _)]
    simp [pow_two, mul_comm]
  exact hbigO.hasFDerivAt (by norm_num)

end

/-- Helper for Lemma 4.2.4: differentiating the translated cubic gradient gives the explicit
Hessian formula. -/
private theorem powerDistance_three_gradient_eq (x0 : E) :
    gradient (powerDistance (3 : ℝ) x0) = fun y : E ↦ ‖y - x0‖ • (y - x0) := by
  -- Specialize the general power-distance gradient formula to the cubic case.
  apply gradient_eq
  intro y
  simpa [show (3 : ℝ) - 2 = 1 by norm_num, Real.rpow_one] using
    hasGradientAt_powerDistance (E := E) (p := (3 : ℝ)) (by norm_num) x0 y

section
omit [CompleteSpace E]

/-- Helper for Lemma 4.2.4: translating the origin-centered quadratic map to the center `x0`
keeps derivative `0` at the center. -/
private theorem translated_norm_smul_id_center_comp (x0 : E) :
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

end

section
omit [CompleteSpace E]

private theorem hasFDerivAt_powerDistance_three_gradient (x0 x : E) :
    HasFDerivAt (fun y : E ↦ ‖y - x0‖ • (y - x0))
      (‖x - x0‖ • ContinuousLinearMap.id ℝ E +
        ((‖x - x0‖)⁻¹ • innerSL ℝ (x - x0)).smulRight (x - x0)) x := by
  -- Compose the origin-centered derivative model with the translation `y ↦ y - x0`.
  by_cases hx : x = x0
  · -- At the center, the translated map lands at `0`, so the derivative collapses to `0`.
    subst x
    simpa using translated_norm_smul_id_center_comp x0
  · -- Away from the center, the origin-centered explicit derivative formula applies directly.
    have hsub : HasFDerivAt (fun y : E ↦ y - x0) (1 : E →L[ℝ] E) x := by
      simpa using (hasFDerivAt_id x).sub_const x0
    have houter :
        HasFDerivAt (fun z : E ↦ ‖z‖ • z)
          (‖x - x0‖ • ContinuousLinearMap.id ℝ E +
            ((‖x - x0‖)⁻¹ • innerSL ℝ (x - x0)).smulRight (x - x0)) (x - x0) :=
      hasFDerivAt_norm_smul_id (by simpa [sub_eq_zero] using hx)
    simpa [Function.comp_def] using (houter.comp x hsub)

end

private theorem powerDistance_three_hessian_formula (x0 x : E) :
    hessian (powerDistance (3 : ℝ) x0) x =
      ‖x - x0‖ • ContinuousLinearMap.id ℝ E +
        ((‖x - x0‖)⁻¹ • innerSL ℝ (x - x0)).smulRight (x - x0) := by
  -- Rewrite the Hessian as the derivative of the gradient map and insert the explicit model.
  rw [hessian, powerDistance_three_gradient_eq x0]
  exact (hasFDerivAt_powerDistance_three_gradient x0 x).fderiv

section
omit [CompleteSpace E]

/-- Helper for Lemma 4.2.4: the cubic power-distance has the explicit first derivative
everywhere. -/
private theorem powerDistance_three_hasFDerivAt (x0 x : E) :
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
  simpa [hfun, one_div, Real.rpow_one, smul_smul, mul_assoc, mul_comm, mul_left_comm,
    show ((3 : ℝ) - 2) = 1 by norm_num] using hscaled

end

section
omit [CompleteSpace E]

/-- Helper for Lemma 4.2.4: the cubic power-distance derivative is the Riesz image of
`‖x - x₀‖ • (x - x₀)`. -/
private theorem powerDistance_three_fderiv_eq (x0 x : E) :
    fderiv ℝ (powerDistance (3 : ℝ) x0) x =
      ‖x - x0‖ • innerSL ℝ (x - x0) := by
  -- Read off the Fréchet derivative from the explicit first-derivative theorem.
  exact (powerDistance_three_hasFDerivAt x0 x).fderiv

end

section
omit [CompleteSpace E]

/-- Helper for Lemma 4.2.4: the cubic second derivative is the `innerSL` image of the translated
`z ↦ ‖z‖ • z` derivative model. -/
private theorem powerDistance_three_sndFDeriv_eq (x0 x : E) :
    fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0)) x =
      (innerSL ℝ).comp
        (‖x - x0‖ • ContinuousLinearMap.id ℝ E +
          ((‖x - x0‖)⁻¹ • innerSL ℝ (x - x0)).smulRight (x - x0)) := by
  -- Rewrite the first derivative as `innerSL ∘ (fun y ↦ ‖y - x₀‖ • (y - x₀))`.
  have hfun :
      fderiv ℝ (powerDistance (3 : ℝ) x0) =
        fun y : E ↦ (innerSL ℝ) (‖y - x0‖ • (y - x0)) := by
    funext y
    ext z
    simp [powerDistance_three_fderiv_eq]
  rw [hfun]
  -- Then differentiate through the translated vector-field model.
  exact
    ((innerSL ℝ).hasFDerivAt.comp x (hasFDerivAt_powerDistance_three_gradient x0 x)).fderiv

/-- Helper for Lemma 4.2.4: evaluating the cubic second derivative on two directions yields the
explicit bilinear model. -/
private theorem powerDistance_three_sndFDeriv_apply_apply (x0 x z w : E) :
    (fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0)) x z) w =
      ‖x - x0‖ * inner ℝ z w +
        ‖x - x0‖⁻¹ * inner ℝ (x - x0) z * inner ℝ (x - x0) w := by
  -- Expand the second-derivative model and evaluate the identity and radial terms separately.
  let u : E := x - x0
  rw [powerDistance_three_sndFDeriv_eq]
  change inner ℝ ((‖u‖ • ContinuousLinearMap.id ℝ E + (‖u‖⁻¹ • innerSL ℝ u).smulRight u) z) w =
    ‖u‖ * inner ℝ z w + ‖u‖⁻¹ * inner ℝ u z * inner ℝ u w
  have huz : inner ℝ x z - inner ℝ x0 z = inner ℝ u z := by
    dsimp [u]
    rw [inner_sub_left]
  simp [u, huz, inner_add_left, inner_smul_left, mul_comm, mul_left_comm]

/-- Helper for Lemma 4.2.4: the cubic second derivative is symmetric in its two direction
arguments. -/
private theorem powerDistance_three_sndFDeriv_apply_swap (x0 x z w : E) :
    (fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0)) x z) w =
      (fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0)) x w) z := by
  -- Swap the two directional arguments in the explicit bilinear formula.
  rw [powerDistance_three_sndFDeriv_apply_apply, powerDistance_three_sndFDeriv_apply_apply]
  rw [real_inner_comm z w]
  ring

/-- Helper for Lemma 4.2.4: along one repeated direction, the cubic second derivative reduces to
a Rayleigh-type scalar expression. -/
private theorem powerDistance_three_sndFDeriv_reApplyInnerSelf (x0 x z : E) :
    (fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0)) x z) z =
      ‖x - x0‖ * ‖z‖ ^ (2 : ℕ) + ‖x - x0‖⁻¹ * (inner ℝ (x - x0) z) ^ (2 : ℕ) := by
  -- Specialize the bilinear formula to `w = z` and rewrite the diagonal inner product as a square.
  rw [powerDistance_three_sndFDeriv_apply_apply]
  simp [pow_two, mul_comm, mul_assoc]

/-- Helper for Lemma 4.2.4: for a nonzero direction, the repeated-direction model factors through
the normalized direction with an explicit `‖z‖²` factor. -/
private theorem powerDistanceThreeSndFDerivDiagonalScale {x0 x z : E} (hz : z ≠ 0) :
    (fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0)) x z) z =
      ‖z‖ ^ (2 : ℕ) *
        (‖x - x0‖ + ‖x - x0‖⁻¹ * (inner ℝ (x - x0) (‖z‖⁻¹ • z)) ^ (2 : ℕ)) := by
  -- Normalize to the unit direction `‖z‖⁻¹ • z` and pull out the common `‖z‖²` factor.
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

section
omit [CompleteSpace E]

/-- Helper for Lemma 4.2.4: a symmetric operator is controlled in norm by a quadratic-form bound.
-/
private theorem symmetricOpNormLeOfQuadraticBound
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

end

section
omit [CompleteSpace E]

/-- Helper for Lemma 4.2.4: every affine test of the normalized quadratic model lies below the
exact model. -/
private theorem unitDirectionQuadraticModel_affineLe (u e : E) (t : ℝ) :
    (1 - t ^ (2 : ℕ)) * ‖u‖ + 2 * t * inner ℝ u e ≤
      ‖u‖ + ‖u‖⁻¹ * (inner ℝ u e) ^ (2 : ℕ) := by
  by_cases hu : u = 0
  · -- At the origin, both sides vanish.
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

end

section
omit [CompleteSpace E]

/-- Helper for Lemma 4.2.4: for a unit direction, the normalized quadratic model is
`2`-Lipschitz. -/
private theorem unitDirectionQuadraticModel_subLe
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
  -- Compare the exact value at `u` with the universal affine upper bound at `v`.
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

end

section
omit [CompleteSpace E]

/-- Helper for Lemma 4.2.4: for a unit direction, the normalized quadratic model has absolute
variation bounded by `2 * ‖u - v‖`. -/
private theorem unitDirectionQuadraticModel_abs_subLe
    {e u v : E} (he : ‖e‖ = 1) :
    |(‖u‖ + ‖u‖⁻¹ * (inner ℝ u e) ^ (2 : ℕ)) -
        (‖v‖ + ‖v‖⁻¹ * (inner ℝ v e) ^ (2 : ℕ))| ≤
      2 * ‖u - v‖ := by
  refine abs_le.2 ?_
  constructor
  · have hvu := unitDirectionQuadraticModel_subLe (e := e) (u := v) (v := u) he
    have hvu' :
        (‖v‖ + ‖v‖⁻¹ * (inner ℝ v e) ^ (2 : ℕ)) -
            (‖u‖ + ‖u‖⁻¹ * (inner ℝ u e) ^ (2 : ℕ)) ≤
          2 * ‖u - v‖ := by
      simpa [norm_sub_rev] using hvu
    linarith
  · exact unitDirectionQuadraticModel_subLe (e := e) (u := u) (v := v) he

end

/-- Helper for Lemma 4.2.4: the cubic diagonal second-derivative gap is bounded by
`2 * ‖x - y‖ * ‖z‖²`. -/
private theorem powerDistanceThreeSndFDerivQuadraticSubLe (x0 x y z : E) :
    |(fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0)) x z) z -
        (fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0)) y z) z| ≤
      2 * ‖x - y‖ * ‖z‖ ^ (2 : ℕ) := by
  -- Normalize to the unit direction `‖z‖⁻¹ • z` and use the unit-direction model bound.
  by_cases hz : z = 0
  · subst z
    simp
  · let e : E := ‖z‖⁻¹ • z
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

set_option synthInstance.maxHeartbeats 200000 in
/-- Helper for Lemma 4.2.4: the cubic second derivative is globally `2`-Lipschitz in operator
norm. -/
private theorem powerDistanceThreeSndFDerivNormSubLe (x0 x y : E) :
    ‖fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0)) x -
        fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0)) y‖ ≤
      2 * ‖x - y‖ := by
  -- Route correction: rewrite the difference once as `innerSL ∘ T`, then control `T` by its
  -- diagonal quadratic form.
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
    exact powerDistanceThreeSndFDerivQuadraticSubLe x0 x y z
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

end

section
omit [CompleteSpace E]

/-- Helper for Lemma 4.2.4: the translated cubic power function is twice continuously
differentiable. -/
private theorem powerDistance_three_contDiff_two (x0 : E) :
    ContDiff ℝ 2 (powerDistance (3 : ℝ) x0) := by
  -- Package the explicit derivative and the global second-derivative Lipschitz bound into
  -- `ContDiff ℝ 2`.
  refine
    (contDiff_succ_iff_fderiv (𝕜 := ℝ) (n := (1 : ℕ∞))
      (f := powerDistance (3 : ℝ) x0)).2 ?_
  refine ⟨?_, ?_, ?_⟩
  · -- The cubic power-distance is differentiable everywhere by the explicit derivative formula.
    intro x
    exact (powerDistance_three_hasFDerivAt x0 x).differentiableAt
  · -- The side condition `1 ≠ ∞` is automatic.
    intro hω
    cases hω
  · -- The derivative map is `C¹` because its derivative is globally Lipschitz.
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
        convert ((innerSL ℝ).hasFDerivAt.comp x (hasFDerivAt_powerDistance_three_gradient x0 x))
          using 1
      exact hderivAt.differentiableAt
    · -- A globally Lipschitz derivative is continuous.
      have hLip :
          LipschitzWith (2 : NNReal)
            (fderiv ℝ (fderiv ℝ (powerDistance (3 : ℝ) x0))) := by
        rw [lipschitzWith_iff_norm_sub_le]
        intro x y
        simpa using powerDistanceThreeSndFDerivNormSubLe x0 x y
      exact hLip.continuous

end

section
omit [CompleteSpace E]

/-- The translated cubic power function `powerDistance (3 : ℝ) x₀` has globally `2`-Lipschitz
Hessian. This is the owner-level statement underlying Lemma 4.2.4 and its translated uses. -/
theorem powerDistance_three_mem_C22 (x0 : E) :
    powerDistance (3 : ℝ) x0 ∈ C22[(2 : NNReal)] := by
  -- Route correction: package the cubic second-derivative control directly on the `C22[2]`
  -- owner surface instead of reconstructing it from a separate Hessian bridge.
  refine
    { contDiff := powerDistance_three_contDiff_two x0
      sndFDeriv_lipschitz := ?_ }
  rw [lipschitzWith_iff_norm_sub_le]
  intro x y
  simpa using powerDistanceThreeSndFDerivNormSubLe x0 x y

end

/-- The Hessians of the translated cubic power function satisfy the owner inequality
`‖∇² d₃,x₀(x) - ∇² d₃,x₀(y)‖ ≤ 2 * ‖x - y‖`. -/
theorem powerDistance_three_hessian_norm_sub_le (x0 x y : E) :
    ‖hessian (powerDistance (3 : ℝ) x0) x -
        hessian (powerDistance (3 : ℝ) x0) y‖ ≤
      (2 : ℝ) * ‖x - y‖ := by
  simpa using
    HasLipschitzContinuousHessian.norm_sub_le (powerDistance_three_mem_C22 x0) x y

section
omit [CompleteSpace E]

/-- Helper for Lemma 4.2.4: the centered cubic power function `d₃(x) = (1 / 3) * ‖x‖³`,
realized as `powerDistance (3 : ℝ) 0`, lies in `C22[2]`. -/
theorem powerDistance_three_zero_mem_C22 :
    powerDistance (3 : ℝ) (0 : E) ∈ C22[(2 : NNReal)] := by
  simpa using powerDistance_three_mem_C22 (0 : E)

end

/-- Lemma 4.2.4, pointwise form: for any `x, y ∈ E`, the Hessian of the centered cubic power
function satisfies `‖∇² d₃(x) - ∇² d₃(y)‖ ≤ 2 * ‖x - y‖`. -/
theorem powerDistance_three_zero_hessian_norm_sub_le (x y : E) :
    ‖hessian (powerDistance (3 : ℝ) (0 : E)) x -
        hessian (powerDistance (3 : ℝ) (0 : E)) y‖ ≤
      (2 : ℝ) * ‖x - y‖ := by
  simpa using powerDistance_three_hessian_norm_sub_le (0 : E) x y

end
