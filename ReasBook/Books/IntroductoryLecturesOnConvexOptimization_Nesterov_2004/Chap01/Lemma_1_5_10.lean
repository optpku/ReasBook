/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_5_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.FirstOrderTaylorModel

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {L : NNReal} {f : E → ℝ}
variable (hf : ContDiff ℝ 1 f) (hgrad : LipschitzWith L (∇ f))

include hf hgrad

/- Lemma 1.5.10 is source-facing in first-order smooth optimization.

Source/core/bridge triage:
* source-facing: the first-order Taylor remainder bound and its quadratic upper/lower companions
* core/canonical: the owner hypotheses `ContDiff ℝ 1 f` and `LipschitzWith L (∇ f)` from
  Definition 1.5.2 together with the affine Taylor-model owner `firstOrderTaylorModelAt f x`
* bridge/view: evaluation of the owner model via `firstOrderTaylorModelAt_apply`

Primitive data:
* a function `f`
* a Lipschitz constant `L`
* a base point `x`

Derived API:
* the absolute remainder estimate
* the quadratic upper and lower bounds obtained by comparing `f y` with the owner affine model

The statements are written on a real Hilbert space; specializing `E` to `EuclideanSpace ℝ (Fin n)`
recovers the textbook `ℝⁿ` formulation. -/

-- Proof sketch: restrict `f` to the segment `t ↦ x + t • (y - x)`, apply the fundamental theorem
-- of calculus to the derivative `⟪∇ f (x + t • (y - x)), y - x⟫`, subtract the affine term at
-- `x`, and bound the integrand using the `L`-Lipschitz estimate for `∇ f`.
omit hf hgrad

/-- Helper for Lemma 1.5.10: the corrected segment remainder has derivative equal to the gradient
increment paired with the segment direction. -/
private lemma segment_corrected_remainder_hasDerivAt
    (hf : ContDiff ℝ 1 f) (x d : E) (t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ f (x + u • d) - f x - u * inner ℝ (∇ f x) d)
      (inner ℝ (∇ f (x + t • d) - ∇ f x) d) t := by
  -- Differentiate the restriction of `f` to the affine line through `x` in direction `d`.
  have hdiff : DifferentiableAt ℝ f (x + t • d) :=
    hf.differentiable_one.differentiableAt
  have hseg : HasDerivAt (fun u : ℝ ↦ f (x + u • d)) ((fderiv ℝ f (x + t • d)) d) t := by
    have hline : HasDerivAt (fun u : ℝ ↦ x + u • d) d t := by
      simpa [one_smul] using (((hasDerivAt_id t).smul_const d).const_add x)
    simpa [Function.comp] using (hdiff.hasFDerivAt.comp t hline.hasFDerivAt).hasDerivAt
  -- The affine correction contributes exactly the constant gradient term at `x`.
  have hlin : HasDerivAt (fun u : ℝ ↦ u * inner ℝ (∇ f x) d) (inner ℝ (∇ f x) d) t := by
    simpa [one_mul] using (hasDerivAt_id t).mul_const (inner ℝ (∇ f x) d)
  have hmain :
      HasDerivAt (fun u : ℝ ↦ f (x + u • d) - f x - u * inner ℝ (∇ f x) d)
        (((fderiv ℝ f (x + t • d)) d) - inner ℝ (∇ f x) d) t := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      hseg.sub ((hasDerivAt_const t (f x)).add hlin)
  -- Rewrite the Fréchet derivative through the gradient pairing to obtain the source formula.
  convert hmain using 1
  rw [inner_sub_left]
  rw [inner_gradient_left (y := d) hdiff]

/-- Helper for Lemma 1.5.10: the corrected segment remainder vanishes at `0` and equals the
first-order Taylor remainder at `1`. -/
private lemma segment_corrected_remainder_endpoints
    (x y : E) :
    let d := y - x
    let R : ℝ → ℝ := fun t ↦ f (x + t • d) - f x - t * inner ℝ (∇ f x) d
    R 0 = 0 ∧ R 1 = f y - firstOrderTaylorModelAt f x y := by
  -- Evaluating at the endpoints turns the corrected path into the target remainder.
  simp [sub_eq_add_neg, add_assoc, add_comm]

/-- Helper for Lemma 1.5.10: on `(0,1)` the corrected segment remainder has derivative bounded by
`L t ‖d‖²`. -/
private lemma segment_corrected_remainder_deriv_abs_le
    (hf : ContDiff ℝ 1 f) (hgrad : LipschitzWith L (∇ f))
    (x d : E) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    |deriv (fun u : ℝ ↦ f (x + u • d) - f x - u * inner ℝ (∇ f x) d) t|
      ≤ (L : ℝ) * t * ‖d‖ ^ (2 : ℕ) := by
  -- Start from the explicit derivative formula for the corrected path.
  have hderivAt := segment_corrected_remainder_hasDerivAt (f := f) hf x d t
  rw [hderivAt.deriv]
  have hinner :
      |inner ℝ (∇ f (x + t • d) - ∇ f x) d| ≤ ‖∇ f (x + t • d) - ∇ f x‖ * ‖d‖ := by
    simpa [real_inner_comm] using abs_real_inner_le_norm (∇ f (x + t • d) - ∇ f x) d
  have hgrad_bound : ‖∇ f (x + t • d) - ∇ f x‖ ≤ (L : ℝ) * ‖(x + t • d) - x‖ := by
    simpa [dist_eq_norm] using hgrad.norm_sub_le (x + t • d) x
  have hseg_norm : ‖(x + t • d) - x‖ = t * ‖d‖ := by
    calc
      ‖(x + t • d) - x‖ = ‖t • d‖ := by simp
      _ = |t| * ‖d‖ := by simp [norm_smul, Real.norm_eq_abs]
      _ = t * ‖d‖ := by rw [abs_of_pos ht.1]
  -- Combine Cauchy-Schwarz with the Lipschitz gradient estimate along the segment.
  calc
    |inner ℝ (∇ f (x + t • d) - ∇ f x) d| ≤ ‖∇ f (x + t • d) - ∇ f x‖ * ‖d‖ := hinner
    _ ≤ ((L : ℝ) * ‖(x + t • d) - x‖) * ‖d‖ := by gcongr
    _ = ((L : ℝ) * (t * ‖d‖)) * ‖d‖ := by rw [hseg_norm]
    _ = (L : ℝ) * t * ‖d‖ ^ (2 : ℕ) := by ring

include hf hgrad

/-- Lemma 1.5.10: if `f` belongs to the textbook class `C^{1,1}_L(ℝⁿ)`, then the first-order
Taylor remainder at `x` along `y - x` is bounded in absolute value by `(L / 2) ‖y - x‖²`. -/
lemma norm_taylor_remainder_le_half_lipschitzGradient_mul_sq
    (x y : E) :
    |f y - firstOrderTaylorModelAt f x y| ≤
      ((L : ℝ) / 2) * ‖y - x‖ ^ 2 := by
  let d : E := y - x
  -- Restrict `f` to the segment from `x` to `y` and record continuity on `[0,1]`.
  have hcont :
      ContinuousOn (fun t : ℝ ↦ f (x + t • d) - f x - t * inner ℝ (∇ f x) d)
        (Set.Icc (0 : ℝ) 1) := by
    have hsegCont : Continuous (fun t : ℝ ↦ f (x + t • d)) :=
      hf.continuous.comp (by fun_prop)
    have hlinCont : Continuous (fun t : ℝ ↦ t * inner ℝ (∇ f x) d) := by
      fun_prop
    exact ((hsegCont.sub continuous_const).sub hlinCont).continuousOn
  -- The derivative formula makes the corrected path differentiable on the open interval.
  have hdiff :
      DifferentiableOn ℝ (fun t : ℝ ↦ f (x + t • d) - f x - t * inner ℝ (∇ f x) d)
        (Set.Ioo (0 : ℝ) 1) := by
    intro t ht
    exact (segment_corrected_remainder_hasDerivAt (f := f) hf x d t).differentiableAt
      |>.differentiableWithinAt
  -- Apply the integral bound for a one-variable path with controlled derivative.
  have hbound :=
    norm_sub_le_integral_of_norm_deriv_le_of_le
      (f := fun t : ℝ ↦ f (x + t • d) - f x - t * inner ℝ (∇ f x) d)
      (B := fun t : ℝ ↦ (L : ℝ) * t * ‖d‖ ^ (2 : ℕ))
      (a := (0 : ℝ)) (b := 1)
      (by norm_num) hcont hdiff
      (Filter.Eventually.of_forall fun t ht_mem ↦
        segment_corrected_remainder_deriv_abs_le (f := f) hf hgrad x d ht_mem)
      (by
        simpa [mul_assoc] using
          (show IntervalIntegrable (fun t : ℝ ↦ t) MeasureTheory.volume 0 1 from
            intervalIntegrable_id).const_mul ((L : ℝ) * ‖d‖ ^ (2 : ℕ)))
  -- Rewrite the endpoint values back to the Taylor remainder from the statement.
  have hendpoint := segment_corrected_remainder_endpoints (f := f) x y
  have hR0 :
      (fun t : ℝ ↦ f (x + t • d) - f x - t * inner ℝ (∇ f x) d) 0 = 0 := by
    simpa [d] using hendpoint.1
  have hR1 :
      (fun t : ℝ ↦ f (x + t • d) - f x - t * inner ℝ (∇ f x) d) 1 =
        f y - firstOrderTaylorModelAt f x y := by
    simpa [d] using hendpoint.2
  rw [hR1, hR0, sub_zero, Real.norm_eq_abs] at hbound
  calc
    |f y - firstOrderTaylorModelAt f x y| ≤
        ∫ t in (0 : ℝ)..1, (L : ℝ) * t * ‖d‖ ^ (2 : ℕ) := hbound
    _ = ((L : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) := by
      -- Compute the scalar integral `∫₀¹ t dt = 1 / 2`.
      calc
        ∫ t in (0 : ℝ)..1, (L : ℝ) * t * ‖d‖ ^ (2 : ℕ) =
            ∫ t in (0 : ℝ)..1, ((L : ℝ) * ‖d‖ ^ (2 : ℕ)) * t := by
              congr with t
              ring
        _ = ((L : ℝ) * ‖d‖ ^ (2 : ℕ)) * ∫ t in (0 : ℝ)..1, t := by
              rw [intervalIntegral.integral_const_mul]
        _ = ((L : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) := by
              rw [integral_id]
              norm_num
              ring
    _ = ((L : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ) := by
      simp [d]

-- Proof sketch: apply the core remainder estimate
-- `norm_taylor_remainder_le_half_lipschitzGradient_mul_sq`, then use that `a ≤ b` follows from
-- `|a| ≤ b`.
/-- The canonical first-order Taylor model at `x` gives a quadratic upper bound for `f y`. -/
lemma taylor_upper_bound_of_contDiffOne_withLipschitzGradient
    (x y : E) :
    f y ≤ firstOrderTaylorModelAt f x y + ((L : ℝ) / 2) * ‖y - x‖ ^ 2 := by
  have hrem :=
    abs_le.mp <| norm_taylor_remainder_le_half_lipschitzGradient_mul_sq hf hgrad x y
  linarith [hrem.2]

-- Proof sketch: apply the core remainder estimate
-- `norm_taylor_remainder_le_half_lipschitzGradient_mul_sq`, then use that `-b ≤ a` follows from
-- `|a| ≤ b` and rearrange.
/-- The canonical first-order Taylor model at `x` also gives the corresponding quadratic lower
bound for `f y`. -/
lemma taylor_lower_bound_of_contDiffOne_withLipschitzGradient
    (x y : E) :
    f y ≥ firstOrderTaylorModelAt f x y - ((L : ℝ) / 2) * ‖y - x‖ ^ 2 := by
  have hrem :=
    abs_le.mp <| norm_taylor_remainder_le_half_lipschitzGradient_mul_sq hf hgrad x y
  linarith [hrem.1]

omit hf hgrad

end
