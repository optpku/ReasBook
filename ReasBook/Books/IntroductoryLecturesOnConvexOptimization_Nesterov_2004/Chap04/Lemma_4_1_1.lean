/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Lemma_1_5_11
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section

variable {L : NNReal} {𝓕 : Set E} {f : E → ℝ}

/- Lemma 4.1.1 lies in the local Hessian-Lipschitz Taylor-remainder domain on complete real
inner-product spaces.

Sampled owner declarations:
* `HessianLipschitzOn` in `Definition_4_1_2`
* `HessianLipschitzOn.contDiffOn` in `Definition_4_1_2`
* `HessianLipschitzOn.lipschitz` in `Definition_4_1_2`
* `HasLipschitzContinuousHessian.gradient_deviation_le` in `Chap01/Lemma_1_5_11`
* `HasLipschitzContinuousHessian.secondOrderTaylorModel_error_le` in
  `Chap01/Lemma_1_5_11`

Source/core/bridge triage:
* source-facing: the local-on-`𝓕` Taylor remainder bounds of Lemma 4.1.1
* core/canonical: the chapter owner `HessianLipschitzOn L 𝓕 f` and the quadratic owner
  `secondOrderTaylorModelAt f x`
* bridge/view: the pointwise specialization to `x, y ∈ 𝓕`

Primitive data:
* the owner hypothesis `hf : HessianLipschitzOn L 𝓕 f`
* points `x, y` in `𝓕`

Derived API:
* the localized gradient-deviation bound
* the second-order Taylor-model error bound

The previous separate hypotheses `Convex ℝ 𝓕`, `ContDiffOn ℝ 2 f 𝓕`, and the pointwise
Hessian-difference estimate duplicated primitive fields of `HessianLipschitzOn`; this file keeps
the owner abstraction directly and states the second conclusion using the canonical quadratic
Taylor model owner rather than an expanded ad hoc formula. The first conclusion is likewise stated
with the intrinsic Hessian operator `hessian f x`, not the raw derivative of the gradient map. -/

namespace HessianLipschitzOn

/-- Helper for Lemma 4.1.1: the Riesz isomorphism turns the dual-valued derivative of a scalar
field into its gradient vector. -/
private abbrev rieszToPrimal : StrongDual ℝ E →L[ℝ] E :=
  (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- Helper for Lemma 4.1.1: the affine segment `t ↦ x + t • d` has derivative `d`. -/
private theorem line_hasDerivAt (x d : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ x + s • d) d t := by
  -- Differentiate the scalar multiple first, then translate by the base point.
  simpa [one_smul] using ((hasDerivAt_id t).smul_const d).const_add x

/-- Helper for Lemma 4.1.1: every point of the segment from `x` to `y` stays inside the feasible
set of a convex `HessianLipschitzOn` domain. -/
private theorem segment_mem_of_hessianLipschitzOn
    (hf : HessianLipschitzOn L 𝓕 f)
    {x y : E} (hx : x ∈ 𝓕) (hy : y ∈ 𝓕)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    x + t • (y - x) ∈ 𝓕 := by
  -- Rewrite the affine segment as the standard line map and use convexity of `𝓕`.
  have hsegment : x + t • (y - x) = AffineMap.lineMap x y t := by
    rw [AffineMap.lineMap_apply_module']
    abel_nf
  simpa [hsegment] using hf.convex.lineMap_mem hx hy ht

/-- Helper for Lemma 4.1.1: on the feasible set, the gradient field is continuous. -/
private theorem gradient_continuousOn
    (hf : HessianLipschitzOn L 𝓕 f) :
    ContinuousOn (∇ f) 𝓕 := by
  let D : StrongDual ℝ E →L[ℝ] E := rieszToPrimal
  have hcontFDeriv : ContinuousOn (fderiv ℝ f) 𝓕 := by
    -- On the open feasible set, `C²` regularity upgrades the derivative map to `C¹`, hence
    -- continuous.
    exact
      (hf.contDiffOn.fderiv_of_isOpen hf.isOpen
        (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))).continuousOn
  -- Transport the derivative continuity through the Riesz map to obtain gradient continuity.
  simpa [gradient, D] using D.continuous.comp_continuousOn hcontFDeriv

/-- Helper for Lemma 4.1.1: at every feasible point, the derivative of the gradient is the
Hessian operator. -/
private theorem gradient_hasFDerivAt
    (hf : HessianLipschitzOn L 𝓕 f)
    {z : E} (hz : z ∈ 𝓕) :
    HasFDerivAt (∇ f) (hessian f z) z := by
  let D : StrongDual ℝ E →L[ℝ] E := rieszToPrimal
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ f) z := by
    have hfderiv : ContDiffAt ℝ 1 (fderiv ℝ f) z :=
      (hf.contDiffAt hz).fderiv_right
        (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
    exact hfderiv.differentiableAt one_ne_zero
  have hgradDiff : DifferentiableAt ℝ (∇ f) z := by
    -- Rewrite the gradient through the Riesz map before differentiating.
    simpa [gradient, D] using D.differentiableAt.comp z hfdiff
  -- The derivative of the gradient is the Hessian by definition.
  simpa [hessian] using hgradDiff.hasFDerivAt

/-- Helper for Lemma 4.1.1: integrating the Hessian action along the feasible segment recovers
the gradient increment. -/
private theorem segment_gradient_integral_eq
    (hf : HessianLipschitzOn L 𝓕 f)
    (x y : E) (hx : x ∈ 𝓕) (hy : y ∈ 𝓕) :
    ∇ f y - ∇ f x = ∫ t in 0..1, hessian f (x + t • (y - x)) (y - x) := by
  let d : E := y - x
  have hderiv :
      ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun s : ℝ ↦ ∇ f (x + s • d)) (hessian f (x + t • d) d) t := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht
    -- Differentiate the gradient after restricting to the segment inside `𝓕`.
    simpa [Function.comp, d] using
      (gradient_hasFDerivAt (hf := hf)
        (z := x + t • d)
        (hz := segment_mem_of_hessianLipschitzOn (hf := hf) hx hy ht')).comp_hasDerivAt t
          (line_hasDerivAt x d t)
  have hcont :
      ContinuousOn (fun t : ℝ ↦ hessian f (x + t • d) d) (Set.Icc (0 : ℝ) 1) := by
    have hmaps :
        Set.MapsTo (fun t : ℝ ↦ x + t • d) (Set.Icc (0 : ℝ) 1) 𝓕 := by
      intro t ht
      simpa [d] using segment_mem_of_hessianLipschitzOn (hf := hf) hx hy ht
    have hcontH :
        ContinuousOn (fun t : ℝ ↦ hessian f (x + t • d)) (Set.Icc (0 : ℝ) 1) :=
      (hf.continuousOn_hessian.comp
        (continuousOn_const.add (continuousOn_id.smul continuousOn_const))
        hmaps)
    exact hcontH.clm_apply continuousOn_const
  have hint :
      IntervalIntegrable (fun t : ℝ ↦ hessian f (x + t • d) d) MeasureTheory.volume 0 1 :=
    by
      exact hcont.intervalIntegrable_of_Icc (show (0 : ℝ) ≤ 1 by norm_num)
  have hy' : x + d = y := by
    simp [d]
  -- Apply the fundamental theorem of calculus to the gradient restricted to the segment.
  symm
  simpa [d, hy'] using intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/-- Helper for Lemma 4.1.1: the local Hessian Lipschitz estimate gives the quadratic segment
bound for the Hessian action. -/
private theorem segment_hessian_action_bound
    (hf : HessianLipschitzOn L 𝓕 f)
    (x y : E) (hx : x ∈ 𝓕) (hy : y ∈ 𝓕)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖(hessian f (x + t • (y - x)) - hessian f x) (y - x)‖ ≤
      (L : ℝ) * t * ‖y - x‖ ^ (2 : ℕ) := by
  have hnorm :
      ‖hessian f (x + t • (y - x)) - hessian f x‖ ≤ (L : ℝ) * ‖t • (y - x)‖ := by
    have hseg := segment_mem_of_hessianLipschitzOn (hf := hf) hx hy ht
    have hnorm0 :
        ‖hessian f (x + t • (y - x)) - hessian f x‖ ≤
          (L : ℝ) * ‖(x + t • (y - x)) - x‖ := by
      exact hf.norm_sub_le hseg hx
    have hsub : (x + t • (y - x)) - x = t • (y - x) := by
      abel_nf
    calc
      ‖hessian f (x + t • (y - x)) - hessian f x‖ ≤ (L : ℝ) * ‖(x + t • (y - x)) - x‖ := hnorm0
      _ = (L : ℝ) * ‖t • (y - x)‖ := by rw [hsub]
  -- Convert the operator-norm estimate into the action estimate on the displacement vector.
  calc
    ‖(hessian f (x + t • (y - x)) - hessian f x) (y - x)‖
      ≤ ‖hessian f (x + t • (y - x)) - hessian f x‖ * ‖y - x‖ := by
          exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ ((L : ℝ) * ‖t • (y - x)‖) * ‖y - x‖ := by
          gcongr
    _ = ((L : ℝ) * (t * ‖y - x‖)) * ‖y - x‖ := by
          rw [norm_smul, Real.norm_of_nonneg ht.1]
    _ = (L : ℝ) * t * ‖y - x‖ ^ (2 : ℕ) := by
          ring

/-- Helper for Lemma 4.1.1: the scalar restriction of `f` to a feasible segment satisfies the
usual fundamental-theorem identity. -/
private theorem segment_scalar_integral_eq
    (hf : HessianLipschitzOn L 𝓕 f)
    (x y : E) (hx : x ∈ 𝓕) (hy : y ∈ 𝓕) :
    f y - f x = ∫ t in 0..1, inner ℝ (∇ f (x + t • (y - x))) (y - x) := by
  let d : E := y - x
  let φ : ℝ → ℝ := fun t ↦ f (x + t • d)
  let ψ : ℝ → ℝ := fun t ↦ inner ℝ (∇ f (x + t • d)) d
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt φ (ψ t) t := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht
    have hz : x + t • d ∈ 𝓕 := by
      simpa [d] using segment_mem_of_hessianLipschitzOn (hf := hf) hx hy ht'
    have hdiff : DifferentiableAt ℝ f (x + t • d) :=
      (hf.contDiffAt hz).differentiableAt (by norm_num)
    have hcomp :
        HasDerivAt (fun s : ℝ ↦ f (x + s • d))
          (fderiv ℝ f (x + t • d) d) t := by
      exact hdiff.hasFDerivAt.comp_hasDerivAt t (line_hasDerivAt x d t)
    -- Rewrite the scalar derivative through the gradient pairing.
    simpa [φ, ψ, d, hdiff.hasGradientAt.fderiv_apply] using hcomp
  have hcont :
      ContinuousOn ψ (Set.Icc (0 : ℝ) 1) := by
    have hmaps :
        Set.MapsTo (fun t : ℝ ↦ x + t • d) (Set.Icc (0 : ℝ) 1) 𝓕 := by
      intro t ht
      simpa [d] using segment_mem_of_hessianLipschitzOn (hf := hf) hx hy ht
    have hcontGrad :
        ContinuousOn (fun t : ℝ ↦ ∇ f (x + t • d)) (Set.Icc (0 : ℝ) 1) :=
      (gradient_continuousOn (hf := hf)).comp
        (continuousOn_const.add (continuousOn_id.smul continuousOn_const))
        hmaps
    exact hcontGrad.inner continuousOn_const
  have hint : IntervalIntegrable ψ MeasureTheory.volume 0 1 := by
    exact hcont.intervalIntegrable_of_Icc (show (0 : ℝ) ≤ 1 by norm_num)
  have hy' : x + d = y := by
    simp [d]
  -- Apply the fundamental theorem of calculus to the scalar segment restriction.
  symm
  simpa [φ, ψ, d, hy'] using intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/-- Helper for Lemma 4.1.1: differentiating the gradient pairing along the feasible segment
produces the Hessian quadratic form. -/
private theorem segment_gradient_pair_hasDerivAt
    (hf : HessianLipschitzOn L 𝓕 f)
    (x y : E) (hx : x ∈ 𝓕) (hy : y ∈ 𝓕)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt (fun s : ℝ ↦ inner ℝ (∇ f (x + s • (y - x))) (y - x))
      (inner ℝ (hessian f (x + t • (y - x)) (y - x)) (y - x)) t := by
  -- Differentiate the gradient field along the segment before pairing with the displacement.
  have hgrad :
      HasDerivAt (fun s : ℝ ↦ ∇ f (x + s • (y - x)))
        (hessian f (x + t • (y - x)) (y - x)) t := by
    simpa [Function.comp] using
      (gradient_hasFDerivAt (hf := hf)
        (z := x + t • (y - x))
        (hz := segment_mem_of_hessianLipschitzOn (hf := hf) hx hy ht)).comp_hasDerivAt t
          (line_hasDerivAt x (y - x) t)
  simpa using hgrad.inner ℝ (hasDerivAt_const t (y - x))

/-- Helper for Lemma 4.1.1: the scalar first-order remainder of the gradient pairing is the
integral of the Hessian difference along the feasible segment. -/
private theorem segment_gradient_pair_remainder_eq_integral
    (hf : HessianLipschitzOn L 𝓕 f)
    (x y : E) (hx : x ∈ 𝓕) (hy : y ∈ 𝓕)
    (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    inner ℝ (∇ f (x + u • (y - x))) (y - x) - inner ℝ (∇ f x) (y - x) -
        u * inner ℝ (hessian f x (y - x)) (y - x) =
      ∫ s in 0..u, inner ℝ ((hessian f (x + s • (y - x)) - hessian f x) (y - x)) (y - x) := by
  let ψ : ℝ → ℝ := fun t ↦ inner ℝ (∇ f (x + t • (y - x))) (y - x)
  let θ : ℝ → ℝ := fun t ↦ inner ℝ (hessian f (x + t • (y - x)) (y - x)) (y - x)
  have hderiv :
      ∀ t ∈ Set.uIcc (0 : ℝ) u,
        HasDerivAt (fun s : ℝ ↦ ψ s - s * θ 0) (θ t - θ 0) t := by
    intro t ht
    have htI : t ∈ Set.Icc (0 : ℝ) u := by
      simpa [Set.uIcc_of_le hu.1] using ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
      exact ⟨htI.1, htI.2.trans hu.2⟩
    -- Subtract the linearization term before applying FTC a second time.
    simpa [ψ, θ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
      mul_assoc] using
      (segment_gradient_pair_hasDerivAt (hf := hf) (x := x) (y := y) hx hy t ht').sub
        ((hasDerivAt_id t).mul_const (θ 0))
  have hcontθ :
      ContinuousOn θ (Set.uIcc (0 : ℝ) u) := by
    have hcontHd :
        ContinuousOn (fun t : ℝ ↦ hessian f (x + t • (y - x)) (y - x)) (Set.uIcc (0 : ℝ) u) := by
      have hmaps :
          Set.MapsTo (fun t : ℝ ↦ x + t • (y - x)) (Set.uIcc (0 : ℝ) u) 𝓕 := by
        intro t ht
        have htI : t ∈ Set.Icc (0 : ℝ) u := by
          simpa [Set.uIcc_of_le hu.1] using ht
        exact segment_mem_of_hessianLipschitzOn (hf := hf) hx hy ⟨htI.1, htI.2.trans hu.2⟩
      have hcontH :
          ContinuousOn (fun t : ℝ ↦ hessian f (x + t • (y - x))) (Set.uIcc (0 : ℝ) u) :=
        (hf.continuousOn_hessian.comp
          (continuousOn_const.add (continuousOn_id.smul continuousOn_const))
          hmaps)
      exact hcontH.clm_apply continuousOn_const
    exact hcontHd.inner continuousOn_const
  have hint : IntervalIntegrable (fun t : ℝ ↦ θ t - θ 0) MeasureTheory.volume 0 u :=
    (hcontθ.sub continuousOn_const).intervalIntegrable
  have hftc :
      ∫ s in 0..u, (θ s - θ 0) = (ψ u - u * θ 0) - (ψ 0 - 0 * θ 0) := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  -- Rewrite the one-dimensional FTC identity as the Hessian-difference remainder formula.
  calc
    inner ℝ (∇ f (x + u • (y - x))) (y - x) - inner ℝ (∇ f x) (y - x) -
        u * inner ℝ (hessian f x (y - x)) (y - x)
      = (ψ u - u * θ 0) - (ψ 0 - 0 * θ 0) := by
          simp [ψ, θ]
          ring
    _ = ∫ s in 0..u, (θ s - θ 0) := by
          symm
          exact hftc
    _ = ∫ s in 0..u, inner ℝ ((hessian f (x + s • (y - x)) - hessian f x) (y - x)) (y - x) := by
          congr with s
          simp [θ, inner_sub_left]

/-- Helper for Lemma 4.1.1: integrating the scalar first-order remainder identity over the
segment parameter yields the source-style double-integral second-order remainder. -/
private theorem second_order_remainder_eq_double_integral
    (hf : HessianLipschitzOn L 𝓕 f)
    (x y : E) (hx : x ∈ 𝓕) (hy : y ∈ 𝓕) :
    f y - f x - inner ℝ (∇ f x) (y - x) -
        (1 / 2 : ℝ) * inner ℝ (hessian f x (y - x)) (y - x) =
      ∫ u in 0..1, ∫ s in 0..u,
        inner ℝ ((hessian f (x + s • (y - x)) - hessian f x) (y - x)) (y - x) := by
  let ψ : ℝ → ℝ := fun t ↦ inner ℝ (∇ f (x + t • (y - x))) (y - x)
  let θ : ℝ → ℝ := fun t ↦ inner ℝ (hessian f (x + t • (y - x)) (y - x)) (y - x)
  have hcontψ :
      ContinuousOn ψ (Set.Icc (0 : ℝ) 1) := by
    have hmaps :
        Set.MapsTo (fun t : ℝ ↦ x + t • (y - x)) (Set.Icc (0 : ℝ) 1) 𝓕 := by
      intro t ht
      exact segment_mem_of_hessianLipschitzOn (hf := hf) hx hy ht
    have hcontGrad :
        ContinuousOn (fun t : ℝ ↦ ∇ f (x + t • (y - x))) (Set.Icc (0 : ℝ) 1) :=
      (gradient_continuousOn (hf := hf)).comp
        (continuousOn_const.add (continuousOn_id.smul continuousOn_const))
        hmaps
    exact hcontGrad.inner continuousOn_const
  have hintψ : IntervalIntegrable ψ MeasureTheory.volume 0 1 := by
    exact hcontψ.intervalIntegrable_of_Icc (show (0 : ℝ) ≤ 1 by norm_num)
  have hintConst : IntervalIntegrable (fun _ : ℝ ↦ ψ 0) MeasureTheory.volume 0 1 :=
    continuousOn_const.intervalIntegrable
  have hintLin : IntervalIntegrable (fun u : ℝ ↦ u * θ 0) MeasureTheory.volume 0 1 :=
    (continuousOn_id.mul continuousOn_const).intervalIntegrable
  have houter :
      f y - f x - inner ℝ (∇ f x) (y - x) -
          (1 / 2 : ℝ) * inner ℝ (hessian f x (y - x)) (y - x) =
        ∫ u in 0..1, (ψ u - ψ 0 - u * θ 0) := by
    -- First rewrite the scalar remainder as an outer integral of the gradient-pairing remainder.
    rw [segment_scalar_integral_eq (hf := hf) (x := x) (y := y) hx hy]
    rw [show inner ℝ (∇ f x) (y - x) = ψ 0 by simp [ψ]]
    rw [show inner ℝ (hessian f x (y - x)) (y - x) = θ 0 by simp [θ]]
    rw [show (fun u : ℝ ↦ ψ u - ψ 0 - u * θ 0) = fun u ↦ (ψ u - ψ 0) - u * θ 0 by rfl]
    rw [intervalIntegral.integral_sub (hintψ.sub hintConst) hintLin]
    rw [intervalIntegral.integral_sub hintψ hintConst]
    rw [intervalIntegral.integral_const, intervalIntegral.integral_mul_const, integral_id]
    ring
  have hdouble :
      ∫ u in 0..1, (ψ u - ψ 0 - u * θ 0) =
        ∫ u in 0..1, ∫ s in 0..u,
          inner ℝ ((hessian f (x + s • (y - x)) - hessian f x) (y - x)) (y - x) := by
    -- Then integrate the pointwise gradient-pairing remainder formula in the outer variable.
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro u hu
    have hu' : u ∈ Set.Icc (0 : ℝ) 1 := by
      have hu0 : 0 < u := by
        simpa [min_eq_left (show (0 : ℝ) ≤ 1 by norm_num)] using hu.1
      have hu1 : u ≤ 1 := by
        simpa [max_eq_right (show (0 : ℝ) ≤ 1 by norm_num)] using hu.2
      exact ⟨le_of_lt hu0, hu1⟩
    simpa [ψ, θ] using
      segment_gradient_pair_remainder_eq_integral (hf := hf) (x := x) (y := y) hx hy u hu'
  exact houter.trans hdouble

/-- Helper for Lemma 4.1.1: the Hessian Lipschitz estimate yields the cubic segment bound for the
quadratic Hessian form. -/
private theorem segment_hessian_quadratic_bound
    (hf : HessianLipschitzOn L 𝓕 f)
    (x y : E) (hx : x ∈ 𝓕) (hy : y ∈ 𝓕)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    |inner ℝ ((hessian f (x + s • (y - x)) - hessian f x) (y - x)) (y - x)| ≤
      (L : ℝ) * s * ‖y - x‖ ^ (3 : ℕ) := by
  -- Pair the Hessian action bound with the displacement one more time.
  calc
    |inner ℝ ((hessian f (x + s • (y - x)) - hessian f x) (y - x)) (y - x)|
      ≤ ‖(hessian f (x + s • (y - x)) - hessian f x) (y - x)‖ * ‖y - x‖ := by
          simpa [real_inner_comm] using
            abs_real_inner_le_norm
              ((hessian f (x + s • (y - x)) - hessian f x) (y - x)) (y - x)
    _ ≤ ((L : ℝ) * s * ‖y - x‖ ^ (2 : ℕ)) * ‖y - x‖ := by
          gcongr
          exact segment_hessian_action_bound (hf := hf) (x := x) (y := y) hx hy hs
    _ = (L : ℝ) * s * ‖y - x‖ ^ (3 : ℕ) := by
          ring

-- Proof sketch: use the owner hypothesis `hf : HessianLipschitzOn L 𝓕 f` to supply the local convex
-- `C²`, and Hessian-Lipschitz data on the segment from `x` to `y`; then apply the same integral
-- remainder argument as in the global owner theorem
-- `HasLipschitzContinuousHessian.gradient_deviation_le`, localized to `𝓕`.
/-- Lemma 4.1.1 (1): if `f` has `L`-Lipschitz Hessian on `𝓕`, then for `x, y ∈ 𝓕` the
first-order Taylor remainder in the gradient is bounded by `(L / 2) * ‖y - x‖²`. -/
theorem gradient_deviation_le
    (hf : HessianLipschitzOn L 𝓕 f)
    (x y : E) (hx : x ∈ 𝓕) (hy : y ∈ 𝓕) :
    ‖∇ f y - ∇ f x - hessian f x (y - x)‖ ≤
      ((L : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ) := by
  have hcontIntegrand :
      ContinuousOn
        (fun t : ℝ ↦ (hessian f (x + t • (y - x)) - hessian f x) (y - x))
        (Set.Icc (0 : ℝ) 1) := by
    have hmaps :
        Set.MapsTo (fun t : ℝ ↦ x + t • (y - x)) (Set.Icc (0 : ℝ) 1) 𝓕 := by
      intro t ht
      exact segment_mem_of_hessianLipschitzOn (hf := hf) hx hy ht
    have hcontH :
        ContinuousOn (fun t : ℝ ↦ hessian f (x + t • (y - x)) - hessian f x)
          (Set.Icc (0 : ℝ) 1) :=
      (hf.continuousOn_hessian.comp
        (continuousOn_const.add (continuousOn_id.smul continuousOn_const))
        hmaps).sub continuousOn_const
    exact hcontH.clm_apply continuousOn_const
  have hintIntegrand :
      IntervalIntegrable
        (fun t : ℝ ↦ (hessian f (x + t • (y - x)) - hessian f x) (y - x))
        MeasureTheory.volume 0 1 :=
    by
      exact hcontIntegrand.intervalIntegrable_of_Icc (show (0 : ℝ) ≤ 1 by norm_num)
  have hintBound :
      IntervalIntegrable (fun t : ℝ ↦ (L : ℝ) * t * ‖y - x‖ ^ (2 : ℕ))
        MeasureTheory.volume 0 1 :=
    by
      exact
        ((continuousOn_const.mul continuousOn_id).mul continuousOn_const).intervalIntegrable_of_Icc
        (show (0 : ℝ) ≤ 1 by norm_num)
  have hmono :
      ∫ t in 0..1, ‖(hessian f (x + t • (y - x)) - hessian f x) (y - x)‖
        ≤ ∫ t in 0..1, (L : ℝ) * t * ‖y - x‖ ^ (2 : ℕ) := by
    -- Bound the segment integrand pointwise by the Hessian Lipschitz majorant.
    refine intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ 1 by norm_num)
      hintIntegrand.norm hintBound ?_
    intro t ht
    exact segment_hessian_action_bound (hf := hf) (x := x) (y := y) hx hy ht
  have hrewrite :
      ∇ f y - ∇ f x - hessian f x (y - x) =
        ∫ t in 0..1, (hessian f (x + t • (y - x)) - hessian f x) (y - x) := by
    -- Rewrite the gradient remainder as an integral of Hessian differences on the segment.
    rw [segment_gradient_integral_eq (hf := hf) (x := x) (y := y) hx hy]
    have hconst : ∫ t in 0..1, hessian f x (y - x) = hessian f x (y - x) := by
      simp
    rw [hconst.symm]
    have hintSegment :
        IntervalIntegrable (fun t : ℝ ↦ hessian f (x + t • (y - x)) (y - x))
          MeasureTheory.volume 0 1 := by
      have hcont :
          ContinuousOn (fun t : ℝ ↦ hessian f (x + t • (y - x)) (y - x))
            (Set.Icc (0 : ℝ) 1) := by
        have hmaps :
            Set.MapsTo (fun t : ℝ ↦ x + t • (y - x)) (Set.Icc (0 : ℝ) 1) 𝓕 := by
          intro t ht
          exact segment_mem_of_hessianLipschitzOn (hf := hf) hx hy ht
        have hcontH :
            ContinuousOn (fun t : ℝ ↦ hessian f (x + t • (y - x))) (Set.Icc (0 : ℝ) 1) :=
          (hf.continuousOn_hessian.comp
            (continuousOn_const.add (continuousOn_id.smul continuousOn_const))
            hmaps)
        exact hcontH.clm_apply continuousOn_const
      exact hcont.intervalIntegrable_of_Icc (show (0 : ℝ) ≤ 1 by norm_num)
    have hsub0 :
        ∫ t in 0..1, hessian f (x + t • (y - x)) (y - x) - hessian f x (y - x) =
          (∫ t in 0..1, hessian f (x + t • (y - x)) (y - x)) -
            ∫ t in 0..1, hessian f x (y - x) := by
      simpa using
        (intervalIntegral.integral_sub
          (f := fun t : ℝ ↦ hessian f (x + t • (y - x)) (y - x))
          (g := fun _ : ℝ ↦ hessian f x (y - x))
          (μ := MeasureTheory.volume)
          hintSegment
          continuousOn_const.intervalIntegrable)
    have hsub :
        (∫ t in 0..1, hessian f (x + t • (y - x)) (y - x)) -
            ∫ t in 0..1, hessian f x (y - x) =
          ∫ t in 0..1, hessian f (x + t • (y - x)) (y - x) - hessian f x (y - x) := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsub0.symm
    calc
      (∫ t in 0..1, hessian f (x + t • (y - x)) (y - x)) -
          ∫ t in 0..1, hessian f x (y - x)
        = ∫ t in 0..1, hessian f (x + t • (y - x)) (y - x) - hessian f x (y - x) := hsub
      _ = ∫ t in 0..1, (hessian f (x + t • (y - x)) - hessian f x) (y - x) := by
          refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
          intro t ht
          simp
  -- Integrate the pointwise Hessian bound and compute `∫₀¹ t = 1 / 2`.
  calc
    ‖∇ f y - ∇ f x - hessian f x (y - x)‖
      = ‖∫ t in 0..1, (hessian f (x + t • (y - x)) - hessian f x) (y - x)‖ := by
          rw [hrewrite]
    _ ≤ ∫ t in 0..1, ‖(hessian f (x + t • (y - x)) - hessian f x) (y - x)‖ := by
          exact intervalIntegral.norm_integral_le_integral_norm
            (f := fun t : ℝ ↦ (hessian f (x + t • (y - x)) - hessian f x) (y - x))
            (a := (0 : ℝ)) (b := 1) (show (0 : ℝ) ≤ 1 by norm_num)
    _ ≤ ∫ t in 0..1, (L : ℝ) * t * ‖y - x‖ ^ (2 : ℕ) := hmono
    _ = ((L : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ) := by
          calc
            ∫ t in 0..1, (L : ℝ) * t * ‖y - x‖ ^ (2 : ℕ)
              = ∫ t in 0..1, ((L : ℝ) * ‖y - x‖ ^ (2 : ℕ)) * t := by
                  congr with t
                  ring
            _ = ((L : ℝ) * ‖y - x‖ ^ (2 : ℕ)) * (1 / 2 : ℝ) := by
                  rw [intervalIntegral.integral_const_mul, integral_id]
                  norm_num
            _ = ((L : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ) := by
                  ring

-- Proof sketch: use the owner hypothesis `hf : HessianLipschitzOn L 𝓕 f` to localize the Chapter 1
-- quadratic Taylor-model estimate to the segment from `x` to `y` inside `𝓕`. The canonical owner
-- `secondOrderTaylorModelAt f x` packages the affine and quadratic terms, so the public statement
-- does not keep a second expanded copy of that data.
/-- Lemma 4.1.1 (2): if `f` has `L`-Lipschitz Hessian on `𝓕`, then for `x, y ∈ 𝓕` the
second-order Taylor remainder of `f` at `x` is bounded by `(L / 6) * ‖y - x‖³`. -/
theorem secondOrderTaylorModel_error_le
    (hf : HessianLipschitzOn L 𝓕 f)
    (x y : E) (hx : x ∈ 𝓕) (hy : y ∈ 𝓕) :
    |f y - secondOrderTaylorModelAt f x y| ≤
      ((L : ℝ) / 6) * ‖y - x‖ ^ (3 : ℕ) := by
  let r : ℝ → ℝ := fun u ↦
    inner ℝ (∇ f (x + u • (y - x))) (y - x) - inner ℝ (∇ f x) (y - x) -
      u * inner ℝ (hessian f x (y - x)) (y - x)
  have hcont_r :
      ContinuousOn r (Set.Icc (0 : ℝ) 1) := by
    have hmaps :
        Set.MapsTo (fun u : ℝ ↦ x + u • (y - x)) (Set.Icc (0 : ℝ) 1) 𝓕 := by
      intro u hu
      exact segment_mem_of_hessianLipschitzOn (hf := hf) hx hy hu
    have hcontGrad :
        ContinuousOn (fun u : ℝ ↦ ∇ f (x + u • (y - x))) (Set.Icc (0 : ℝ) 1) :=
      (gradient_continuousOn (hf := hf)).comp
        (continuousOn_const.add (continuousOn_id.smul continuousOn_const))
        hmaps
    have hconstGrad : ContinuousOn (fun _ : ℝ ↦ inner ℝ (∇ f x) (y - x)) (Set.Icc (0 : ℝ) 1) :=
      continuousOn_const
    have hlin :
        ContinuousOn (fun u : ℝ ↦ inner ℝ (hessian f x (y - x)) (y - x) * u) (Set.Icc (0 : ℝ) 1) :=
      continuousOn_const.mul continuousOn_id
    -- Assemble the segment remainder from continuous pieces on `[0,1]`.
    simpa [r, mul_comm] using (hcontGrad.inner continuousOn_const).sub hconstGrad |>.sub hlin
  have hint_r : IntervalIntegrable r MeasureTheory.volume 0 1 := by
    exact hcont_r.intervalIntegrable_of_Icc (show (0 : ℝ) ≤ 1 by norm_num)
  have hint_bound :
      IntervalIntegrable (fun u : ℝ ↦ (((L : ℝ) / 2) * ‖y - x‖ ^ (3 : ℕ)) * u ^ (2 : ℕ))
        MeasureTheory.volume 0 1 :=
    by
      exact (continuousOn_const.mul (continuousOn_id.pow 2)).intervalIntegrable_of_Icc
        (show (0 : ℝ) ≤ 1 by norm_num)
  have houter :
      f y - secondOrderTaylorModelAt f x y = ∫ u in 0..1, r u := by
    -- Route correction: rewrite through the canonical quadratic Taylor model first, then use the
    -- segment scalar remainder identity instead of expanding ad hoc polynomial terms.
    rw [secondOrderTaylorModelAt_apply]
    have hmodel :
        f y -
            (f x + inner ℝ (∇ f x) (y - x) +
              (1 / 2 : ℝ) * inner ℝ (hessian f x (y - x)) (y - x)) =
          f y - f x - inner ℝ (∇ f x) (y - x) -
            (1 / 2 : ℝ) * inner ℝ (hessian f x (y - x)) (y - x) := by
      ring
    rw [hmodel, second_order_remainder_eq_double_integral (hf := hf) (x := x) (y := y) hx hy]
    have hsplit :
        ∫ u in 0..1, ∫ s in 0..u,
            inner ℝ ((hessian f (x + s • (y - x)) - hessian f x) (y - x)) (y - x) =
          ∫ u in 0..1, r u := by
      refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
      intro u hu
      have hu' : u ∈ Set.Icc (0 : ℝ) 1 := by
        have hu0 : 0 < u := by
          simpa [min_eq_left (show (0 : ℝ) ≤ 1 by norm_num)] using hu.1
        have hu1 : u ≤ 1 := by
          simpa [max_eq_right (show (0 : ℝ) ≤ 1 by norm_num)] using hu.2
        exact ⟨le_of_lt hu0, hu1⟩
      symm
      simpa [r] using
        segment_gradient_pair_remainder_eq_integral (hf := hf) (x := x) (y := y) hx hy u hu'
    exact hsplit
  have hr_bound :
      ∀ u ∈ Set.Icc (0 : ℝ) 1,
        |r u| ≤ (((L : ℝ) / 2) * ‖y - x‖ ^ (3 : ℕ)) * u ^ (2 : ℕ) := by
    intro u hu
    have hintInner :
        IntervalIntegrable
          (fun s : ℝ ↦ inner ℝ ((hessian f (x + s • (y - x)) - hessian f x) (y - x)) (y - x))
          MeasureTheory.volume 0 u := by
      have hcontInner :
          ContinuousOn
            (fun s : ℝ ↦ inner ℝ ((hessian f (x + s • (y - x)) - hessian f x) (y - x)) (y - x))
            (Set.uIcc (0 : ℝ) u) := by
        have hmaps :
            Set.MapsTo (fun s : ℝ ↦ x + s • (y - x)) (Set.uIcc (0 : ℝ) u) 𝓕 := by
          intro s hs
          have hsI : s ∈ Set.Icc (0 : ℝ) u := by
            simpa [Set.uIcc_of_le hu.1] using hs
          exact segment_mem_of_hessianLipschitzOn (hf := hf) hx hy ⟨hsI.1, hsI.2.trans hu.2⟩
        have hcontHd :
            ContinuousOn (fun s : ℝ ↦ (hessian f (x + s • (y - x)) - hessian f x) (y - x))
              (Set.uIcc (0 : ℝ) u) := by
          have hcontH :
              ContinuousOn (fun s : ℝ ↦ hessian f (x + s • (y - x)) - hessian f x)
                (Set.uIcc (0 : ℝ) u) :=
            (hf.continuousOn_hessian.comp
              (continuousOn_const.add (continuousOn_id.smul continuousOn_const))
              hmaps).sub continuousOn_const
          exact hcontH.clm_apply continuousOn_const
        exact hcontHd.inner continuousOn_const
      exact hcontInner.intervalIntegrable
    have hintMajorant :
        IntervalIntegrable (fun s : ℝ ↦ (L : ℝ) * s * ‖y - x‖ ^ (3 : ℕ))
          MeasureTheory.volume 0 u := by
      have huIcc :
          ContinuousOn (fun s : ℝ ↦ (L : ℝ) * s * ‖y - x‖ ^ (3 : ℕ))
            (Set.uIcc (0 : ℝ) u) :=
        (continuousOn_const.mul continuousOn_id).mul continuousOn_const
      exact huIcc.intervalIntegrable
    have hmono :
        ∫ s in 0..u, |inner ℝ ((hessian f (x + s • (y - x)) - hessian f x) (y - x)) (y - x)|
          ≤ ∫ s in 0..u, (L : ℝ) * s * ‖y - x‖ ^ (3 : ℕ) := by
      -- Bound the inner Hessian remainder by the cubic majorant on `[0,u]`.
      refine intervalIntegral.integral_mono_on hu.1 hintInner.norm hintMajorant ?_
      intro s hs
      exact segment_hessian_quadratic_bound (hf := hf) (x := x) (y := y) hx hy
        ⟨hs.1, hs.2.trans hu.2⟩
    have hremainder :
        r u =
          ∫ s in 0..u, inner ℝ ((hessian f (x + s • (y - x)) - hessian f x) (y - x)) (y - x) := by
      exact segment_gradient_pair_remainder_eq_integral (hf := hf) (x := x) (y := y) hx hy u hu
    -- Estimate the inner remainder by integrating the cubic majorant on `[0,u]`.
    calc
      |r u|
        = |∫ s in 0..u, inner ℝ ((hessian f (x + s • (y - x)) - hessian f x) (y - x)) (y - x)| := by
            rw [hremainder]
      _ ≤ ∫ s in 0..u,
            |inner ℝ ((hessian f (x + s • (y - x)) - hessian f x) (y - x)) (y - x)| := by
            exact intervalIntegral.abs_integral_le_integral_abs
              (f := fun s : ℝ ↦
                inner ℝ ((hessian f (x + s • (y - x)) - hessian f x) (y - x)) (y - x))
              hu.1
      _ ≤ ∫ s in 0..u, (L : ℝ) * s * ‖y - x‖ ^ (3 : ℕ) := hmono
      _ = (((L : ℝ) / 2) * ‖y - x‖ ^ (3 : ℕ)) * u ^ (2 : ℕ) := by
            calc
              ∫ s in 0..u, (L : ℝ) * s * ‖y - x‖ ^ (3 : ℕ)
                = ∫ s in 0..u, ((L : ℝ) * ‖y - x‖ ^ (3 : ℕ)) * s := by
                    congr with s
                    ring
              _ = ((L : ℝ) * ‖y - x‖ ^ (3 : ℕ)) * (u ^ (2 : ℕ) / 2) := by
                    rw [intervalIntegral.integral_const_mul, integral_id]
                    ring
              _ = (((L : ℝ) / 2) * ‖y - x‖ ^ (3 : ℕ)) * u ^ (2 : ℕ) := by
                    ring
  have hmono_outer :
      ∫ u in 0..1, |r u| ≤
        ∫ u in 0..1, (((L : ℝ) / 2) * ‖y - x‖ ^ (3 : ℕ)) * u ^ (2 : ℕ) := by
    -- Apply the pointwise segment remainder bound on the full outer interval.
    refine intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ 1 by norm_num)
      hint_r.norm hint_bound ?_
    intro u hu
    exact hr_bound u hu
  -- Integrate `|r(u)| ≤ (L / 2) ‖y - x‖³ u²` and compute `∫₀¹ u² = 1 / 3`.
  calc
    |f y - secondOrderTaylorModelAt f x y| = |∫ u in 0..1, r u| := by
      rw [houter]
    _ ≤ ∫ u in 0..1, |r u| := by
      exact intervalIntegral.abs_integral_le_integral_abs (f := r) (show (0 : ℝ) ≤ 1 by norm_num)
    _ ≤ ∫ u in 0..1, (((L : ℝ) / 2) * ‖y - x‖ ^ (3 : ℕ)) * u ^ (2 : ℕ) := hmono_outer
    _ = ((L : ℝ) / 6) * ‖y - x‖ ^ (3 : ℕ) := by
          rw [intervalIntegral.integral_const_mul, integral_pow]
          ring

end HessianLipschitzOn

end
