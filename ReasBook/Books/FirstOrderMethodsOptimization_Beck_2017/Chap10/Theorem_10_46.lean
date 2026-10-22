/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_43

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

variable {E : Type u} {V : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/- Theorem 10.46 is `bridge/view`: the underlying analytic owners are still `ConvexOn`,
`is_l_smooth_on`, and the Chapter 10 smooth-approximation interface from Definition 10.43. Domain
sampling in the project and mathlib shows that affine transport results are organized around the
owner abstractions `AffineMap` and `ContinuousAffineMap`, with the concrete source formula
`x ↦ A x + b` treated as a specialization. The nonnegative-parameter companion owner already lives
in Definition 10.43, so this file records the closure operations as derived API on
`IsSmoothApproximationNonneg`, keeps the continuous-affine precomposition theorem as the public
core, and derives the `x ↦ A x + b` form as a bridge. -/

namespace IsSmoothApproximationNonneg

/-- Helper for Theorem 10.46: a nonnegative weighted sum of globally smooth functions is globally
smooth, with smoothness constant given by the same weighted sum. -/
lemma is_l_smooth_on_nonneg_weighted_sum
    {f1 f2 : E → ℝ} {L1 L2 gamma1 gamma2 : NNReal}
    (hs1 : is_l_smooth_on f1 Set.univ L1)
    (hs2 : is_l_smooth_on f2 Set.univ L2) :
    is_l_smooth_on
      (fun x ↦ (gamma1 : ℝ) * f1 x + (gamma2 : ℝ) * f2 x)
      Set.univ
      (gamma1 * L1 + gamma2 * L2) := by
  -- Rewrite smoothness into differentiability plus the textbook derivative-Lipschitz estimate.
  rw [is_l_smooth_on_iff] at hs1 hs2 ⊢
  refine ⟨?_, ?_⟩
  · intro x hx
    -- Each weighted summand is differentiable, hence so is their sum.
    simpa [smul_eq_mul] using
      ((hs1.1 x hx).const_smul (gamma1 : ℝ)).add ((hs2.1 x hx).const_smul (gamma2 : ℝ))
  · intro x hx y hy
    have hxderiv :
        fderiv ℝ (fun z ↦ (gamma1 : ℝ) * f1 z + (gamma2 : ℝ) * f2 z) x =
          (gamma1 : ℝ) • fderiv ℝ f1 x + (gamma2 : ℝ) • fderiv ℝ f2 x := by
      -- Compute the derivative of the weighted sum using the sum rule and constant-scalar rule.
      have hsmul :
          fderiv ℝ (((gamma1 : ℝ) • f1) + ((gamma2 : ℝ) • f2)) x =
            (gamma1 : ℝ) • fderiv ℝ f1 x + (gamma2 : ℝ) • fderiv ℝ f2 x := by
        rw [fderiv_add
          ((hs1.1 x hx).const_smul (gamma1 : ℝ))
          ((hs2.1 x hx).const_smul (gamma2 : ℝ))]
        simp [fderiv_const_smul_field]
      simpa [Pi.smul_apply, smul_eq_mul] using hsmul
    have hyderiv :
        fderiv ℝ (fun z ↦ (gamma1 : ℝ) * f1 z + (gamma2 : ℝ) * f2 z) y =
          (gamma1 : ℝ) • fderiv ℝ f1 y + (gamma2 : ℝ) • fderiv ℝ f2 y := by
      -- The same derivative formula holds at the second point.
      have hsmul :
          fderiv ℝ (((gamma1 : ℝ) • f1) + ((gamma2 : ℝ) • f2)) y =
            (gamma1 : ℝ) • fderiv ℝ f1 y + (gamma2 : ℝ) • fderiv ℝ f2 y := by
        rw [fderiv_add
          ((hs1.1 y hy).const_smul (gamma1 : ℝ))
          ((hs2.1 y hy).const_smul (gamma2 : ℝ))]
        simp [fderiv_const_smul_field]
      simpa [Pi.smul_apply, smul_eq_mul] using hsmul
    have hsub :
        (gamma1 : ℝ) • fderiv ℝ f1 x + (gamma2 : ℝ) • fderiv ℝ f2 x -
            ((gamma1 : ℝ) • fderiv ℝ f1 y + (gamma2 : ℝ) • fderiv ℝ f2 y) =
          (gamma1 : ℝ) • (fderiv ℝ f1 x - fderiv ℝ f1 y) +
            (gamma2 : ℝ) • (fderiv ℝ f2 x - fderiv ℝ f2 y) := by
      -- Reassociate the subtraction so the triangle inequality applies termwise.
      ext z
      simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    calc
      ‖fderiv ℝ (fun z ↦ (gamma1 : ℝ) * f1 z + (gamma2 : ℝ) * f2 z) x -
          fderiv ℝ (fun z ↦ (gamma1 : ℝ) * f1 z + (gamma2 : ℝ) * f2 z) y‖
          =
          ‖(gamma1 : ℝ) • (fderiv ℝ f1 x - fderiv ℝ f1 y) +
              (gamma2 : ℝ) • (fderiv ℝ f2 x - fderiv ℝ f2 y)‖ := by
            rw [hxderiv, hyderiv, hsub]
      _ ≤ ‖(gamma1 : ℝ) • (fderiv ℝ f1 x - fderiv ℝ f1 y)‖ +
            ‖(gamma2 : ℝ) • (fderiv ℝ f2 x - fderiv ℝ f2 y)‖ := norm_add_le _ _
      _ = (gamma1 : ℝ) * ‖fderiv ℝ f1 x - fderiv ℝ f1 y‖ +
            (gamma2 : ℝ) * ‖fderiv ℝ f2 x - fderiv ℝ f2 y‖ := by
            simp [norm_smul]
      _ ≤ (gamma1 : ℝ) * ((L1 : ℝ) * ‖x - y‖) +
            (gamma2 : ℝ) * ((L2 : ℝ) * ‖x - y‖) := by
            gcongr
            · exact hs1.2 x hx y hy
            · exact hs2.2 x hx y hy
      _ = ((gamma1 * L1 + gamma2 * L2 : NNReal) : ℝ) * ‖x - y‖ := by
            simp [add_mul, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Theorem 10.46: differentiating a real-valued function after precomposition by a
continuous affine map amounts to composing the derivative with the affine map's linear part. -/
lemma fderiv_comp_continuousAffineMap
    {f : V → ℝ} {φ : E →ᴬ[ℝ] V} {x : E}
    (hf : DifferentiableAt ℝ f (φ x)) :
    fderiv ℝ (fun z ↦ f (φ z)) x = (fderiv ℝ f (φ x)).comp φ.contLinear := by
  -- Use the chain rule together with the canonical derivative of a continuous affine map.
  have hcomp : fderiv ℝ (f ∘ φ) x = (fderiv ℝ f (φ x)).comp φ.contLinear := by
    rw [fderiv_comp x hf φ.differentiableAt, φ.fderiv]
  simpa [Function.comp] using hcomp

/-- Helper for Theorem 10.46: the displacement of a continuous affine map is controlled by the
operator norm of its linear part. -/
lemma continuousAffineMap_norm_sub_le
    (φ : E →ᴬ[ℝ] V) (x y : E) :
    ‖φ x - φ y‖ ≤ ‖φ.contLinear‖ * ‖x - y‖ := by
  -- Rewrite the affine difference through the linear part, then apply the operator-norm bound.
  have hmap : φ.contLinear (x - y) = φ x - φ y := by
    simpa [vsub_eq_sub] using φ.contLinear_map_vsub x y
  calc
    ‖φ x - φ y‖ = ‖φ.contLinear (x - y)‖ := by rw [hmap]
    _ ≤ ‖φ.contLinear‖ * ‖x - y‖ := φ.contLinear.le_opNorm (x - y)

/-- Helper for Theorem 10.46: precomposing a globally smooth function with a continuous affine map
multiplies the smoothness constant by the square of the operator norm of the linear part. -/
lemma is_l_smooth_on_precompose_continuousAffineMap
    {f : V → ℝ} {φ : E →ᴬ[ℝ] V} {L : NNReal}
    (hs : is_l_smooth_on f Set.univ L) :
    is_l_smooth_on
      (fun x ↦ f (φ x))
      Set.univ
      (L * ‖φ.contLinear‖₊ ^ (2 : ℕ)) := by
  -- Rewrite smoothness into differentiability plus a derivative-Lipschitz estimate.
  rw [is_l_smooth_on_iff] at hs ⊢
  refine ⟨?_, ?_⟩
  · intro x hx
    -- Differentiability is preserved under composition with the affine map.
    exact ((hs.1 (φ x) (by simp)).hasFDerivAt.comp x φ.hasFDerivAt).differentiableAt
  · intro x hx y hy
    have hxderiv :
        fderiv ℝ (fun z ↦ f (φ z)) x =
          (fderiv ℝ f (φ x)).comp φ.contLinear :=
      fderiv_comp_continuousAffineMap (x := x) (φ := φ) (hs.1 (φ x) (by simp))
    have hyderiv :
        fderiv ℝ (fun z ↦ f (φ z)) y =
          (fderiv ℝ f (φ y)).comp φ.contLinear :=
      fderiv_comp_continuousAffineMap (x := y) (φ := φ) (hs.1 (φ y) (by simp))
    have hsub :
        (fderiv ℝ f (φ x)).comp φ.contLinear -
            (fderiv ℝ f (φ y)).comp φ.contLinear =
          (fderiv ℝ f (φ x) - fderiv ℝ f (φ y)).comp φ.contLinear := by
      -- Move the subtraction inside the left factor before applying the operator-norm estimate.
      ext z
      rfl
    calc
      ‖fderiv ℝ (fun z ↦ f (φ z)) x - fderiv ℝ (fun z ↦ f (φ z)) y‖
          =
          ‖(fderiv ℝ f (φ x) - fderiv ℝ f (φ y)).comp φ.contLinear‖ := by
            rw [hxderiv, hyderiv, hsub]
      _ ≤ ‖fderiv ℝ f (φ x) - fderiv ℝ f (φ y)‖ * ‖φ.contLinear‖ := by
            exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (L : ℝ) * ‖φ x - φ y‖ * ‖φ.contLinear‖ := by
            gcongr
            exact hs.2 (φ x) (by simp) (φ y) (by simp)
      _ ≤ (L : ℝ) * (‖φ.contLinear‖ * ‖x - y‖) * ‖φ.contLinear‖ := by
            gcongr
            exact continuousAffineMap_norm_sub_le φ x y
      _ = ((L * ‖φ.contLinear‖₊ ^ (2 : ℕ)) : ℝ) * ‖x - y‖ := by
            simp [pow_two, mul_left_comm, mul_comm]

-- Proof sketch: combine the convexity and pointwise approximation inequalities termwise, then use
-- the sum rule for derivatives together with the Lipschitz estimates scaled by `gamma1` and
-- `gamma2`.
/-- Theorem 10.46 (1): a nonnegative linear combination of two `1 / μ`-smooth approximations is a
`1 / μ`-smooth approximation of the corresponding nonnegative linear combination, with parameters
obtained by the same linear combination. -/
theorem nonneg_weighted_sum
    {h1 h1μ h2 h2μ : E → ℝ} {α1 β1 α2 β2 : NNReal} {μ : PosReal}
    (hh1 : IsSmoothApproximationNonneg h1 h1μ α1 β1 μ)
    (hh2 : IsSmoothApproximationNonneg h2 h2μ α2 β2 μ)
    (gamma1 gamma2 : NNReal) :
    IsSmoothApproximationNonneg
      (fun x ↦ (gamma1 : ℝ) * h1 x + (gamma2 : ℝ) * h2 x)
      (fun x ↦ (gamma1 : ℝ) * h1μ x + (gamma2 : ℝ) * h2μ x)
      (gamma1 * α1 + gamma2 * α2)
      (gamma1 * β1 + gamma2 * β2)
      μ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Convexity is preserved by nonnegative scaling and addition.
    simpa [smul_eq_mul] using (hh1.convex.smul gamma1.2).add (hh2.convex.smul gamma2.2)
  · intro x
    -- The lower approximation bounds combine termwise.
    gcongr
    · exact hh1.lower_le x
    · exact hh2.lower_le x
  · intro x
    -- The upper approximation bounds combine termwise, and the error coefficients add.
    have h1upper : (gamma1 : ℝ) * h1 x ≤ (gamma1 : ℝ) * (h1μ x + (β1 : ℝ) * (μ : ℝ)) :=
      mul_le_mul_of_nonneg_left (hh1.upper_le x) gamma1.2
    have h2upper : (gamma2 : ℝ) * h2 x ≤ (gamma2 : ℝ) * (h2μ x + (β2 : ℝ) * (μ : ℝ)) :=
      mul_le_mul_of_nonneg_left (hh2.upper_le x) gamma2.2
    calc
      (gamma1 : ℝ) * h1 x + (gamma2 : ℝ) * h2 x
          ≤ (gamma1 : ℝ) * (h1μ x + (β1 : ℝ) * (μ : ℝ)) +
              (gamma2 : ℝ) * (h2μ x + (β2 : ℝ) * (μ : ℝ)) := add_le_add h1upper h2upper
      _ =
          (gamma1 : ℝ) * h1μ x + (gamma2 : ℝ) * h2μ x +
            (((gamma1 * β1 + gamma2 * β2 : NNReal) : ℝ) * (μ : ℝ)) := by
            rw [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mul]
            ring
  · -- Smoothness is exactly the weighted-sum smoothness helper applied to the two models.
    simpa [div_eq_mul_inv, add_mul, mul_add, mul_assoc, mul_left_comm, mul_comm] using
      is_l_smooth_on_nonneg_weighted_sum
        (gamma1 := gamma1)
        (gamma2 := gamma2)
        hh1.smooth
        hh2.smooth

/-- Theorem 10.46 (2): precomposing a `1 / μ`-smooth approximation with a continuous affine map
`φ` multiplies the smoothness parameter by `‖φ.contLinear‖²` and leaves the error parameter
unchanged. -/
theorem precompose_continuousAffineMap
    {h hμ : V → ℝ} {α β : NNReal} {μ : PosReal}
    (hh : IsSmoothApproximationNonneg h hμ α β μ)
    (φ : E →ᴬ[ℝ] V) :
    IsSmoothApproximationNonneg
      (fun x ↦ h (φ x))
      (fun x ↦ hμ (φ x))
      (α * ‖φ.contLinear‖₊ ^ (2 : ℕ))
      β
      μ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Convexity is preserved under affine precomposition.
    simpa [Function.comp] using hh.convex.comp_affineMap (φ : E →ᵃ[ℝ] V)
  · intro x
    -- The lower approximation bound is evaluated at `φ x`.
    simpa using hh.lower_le (φ x)
  · intro x
    -- The upper approximation bound is evaluated at `φ x`.
    simpa using hh.upper_le (φ x)
  · -- The chain rule and two operator-norm estimates yield the new smoothness constant.
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      is_l_smooth_on_precompose_continuousAffineMap
        (φ := φ)
        (L := α / PosReal.toNNReal μ)
        hh.smooth

-- Proof sketch: instantiate the canonical continuous affine owner with
-- `A.toContinuousAffineMap + ContinuousAffineMap.const ℝ E b`; its linear part is `A`, and its
-- value at `x` is `A x + b`.
/-- Source-facing specialization of Theorem 10.46 (2) to affine maps written as `x ↦ A x + b`. -/
theorem precompose_linearMap_add
    {h hμ : V → ℝ} {α β : NNReal} {μ : PosReal}
    (hh : IsSmoothApproximationNonneg h hμ α β μ)
    (A : E →L[ℝ] V) (b : V) :
    IsSmoothApproximationNonneg
      (fun x ↦ h (A x + b))
      (fun x ↦ hμ (A x + b))
      (α * ‖A‖₊ ^ (2 : ℕ))
      β
      μ := by
  simpa [ContinuousAffineMap.add_contLinear] using
    hh.precompose_continuousAffineMap
      (A.toContinuousAffineMap + ContinuousAffineMap.const ℝ E b)

end IsSmoothApproximationNonneg

end
