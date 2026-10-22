/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Analysis.InnerProductSpace.NormPow
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_16
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_4_19
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_4_20
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient
open scoped CubicRegularizationResidual

noncomputable section

universe u

/- Lemma 4.1.2 lies in the cubic-regularization / Hessian-positivity domain on real Hilbert
spaces, with a Euclidean matrix bridge.

Sampled owner declarations:
* `IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ y` in
  `Definition_4_1_3`, the canonical owner for a global minimizer of the cubic model;
* `hessian` in `Chap01/Definition_1_4_16`, the intrinsic Hessian operator owner;
* `ContinuousLinearMap.IsPositive`, the canonical positivity owner for self-adjoint operators;
* `LinearMap.posSemidef_toMatrix_iff`, the Euclidean matrix bridge from operator positivity to
  `Matrix.PosSemidef`.

Source/core/bridge triage:
* source-facing: the lower bound for the regularized Hessian at a cubic model minimizer;
* core/canonical: positivity of the intrinsic operator
  `hessian f x + ((M / 2) * r_M(x)) • 1`;
* bridge/view: the Euclidean matrix restatement
  `∇² f x + ((M / 2) * r_M(x)) I_n`.

Primitive data:
* the regularization parameter `M`
* the base point `x`
* the current cubic-model minimizer `trialPoint`
* the owner minimality hypothesis
  `IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ trialPoint`
* the pointwise `C²` hypothesis `ContDiffAt ℝ 2 f x`, needed for Hessian symmetry

Derived API:
* the residual `r[trialPoint] x`
* the intrinsic positivity statement for
  `hessian f x + ((M / 2) * r_M(x)) • 1`
* the Euclidean matrix positivity statement, obtained by transporting that operator positivity to
  the standard orthonormal basis.

This file therefore keeps the public statement on the canonical `IsMinOn` owner and the intrinsic
Hessian operator, and treats the Euclidean matrix form only as the thin coordinate bridge required
by later `ℝⁿ` files. -/

section Intrinsic

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Helper for Lemma 4.1.2: restricting the cubic model to the affine line through the minimizer
preserves local minimality at the line parameter `0`. -/
lemma cubic_model_line_isLocalMin_at_zero
    {f : E → ℝ} {M : ℝ} {x trialPoint : E}
    (hmin :
      IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ trialPoint)
    (v : E) :
    IsLocalMin
      (fun t : ℝ ↦ cubicRegularizationQuadraticApproximation f M x (trialPoint + t • v))
      0 := by
  -- The whole-space minimizer is already a local minimizer in the ambient space.
  have hlocal :
      IsLocalMin (cubicRegularizationQuadraticApproximation f M x) trialPoint :=
    hmin.isLocalMin (by simp)
  have hlocal0 :
      IsLocalMin
        (cubicRegularizationQuadraticApproximation f M x)
        (trialPoint + (0 : ℝ) • v) := by
    simpa using hlocal
  -- Compose that local minimality with the continuous affine line through `trialPoint`.
  have hline :
      ContinuousAt (fun t : ℝ ↦ trialPoint + t • v) 0 := by
    simpa [one_smul] using
      (HasDerivAt.const_add trialPoint ((hasDerivAt_id 0).smul_const v)).continuousAt
  -- Repackage the slice as a composition so the local-minimum composition lemma applies directly.
  change IsLocalMin
    ((cubicRegularizationQuadraticApproximation f M x) ∘
      (fun t : ℝ ↦ trialPoint + t • v)) 0
  exact hlocal0.comp_continuous (g := fun t : ℝ ↦ trialPoint + t • v) (b := 0) hline

/-- Helper for Lemma 4.1.2: the quadratic Taylor slice along `trialPoint + t • v` has the same
second derivative at `0` as the ambient Hessian quadratic form in direction `v`. -/
lemma quadratic_slice_hessian_quadratic_at_zero
    {f : E → ℝ} {x trialPoint : E}
    (hf : ContDiffAt ℝ 2 f x)
    (v : E) :
    inner ℝ
        (hessian (fun t : ℝ ↦ secondOrderTaylorModelAt f x (trialPoint + t • v)) 0 1) 1 =
      inner ℝ (hessian f x v) v := by
  let a : E := trialPoint - x
  let T : E →L[ℝ] E := hessian f x
  let g : E := ∇ f x
  let A : ℝ := inner ℝ g v + inner ℝ (T a) v
  let B : ℝ := inner ℝ (T v) v
  have hselfAdjoint : IsSelfAdjoint T := by
    simpa using (fderiv_gradient_isSymmetric_of_contDiffAt hf).isSelfAdjoint
  have hcross :
      inner ℝ (T v) a = inner ℝ (T a) v := by
    calc
      inner ℝ (T v) a = inner ℝ v (T a) := hselfAdjoint.isSymmetric v a
      _ = inner ℝ (T a) v := by rw [real_inner_comm]
  have hpoly :
      (fun t : ℝ ↦ secondOrderTaylorModelAt f x (trialPoint + t • v)) =
        fun t : ℝ ↦
          secondOrderTaylorModelAt f x trialPoint +
            A * t +
            (B / 2 : ℝ) * t ^ (2 : ℕ) := by
    -- Expand the Taylor model along the affine line and collect the scalar polynomial terms.
    funext t
    have hdisp : trialPoint + t • v - x = a + t • v := by
      simp [a, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    rw [secondOrderTaylorModelAt_apply, secondOrderTaylorModelAt_apply, hdisp]
    simp [A, B, T, g, a, hcross, inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right, pow_two]
    ring
  have hgradEq :
      ∇ (fun t : ℝ ↦ secondOrderTaylorModelAt f x (trialPoint + t • v)) =
        fun t : ℝ ↦ A + B * t := by
    -- Differentiate the scalar polynomial description pointwise and recover the gradient on `ℝ`.
    refine gradient_eq ?_
    intro t
    rw [hpoly]
    have hderiv :
        HasDerivAt
          (fun s : ℝ ↦
            secondOrderTaylorModelAt f x trialPoint +
              A * s +
              (B / 2 : ℝ) * s ^ (2 : ℕ))
          (A + B * t) t := by
      have hlin :
          HasDerivAt (fun s : ℝ ↦ A * s) A t := by
        simpa using (HasDerivAt.const_mul A (hasDerivAt_id t))
      have hquad :
          HasDerivAt (fun s : ℝ ↦ (B / 2 : ℝ) * s ^ (2 : ℕ)) (B * t) t := by
        have hquadBase :
            HasDerivAt (fun s : ℝ ↦ (B / 2 : ℝ) * s ^ (2 : ℕ)) ((B / 2 : ℝ) * (2 * t)) t := by
          simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using
            (HasDerivAt.const_mul (B / 2 : ℝ) ((hasDerivAt_id t).pow 2))
        convert hquadBase using 1
        ring
      simpa [add_assoc, add_left_comm, add_comm] using
        (HasDerivAt.const_add (secondOrderTaylorModelAt f x trialPoint) (hlin.add hquad))
    simpa [gradient_eq_deriv'] using hderiv.hasGradientAt'
  have hgradDeriv :
      HasDerivAt
        (fun t : ℝ ↦ ∇ (fun s : ℝ ↦ secondOrderTaylorModelAt f x (trialPoint + s • v)) t)
        B 0 := by
    -- The gradient polynomial is affine, so its derivative at `0` is exactly `B`.
    rw [hgradEq]
    simpa [B] using (HasDerivAt.const_add A ((hasDerivAt_id 0).const_mul B))
  -- Rewrite the one-dimensional Hessian through the affine gradient formula.
  have hhessEval :
      hessian (fun t : ℝ ↦ secondOrderTaylorModelAt f x (trialPoint + t • v)) 0 1 = B := by
    rw [hessian]
    calc
      fderiv ℝ (∇ fun t : ℝ ↦ secondOrderTaylorModelAt f x (trialPoint + t • v)) 0 1
        = deriv (∇ fun t : ℝ ↦ secondOrderTaylorModelAt f x (trialPoint + t • v)) 0 := by
            simpa using
              (fderiv_eq_deriv_mul
                (f := ∇ fun t : ℝ ↦ secondOrderTaylorModelAt f x (trialPoint + t • v))
                (x := 0) (y := (1 : ℝ)))
      _ = B := by
          simpa using hgradDeriv.deriv
  have hsliceEval :
      inner ℝ (hessian (fun t : ℝ ↦ secondOrderTaylorModelAt f x (trialPoint + t • v)) 0 1) 1 =
        B := by
    calc
    inner ℝ (hessian (fun t : ℝ ↦ secondOrderTaylorModelAt f x (trialPoint + t • v)) 0 1) 1
      = inner ℝ B 1 := by
          exact congrArg (fun z : ℝ ↦ inner ℝ z 1) hhessEval
    _ = B := by
      change 1 * B = B
      ring
  simpa [B, T] using hsliceEval

/-- Helper for Lemma 4.1.2: the scalar function `t ↦ t * |t|` has derivative `0` at `0`. -/
lemma t_mul_abs_hasDerivAt_zero :
    HasDerivAt (fun t : ℝ ↦ t * |t|) 0 0 := by
  -- Rewrite the derivative at `0` as a slope-limit statement and bound the slope by `|t|`.
  rw [hasDerivAt_iff_tendsto_slope_zero, tendsto_zero_iff_norm_tendsto_zero]
  refine @squeeze_zero ℝ
    (fun t : ℝ ↦ ‖t⁻¹ • (((0 : ℝ) + t) * |(0 : ℝ) + t| - (((0 : ℝ) * |(0 : ℝ)|)))‖)
    (fun t : ℝ ↦ |t|)
    (nhdsWithin (0 : ℝ) {0}ᶜ)
    ?_
    ?_
    ?_
  · intro t
    exact norm_nonneg _
  · intro t
    by_cases ht : t = 0
    · simp [ht]
    · calc
        ‖t⁻¹ • (((0 : ℝ) + t) * |(0 : ℝ) + t| - (((0 : ℝ) * |(0 : ℝ)|)))‖
            = ‖t⁻¹ * (t * |t|)‖ := by
                simp [smul_eq_mul, ht]
        _ = |t⁻¹ * (t * |t|)| := by
              simp [Real.norm_eq_abs]
        _ = |t| := by
              rw [abs_mul, abs_mul, abs_inv, abs_abs]
              field_simp [abs_ne_zero.mpr ht]
        _ ≤ |t| := le_rfl
  · simpa using
      (continuous_abs.continuousAt : ContinuousAt abs (0 : ℝ)).tendsto.mono_left
        (show nhdsWithin (0 : ℝ) {0}ᶜ ≤ nhds (0 : ℝ) from nhdsWithin_le_nhds)

/-- Helper for Lemma 4.1.2: the cubic penalty slice has the textbook gradient formula along any
affine line. -/
lemma cubic_penalty_slice_gradient_eq
    {M : ℝ} (a v : E) :
    ∇ (fun t : ℝ ↦ (M / 6 : ℝ) * ‖a + t • v‖ ^ (3 : ℕ)) =
      fun t ↦ (M / 2 : ℝ) * ‖a + t • v‖ * inner ℝ (a + t • v) v := by
  have hthree : 1 < (3 : ℝ) := by
    norm_num
  -- Differentiate the norm-power through the affine line and convert the scalar derivative to a
  -- gradient on `ℝ`.
  refine gradient_eq ?_
  intro t
  have hline : HasDerivAt (fun s : ℝ ↦ a + s • v) v t := by
    simpa [one_smul] using
      (HasDerivAt.const_add a ((hasDerivAt_id t).smul_const v))
  have hnorm :
      HasFDerivAt (fun z : E ↦ ‖z‖ ^ (3 : ℝ))
        ((3 * ‖a + t • v‖ ^ ((3 : ℝ) - 2)) • innerSL ℝ (a + t • v))
        (a + t • v) := by
    simpa using (hasFDerivAt_norm_rpow (a + t • v) hthree)
  have hraw0 :
      HasDerivAt (fun s : ℝ ↦ ‖a + s • v‖ ^ (3 : ℝ))
        (((3 : ℝ) * ‖a + t • v‖ ^ ((3 : ℝ) - 2)) * inner ℝ a v +
          ((3 : ℝ) * ‖a + t • v‖ ^ ((3 : ℝ) - 2)) * (t * ‖v‖ ^ (2 : ℕ)))
        t := by
    simpa [Function.comp, innerSL_apply_apply, real_inner_self_eq_norm_sq] using
      HasFDerivAt.comp_hasDerivAt (x := t) hnorm hline
  have hraw :
      HasDerivAt (fun s : ℝ ↦ ‖a + s • v‖ ^ (3 : ℝ))
        (((3 : ℝ) * ‖a + t • v‖ ^ ((3 : ℝ) - 2)) * inner ℝ (a + t • v) v)
        t := by
    -- Repackage the chain-rule derivative through the textbook factor `⟪a + tv, v⟫`.
    convert hraw0 using 1
    rw [inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq]
    simp
    ring
  have hscaled :
      HasDerivAt (fun s : ℝ ↦ (M / 6 : ℝ) * ‖a + s • v‖ ^ (3 : ℝ))
        ((M / 6 : ℝ) *
          (((3 : ℝ) * ‖a + t • v‖ ^ ((3 : ℝ) - 2)) * inner ℝ (a + t • v) v))
        t := by
    simpa [mul_comm] using (HasDerivAt.const_mul (M / 6 : ℝ) hraw)
  convert hscaled.hasGradientAt' using 1
  · ext s
    simp
  · have hexp : ((3 : ℝ) - 2) = 1 := by
      norm_num
    rw [hexp, Real.rpow_one]
    ring

/-- Helper for Lemma 4.1.2: when the cubic residual on the line is zero, the cubic-slice
gradient has derivative `0` at the base parameter `0`. -/
lemma cubic_penalty_slice_gradient_hasDerivAt_zero_of_zero_residual
    {M : ℝ} {a v : E} (ha : a = 0) :
    HasDerivAt
      (fun t : ℝ ↦ (M / 2 : ℝ) * ‖a + t • v‖ * inner ℝ (a + t • v) v)
      0
      0 := by
  subst ha
  -- After normalizing the zero residual, the gradient is a scalar multiple of `t * |t|`.
  have hscaled :
      HasDerivAt
        (fun t : ℝ ↦ ((M / 2 : ℝ) * ‖v‖ ^ (3 : ℕ)) * (t * |t|))
        (((M / 2 : ℝ) * ‖v‖ ^ (3 : ℕ)) * 0)
        0 := by
    simpa using
      (HasDerivAt.const_mul (((M / 2 : ℝ) * ‖v‖ ^ (3 : ℕ)) : ℝ) t_mul_abs_hasDerivAt_zero)
  convert hscaled using 1
  · ext t
    simp [norm_smul, Real.norm_eq_abs, inner_smul_left]
    ring_nf
  · ring

/-- Helper for Lemma 4.1.2: when the cubic residual is nonzero, the cubic-slice gradient has the
textbook derivative at the base parameter `0`. -/
lemma cubic_penalty_slice_gradient_hasDerivAt_zero_of_nonzero_residual
    {M : ℝ} {a v : E} (ha : a ≠ 0) :
    HasDerivAt
      (fun t : ℝ ↦ (M / 2 : ℝ) * ‖a + t • v‖ * inner ℝ (a + t • v) v)
      (((M / 2) * ‖a‖) * ‖v‖ ^ (2 : ℕ) + ((M / 2) / ‖a‖) * (inner ℝ a v) ^ (2 : ℕ))
      0 := by
  have hnorm_nonzero : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have hnorm : HasDerivAt (fun t : ℝ ↦ ‖a + t • v‖) ((inner ℝ a v) / ‖a‖) 0 := by
    have hline : HasDerivAt (fun t : ℝ ↦ a + t • v) v 0 := by
      simpa [one_smul] using
        (HasDerivAt.const_add a ((hasDerivAt_id (0 : ℝ)).smul_const v))
    have hq :
        HasDerivAt
          (fun t : ℝ ↦ inner ℝ (a + t • v) (a + t • v))
          (inner ℝ a v + inner ℝ v a)
          0 := by
      simpa using (HasDerivAt.inner ℝ hline hline)
    have hq' :
        HasDerivAt
          (fun t : ℝ ↦ inner ℝ (a + t • v) (a + t • v))
          (2 * inner ℝ a v)
          0 := by
      convert hq using 1
      rw [real_inner_comm, two_mul]
    have hsq_nonzero : inner ℝ (a + (0 : ℝ) • v) (a + (0 : ℝ) • v) ≠ 0 := by
      simpa [real_inner_self_eq_norm_sq] using (pow_ne_zero 2 hnorm_nonzero)
    have hsqrt :
        HasDerivAt
          (fun t : ℝ ↦ √(inner ℝ (a + t • v) (a + t • v)))
          ((2 * inner ℝ a v) / (2 * √(inner ℝ (a + (0 : ℝ) • v) (a + (0 : ℝ) • v))))
          0 := by
      exact hq'.sqrt hsq_nonzero
    -- Identify the square-root expression with the norm of the affine slice.
    convert hsqrt using 1
    · ext t
      rw [real_inner_self_eq_norm_sq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    · simp
      ring
  have hinner :
      HasDerivAt (fun t : ℝ ↦ inner ℝ (a + t • v) v) (‖v‖ ^ (2 : ℕ)) 0 := by
    have hline : HasDerivAt (fun t : ℝ ↦ a + t • v) v 0 := by
      simpa [one_smul] using
        (HasDerivAt.const_add a ((hasDerivAt_id (0 : ℝ)).smul_const v))
    have hcomp :
        HasDerivAt (fun t : ℝ ↦ inner ℝ v (a + t • v)) (‖v‖ ^ (2 : ℕ)) 0 := by
      simpa [real_inner_self_eq_norm_sq] using
        (HasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) ((innerSL ℝ v).hasFDerivAt) hline)
    simpa [real_inner_comm] using hcomp
  have hmul :
      HasDerivAt
        (fun t : ℝ ↦ ‖a + t • v‖ * inner ℝ (a + t • v) v)
        (((inner ℝ a v) / ‖a‖) * inner ℝ a v + ‖a‖ * ‖v‖ ^ (2 : ℕ))
        0 := by
    -- Differentiate the norm factor and the linear-inner-product factor separately.
    simpa using hnorm.mul hinner
  have hscaled := (HasDerivAt.const_mul (M / 2 : ℝ) hmul)
  convert hscaled using 1
  field_simp [hnorm_nonzero]
  ring

/-- Helper for Lemma 4.1.2: the quadratic Taylor slice has differentiable gradient at the base
parameter `0`, with derivative equal to the ambient Hessian quadratic form. -/
lemma quadratic_slice_gradient_hasDerivAt_zero
    {f : E → ℝ} {x trialPoint : E}
    (hf : ContDiffAt ℝ 2 f x)
    (v : E) :
    HasDerivAt
      (fun t : ℝ ↦ ∇ (fun s : ℝ ↦ secondOrderTaylorModelAt f x (trialPoint + s • v)) t)
      (inner ℝ (hessian f x v) v)
      0 := by
  let a : E := trialPoint - x
  let T : E →L[ℝ] E := hessian f x
  let g : E := ∇ f x
  let A : ℝ := inner ℝ g v + inner ℝ (T a) v
  let B : ℝ := inner ℝ (T v) v
  have hselfAdjoint : IsSelfAdjoint T := by
    simpa using (fderiv_gradient_isSymmetric_of_contDiffAt hf).isSelfAdjoint
  have hcross :
      inner ℝ (T v) a = inner ℝ (T a) v := by
    calc
      inner ℝ (T v) a = inner ℝ v (T a) := hselfAdjoint.isSymmetric v a
      _ = inner ℝ (T a) v := by
          rw [real_inner_comm]
  have hpoly :
      (fun t : ℝ ↦ secondOrderTaylorModelAt f x (trialPoint + t • v)) =
        fun t : ℝ ↦
          secondOrderTaylorModelAt f x trialPoint +
            A * t +
            (B / 2 : ℝ) * t ^ (2 : ℕ) := by
    -- Expand the quadratic model along the line and collect the scalar polynomial terms.
    funext t
    have hdisp : trialPoint + t • v - x = a + t • v := by
      simp [a, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    rw [secondOrderTaylorModelAt_apply, secondOrderTaylorModelAt_apply, hdisp]
    simp [A, B, T, g, a, hcross, inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right, pow_two]
    ring
  have hgradEq :
      ∇ (fun t : ℝ ↦ secondOrderTaylorModelAt f x (trialPoint + t • v)) =
        fun t : ℝ ↦ A + B * t := by
    -- Differentiate the scalar polynomial description pointwise.
    refine gradient_eq ?_
    intro t
    rw [hpoly]
    have hderiv :
        HasDerivAt
          (fun s : ℝ ↦
            secondOrderTaylorModelAt f x trialPoint +
              A * s +
              (B / 2 : ℝ) * s ^ (2 : ℕ))
          (A + B * t)
          t := by
      have hlin : HasDerivAt (fun s : ℝ ↦ A * s) A t := by
        simpa using (HasDerivAt.const_mul A (hasDerivAt_id t))
      have hquad :
          HasDerivAt (fun s : ℝ ↦ (B / 2 : ℝ) * s ^ (2 : ℕ)) (B * t) t := by
        have hquadBase :
            HasDerivAt
              (fun s : ℝ ↦ (B / 2 : ℝ) * s ^ (2 : ℕ))
              ((B / 2 : ℝ) * (2 * t))
              t := by
          simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using
            (HasDerivAt.const_mul (B / 2 : ℝ) ((hasDerivAt_id t).pow 2))
        convert hquadBase using 1
        ring
      simpa [add_assoc, add_left_comm, add_comm] using
        (HasDerivAt.const_add (secondOrderTaylorModelAt f x trialPoint) (hlin.add hquad))
    simpa [gradient_eq_deriv'] using hderiv.hasGradientAt'
  -- Differentiate the affine gradient formula at `0`.
  rw [hgradEq]
  simpa [A, B, T] using (HasDerivAt.const_add A ((hasDerivAt_id 0).const_mul B))

/-- Helper for Lemma 4.1.2: the cubic penalty slice contributes at least the textbook
`(M / 2) * r_M(x) * ‖v‖²` to the second derivative at the minimizer line parameter. -/
lemma cubic_penalty_slice_hessian_quadratic_lower_bound
    {f : E → ℝ} {M : ℝ} {x trialPoint : E}
    (hM : 0 ≤ M)
    (v : E) :
    ((M / 2) * r[trialPoint] x) * ‖v‖ ^ (2 : ℕ) ≤
      inner ℝ
        (hessian
          (fun t : ℝ ↦
            (M / 6 : ℝ) * ‖(trialPoint + t • v) - x‖ ^ (3 : ℕ)) 0 1) 1 := by
  let a : E := trialPoint - x
  let ψ : ℝ → ℝ := fun t : ℝ ↦ (M / 6 : ℝ) * ‖a + t • v‖ ^ (3 : ℕ)
  have hψ :
      (fun t : ℝ ↦ (M / 6 : ℝ) * ‖(trialPoint + t • v) - x‖ ^ (3 : ℕ)) = ψ := by
    -- Rewrite the displacement from `x` through the fixed residual vector `a`.
    funext t
    simp [ψ, a, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hgradEq :
      ∇ ψ = fun t ↦ (M / 2 : ℝ) * ‖a + t • v‖ * inner ℝ (a + t • v) v :=
    cubic_penalty_slice_gradient_eq (M := M) a v
  have hhessEval0 :
      hessian ψ (0 : ℝ) (1 : ℝ) =
        deriv (fun t : ℝ ↦ (M / 2 : ℝ) * ‖a + t • v‖ * inner ℝ (a + t • v) v) (0 : ℝ) := by
    -- Route correction: evaluate the scalar Hessian through the derivative of the explicit
    -- gradient formula instead of trying to differentiate the cubic norm directly twice.
    rw [hessian]
    calc
      fderiv ℝ (∇ ψ) (0 : ℝ) (1 : ℝ) = deriv (∇ ψ) (0 : ℝ) := by
        simpa using
          (fderiv_eq_deriv_mul
            (f := ∇ ψ)
            (x := (0 : ℝ))
            (y := (1 : ℝ)))
      _ =
          deriv
            (fun t : ℝ ↦ (M / 2 : ℝ) * ‖a + t • v‖ * inner ℝ (a + t • v) v)
            (0 : ℝ) := by
              rw [hgradEq]
  have hhessEval :
      inner ℝ (hessian ψ (0 : ℝ) (1 : ℝ)) (1 : ℝ) =
        deriv (fun t : ℝ ↦ (M / 2 : ℝ) * ‖a + t • v‖ * inner ℝ (a + t • v) v) (0 : ℝ) := by
    calc
      inner ℝ (hessian ψ (0 : ℝ) (1 : ℝ)) (1 : ℝ)
          = inner ℝ
              (deriv
                (fun t : ℝ ↦ (M / 2 : ℝ) * ‖a + t • v‖ * inner ℝ (a + t • v) v)
                (0 : ℝ))
              (1 : ℝ) := by
                exact congrArg (fun z : ℝ ↦ inner ℝ z (1 : ℝ)) hhessEval0
      _ =
          deriv
            (fun t : ℝ ↦ (M / 2 : ℝ) * ‖a + t • v‖ * inner ℝ (a + t • v) v)
            (0 : ℝ) := by
              change
                1 *
                    (deriv
                      (fun t : ℝ ↦ (M / 2 : ℝ) * ‖a + t • v‖ * inner ℝ (a + t • v) v)
                      (0 : ℝ)) =
                  deriv
                    (fun t : ℝ ↦ (M / 2 : ℝ) * ‖a + t • v‖ * inner ℝ (a + t • v) v)
                    (0 : ℝ)
              ring
  have hresidual :
      r[trialPoint] x = ‖a‖ := by
    -- The residual is the norm of `trialPoint - x`, up to the harmless sign change.
    rw [cubicRegularizationResidual_eq_norm_sub]
    simpa [a, sub_eq_add_neg] using norm_neg (trialPoint - x)
  by_cases ha : a = 0
  · have hderiv :
        deriv (fun t : ℝ ↦ (M / 2 : ℝ) * ‖a + t • v‖ * inner ℝ (a + t • v) v) (0 : ℝ) = 0 := by
      exact (cubic_penalty_slice_gradient_hasDerivAt_zero_of_zero_residual (M := M) ha).deriv
    -- In the zero-residual case both sides of the desired inequality vanish.
    rw [hψ, hhessEval, hderiv, hresidual, ha]
    simp
  · have hderiv :
        deriv (fun t : ℝ ↦ (M / 2 : ℝ) * ‖a + t • v‖ * inner ℝ (a + t • v) v) (0 : ℝ) =
          ((M / 2) * ‖a‖) * ‖v‖ ^ (2 : ℕ) +
            ((M / 2) / ‖a‖) * (inner ℝ a v) ^ (2 : ℕ) := by
      exact
        (cubic_penalty_slice_gradient_hasDerivAt_zero_of_nonzero_residual
          (M := M) (a := a) (v := v) ha).deriv
    have hsq_nonneg :
        0 ≤ ((M / 2) / ‖a‖) * (inner ℝ a v) ^ (2 : ℕ) := by
      have hcoeff_nonneg : 0 ≤ (M / 2) / ‖a‖ := by
        have hnorm_pos : 0 < ‖a‖ := norm_pos_iff.mpr ha
        positivity
      positivity
    -- The exact second derivative splits into the textbook lower-bound term and an extra square.
    rw [hψ, hhessEval, hderiv, hresidual]
    exact le_add_of_nonneg_right hsq_nonneg

/-- Helper for Lemma 4.1.2: the one-dimensional slice through a cubic-model minimizer has
nonnegative Hessian quadratic form at the minimizing parameter `0`. -/
lemma slice_hessian_quadratic_nonneg_at_local_min
    {f : E → ℝ} {M : ℝ} {x trialPoint : E}
    (hf : ContDiffAt ℝ 2 f x)
    (hmin :
      IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ trialPoint)
    (v : E) :
    0 ≤
      inner ℝ
        (hessian
          (fun t : ℝ ↦ cubicRegularizationQuadraticApproximation f M x (trialPoint + t • v))
          0 1) 1 := by
  let a : E := trialPoint - x
  let q : ℝ → ℝ := fun t : ℝ ↦ secondOrderTaylorModelAt f x (trialPoint + t • v)
  let p : ℝ → ℝ := fun t : ℝ ↦ (M / 6 : ℝ) * ‖a + t • v‖ ^ (3 : ℕ)
  let φ : ℝ → ℝ := fun t : ℝ ↦ cubicRegularizationQuadraticApproximation f M x (trialPoint + t • v)
  let T : E →L[ℝ] E := hessian f x
  let g : E := ∇ f x
  let A : ℝ := inner ℝ g v + inner ℝ (T a) v
  let B : ℝ := inner ℝ (T v) v
  have hlineMin : IsLocalMin φ 0 := by
    simpa [φ] using cubic_model_line_isLocalMin_at_zero hmin v
  have hselfAdjoint : IsSelfAdjoint T := by
    simpa using (fderiv_gradient_isSymmetric_of_contDiffAt hf).isSelfAdjoint
  have hcross :
      inner ℝ (T v) a = inner ℝ (T a) v := by
    calc
      inner ℝ (T v) a = inner ℝ v (T a) := hselfAdjoint.isSymmetric v a
      _ = inner ℝ (T a) v := by
          rw [real_inner_comm]
  have hqPoly :
      q =
        fun t : ℝ ↦
          secondOrderTaylorModelAt f x trialPoint +
            A * t +
            (B / 2 : ℝ) * t ^ (2 : ℕ) := by
    -- Expand the quadratic Taylor slice into an explicit scalar polynomial.
    funext t
    have hdisp : trialPoint + t • v - x = a + t • v := by
      simp [a, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    change
      secondOrderTaylorModelAt f x (trialPoint + t • v) =
        secondOrderTaylorModelAt f x trialPoint +
          A * t +
          (B / 2 : ℝ) * t ^ (2 : ℕ)
    rw [secondOrderTaylorModelAt_apply, secondOrderTaylorModelAt_apply, hdisp]
    simp [A, B, T, g, a, hcross, inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right, pow_two]
    ring
  have hqGradEq :
      ∇ q = fun t : ℝ ↦ A + B * t := by
    -- Differentiate the polynomial quadratic slice pointwise.
    refine gradient_eq ?_
    intro t
    rw [hqPoly]
    have hderiv :
        HasDerivAt
          (fun s : ℝ ↦
            secondOrderTaylorModelAt f x trialPoint +
              A * s +
              (B / 2 : ℝ) * s ^ (2 : ℕ))
          (A + B * t)
          t := by
      have hlin : HasDerivAt (fun s : ℝ ↦ A * s) A t := by
        simpa using (HasDerivAt.const_mul A (hasDerivAt_id t))
      have hquad :
          HasDerivAt (fun s : ℝ ↦ (B / 2 : ℝ) * s ^ (2 : ℕ)) (B * t) t := by
        have hquadBase :
            HasDerivAt
              (fun s : ℝ ↦ (B / 2 : ℝ) * s ^ (2 : ℕ))
              ((B / 2 : ℝ) * (2 * t))
              t := by
          simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using
            (HasDerivAt.const_mul (B / 2 : ℝ) ((hasDerivAt_id t).pow 2))
        convert hquadBase using 1
        ring
      simpa [add_assoc, add_left_comm, add_comm] using
        (HasDerivAt.const_add (secondOrderTaylorModelAt f x trialPoint) (hlin.add hquad))
    simpa [gradient_eq_deriv'] using hderiv.hasGradientAt'
  have hthree : 1 < (3 : ℝ) := by
    norm_num
  have hpDiffAll : ∀ t : ℝ, DifferentiableAt ℝ p t := by
    intro t
    have hlineDiff : DifferentiableAt ℝ (fun s : ℝ ↦ a + s • v) t := by
      simpa [one_smul] using
        (HasDerivAt.const_add a ((hasDerivAt_id t).smul_const v)).differentiableAt
    have hnormDiff : DifferentiableAt ℝ (fun z : E ↦ ‖z‖ ^ (3 : ℝ)) (a + t • v) :=
      (differentiable_norm_rpow (E := E) hthree) (a + t • v)
    simpa [p] using (hnormDiff.comp t hlineDiff).const_mul (M / 6 : ℝ)
  have hφEq : φ = q + p := by
    -- The full slice splits into the quadratic Taylor slice plus the cubic penalty slice.
    funext t
    simp [φ, q, p, cubicRegularizationQuadraticApproximation, a, sub_eq_add_neg, add_assoc,
      add_left_comm, add_comm]
  have hφDiff : DifferentiableAt ℝ φ 0 := by
    rw [hφEq]
    have hqDiff : DifferentiableAt ℝ q 0 := by
      rw [hqPoly]
      fun_prop
    exact hqDiff.add (hpDiffAll 0)
  have hpGradDiff :
      DifferentiableAt
        ℝ
        (fun t : ℝ ↦ (M / 2 : ℝ) * ‖a + t • v‖ * inner ℝ (a + t • v) v)
        0 := by
    by_cases ha : a = 0
    · exact
        (cubic_penalty_slice_gradient_hasDerivAt_zero_of_zero_residual
          (M := M) (a := a) (v := v) ha).differentiableAt
    · exact
        (cubic_penalty_slice_gradient_hasDerivAt_zero_of_nonzero_residual
          (M := M) (a := a) (v := v) ha).differentiableAt
  have hφGradEq :
      ∇ φ =
        fun t : ℝ ↦
          A + B * t + (M / 2 : ℝ) * ‖a + t • v‖ * inner ℝ (a + t • v) v := by
    -- Differentiate the quadratic and cubic pieces separately and add the scalar derivatives.
    refine gradient_eq ?_
    intro t
    have hqDiff : DifferentiableAt ℝ q t := by
      rw [hqPoly]
      fun_prop
    have hqDeriv : HasDerivAt q (A + B * t) t := by
      have hqDerivVal : deriv q t = A + B * t := by
        rw [← gradient_eq_deriv', hqGradEq]
      exact hqDerivVal ▸ hqDiff.hasDerivAt
    have hpDeriv :
        HasDerivAt p ((M / 2 : ℝ) * ‖a + t • v‖ * inner ℝ (a + t • v) v) t := by
      have hpDerivVal :
          deriv p t = (M / 2 : ℝ) * ‖a + t • v‖ * inner ℝ (a + t • v) v := by
        calc
          deriv p t = ∇ p t := by
            rw [gradient_eq_deriv']
          _ = (M / 2 : ℝ) * ‖a + t • v‖ * inner ℝ (a + t • v) v := by
              simpa [p] using congrFun (cubic_penalty_slice_gradient_eq (M := M) a v) t
      exact hpDerivVal ▸ (hpDiffAll t).hasDerivAt
    rw [hφEq]
    simpa [add_assoc, add_left_comm, add_comm] using (hqDeriv.add hpDeriv).hasGradientAt'
  have hφGradDiff : DifferentiableAt ℝ (∇ φ) 0 := by
    rw [hφGradEq]
    have hqGradDiff :
        DifferentiableAt ℝ (fun t : ℝ ↦ A + B * t) 0 := by
      simpa using (HasDerivAt.const_add A ((hasDerivAt_id (0 : ℝ)).const_mul B)).differentiableAt
    exact hqGradDiff.add hpGradDiff
  -- Apply the scalar second-order necessary condition to the restricted cubic model.
  have hnonneg :
      0 ≤ inner ℝ (hessian φ 0 1) 1 :=
    (isLocalMin_gradient_eq_zero_and_hessian_quadratic_nonneg hφDiff hφGradDiff hlineMin).2 1
  simpa [φ] using hnonneg

/-- Helper for Lemma 4.1.2: the quadratic Taylor slice through `trialPoint + t • v` has the
textbook first derivative at the base parameter `0`. -/
lemma quadratic_slice_gradient_at_zero
    {f : E → ℝ} {x trialPoint : E}
    (hf : ContDiffAt ℝ 2 f x)
    (v : E) :
    ∇ (fun t : ℝ ↦ secondOrderTaylorModelAt f x (trialPoint + t • v)) 0 =
      inner ℝ (∇ f x) v + inner ℝ (hessian f x (trialPoint - x)) v := by
  let a : E := trialPoint - x
  let T : E →L[ℝ] E := hessian f x
  let g : E := ∇ f x
  let A : ℝ := inner ℝ g v + inner ℝ (T a) v
  let B : ℝ := inner ℝ (T v) v
  have hselfAdjoint : IsSelfAdjoint T := by
    simpa using (fderiv_gradient_isSymmetric_of_contDiffAt hf).isSelfAdjoint
  have hcross :
      inner ℝ (T v) a = inner ℝ (T a) v := by
    calc
      inner ℝ (T v) a = inner ℝ v (T a) := hselfAdjoint.isSymmetric v a
      _ = inner ℝ (T a) v := by
          rw [real_inner_comm]
  have hpoly :
      (fun t : ℝ ↦ secondOrderTaylorModelAt f x (trialPoint + t • v)) =
        fun t : ℝ ↦
          secondOrderTaylorModelAt f x trialPoint +
            A * t +
            (B / 2 : ℝ) * t ^ (2 : ℕ) := by
    -- Expand the quadratic Taylor model along the affine line and collect the scalar terms.
    funext t
    have hdisp : trialPoint + t • v - x = a + t • v := by
      simp [a, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    rw [secondOrderTaylorModelAt_apply, secondOrderTaylorModelAt_apply, hdisp]
    simp [A, B, T, g, a, hcross, inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right, pow_two]
    ring
  have hgradEq :
      ∇ (fun t : ℝ ↦ secondOrderTaylorModelAt f x (trialPoint + t • v)) =
        fun t : ℝ ↦ A + B * t := by
    -- Differentiate the scalar polynomial description pointwise.
    refine gradient_eq ?_
    intro t
    rw [hpoly]
    have hderiv :
        HasDerivAt
          (fun s : ℝ ↦
            secondOrderTaylorModelAt f x trialPoint +
              A * s +
              (B / 2 : ℝ) * s ^ (2 : ℕ))
          (A + B * t)
          t := by
      have hlin : HasDerivAt (fun s : ℝ ↦ A * s) A t := by
        simpa using (HasDerivAt.const_mul A (hasDerivAt_id t))
      have hquad :
          HasDerivAt (fun s : ℝ ↦ (B / 2 : ℝ) * s ^ (2 : ℕ)) (B * t) t := by
        have hquadBase :
            HasDerivAt
              (fun s : ℝ ↦ (B / 2 : ℝ) * s ^ (2 : ℕ))
              ((B / 2 : ℝ) * (2 * t))
              t := by
          simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using
            (HasDerivAt.const_mul (B / 2 : ℝ) ((hasDerivAt_id t).pow 2))
        convert hquadBase using 1
        ring
      simpa [add_assoc, add_left_comm, add_comm] using
        (HasDerivAt.const_add (secondOrderTaylorModelAt f x trialPoint) (hlin.add hquad))
    simpa [gradient_eq_deriv'] using hderiv.hasGradientAt'
  -- Evaluate the affine gradient formula at the minimizing parameter.
  simpa [A, B, T, g, a] using congrFun hgradEq 0

/-- Helper for Lemma 4.1.2: every affine line through a cubic-model minimizer satisfies the
textbook first-order stationarity identity at the base parameter `0`. -/
lemma cubic_model_directional_stationarity_at_trial_point
    {f : E → ℝ} {M : ℝ} {x trialPoint : E}
    (hf : ContDiffAt ℝ 2 f x)
    (hmin :
      IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ trialPoint)
    (v : E) :
    inner ℝ (∇ f x) v +
      inner ℝ (hessian f x (trialPoint - x)) v +
      ((M / 2) * r[trialPoint] x) * inner ℝ (trialPoint - x) v = 0 := by
  let a : E := trialPoint - x
  let q : ℝ → ℝ := fun t : ℝ ↦ secondOrderTaylorModelAt f x (trialPoint + t • v)
  let p : ℝ → ℝ := fun t : ℝ ↦ (M / 6 : ℝ) * ‖a + t • v‖ ^ (3 : ℕ)
  let φ : ℝ → ℝ := fun t : ℝ ↦ cubicRegularizationQuadraticApproximation f M x (trialPoint + t • v)
  have hlineMin : IsLocalMin φ 0 := by
    simpa [φ] using cubic_model_line_isLocalMin_at_zero hmin v
  have hqDeriv :
      HasDerivAt q (inner ℝ (∇ f x) v + inner ℝ (hessian f x a) v) 0 := by
    let T : E →L[ℝ] E := hessian f x
    let g : E := ∇ f x
    have hselfAdjoint : IsSelfAdjoint T := by
      simpa using (fderiv_gradient_isSymmetric_of_contDiffAt hf).isSelfAdjoint
    have hcross :
        inner ℝ (T v) a = inner ℝ (T a) v := by
      calc
        inner ℝ (T v) a = inner ℝ v (T a) := hselfAdjoint.isSymmetric v a
        _ = inner ℝ (T a) v := by
            rw [real_inner_comm]
    have hdisp :
        q =
          fun t : ℝ ↦
            f x +
              inner ℝ g (a + t • v) +
              (1 / 2 : ℝ) * inner ℝ (T (a + t • v)) (a + t • v) := by
      -- Rewrite the slice entirely in terms of the residual vector `a`.
      funext t
      have hshift : trialPoint + t • v - x = a + t • v := by
        simp [a, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      simp [q, secondOrderTaylorModelAt_apply, g, T, a, hshift, map_add, map_sub,
        sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    have hline : HasDerivAt (fun t : ℝ ↦ a + t • v) v 0 := by
      simpa [one_smul] using
        (HasDerivAt.const_add a ((hasDerivAt_id (0 : ℝ)).smul_const v))
    have hlin :
        HasDerivAt (fun t : ℝ ↦ inner ℝ g (a + t • v)) (inner ℝ g v) 0 := by
      simpa using
        (HasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) ((innerSL ℝ g).hasFDerivAt) hline)
    have hquad :
        HasDerivAt
          (fun t : ℝ ↦ (1 / 2 : ℝ) * inner ℝ (T (a + t • v)) (a + t • v))
          (inner ℝ (T a) v)
          0 := by
      have hTa :
          HasDerivAt (fun t : ℝ ↦ T (a + t • v)) (T v) 0 := by
        convert T.hasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) hline using 1
      have hquadBase :
          HasDerivAt
            (fun t : ℝ ↦ inner ℝ (T (a + t • v)) (a + t • v))
            (inner ℝ (T v) a + inner ℝ (T a) v)
            0 := by
        simpa [add_comm] using (HasDerivAt.inner ℝ hTa hline)
      have hquadScaled :
          HasDerivAt
            (fun t : ℝ ↦ (1 / 2 : ℝ) * inner ℝ (T (a + t • v)) (a + t • v))
            ((1 / 2 : ℝ) * (inner ℝ (T v) a + inner ℝ (T a) v))
            0 := by
        simpa [mul_comm] using (HasDerivAt.const_mul (1 / 2 : ℝ) hquadBase)
      convert hquadScaled using 1
      rw [hcross]
      ring
    rw [hdisp]
    simpa [g, T, a, add_assoc, add_left_comm, add_comm] using
      (HasDerivAt.const_add (f x) (hlin.add hquad))
  have hpDeriv :
      HasDerivAt p (((M / 2 : ℝ) * ‖a‖) * inner ℝ a v) 0 := by
    -- Differentiate the cubic penalty slice directly through the norm-power chain rule at `t = 0`.
    have hthree : 1 < (3 : ℝ) := by
      norm_num
    have hline : HasDerivAt (fun t : ℝ ↦ a + t • v) v 0 := by
      simpa [one_smul] using
        (HasDerivAt.const_add a ((hasDerivAt_id (0 : ℝ)).smul_const v))
    have hnorm :
        HasFDerivAt
          (fun z : E ↦ ‖z‖ ^ (3 : ℝ))
          ((3 * ‖a + (0 : ℝ) • v‖ ^ ((3 : ℝ) - 2)) • innerSL ℝ (a + (0 : ℝ) • v))
          (a + (0 : ℝ) • v) := by
      simpa using (hasFDerivAt_norm_rpow (a + (0 : ℝ) • v) hthree)
    have hraw :
        HasDerivAt
          (fun t : ℝ ↦ ‖a + t • v‖ ^ (3 : ℝ))
          (((3 : ℝ) * ‖a‖ ^ ((3 : ℝ) - 2)) * inner ℝ a v)
          0 := by
      simpa [Function.comp, innerSL_apply_apply] using
        HasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) hnorm hline
    have hscaled :
        HasDerivAt
          (fun t : ℝ ↦ (M / 6 : ℝ) * ‖a + t • v‖ ^ (3 : ℝ))
          ((M / 6 : ℝ) * (((3 : ℝ) * ‖a‖ ^ ((3 : ℝ) - 2)) * inner ℝ a v))
          0 := by
      have hscaledBase :
          HasDerivAt
            (fun t : ℝ ↦ (M / 6 : ℝ) * ‖a + t • v‖ ^ (3 : ℝ))
            ((M / 6 : ℝ) *
              (((3 : ℝ) * ‖a + (0 : ℝ) • v‖ ^ ((3 : ℝ) - 2)) * inner ℝ (a + (0 : ℝ) • v) v))
            0 := by
        simpa [mul_comm] using (HasDerivAt.const_mul (M / 6 : ℝ) hraw)
      simpa using hscaledBase
    convert hscaled using 1
    · ext t
      rw [show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast]
    · have hexp : ((3 : ℝ) - 2) = 1 := by
        norm_num
      simp [hexp, Real.rpow_one]
      ring
  have hφEq : φ = q + p := by
    -- Split the restricted cubic model into its quadratic Taylor slice and cubic penalty slice.
    funext t
    simp [φ, q, p, cubicRegularizationQuadraticApproximation, a, sub_eq_add_neg, add_assoc,
      add_left_comm, add_comm]
  have hφDeriv :
      HasDerivAt
        φ
        (inner ℝ (∇ f x) v + inner ℝ (hessian f x a) v +
          ((M / 2 : ℝ) * ‖a‖) * inner ℝ a v)
        0 := by
    -- Add the quadratic and cubic slice derivatives at the minimizing parameter.
    rw [hφEq]
    simpa [a, add_assoc, add_left_comm, add_comm] using hqDeriv.add hpDeriv
  have hstationary :
      inner ℝ (∇ f x) v + inner ℝ (hessian f x a) v +
        ((M / 2 : ℝ) * ‖a‖) * inner ℝ a v = 0 :=
    hlineMin.hasDerivAt_eq_zero hφDeriv
  have hresidual :
      r[trialPoint] x = ‖a‖ := by
    rw [cubicRegularizationResidual_eq_norm_sub]
    simpa [a] using norm_sub_rev x trialPoint
  simpa [a, hresidual, norm_sub_rev] using hstationary

/-- Helper for Lemma 4.1.2: the cubic norm satisfies the affine-quadratic lower bound used in
the source proof. -/
lemma norm_add_pow_three_ge_affine_quadratic
    (a v : E) :
    ‖a + v‖ ^ (3 : ℕ) ≥
      ‖a‖ ^ (3 : ℕ) + (3 : ℝ) * ‖a‖ * inner ℝ a v + (3 / 2 : ℝ) * ‖a‖ * ‖v‖ ^ (2 : ℕ) := by
  have hsq :
      ‖a + v‖ ^ (2 : ℕ) = ‖a‖ ^ (2 : ℕ) + 2 * inner ℝ a v + ‖v‖ ^ (2 : ℕ) := by
    -- Expand the squared norm of `a + v` through the real inner-product polarization identity.
    calc
      ‖a + v‖ ^ (2 : ℕ) = inner ℝ (a + v) (a + v) := by
        rw [real_inner_self_eq_norm_sq]
      _ = inner ℝ a a + inner ℝ a v + (inner ℝ v a + inner ℝ v v) := by
        rw [inner_add_left, inner_add_right, inner_add_right]
      _ = ‖a‖ ^ (2 : ℕ) + 2 * inner ℝ a v + ‖v‖ ^ (2 : ℕ) := by
        rw [real_inner_comm v a, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
        ring
  have hfactor :
      0 ≤ (‖a + v‖ - ‖a‖) ^ (2 : ℕ) * (2 * ‖a + v‖ + ‖a‖) := by
    -- The scalar identity `(b - r)^2 (2b + r) ≥ 0` controls the cubic remainder globally.
    positivity
  nlinarith [hsq, hfactor, norm_nonneg (a + v), norm_nonneg a]

/-- Helper for Lemma 4.1.2: if `M ≥ 0`, a global minimizer of the cubic model also minimizes the
quadratic Taylor model on the closed ball with the same residual radius. -/
lemma quadratic_model_isMinOn_closedBall_of_cubic_model_global_min
    {f : E → ℝ} {M : ℝ}
    (hM : 0 ≤ M)
    {x trialPoint : E}
    (hmin :
      IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ trialPoint) :
    IsMinOn (secondOrderTaylorModelAt f x) (Metric.closedBall x (r[trialPoint] x)) trialPoint := by
  rw [isMinOn_iff] at hmin ⊢
  intro y hy
  -- Compare the cubic model values, then use monotonicity of the cubic penalty on the closed
  -- ball to strip off the common regularization term.
  have hmodel :
      cubicRegularizationQuadraticApproximation f M x trialPoint ≤
        cubicRegularizationQuadraticApproximation f M x y :=
    hmin y (by simp)
  rw [cubicRegularizationQuadraticApproximation_apply,
    cubicRegularizationQuadraticApproximation_apply] at hmodel
  have hy_norm : ‖y - x‖ ≤ r[trialPoint] x := by
    simpa [Metric.mem_closedBall, dist_eq_norm, dist_comm] using hy
  have hr_eq : r[trialPoint] x = ‖trialPoint - x‖ := by
    rw [cubicRegularizationResidual_eq_norm_sub]
    simpa using norm_sub_rev x trialPoint
  have hy_norm' : ‖y - x‖ ≤ ‖trialPoint - x‖ := by
    calc
      ‖y - x‖ ≤ ‖x - trialPoint‖ := by
        simpa [cubicRegularizationResidual_eq_norm_sub] using hy_norm
      _ = ‖trialPoint - x‖ := by
        simpa using norm_sub_rev x trialPoint
  have hpenalty :
      (M / 6 : ℝ) * ‖y - x‖ ^ (3 : ℕ) ≤ (M / 6 : ℝ) * ‖trialPoint - x‖ ^ (3 : ℕ) := by
    have hM6 : 0 ≤ (M / 6 : ℝ) := by
      positivity
    have hy_cubed : ‖y - x‖ ^ (3 : ℕ) ≤ ‖trialPoint - x‖ ^ (3 : ℕ) := by
      have hy_sq : ‖y - x‖ ^ (2 : ℕ) ≤ ‖trialPoint - x‖ ^ (2 : ℕ) := by
        nlinarith [hy_norm', norm_nonneg (y - x), norm_nonneg (trialPoint - x)]
      calc
        ‖y - x‖ ^ (3 : ℕ) = ‖y - x‖ * ‖y - x‖ ^ (2 : ℕ) := by
          ring
        _ ≤ ‖trialPoint - x‖ * ‖trialPoint - x‖ ^ (2 : ℕ) := by
          exact mul_le_mul hy_norm' hy_sq (sq_nonneg ‖y - x‖) (norm_nonneg _)
        _ = ‖trialPoint - x‖ ^ (3 : ℕ) := by
          ring
    exact mul_le_mul_of_nonneg_left hy_cubed hM6
  have hpenalty_diff :
      0 ≤ (M / 6 : ℝ) * ‖trialPoint - x‖ ^ (3 : ℕ) - (M / 6 : ℝ) * ‖y - x‖ ^ (3 : ℕ) := by
    linarith
  linarith

/-- Helper for Lemma 4.1.2: after eliminating the first-order term by directional stationarity,
the quadratic Taylor gap admits an exact shifted-Hessian identity. -/
lemma regularized_hessian_quadratic_gap_on_closedBall
    {f : E → ℝ} {M : ℝ} {x trialPoint y : E}
    (hf : ContDiffAt ℝ 2 f x)
    (hmin :
      IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ trialPoint) :
    secondOrderTaylorModelAt f x y - secondOrderTaylorModelAt f x trialPoint =
      (1 / 2 : ℝ) *
          inner ℝ
            (((hessian f x + ((M / 2) * r[trialPoint] x) • (1 : E →L[ℝ] E))
                (y - trialPoint)))
            (y - trialPoint) +
        ((((M / 2) * r[trialPoint] x) / 2 : ℝ) *
          (((r[trialPoint] x) ^ (2 : ℕ)) - ‖y - x‖ ^ (2 : ℕ))) := by
  let d : E := trialPoint - x
  let u : E := y - trialPoint
  let Q : E →L[ℝ] E := hessian f x
  let c : ℝ := (M / 2) * r[trialPoint] x
  let A : E →L[ℝ] E := Q + c • (1 : E →L[ℝ] E)
  have hselfAdjoint : IsSelfAdjoint Q := by
    simpa [Q] using (fderiv_gradient_isSymmetric_of_contDiffAt hf).isSelfAdjoint
  have hcross :
      inner ℝ (Q u) d = inner ℝ (Q d) u := by
    calc
      inner ℝ (Q u) d = inner ℝ u (Q d) := hselfAdjoint.isSymmetric u d
      _ = inner ℝ (Q d) u := by
          rw [real_inner_comm]
  have hstationary :
      inner ℝ (∇ f x) u + inner ℝ (Q d) u + c * inner ℝ d u = 0 := by
    simpa [Q, d, u, c, mul_assoc, mul_left_comm, mul_comm] using
      cubic_model_directional_stationarity_at_trial_point hf hmin u
  have hdisp : y - x = d + u := by
    simp [d, u, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hr_eq : r[trialPoint] x = ‖d‖ := by
    rw [cubicRegularizationResidual_eq_norm_sub]
    simpa [d] using norm_sub_rev x trialPoint
  have hrsq_eq : (r[trialPoint] x) ^ (2 : ℕ) = ‖d‖ ^ (2 : ℕ) := by
    rw [hr_eq]
  have hnormsq :
      ‖y - x‖ ^ (2 : ℕ) = ‖d‖ ^ (2 : ℕ) + 2 * inner ℝ d u + ‖u‖ ^ (2 : ℕ) := by
    calc
      ‖y - x‖ ^ (2 : ℕ) = inner ℝ (d + u) (d + u) := by
        rw [hdisp, real_inner_self_eq_norm_sq]
      _ = inner ℝ d d + 2 * inner ℝ d u + inner ℝ u u := by
        rw [inner_add_left, inner_add_right, inner_add_right, real_inner_comm u d]
        ring
      _ = ‖d‖ ^ (2 : ℕ) + 2 * inner ℝ d u + ‖u‖ ^ (2 : ℕ) := by
        rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  have hquad_expand :
      inner ℝ (Q (d + u)) (d + u) =
        inner ℝ (Q d) d + 2 * inner ℝ (Q d) u + inner ℝ (Q u) u := by
    rw [map_add, inner_add_left, inner_add_right, inner_add_right, hcross]
    ring
  calc
    secondOrderTaylorModelAt f x y - secondOrderTaylorModelAt f x trialPoint
      = inner ℝ (∇ f x) u + inner ℝ (Q d) u + (1 / 2 : ℝ) * inner ℝ (Q u) u := by
          -- Expand the Taylor gap around the minimizer displacement `d` and collect the mixed
          -- quadratic terms using Hessian symmetry.
          rw [secondOrderTaylorModelAt_apply, secondOrderTaylorModelAt_apply, hdisp, hquad_expand]
          rw [inner_add_right]
          simp [Q, d, u, add_assoc, add_left_comm, add_comm]
          ring
    _ = (1 / 2 : ℝ) * inner ℝ (Q u) u - c * inner ℝ d u := by
          nlinarith [hstationary]
    _ = (1 / 2 : ℝ) * inner ℝ (A u) u +
          ((c / 2 : ℝ) * ((r[trialPoint] x) ^ (2 : ℕ) - ‖y - x‖ ^ (2 : ℕ))) := by
          -- Reinsert the shifted identity part and trade the remaining mixed term for the
          -- radius defect on the closed ball.
          rw [hnormsq, hrsq_eq]
          simp [A, c, real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
            inner_smul_left, inner_smul_right]
          ring
    _ = (1 / 2 : ℝ) *
          inner ℝ
            (((hessian f x + ((M / 2) * r[trialPoint] x) • (1 : E →L[ℝ] E))
                (y - trialPoint)))
            (y - trialPoint) +
        ((((M / 2) * r[trialPoint] x) / 2 : ℝ) *
          (((r[trialPoint] x) ^ (2 : ℕ)) - ‖y - x‖ ^ (2 : ℕ))) := by
          simp [A, Q, c, u]

/-- Helper for Lemma 4.1.2: the shifted Hessian quadratic form is nonnegative on the residual
displacement `trialPoint - x`. -/
lemma regularized_hessian_displacement_quadratic_nonneg
    {f : E → ℝ} {M : ℝ}
    (hM : 0 ≤ M)
    {x trialPoint : E}
    (hf : ContDiffAt ℝ 2 f x)
    (hmin :
      IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ trialPoint) :
    0 ≤
      inner ℝ
        (((hessian f x + ((M / 2) * r[trialPoint] x) • (1 : E →L[ℝ] E))
            (trialPoint - x)))
        (trialPoint - x) := by
  let y : E := (2 : ℝ) • x - trialPoint
  have hy_ball : y ∈ Metric.closedBall x (r[trialPoint] x) := by
    -- Reflecting `trialPoint` through `x` preserves the residual radius exactly.
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hy_shift : y - x = -(trialPoint - x) := by
      simp [y, two_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    rw [hy_shift, norm_neg, cubicRegularizationResidual_eq_norm_sub]
    simpa using le_of_eq (norm_sub_rev x trialPoint).symm
  have hquadMin :
      secondOrderTaylorModelAt f x trialPoint ≤ secondOrderTaylorModelAt f x y :=
    (quadratic_model_isMinOn_closedBall_of_cubic_model_global_min hM hmin) hy_ball
  have hnonneg_gap :
      0 ≤ secondOrderTaylorModelAt f x y - secondOrderTaylorModelAt f x trialPoint := by
    exact sub_nonneg.mpr hquadMin
  have hy_radius : ‖y - x‖ = r[trialPoint] x := by
    have hy_shift : y - x = -(trialPoint - x) := by
      simp [y, two_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    rw [hy_shift, norm_neg, cubicRegularizationResidual_eq_norm_sub]
    simpa using (norm_sub_rev x trialPoint).symm
  have hy_radius_sq : ‖y - x‖ ^ (2 : ℕ) = (r[trialPoint] x) ^ (2 : ℕ) := by
    rw [hy_radius]
  have hy_trial :
      y - trialPoint = (- (2 : ℝ)) • (trialPoint - x) := by
    simp [y, two_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hgap_eval :
      secondOrderTaylorModelAt f x y - secondOrderTaylorModelAt f x trialPoint =
        2 *
          inner ℝ
            (((hessian f x + ((M / 2) * r[trialPoint] x) • (1 : E →L[ℝ] E))
                (trialPoint - x)))
            (trialPoint - x) := by
    let B : E →L[ℝ] E := hessian f x + ((M / 2) * r[trialPoint] x) • (1 : E →L[ℝ] E)
    -- On the reflected sphere point, the radius defect vanishes and only the radial quadratic
    -- coefficient remains.
    rw [regularized_hessian_quadratic_gap_on_closedBall hf hmin, hy_radius_sq, hy_trial]
    have hzero :
        ((((M / 2) * r[trialPoint] x) / 2 : ℝ) *
          (((r[trialPoint] x) ^ (2 : ℕ)) - (r[trialPoint] x) ^ (2 : ℕ))) = 0 := by
      ring
    have hmap :
        B ((- (2 : ℝ)) • (trialPoint - x)) = (- (2 : ℝ)) • (B (trialPoint - x)) := by
      simp [B, smul_smul, mul_assoc, mul_left_comm, mul_comm]
    have hscaled :
      (1 / 2 : ℝ) *
          inner ℝ
            (((hessian f x + ((M / 2) * r[trialPoint] x) • (1 : E →L[ℝ] E))
                ((- (2 : ℝ)) • (trialPoint - x))))
            ((- (2 : ℝ)) • (trialPoint - x))
        = 2 *
            inner ℝ
              (B (trialPoint - x))
              (trialPoint - x) := by
        rw [hmap]
        simp [inner_smul_left, inner_smul_right]
    calc
      (1 / 2 : ℝ) *
          inner ℝ
            (((hessian f x + ((M / 2) * r[trialPoint] x) • (1 : E →L[ℝ] E))
                ((- (2 : ℝ)) • (trialPoint - x))))
            ((- (2 : ℝ)) • (trialPoint - x))
          +
            ((((M / 2) * r[trialPoint] x) / 2 : ℝ) *
              (((r[trialPoint] x) ^ (2 : ℕ)) - (r[trialPoint] x) ^ (2 : ℕ)))
        = (1 / 2 : ℝ) *
            inner ℝ
              (((hessian f x + ((M / 2) * r[trialPoint] x) • (1 : E →L[ℝ] E))
                  ((- (2 : ℝ)) • (trialPoint - x))))
              ((- (2 : ℝ)) • (trialPoint - x)) := by
              rw [hzero]
              ring
      _ = 2 *
            inner ℝ
              (B (trialPoint - x))
              (trialPoint - x) := hscaled
      _ = 2 *
            inner ℝ
              (((hessian f x + ((M / 2) * r[trialPoint] x) • (1 : E →L[ℝ] E))
                  (trialPoint - x)))
              (trialPoint - x) := by
              simp [B]
  nlinarith [hnonneg_gap, hgap_eval]

/-- Helper for Lemma 4.1.2: when the residual vanishes, the cubic slice contributes no second
order term, so the ambient Hessian quadratic form is already nonnegative. -/
lemma regularized_hessian_quadratic_nonneg_of_zero_residual
    {f : E → ℝ} {M : ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x)
    (hmin :
      IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ x)
    (v : E) :
    0 ≤ inner ℝ ((hessian f x) v) v := by
  let q : ℝ → ℝ := fun t : ℝ ↦ secondOrderTaylorModelAt f x (x + t • v)
  let p : ℝ → ℝ := fun t : ℝ ↦ (M / 6 : ℝ) * ‖(0 : E) + t • v‖ ^ (3 : ℕ)
  let φ : ℝ → ℝ := fun t : ℝ ↦ cubicRegularizationQuadraticApproximation f M x (x + t • v)
  let A : ℝ := inner ℝ (∇ f x) v
  let B : ℝ := inner ℝ (hessian f x v) v
  let C : ℝ := ((M / 2 : ℝ) * ‖v‖ ^ (3 : ℕ))
  have hslice_nonneg :
      0 ≤ inner ℝ (hessian φ 0 1) 1 := by
    -- The restricted cubic model has nonnegative scalar Hessian at its minimizing parameter.
    simpa [φ] using slice_hessian_quadratic_nonneg_at_local_min hf hmin v
  have hqPoly :
      q =
        fun t : ℝ ↦
          secondOrderTaylorModelAt f x x + A * t + (B / 2 : ℝ) * t ^ (2 : ℕ) := by
    -- Along the zero-residual line, the quadratic model becomes a scalar quadratic polynomial.
    funext t
    have hdisp : x + t • v - x = t • v := by
      simp
    dsimp [q]
    simp [secondOrderTaylorModelAt_apply, hdisp, A, B, inner_smul_left, inner_smul_right,
      pow_two]
    ring
  have hqGradEq : ∇ q = fun t : ℝ ↦ A + B * t := by
    -- Differentiate the explicit scalar quadratic polynomial pointwise.
    refine gradient_eq ?_
    intro t
    rw [hqPoly]
    have hderiv :
        HasDerivAt
          (fun s : ℝ ↦
            secondOrderTaylorModelAt f x x + A * s + (B / 2 : ℝ) * s ^ (2 : ℕ))
          (A + B * t)
          t := by
      have hlin : HasDerivAt (fun s : ℝ ↦ A * s) A t := by
        simpa using (HasDerivAt.const_mul A (hasDerivAt_id t))
      have hquad :
          HasDerivAt (fun s : ℝ ↦ (B / 2 : ℝ) * s ^ (2 : ℕ)) (B * t) t := by
        have hquadBase :
            HasDerivAt
              (fun s : ℝ ↦ (B / 2 : ℝ) * s ^ (2 : ℕ))
              ((B / 2 : ℝ) * (2 * t))
              t := by
          simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using
            (HasDerivAt.const_mul (B / 2 : ℝ) ((hasDerivAt_id t).pow 2))
        convert hquadBase using 1
        ring
      simpa [add_assoc, add_left_comm, add_comm] using
        (HasDerivAt.const_add (secondOrderTaylorModelAt f x x) (hlin.add hquad))
    simpa [gradient_eq_deriv'] using hderiv.hasGradientAt'
  have hqDiff : ∀ t : ℝ, DifferentiableAt ℝ q t := by
    -- The polynomial slice is differentiable at every scalar parameter.
    intro t
    rw [hqPoly]
    fun_prop
  have hpDiff : ∀ t : ℝ, DifferentiableAt ℝ p t := by
    -- The cubic penalty slice is differentiable everywhere because `‖·‖^3` is `C¹`.
    intro t
    have hthree : 1 < (3 : ℝ) := by
      norm_num
    have hlineDiff : DifferentiableAt ℝ (fun s : ℝ ↦ (0 : E) + s • v) t := by
      simpa [one_smul] using
        (HasDerivAt.const_add (0 : E) ((hasDerivAt_id t).smul_const v)).differentiableAt
    have hnormDiff : DifferentiableAt ℝ (fun z : E ↦ ‖z‖ ^ (3 : ℝ)) ((0 : E) + t • v) :=
      (differentiable_norm_rpow (E := E) hthree) ((0 : E) + t • v)
    have hpDiffRpow :
        DifferentiableAt ℝ (fun s : ℝ ↦ (M / 6 : ℝ) * ‖(0 : E) + s • v‖ ^ (3 : ℝ)) t := by
      exact (hnormDiff.comp t hlineDiff).const_mul (M / 6 : ℝ)
    convert hpDiffRpow using 1
    ext s
    rw [show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast]
  have hpGradEq : ∇ p = fun t : ℝ ↦ C * (t * |t|) := by
    -- The zero-residual cubic slice gradient collapses to a scalar multiple of `t * |t|`.
    funext t
    calc
      ∇ p t
          = (M / 2 : ℝ) * ‖(0 : E) + t • v‖ * inner ℝ ((0 : E) + t • v) v := by
              simpa [p] using
                congrFun (cubic_penalty_slice_gradient_eq (M := M) (a := (0 : E)) v) t
      _ = C * (t * |t|) := by
          simp [C, norm_smul, Real.norm_eq_abs, inner_smul_left, real_inner_self_eq_norm_sq]
          ring
  have hφEq : φ = q + p := by
    -- Split the restricted cubic model into its quadratic Taylor slice and cubic penalty slice.
    funext t
    simp [φ, q, p, cubicRegularizationQuadraticApproximation, sub_eq_add_neg, add_assoc,
      add_left_comm, add_comm]
  have hφGradEq :
      ∇ φ = fun t : ℝ ↦ (A + B * t) + C * (t * |t|) := by
    -- Recombine the already identified gradients of the quadratic and cubic slices.
    refine gradient_eq ?_
    intro t
    have hqDerivBase : HasDerivAt q (deriv q t) t := (hqDiff t).hasDerivAt
    have hqDeriv : HasDerivAt q (A + B * t) t := by
      convert hqDerivBase using 1
      rw [← gradient_eq_deriv', hqGradEq]
    have hpDerivBase : HasDerivAt p (deriv p t) t := (hpDiff t).hasDerivAt
    have hpDeriv : HasDerivAt p (C * (t * |t|)) t := by
      convert hpDerivBase using 1
      rw [← gradient_eq_deriv', hpGradEq]
    rw [hφEq]
    simpa [add_assoc, add_left_comm, add_comm] using (hqDeriv.add hpDeriv).hasGradientAt'
  have hφGradDeriv :
      HasDerivAt (fun t : ℝ ↦ ∇ φ t) B 0 := by
    -- The quadratic slice contributes `B`, while the zero-residual cubic slice contributes `0`.
    rw [hφGradEq]
    have hlin :
        HasDerivAt (fun t : ℝ ↦ A + B * t) B 0 := by
      simpa using (HasDerivAt.const_add A ((hasDerivAt_id 0).const_mul B))
    have hcub :
        HasDerivAt (fun t : ℝ ↦ C * (t * |t|)) 0 0 := by
      simpa [C] using (HasDerivAt.const_mul C t_mul_abs_hasDerivAt_zero)
    simpa using hlin.add hcub
  have hhessEval0 : hessian φ (0 : ℝ) (1 : ℝ) = B := by
    -- Evaluate the scalar Hessian through the derivative of the gradient function.
    rw [hessian]
    calc
      fderiv ℝ (∇ φ) (0 : ℝ) (1 : ℝ) = deriv (∇ φ) (0 : ℝ) := by
        simpa using
          (fderiv_eq_deriv_mul
            (f := ∇ φ)
            (x := (0 : ℝ))
            (y := (1 : ℝ)))
      _ = B := by
          simpa using hφGradDeriv.deriv
  have hhessEval :
      inner ℝ (hessian φ (0 : ℝ) (1 : ℝ)) (1 : ℝ) = B := by
    calc
      inner ℝ (hessian φ (0 : ℝ) (1 : ℝ)) (1 : ℝ) = inner ℝ B (1 : ℝ) := by
        exact congrArg (fun z : ℝ ↦ inner ℝ z (1 : ℝ)) hhessEval0
      _ = B := by
        change 1 * B = B
        ring
  rw [hhessEval] at hslice_nonneg
  simpa [B] using hslice_nonneg

/-- Helper for Lemma 4.1.2: the stereographic path in the plane spanned by the residual and an
orthogonal unit vector stays on the sphere of residual radius. -/
lemma sphere_path_has_fixed_residual_radius
    {x trialPoint e : E}
    (he_unit : ‖e‖ = 1)
    (he_orth : inner ℝ (trialPoint - x) e = 0) :
    let r := r[trialPoint] x
    let gamma :=
      fun t : ℝ ↦
        x + ((1 - t ^ (2 : ℕ)) / (1 + t ^ (2 : ℕ))) • (trialPoint - x) +
          ((2 * r * t) / (1 + t ^ (2 : ℕ))) • e
    ∀ t, ‖gamma t - x‖ = r := by
  dsimp
  let d : E := trialPoint - x
  have hr : r[trialPoint] x = ‖d‖ := by
    rw [cubicRegularizationResidual_eq_norm_sub]
    simpa [d] using norm_sub_rev x trialPoint
  intro t
  have hden_pos : 0 < 1 + t ^ (2 : ℕ) := by
    positivity
  have hden_ne : (1 + t ^ (2 : ℕ)) ≠ 0 := ne_of_gt hden_pos
  let a : ℝ := (1 - t ^ (2 : ℕ)) / (1 + t ^ (2 : ℕ))
  let b : ℝ := (2 * r[trialPoint] x * t) / (1 + t ^ (2 : ℕ))
  have hsq :
      ‖a • d + b • e‖ ^ (2 : ℕ) = (r[trialPoint] x) ^ (2 : ℕ) := by
    -- Expand the squared norm, kill the mixed term by orthogonality, and simplify the scalar
    -- rational identity on `t`.
    have hd_orth : inner ℝ d e = 0 := by
      simpa [d] using he_orth
    have hed_orth : inner ℝ e d = 0 := by
      rw [real_inner_comm]
      exact hd_orth
    have he_self : inner ℝ e e = 1 := by
      rw [real_inner_self_eq_norm_sq, he_unit]
      norm_num
    have hd_self : inner ℝ d d = (r[trialPoint] x) ^ (2 : ℕ) := by
      rw [real_inner_self_eq_norm_sq, hr]
    calc
      ‖a • d + b • e‖ ^ (2 : ℕ) = inner ℝ (a • d + b • e) (a • d + b • e) := by
        rw [real_inner_self_eq_norm_sq]
      _ = inner ℝ (a • d) (a • d) + inner ℝ (a • d) (b • e) +
            inner ℝ (b • e) (a • d) + inner ℝ (b • e) (b • e) := by
            rw [inner_add_left, inner_add_right, inner_add_right]
            ring
      _ = ‖a • d‖ ^ (2 : ℕ) + b * (a * inner ℝ d e) +
            a * (b * inner ℝ e d) + ‖b • e‖ ^ (2 : ℕ) := by
            simp [inner_smul_left, inner_smul_right]
      _ = a ^ (2 : ℕ) * ‖d‖ ^ (2 : ℕ) + (a * b) * inner ℝ d e +
            (b * a) * inner ℝ e d + b ^ (2 : ℕ) * ‖e‖ ^ (2 : ℕ) := by
            rw [norm_smul, norm_smul]
            rw [Real.norm_eq_abs, Real.norm_eq_abs]
            have ha_sq : (|a| * ‖d‖) ^ (2 : ℕ) = a ^ (2 : ℕ) * ‖d‖ ^ (2 : ℕ) := by
              calc
                (|a| * ‖d‖) ^ (2 : ℕ) = |a| ^ (2 : ℕ) * ‖d‖ ^ (2 : ℕ) := by ring
                _ = a ^ (2 : ℕ) * ‖d‖ ^ (2 : ℕ) := by rw [sq_abs]
            have hb_sq : (|b| * ‖e‖) ^ (2 : ℕ) = b ^ (2 : ℕ) * ‖e‖ ^ (2 : ℕ) := by
              calc
                (|b| * ‖e‖) ^ (2 : ℕ) = |b| ^ (2 : ℕ) * ‖e‖ ^ (2 : ℕ) := by ring
                _ = b ^ (2 : ℕ) * ‖e‖ ^ (2 : ℕ) := by rw [sq_abs]
            rw [ha_sq, hb_sq]
            ring
      _ = a ^ (2 : ℕ) * inner ℝ d d + (a * b) * inner ℝ d e +
            (b * a) * inner ℝ e d + b ^ (2 : ℕ) * inner ℝ e e := by
            rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
      _ = a ^ (2 : ℕ) * (r[trialPoint] x) ^ (2 : ℕ) + b ^ (2 : ℕ) := by
            rw [hd_orth, hed_orth, hd_self, he_self]
            ring
      _ = (r[trialPoint] x) ^ (2 : ℕ) := by
            dsimp [a, b]
            field_simp [hden_ne]
            ring
  have hnonneg_left : 0 ≤ ‖a • d + b • e‖ := norm_nonneg _
  have hnonneg_right : 0 ≤ r[trialPoint] x := by
    rw [cubicRegularizationResidual_eq_norm_sub]
    exact norm_nonneg _
  have hsq_gamma : ‖a • d + b • e‖ * ‖a • d + b • e‖ = r[trialPoint] x * r[trialPoint] x := by
    simpa [pow_two] using hsq
  have hnorm_eq : ‖a • d + b • e‖ = r[trialPoint] x := by
    nlinarith
  simpa [a, b, d, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hnorm_eq

/-- Helper for Lemma 4.1.2: the scalar Hessian of the restricted cubic-model slice splits into the
scalar Hessians of its quadratic Taylor part and its cubic penalty part. -/
lemma cubic_model_slice_hessian_eq_quadratic_plus_penalty
    {f : E → ℝ} {M : ℝ} {x trialPoint : E}
    (hf : ContDiffAt ℝ 2 f x)
    (v : E) :
    let φ := fun t : ℝ ↦ cubicRegularizationQuadraticApproximation f M x (trialPoint + t • v)
    let q := fun t : ℝ ↦ secondOrderTaylorModelAt f x (trialPoint + t • v)
    let p := fun t : ℝ ↦ (M / 6 : ℝ) * ‖(trialPoint + t • v) - x‖ ^ (3 : ℕ)
    inner ℝ (hessian φ 0 1) 1 =
      inner ℝ (hessian q 0 1) 1 + inner ℝ (hessian p 0 1) 1 := by
  dsimp
  let a : E := trialPoint - x
  let q : ℝ → ℝ := fun t : ℝ ↦ secondOrderTaylorModelAt f x (trialPoint + t • v)
  let p : ℝ → ℝ := fun t : ℝ ↦ (M / 6 : ℝ) * ‖a + t • v‖ ^ (3 : ℕ)
  let T : E →L[ℝ] E := hessian f x
  let g : E := ∇ f x
  let A : ℝ := inner ℝ g v + inner ℝ (T a) v
  let B : ℝ := inner ℝ (T v) v
  have hφEq :
      (fun t : ℝ ↦ cubicRegularizationQuadraticApproximation f M x (trialPoint + t • v)) =
        q + p := by
    -- Split the restricted cubic model into the quadratic Taylor slice and the cubic penalty.
    funext t
    simp [q, p, cubicRegularizationQuadraticApproximation, a, sub_eq_add_neg, add_assoc,
      add_left_comm, add_comm]
  have hselfAdjoint : IsSelfAdjoint T := by
    simpa using (fderiv_gradient_isSymmetric_of_contDiffAt hf).isSelfAdjoint
  have hcross :
      inner ℝ (T v) a = inner ℝ (T a) v := by
    calc
      inner ℝ (T v) a = inner ℝ v (T a) := hselfAdjoint.isSymmetric v a
      _ = inner ℝ (T a) v := by
          rw [real_inner_comm]
  have hqPoly :
      q =
        fun t : ℝ ↦
          secondOrderTaylorModelAt f x trialPoint +
            A * t +
            (B / 2 : ℝ) * t ^ (2 : ℕ) := by
    -- Expand the quadratic Taylor slice into an explicit scalar quadratic polynomial.
    funext t
    have hdisp : trialPoint + t • v - x = a + t • v := by
      simp [a, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    change
      secondOrderTaylorModelAt f x (trialPoint + t • v) =
        secondOrderTaylorModelAt f x trialPoint +
          A * t +
          (B / 2 : ℝ) * t ^ (2 : ℕ)
    rw [secondOrderTaylorModelAt_apply, secondOrderTaylorModelAt_apply, hdisp]
    simp [A, B, T, g, a, hcross, inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right, pow_two]
    ring
  have hqDiff : ∀ t : ℝ, DifferentiableAt ℝ q t := by
    -- The quadratic Taylor slice is a scalar polynomial in the line parameter.
    intro t
    rw [hqPoly]
    fun_prop
  have hpDiff : ∀ t : ℝ, DifferentiableAt ℝ p t := by
    -- The cubic penalty slice is differentiable because `‖·‖^3` is `C¹`.
    intro t
    have hthree : 1 < (3 : ℝ) := by
      norm_num
    have hlineDiff : DifferentiableAt ℝ (fun s : ℝ ↦ a + s • v) t := by
      simpa [one_smul] using
        (HasDerivAt.const_add a ((hasDerivAt_id t).smul_const v)).differentiableAt
    have hnormDiff : DifferentiableAt ℝ (fun z : E ↦ ‖z‖ ^ (3 : ℝ)) (a + t • v) :=
      (differentiable_norm_rpow (E := E) hthree) (a + t • v)
    have hpDiffRpow :
        DifferentiableAt ℝ (fun s : ℝ ↦ (M / 6 : ℝ) * ‖a + s • v‖ ^ (3 : ℝ)) t := by
      exact (hnormDiff.comp t hlineDiff).const_mul (M / 6 : ℝ)
    convert hpDiffRpow using 1
    ext s
    rw [show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast]
  have hgradAddEq :
      ∇ (q + p) = fun t : ℝ ↦ ∇ q t + ∇ p t := by
    -- Differentiate the sum pointwise and identify the resulting gradient.
    refine gradient_eq ?_
    intro t
    have hqGrad : HasGradientAt q (∇ q t) t := (hqDiff t).hasGradientAt
    have hpGrad : HasGradientAt p (∇ p t) t := (hpDiff t).hasGradientAt
    rw [hasGradientAt_iff_hasFDerivAt] at hqGrad hpGrad ⊢
    simpa [ContinuousLinearMap.add_apply] using hqGrad.add hpGrad
  have hqGradDiff : DifferentiableAt ℝ (∇ q) 0 := by
    -- The quadratic-slice gradient is affine, so its derivative at `0` already exists.
    exact (quadratic_slice_gradient_hasDerivAt_zero (hf := hf) (x := x)
      (trialPoint := trialPoint) v).differentiableAt
  have hpGradDiff : DifferentiableAt ℝ (∇ p) 0 := by
    -- The cubic-slice gradient derivative is handled by the residual-zero/nonzero split.
    have hpGradEq :
        ∇ p = fun t ↦ (M / 2 : ℝ) * ‖a + t • v‖ * inner ℝ (a + t • v) v := by
      simpa [p] using cubic_penalty_slice_gradient_eq (M := M) a v
    rw [hpGradEq]
    by_cases ha : a = 0
    · exact
        (cubic_penalty_slice_gradient_hasDerivAt_zero_of_zero_residual
          (M := M) (a := a) (v := v) ha).differentiableAt
    · exact
        (cubic_penalty_slice_gradient_hasDerivAt_zero_of_nonzero_residual
          (M := M) (a := a) (v := v) ha).differentiableAt
  have hhessSplit :
      hessian (q + p) 0 1 = hessian q 0 1 + hessian p 0 1 := by
    -- The Hessian is the derivative of the gradient, so the scalar split follows from `fderiv`
    -- linearity on the already-differentiable gradient functions.
    rw [hessian, hgradAddEq]
    change (fderiv ℝ (fun t : ℝ ↦ ∇ q t + ∇ p t) 0) 1 =
      ((fderiv ℝ (∇ q) 0) + (fderiv ℝ (∇ p) 0)) 1
    simpa using
      congrArg (fun L : ℝ →L[ℝ] ℝ ↦ L 1)
        (fderiv_add (f := ∇ q) (g := ∇ p) hqGradDiff hpGradDiff)
  -- Apply the Hessian split inside the scalar quadratic form `⟪·,1⟫`.
  calc
    inner ℝ
        (hessian
          (fun t : ℝ ↦ cubicRegularizationQuadraticApproximation f M x (trialPoint + t • v))
          0 1) 1
      = inner ℝ (hessian (q + p) 0 1) 1 := by
          rw [← hφEq]
    _ = inner ℝ (hessian q 0 1 + hessian p 0 1) 1 := by
          rw [hhessSplit]
    _ = inner ℝ (hessian q 0 1) 1 + inner ℝ (hessian p 0 1) 1 := by
          rw [inner_add_left]
    _ =
        inner ℝ
            (hessian (fun t : ℝ ↦ secondOrderTaylorModelAt f x (trialPoint + t • v)) 0 1) 1 +
          inner ℝ
            (hessian (fun t : ℝ ↦ (M / 6 : ℝ) * ‖(trialPoint + t • v) - x‖ ^ (3 : ℕ)) 0 1) 1 := by
          simp [q, p, a, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Lemma 4.1.2: on a direction orthogonal to the residual `trialPoint - x`, the cubic
penalty slice contributes exactly the textbook quadratic term `((M / 2) * r_M(x)) ‖e‖²`. -/
lemma cubic_penalty_slice_hessian_quadratic_orthogonal
    {M : ℝ} {x trialPoint e : E}
    (he_orth : inner ℝ (trialPoint - x) e = 0) :
    inner ℝ
        (hessian
          (fun t : ℝ ↦ (M / 6 : ℝ) * ‖(trialPoint + t • e) - x‖ ^ (3 : ℕ))
          0
          1)
        1
      = ((M / 2) * r[trialPoint] x) * ‖e‖ ^ (2 : ℕ) := by
  let a : E := trialPoint - x
  let ψ : ℝ → ℝ := fun t : ℝ ↦ (M / 6 : ℝ) * ‖a + t • e‖ ^ (3 : ℕ)
  have hψ :
      (fun t : ℝ ↦ (M / 6 : ℝ) * ‖(trialPoint + t • e) - x‖ ^ (3 : ℕ)) = ψ := by
    -- Rewrite the cubic penalty slice through the fixed residual vector `a`.
    funext t
    simp [ψ, a, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hgradEq :
      ∇ ψ = fun t ↦ (M / 2 : ℝ) * ‖a + t • e‖ * inner ℝ (a + t • e) e := by
    simpa [ψ] using cubic_penalty_slice_gradient_eq (M := M) a e
  have hhessEval0 :
      hessian ψ (0 : ℝ) (1 : ℝ) =
        deriv (fun t : ℝ ↦ (M / 2 : ℝ) * ‖a + t • e‖ * inner ℝ (a + t • e) e) (0 : ℝ) := by
    -- Evaluate the scalar Hessian through the derivative of the explicit gradient formula.
    rw [hessian]
    calc
      fderiv ℝ (∇ ψ) (0 : ℝ) (1 : ℝ) = deriv (∇ ψ) (0 : ℝ) := by
        simpa using
          (fderiv_eq_deriv_mul
            (f := ∇ ψ)
            (x := (0 : ℝ))
            (y := (1 : ℝ)))
      _ =
          deriv
            (fun t : ℝ ↦ (M / 2 : ℝ) * ‖a + t • e‖ * inner ℝ (a + t • e) e)
            (0 : ℝ) := by
              rw [hgradEq]
  have hhessEval :
      inner ℝ (hessian ψ (0 : ℝ) (1 : ℝ)) (1 : ℝ) =
        deriv (fun t : ℝ ↦ (M / 2 : ℝ) * ‖a + t • e‖ * inner ℝ (a + t • e) e) (0 : ℝ) := by
    calc
      inner ℝ (hessian ψ (0 : ℝ) (1 : ℝ)) (1 : ℝ)
          =
            inner ℝ
              (deriv
                (fun t : ℝ ↦ (M / 2 : ℝ) * ‖a + t • e‖ * inner ℝ (a + t • e) e)
                (0 : ℝ))
              (1 : ℝ) := by
                exact congrArg (fun z : ℝ ↦ inner ℝ z (1 : ℝ)) hhessEval0
      _ =
          deriv
            (fun t : ℝ ↦ (M / 2 : ℝ) * ‖a + t • e‖ * inner ℝ (a + t • e) e)
            (0 : ℝ) := by
              change
                1 *
                    (deriv
                      (fun t : ℝ ↦ (M / 2 : ℝ) * ‖a + t • e‖ * inner ℝ (a + t • e) e)
                      (0 : ℝ)) =
                  deriv
                    (fun t : ℝ ↦ (M / 2 : ℝ) * ‖a + t • e‖ * inner ℝ (a + t • e) e)
                    (0 : ℝ)
              ring
  have hresidual :
      r[trialPoint] x = ‖a‖ := by
    rw [cubicRegularizationResidual_eq_norm_sub]
    simpa [a] using norm_sub_rev x trialPoint
  have he_orth' : inner ℝ a e = 0 := by
    simpa [a] using he_orth
  by_cases ha : a = 0
  · have hderiv :
        deriv (fun t : ℝ ↦ (M / 2 : ℝ) * ‖a + t • e‖ * inner ℝ (a + t • e) e) (0 : ℝ) = 0 := by
      exact (cubic_penalty_slice_gradient_hasDerivAt_zero_of_zero_residual (M := M) ha).deriv
    -- When the residual vanishes, the cubic penalty has no quadratic contribution at the base.
    rw [hψ, hhessEval, hderiv, hresidual, ha]
    simp
  · have hderiv :
        deriv (fun t : ℝ ↦ (M / 2 : ℝ) * ‖a + t • e‖ * inner ℝ (a + t • e) e) (0 : ℝ) =
          ((M / 2) * ‖a‖) * ‖e‖ ^ (2 : ℕ) +
            ((M / 2) / ‖a‖) * (inner ℝ a e) ^ (2 : ℕ) := by
      exact
        (cubic_penalty_slice_gradient_hasDerivAt_zero_of_nonzero_residual
          (M := M) (a := a) (v := e) ha).deriv
    -- Orthogonality kills the rank-one correction term in the nonzero-residual formula.
    rw [hψ, hhessEval, hderiv, hresidual, he_orth']
    ring

/-- Helper for Lemma 4.1.2: every direction orthogonal to the residual already satisfies the
regularized-Hessian quadratic lower bound by the exact scalar slice computation. -/
lemma regularized_hessian_orthogonal_direction_nonneg
    {f : E → ℝ} {M : ℝ} {x trialPoint e : E}
    (hf : ContDiffAt ℝ 2 f x)
    (hmin :
      IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ trialPoint)
    (he_orth : inner ℝ (trialPoint - x) e = 0) :
    0 ≤
      inner ℝ
        (((hessian f x + ((M / 2) * r[trialPoint] x) • (1 : E →L[ℝ] E)) e))
        e := by
  have hslice_nonneg :
      0 ≤
        inner ℝ
          (hessian
            (fun t : ℝ ↦ cubicRegularizationQuadraticApproximation f M x (trialPoint + t • e))
            0
            1)
          1 := by
    -- The scalar slice through the minimizer has nonnegative Hessian at the minimizing
    -- parameter.
    simpa using slice_hessian_quadratic_nonneg_at_local_min (hf := hf) (hmin := hmin) e
  have hsplit :
      inner ℝ
          (hessian
            (fun t : ℝ ↦ cubicRegularizationQuadraticApproximation f M x (trialPoint + t • e))
            0
            1)
          1 =
        inner ℝ
            (hessian (fun t : ℝ ↦ secondOrderTaylorModelAt f x (trialPoint + t • e)) 0 1)
            1 +
          inner ℝ
            (hessian (fun t : ℝ ↦ (M / 6 : ℝ) * ‖(trialPoint + t • e) - x‖ ^ (3 : ℕ)) 0 1)
            1 := by
    -- Split the scalar Hessian into the quadratic Taylor part and the cubic penalty part.
    simpa using cubic_model_slice_hessian_eq_quadratic_plus_penalty (hf := hf) (x := x)
      (trialPoint := trialPoint) (M := M) (v := e)
  have hquad :
      inner ℝ
          (hessian (fun t : ℝ ↦ secondOrderTaylorModelAt f x (trialPoint + t • e)) 0 1)
          1 =
        inner ℝ (hessian f x e) e := by
    -- The quadratic Taylor slice has the ambient Hessian quadratic form as its scalar Hessian.
    simpa using quadratic_slice_hessian_quadratic_at_zero (hf := hf) (x := x)
      (trialPoint := trialPoint) e
  have hpenalty :
      inner ℝ
          (hessian (fun t : ℝ ↦ (M / 6 : ℝ) * ‖(trialPoint + t • e) - x‖ ^ (3 : ℕ)) 0 1)
          1 =
        ((M / 2) * r[trialPoint] x) * ‖e‖ ^ (2 : ℕ) := by
    -- Orthogonality removes the extra square from the exact cubic-slice Hessian.
    simpa using cubic_penalty_slice_hessian_quadratic_orthogonal (M := M) (x := x)
      (trialPoint := trialPoint) (e := e) he_orth
  have hsum :
      0 ≤ inner ℝ (hessian f x e) e + ((M / 2) * r[trialPoint] x) * ‖e‖ ^ (2 : ℕ) := by
    rw [hsplit, hquad, hpenalty] at hslice_nonneg
    exact hslice_nonneg
  -- Repackage the scalar sum as the quadratic form of the shifted Hessian operator.
  simpa [ContinuousLinearMap.add_apply, inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq,
    mul_assoc, mul_left_comm, mul_comm] using hsum

omit [CompleteSpace E] in
/-- Helper for Lemma 4.1.2: scaling a vector pulls out a scalar square from the ambient quadratic
form associated with a continuous linear operator. -/
lemma regularizedHessianQuadraticForm_smul
    (B : E →L[ℝ] E)
    (c : ℝ)
    (u : E) :
    inner ℝ (B (c • u)) (c • u) = c ^ (2 : ℕ) * inner ℝ (B u) u := by
  -- Pull the scalar through the operator and both inner-product slots, then collect the square.
  rw [ContinuousLinearMap.map_smul, inner_smul_left, inner_smul_right]
  simp [pow_two, mul_assoc]

omit [CompleteSpace E] in
/-- Helper for Lemma 4.1.2: every nonradial vector in the residual plane is a scalar multiple of
the sphere-path normal form `r • e - t • d`. -/
lemma residualPlaneReparameterization
    {d e : E} {r a b : ℝ}
    (hr : r ≠ 0)
    (hb : b ≠ 0) :
    let t : ℝ := - (a * r) / b
    a • d + b • e = (b / r) • (r • e - t • d) := by
  dsimp
  have hscale_r : (b / r : ℝ) * r = b := by
    field_simp [hr]
  have hscale_t : (b / r : ℝ) * (-(a * r) / b) = -a := by
    field_simp [hr, hb]
  symm
  calc
    (b / r : ℝ) • (r • e - (-(a * r) / b) • d)
      = ((b / r : ℝ) * r) • e - ((b / r : ℝ) * (-(a * r) / b)) • d := by
          rw [smul_sub, smul_smul, smul_smul]
    _ = b • e - (-a) • d := by
          rw [hscale_r, hscale_t]
    _ = a • d + b • e := by
          simp [sub_eq_add_neg, add_comm]

omit [CompleteSpace E] in
/-- Helper for Lemma 4.1.2: the stereographic sphere path displacement rewrites as a scalar
multiple of the residual-plane vector `r[trialPoint] x • e - t • (trialPoint - x)`. -/
lemma sphere_path_sub_trialPoint_eq_scaled_plane_vector
    {x trialPoint e : E} :
    let r := r[trialPoint] x
    let gamma :=
      fun t : ℝ ↦
        x + ((1 - t ^ (2 : ℕ)) / (1 + t ^ (2 : ℕ))) • (trialPoint - x) +
          ((2 * r * t) / (1 + t ^ (2 : ℕ))) • e
    ∀ t,
      gamma t - trialPoint =
        ((2 * t) / (1 + t ^ (2 : ℕ))) •
          (r[trialPoint] x • e - t • (trialPoint - x)) := by
  dsimp
  intro t
  have hden_pos : 0 < 1 + t ^ (2 : ℕ) := by
    positivity
  have hden_ne : (1 + t ^ (2 : ℕ)) ≠ 0 := ne_of_gt hden_pos
  have hdCoeff :
      (((1 - t ^ (2 : ℕ)) / (1 + t ^ (2 : ℕ))) - 1 : ℝ) =
        ((2 * t) / (1 + t ^ (2 : ℕ))) * (-t) := by
    field_simp [hden_ne]
    ring
  have heCoeff :
      (((2 * r[trialPoint] x * t) / (1 + t ^ (2 : ℕ))) : ℝ) =
        ((2 * t) / (1 + t ^ (2 : ℕ))) * r[trialPoint] x := by
    field_simp [hden_ne]
  -- Recenter the path at `trialPoint` and collect the common scalar factor.
  calc
    (x + ((1 - t ^ (2 : ℕ)) / (1 + t ^ (2 : ℕ))) • (trialPoint - x) +
          ((2 * r[trialPoint] x * t) / (1 + t ^ (2 : ℕ))) • e) - trialPoint
      =
        ((((1 - t ^ (2 : ℕ)) / (1 + t ^ (2 : ℕ))) - 1) : ℝ) • (trialPoint - x) +
          (((2 * r[trialPoint] x * t) / (1 + t ^ (2 : ℕ))) : ℝ) • e := by
            module
    _ =
        ((((2 * t) / (1 + t ^ (2 : ℕ))) * (-t)) : ℝ) • (trialPoint - x) +
          ((((2 * t) / (1 + t ^ (2 : ℕ))) * r[trialPoint] x) : ℝ) • e := by
            rw [hdCoeff, heCoeff]
    _ =
        ((2 * t) / (1 + t ^ (2 : ℕ))) • ((-t) • (trialPoint - x)) +
          ((2 * t) / (1 + t ^ (2 : ℕ))) • (r[trialPoint] x • e) := by
            rw [smul_smul, smul_smul]
    _ =
        ((2 * t) / (1 + t ^ (2 : ℕ))) •
          (((-t) • (trialPoint - x)) + r[trialPoint] x • e) := by
            rw [← smul_add]
    _ =
        ((2 * t) / (1 + t ^ (2 : ℕ))) •
          (r[trialPoint] x • e - t • (trialPoint - x)) := by
            congr 1
            simp [sub_eq_add_neg, add_assoc, add_comm]

/-- Helper for Lemma 4.1.2: the sphere comparison turns the closed-ball quadratic-gap identity
into nonnegativity of the regularized-Hessian quadratic form on the residual sphere plane. -/
lemma regularized_hessian_quadratic_nonneg_on_sphere_plane
    {f : E → ℝ} {M : ℝ}
    (hM : 0 ≤ M)
    {x trialPoint e : E}
    (hf : ContDiffAt ℝ 2 f x)
    (hmin :
      IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ trialPoint)
    (he_unit : ‖e‖ = 1)
    (he_orth : inner ℝ (trialPoint - x) e = 0) :
    let B := hessian f x + ((M / 2) * r[trialPoint] x) • (1 : E →L[ℝ] E)
    ∀ t : ℝ,
      0 ≤
        inner ℝ
          (B (r[trialPoint] x • e - t • (trialPoint - x)))
          (r[trialPoint] x • e - t • (trialPoint - x)) := by
  dsimp
  intro t
  let B : E →L[ℝ] E := hessian f x + ((M / 2) * r[trialPoint] x) • (1 : E →L[ℝ] E)
  by_cases ht : t = 0
  · subst ht
    have hbase :
        0 ≤ inner ℝ (B e) e := by
      -- The orthogonal direction case is already handled by the scalar slice computation.
      simpa [B] using
        regularized_hessian_orthogonal_direction_nonneg
          (hf := hf) (hmin := hmin) (x := x) (trialPoint := trialPoint) (e := e) he_orth
    have hscaled :
        0 ≤ inner ℝ (B (r[trialPoint] x • e)) (r[trialPoint] x • e) := by
      -- Scale the orthogonal direction by the residual radius.
      rw [regularizedHessianQuadraticForm_smul (B := B) (c := r[trialPoint] x) (u := e)]
      have hrsq_nonneg : 0 ≤ (r[trialPoint] x) ^ (2 : ℕ) := by
        positivity
      nlinarith
    simpa [B, smul_smul, mul_assoc, mul_left_comm, mul_comm] using hscaled
  · let r : ℝ := r[trialPoint] x
    let gamma :=
      fun s : ℝ ↦
        x + ((1 - s ^ (2 : ℕ)) / (1 + s ^ (2 : ℕ))) • (trialPoint - x) +
          ((2 * r * s) / (1 + s ^ (2 : ℕ))) • e
    let c : ℝ := (2 * t) / (1 + t ^ (2 : ℕ))
    let u : E := r[trialPoint] x • e - t • (trialPoint - x)
    -- Route correction: use the existing closed-ball quadratic-gap identity on the stereographic
    -- sphere path, then divide out the scalar square from the rewritten displacement.
    have hgamma_radius : ‖gamma t - x‖ = r := by
      simpa [r, gamma] using
        sphere_path_has_fixed_residual_radius
          (x := x) (trialPoint := trialPoint) (e := e) he_unit he_orth t
    have hgamma_ball : gamma t ∈ Metric.closedBall x r := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact le_of_eq hgamma_radius
    have hgap_nonneg :
        0 ≤ secondOrderTaylorModelAt f x (gamma t) - secondOrderTaylorModelAt f x trialPoint := by
      exact sub_nonneg.mpr
        ((quadratic_model_isMinOn_closedBall_of_cubic_model_global_min hM hmin) hgamma_ball)
    have hgamma_radius_sq : ‖gamma t - x‖ ^ (2 : ℕ) = r ^ (2 : ℕ) := by
      rw [hgamma_radius]
    have hgap_eval :
        secondOrderTaylorModelAt f x (gamma t) - secondOrderTaylorModelAt f x trialPoint =
          (1 / 2 : ℝ) * inner ℝ (B (gamma t - trialPoint)) (gamma t - trialPoint) := by
      -- On the residual sphere, the radius-defect term in the closed-ball gap identity vanishes.
      rw [regularized_hessian_quadratic_gap_on_closedBall hf hmin, hgamma_radius_sq]
      ring
    have hpath :
        gamma t - trialPoint = c • u := by
      simpa [r, gamma, c, u] using
        sphere_path_sub_trialPoint_eq_scaled_plane_vector
          (x := x) (trialPoint := trialPoint) (e := e) t
    have hscaled_nonneg :
        0 ≤ (1 / 2 : ℝ) * (c ^ (2 : ℕ) * inner ℝ (B u) u) := by
      rw [← regularizedHessianQuadraticForm_smul, ← hpath, ← hgap_eval]
      exact hgap_nonneg
    have hc_ne : c ≠ 0 := by
      dsimp [c]
      apply div_ne_zero
      · exact mul_ne_zero (by norm_num) ht
      · positivity
    have hc_sq_pos : 0 < c ^ (2 : ℕ) := by
      have hc_sq_ne : c ^ (2 : ℕ) ≠ 0 := by
        exact pow_ne_zero 2 hc_ne
      have hc_sq_nonneg : 0 ≤ c ^ (2 : ℕ) := by
        positivity
      exact lt_of_le_of_ne hc_sq_nonneg (by simpa using hc_sq_ne.symm)
    have hhalf_pos : 0 < (1 / 2 : ℝ) := by
      norm_num
    have hu_nonneg : 0 ≤ inner ℝ (B u) u := by
      nlinarith
    simpa [B, u] using hu_nonneg

/-- Helper for Lemma 4.1.2: the regularized-Hessian quadratic form is nonnegative on every
vector in the plane spanned by the residual and a unit orthogonal direction. -/
lemma regularized_hessian_quadratic_nonneg_on_residual_plane
    {f : E → ℝ} {M : ℝ}
    (hM : 0 ≤ M)
    {x trialPoint e : E}
    (hf : ContDiffAt ℝ 2 f x)
    (hmin :
      IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ trialPoint)
    (htx : trialPoint ≠ x)
    (he_unit : ‖e‖ = 1)
    (he_orth : inner ℝ (trialPoint - x) e = 0) :
    let B := hessian f x + ((M / 2) * r[trialPoint] x) • (1 : E →L[ℝ] E)
    ∀ a b : ℝ,
      0 ≤ inner ℝ (B (a • (trialPoint - x) + b • e)) (a • (trialPoint - x) + b • e) := by
  dsimp
  intro a b
  let B : E →L[ℝ] E := hessian f x + ((M / 2) * r[trialPoint] x) • (1 : E →L[ℝ] E)
  by_cases hb : b = 0
  · subst hb
    have hbase :
        0 ≤ inner ℝ (B (trialPoint - x)) (trialPoint - x) := by
      -- The residual direction is already covered by the reflected closed-ball comparison.
      simpa [B] using
        regularized_hessian_displacement_quadratic_nonneg
          (hM := hM) (hf := hf) (hmin := hmin) (x := x) (trialPoint := trialPoint)
    have hscaled :
        0 ≤ inner ℝ (B (a • (trialPoint - x))) (a • (trialPoint - x)) := by
      -- Pull the scalar square out of the radial quadratic form.
      rw [regularizedHessianQuadraticForm_smul (B := B) (c := a) (u := trialPoint - x)]
      have hasq_nonneg : 0 ≤ a ^ (2 : ℕ) := by
        positivity
      nlinarith
    simpa [B, smul_smul, mul_assoc, mul_left_comm, mul_comm] using hscaled
  · have hd_ne : trialPoint - x ≠ 0 := sub_ne_zero.mpr htx
    have hr_ne : r[trialPoint] x ≠ 0 := by
      rw [cubicRegularizationResidual_eq_norm_sub]
      simpa [norm_sub_rev] using norm_ne_zero_iff.mpr hd_ne
    let t : ℝ := - (a * r[trialPoint] x) / b
    have hsphere :
        0 ≤ inner ℝ (B (r[trialPoint] x • e - t • (trialPoint - x)))
            (r[trialPoint] x • e - t • (trialPoint - x)) := by
      -- The sphere-path family gives the nonradial plane positivity statement.
      simpa [B, t] using
        regularized_hessian_quadratic_nonneg_on_sphere_plane
          (hM := hM) (hf := hf) (hmin := hmin)
          (x := x) (trialPoint := trialPoint) (e := e) he_unit he_orth t
    have hscaled :
        0 ≤
          inner ℝ
            (B (((b / r[trialPoint] x) : ℝ) • (r[trialPoint] x • e - t • (trialPoint - x))))
            (((b / r[trialPoint] x) : ℝ) • (r[trialPoint] x • e - t • (trialPoint - x))) := by
      -- Scale the sphere-path normal form back to the arbitrary residual-plane vector.
      rw [regularizedHessianQuadraticForm_smul
        (B := B) (c := (b / r[trialPoint] x : ℝ))
        (u := r[trialPoint] x • e - t • (trialPoint - x))]
      have hsq_nonneg : 0 ≤ (b / r[trialPoint] x : ℝ) ^ (2 : ℕ) := by
        positivity
      nlinarith
    have hreparam :
        a • (trialPoint - x) + b • e =
          (b / r[trialPoint] x : ℝ) • (r[trialPoint] x • e - t • (trialPoint - x)) := by
      simpa [t, add_comm, add_left_comm, add_assoc] using
        residualPlaneReparameterization
          (d := trialPoint - x) (e := e) (r := r[trialPoint] x) (a := a) (b := b) hr_ne hb
    rw [hreparam]
    exact hscaled

/-- Lemma 4.1.2 on scalar quadratic forms: if `M ≥ 0`, `f` is `C²` at `x`, and `T_M(x)`
globally minimizes the chapter cubic model centered at `x`, then the regularized Hessian quadratic
form `v ↦ ⟪(hessian f x + (M / 2) r_M(x) • 1) v, v⟫` is nonnegative on every direction `v`. -/
lemma regularized_hessian_quadratic_nonneg_of_cubic_model_global_min
    {f : E → ℝ} {M : ℝ}
    (hM : 0 ≤ M)
    {x trialPoint : E}
    (hf : ContDiffAt ℝ 2 f x)
    (hmin :
      IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ trialPoint)
    (v : E) :
    0 ≤
      inner ℝ
        ((hessian f x + ((M / 2) * r[trialPoint] x) • (1 : E →L[ℝ] E)) v)
        v := by
  by_cases htx : trialPoint = x
  · subst trialPoint
    -- When the residual vanishes, the shifted operator reduces to the ambient Hessian.
    simpa [cubicRegularizationResidual_eq_norm_sub] using
      regularized_hessian_quadratic_nonneg_of_zero_residual
        (hf := hf) (hmin := hmin) (x := x) v
  · let d : E := trialPoint - x
    let B : E →L[ℝ] E := hessian f x + ((M / 2) * r[trialPoint] x) • (1 : E →L[ℝ] E)
    have hd_ne : d ≠ 0 := by
      exact sub_ne_zero.mpr htx
    have hd_self_ne : inner ℝ d d ≠ 0 := by
      rw [real_inner_self_eq_norm_sq]
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hd_ne)
    let a : ℝ := inner ℝ d v / inner ℝ d d
    let w : E := v - a • d
    have ha_mul : a * inner ℝ d d = inner ℝ d v := by
      dsimp [a]
      field_simp [hd_self_ne]
    have hw_orth : inner ℝ d w = 0 := by
      -- Project `v` onto the residual line and keep the orthogonal remainder.
      calc
        inner ℝ d w = inner ℝ d v - inner ℝ d (a • d) := by
          simp [w, inner_sub_right]
        _ = inner ℝ d v - a * inner ℝ d d := by
          simp [inner_smul_right]
        _ = 0 := by
          nlinarith [ha_mul]
    have hv_decomp : v = a • d + w := by
      -- Reassemble the residual component and the orthogonal remainder.
      dsimp [w]
      module
    by_cases hw : w = 0
    · have hbase :
          0 ≤ inner ℝ (B d) d := by
        -- The purely residual case is already the radial positivity lemma.
        simpa [B, d] using
          regularized_hessian_displacement_quadratic_nonneg
            (hM := hM) (hf := hf) (hmin := hmin) (x := x) (trialPoint := trialPoint)
      have hscaled :
          0 ≤ inner ℝ (B (a • d)) (a • d) := by
        -- Pull out the scalar square along the residual line.
        rw [regularizedHessianQuadraticForm_smul (B := B) (c := a) (u := d)]
        have hasq_nonneg : 0 ≤ a ^ (2 : ℕ) := by
          positivity
        nlinarith
      have hv_eq : v = a • d := by
        dsimp [w] at hw
        exact sub_eq_zero.mp hw
      simpa [B, d, hv_eq] using hscaled
    · let e : E := ‖w‖⁻¹ • w
      have hw_norm_ne : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
      have hw_norm_pos : 0 < ‖w‖ := by
        exact norm_pos_iff.mpr hw
      have he_unit : ‖e‖ = 1 := by
        -- Normalize the orthogonal remainder to a unit vector.
        dsimp [e]
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg]
        · field_simp [hw_norm_ne]
        · exact inv_nonneg.mpr (norm_nonneg _)
      have he_orth : inner ℝ d e = 0 := by
        -- Orthogonality is preserved under scalar normalization.
        dsimp [e]
        rw [inner_smul_right]
        simp [hw_orth]
      have hw_eq : ‖w‖ • e = w := by
        -- Undo the normalization to recover the original orthogonal remainder.
        dsimp [e]
        rw [smul_smul]
        have hcoeff : ‖w‖ * ‖w‖⁻¹ = (1 : ℝ) := by
          field_simp [hw_norm_ne]
        simp [hcoeff]
      have hplane :
          0 ≤ inner ℝ (B (a • d + ‖w‖ • e)) (a • d + ‖w‖ • e) := by
        -- Route correction: use the residual-plane positivity lemma rather than expanding the
        -- mixed term directly in the orthogonal decomposition.
        simpa [B, d] using
          regularized_hessian_quadratic_nonneg_on_residual_plane
            (hM := hM) (hf := hf) (hmin := hmin) (htx := htx)
            (x := x) (trialPoint := trialPoint) (e := e) he_unit he_orth a ‖w‖
      have hv_eq : v = a • d + ‖w‖ • e := by
        calc
          v = a • d + w := hv_decomp
          _ = a • d + ‖w‖ • e := by
              exact congrArg (fun z ↦ a • d + z) hw_eq.symm
      simpa [B, d, hv_eq] using hplane

-- Proof sketch: restrict the cubic model
-- `cubicRegularizationQuadraticApproximation f M x` to the line `trialPoint + t • v`, and use
-- that a global minimizer has nonnegative second derivative in every direction. The second
-- derivative of the cubic term yields an extra nonnegative contribution because `M ≥ 0`, leaving
-- the lower bound `⟪(hessian f x + (M / 2) r_M(x) • 1) v, v⟫ ≥ 0` for all `v`. Under the
-- canonical `C²` symmetry bridge, this is exactly positivity of the regularized Hessian
-- operator.
/-- Helper for Lemma 4.1.2: the scalar quadratic-form nonnegativity statement upgrades to
positivity of the regularized Hessian operator using the canonical `C²` symmetry bridge. -/
theorem regularizedHessian_isPositive_of_isMinOn_cubicRegularizationQuadraticApproximation
    {f : E → ℝ} {M : ℝ}
    (hM : 0 ≤ M) {x : E}
    {trialPoint : E}
    (hf : ContDiffAt ℝ 2 f x)
    (hmin :
      IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ trialPoint) :
    (hessian f x +
        ((M / 2) * r[trialPoint] x) •
          (1 : E →L[ℝ] E)).IsPositive := by
  -- Package the remaining scalar quadratic-form statement with the canonical symmetry bridge.
  apply (ContinuousLinearMap.isPositive_toLinearMap_iff _).mp
  refine (LinearMap.isPositive_iff _).2 ?_
  constructor
  · -- The Hessian is symmetric under the `C²` hypothesis, and scalar multiples of the identity
    -- preserve symmetry.
    have hhessSymm : (hessian f x).toLinearMap.IsSymmetric := by
      simpa using fderiv_gradient_isSymmetric_of_contDiffAt hf
    have hidSymm : (LinearMap.id : E →ₗ[ℝ] E).IsSymmetric :=
      LinearMap.IsSymmetric.id
    simpa using
      hhessSymm.add
        (LinearMap.IsSymmetric.smul (c := ((M / 2) * r[trialPoint] x)) (by simp) hidSymm)
  · -- The remaining quadratic-form nonnegativity is delegated to the reduced global-minimum
    -- lemma above.
    intro v
    simpa using
      regularized_hessian_quadratic_nonneg_of_cubic_model_global_min hM hf hmin v

end Intrinsic

section Euclidean

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Euclidean matrix bridge for Lemma 4.1.2: the intrinsic regularized-Hessian positivity theorem
specializes to positive semidefiniteness of the standard-basis Hessian matrix. -/
theorem regularizedHessian_posSemidef_of_isMinOn_cubicRegularizationQuadraticApproximation
    {f : E → ℝ} {M : ℝ}
    (hM : 0 ≤ M) {x : E}
    {trialPoint : E}
    (hf : ContDiffAt ℝ 2 f x)
    (hmin :
      IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ trialPoint) :
    (∇² f x +
        ((M / 2) * r[trialPoint] x) •
          (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by
  have hpos :
      (hessian f x +
          ((M / 2) * r[trialPoint] x) •
            (1 : E →L[ℝ] E)).IsPositive :=
    regularizedHessian_isPositive_of_isMinOn_cubicRegularizationQuadraticApproximation
      hM hf hmin
  simpa [hessianMatrix, LinearMap.toMatrixOrthonormal] using
    (LinearMap.posSemidef_toMatrix_iff (EuclideanSpace.basisFun (Fin n) ℝ)).2 hpos.toLinearMap

end Euclidean
