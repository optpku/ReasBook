/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Lemma_1_5_11
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Lemma_4_1_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient
open scoped ConstrainedArgmin
open scoped CubicRegularizationModelNotation

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Lemma 4.2.5 lies in the cubic-regularization / Hessian-Lipschitz remainder domain on complete
real inner-product spaces.

Sampled owner declarations:
* `HasLipschitzContinuousHessian` in `Definition_4_2_7`
* `HasLipschitzContinuousHessian.gradient_deviation_le` in `Chap01/Lemma_1_5_11`
* `gradient_norm_le_of_isMinOn_cubicRegularizationQuadraticApproximation` in `Lemma_4_1_4`
* `hessian` in `Chap01/Definition_1_4_16`
* the local stationarity helper proved below from the cubic-model owner in `Lemma_4_1_4`
* `argmin[Set.univ] (m[f; M](x))` in `Definition_4_1_3`

Best owner abstraction:
* the global Hessian-Lipschitz owner `f ∈ C22[L3]`
* the canonical cubic-step owner
  `argmin[Set.univ] (m[f; M](x))`

Primitive data:
* the owner hypothesis `hf : f ∈ C22[L3]`
* the cubic-step membership
  `T ∈ argmin[Set.univ] (m[f; M](x))`

Derived API:
* the gradient remainder bound
  `HasLipschitzContinuousHessian.gradient_deviation_le hf x T`
* the owner radius estimate derived from
  `gradient_norm_le_of_isMinOn_cubicRegularizationQuadraticApproximation`
* the cubic-step first-order optimality equation rewritten below from the cubic-model owner

Source/core/bridge triage:
* source-facing: the gradient-pairing lower bound for one cubic-regularized Newton step
* core/canonical: `f ∈ C22[L3]` and `hessian f x`
* bridge/view: the first-order optimality equation extracted from the cubic-step owner

The previous theorem used a free linear operator `B : E →ₗ[ℝ] E` with pointwise axioms forcing the
cubic term back to the standard Euclidean-radius expression. In this plain real inner-product-space
setting, that extra wrapper is not the mathematical owner. This refinement keeps the source-facing
pairing estimate, but moves the step hypothesis to the canonical cubic-step owner
`argmin[Set.univ] (m[f; M](x))` and uses the intrinsic radius
`‖T - x‖` together with the owner first-order optimality equation. -/

-- Proof sketch: first derive the radius lower bound
-- `‖T - x‖² ≥ (2 / (L₃ + M)) * ‖∇ f T‖` internally from
-- `gradient_norm_le_of_isMinOn_cubicRegularizationQuadraticApproximation`, using
-- `hM : 2 * L₃ ≤ M` to get `0 ≤ M`. Then apply the owner theorem
-- `HasLipschitzContinuousHessian.gradient_deviation_le hf x T`, combine it with
-- the local first-order optimality helper for the cubic-step owner proved below,
-- and obtain
-- `‖∇ f T + ((1 / 2) * M * ‖T - x‖) • (T - x)‖² ≤ ((L₃ / 2) * ‖T - x‖²)²`. Expanding the square
-- yields a lower bound for `⟪∇ f T, x - T⟫` in terms of
-- `‖∇ f T‖² / (M * ‖T - x‖)` and `((M² - L₃²) / (4 * M)) * ‖T - x‖³`. The assumption
-- `2 * L₃ ≤ M` makes this lower bound monotone on the feasible ray
-- `‖T - x‖² ≥ 2 ‖∇ f T‖ / (L₃ + M)`. Since `L₃ : NNReal` and `hM` force
-- `0 ≤ (L₃ : ℝ) + M`, the square-root coefficient is well-defined internally; in the degenerate
-- case `L₃ = M = 0`, the right-hand side vanishes. Evaluating the lower bound at the boundary
-- gives the stated
-- `‖∇ f T‖^(3 / 2)` estimate.

/-- Helper for Lemma 4.2.5: restricting the cubic model to an affine line through a global
minimizer preserves local minimality at the line parameter `0`. -/
lemma cubic_model_line_isLocalMin_at_zero
    {f : E → ℝ} {M : ℝ} {x y : E}
    (hy : IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ y)
    (v : E) :
    IsLocalMin
      (fun t : ℝ ↦ cubicRegularizationQuadraticApproximation f M x (y + t • v))
      0 := by
  have huniv : Set.univ ∈ nhds y := by
    simp
  have hlocal : IsLocalMin (cubicRegularizationQuadraticApproximation f M x) y :=
    hy.isLocalMin huniv
  have hlocal0 :
      IsLocalMin (cubicRegularizationQuadraticApproximation f M x) (y + (0 : ℝ) • v) := by
    simpa using hlocal
  have hline : ContinuousAt (fun t : ℝ ↦ y + t • v) 0 := by
    -- The affine line through `y` is smooth, hence continuous at the minimizing parameter.
    simpa [one_smul] using
      (HasDerivAt.const_add y ((hasDerivAt_id (0 : ℝ)).smul_const v)).continuousAt
  -- Compose ambient local minimality with the affine line parametrization.
  change IsLocalMin
    ((cubicRegularizationQuadraticApproximation f M x) ∘ fun t : ℝ ↦ y + t • v) 0
  exact hlocal0.comp_continuous (g := fun t : ℝ ↦ y + t • v) (b := 0) hline

/-- Helper for Lemma 4.2.5: along an affine line through `y`, the quadratic Taylor model centered
at `x` has derivative `⟪∇ f x + ∇² f(x)(y - x), v⟫` at the line parameter `0`. -/
lemma quadratic_model_line_hasDerivAt_zero
    {f : E → ℝ} {x y v : E}
    (hf2 : ContDiffAt ℝ 2 f x) :
    HasDerivAt
      (fun t : ℝ ↦ secondOrderTaylorModelAt f x (y + t • v))
      (inner ℝ (∇ f x + hessian f x (y - x)) v)
      0 := by
  let a : E := y - x
  let T : E →L[ℝ] E := hessian f x
  let g : E := ∇ f x
  let A : ℝ := inner ℝ g v + inner ℝ (T a) v
  let B : ℝ := inner ℝ (T v) v
  have hsymm : T.IsSymmetric := by
    simpa [T] using fderiv_gradient_isSymmetric_of_contDiffAt hf2
  have hcross : inner ℝ (T v) a = inner ℝ (T a) v := by
    -- Symmetry of the Hessian identifies the two mixed terms in the quadratic expansion.
    calc
      inner ℝ (T v) a = inner ℝ v (T a) := hsymm v a
      _ = inner ℝ (T a) v := by
          rw [real_inner_comm]
  have hpoly :
      (fun t : ℝ ↦ secondOrderTaylorModelAt f x (y + t • v)) =
        fun t : ℝ ↦ secondOrderTaylorModelAt f x y + A * t + (B / 2 : ℝ) * t ^ (2 : ℕ) := by
    -- Expand the quadratic model along the line and collect the scalar polynomial terms.
    funext t
    have hdisp : y + t • v - x = a + t • v := by
      simp [a, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    rw [secondOrderTaylorModelAt_apply, secondOrderTaylorModelAt_apply, hdisp]
    simp [A, B, T, g, a, hcross, inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right, pow_two]
    ring
  rw [hpoly]
  have hlin : HasDerivAt (fun s : ℝ ↦ A * s) A 0 := by
    simpa using (HasDerivAt.const_mul A (hasDerivAt_id (0 : ℝ)))
  have hquad : HasDerivAt (fun s : ℝ ↦ (B / 2 : ℝ) * s ^ (2 : ℕ)) 0 0 := by
    -- The quadratic correction has zero derivative at the base parameter.
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using
      (HasDerivAt.const_mul (B / 2 : ℝ) ((hasDerivAt_id (0 : ℝ)).pow 2))
  -- Differentiate the scalar polynomial description at `0`.
  simpa [A, B, T, g, a, inner_add_left, add_assoc, add_left_comm, add_comm] using
    (HasDerivAt.const_add (secondOrderTaylorModelAt f x y) (hlin.add hquad))

/-- Helper for Lemma 4.2.5: along an affine line through `y`, the cubic penalty contributes the
directional derivative `((M / 2) * ‖y - x‖) * ⟪y - x, v⟫` at the base parameter `0`. -/
lemma cubic_penalty_line_hasDerivAt_zero
    {M : ℝ} {x y v : E} :
    HasDerivAt
      (fun t : ℝ ↦ (M / 6 : ℝ) * ‖(y + t • v) - x‖ ^ (3 : ℕ))
      ((((M / 2 : ℝ) * ‖y - x‖) * inner ℝ (y - x) v))
      0 := by
  have hthree : 1 < (3 : ℝ) := by
    norm_num
  have hexp : ((3 : ℝ) - 2) = 1 := by
    norm_num
  have hline : HasDerivAt (fun t : ℝ ↦ (y - x) + t • v) v 0 := by
    -- The norm-power derivative is composed with the affine line `t ↦ (y - x) + t v`.
    simpa [one_smul] using
      (HasDerivAt.const_add (y - x) ((hasDerivAt_id (0 : ℝ)).smul_const v))
  have hnorm :
      HasFDerivAt (fun z : E ↦ ‖z‖ ^ (3 : ℝ))
        ((3 * ‖y - x‖ ^ ((3 : ℝ) - 2)) • innerSL ℝ (y - x))
        ((y - x) + (0 : ℝ) • v) := by
    simpa [one_smul] using
      (hasFDerivAt_norm_rpow (y - x) hthree)
  have hraw :
      HasDerivAt (fun t : ℝ ↦ ‖(y - x) + t • v‖ ^ (3 : ℝ))
        (((3 : ℝ) * ‖y - x‖ ^ ((3 : ℝ) - 2)) * inner ℝ y v -
          (((3 : ℝ) * ‖y - x‖ ^ ((3 : ℝ) - 2)) * inner ℝ x v))
        0 := by
    simpa [Function.comp, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
      innerSL_apply_apply] using
      HasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) hnorm hline
  have hbase :
      HasDerivAt (fun t : ℝ ↦ ‖(y - x) + t • v‖ ^ (3 : ℝ))
        ((((3 : ℝ) * ‖y - x‖ ^ ((3 : ℝ) - 2))) * inner ℝ (y - x) v)
        0 := by
    -- Rewrite the raw scalar derivative through `inner (y - x) v`.
    convert hraw using 1
    rw [inner_sub_left]
    ring
  have hscaled :
      HasDerivAt (fun t : ℝ ↦ (M / 6 : ℝ) * ‖(y - x) + t • v‖ ^ (3 : ℝ))
        ((M / 6 : ℝ) * ((((3 : ℝ) * ‖y - x‖ ^ ((3 : ℝ) - 2))) * inner ℝ (y - x) v))
        0 := by
    -- Scale the norm-power derivative by the cubic coefficient `M / 6`.
    simpa [mul_comm] using (HasDerivAt.const_mul (M / 6 : ℝ) hbase)
  convert hscaled using 1
  · ext t
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  · rw [hexp, Real.rpow_one]
    ring

/-- Helper for Lemma 4.2.5: first-order optimality of a global minimizer of the cubic model
rewrites the linearized gradient as the negative cubic-penalty vector. -/
lemma linearized_gradient_eq_neg_cubic_penalty_of_isMinOn
    {f : E → ℝ} {L : NNReal} {M : ℝ} {x y : E}
    (hf : HessianLipschitzOn L Set.univ f)
    (hy : IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ y) :
    ∇ f x + hessian f x (y - x) = -((((M / 2 : ℝ) * ‖y - x‖) • (y - x))) := by
  apply ext_inner_right ℝ
  intro v
  have hlineMin :
      IsLocalMin
        (fun t : ℝ ↦ cubicRegularizationQuadraticApproximation f M x (y + t • v))
        0 :=
    cubic_model_line_isLocalMin_at_zero hy v
  have hquad :
      HasDerivAt
        (fun t : ℝ ↦ secondOrderTaylorModelAt f x (y + t • v))
        (inner ℝ (∇ f x + hessian f x (y - x)) v)
        0 :=
    quadratic_model_line_hasDerivAt_zero (hf.contDiffAt (by simp))
  have hpen :
      HasDerivAt
        (fun t : ℝ ↦ (M / 6 : ℝ) * ‖(y + t • v) - x‖ ^ (3 : ℕ))
        ((((M / 2 : ℝ) * ‖y - x‖) * inner ℝ (y - x) v))
        0 :=
    cubic_penalty_line_hasDerivAt_zero (M := M)
  have hmodel :
      HasDerivAt
        (fun t : ℝ ↦ cubicRegularizationQuadraticApproximation f M x (y + t • v))
        (inner ℝ (∇ f x + hessian f x (y - x)) v +
          (((M / 2 : ℝ) * ‖y - x‖) * inner ℝ (y - x) v))
        0 := by
    -- Differentiate the quadratic Taylor part and the cubic penalty separately on the line.
    simpa [cubicRegularizationQuadraticApproximation, inner_add_left] using hquad.add hpen
  have hzero :
      inner ℝ (∇ f x + hessian f x (y - x)) v +
        (((M / 2 : ℝ) * ‖y - x‖) * inner ℝ (y - x) v) = 0 :=
    hlineMin.hasDerivAt_eq_zero hmodel
  have hinner :
      inner ℝ (∇ f x + hessian f x (y - x)) v =
        -((((M / 2 : ℝ) * ‖y - x‖) * inner ℝ (y - x) v)) := by
    -- Fermat stationarity on the line slice gives the scalar optimality equation.
    rw [eq_neg_iff_add_eq_zero]
    exact hzero
  simpa [inner_smul_left] using hinner

/-- Helper for Lemma 4.2.5: the canonical cubic-step owner supplies the radius inequality
`2 ‖∇ f(T)‖ ≤ (L₃ + M) ‖T - x‖²`. -/
lemma cubic_step_radius_sq_lower_bound
    {f : E → ℝ} {L3 : NNReal} (hf : f ∈ C22[L3]) {x T : E} {M : ℝ}
    (hM : 2 * (L3 : ℝ) ≤ M)
    (hT : T ∈ argmin[Set.univ] (m[f; M](x))) :
    2 * ‖∇ f T‖ ≤ ((L3 : ℝ) + M) * ‖T - x‖ ^ (2 : ℕ) := by
  have hL3_nonneg : 0 ≤ (L3 : ℝ) := by
    exact_mod_cast L3.2
  have hM_nonneg : 0 ≤ M := by
    linarith
  have hf_univ : HessianLipschitzOn L3 Set.univ f :=
    hf.toHessianLipschitzOn isOpen_univ convex_univ
  have hgrad :
      ‖∇ f T‖ ≤ (((L3 : ℝ) + M) / 2) * ‖T - x‖ ^ (2 : ℕ) :=
    gradient_norm_le_of_isMinOn_cubicRegularizationQuadraticApproximation
      hf_univ
      hM_nonneg
      (mem_constrainedArgmin_iff.mp hT).2
      (by simp)
      (by simp)
  -- Clear the factor `1 / 2` to recover the source-facing radius condition.
  linarith

/-- Helper for Lemma 4.2.5: combining the cubic-step stationarity identity with the
Hessian-Lipschitz gradient remainder yields the regularized residual estimate. -/
lemma cubic_step_regularized_gradient_residual_le
    {f : E → ℝ} {L3 : NNReal} (hf : f ∈ C22[L3]) {x T : E} {M : ℝ}
    (hT : T ∈ argmin[Set.univ] (m[f; M](x))) :
    ‖∇ f T + ((M / 2 : ℝ) * ‖T - x‖) • (T - x)‖ ≤
      ((L3 : ℝ) / 2) * ‖T - x‖ ^ (2 : ℕ) := by
  have hlinearized :
      ∇ f x + hessian f x (T - x) =
        -(((M / 2 : ℝ) * ‖T - x‖) • (T - x)) := by
    have hf_univ : HessianLipschitzOn L3 Set.univ f :=
      hf.toHessianLipschitzOn isOpen_univ convex_univ
    exact
      linearized_gradient_eq_neg_cubic_penalty_of_isMinOn
        hf_univ
        (mem_constrainedArgmin_iff.mp hT).2
  have hdeviation :=
    HasLipschitzContinuousHessian.gradient_deviation_le hf x T
  -- Rewrite the Taylor remainder with the stationarity identity so the cubic term becomes explicit.
  calc
    ‖∇ f T + ((M / 2 : ℝ) * ‖T - x‖) • (T - x)‖
        = ‖∇ f T - (∇ f x + hessian f x (T - x))‖ := by
          rw [hlinearized]
          simp
    _ = ‖∇ f T - ∇ f x - hessian f x (T - x)‖ := by
          abel_nf
    _ ≤ ((L3 : ℝ) / 2) * ‖T - x‖ ^ (2 : ℕ) := hdeviation

/-- Helper for Lemma 4.2.5: the normalized scalar factor along the feasible ray `t ≥ 1` is at
least `1` once `M ≥ 2L`. -/
lemma cubic_pairing_scalar_factor_ge_one
    {L M t : ℝ}
    (hM : 0 < M)
    (hL : 0 ≤ L)
    (hLM : 2 * L ≤ M)
    (ht : 1 ≤ t) :
    ((L + M) / (2 * M)) / t + ((M - L) / (2 * M)) * t ^ (3 : ℕ) ≥ 1 := by
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hML_nonneg : 0 ≤ M - L := by
    nlinarith [hL, hLM]
  have hsum_ge_four : 4 ≤ t ^ (3 : ℕ) + t ^ (2 : ℕ) + t + 1 := by
    have ht2 : 1 ≤ t ^ (2 : ℕ) := one_le_pow₀ ht
    have ht3 : 1 ≤ t ^ (3 : ℕ) := one_le_pow₀ ht
    nlinarith
  have hbracket_nonneg :
      0 ≤ (M - L) * (t ^ (3 : ℕ) + t ^ (2 : ℕ) + t + 1) - 2 * M := by
    have hcoeff : 2 * M ≤ (M - L) * 4 := by
      nlinarith
    have hscale : (M - L) * 4 ≤ (M - L) * (t ^ (3 : ℕ) + t ^ (2 : ℕ) + t + 1) := by
      exact mul_le_mul_of_nonneg_left hsum_ge_four hML_nonneg
    linarith
  have hnum_nonneg :
      0 ≤ (M - L) * t ^ (4 : ℕ) - 2 * M * t + (L + M) := by
    have hfactor :
        (M - L) * t ^ (4 : ℕ) - 2 * M * t + (L + M) =
          (t - 1) * ((M - L) * (t ^ (3 : ℕ) + t ^ (2 : ℕ) + t + 1) - 2 * M) := by
      ring
    rw [hfactor]
    exact mul_nonneg (sub_nonneg.mpr ht) hbracket_nonneg
  have hrewrite :
      ((L + M) / (2 * M)) / t + ((M - L) / (2 * M)) * t ^ (3 : ℕ) - 1 =
        ((M - L) * t ^ (4 : ℕ) - 2 * M * t + (L + M)) / (2 * M * t) := by
    field_simp [hM.ne', ht_pos.ne']
    ring
  have hmain :
      0 ≤ ((L + M) / (2 * M)) / t + ((M - L) / (2 * M)) * t ^ (3 : ℕ) - 1 := by
    rw [hrewrite]
    exact div_nonneg hnum_nonneg (by positivity)
  linarith

/-- Helper for Lemma 4.2.5: the boundary expression `g √(2g / A)` is the same as the canonical
`√(2 / A) g^(3/2)` factor. -/
lemma gradient_norm_mul_sqrt_eq_sqrt_mul_rpow_threeHalves
    {g A : ℝ}
    (hg : 0 ≤ g)
    (hA : 0 < A) :
    g * Real.sqrt (2 * g / A) =
      Real.sqrt (2 / A) * Real.rpow g (3 / 2 : ℝ) := by
  by_cases hg0 : g = 0
  · simp [hg0]
  · have hg_pos : 0 < g := by
      exact lt_of_le_of_ne hg (by
        intro hg_zero
        exact hg0 hg_zero.symm)
    have hg32 : Real.rpow g (3 / 2 : ℝ) = g * Real.sqrt g := by
      calc
        Real.rpow g (3 / 2 : ℝ) = Real.rpow g ((1 : ℝ) + 1 / 2) := by
          norm_num
        _ = Real.rpow g (1 : ℝ) * Real.rpow g (1 / 2 : ℝ) := by
          simpa using (Real.rpow_add hg_pos (1 : ℝ) (1 / 2 : ℝ))
        _ = g * Real.sqrt g := by
          simp [Real.sqrt_eq_rpow]
    have hsqrt_mul :
        Real.sqrt (2 * g / A) = Real.sqrt (2 / A) * Real.sqrt g := by
      have h2A_nonneg : 0 ≤ 2 / A := by
        positivity
      calc
        Real.sqrt (2 * g / A) = Real.sqrt ((2 / A) * g) := by
          field_simp [hA.ne']
        _ = Real.sqrt (2 / A) * Real.sqrt g := by
          simpa [mul_comm] using (Real.sqrt_mul h2A_nonneg g)
    -- Once the square-root factor is split, only the `3 / 2`-power rewrite remains.
    rw [hg32, hsqrt_mul]
    ring

/-- Helper for Lemma 4.2.5: squaring the regularized residual bound isolates the pairing
numerator before any normalization by `M * ‖T - x‖`. -/
lemma pairing_numerator_lower_bound_from_squared_residual
    {gvec : E} {x T : E} {L M : ℝ}
    (hLM : 2 * L ≤ M)
    (hresid :
      ‖gvec + ((M / 2 : ℝ) * ‖T - x‖) • (T - x)‖ ≤
        (L / 2 : ℝ) * ‖T - x‖ ^ (2 : ℕ)) :
    M * ‖T - x‖ * inner ℝ gvec (x - T) ≥
      ‖gvec‖ ^ (2 : ℕ) + ((M ^ (2 : ℕ) - L ^ (2 : ℕ)) / 4) * ‖T - x‖ ^ (4 : ℕ) := by
  have hrhs_nonneg : 0 ≤ (L / 2 : ℝ) * ‖T - x‖ ^ (2 : ℕ) := by
    exact le_trans (norm_nonneg _) hresid
  have hsq :
      ‖gvec + ((M / 2 : ℝ) * ‖T - x‖) • (T - x)‖ ^ (2 : ℕ) ≤
        ((L / 2 : ℝ) * ‖T - x‖ ^ (2 : ℕ)) ^ (2 : ℕ) := by
    -- Squaring is legitimate because both sides of the residual estimate are nonnegative.
    exact (sq_le_sq₀ (norm_nonneg _) hrhs_nonneg).2 hresid
  have hexpand :
      ‖gvec + ((M / 2 : ℝ) * ‖T - x‖) • (T - x)‖ ^ (2 : ℕ) =
        ‖gvec‖ ^ (2 : ℕ) + M * ‖T - x‖ * inner ℝ gvec (T - x) +
          (M ^ (2 : ℕ) / 4) * ‖T - x‖ ^ (4 : ℕ) := by
    -- Expand the norm square and collect the cubic-step cross term into a single pairing.
    rw [norm_add_sq_real]
    simp [pow_two, real_inner_smul_right, norm_smul]
    have habs : |M| ^ (2 : ℕ) = M ^ (2 : ℕ) := by
      simpa [pow_two] using (sq_abs M)
    ring_nf
    rw [habs]
    ring
  have hrhs_sq :
      ((L / 2 : ℝ) * ‖T - x‖ ^ (2 : ℕ)) ^ (2 : ℕ) =
        (L ^ (2 : ℕ) / 4) * ‖T - x‖ ^ (4 : ℕ) := by
    ring_nf
  have hbound :
      ‖gvec‖ ^ (2 : ℕ) + M * ‖T - x‖ * inner ℝ gvec (T - x) +
          (M ^ (2 : ℕ) / 4) * ‖T - x‖ ^ (4 : ℕ) ≤
        (L ^ (2 : ℕ) / 4) * ‖T - x‖ ^ (4 : ℕ) := by
    -- After rewriting both squares, the residual estimate becomes a scalar quartic inequality.
    rw [hexpand, hrhs_sq] at hsq
    exact hsq
  have hpair :
      inner ℝ gvec (T - x) = -inner ℝ gvec (x - T) := by
    -- Rewrite the cross term so the target pairing `⟪gvec, x - T⟫` appears with a positive sign.
    have hsub : T - x = -(x - T) := by
      abel_nf
    rw [hsub, inner_neg_right]
  have hbound' :
      ‖gvec‖ ^ (2 : ℕ) - M * ‖T - x‖ * inner ℝ gvec (x - T) +
          (M ^ (2 : ℕ) / 4) * ‖T - x‖ ^ (4 : ℕ) ≤
        (L ^ (2 : ℕ) / 4) * ‖T - x‖ ^ (4 : ℕ) := by
    simpa [hpair] using hbound
  nlinarith [hbound']

/-- Helper for Lemma 4.2.5: once the numerator inequality is known, the boundary normalization
`r = t * √(2g / (L + M))` converts it into the claimed `g^(3/2)` lower bound. -/
lemma normalized_pairing_boundary_lower_bound
    {g r p L M : ℝ}
    (hg : 0 < g)
    (hr : 0 ≤ r)
    (hL : 0 ≤ L)
    (hLM : 2 * L ≤ M)
    (hrad : 2 * g ≤ (L + M) * r ^ (2 : ℕ))
    (hnum :
      M * r * p ≥
        g ^ (2 : ℕ) + ((M ^ (2 : ℕ) - L ^ (2 : ℕ)) / 4) * r ^ (4 : ℕ)) :
    p ≥ Real.sqrt (2 / (L + M)) * Real.rpow g (3 / 2 : ℝ) := by
  have hA_pos : 0 < L + M := by
    by_contra hA_nonpos
    have hAr_nonpos : (L + M) * r ^ (2 : ℕ) ≤ 0 := by
      nlinarith [sq_nonneg r, hA_nonpos]
    linarith
  have hM_pos : 0 < M := by
    by_contra hM_nonpos
    have hA_nonpos : L + M ≤ 0 := by
      linarith
    linarith
  have hr_pos : 0 < r := by
    -- The radius cannot vanish because the boundary inequality forces a positive right-hand side.
    have hr_ne : r ≠ 0 := by
      intro hr_zero
      have : 2 * g ≤ 0 := by
        simpa [hr_zero] using hrad
      linarith
    exact lt_of_le_of_ne hr hr_ne.symm
  let s : ℝ := Real.sqrt (2 * g / (L + M))
  let t : ℝ := r / s
  have hs_pos : 0 < s := by
    -- The boundary scale is positive because `g > 0` and `L + M > 0`.
    dsimp [s]
    apply Real.sqrt_pos.2
    positivity
  have hs_sq :
      s ^ (2 : ℕ) = 2 * g / (L + M) := by
    -- Record the defining square of the boundary scale for later algebraic normalization.
    dsimp [s]
    simpa [pow_two] using (Real.sq_sqrt <| show 0 ≤ 2 * g / (L + M) by positivity)
  have hs_sq_le :
      s ^ (2 : ℕ) ≤ r ^ (2 : ℕ) := by
    rw [hs_sq]
    exact (div_le_iff₀ hA_pos).2 <| by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hrad
  have hs_le_r : s ≤ r := by
    -- Comparing the boundary squares shows the actual radius lies on the feasible ray `t ≥ 1`.
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) hr).mp <| by
      simpa [pow_two] using hs_sq_le
  have ht : 1 ≤ t := by
    -- Divide by the positive boundary scale to obtain the normalized feasible parameter.
    have hdiv : s / s ≤ r / s := div_le_div_of_nonneg_right hs_le_r hs_pos.le
    simpa [t, hs_pos.ne'] using hdiv
  have hscalar :
      (g ^ (2 : ℕ) + ((M ^ (2 : ℕ) - L ^ (2 : ℕ)) / 4) * r ^ (4 : ℕ)) / (M * r) ≤ p := by
    -- The numerator estimate is now ready to be divided by the positive factor `M * r`.
    exact (div_le_iff₀ (mul_pos hM_pos hr_pos)).2 <| by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hnum
  have hs_factor :
      s ^ (2 : ℕ) * (L + M) / 2 = g := by
    -- Repackage `s² = 2g / (L + M)` into the boundary-scale identity used in the scalar algebra.
    have hs_sq' := hs_sq
    field_simp [hA_pos.ne'] at hs_sq'
    linarith
  have hg_div_sq :
      g / s ^ (2 : ℕ) = (L + M) / 2 := by
    -- Dividing the boundary identity by `s²` gives the coefficient needed in the quartic term.
    apply (div_eq_iff (pow_ne_zero 2 hs_pos.ne')).2
    calc
      g = s ^ (2 : ℕ) * (L + M) / 2 := by
            simpa using hs_factor.symm
      _ = ((L + M) / 2) * s ^ (2 : ℕ) := by ring
  have hfirst_term :
      g * s * (((L + M) / (2 * M)) / t) = g ^ (2 : ℕ) / (M * r) := by
    -- The first normalized term is exactly the `g² / (M r)` contribution.
    calc
      g * s * (((L + M) / (2 * M)) / t)
          = g * (s ^ (2 : ℕ) * (L + M) / 2) / (M * r) := by
              dsimp [t]
              field_simp [hM_pos.ne', hr_pos.ne', hs_pos.ne']
      _ = g * g / (M * r) := by rw [hs_factor]
      _ = g ^ (2 : ℕ) / (M * r) := by ring
  have hsecond_term :
      g * s * (((M - L) / (2 * M)) * t ^ (3 : ℕ)) =
        (((M ^ (2 : ℕ) - L ^ (2 : ℕ)) / 4) * r ^ (4 : ℕ)) / (M * r) := by
    -- The cubic normalized term is the quartic numerator contribution divided by `M r`.
    calc
      g * s * (((M - L) / (2 * M)) * t ^ (3 : ℕ))
          = (g / s ^ (2 : ℕ)) * ((M - L) / (2 * M)) * r ^ (3 : ℕ) := by
              dsimp [t]
              field_simp [pow_two, hM_pos.ne', hs_pos.ne']
      _ = ((L + M) / 2) * ((M - L) / (2 * M)) * r ^ (3 : ℕ) := by
            rw [hg_div_sq]
      _ = (((M ^ (2 : ℕ) - L ^ (2 : ℕ)) / 4) * r ^ (4 : ℕ)) / (M * r) := by
            field_simp [hM_pos.ne', hr_pos.ne']
            ring
  have hfactor :
      (g ^ (2 : ℕ) + ((M ^ (2 : ℕ) - L ^ (2 : ℕ)) / 4) * r ^ (4 : ℕ)) / (M * r) =
        g * s * (((L + M) / (2 * M)) / t + ((M - L) / (2 * M)) * t ^ (3 : ℕ)) := by
    -- Rewrite the divided numerator in terms of the normalized ray parameter `t = r / s`.
    calc
      (g ^ (2 : ℕ) + ((M ^ (2 : ℕ) - L ^ (2 : ℕ)) / 4) * r ^ (4 : ℕ)) / (M * r)
          = g ^ (2 : ℕ) / (M * r) +
              (((M ^ (2 : ℕ) - L ^ (2 : ℕ)) / 4) * r ^ (4 : ℕ)) / (M * r) := by
                field_simp [hM_pos.ne', hr_pos.ne']
      _ = g * s * (((L + M) / (2 * M)) / t) +
            g * s * (((M - L) / (2 * M)) * t ^ (3 : ℕ)) := by
              rw [hfirst_term, hsecond_term]
      _ = g * s * (((L + M) / (2 * M)) / t + ((M - L) / (2 * M)) * t ^ (3 : ℕ)) := by
              ring
  have hbracket :
      1 ≤ ((L + M) / (2 * M)) / t + ((M - L) / (2 * M)) * t ^ (3 : ℕ) := by
    -- The one-variable scalar factor is monotone along the feasible ray `t ≥ 1`.
    exact cubic_pairing_scalar_factor_ge_one hM_pos hL hLM ht
  have hgs_le_p : g * s ≤ p := by
    -- Separate the boundary factor `g * s` from the normalized scalar bracket and bound the latter by `1`.
    calc
      g * s = g * s * 1 := by ring
      _ ≤ g * s * (((L + M) / (2 * M)) / t + ((M - L) / (2 * M)) * t ^ (3 : ℕ)) := by
            exact mul_le_mul_of_nonneg_left hbracket (by positivity)
      _ = (g ^ (2 : ℕ) + ((M ^ (2 : ℕ) - L ^ (2 : ℕ)) / 4) * r ^ (4 : ℕ)) / (M * r) := by
            rw [hfactor]
      _ ≤ p := hscalar
  -- The already-proved `rpow` identity turns the boundary factor into the source expression.
  calc
    p ≥ g * s := hgs_le_p
    _ = Real.sqrt (2 / (L + M)) * Real.rpow g (3 / 2 : ℝ) := by
          simpa [s] using
            gradient_norm_mul_sqrt_eq_sqrt_mul_rpow_threeHalves
              (g := g)
              (A := L + M)
              hg.le
              hA_pos

/-- Helper for Lemma 4.2.5: the radius lower bound and the regularized residual estimate imply
the source-facing pairing lower bound. -/
lemma pairing_lower_bound_from_radius_and_residual
    {gvec : E} {x T : E} {L M : ℝ}
    (hL : 0 ≤ L)
    (hLM : 2 * L ≤ M)
    (hrad : 2 * ‖gvec‖ ≤ (L + M) * ‖T - x‖ ^ (2 : ℕ))
    (hresid :
      ‖gvec + ((M / 2 : ℝ) * ‖T - x‖) • (T - x)‖ ≤
        (L / 2 : ℝ) * ‖T - x‖ ^ (2 : ℕ)) :
    inner ℝ gvec (x - T) ≥
      Real.sqrt (2 / (L + M)) * Real.rpow ‖gvec‖ (3 / 2 : ℝ) := by
  -- Route correction: separate the vector norm-square expansion from the scalar boundary
  -- normalization instead of keeping the whole closing argument in one proof block.
  by_cases hg0 : ‖gvec‖ = 0
  · -- Vanishing gradient norm forces the pairing and the target lower bound to be zero.
    have hgvec_zero : gvec = 0 := norm_eq_zero.mp hg0
    simp [hgvec_zero]
  · have hg_pos : 0 < ‖gvec‖ := by
      exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hg0)
    have hnum :
        M * ‖T - x‖ * inner ℝ gvec (x - T) ≥
          ‖gvec‖ ^ (2 : ℕ) + ((M ^ (2 : ℕ) - L ^ (2 : ℕ)) / 4) * ‖T - x‖ ^ (4 : ℕ) :=
      pairing_numerator_lower_bound_from_squared_residual
        (x := x)
        (T := T)
        (L := L)
        (M := M)
        hLM
        hresid
    -- Feed the vector-side numerator estimate into the scalar boundary lemma.
    exact
      normalized_pairing_boundary_lower_bound
        (g := ‖gvec‖)
        (r := ‖T - x‖)
        (p := inner ℝ gvec (x - T))
        hg_pos
        (norm_nonneg _)
        hL
        hLM
        hrad
        hnum

/-- Lemma 4.2.5: if `f ∈ C22[L₃]`, if `T` belongs to the canonical cubic-regularization step set
`argmin[Set.univ] (m[f; M](x))`, and if `2 L₃ ≤ M`, then
`⟪∇ f(T), x - T⟫ ≥ √(2 / (L₃ + M)) ‖∇ f(T)‖^(3 / 2)`. -/
theorem cubicRegularization_gradientPairing_ge_sqrt_mul_gradientNorm_rpow_threeHalves
    {f : E → ℝ} {L3 : NNReal} (hf : f ∈ C22[L3]) {x T : E} {M : ℝ}
    (hM : 2 * (L3 : ℝ) ≤ M)
    (hT : T ∈ argmin[Set.univ] (m[f; M](x))) :
    inner ℝ (∇ f T) (x - T) ≥
      Real.sqrt (2 / ((L3 : ℝ) + M)) * Real.rpow ‖∇ f T‖ (3 / 2 : ℝ) := by
  have hL3_nonneg : 0 ≤ (L3 : ℝ) := by
    exact_mod_cast L3.2
  have hradius :=
    cubic_step_radius_sq_lower_bound hf hM hT
  have hresidual :=
    cubic_step_regularized_gradient_residual_le hf hT
  -- The main theorem is exactly the source pairing bound extracted from the owner radius and
  -- residual inequalities proved above.
  exact pairing_lower_bound_from_radius_and_residual
    (gvec := ∇ f T)
    (x := x)
    (T := T)
    (L := (L3 : ℝ))
    (M := M)
    hL3_nonneg
    hM
    hradius
    hresidual
