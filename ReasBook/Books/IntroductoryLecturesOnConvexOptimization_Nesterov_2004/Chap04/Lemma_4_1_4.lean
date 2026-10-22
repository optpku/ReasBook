/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_4_19
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Lemma_4_1_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Lemma 4.1.4 lies in the Chapter 4 cubic-regularization / Hessian-Lipschitz domain on
complete real inner-product spaces.

Sampled owner declarations:
* `HessianLipschitzOn` in `Definition_4_1_2`, the chapter owner for local `C²` Hessian-
  Lipschitz control on an open convex set;
* `HessianLipschitzOn.gradient_deviation_le` in `Lemma_4_1_1`, the localized gradient Taylor
  remainder bound supplied by that owner;
* `cubicRegularizationQuadraticApproximation` in `Definition_4_1_3`, the chapter owner of the
  cubic model centered at `x`;
* `IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ y`, the canonical global
  minimizer interface for the cubic model.

Source/core/bridge triage:
* source-facing: the gradient bound for a cubic-model minimizer `T_M(x)`;
* core/canonical: `HessianLipschitzOn L 𝓕 f` together with
  `IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ y`;
* bridge/view: downstream specialization from the owner-level minimizer statement to a chosen
  step map `y = T_M(x)`.

Owner abstraction:
* keep the cubic-model minimizer relation as the public owner abstraction on the intrinsic ambient
  space `E`;
* derive the estimate from the localized gradient-deviation owner
  `HessianLipschitzOn.gradient_deviation_le`, rather than through a downstream residual wrapper.

Primitive data:
* the objective `f : E → ℝ`;
* the regularization parameter `M`;
* the base point `x`;
* the minimizer `y`;
* the owner hypotheses
  `HessianLipschitzOn L 𝓕 f` and
  `IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ y`.

Derived API:
* the norm bound for `∇ f y`;
* downstream step-map reformulations obtained by instantiating the same `IsMinOn` owner at a
  chosen trial-point map.

This removes the conflicting local owner `cubicRegularizationTrialPoint`, reuses the existing
cubic-model minimizer interface from `Definition_4_1_3` directly, and depends only on the direct
upstream gradient-remainder ingredient `Lemma_4_1_1` instead of reaching it through the
downstream residual file `Lemma_4_1_5`. -/

-- Proof sketch: use the first-order optimality equation satisfied by a global minimizer `y` of
-- `cubicRegularizationQuadraticApproximation f M x` to rewrite the linearized gradient at `y`,
-- then combine that identity with the gradient Taylor remainder estimate on `𝓕`; only the
-- nonnegativity `0 ≤ M` of the cubic coefficient is needed in the final estimate.
/-- Helper for Lemma 4.1.4: restricting the cubic model to an affine line through a global
minimizer preserves local minimality at the line parameter `0`. -/
private theorem cubic_model_line_isLocalMin_at_zero
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

/-- Helper for Lemma 4.1.4: along an affine line through `y`, the quadratic Taylor model centered
at `x` has derivative `⟪∇ f x + ∇² f(x)(y - x), v⟫` at the line parameter `0`. -/
private theorem quadratic_model_line_hasDerivAt_zero
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

/-- Helper for Lemma 4.1.4: along an affine line through `y`, the cubic penalty contributes the
directional derivative `((M / 2) * ‖y - x‖) * ⟪y - x, v⟫` at the base parameter `0`. -/
private theorem cubic_penalty_line_hasDerivAt_zero
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

/-- Helper for Lemma 4.1.4: first-order optimality of a global minimizer of the cubic model
rewrites the linearized gradient as the negative cubic-penalty vector. -/
private theorem linearized_gradient_eq_neg_cubic_penalty_of_isMinOn
    {f : E → ℝ} {𝓕 : Set E} {L : NNReal} {M : ℝ} {x y : E}
    (hf : HessianLipschitzOn L 𝓕 f)
    (hy : IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ y)
    (hx : x ∈ 𝓕) :
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
    quadratic_model_line_hasDerivAt_zero (hf.contDiffAt hx)
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

/-- Lemma 4.1.4: if `f` has `L`-Lipschitz Hessian on `𝓕`, and `y` globally minimizes the cubic
model centered at `x` with parameter `M`, then `‖∇ f y‖ ≤ ((L + M) / 2) ‖y - x‖²`. -/
theorem gradient_norm_le_of_isMinOn_cubicRegularizationQuadraticApproximation
    {f : E → ℝ} {𝓕 : Set E} {L : NNReal} {M : ℝ} {x y : E}
    (hf : HessianLipschitzOn L 𝓕 f)
    (hM : 0 ≤ M)
    (hy :
      IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ y)
    (hx : x ∈ 𝓕)
    (hy𝓕 : y ∈ 𝓕) :
    ‖∇ f y‖ ≤ (((L : ℝ) + M) / 2) * ‖y - x‖ ^ (2 : ℕ) := by
  let d : E := y - x
  let cubicVector : E := (((M / 2 : ℝ) * ‖d‖) • d)
  have hlinearized :
      ∇ f x + hessian f x d = -cubicVector := by
    -- The minimizer stationarity identity is obtained from the line-slice derivative formula.
    simpa [d, cubicVector] using
      linearized_gradient_eq_neg_cubic_penalty_of_isMinOn hf hy hx
  have hdeviation :
      ‖∇ f y - ∇ f x - hessian f x d‖ ≤ ((L : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) := by
    -- This is exactly the localized gradient Taylor remainder from Lemma 4.1.1.
    simpa [d] using hf.gradient_deviation_le x y hx hy𝓕
  have hMhalf_nonneg : 0 ≤ (M / 2 : ℝ) := by
    linarith
  have hcubic_nonneg : 0 ≤ ((M / 2 : ℝ) * ‖d‖) := by
    exact mul_nonneg hMhalf_nonneg (norm_nonneg d)
  have hcubic_norm : ‖cubicVector‖ = (M / 2 : ℝ) * ‖d‖ ^ (2 : ℕ) := by
    -- The cubic penalty vector has norm `(M / 2) * ‖d‖²` because `M ≥ 0`.
    calc
      ‖cubicVector‖ = ‖((M / 2 : ℝ) * ‖d‖)‖ * ‖d‖ := by
        simp [cubicVector, norm_smul]
      _ = ((M / 2 : ℝ) * ‖d‖) * ‖d‖ := by
        rw [Real.norm_of_nonneg hcubic_nonneg]
      _ = (M / 2 : ℝ) * ‖d‖ ^ (2 : ℕ) := by
        ring
  have hrepack :
      ∇ f y = (∇ f y - ∇ f x - hessian f x d) - cubicVector := by
    -- Substitute the stationarity identity into the gradient at `y`.
    calc
      ∇ f y = (∇ f y - (∇ f x + hessian f x d)) - cubicVector := by
        rw [hlinearized]
        abel_nf
      _ = (∇ f y - ∇ f x - hessian f x d) - cubicVector := by
        abel_nf
  -- Apply the triangle inequality after isolating the Taylor remainder and cubic vector terms.
  calc
    ‖∇ f y‖ = ‖(∇ f y - ∇ f x - hessian f x d) - cubicVector‖ := by
      rw [← hrepack]
    _ ≤ ‖∇ f y - ∇ f x - hessian f x d‖ + ‖cubicVector‖ := norm_sub_le _ _
    _ ≤ ((L : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) + ‖cubicVector‖ := by
      exact add_le_add hdeviation le_rfl
    _ = ((L : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) + (M / 2 : ℝ) * ‖d‖ ^ (2 : ℕ) := by
      rw [hcubic_norm]
    _ = (((L : ℝ) + M) / 2) * ‖d‖ ^ (2 : ℕ) := by
      ring
