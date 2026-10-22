/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_16
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.FirstOrderTaylorModel
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_17
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Example_2_1_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Proposition_2_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient StrongConvexSmooth

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Proposition 2.6 belongs to smooth strongly convex quadratic optimization on a real Hilbert
space.

Relevant owner-style declarations sampled in this domain:
* `hessian` in `Chap01/Definition_1_4_16`, the intrinsic second-order operator owner;
* `quadraticallyRegularizedObjective` in `Chap01/FirstOrderTaylorModel`, the canonical owner for
  the centered `(\delta / 2) \|x - x_0\|^2` term;
* `IsStrongConvexSmoothObjective` and `𝓢[μ, L]¹¹` in `Chap02/Definition_2_17`, the chapter owner
  predicate and its source-facing notation;
* the finite-dimensional analogue `quadraticObjective_mem_S11` in
  `Chap02/Proposition_2_4`.

Source/core/bridge triage:
* source-facing: the quadratic objective `f_{μ,Q_f}` and its membership in `𝓢[μ, μ Q_f]¹¹`;
* core/canonical: the bounded self-adjoint operator `A : E →L[ℝ] E`, the Hessian operator
  `hessian f x`, and `IsStrongConvexSmoothObjective μ L f`;
* bridge/view: the constant Hessian formula and its Loewner lower and upper bounds.

Primitive data:
* the scalar parameters `μ`, `Q_f`;
* the bounded operator `A : E →L[ℝ] E`.

Derived API:
* the pointwise formula for `f_{μ,Q_f}`, obtained by quadratic regularization of the operator
  quadratic form at the origin;
* twice Fréchet differentiability, the constant Hessian formula, and the Loewner Hessian bounds;
* the source-facing membership statement in `𝓢[μ, μ Q_f]¹¹`.
-/

local notation "I" => ContinuousLinearMap.id ℝ E

/-- The quadratic objective `f_{μ,Q_f}` attached to a bounded operator on a real Hilbert space. -/
def nesterovQuadraticObjective (μ Q_f : ℝ) (A : E →L[ℝ] E) : E → ℝ :=
  quadraticallyRegularizedObjective
    (fun x ↦ μ * (Q_f - 1) / 8 * inner ℝ x (A x))
    μ
    (0 : E)

variable {μ Q_f : ℝ} {A : E →L[ℝ] E}

/-- Evaluating the quadratic objective expands to its defining formula. -/
@[simp] theorem nesterovQuadraticObjective_apply (x : E) :
    nesterovQuadraticObjective μ Q_f A x =
      μ * (Q_f - 1) / 8 * inner ℝ x (A x) + μ / 2 * ‖x‖ ^ (2 : ℕ) :=
  by simp [nesterovQuadraticObjective, quadraticallyRegularizedObjective]

variable [CompleteSpace E]

/-- Helper for Proposition 2.6: the gradient of the operator quadratic objective is the affine
map with linear part `((μ (Q_f - 1)) / 8) (A + A†)` and regularizing term `μ I`. -/
theorem nesterovQuadraticObjective_gradient_eq :
    ∇ (nesterovQuadraticObjective μ Q_f A) =
      fun x ↦ ((((μ * (Q_f - 1)) / 8) • (A + A.adjoint)) + μ • I) x := by
  -- Differentiate the quadratic core and the squared-norm regularizer separately.
  have hgradAt :
      ∀ x : E,
        HasGradientAt (nesterovQuadraticObjective μ Q_f A)
          (((μ * (Q_f - 1) / 8) • ((A + A.adjoint) x)) + μ • x) x := by
    intro x
    have htoDual_innerSL (z : E) : (InnerProductSpace.toDual ℝ E).symm ((innerSL ℝ) z) = z := by
      apply ext_inner_right ℝ
      intro y
      simp [InnerProductSpace.toDual_symm_apply]
    have htoDual_toDual (z : E) :
        (InnerProductSpace.toDual ℝ E).symm ((InnerProductSpace.toDual ℝ E) z) = z := by
      apply ext_inner_right ℝ
      intro y
      simp
    have hcore0 :
        HasFDerivAt (fun y : E ↦ inner ℝ y (A y))
          (innerSL ℝ ((A + A.adjoint) x)) x := by
      have hcoreCLM :
          ((fderivInnerCLM ℝ (x, A x)).comp ((1 : E →L[ℝ] E).prod A)) =
            innerSL ℝ ((A + A.adjoint) x) := by
        ext y
        calc
          ((fderivInnerCLM ℝ (x, A x)).comp ((1 : E →L[ℝ] E).prod A)) y
              = inner ℝ x (A y) + inner ℝ y (A x) := by
                  simp [fderivInnerCLM_apply]
          _ = inner ℝ y (A.adjoint x) + inner ℝ y (A x) := by
                have hAdj : inner ℝ x (A y) = inner ℝ y (A.adjoint x) := by
                  calc
                    inner ℝ x (A y) = inner ℝ (A y) x := by rw [real_inner_comm]
                    _ = inner ℝ y (A.adjoint x) := by rw [A.adjoint_inner_right]
                rw [hAdj]
          _ = inner ℝ y (A x + A.adjoint x) := by
                simpa [add_comm] using (inner_add_right y (A x) (A.adjoint x)).symm
          _ = innerSL ℝ ((A + A.adjoint) x) y := by
                simp [innerSL_apply_apply, real_inner_comm, inner_add_right]
      exact hcoreCLM ▸ ((hasFDerivAt_id x).inner ℝ A.hasFDerivAt)
    have hcore :
        HasGradientAt (fun y : E ↦ μ * (Q_f - 1) / 8 * inner ℝ y (A y))
          ((μ * (Q_f - 1) / 8) • ((A + A.adjoint) x)) x := by
      have hsmul :
          HasFDerivAt (fun y : E ↦ μ * (Q_f - 1) / 8 * inner ℝ y (A y))
            (((μ * (Q_f - 1) / 8) • innerSL ℝ ((A + A.adjoint) x)) : E →L[ℝ] ℝ) x := by
        simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
          hcore0.const_smul (μ * (Q_f - 1) / 8)
      simpa [htoDual_innerSL, add_comm, add_left_comm, add_assoc] using hsmul.hasGradientAt
    have hnormSq :
        HasFDerivAt (fun y : E ↦ ‖y‖ ^ (2 : ℕ)) (2 • innerSL ℝ x) x := by
      simpa using (hasStrictFDerivAt_norm_sq x).hasFDerivAt
    have hreg :
        HasGradientAt (fun y : E ↦ (μ / 2) * ‖y‖ ^ (2 : ℕ)) (μ • x) x := by
      have hsmul :
          HasFDerivAt (fun y : E ↦ (μ / 2) * ‖y‖ ^ (2 : ℕ))
            ((μ / 2) • (2 • innerSL ℝ x)) x := by
        simpa [smul_eq_mul] using hnormSq.const_smul (μ / 2)
      have hlin :
          ((μ / 2) • (2 • innerSL ℝ x)) = InnerProductSpace.toDual ℝ E (μ • x) := by
        ext y
        simp [InnerProductSpace.toDual_apply_apply, two_smul]
        ring
      exact (htoDual_toDual (μ • x)) ▸ (hlin ▸ hsmul).hasGradientAt
    have hsum :
        HasGradientAt
          (fun y : E ↦
            μ * (Q_f - 1) / 8 * inner ℝ y (A y) + (μ / 2) * ‖y‖ ^ (2 : ℕ))
          (((μ * (Q_f - 1) / 8) • ((A + A.adjoint) x)) + μ • x) x := by
      simpa [add_assoc, add_left_comm, add_comm]
        using (hcore.hasFDerivAt.add hreg.hasFDerivAt).hasGradientAt
    convert hsum using 1
    funext y
    rw [nesterovQuadraticObjective_apply]
  calc
    ∇ (nesterovQuadraticObjective μ Q_f A)
        = fun x ↦ ((μ * (Q_f - 1) / 8) • ((A + A.adjoint) x)) + μ • x :=
            gradient_eq hgradAt
    _ = fun x ↦ ((((μ * (Q_f - 1)) / 8) • (A + A.adjoint)) + μ • I) x := by
          funext x
          simp [ContinuousLinearMap.add_apply]

/-- The quadratic objective is twice Fréchet differentiable, equivalently its gradient is
Fréchet differentiable on the whole Hilbert space. -/
-- Proof sketch: differentiate the quadratic form `x ↦ inner ℝ x (A x)` and the norm-square term
-- separately; both contributions are polynomial in `x`, so the gradient is differentiable
-- everywhere.
theorem nesterovQuadraticObjective_twiceDifferentiable :
    Differentiable ℝ (∇ (nesterovQuadraticObjective μ Q_f A)) := by
  -- The explicit gradient formula is a continuous linear map, hence differentiable everywhere.
  rw [nesterovQuadraticObjective_gradient_eq]
  exact ((((μ * (Q_f - 1) / 8) • (A + A.adjoint)) + μ • I) : E →L[ℝ] E).differentiable

/-- When `A` is self-adjoint, the Hessian of the quadratic objective is the constant operator
`((μ (Q_f - 1)) / 4) A + μ I`. -/
-- Proof sketch: differentiate the quadratic form `x ↦ inner ℝ x (A x)` once, use
-- self-adjointness to identify the adjoint contribution with `A`, and differentiate the
-- norm-square term to obtain the `μ I` summand.
theorem nesterovQuadraticObjective_hessian_eq (hA : IsSelfAdjoint A) (x : E) :
    hessian (nesterovQuadraticObjective μ Q_f A) x =
      ((μ * (Q_f - 1) / 4) • A) + μ • I := by
  -- Rewrite the gradient as a linear map and read off its derivative.
  let B : E →L[ℝ] E := (((μ * (Q_f - 1) / 8) • (A + A.adjoint)) + μ • I)
  have hB :
      HasFDerivAt (∇ (nesterovQuadraticObjective μ Q_f A)) B x := by
    simpa [B, nesterovQuadraticObjective_gradient_eq] using B.hasFDerivAt
  have hcollapse : B = ((μ * (Q_f - 1) / 4) • A) + μ • I := by
    have hsum : A + A.adjoint = (2 : ℝ) • A := by
      simp [hA.adjoint_eq, two_smul]
    calc
      B = (((μ * (Q_f - 1) / 8) • ((2 : ℝ) • A)) + μ • I) := by
            unfold B
            rw [hsum]
      _ = ((((μ * (Q_f - 1) / 8) * 2) • A) + μ • I) := by
            rw [smul_smul]
      _ = ((μ * (Q_f - 1) / 4) • A) + μ • I := by
            congr 1
            ring
  simpa [hessian, hcollapse] using hB.fderiv

/-- Under the Loewner assumptions `0 ≤ A` and `1 ≤ Q_f`, the Hessian is bounded below by
`μ I`. -/
-- Proof sketch: combine the constant Hessian formula with `0 ≤ A` and `1 ≤ Q_f` to see that the
-- perturbation term `((μ (Q_f - 1)) / 4) • A` is positive semidefinite, then add `μ I`.
theorem nesterovQuadraticObjective_hessian_lower_bound
    (hμ : 0 ≤ μ) (hQf : 1 ≤ Q_f) (hA_nonneg : 0 ≤ A) (x : E) :
    μ • I ≤ hessian (nesterovQuadraticObjective μ Q_f A) x := by
  -- Positivity of `A` makes the scaled perturbation term positive semidefinite.
  have hA_pos : A.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive A).mp hA_nonneg
  have hA_self : IsSelfAdjoint A := by
    rw [ContinuousLinearMap.isPositive_iff'] at hA_pos
    exact hA_pos.1
  have hcoeff : 0 ≤ μ * (Q_f - 1) / 4 := by
    nlinarith
  rw [nesterovQuadraticObjective_hessian_eq hA_self x, ContinuousLinearMap.le_def]
  simpa using hA_pos.smul_of_nonneg hcoeff

/-- Under the Loewner assumption `A ≤ 4 I`, the Hessian is bounded above by `(μ Q_f) I`. -/
-- Proof sketch: rewrite the Hessian by `nesterovQuadraticObjective_hessian_eq`, use
-- `hA_le : A ≤ 4 I` to bound the perturbation term by `μ (Q_f - 1) I`, and simplify the scalar
-- factor to obtain the upper bound `(μ Q_f) I`.
theorem nesterovQuadraticObjective_hessian_upper_bound
    (hμ : 0 ≤ μ) (hQf : 1 ≤ Q_f)
    (hA_le : A ≤ (4 : ℝ) • I) (x : E) :
    hessian (nesterovQuadraticObjective μ Q_f A) x ≤ (μ * Q_f) • I := by
  -- Rewrite the gap to the upper bound as a nonnegative scalar multiple of `4 I - A`.
  have hshift_pos : (((4 : ℝ) • I) - A).IsPositive := by
    simpa [ContinuousLinearMap.le_def] using hA_le
  have hshift_self : IsSelfAdjoint (((4 : ℝ) • I) - A) := by
    rw [ContinuousLinearMap.isPositive_iff'] at hshift_pos
    exact hshift_pos.1
  have hI_self : IsSelfAdjoint ((4 : ℝ) • I : E →L[ℝ] E) := by
    have hpos : (((4 : ℝ) • (I : E →L[ℝ] E)) : E →L[ℝ] E).IsPositive :=
      ContinuousLinearMap.isPositive_one.smul_of_nonneg (show 0 ≤ (4 : ℝ) by norm_num)
    rw [ContinuousLinearMap.isPositive_iff'] at hpos
    exact hpos.1
  have hA_self : IsSelfAdjoint A := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hI_self.sub hshift_self
  have hcoeff : 0 ≤ μ * (Q_f - 1) / 4 := by
    nlinarith
  have hshift_scaled :
      (((μ * Q_f) • I) - (((μ * (Q_f - 1) / 4) • A) + μ • I)).IsPositive := by
    have hbase :
        (((μ * (Q_f - 1) / 4) • (((4 : ℝ) • I) - A)) : E →L[ℝ] E).IsPositive :=
      hshift_pos.smul_of_nonneg hcoeff
    have hrewrite :
        (((μ * Q_f) • I) - (((μ * (Q_f - 1) / 4) • A) + μ • I)) =
          ((μ * (Q_f - 1) / 4) • (((4 : ℝ) • I) - A)) := by
      calc
        (((μ * Q_f) • I) - (((μ * (Q_f - 1) / 4) • A) + μ • I))
            = (((μ * Q_f) • I - μ • I) - ((μ * (Q_f - 1) / 4) • A)) := by
                abel_nf
        _ = ((μ * (Q_f - 1)) • I - ((μ * (Q_f - 1) / 4) • A)) := by
              rw [← sub_smul]
              congr 1
              ring
        _ = (((μ * (Q_f - 1) / 4) • ((4 : ℝ) • I)) - ((μ * (Q_f - 1) / 4) • A)) := by
              congr 1
              rw [smul_smul]
              congr 1
              ring
        _ = ((μ * (Q_f - 1) / 4) • (((4 : ℝ) • I) - A)) := by
              rw [smul_sub]
    exact hrewrite ▸ hbase
  rw [ContinuousLinearMap.le_def]
  rw [nesterovQuadraticObjective_hessian_eq hA_self x]
  simpa using hshift_scaled

/-- Helper for Proposition 2.6: the constant Hessian operator has norm at most `μ Q_f` under the
Loewner bounds `0 ≤ A ≤ 4 I`. -/
lemma nesterovQuadraticObjective_hessian_operator_norm_le
    (hμ : 0 ≤ μ) (hQf : 1 ≤ Q_f) (hA_nonneg : 0 ≤ A) (hA_le : A ≤ (4 : ℝ) • I) :
    ‖((μ * (Q_f - 1) / 4) • A) + μ • I‖ ≤ μ * Q_f := by
  -- The Hessian is self-adjoint and squeezed between `0` and `(μ Q_f) I`, so Rayleigh quotients
  -- control its operator norm exactly as in the finite-dimensional quadratic case.
  let B : E →L[ℝ] E := ((μ * (Q_f - 1) / 4) • A) + μ • I
  have hA_pos : A.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive A).mp hA_nonneg
  have hA_self : IsSelfAdjoint A := by
    rw [ContinuousLinearMap.isPositive_iff'] at hA_pos
    exact hA_pos.1
  have hB_eq : hessian (nesterovQuadraticObjective μ Q_f A) (0 : E) = B := by
    simpa [B] using
      nesterovQuadraticObjective_hessian_eq
        (μ := μ) (Q_f := Q_f) (A := A) hA_self (0 : E)
  have hB_lower : μ • I ≤ B := by
    rw [← hB_eq]
    exact nesterovQuadraticObjective_hessian_lower_bound
      (μ := μ) (Q_f := Q_f) (A := A) hμ hQf hA_nonneg (0 : E)
  have hB_nonneg : (0 : E →L[ℝ] E) ≤ B := by
    have hμI_nonneg : (0 : E →L[ℝ] E) ≤ μ • I := by
      rw [ContinuousLinearMap.nonneg_iff_isPositive]
      simpa using ContinuousLinearMap.isPositive_one.smul_of_nonneg hμ
    exact le_trans hμI_nonneg hB_lower
  have hB_le : B ≤ (μ * Q_f) • I := by
    rw [← hB_eq]
    exact nesterovQuadraticObjective_hessian_upper_bound
      (μ := μ) (Q_f := Q_f) (A := A) hμ hQf hA_le (0 : E)
  have hB_symm : (B : E →ₗ[ℝ] E).IsSymmetric := by
    have hB_pos : B.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive B).mp hB_nonneg
    rw [ContinuousLinearMap.isPositive_iff'] at hB_pos
    simpa using hB_pos.1.isSymmetric
  have hL_nonneg : 0 ≤ μ * Q_f := by
    nlinarith
  have hbound : ∀ z : E, |B.rayleighQuotient z| ≤ μ * Q_f := by
    intro z
    by_cases hz : z = 0
    · simpa [hz] using hL_nonneg
    · have hz_norm_sq_pos : 0 < ‖z‖ ^ (2 : ℕ) := by
        positivity
      have hLI_pos : (((μ * Q_f) • I) - B).IsPositive := by
        simpa [ContinuousLinearMap.le_def] using hB_le
      have hquad : inner ℝ (B z) z ≤ (μ * Q_f) * ‖z‖ ^ (2 : ℕ) := by
        have hnonneg := hLI_pos.inner_nonneg_left z
        simpa [inner_smul_left, inner_sub_left, inner_self_eq_norm_sq_to_K, mul_assoc,
          mul_left_comm, mul_comm] using hnonneg
      have hnonneg : 0 ≤ inner ℝ (B z) z :=
        ((ContinuousLinearMap.nonneg_iff_isPositive _).1 hB_nonneg).inner_nonneg_left z
      rw [ContinuousLinearMap.rayleighQuotient, abs_of_nonneg]
      · exact (div_le_iff₀ hz_norm_sq_pos).2 hquad
      · exact div_nonneg hnonneg hz_norm_sq_pos.le
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient B hB_symm]
  exact ciSup_le hbound

/-- Proposition 2.6: if `μ > 0`, `1 ≤ Q_f`, and `0 ≤ A ≤ 4 I` in the Loewner order, then the
quadratic objective `f_{μ,Q_f}` belongs to the source class `𝓢[μ, μ * Q_f]¹¹`; in particular its
condition number parameter is `Q_f`. -/
-- Proof sketch: use `nesterovQuadraticObjective_twiceDifferentiable` and the two Loewner Hessian
-- bounds to obtain `μ`-strong convexity and `(μ Q_f)`-Lipschitz gradient, then package these
-- data in the chapter owner predicate and rewrite through the source-facing notation `𝓢[μ, L]¹¹`.
theorem nesterovQuadraticObjective_mem_S11
    (hμ : 0 < μ) (hQf : 1 ≤ Q_f)
    (hA_nonneg : 0 ≤ A) (hA_le : A ≤ (4 : ℝ) • I) :
    nesterovQuadraticObjective μ Q_f A ∈ 𝓢[μ, μ * Q_f]¹¹ := by
  -- The positive operator assumption gives both convexity of the quadratic perturbation and
  -- self-adjointness of `A`.
  have hA_pos : A.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive A).mp hA_nonneg
  have hA_self : IsSelfAdjoint A := by
    rw [ContinuousLinearMap.isPositive_iff'] at hA_pos
    exact hA_pos.1
  have hcoeff_nonneg : 0 ≤ μ * (Q_f - 1) / 4 := by
    nlinarith
  have hquad_convex0 :
      ConvexOn ℝ Set.univ
        (fun x : E ↦
          (1 / 2 : ℝ) * inner ℝ ((((μ * (Q_f - 1) / 4) : ℝ) • A) x) x) :=
    LinearMap.IsPositive.convexOn_half_inner_map_self (hA_pos.smul_of_nonneg hcoeff_nonneg)
  have hquad_convex :
      ConvexOn ℝ Set.univ (fun x : E ↦ μ * (Q_f - 1) / 8 * inner ℝ x (A x)) := by
    refine hquad_convex0.congr ?_
    intro x hx
    calc
      (1 / 2 : ℝ) * inner ℝ ((((μ * (Q_f - 1) / 4) : ℝ) • A) x) x
          = (1 / 2 : ℝ) * ((μ * (Q_f - 1) / 4) * inner ℝ (A x) x) := by
              simp [inner_smul_left]
      _ = μ * (Q_f - 1) / 8 * inner ℝ x (A x) := by
            rw [real_inner_comm]
            ring
  have hstrong0 :
      StrongConvexOn Set.univ μ
        ((fun x : E ↦ μ * (Q_f - 1) / 8 * inner ℝ x (A x)) +
          quadraticallyRegularizedObjective (fun _ : E ↦ 0) μ (0 : E)) :=
    StrongConvexOn.add_convexOn
      (quadraticallyRegularizedObjective_zero_strongConvexOn (0 : E) μ)
      hquad_convex
  have hsplit :
      nesterovQuadraticObjective μ Q_f A =
        (fun x : E ↦ μ * (Q_f - 1) / 8 * inner ℝ x (A x)) +
          quadraticallyRegularizedObjective (fun _ : E ↦ 0) μ (0 : E) := by
    funext x
    simp [nesterovQuadraticObjective, quadraticallyRegularizedObjective]
  have hstrong : StrongConvexOn Set.univ μ (nesterovQuadraticObjective μ Q_f A) := by
    exact hsplit.symm ▸ hstrong0
  have hcont_quad :
      ContDiff ℝ 1 (fun x : E ↦ μ * (Q_f - 1) / 8 * inner ℝ x (A x)) := by
    simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
      contDiff_const.mul (contDiff_id.inner ℝ A.contDiff)
  have hcont_reg : ContDiff ℝ 1 (fun x : E ↦ (μ / 2) * ‖x‖ ^ (2 : ℕ)) := by
    simpa [smul_eq_mul] using (contDiff_norm_sq ℝ).const_smul (μ / 2)
  have hcont : ContDiff ℝ 1 (nesterovQuadraticObjective μ Q_f A) := by
    convert hcont_quad.add hcont_reg using 1
    funext x
    rw [nesterovQuadraticObjective_apply]
  let B : E →L[ℝ] E := ((μ * (Q_f - 1) / 4) • A) + μ • I
  have hcollapse :
      ((((μ * (Q_f - 1) / 8) • (A + A.adjoint)) + μ • I) : E →L[ℝ] E) = B := by
    have hsum : A + A.adjoint = (2 : ℝ) • A := by
      simp [hA_self.adjoint_eq, two_smul]
    calc
      ((((μ * (Q_f - 1) / 8) • (A + A.adjoint)) + μ • I) : E →L[ℝ] E)
          = (((μ * (Q_f - 1) / 8) • ((2 : ℝ) • A)) + μ • I) := by
              rw [hsum]
      _ = ((((μ * (Q_f - 1) / 8) * 2) • A) + μ • I) := by
            rw [smul_smul]
      _ = B := by
            unfold B
            congr 1
            ring
  have hgrad_eq : ∇ (nesterovQuadraticObjective μ Q_f A) = fun x ↦ B x := by
    rw [nesterovQuadraticObjective_gradient_eq]
    exact congrArg (fun T : E →L[ℝ] E => fun x : E ↦ T x) hcollapse
  have hBnorm : ‖B‖ ≤ μ * Q_f :=
    nesterovQuadraticObjective_hessian_operator_norm_le
      (μ := μ) (Q_f := Q_f) (A := A) hμ.le hQf hA_nonneg hA_le
  have hnnorm : (‖B‖₊ : ℝ) ≤ μ * Q_f := by
    exact_mod_cast hBnorm
  have hgrad_lip : ∀ x y : E,
      ‖∇ (nesterovQuadraticObjective μ Q_f A) x -
          ∇ (nesterovQuadraticObjective μ Q_f A) y‖ ≤
        (μ * Q_f) * ‖x - y‖ := by
    intro x y
    simpa [hgrad_eq] using
      (B.lipschitz.norm_sub_le x y).trans <|
        mul_le_mul_of_nonneg_right hnnorm (norm_nonneg _)
  exact mem_S11_iff.mpr ⟨hμ, hcont, hstrong, hgrad_lip⟩
