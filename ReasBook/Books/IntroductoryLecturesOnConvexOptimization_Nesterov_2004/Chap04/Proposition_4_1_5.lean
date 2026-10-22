/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_9
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProduct MinimalSingularValue
open scoped ConstrainedArgmin

noncomputable section

universe u v

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]

/-
Proposition 4.1.5 lies in nonlinear least squares on real inner-product spaces.

Relevant owner declarations sampled before refinement:
* `GradientDominatedOn` and `GradientDominatedOn.UsesConstant` in `Definition_4_1_9`, the chapter
  owners for gradient domination on a feasible set;
* `gradientWithin` and `UniqueDiffOn`, the canonical constrained first-order owner layer used by
  `GradientDominatedOn`;
* `minimalSingularValue` with source-facing notation `σ_min` in `Definition_4_4_5`, the chapter
  owner for Jacobian nondegeneracy;
* the canonical adjoint-side positivity condition `0 < σ_min((fderivWithin ℝ g 𝓕 x)†)` built from
  the same singular-value owner and the adjoint owner `A†`.

Best owner abstraction:
* source-facing: the half squared-residual objective together with a positive uniform lower bound
  on `J(x) J(x)^*`;
* core/canonical: `GradientDominatedOn 2 𝓕`, `gradientWithin`, and the Jacobian owner
  `σ_min((fderivWithin ℝ g 𝓕 x)†)`;
* bridge/view: the fixed-root witness `xStar` and the textbook constant `(2 * σ)⁻¹`.

Primitive data:
* the residual map `g : E → F`;
* the feasible set `𝓕`;
* a unique-differentiability hypothesis on `𝓕`, making `gradientWithin` intrinsic;
* a root `xStar ∈ 𝓕` of `g`;
* the positive constant `σ`.

Derived API:
* the half squared-residual objective `x ↦ (1 / 2) * ‖g x‖²`;
* the owner witness `GradientDominatedOn 2 𝓕 ...`;
* the source-facing constant witness
  `GradientDominatedOn.UsesConstant 2 𝓕 fLS xStar (1 / (2 * σ))`;
* the companion squared constrained-gradient inequality.
-/

section

variable (g : E → F)

local notation "fLS" =>
  fun x : E ↦ (1 / 2 : ℝ) * ‖g x‖ ^ (2 : ℕ)

local notation "withinJacobianMinSq" =>
  fun (𝓕 : Set E) (x : E) ↦ (σ_min((fderivWithin ℝ g 𝓕 x)†)) ^ (2 : ℕ)

section

variable (𝓕 : Set E) (xStar : E) (σ : ℝ)
variable (h𝓕_unique : UniqueDiffOn ℝ 𝓕)
variable (hg : DifferentiableOn ℝ g 𝓕) (hxStar : xStar ∈ 𝓕) (hgstar : g xStar = 0)
variable (hσ_pos : 0 < σ)
variable (hσ : ∀ ⦃x : E⦄, x ∈ 𝓕 → σ ≤ withinJacobianMinSq 𝓕 x)

/-- Helper for Proposition 4.1.5: a feasible root of `g` minimizes the half squared residual on
`𝓕`. -/
lemma root_mem_argmin_half_residual_sq
    (hxStar : xStar ∈ 𝓕) (hgstar : g xStar = 0) :
    xStar ∈ argmin[𝓕] fLS := by
  rw [mem_constrainedArgmin_iff]
  constructor
  · exact hxStar
  · -- At the root, the objective is zero, and the half squared norm is everywhere nonnegative.
    intro y hy
    have hy_nonneg : 0 ≤ (1 / 2 : ℝ) * ‖g y‖ ^ (2 : ℕ) := by
      positivity
    change (1 / 2 : ℝ) * ‖g xStar‖ ^ (2 : ℕ) ≤ (1 / 2 : ℝ) * ‖g y‖ ^ (2 : ℕ)
    simpa [hgstar] using hy_nonneg

/-- Helper for Proposition 4.1.5: on the feasible set, the constrained gradient of the half
squared residual is the adjoint Jacobian applied to the residual. -/
lemma gradientWithin_half_residual_sq_eq_adjoint_apply
    (h𝓕_unique : UniqueDiffOn ℝ 𝓕) (hg : DifferentiableOn ℝ g 𝓕)
    {x : E} (hx : x ∈ 𝓕) :
    gradientWithin fLS 𝓕 x =
      (ContinuousLinearMap.adjoint (fderivWithin ℝ g 𝓕 x)) (g x) := by
  -- Differentiate the squared norm and scale by `1 / 2`.
  have hderiv :
      HasFDerivWithinAt fLS
        ((1 / 2 : ℝ) •
          (2 • (innerSL ℝ (g x)).comp (fderivWithin ℝ g 𝓕 x))) 𝓕 x := by
    change HasFDerivWithinAt (fun y : E ↦ (1 / 2 : ℝ) * ‖g y‖ ^ (2 : ℕ))
      ((1 / 2 : ℝ) • (2 • (innerSL ℝ (g x)).comp (fderivWithin ℝ g 𝓕 x))) 𝓕 x
    exact (hg x hx).hasFDerivWithinAt.norm_sq.const_mul (1 / 2 : ℝ)
  have hfderiv :
      fderivWithin ℝ fLS 𝓕 x =
        ((1 / 2 : ℝ) •
          (2 • (innerSL ℝ (g x)).comp (fderivWithin ℝ g 𝓕 x))) := by
    exact hderiv.fderivWithin (h𝓕_unique x hx)
  -- Rewrite the Fréchet derivative through the adjoint and convert it back to a gradient.
  calc
    gradientWithin fLS 𝓕 x
        = (InnerProductSpace.toDual ℝ E).symm
            (((1 / 2 : ℝ) •
              (2 • (innerSL ℝ (g x)).comp (fderivWithin ℝ g 𝓕 x)))) := by
          simpa [gradientWithin] using congrArg ((InnerProductSpace.toDual ℝ E).symm) hfderiv
    _ = (InnerProductSpace.toDual ℝ E).symm
          (InnerProductSpace.toDual ℝ E
            ((ContinuousLinearMap.adjoint (fderivWithin ℝ g 𝓕 x)) (g x))) := by
          apply (InnerProductSpace.toDual ℝ E).injective
          rw [LinearIsometryEquiv.apply_symm_apply, ContinuousLinearMap.innerSL_apply_comp]
          ext y
          simp [InnerProductSpace.toDual_apply_apply]
    _ = (ContinuousLinearMap.adjoint (fderivWithin ℝ g 𝓕 x)) (g x) := by
          simp

/-- Helper for Proposition 4.1.5: the defining infimum of the least singular value yields the
squared norm lower bound for every vector. -/
lemma minimalSingularValue_sq_mul_norm_sq_le_norm_sq
    (B : F →L[ℝ] E) (y : F) :
    (σ_min(B)) ^ (2 : ℕ) * ‖y‖ ^ (2 : ℕ) ≤ ‖B y‖ ^ (2 : ℕ) := by
  -- First recover the standard unsquared lower bound from the infimum definition.
  have hmul : σ_min(B) * ‖y‖ ≤ ‖B y‖ := by
    by_cases hy : y = 0
    · simp [hy]
    · have hy_norm : 0 < ‖y‖ := norm_pos_iff.mpr hy
      have hσy : σ_min(B) ≤ ‖B y‖ / ‖y‖ := by
        rw [minimalSingularValue_def]
        refine csInf_le ?_ ?_
        · refine ⟨0, ?_⟩
          rintro _ ⟨z, rfl⟩
          exact div_nonneg (norm_nonneg _) (norm_nonneg _)
        · exact ⟨⟨y, hy⟩, rfl⟩
      exact (le_div_iff₀ hy_norm).1 hσy
  have hsq : (σ_min(B) * ‖y‖) ^ (2 : ℕ) ≤ ‖B y‖ ^ (2 : ℕ) := by
    have hleft_nonneg : 0 ≤ σ_min(B) * ‖y‖ := by
      exact mul_nonneg (minimalSingularValue_nonneg B) (norm_nonneg _)
    have hright_nonneg : 0 ≤ ‖B y‖ := norm_nonneg _
    nlinarith
  -- Expand the square of the product into the stated form.
  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hsq

/-- Helper for Proposition 4.1.5: the half squared residual satisfies the explicit degree-two
gradient-domination bound at the given root with constant `(2 * σ)⁻¹`. -/
lemma half_residual_sq_usesConstant_at_root
    (h𝓕_unique : UniqueDiffOn ℝ 𝓕) (hg : DifferentiableOn ℝ g 𝓕)
    (hxStar : xStar ∈ 𝓕) (hgstar : g xStar = 0)
    (hσ_pos : 0 < σ)
    (hσ : ∀ ⦃x : E⦄, x ∈ 𝓕 → σ ≤ withinJacobianMinSq 𝓕 x) :
    GradientDominatedOn.UsesConstant 2 𝓕 fLS xStar (1 / (2 * σ)) := by
  refine ⟨h𝓕_unique,
    root_mem_argmin_half_residual_sq (g := g) (𝓕 := 𝓕) (xStar := xStar) hxStar hgstar,
    by positivity, ?_⟩
  intro x hx
  have hxStar_zero : fLS xStar = 0 := by
    change (1 / 2 : ℝ) * ‖g xStar‖ ^ (2 : ℕ) = 0
    simp [hgstar]
  have hgrad :
      gradientWithin fLS 𝓕 x =
        (ContinuousLinearMap.adjoint (fderivWithin ℝ g 𝓕 x)) (g x) := by
    simpa using gradientWithin_half_residual_sq_eq_adjoint_apply
      (g := g) (𝓕 := 𝓕) h𝓕_unique hg hx
  have hsq :
      (σ_min((fderivWithin ℝ g 𝓕 x)†)) ^ (2 : ℕ) * ‖g x‖ ^ (2 : ℕ) ≤
        ‖gradientWithin fLS 𝓕 x‖ ^ (2 : ℕ) := by
    simpa [← hgrad] using
      minimalSingularValue_sq_mul_norm_sq_le_norm_sq
        (B := (fderivWithin ℝ g 𝓕 x)†) (y := g x)
  have hσnorm : σ * ‖g x‖ ^ (2 : ℕ) ≤ ‖gradientWithin fLS 𝓕 x‖ ^ (2 : ℕ) := by
    have hnorm_nonneg : 0 ≤ ‖g x‖ ^ (2 : ℕ) := by
      positivity
    nlinarith [hσ hx, hsq]
  have hgap_sq :
      fLS x - fLS xStar ≤ (1 / (2 * σ)) * ‖gradientWithin fLS 𝓕 x‖ ^ (2 : ℕ) := by
    -- Rewrite the objective gap as `(1 / (2 * σ)) * (σ * ‖g x‖²)` and use `hσnorm`.
    have hscale : ((1 / (2 * σ) : ℝ) * σ) = 1 / 2 := by
      field_simp [ne_of_gt hσ_pos]
    calc
      fLS x - fLS xStar = (1 / (2 : ℝ)) * ‖g x‖ ^ (2 : ℕ) := by
        rw [hxStar_zero]
        ring
      _ = ((1 / (2 * σ) : ℝ) * σ) * ‖g x‖ ^ (2 : ℕ) := by
        rw [hscale]
      _ = (1 / (2 * σ) : ℝ) * (σ * ‖g x‖ ^ (2 : ℕ)) := by
        ring
      _ ≤ (1 / (2 * σ) : ℝ) * ‖gradientWithin fLS 𝓕 x‖ ^ (2 : ℕ) := by
        exact mul_le_mul_of_nonneg_left hσnorm (by positivity)
  -- Convert the degree-two `Real.rpow` term back to an ordinary square.
  simpa [Real.rpow_natCast] using hgap_sq

/-- Proposition 4.1.5: if `g : E → F` is differentiable on the uniquely differentiable feasible
set `𝓕`, `xStar ∈ 𝓕` is a root of `g`, and `σ > 0` is a uniform lower bound on the least
eigenvalue of `J(x) J(x)^*`, recorded canonically as the inequality
`σ ≤ σ_min((fderivWithin ℝ g 𝓕 x)†)^2` for every `x ∈ 𝓕`, then the nonlinear
least-squares objective `x ↦ (1 / 2) ‖g x‖²` is gradient dominated of degree `2` on `𝓕`. -/
-- Proof sketch: the root hypothesis makes `xStar` a minimizer of the half squared-residual
-- objective. The uniform bound on `σ_min((fderivWithin ℝ g 𝓕 x)†)^2` is the
-- canonical constrained nondegeneracy input controlling the objective gap by `(2 * σ)⁻¹` times
-- the squared
-- constrained-gradient norm, which packages exactly into `GradientDominatedOn 2 𝓕 fLS`.
theorem nonlinearLeastSquares_gradientDominatedOn_two
    (h𝓕_unique : UniqueDiffOn ℝ 𝓕) (hg : DifferentiableOn ℝ g 𝓕)
    (hxStar : xStar ∈ 𝓕) (hgstar : g xStar = 0)
    (hσ_pos : 0 < σ)
    (hσ : ∀ ⦃x : E⦄, x ∈ 𝓕 → σ ≤ withinJacobianMinSq 𝓕 x)
    : GradientDominatedOn 2 𝓕 fLS := by
  refine ⟨?_, ?_, ?_⟩
  · -- The objective is a constant multiple of the squared residual norm.
    change DifferentiableOn ℝ (fun x : E ↦ (1 / 2 : ℝ) * ‖g x‖ ^ (2 : ℕ)) 𝓕
    have hnormsq : DifferentiableOn ℝ (fun x : E ↦ ‖g x‖ ^ (2 : ℕ)) 𝓕 := by
      exact DifferentiableOn.norm_sq (𝕜 := ℝ) hg
    exact hnormsq.const_mul (1 / 2 : ℝ)
  · exact ⟨by norm_num, by norm_num⟩
  · -- Package the explicit minimizer and constant from the source proof.
    exact ⟨xStar, 1 / (2 * σ),
      half_residual_sq_usesConstant_at_root
        (g := g) (𝓕 := 𝓕) (xStar := xStar) (σ := σ)
        h𝓕_unique hg hxStar hgstar hσ_pos hσ⟩

/-- The owner from Proposition 4.1.5 is witnessed at the given root by the textbook constant
`(2 * σ)⁻¹`. -/
-- Proof sketch: apply `nonlinearLeastSquares_gradientDominatedOn_two` and use the given root
-- `xStar` as the minimizer witness in the canonical `UsesConstant` package.
theorem nonlinearLeastSquares_gradientDominatedOn_two_usesConstant
    (h𝓕_unique : UniqueDiffOn ℝ 𝓕) (hg : DifferentiableOn ℝ g 𝓕)
    (hxStar : xStar ∈ 𝓕) (hgstar : g xStar = 0)
    (hσ_pos : 0 < σ)
    (hσ : ∀ ⦃x : E⦄, x ∈ 𝓕 → σ ≤ withinJacobianMinSq 𝓕 x)
    :
    GradientDominatedOn.UsesConstant 2 𝓕 fLS xStar (1 / (2 * σ)) := by
  -- Reuse the explicit witness constructed from the root and the singular-value bound.
  exact half_residual_sq_usesConstant_at_root
    (g := g) (𝓕 := 𝓕) (xStar := xStar) (σ := σ)
    h𝓕_unique hg hxStar hgstar hσ_pos hσ

/-- Companion squared-norm form of Proposition 4.1.5's constrained gradient-domination
inequality. -/
-- Proof sketch: apply `nonlinearLeastSquares_gradientDominatedOn_two_usesConstant` and rewrite
-- the degree-two `Real.rpow` term as `‖gradientWithin fLS 𝓕 x‖ ^ 2`.
theorem nonlinearLeastSquares_sub_le_inv_two_mul_norm_gradient_sq
    (h𝓕_unique : UniqueDiffOn ℝ 𝓕) (hg : DifferentiableOn ℝ g 𝓕)
    (hxStar : xStar ∈ 𝓕) (hgstar : g xStar = 0)
    (hσ_pos : 0 < σ)
    (hσ : ∀ ⦃x : E⦄, x ∈ 𝓕 → σ ≤ withinJacobianMinSq 𝓕 x)
    {x : E} (hx : x ∈ 𝓕) :
    fLS x - fLS xStar ≤ (1 / (2 * σ)) * ‖gradientWithin fLS 𝓕 x‖ ^ (2 : ℕ) := by
  -- Apply the packaged degree-two bound and rewrite `Real.rpow` as an ordinary square.
  simpa [Real.rpow_natCast] using
    (nonlinearLeastSquares_gradientDominatedOn_two_usesConstant
      (g := g) (𝓕 := 𝓕) (xStar := xStar) (σ := σ)
      h𝓕_unique hg hxStar hgstar hσ_pos hσ).bound hx

end

end
