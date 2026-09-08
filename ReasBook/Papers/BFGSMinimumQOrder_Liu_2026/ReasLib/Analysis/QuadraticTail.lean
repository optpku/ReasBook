module

public import ReasLib.Analysis.ConvexConjugate
public import ReasLib.Analysis.Convex.Hessian
public import ReasLib.Analysis.Hessian
public import ReasLib.Analysis.StandardQuadratic
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Order.Filter.Extr

public section

open scoped ContDiff Gradient Manifold Matrix.Norms.L2Operator MatrixOrder NNReal
open scoped Topology

open InnerProductSpace

namespace QuadraticTail

section

variable {n : ℕ} (H : EuclideanSpace ℝ (Fin n) → ℝ) (θ : ℝ)
variable (h_smooth : ContDiff ℝ ⊤ H)
variable (h_sub_smooth :
  ContDiff ℝ ⊤
    (H - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)))
variable (h_sub_compact :
  HasCompactSupport
    (H - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)))
variable (h_hessian_close : ∀ z, ‖ConvexAnalysis.hessian H z - 1‖ ≤ θ)
variable (h_theta : θ < 1)
variable (h_gradient_zero : gradient H 0 = 0)
variable (h_hessian_zero : ConvexAnalysis.hessian H 0 = 1)

include h_smooth

/-- The gradient of a smooth real-valued function on Euclidean space is smooth. -/
private lemma gradientContDiff : ContDiff ℝ ⊤ (gradient H) := by
  -- Differentiate once and transport the derivative through the Riesz equivalence.
  have h_gradient_formula :
      gradient H = fun x ↦ (toDual ℝ _).symm (fderiv ℝ H x) := by
    funext x
    rfl
  have h_fderiv_order : (⊤ : ℕ∞ω) + 1 ≤ ⊤ := by
    simp
  rw [h_gradient_formula]
  exact (toDual ℝ _).symm.contDiff.comp
    (ContDiff.fderiv_right h_smooth (m := ⊤) h_fderiv_order)

/-- A uniform Hessian bound controls the gradient as a perturbation of the identity. -/
private lemma gradientApproximatesIdentity (c : ℝ≥0)
    (h_close : ∀ z, ‖ConvexAnalysis.hessian H z - 1‖ ≤ c) :
    ApproximatesLinearOn (gradient H) (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)) Set.univ c := by
  -- Apply the mean-value theorem to the difference between the gradient and the identity.
  rw [ApproximatesLinearOn.approximatesLinearOn_iff_lipschitzOnWith]
  rw [lipschitzOnWith_univ]
  have h_gradient_smooth := gradientContDiff H h_smooth
  have h_difference_smooth := h_gradient_smooth.sub contDiff_id
  have h_top_ne_zero : (⊤ : ℕ∞ω) ≠ 0 := by
    simp
  refine lipschitzWith_of_nnnorm_fderiv_le (h_difference_smooth.differentiable h_top_ne_zero)
    (fun z ↦ ?_)
  -- The derivative of this difference is the Hessian minus the identity map.
  rw [fderiv_sub (h_gradient_smooth.differentiable h_top_ne_zero).differentiableAt
    (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).differentiableAt,
    ContinuousLinearMap.fderiv]
  rw [← ConvexAnalysis.toEuclideanCLM_hessian]
  rw [← map_one (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _), ← map_sub]
  exact_mod_cast h_close z

omit h_smooth

/-- A continuous linear endomorphism less than one from the identity is a continuous
linear equivalence. -/
private lemma existsContinuousLinearEquivOfNormSubIdentityLtOne
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A : E →L[ℝ] E) (hA : ‖A - 1‖ < 1) :
    ∃ e : E ≃L[ℝ] E, (e : E →L[ℝ] E) = A := by
  -- Rewrite `A` as a Neumann-series unit around the identity.
  have h_one_sub : ‖1 - A‖ < 1 := by
    calc
      ‖1 - A‖ = ‖-(1 - A)‖ := (norm_neg _).symm
      _ = ‖A - 1‖ := by rw [neg_sub]
      _ < 1 := hA
  have h_unit : IsUnit A := by
    simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one h_one_sub
  -- The canonical equivalence associated to this unit has underlying map `A`.
  refine ⟨ContinuousLinearEquiv.ofUnit h_unit.unit, ?_⟩
  exact h_unit.unit_spec

/-- A smooth global perturbation of the identity by a contraction is a smooth
diffeomorphism. -/
private lemma smoothDiffeomorphOfApproximatesIdentity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : E → E) (c : ℝ≥0) (h_smooth_f : ContDiff ℝ ⊤ f)
    (h_approx : ApproximatesLinearOn f (1 : E →L[ℝ] E) Set.univ c)
    (hc : (c : ℝ) < 1) :
    ∃ e : E ≃ₘ[ℝ] E, (∀ x, e x = f x) ∧ ContDiff ℝ ⊤ (e.symm : E → E) := by
  classical
  have h_top_ne_zero : (⊤ : ℕ∞ω) ≠ 0 := by
    simp
  have h_infty_le_top : (∞ : ℕ∞ω) ≤ ⊤ := by
    simp
  -- The approximation theorem first supplies a global homeomorphism.
  have h_threshold :
      Subsingleton E ∨
        c < ‖((ContinuousLinearEquiv.refl ℝ E).symm : E →L[ℝ] E)‖₊⁻¹ := by
    by_cases hE : Subsingleton E
    · exact Or.inl hE
    · right
      -- Local instance justification (proof-local temporary data): the norm of the identity
      -- map is one in
      -- precisely the non-subsingleton branch.
      letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
      simp only [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl,
        ContinuousLinearMap.nnnorm_id, inv_one]
      exact_mod_cast hc
  have h_approx_refl :
      ApproximatesLinearOn f
        (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) Set.univ c := by
    have h_refl : (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) = 1 := by
      ext x
      rfl
    rw [h_refl]
    exact h_approx
  let home : E ≃ₜ E := ApproximatesLinearOn.toHomeomorph f h_approx_refl h_threshold
  have h_home_apply (x : E) : home x = f x := by
    rfl
  have h_home_fun : (home : E → E) = f := funext h_home_apply
  have h_home_smooth : ContDiff ℝ ⊤ (home : E → E) := by
    rw [h_home_fun]
    exact h_smooth_f
  -- Differentiating the Lipschitz remainder shows every derivative is invertible.
  have h_remainder_lipschitz : LipschitzWith c (f - ⇑(1 : E →L[ℝ] E)) := by
    rw [← lipschitzOnWith_univ]
    exact h_approx.lipschitzOnWith
  have h_derivative_close (x : E) : ‖fderiv ℝ f x - 1‖ < 1 := by
    have h_f_diff : DifferentiableAt ℝ f x :=
      (h_smooth_f.differentiable h_top_ne_zero).differentiableAt
    have h_id_diff : DifferentiableAt ℝ (1 : E →L[ℝ] E) x :=
      (1 : E →L[ℝ] E).differentiableAt
    have h_fderiv_sub :
        fderiv ℝ (f - ⇑(1 : E →L[ℝ] E)) x = fderiv ℝ f x - 1 := by
      simpa only [ContinuousLinearMap.fderiv] using fderiv_sub h_f_diff h_id_diff
    calc
      ‖fderiv ℝ f x - 1‖ = ‖fderiv ℝ (f - ⇑(1 : E →L[ℝ] E)) x‖ :=
        congrArg norm h_fderiv_sub.symm
      _ ≤ c := norm_fderiv_le_of_lipschitz ℝ h_remainder_lipschitz
      _ < 1 := hc
  have h_derivative_equiv (x : E) :
      ∃ e : E ≃L[ℝ] E, (e : E →L[ℝ] E) = fderiv ℝ f x :=
    existsContinuousLinearEquivOfNormSubIdentityLtOne _ (h_derivative_close x)
  choose f' hf' using h_derivative_equiv
  have h_home_deriv (x : E) : HasFDerivAt home (f' x : E →L[ℝ] E) x := by
    rw [hf' x]
    rw [h_home_fun]
    exact (h_smooth_f.differentiable h_top_ne_zero).differentiableAt.hasFDerivAt
  have h_inverse_smooth : ContDiff ℝ ⊤ (home.symm : E → E) :=
    home.contDiff_symm h_home_deriv h_home_smooth
  -- Package the homeomorphism and the two smoothness statements.
  let e : E ≃ₘ[ℝ] E :=
    { toEquiv := home.toEquiv
      contMDiff_toFun := (h_home_smooth.of_le h_infty_le_top).contMDiff
      contMDiff_invFun := (h_inverse_smooth.of_le h_infty_le_top).contMDiff }
  refine ⟨e, fun x ↦ h_home_apply x, ?_⟩
  exact h_inverse_smooth

/-- A map uniformly closer than one to the identity is strictly monotone in the real
inner product. -/
private lemma innerMapSubMapSubPosOfApproximatesIdentity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → E) (c : ℝ≥0)
    (h_approx : ApproximatesLinearOn f (1 : E →L[ℝ] E) Set.univ c)
    (hc : (c : ℝ) < 1) {u v : E} (huv : u ≠ v) :
    0 < ⟪f u - f v, u - v⟫_ℝ := by
  -- Separate the identity contribution from the contraction error.
  have h_error := h_approx u (Set.mem_univ u) v (Set.mem_univ v)
  simp only [one_apply_eq_self] at h_error
  have h_inner_error := abs_real_inner_le_norm (f u - f v - (u - v)) (u - v)
  have h_error_inner_lower :
      -(c : ℝ) * ‖u - v‖ ^ 2 ≤ ⟪f u - f v - (u - v), u - v⟫_ℝ := by
    have h_abs :
        |⟪f u - f v - (u - v), u - v⟫_ℝ| ≤ (c : ℝ) * ‖u - v‖ ^ 2 := by
      calc
        |⟪f u - f v - (u - v), u - v⟫_ℝ| ≤
            ‖f u - f v - (u - v)‖ * ‖u - v‖ := h_inner_error
        _ ≤ ((c : ℝ) * ‖u - v‖) * ‖u - v‖ := by
          gcongr
        _ = (c : ℝ) * ‖u - v‖ ^ 2 := by ring
    simpa only [neg_mul] using neg_le_of_abs_le h_abs
  have h_norm_sq_pos : 0 < ‖u - v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr huv))
  have h_main : 0 < (1 - (c : ℝ)) * ‖u - v‖ ^ 2 :=
    mul_pos (sub_pos.mpr hc) h_norm_sq_pos
  -- Recombine the error and identity terms into the desired pairing.
  rw [inner_sub_left, inner_sub_left, real_inner_self_eq_norm_sq] at h_error_inner_lower
  rw [inner_sub_left]
  nlinarith

/-- The derivative of a smooth function along an affine line is its gradient paired with
the line direction. -/
private lemma hasDerivAtAlongAffineLine
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {H : E → ℝ} (hH : Differentiable ℝ H) (z d : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ H (z + s • d))
      ⟪gradient H (z + t • d), d⟫_ℝ t := by
  -- Differentiate the affine parametrization and then compose with `H`.
  have h_line_raw := (hasDerivAt_const t z).add ((hasDerivAt_id t).smul_const d)
  have h_line_fun :
      (fun s : ℝ ↦ z) + (fun s : ℝ ↦ id s • d) = fun s : ℝ ↦ z + s • d := by
    funext s
    rfl
  have h_line : HasDerivAt (fun s : ℝ ↦ z + s • d) d t := by
    rw [← h_line_fun]
    simpa only [zero_add, one_smul] using h_line_raw
  have h_comp := hH.differentiableAt.hasGradientAt.hasFDerivAt.comp_hasDerivAt t h_line
  have h_comp_fun :
      H ∘ (fun s : ℝ ↦ z + s • d) = fun s : ℝ ↦ H (z + s • d) := rfl
  rw [← h_comp_fun]
  simpa only [toDual_apply_apply] using h_comp

/-- Along every nonconstant affine line, a smooth potential whose gradient approximates
the identity is strictly convex. -/
private lemma strictConvexOnAffineLineOfGradientApproximatesIdentity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (H : E → ℝ) (c : ℝ≥0) (h_smooth_H : ContDiff ℝ ⊤ H)
    (h_approx : ApproximatesLinearOn (gradient H) (1 : E →L[ℝ] E) Set.univ c)
    (hc : (c : ℝ) < 1) (z d : E) (hd : d ≠ 0) :
    StrictConvexOn ℝ Set.univ (fun t : ℝ ↦ H (z + t • d)) := by
  have h_top_ne_zero : (⊤ : ℕ∞ω) ≠ 0 := by simp
  have h_H_diff : Differentiable ℝ H := h_smooth_H.differentiable h_top_ne_zero
  have h_line_deriv (t : ℝ) :
      HasDerivAt (fun s : ℝ ↦ H (z + s • d))
        ⟪gradient H (z + t • d), d⟫_ℝ t :=
    hasDerivAtAlongAffineLine h_H_diff z d t
  have h_deriv_strict : StrictMono (deriv fun t : ℝ ↦ H (z + t • d)) := by
    intro a b hab
    rw [(h_line_deriv a).deriv, (h_line_deriv b).deriv]
    have h_scale : z + b • d - (z + a • d) = (b - a) • d := by
      module
    have h_points_ne : z + b • d ≠ z + a • d := by
      intro h_points
      have h_smul : (b - a) • d = 0 := by
        rw [← h_scale]
        exact sub_eq_zero.mpr h_points
      exact hd (smul_eq_zero.mp h_smul |>.resolve_left (sub_ne_zero.mpr hab.ne'))
    have h_positive := innerMapSubMapSubPosOfApproximatesIdentity
      (gradient H) c h_approx hc h_points_ne
    rw [h_scale, inner_smul_right, inner_sub_left] at h_positive
    nlinarith
  -- The one-dimensional derivative criterion now gives strict convexity.
  exact h_deriv_strict.strictConvexOn_univ_of_deriv
    (h_smooth_H.comp (contDiff_const.add (contDiff_id.smul_const d))).continuous

/-- The inverse-gradient point uniquely maximizes the pairing minus a smooth potential
whose gradient is a contraction perturbation of the identity. -/
private lemma pairingSubUniqueMaximumAtInvGradient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (H : E → ℝ) (c : ℝ≥0) (h_smooth_H : ContDiff ℝ ⊤ H)
    (h_approx : ApproximatesLinearOn (gradient H) (1 : E →L[ℝ] E) Set.univ c)
    (hc : (c : ℝ) < 1) (h_bij : Function.Bijective (gradient H)) (x : E) :
    IsGreatest (Set.range (fun y ↦ ⟪x, y⟫_ℝ - H y))
        (⟪x, Function.invFun (gradient H) x⟫_ℝ - H (Function.invFun (gradient H) x)) ∧
      ∀ y, ⟪x, y⟫_ℝ - H y =
          ⟪x, Function.invFun (gradient H) x⟫_ℝ - H (Function.invFun (gradient H) x) →
        y = Function.invFun (gradient H) x := by
  let z := Function.invFun (gradient H) x
  have h_gradient_z : gradient H z = x := Function.rightInverse_invFun h_bij.2 x
  have h_top_ne_zero : (⊤ : ℕ∞ω) ≠ 0 := by simp
  have h_H_diff : Differentiable ℝ H := h_smooth_H.differentiable h_top_ne_zero
  -- Strict convexity on the line from `z` to any other point gives the supporting inequality.
  have h_strict_support {y : E} (hy : y ≠ z) :
      ⟪x, y⟫_ℝ - H y < ⟪x, z⟫_ℝ - H z := by
    have hd : y - z ≠ 0 := sub_ne_zero.mpr hy
    have h_line_convex := strictConvexOnAffineLineOfGradientApproximatesIdentity
      H c h_smooth_H h_approx hc z (y - z) hd
    have h_line_deriv := hasDerivAtAlongAffineLine h_H_diff z (y - z) 0
    have h_slope := h_line_convex.lt_slope_of_hasDerivAt
      (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one h_line_deriv
    have h_endpoint : z + (1 : ℝ) • (y - z) = y := by
      module
    have h_tangent : ⟪x, y - z⟫_ℝ < H y - H z := by
      rw [slope_def_field] at h_slope
      rw [h_endpoint, zero_smul, add_zero, h_gradient_z] at h_slope
      simpa only [sub_zero, div_one] using h_slope
    rw [inner_sub_right] at h_tangent
    linarith
  have h_maximal (y : E) : ⟪x, y⟫_ℝ - H y ≤ ⟪x, z⟫_ℝ - H z := by
    by_cases hy : y = z
    · rw [hy]
    · exact (h_strict_support hy).le
  constructor
  · constructor
    · exact ⟨z, rfl⟩
    · rintro _ ⟨y, rfl⟩
      exact h_maximal y
  · intro y hy
    by_contra hyz
    exact (h_strict_support hyz).ne hy

include h_smooth h_sub_smooth h_sub_compact h_hessian_close h_theta
  h_gradient_zero h_hessian_zero

/-- QuadraticTail.gradientDiffeomorph: The gradient of a smooth compactly supported
perturbation of the standard quadratic, with Hessian uniformly less than one from the
identity, is a global smooth diffeomorphism. -/
theorem gradientDiffeomorph :
    ∃ e : EuclideanSpace ℝ (Fin n) ≃ₘ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ x, e x = gradient H x := by
  -- The bound at the origin first shows that the approximation radius is nonnegative.
  have h_theta_nonneg : 0 ≤ θ :=
    (norm_nonneg (ConvexAnalysis.hessian H 0 - 1)).trans (h_hessian_close 0)
  let c : ℝ≥0 := ⟨θ, h_theta_nonneg⟩
  -- Apply the global smooth inverse theorem to the gradient's contraction remainder.
  have h_close_c : ∀ z, ‖ConvexAnalysis.hessian H z - 1‖ ≤ (c : ℝ) := by
    intro z
    change ‖ConvexAnalysis.hessian H z - 1‖ ≤ θ
    exact h_hessian_close z
  have h_approx := gradientApproximatesIdentity H h_smooth c h_close_c
  have hc : (c : ℝ) < 1 := by
    change θ < 1
    exact h_theta
  obtain ⟨e, he, _⟩ := smoothDiffeomorphOfApproximatesIdentity (gradient H) c
    (gradientContDiff H h_smooth) h_approx hc
  exact ⟨e, he⟩

omit h_sub_smooth h_sub_compact h_gradient_zero h_hessian_zero

/-- The gradient is bijective and its set-theoretic inverse retains the full regularity
of the potential. -/
private lemma gradientInverseData :
    Function.Bijective (gradient H) ∧
      ContDiff ℝ ⊤ (Function.invFun (gradient H)) := by
  have h_theta_nonneg : 0 ≤ θ :=
    (norm_nonneg (ConvexAnalysis.hessian H 0 - 1)).trans (h_hessian_close 0)
  let c : ℝ≥0 := ⟨θ, h_theta_nonneg⟩
  have h_close_c : ∀ z, ‖ConvexAnalysis.hessian H z - 1‖ ≤ (c : ℝ) := by
    intro z
    change ‖ConvexAnalysis.hessian H z - 1‖ ≤ θ
    exact h_hessian_close z
  have h_approx := gradientApproximatesIdentity H h_smooth c h_close_c
  have hc : (c : ℝ) < 1 := by
    change θ < 1
    exact h_theta
  obtain ⟨e, he, h_inverse_smooth⟩ := smoothDiffeomorphOfApproximatesIdentity
    (gradient H) c (gradientContDiff H h_smooth) h_approx hc
  have h_e_fun : (e : _ → _) = gradient H := funext he
  have h_bij : Function.Bijective (gradient H) := by
    rw [← h_e_fun]
    exact e.bijective
  have h_right_inverse : Function.RightInverse (e.symm : _ → _) (gradient H) := by
    intro x
    rw [← he (e.symm x)]
    exact e.apply_symm_apply x
  have h_inv_fun : Function.invFun (gradient H) = (e.symm : _ → _) :=
    Function.invFun_eq_of_injective_of_rightInverse h_bij.1 h_right_inverse
  constructor
  · exact h_bij
  · rw [h_inv_fun]
    exact h_inverse_smooth

/-- The convex conjugate is attained at the inverse-gradient point. -/
private lemma conjugate_eq_inner_invGradient (x : EuclideanSpace ℝ (Fin n)) :
    ConvexAnalysis.conjugate H x =
      ⟪x, Function.invFun (gradient H) x⟫_ℝ - H (Function.invFun (gradient H) x) := by
  have h_theta_nonneg : 0 ≤ θ :=
    (norm_nonneg (ConvexAnalysis.hessian H 0 - 1)).trans (h_hessian_close 0)
  let c : ℝ≥0 := ⟨θ, h_theta_nonneg⟩
  have h_close_c : ∀ z, ‖ConvexAnalysis.hessian H z - 1‖ ≤ (c : ℝ) := by
    intro z
    change ‖ConvexAnalysis.hessian H z - 1‖ ≤ θ
    exact h_hessian_close z
  have h_approx := gradientApproximatesIdentity H h_smooth c h_close_c
  have hc : (c : ℝ) < 1 := by
    change θ < 1
    exact h_theta
  have h_bij := (gradientInverseData H θ h_smooth h_hessian_close h_theta).1
  -- Evaluate the defining supremum at its greatest element.
  rw [ConvexAnalysis.conjugate_apply]
  exact (pairingSubUniqueMaximumAtInvGradient H c h_smooth h_approx hc h_bij x).1.csSup_eq

/-- The convex conjugate has gradient equal to the inverse of the original gradient at
every point. -/
private lemma hasGradientAtConjugate (x : EuclideanSpace ℝ (Fin n)) :
    HasGradientAt (ConvexAnalysis.conjugate H)
      (Function.invFun (gradient H) x) x := by
  let g := Function.invFun (gradient H)
  have h_inverse_data := gradientInverseData H θ h_smooth h_hessian_close h_theta
  have h_bij : Function.Bijective (gradient H) := h_inverse_data.1
  have h_g_smooth : ContDiff ℝ ⊤ g := h_inverse_data.2
  have h_top_ne_zero : (⊤ : ℕ∞ω) ≠ 0 := by simp
  have h_g_deriv : HasFDerivAt g (fderiv ℝ g x) x :=
    (h_g_smooth.differentiable h_top_ne_zero).differentiableAt.hasFDerivAt
  have h_H_deriv :
      HasFDerivAt H (toDual ℝ _ (gradient H (g x))) (g x) :=
    (h_smooth.differentiable h_top_ne_zero).differentiableAt.hasGradientAt.hasFDerivAt
  have h_gradient_g : gradient H (g x) = x := Function.rightInverse_invFun h_bij.2 x
  have h_pairing_deriv := (hasFDerivAt_id x).inner ℝ h_g_deriv
  have h_composed_deriv := h_H_deriv.comp x h_g_deriv
  have h_difference_deriv := h_pairing_deriv.sub h_composed_deriv
  have h_derivative_eq :
      (fderivInnerCLM ℝ (x, g x)).comp
          ((1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).prod
            (fderiv ℝ g x)) -
        (toDual ℝ _ (gradient H (g x))).comp (fderiv ℝ g x) =
          toDual ℝ _ (g x) := by
    ext v
    simp only [sub_apply, ContinuousLinearMap.comp_apply,
      fderivInnerCLM_apply, ContinuousLinearMap.prod_apply, one_apply_eq_self,
      toDual_apply_apply, h_gradient_g]
    rw [real_inner_comm v (g x)]
    ring
  have h_expression_gradient :
      HasGradientAt (fun y ↦ ⟪y, g y⟫_ℝ - H (g y)) (g x) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    exact h_difference_deriv.congr_fderiv h_derivative_eq
  have h_formula : ConvexAnalysis.conjugate H = fun y ↦ ⟪y, g y⟫_ℝ - H (g y) := by
    funext y
    exact conjugate_eq_inner_invGradient H θ h_smooth h_hessian_close h_theta y
  -- Transfer the derivative computation through the maximizer formula.
  rw [h_formula]
  exact h_expression_gradient

include h_sub_smooth h_sub_compact h_gradient_zero h_hessian_zero

/-- The convex conjugate of a smooth compactly supported perturbation of the standard
quadratic is smooth under the stated Hessian bound and normalization. -/
theorem conjugateContDiff : ContDiff ℝ ⊤ (ConvexAnalysis.conjugate H) := by
  -- Rewrite the supremum using its unique inverse-gradient maximizer.
  have h_formula : ConvexAnalysis.conjugate H = fun x ↦
      ⟪x, Function.invFun (gradient H) x⟫_ℝ - H (Function.invFun (gradient H) x) := by
    funext x
    exact conjugate_eq_inner_invGradient H θ h_smooth h_hessian_close h_theta x
  have h_inverse_smooth := (gradientInverseData H θ h_smooth h_hessian_close h_theta).2
  rw [h_formula]
  -- Both the pairing and the composed potential are smooth.
  exact (contDiff_id.inner ℝ h_inverse_smooth).sub (h_smooth.comp h_inverse_smooth)

/-- The gradient of the convex conjugate is the functional inverse of the original
gradient under the quadratic-tail hypotheses. -/
theorem gradient_conjugate :
    gradient (ConvexAnalysis.conjugate H) = Function.invFun (gradient H) := by
  -- Pointwise gradient uniqueness applies to the derivative formula above.
  exact gradient_eq fun x ↦
    hasGradientAtConjugate H θ h_smooth h_hessian_close h_theta x

/-- The Hessian of the convex conjugate is the inverse Hessian evaluated at the
inverse-gradient point. -/
theorem hessian_conjugate (x : EuclideanSpace ℝ (Fin n)) :
    ConvexAnalysis.hessian (ConvexAnalysis.conjugate H) x =
      (ConvexAnalysis.hessian H (Function.invFun (gradient H) x))⁻¹ := by
  let g := Function.invFun (gradient H)
  let A := ConvexAnalysis.hessian H (g x)
  let B := ConvexAnalysis.hessian (ConvexAnalysis.conjugate H) x
  have h_inverse_data := gradientInverseData H θ h_smooth h_hessian_close h_theta
  have h_bij : Function.Bijective (gradient H) := h_inverse_data.1
  have h_top_ne_zero : (⊤ : ℕ∞ω) ≠ 0 := by simp
  have h_gradient_diff : Differentiable ℝ (gradient H) :=
    (gradientContDiff H h_smooth).differentiable h_top_ne_zero
  have h_g_diff : Differentiable ℝ g := h_inverse_data.2.differentiable h_top_ne_zero
  have h_gradient_g (y : EuclideanSpace ℝ (Fin n)) : gradient H (g y) = y :=
    Function.rightInverse_invFun h_bij.2 y
  have h_g_gradient (y : EuclideanSpace ℝ (Fin n)) : g (gradient H y) = y :=
    Function.leftInverse_invFun h_bij.1 y
  -- Differentiate both global inverse identities at the relevant points.
  have h_deriv_mul_right :
      fderiv ℝ (gradient H) (g x) * fderiv ℝ g x = 1 := by
    have h_chain := fderiv_comp (𝕜 := ℝ) (f := g) (g := gradient H) (x := x)
      h_gradient_diff.differentiableAt h_g_diff.differentiableAt
    have h_comp : gradient H ∘ g = id := funext h_gradient_g
    calc
      fderiv ℝ (gradient H) (g x) * fderiv ℝ g x =
          (fderiv ℝ (gradient H) (g x)).comp (fderiv ℝ g x) :=
        ContinuousLinearMap.mul_def _ _
      _ = fderiv ℝ (gradient H ∘ g) x := h_chain.symm
      _ = fderiv ℝ id x := congrArg (fun k ↦ fderiv ℝ k x) h_comp
      _ = 1 := fderiv_id
  have h_deriv_mul_left :
      fderiv ℝ g x * fderiv ℝ (gradient H) (g x) = 1 := by
    have h_chain := fderiv_comp (𝕜 := ℝ) (f := gradient H) (g := g) (x := g x)
      h_g_diff.differentiableAt h_gradient_diff.differentiableAt
    have h_comp : g ∘ gradient H = id := funext h_g_gradient
    calc
      fderiv ℝ g x * fderiv ℝ (gradient H) (g x) =
          (fderiv ℝ g x).comp (fderiv ℝ (gradient H) (g x)) :=
        ContinuousLinearMap.mul_def _ _
      _ = (fderiv ℝ g (gradient H (g x))).comp
          (fderiv ℝ (gradient H) (g x)) := by rw [h_gradient_g]
      _ = fderiv ℝ (g ∘ gradient H) (g x) := h_chain.symm
      _ = fderiv ℝ id (g x) := congrArg (fun k ↦ fderiv ℝ k (g x)) h_comp
      _ = 1 := fderiv_id
  have h_gradient_conjugate :
      gradient (ConvexAnalysis.conjugate H) = g :=
    gradient_conjugate H θ h_smooth h_sub_smooth h_sub_compact h_hessian_close h_theta
      h_gradient_zero h_hessian_zero
  have h_toA :
      (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _) A =
        fderiv ℝ (gradient H) (g x) := by
    dsimp only [A]
    exact ConvexAnalysis.toEuclideanCLM_hessian H (g x)
  have h_toB :
      (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _) B =
        fderiv ℝ g x := by
    calc
      (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _) B =
          fderiv ℝ (gradient (ConvexAnalysis.conjugate H)) x := by
        dsimp only [B]
        exact ConvexAnalysis.toEuclideanCLM_hessian (ConvexAnalysis.conjugate H) x
      _ = fderiv ℝ g x := congrArg (fun k ↦ fderiv ℝ k x) h_gradient_conjugate
  -- Transport the two inverse identities from continuous linear maps to Hessian matrices.
  have h_AB : A * B = 1 := by
    apply (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _).injective
    calc
      (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _) (A * B) =
          (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _) A *
            (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _) B := map_mul _ A B
      _ = fderiv ℝ (gradient H) (g x) * fderiv ℝ g x := congrArg₂ (· * ·) h_toA h_toB
      _ = 1 := h_deriv_mul_right
      _ = (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _) 1 := (map_one _).symm
  have h_BA : B * A = 1 := by
    apply (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _).injective
    calc
      (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _) (B * A) =
          (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _) B *
            (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _) A := map_mul _ B A
      _ = fderiv ℝ g x * fderiv ℝ (gradient H) (g x) := congrArg₂ (· * ·) h_toB h_toA
      _ = 1 := h_deriv_mul_left
      _ = (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _) 1 := (map_one _).symm
  have h_A_unit : IsUnit A := ⟨⟨A, B, h_AB, h_BA⟩, rfl⟩
  have h_A_det : IsUnit A.det := A.isUnit_iff_isUnit_det.mp h_A_unit
  -- A two-sided inverse agrees with the canonical nonsingular matrix inverse.
  change B = A⁻¹
  calc
    B = B * 1 := (mul_one B).symm
    _ = B * (A * A⁻¹) := by rw [Matrix.mul_nonsing_inv A h_A_det]
    _ = (B * A) * A⁻¹ := by rw [Matrix.mul_assoc]
    _ = A⁻¹ := by rw [h_BA, one_mul]

omit h_sub_smooth h_sub_compact h_hessian_close h_theta h_gradient_zero h_hessian_zero

/-- The Hessian of a smooth real-valued function on Euclidean space is Hermitian. -/
private lemma hessianIsHermitian (x : EuclideanSpace ℝ (Fin n)) :
    (ConvexAnalysis.hessian H x).IsHermitian := by
  -- Symmetry of the second Fréchet derivative becomes symmetry of the Hessian operator.
  have h_second_order : minSmoothness ℝ 2 ≤ (⊤ : ℕ∞ω) := by
    simp
  have h_second_symmetric : IsSymmSndFDerivAt ℝ H x :=
    h_smooth.contDiffAt.isSymmSndFDerivAt h_second_order
  have h_top_ne_zero : (⊤ : ℕ∞ω) ≠ 0 := by
    simp
  have h_gradient_deriv :
      HasFDerivAt (gradient H) (fderiv ℝ (gradient H) x) x :=
    (gradientContDiff H h_smooth).differentiable h_top_ne_zero
      |>.differentiableAt.hasFDerivAt
  let dualMap : EuclideanSpace ℝ (Fin n) →L[ℝ]
      (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
    (toDual ℝ (EuclideanSpace ℝ (Fin n))).toContinuousLinearEquiv.toContinuousLinearMap
  have h_second_deriv :
      HasFDerivAt (fderiv ℝ H)
        (dualMap.comp (fderiv ℝ (gradient H) x)) x := by
    rw [← toDual_comp_gradient]
    exact dualMap.hasFDerivAt.comp x h_gradient_deriv
  have h_pair (v w : EuclideanSpace ℝ (Fin n)) :
      ⟪fderiv ℝ (gradient H) x v, w⟫_ℝ =
        fderiv ℝ (fderiv ℝ H) x v w := by
    rw [h_second_deriv.fderiv]
    rfl
  rw [← Matrix.isSymmetric_toEuclideanLin_iff]
  intro v w
  rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,
    ConvexAnalysis.toEuclideanCLM_hessian]
  change ⟪fderiv ℝ (gradient H) x v, w⟫_ℝ =
    ⟪v, fderiv ℝ (gradient H) x w⟫_ℝ
  calc
    ⟪fderiv ℝ (gradient H) x v, w⟫_ℝ =
        fderiv ℝ (fderiv ℝ H) x v w := h_pair v w
    _ = fderiv ℝ (fderiv ℝ H) x w v := h_second_symmetric.eq v w
    _ = ⟪fderiv ℝ (gradient H) x w, v⟫_ℝ := (h_pair w v).symm
    _ = ⟪v, fderiv ℝ (gradient H) x w⟫_ℝ := real_inner_comm _ _

omit h_smooth

/-- A Hermitian real matrix lies between the scalar matrices determined by its Euclidean
operator norm. -/
private lemma hermitianMatrixOrderBounds (D : Matrix (Fin n) (Fin n) ℝ)
    (hD : D.IsHermitian) :
    -(‖D‖ • (1 : Matrix (Fin n) (Fin n) ℝ)) ≤ D ∧
      D ≤ ‖D‖ • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  have h_scalar_selfAdjoint (a : ℝ) : IsSelfAdjoint a := by
    rw [isSelfAdjoint_iff, star_trivial]
  have h_quadratic_abs (v : EuclideanSpace ℝ (Fin n)) :
      |⟪(Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _) D v, v⟫_ℝ| ≤
        ‖D‖ * ‖v‖ ^ 2 := by
    calc
      |⟪(Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _) D v, v⟫_ℝ| ≤
          ‖(Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _) D v‖ * ‖v‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ (‖D‖ * ‖v‖) * ‖v‖ := by
        gcongr
        exact ((Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _) D).le_opNorm v
      _ = ‖D‖ * ‖v‖ ^ 2 := by ring
  constructor
  · rw [Matrix.le_iff, ← Matrix.isPositive_toEuclideanLin_iff]
    constructor
    · rw [Matrix.isSymmetric_toEuclideanLin_iff]
      exact hD.sub ((Matrix.isHermitian_one.smul (h_scalar_selfAdjoint _)).neg)
    · intro v
      change 0 ≤ ⟪(Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _)
        (D - -(‖D‖ • 1)) v, v⟫_ℝ
      rw [map_sub, map_neg, map_smul, map_one]
      simp only [sub_apply, neg_apply, smul_apply, one_apply_eq_self, inner_sub_left,
        inner_neg_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
      linarith [neg_le_of_abs_le (h_quadratic_abs v)]
  · rw [Matrix.le_iff, ← Matrix.isPositive_toEuclideanLin_iff]
    constructor
    · rw [Matrix.isSymmetric_toEuclideanLin_iff]
      exact (Matrix.isHermitian_one.smul (h_scalar_selfAdjoint _)).sub hD
    · intro v
      change 0 ≤ ⟪(Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _)
        (‖D‖ • 1 - D) v, v⟫_ℝ
      rw [map_sub, map_smul, map_one]
      simp only [sub_apply, smul_apply, one_apply_eq_self, inner_sub_left, real_inner_smul_left,
        real_inner_self_eq_norm_sq]
      linarith [le_of_abs_le (h_quadratic_abs v)]

/-- A Hermitian matrix within `θ` of the identity has inverse in the reciprocal
Loewner-order interval. -/
private lemma inverseMatrixOrderBoundsOfNormSubOneLe
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hθ_nonneg : 0 ≤ θ) (hθ_lt : θ < 1) (hA_close : ‖A - 1‖ ≤ θ) :
    A⁻¹ ∈ Set.Icc ((1 / (1 + θ) : ℝ) • 1) ((1 / (1 - θ) : ℝ) • 1) := by
  classical
  have h_one_sub_pos : 0 < 1 - θ := sub_pos.mpr hθ_lt
  have h_one_add_pos : 0 < 1 + θ := by linarith
  -- The self-adjoint norm estimate gives the two scalar order bounds for `A`.
  have h_difference_bounds := hermitianMatrixOrderBounds (A - 1)
    (hA.sub Matrix.isHermitian_one)
  have h_difference_upper : A - 1 ≤ θ • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    calc
      A - 1 ≤ ‖A - 1‖ • (1 : Matrix (Fin n) (Fin n) ℝ) := h_difference_bounds.2
      _ ≤ θ • (1 : Matrix (Fin n) (Fin n) ℝ) := by
        exact smul_le_smul_of_nonneg_right hA_close zero_le_one
  have h_difference_lower : -(θ • (1 : Matrix (Fin n) (Fin n) ℝ)) ≤ A - 1 := by
    calc
      -(θ • (1 : Matrix (Fin n) (Fin n) ℝ)) ≤
          -(‖A - 1‖ • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
        exact neg_le_neg (smul_le_smul_of_nonneg_right hA_close zero_le_one)
      _ ≤ A - 1 := h_difference_bounds.1
  have h_A_lower : (1 - θ) • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ A := by
    have := add_le_add_right h_difference_lower 1
    calc
      (1 - θ) • (1 : Matrix (Fin n) (Fin n) ℝ) =
          1 + -(θ • (1 : Matrix (Fin n) (Fin n) ℝ)) := by module
      _ ≤ 1 + (A - 1) := this
      _ = A := by noncomm_ring
  have h_A_upper : A ≤ (1 + θ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    have := add_le_add_right h_difference_upper 1
    calc
      A = 1 + (A - 1) := by noncomm_ring
      _ ≤ 1 + θ • (1 : Matrix (Fin n) (Fin n) ℝ) := this
      _ = (1 + θ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by module
  have h_lower_nonneg :
      0 ≤ (1 - θ) • (1 : Matrix (Fin n) (Fin n) ℝ) :=
    smul_nonneg h_one_sub_pos.le zero_le_one
  have h_lower_unit :
      IsUnit ((1 - θ) • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact (isUnit_iff_ne_zero.mpr h_one_sub_pos.ne').map (algebraMap ℝ _)
  have h_A_nonneg : 0 ≤ A := h_lower_nonneg.trans h_A_lower
  have h_A_unit : IsUnit A := by
    have h_one_sub_norm : ‖1 - A‖ < 1 := by
      rw [← norm_neg (1 - A), neg_sub]
      exact hA_close.trans_lt hθ_lt
    simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one h_one_sub_norm
  have h_A_inverse_mul : A⁻¹ * A = 1 :=
    Matrix.nonsing_inv_mul A (A.isUnit_iff_isUnit_det.mp h_A_unit)
  have h_A_mul_inverse : A * A⁻¹ = 1 :=
    Matrix.mul_nonsing_inv A (A.isUnit_iff_isUnit_det.mp h_A_unit)
  have h_mul_scalar (r : ℝ) :
      A * (r • (1 : Matrix (Fin n) (Fin n) ℝ)) = r • A := by
    rw [mul_smul_comm, mul_one]
  -- Conjugating each inverse difference by `A` reduces it to a product of commuting
  -- nonnegative matrices.
  have h_inverse_lower :
      (1 / (1 + θ) : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ A⁻¹ := by
    rw [Matrix.le_iff]
    refine (Matrix.IsUnit.posSemidef_star_left_conjugate_iff
      (U := A) (x := A⁻¹ - (1 / (1 + θ)) • 1) h_A_unit).mp ?_
    have h_upper_difference : 0 ≤ (1 + θ) • (1 : Matrix (Fin n) (Fin n) ℝ) - A :=
      sub_nonneg.mpr h_A_upper
    have h_commute : Commute A ((1 + θ) • (1 : Matrix (Fin n) (Fin n) ℝ) - A) := by
      exact ((Commute.one_right A).smul_right (1 + θ)).sub_right (Commute.refl A)
    have h_product :
        0 ≤ A * ((1 + θ) • (1 : Matrix (Fin n) (Fin n) ℝ) - A) :=
      Commute.mul_nonneg h_A_nonneg h_upper_difference h_commute
    have h_reciprocal_nonneg : 0 ≤ 1 / (1 + θ) := by
      positivity
    have h_scaled_product :
        0 ≤ (1 / (1 + θ)) •
          (A * ((1 + θ) • (1 : Matrix (Fin n) (Fin n) ℝ) - A)) :=
      smul_nonneg h_reciprocal_nonneg h_product
    have h_scaled_product_posSemidef :
        ((1 / (1 + θ)) •
          (A * ((1 + θ) • (1 : Matrix (Fin n) (Fin n) ℝ) - A))).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp h_scaled_product
    have h_conjugate :
        star A * (A⁻¹ - (1 / (1 + θ)) • 1) * A =
          (1 / (1 + θ)) •
            (A * ((1 + θ) • (1 : Matrix (Fin n) (Fin n) ℝ) - A)) := by
      have h_reciprocal : (1 / (1 + θ)) * (1 + θ) = 1 := by
        field_simp
      simp only [hA.star_eq, mul_sub, sub_mul, h_A_mul_inverse, one_mul, h_mul_scalar,
        smul_mul_assoc, smul_sub, smul_smul, h_reciprocal, one_smul]
    exact h_conjugate.symm ▸ h_scaled_product_posSemidef
  have h_inverse_upper :
      A⁻¹ ≤ (1 / (1 - θ) : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    rw [Matrix.le_iff]
    refine (Matrix.IsUnit.posSemidef_star_left_conjugate_iff
      (U := A) (x := (1 / (1 - θ)) • 1 - A⁻¹) h_A_unit).mp ?_
    have h_lower_difference : 0 ≤ A - (1 - θ) • (1 : Matrix (Fin n) (Fin n) ℝ) :=
      sub_nonneg.mpr h_A_lower
    have h_commute : Commute A (A - (1 - θ) • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
      exact (Commute.refl A).sub_right ((Commute.one_right A).smul_right (1 - θ))
    have h_product :
        0 ≤ A * (A - (1 - θ) • (1 : Matrix (Fin n) (Fin n) ℝ)) :=
      Commute.mul_nonneg h_A_nonneg h_lower_difference h_commute
    have h_reciprocal_nonneg : 0 ≤ 1 / (1 - θ) := by
      positivity
    have h_scaled_product :
        0 ≤ (1 / (1 - θ)) •
          (A * (A - (1 - θ) • (1 : Matrix (Fin n) (Fin n) ℝ))) :=
      smul_nonneg h_reciprocal_nonneg h_product
    have h_scaled_product_posSemidef :
        ((1 / (1 - θ)) •
          (A * (A - (1 - θ) • (1 : Matrix (Fin n) (Fin n) ℝ)))).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp h_scaled_product
    have h_conjugate :
        star A * ((1 / (1 - θ)) • 1 - A⁻¹) * A =
          (1 / (1 - θ)) •
            (A * (A - (1 - θ) • (1 : Matrix (Fin n) (Fin n) ℝ))) := by
      have h_reciprocal : (1 / (1 - θ)) * (1 - θ) = 1 := by
        field_simp
      simp only [hA.star_eq, mul_sub, sub_mul, h_A_mul_inverse, one_mul, h_mul_scalar,
        smul_mul_assoc, smul_sub, smul_smul, h_reciprocal, one_smul]
    exact h_conjugate.symm ▸ h_scaled_product_posSemidef
  exact ⟨h_inverse_lower, h_inverse_upper⟩

/-- The inverse of a matrix less than one from the identity satisfies the expected
pointwise norm estimate. -/
private lemma inverseEuclideanCLM_apply_norm_le
    (A : Matrix (Fin n) (Fin n) ℝ) (hθ_lt : θ < 1)
    (hA_close : ‖A - 1‖ ≤ θ) (v : EuclideanSpace ℝ (Fin n)) :
    ‖(Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _) A⁻¹ v‖ ≤
      (1 / (1 - θ)) * ‖v‖ := by
  have h_one_sub_pos : 0 < 1 - θ := sub_pos.mpr hθ_lt
  have h_A_unit : IsUnit A := by
    have h_one_sub_norm : ‖1 - A‖ < 1 := by
      rw [← norm_neg (1 - A), neg_sub]
      exact hA_close.trans_lt hθ_lt
    simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one h_one_sub_norm
  have h_A_mul_inverse : A * A⁻¹ = 1 :=
    Matrix.mul_nonsing_inv A (A.isUnit_iff_isUnit_det.mp h_A_unit)
  let u := (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _) A⁻¹ v
  have h_A_u :
      (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _) A u = v := by
    dsimp only [u]
    change (((Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _) A) *
      ((Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _) A⁻¹)) v = v
    rw [← map_mul, h_A_mul_inverse, map_one, one_apply_eq_self]
  have h_error_u :
      ‖u - (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _) A u‖ ≤
        θ * ‖u‖ := by
    calc
      ‖u - (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _) A u‖ =
          ‖(Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _) (1 - A) u‖ := by
        rw [map_sub, map_one, sub_apply, one_apply_eq_self]
      _ ≤ ‖1 - A‖ * ‖u‖ :=
        ((Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _) (1 - A)).le_opNorm u
      _ = ‖A - 1‖ * ‖u‖ := by rw [← norm_neg (A - 1), neg_sub]
      _ ≤ θ * ‖u‖ := mul_le_mul_of_nonneg_right hA_close (norm_nonneg u)
  have h_u_bound : (1 - θ) * ‖u‖ ≤ ‖v‖ := by
    have h_triangle : ‖u‖ ≤ ‖u - (Matrix.toEuclideanCLM :
        Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _) A u‖ +
        ‖(Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _) A u‖ := by
      simpa only [sub_add_cancel] using norm_add_le (u -
        (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _) A u)
        ((Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _) A u)
    calc
      (1 - θ) * ‖u‖ ≤
          ‖(Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _) A u‖ := by
        linarith
      _ = ‖v‖ := congrArg norm h_A_u
  change ‖u‖ ≤ (1 / (1 - θ)) * ‖v‖
  have h_reciprocal_nonneg : 0 ≤ 1 / (1 - θ) := by
    positivity
  calc
    ‖u‖ = (1 / (1 - θ)) * ((1 - θ) * ‖u‖) := by field_simp
    _ ≤ (1 / (1 - θ)) * ‖v‖ :=
      mul_le_mul_of_nonneg_left h_u_bound h_reciprocal_nonneg

/-- The inverse matrix map has operator norm at most `(1 - θ)⁻¹` when the matrix is within
`θ < 1` of the identity. -/
private lemma inverseEuclideanCLMNormLe
    (A : Matrix (Fin n) (Fin n) ℝ) (hθ_lt : θ < 1)
    (hA_close : ‖A - 1‖ ≤ θ) :
    ‖(Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _) A⁻¹‖ ≤
      1 / (1 - θ) := by
  -- Upgrade the pointwise bound to an operator-norm bound.
  have h_reciprocal_nonneg : 0 ≤ 1 / (1 - θ) := by
    positivity
  exact ((Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _) A⁻¹).opNorm_le_bound
    h_reciprocal_nonneg (inverseEuclideanCLM_apply_norm_le (θ := θ) A hθ_lt hA_close)

/-- The inverse of a matrix within `θ < 1` of the identity differs from the identity by
norm at most `θ / (1 - θ)`. -/
private lemma inverseMatrixNormSubOneLe
    (A : Matrix (Fin n) (Fin n) ℝ) (hθ_lt : θ < 1)
    (hA_close : ‖A - 1‖ ≤ θ) : ‖A⁻¹ - 1‖ ≤ θ / (1 - θ) := by
  have h_one_sub_pos : 0 < 1 - θ := sub_pos.mpr hθ_lt
  have h_A_unit : IsUnit A := by
    have h_one_sub_norm : ‖1 - A‖ < 1 := by
      rw [← norm_neg (1 - A), neg_sub]
      exact hA_close.trans_lt hθ_lt
    simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one h_one_sub_norm
  have h_inverse_norm : ‖A⁻¹‖ ≤ 1 / (1 - θ) :=
    inverseEuclideanCLMNormLe (θ := θ) A hθ_lt hA_close
  have h_reciprocal_nonneg : 0 ≤ 1 / (1 - θ) := by
    positivity
  -- Factor the inverse error and apply submultiplicativity.
  have h_inverse_mul : A⁻¹ * A = 1 :=
    Matrix.nonsing_inv_mul A (A.isUnit_iff_isUnit_det.mp h_A_unit)
  have h_error_factor : A⁻¹ - 1 = A⁻¹ * (1 - A) := by
    calc
      A⁻¹ - 1 = A⁻¹ - A⁻¹ * A := by rw [h_inverse_mul]
      _ = A⁻¹ * (1 - A) := by noncomm_ring
  rw [h_error_factor]
  calc
    ‖A⁻¹ * (1 - A)‖ ≤ ‖A⁻¹‖ * ‖1 - A‖ := Matrix.l2_opNorm_mul _ _
    _ = ‖A⁻¹‖ * ‖A - 1‖ := by rw [← norm_neg (A - 1), neg_sub]
    _ ≤ (1 / (1 - θ)) * θ :=
      mul_le_mul h_inverse_norm hA_close (norm_nonneg _) h_reciprocal_nonneg
    _ = θ / (1 - θ) := by ring

include h_smooth h_sub_smooth h_sub_compact h_hessian_close h_theta
  h_gradient_zero h_hessian_zero

/-- The Hessian of the convex conjugate lies between the reciprocal scalar Hessian
bounds in the Loewner order. -/
theorem hessian_mem_Icc (x : EuclideanSpace ℝ (Fin n)) :
    ConvexAnalysis.hessian (ConvexAnalysis.conjugate H) x ∈
      Set.Icc ((1 / (1 + θ) : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))
        ((1 / (1 - θ) : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  -- Rewrite the conjugate Hessian as an inverse and apply the Hermitian matrix estimate.
  have hθ_nonneg : 0 ≤ θ :=
    (norm_nonneg (ConvexAnalysis.hessian H 0 - 1)).trans (h_hessian_close 0)
  let z := Function.invFun (gradient H) x
  have h_bounds := inverseMatrixOrderBoundsOfNormSubOneLe (θ := θ)
    (ConvexAnalysis.hessian H z) (hessianIsHermitian (H := H) (h_smooth := h_smooth) z)
    hθ_nonneg h_theta (h_hessian_close z)
  rw [hessian_conjugate H θ h_smooth h_sub_smooth h_sub_compact h_hessian_close h_theta
    h_gradient_zero h_hessian_zero x]
  exact h_bounds

/-- The Hessian of the convex conjugate is pointwise within `θ / (1 - θ)` of the
identity in the Euclidean operator norm. -/
theorem hessianNorm_le (x : EuclideanSpace ℝ (Fin n)) :
    ‖ConvexAnalysis.hessian (ConvexAnalysis.conjugate H) x - 1‖ ≤ θ / (1 - θ) := by
  -- The norm projection of the same inverse-matrix estimate gives the desired bound.
  let z := Function.invFun (gradient H) x
  have h_bound := inverseMatrixNormSubOneLe (θ := θ)
    (ConvexAnalysis.hessian H z) h_theta (h_hessian_close z)
  rw [hessian_conjugate H θ h_smooth h_sub_smooth h_sub_compact h_hessian_close h_theta
    h_gradient_zero h_hessian_zero x]
  exact h_bound

/-- Subtracting the standard quadratic from the convex conjugate gives a smooth
function. -/
theorem conjugateSub_contDiff :
    ContDiff ℝ ⊤
      (ConvexAnalysis.conjugate H -
        (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) := by
  -- The standard quadratic is smooth, so smoothness is preserved by subtraction.
  have h_standard_formula :
      (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ) =
        fun x ↦ (1 / 2 : ℝ) * ‖x‖ ^ 2 := by
    funext x
    exact standardQuadratic_apply x
  have h_standard : ContDiff ℝ ⊤
      (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ) := by
    rw [h_standard_formula]
    exact contDiff_const.mul (contDiff_norm_sq ℝ)
  exact (conjugateContDiff H θ h_smooth h_sub_smooth h_sub_compact h_hessian_close h_theta
    h_gradient_zero h_hessian_zero).sub h_standard

omit h_smooth h_sub_smooth h_sub_compact h_hessian_close h_theta h_gradient_zero h_hessian_zero

/-- The gradient of the standard quadratic is the identity map. -/
private lemma gradient_standardQuadratic :
    gradient (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ) = id := by
  -- Differentiate the squared norm and cancel the scalar factor `1 / 2`.
  apply gradient_eq
  intro x
  rw [hasGradientAt_iff_hasFDerivAt]
  have h_deriv := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (1 / 2 : ℝ)
  have h_standard_formula :
      (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ) =
        fun y ↦ (1 / 2 : ℝ) * ‖y‖ ^ 2 := by
    funext y
    exact standardQuadratic_apply y
  have h_derivative_map :
      (1 / 2 : ℝ) • (2 • (innerSL ℝ) x) =
        (toDual ℝ (EuclideanSpace ℝ (Fin n))) x := by
    ext v
    simp only [smul_apply, innerSL_apply_apply, toDual_apply_apply]
    ring
  rw [h_standard_formula]
  exact h_deriv.congr_fderiv h_derivative_map

include h_smooth h_hessian_close h_theta

/-- Away from the original quadratic tail, the conjugate agrees with the standard
quadratic. -/
private lemma conjugate_eq_standardQuadratic_of_notMem_tsupport
    {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∉ tsupport (H - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ))) :
    ConvexAnalysis.conjugate H x = standardQuadratic x := by
  have h_tail_zero :
      H - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ) =ᶠ[𝓝 x] 0 := by
    rwa [← notMem_tsupport_iff_eventuallyEq]
  have h_H_eq_standard :
      H =ᶠ[𝓝 x] (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ) :=
    h_tail_zero.mono fun y hy ↦ sub_eq_zero.mp hy
  have h_gradient_x : gradient H x = x := by
    calc
      gradient H x = gradient (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ) x :=
        h_H_eq_standard.gradient_eq
      _ = x := congrFun gradient_standardQuadratic x
  have h_bij := (gradientInverseData H θ h_smooth h_hessian_close h_theta).1
  have h_inverse_x : Function.invFun (gradient H) x = x := by
    apply h_bij.1
    rw [Function.rightInverse_invFun h_bij.2 x, h_gradient_x]
  have h_value_x : H x = standardQuadratic x := h_H_eq_standard.self_of_nhds
  -- Substitute the fixed inverse-gradient point into the conjugate formula.
  rw [conjugate_eq_inner_invGradient H θ h_smooth h_hessian_close h_theta x,
    h_inverse_x, h_value_x, standardQuadratic_apply, real_inner_self_eq_norm_sq]
  ring

include h_sub_smooth h_sub_compact h_gradient_zero h_hessian_zero

/-- The topological support of the convex conjugate's quadratic tail is contained in
the topological support of the original quadratic tail. -/
theorem tsupport_conjugateSub_subset :
    tsupport
        (ConvexAnalysis.conjugate H -
          (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) ⊆
      tsupport (H - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) := by
  -- Pointwise vanishing off the original tail passes to topological support by closure.
  apply closure_minimal
  · intro x hx
    by_contra hx_original
    exact hx (sub_eq_zero.mpr
      (conjugate_eq_standardQuadratic_of_notMem_tsupport H θ h_smooth h_hessian_close
        h_theta hx_original))
  · exact isClosed_closure

/-- Subtracting the standard quadratic from the convex conjugate gives a compactly
supported function. -/
theorem conjugateSub_hasCompactSupport :
    HasCompactSupport
      (ConvexAnalysis.conjugate H -
        (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) := by
  -- The new closed support is a closed subset of the original compact support.
  exact IsCompact.of_isClosed_subset h_sub_compact isClosed_closure
    (tsupport_conjugateSub_subset H θ h_smooth h_sub_smooth h_sub_compact h_hessian_close
      h_theta h_gradient_zero h_hessian_zero)

omit h_sub_smooth h_sub_compact h_hessian_zero

/-- A gradient that vanishes at the origin has an inverse that fixes the origin. -/
private lemma invGradient_zero : Function.invFun (gradient H) 0 = 0 := by
  have h_bij := (gradientInverseData H θ h_smooth h_hessian_close h_theta).1
  -- Compare the gradients of both candidate preimages of zero.
  apply h_bij.1
  rw [Function.rightInverse_invFun h_bij.2 0, h_gradient_zero]

include h_sub_smooth h_sub_compact h_hessian_zero

/-- The origin is a global minimizer of the convex conjugate. -/
theorem conjugate_isMinOn :
    IsMinOn (ConvexAnalysis.conjugate H) Set.univ 0 := by
  rw [isMinOn_univ_iff]
  intro x
  have hθ_nonneg : 0 ≤ θ :=
    (norm_nonneg (ConvexAnalysis.hessian H 0 - 1)).trans (h_hessian_close 0)
  let c : ℝ≥0 := ⟨θ, hθ_nonneg⟩
  have h_close_c : ∀ z, ‖ConvexAnalysis.hessian H z - 1‖ ≤ (c : ℝ) := by
    intro z
    exact h_hessian_close z
  have h_approx := gradientApproximatesIdentity H h_smooth c h_close_c
  have hc : (c : ℝ) < 1 := h_theta
  have h_bij := (gradientInverseData H θ h_smooth h_hessian_close h_theta).1
  have h_max := (pairingSubUniqueMaximumAtInvGradient H c h_smooth h_approx hc h_bij x).1
  have h_competitor :
      ⟪x, (0 : EuclideanSpace ℝ (Fin n))⟫_ℝ - H 0 ≤
        ⟪x, Function.invFun (gradient H) x⟫_ℝ -
          H (Function.invFun (gradient H) x) :=
    h_max.2 ⟨0, rfl⟩
  have h_inverse_zero := invGradient_zero H θ h_smooth h_hessian_close h_theta h_gradient_zero
  -- Compare the attained maximum at `x` with the competitor `0`.
  calc
    ConvexAnalysis.conjugate H 0 =
        ⟪(0 : EuclideanSpace ℝ (Fin n)), Function.invFun (gradient H) 0⟫_ℝ -
          H (Function.invFun (gradient H) 0) :=
      conjugate_eq_inner_invGradient H θ h_smooth h_hessian_close h_theta 0
    _ = -H 0 := by
      simp [h_inverse_zero]
    _ = ⟪x, (0 : EuclideanSpace ℝ (Fin n))⟫_ℝ - H 0 := by simp
    _ ≤ ⟪x, Function.invFun (gradient H) x⟫_ℝ -
        H (Function.invFun (gradient H) x) := h_competitor
    _ = ConvexAnalysis.conjugate H x :=
      (conjugate_eq_inner_invGradient H θ h_smooth h_hessian_close h_theta x).symm

/-- Every global minimizer of the convex conjugate is the origin. -/
theorem eq_zero_of_conjugate_isMinOn (x : EuclideanSpace ℝ (Fin n))
    (hx : IsMinOn (ConvexAnalysis.conjugate H) Set.univ x) : x = 0 := by
  have h_origin_min := conjugate_isMinOn H θ h_smooth h_sub_smooth h_sub_compact
    h_hessian_close h_theta h_gradient_zero h_hessian_zero
  have h_value_eq : ConvexAnalysis.conjugate H x = ConvexAnalysis.conjugate H 0 :=
    le_antisymm (isMinOn_univ_iff.mp hx 0) (isMinOn_univ_iff.mp h_origin_min x)
  have hθ_nonneg : 0 ≤ θ :=
    (norm_nonneg (ConvexAnalysis.hessian H 0 - 1)).trans (h_hessian_close 0)
  let c : ℝ≥0 := ⟨θ, hθ_nonneg⟩
  have h_close_c : ∀ z, ‖ConvexAnalysis.hessian H z - 1‖ ≤ (c : ℝ) := by
    intro z
    exact h_hessian_close z
  have h_approx := gradientApproximatesIdentity H h_smooth c h_close_c
  have hc : (c : ℝ) < 1 := h_theta
  have h_bij := (gradientInverseData H θ h_smooth h_hessian_close h_theta).1
  have h_unique := (pairingSubUniqueMaximumAtInvGradient H c h_smooth h_approx hc h_bij x).2
  have h_inverse_zero := invGradient_zero H θ h_smooth h_hessian_close h_theta h_gradient_zero
  have h_competitor_eq :
      ⟪x, (0 : EuclideanSpace ℝ (Fin n))⟫_ℝ - H 0 =
        ⟪x, Function.invFun (gradient H) x⟫_ℝ -
          H (Function.invFun (gradient H) x) := by
    calc
      ⟪x, (0 : EuclideanSpace ℝ (Fin n))⟫_ℝ - H 0 = -H 0 := by simp
      _ = ConvexAnalysis.conjugate H 0 := by
        rw [conjugate_eq_inner_invGradient H θ h_smooth h_hessian_close h_theta 0,
          h_inverse_zero]
        simp
      _ = ConvexAnalysis.conjugate H x := h_value_eq.symm
      _ = ⟪x, Function.invFun (gradient H) x⟫_ℝ -
          H (Function.invFun (gradient H) x) :=
        conjugate_eq_inner_invGradient H θ h_smooth h_hessian_close h_theta x
  have h_inverse_x : Function.invFun (gradient H) x = 0 :=
    (h_unique 0 h_competitor_eq).symm
  -- Apply the original gradient to the equality of inverse-gradient points.
  calc
    x = gradient H (Function.invFun (gradient H) x) :=
      (Function.rightInverse_invFun h_bij.2 x).symm
    _ = gradient H 0 := congrArg (gradient H) h_inverse_x
    _ = 0 := h_gradient_zero

/-- The Hessian of the convex conjugate at the origin is the identity. -/
theorem hessian_conjugate_zero :
    ConvexAnalysis.hessian (ConvexAnalysis.conjugate H) 0 = 1 := by
  have h_inverse_zero := invGradient_zero H θ h_smooth h_hessian_close h_theta h_gradient_zero
  -- Evaluate the inverse-Hessian formula at the fixed inverse-gradient point.
  rw [hessian_conjugate H θ h_smooth h_sub_smooth h_sub_compact h_hessian_close h_theta
    h_gradient_zero h_hessian_zero 0, h_inverse_zero, h_hessian_zero]
  exact inv_one

end

section SmoothConjugacy

/-- The smooth convex-conjugacy data associated with a uniformly small Hessian
perturbation of the standard quadratic. -/
structure SmoothConjugateData {n : ℕ}
    (H : EuclideanSpace ℝ (Fin n) → ℝ) (theta : ℝ) : Prop where
  gradientBijective : Function.Bijective (gradient H)
  conjugateSmooth : ContDiff ℝ ∞ (ConvexAnalysis.conjugate H)
  conjugateTailSmooth : ContDiff ℝ ∞
    (ConvexAnalysis.conjugate H -
      (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ))
  gradientConjugate :
    gradient (ConvexAnalysis.conjugate H) = Function.invFun (gradient H)
  hessianConjugate : ∀ x,
    ConvexAnalysis.hessian (ConvexAnalysis.conjugate H) x =
      (ConvexAnalysis.hessian H (Function.invFun (gradient H) x))⁻¹
  hessianBounds : ∀ x,
    ConvexAnalysis.hessian (ConvexAnalysis.conjugate H) x ∈
      Set.Icc ((1 / (1 + theta) : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))
        ((1 / (1 - theta) : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))
  hessianNorm : ∀ x,
    ‖ConvexAnalysis.hessian (ConvexAnalysis.conjugate H) x - 1‖ ≤
      theta / (1 - theta)
  supportSubset :
    tsupport
        (ConvexAnalysis.conjugate H -
          (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) ⊆
      tsupport (H - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ))
  compactTail : HasCompactSupport
    (ConvexAnalysis.conjugate H -
      (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ))
  strongConvex : StrongConvexOn Set.univ (1 / (1 + theta))
    (ConvexAnalysis.conjugate H)
  uniqueMinimizer : ∀ x, IsMinOn (ConvexAnalysis.conjugate H) Set.univ x ↔ x = 0
  hessianZero : ConvexAnalysis.hessian (ConvexAnalysis.conjugate H) 0 = 1

/-- The gradient of a `C∞` real-valued function on Euclidean space is `C∞`. -/
private lemma gradientContDiffInfty {n : ℕ} (H : EuclideanSpace ℝ (Fin n) → ℝ)
    (hH : ContDiff ℝ ∞ H) : ContDiff ℝ ∞ (gradient H) := by
  -- Express the gradient through the Fréchet derivative and the Riesz equivalence.
  have hGradientFormula :
      gradient H = fun x ↦ (toDual ℝ _).symm (fderiv ℝ H x) := by
    funext x
    rfl
  have hOrder : (∞ : ℕ∞ω) + 1 ≤ ∞ := by simp
  rw [hGradientFormula]
  exact (toDual ℝ _).symm.contDiff.comp
    (ContDiff.fderiv_right hH (m := ∞) hOrder)

/-- A uniform Hessian bound makes a `C∞` gradient a Lipschitz perturbation of the
identity. -/
private lemma gradientApproximatesIdentityInfty {n : ℕ}
    (H : EuclideanSpace ℝ (Fin n) → ℝ) (hH : ContDiff ℝ ∞ H) (c : ℝ≥0)
    (hClose : ∀ z, ‖ConvexAnalysis.hessian H z - 1‖ ≤ c) :
    ApproximatesLinearOn (gradient H)
      (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) Set.univ c := by
  -- Apply the mean-value estimate to the difference from the identity.
  rw [ApproximatesLinearOn.approximatesLinearOn_iff_lipschitzOnWith,
    lipschitzOnWith_univ]
  have hGradientSmooth := gradientContDiffInfty H hH
  have hDifferenceSmooth := hGradientSmooth.sub contDiff_id
  have hInftyNeZero : (∞ : ℕ∞ω) ≠ 0 := by simp
  refine lipschitzWith_of_nnnorm_fderiv_le
    (hDifferenceSmooth.differentiable hInftyNeZero) (fun z ↦ ?_)
  rw [fderiv_sub (hGradientSmooth.differentiable hInftyNeZero).differentiableAt
    (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).differentiableAt,
    ContinuousLinearMap.fderiv, ← ConvexAnalysis.toEuclideanCLM_hessian,
    ← map_one (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _), ← map_sub]
  exact_mod_cast hClose z

/-- A `C∞` global perturbation of the identity by a contraction has a `C∞`
inverse. -/
private lemma smoothDiffeomorphOfApproximatesIdentityInfty
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : E → E) (c : ℝ≥0) (hf : ContDiff ℝ ∞ f)
    (hApprox : ApproximatesLinearOn f (1 : E →L[ℝ] E) Set.univ c)
    (hc : (c : ℝ) < 1) :
    ∃ e : E ≃ₘ[ℝ] E, (∀ x, e x = f x) ∧ ContDiff ℝ ∞ (e.symm : E → E) := by
  classical
  have hInftyNeZero : (∞ : ℕ∞ω) ≠ 0 := by simp
  have hThreshold :
      Subsingleton E ∨
        c < ‖((ContinuousLinearEquiv.refl ℝ E).symm : E →L[ℝ] E)‖₊⁻¹ := by
    by_cases hE : Subsingleton E
    · exact Or.inl hE
    · right
      -- Local instance justification (nontriviality): the identity-map norm is one
      -- precisely in the non-subsingleton branch.
      letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
      simp only [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl,
        ContinuousLinearMap.nnnorm_id, inv_one]
      exact_mod_cast hc
  have hApproxRefl :
      ApproximatesLinearOn f (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E)
        Set.univ c := by
    have hRefl : (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) = 1 := by
      ext x
      rfl
    rw [hRefl]
    exact hApprox
  let home : E ≃ₜ E := ApproximatesLinearOn.toHomeomorph f hApproxRefl hThreshold
  have hHomeApply (x : E) : home x = f x := by rfl
  have hHomeFun : (home : E → E) = f := funext hHomeApply
  have hHomeSmooth : ContDiff ℝ ∞ (home : E → E) := by
    rw [hHomeFun]
    exact hf
  have hRemainderLipschitz : LipschitzWith c (f - ⇑(1 : E →L[ℝ] E)) := by
    rw [← lipschitzOnWith_univ]
    exact hApprox.lipschitzOnWith
  have hDerivativeClose (x : E) : ‖fderiv ℝ f x - 1‖ < 1 := by
    have hfDiff : DifferentiableAt ℝ f x :=
      (hf.differentiable hInftyNeZero).differentiableAt
    have hIdDiff : DifferentiableAt ℝ (1 : E →L[ℝ] E) x :=
      (1 : E →L[ℝ] E).differentiableAt
    have hFderivSub :
        fderiv ℝ (f - ⇑(1 : E →L[ℝ] E)) x = fderiv ℝ f x - 1 := by
      simpa only [ContinuousLinearMap.fderiv] using fderiv_sub hfDiff hIdDiff
    calc
      ‖fderiv ℝ f x - 1‖ = ‖fderiv ℝ (f - ⇑(1 : E →L[ℝ] E)) x‖ :=
        congrArg norm hFderivSub.symm
      _ ≤ c := norm_fderiv_le_of_lipschitz ℝ hRemainderLipschitz
      _ < 1 := hc
  have hDerivativeEquiv (x : E) :
      ∃ e : E ≃L[ℝ] E, (e : E →L[ℝ] E) = fderiv ℝ f x :=
    existsContinuousLinearEquivOfNormSubIdentityLtOne _ (hDerivativeClose x)
  choose f' hf' using hDerivativeEquiv
  have hHomeDeriv (x : E) : HasFDerivAt home (f' x : E →L[ℝ] E) x := by
    rw [hf' x, hHomeFun]
    exact (hf.differentiable hInftyNeZero).differentiableAt.hasFDerivAt
  have hInverseSmooth : ContDiff ℝ ∞ (home.symm : E → E) :=
    home.contDiff_symm hHomeDeriv hHomeSmooth
  let e : E ≃ₘ[ℝ] E :=
    { toEquiv := home.toEquiv
      contMDiff_toFun := hHomeSmooth.contMDiff
      contMDiff_invFun := hInverseSmooth.contMDiff }
  exact ⟨e, fun x ↦ hHomeApply x, hInverseSmooth⟩

/-- The inverse of a `C∞` gradient satisfying the contraction estimate is again
`C∞`. -/
private lemma gradientInverseDataInfty {n : ℕ}
    (H : EuclideanSpace ℝ (Fin n) → ℝ) (theta : ℝ)
    (hH : ContDiff ℝ ∞ H)
    (hClose : ∀ z, ‖ConvexAnalysis.hessian H z - 1‖ ≤ theta)
    (hTheta : theta < 1) :
    Function.Bijective (gradient H) ∧
      ContDiff ℝ ∞ (Function.invFun (gradient H)) := by
  have hThetaNonneg : 0 ≤ theta :=
    (norm_nonneg (ConvexAnalysis.hessian H 0 - 1)).trans (hClose 0)
  let c : ℝ≥0 := ⟨theta, hThetaNonneg⟩
  have hCloseC : ∀ z, ‖ConvexAnalysis.hessian H z - 1‖ ≤ (c : ℝ) := hClose
  have hApprox := gradientApproximatesIdentityInfty H hH c hCloseC
  have hc : (c : ℝ) < 1 := hTheta
  obtain ⟨e, he, hInverseSmooth⟩ := smoothDiffeomorphOfApproximatesIdentityInfty
    (gradient H) c (gradientContDiffInfty H hH) hApprox hc
  have hEFun : (e : _ → _) = gradient H := funext he
  have hBij : Function.Bijective (gradient H) := by
    rw [← hEFun]
    exact e.bijective
  have hRightInverse : Function.RightInverse (e.symm : _ → _) (gradient H) := by
    intro x
    rw [← he (e.symm x)]
    exact e.apply_symm_apply x
  have hInvFun : Function.invFun (gradient H) = (e.symm : _ → _) :=
    Function.invFun_eq_of_injective_of_rightInverse hBij.1 hRightInverse
  refine ⟨hBij, ?_⟩
  rw [hInvFun]
  exact hInverseSmooth

/-- Along every nonconstant affine line, a `C∞` potential whose gradient approximates
the identity is strictly convex. -/
private lemma strictConvexOnAffineLineOfGradientApproximatesIdentityInfty
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (H : E → ℝ) (c : ℝ≥0) (hH : ContDiff ℝ ∞ H)
    (hApprox : ApproximatesLinearOn (gradient H) (1 : E →L[ℝ] E) Set.univ c)
    (hc : (c : ℝ) < 1) (z d : E) (hd : d ≠ 0) :
    StrictConvexOn ℝ Set.univ (fun t : ℝ ↦ H (z + t • d)) := by
  have hInftyNeZero : (∞ : ℕ∞ω) ≠ 0 := by simp
  have hHDiff : Differentiable ℝ H := hH.differentiable hInftyNeZero
  have hLineDeriv (t : ℝ) :
      HasDerivAt (fun s : ℝ ↦ H (z + s • d))
        ⟪gradient H (z + t • d), d⟫_ℝ t :=
    hasDerivAtAlongAffineLine hHDiff z d t
  have hDerivStrict : StrictMono (deriv fun t : ℝ ↦ H (z + t • d)) := by
    intro a b hab
    rw [(hLineDeriv a).deriv, (hLineDeriv b).deriv]
    have hScale : z + b • d - (z + a • d) = (b - a) • d := by module
    have hPointsNe : z + b • d ≠ z + a • d := by
      intro hPoints
      have hSmul : (b - a) • d = 0 := by
        rw [← hScale]
        exact sub_eq_zero.mpr hPoints
      exact hd (smul_eq_zero.mp hSmul |>.resolve_left (sub_ne_zero.mpr hab.ne'))
    have hPositive := innerMapSubMapSubPosOfApproximatesIdentity
      (gradient H) c hApprox hc hPointsNe
    rw [hScale, inner_smul_right, inner_sub_left] at hPositive
    nlinarith
  exact hDerivStrict.strictConvexOn_univ_of_deriv
    (hH.comp (contDiff_const.add (contDiff_id.smul_const d))).continuous

/-- A `C∞` potential whose gradient is a contraction perturbation of the identity
has a unique maximizer in each conjugate fiber. -/
private lemma pairingSubUniqueMaximumAtInvGradientInfty
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (H : E → ℝ) (c : ℝ≥0) (hH : ContDiff ℝ ∞ H)
    (hApprox : ApproximatesLinearOn (gradient H) (1 : E →L[ℝ] E) Set.univ c)
    (hc : (c : ℝ) < 1) (hBij : Function.Bijective (gradient H)) (x : E) :
    IsGreatest (Set.range (fun y ↦ ⟪x, y⟫_ℝ - H y))
        (⟪x, Function.invFun (gradient H) x⟫_ℝ - H (Function.invFun (gradient H) x)) ∧
      ∀ y, ⟪x, y⟫_ℝ - H y =
          ⟪x, Function.invFun (gradient H) x⟫_ℝ - H (Function.invFun (gradient H) x) →
        y = Function.invFun (gradient H) x := by
  let z := Function.invFun (gradient H) x
  have hGradientZ : gradient H z = x := Function.rightInverse_invFun hBij.2 x
  have hInftyNeZero : (∞ : ℕ∞ω) ≠ 0 := by simp
  have hHDiff : Differentiable ℝ H := hH.differentiable hInftyNeZero
  have hStrictSupport {y : E} (hy : y ≠ z) :
      ⟪x, y⟫_ℝ - H y < ⟪x, z⟫_ℝ - H z := by
    have hd : y - z ≠ 0 := sub_ne_zero.mpr hy
    have hLineConvex := strictConvexOnAffineLineOfGradientApproximatesIdentityInfty
      H c hH hApprox hc z (y - z) hd
    have hLineDeriv := hasDerivAtAlongAffineLine hHDiff z (y - z) 0
    have hSlope := hLineConvex.lt_slope_of_hasDerivAt
      (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hLineDeriv
    have hEndpoint : z + (1 : ℝ) • (y - z) = y := by module
    have hTangent : ⟪x, y - z⟫_ℝ < H y - H z := by
      rw [slope_def_field] at hSlope
      rw [hEndpoint, zero_smul, add_zero, hGradientZ] at hSlope
      simpa only [sub_zero, div_one] using hSlope
    rw [inner_sub_right] at hTangent
    linarith
  have hMaximal (y : E) : ⟪x, y⟫_ℝ - H y ≤ ⟪x, z⟫_ℝ - H z := by
    by_cases hy : y = z
    · rw [hy]
    · exact (hStrictSupport hy).le
  constructor
  · constructor
    · exact ⟨z, rfl⟩
    · rintro _ ⟨y, rfl⟩
      exact hMaximal y
  · intro y hy
    by_contra hyz
    exact (hStrictSupport hyz).ne hy

/-- The smooth convex conjugate is attained at the inverse-gradient point. -/
private lemma conjugate_eq_inner_invGradientInfty {n : ℕ}
    (H : EuclideanSpace ℝ (Fin n) → ℝ) (theta : ℝ)
    (hH : ContDiff ℝ ∞ H)
    (hClose : ∀ z, ‖ConvexAnalysis.hessian H z - 1‖ ≤ theta)
    (hTheta : theta < 1) (x : EuclideanSpace ℝ (Fin n)) :
    ConvexAnalysis.conjugate H x =
      ⟪x, Function.invFun (gradient H) x⟫_ℝ - H (Function.invFun (gradient H) x) := by
  have hThetaNonneg : 0 ≤ theta :=
    (norm_nonneg (ConvexAnalysis.hessian H 0 - 1)).trans (hClose 0)
  let c : ℝ≥0 := ⟨theta, hThetaNonneg⟩
  have hCloseC : ∀ z, ‖ConvexAnalysis.hessian H z - 1‖ ≤ (c : ℝ) := hClose
  have hApprox := gradientApproximatesIdentityInfty H hH c hCloseC
  have hc : (c : ℝ) < 1 := hTheta
  have hBij := (gradientInverseDataInfty H theta hH hClose hTheta).1
  rw [ConvexAnalysis.conjugate_apply]
  exact (pairingSubUniqueMaximumAtInvGradientInfty H c hH hApprox hc hBij x).1.csSup_eq

/-- The smooth conjugate has gradient equal to the inverse of the original gradient. -/
private lemma gradient_conjugateInfty {n : ℕ}
    (H : EuclideanSpace ℝ (Fin n) → ℝ) (theta : ℝ)
    (hH : ContDiff ℝ ∞ H)
    (hClose : ∀ z, ‖ConvexAnalysis.hessian H z - 1‖ ≤ theta)
    (hTheta : theta < 1) :
    gradient (ConvexAnalysis.conjugate H) = Function.invFun (gradient H) := by
  let g := Function.invFun (gradient H)
  have hInverseData := gradientInverseDataInfty H theta hH hClose hTheta
  have hBij : Function.Bijective (gradient H) := hInverseData.1
  have hgSmooth : ContDiff ℝ ∞ g := hInverseData.2
  have hInftyNeZero : (∞ : ℕ∞ω) ≠ 0 := by simp
  apply gradient_eq
  intro x
  have hgDeriv : HasFDerivAt g (fderiv ℝ g x) x :=
    (hgSmooth.differentiable hInftyNeZero).differentiableAt.hasFDerivAt
  have hHDeriv : HasFDerivAt H (toDual ℝ _ (gradient H (g x))) (g x) :=
    (hH.differentiable hInftyNeZero).differentiableAt.hasGradientAt.hasFDerivAt
  have hGradientG : gradient H (g x) = x := Function.rightInverse_invFun hBij.2 x
  have hPairingDeriv := (hasFDerivAt_id x).inner ℝ hgDeriv
  have hComposedDeriv := hHDeriv.comp x hgDeriv
  have hDifferenceDeriv := hPairingDeriv.sub hComposedDeriv
  have hDerivativeEq :
      (fderivInnerCLM ℝ (x, g x)).comp
          ((1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).prod
            (fderiv ℝ g x)) -
        (toDual ℝ _ (gradient H (g x))).comp (fderiv ℝ g x) =
          toDual ℝ _ (g x) := by
    ext v
    simp only [sub_apply, ContinuousLinearMap.comp_apply, fderivInnerCLM_apply,
      ContinuousLinearMap.prod_apply, one_apply_eq_self, toDual_apply_apply, hGradientG]
    rw [real_inner_comm v (g x)]
    ring
  have hExpressionGradient :
      HasGradientAt (fun y ↦ ⟪y, g y⟫_ℝ - H (g y)) (g x) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    exact hDifferenceDeriv.congr_fderiv hDerivativeEq
  have hFormula : ConvexAnalysis.conjugate H = fun y ↦ ⟪y, g y⟫_ℝ - H (g y) := by
    funext y
    exact conjugate_eq_inner_invGradientInfty H theta hH hClose hTheta y
  rw [hFormula]
  exact hExpressionGradient

/-- The convex conjugate of a `C∞` small quadratic perturbation is `C∞`. -/
private lemma conjugateContDiffInfty {n : ℕ}
    (H : EuclideanSpace ℝ (Fin n) → ℝ) (theta : ℝ)
    (hH : ContDiff ℝ ∞ H)
    (hClose : ∀ z, ‖ConvexAnalysis.hessian H z - 1‖ ≤ theta)
    (hTheta : theta < 1) : ContDiff ℝ ∞ (ConvexAnalysis.conjugate H) := by
  have hFormula : ConvexAnalysis.conjugate H = fun x ↦
      ⟪x, Function.invFun (gradient H) x⟫_ℝ - H (Function.invFun (gradient H) x) := by
    funext x
    exact conjugate_eq_inner_invGradientInfty H theta hH hClose hTheta x
  have hInverseSmooth := (gradientInverseDataInfty H theta hH hClose hTheta).2
  rw [hFormula]
  exact (contDiff_id.inner ℝ hInverseSmooth).sub (hH.comp hInverseSmooth)

/-- The Hessian of a smooth conjugate is the inverse original Hessian at the inverse
gradient point. -/
private lemma hessian_conjugateInfty {n : ℕ}
    (H : EuclideanSpace ℝ (Fin n) → ℝ) (theta : ℝ)
    (hH : ContDiff ℝ ∞ H)
    (hClose : ∀ z, ‖ConvexAnalysis.hessian H z - 1‖ ≤ theta)
    (hTheta : theta < 1) (x : EuclideanSpace ℝ (Fin n)) :
    ConvexAnalysis.hessian (ConvexAnalysis.conjugate H) x =
      (ConvexAnalysis.hessian H (Function.invFun (gradient H) x))⁻¹ := by
  let g := Function.invFun (gradient H)
  let A := ConvexAnalysis.hessian H (g x)
  let B := ConvexAnalysis.hessian (ConvexAnalysis.conjugate H) x
  have hInverseData := gradientInverseDataInfty H theta hH hClose hTheta
  have hBij : Function.Bijective (gradient H) := hInverseData.1
  have hInftyNeZero : (∞ : ℕ∞ω) ≠ 0 := by simp
  have hGradientDiff : Differentiable ℝ (gradient H) :=
    (gradientContDiffInfty H hH).differentiable hInftyNeZero
  have hgDiff : Differentiable ℝ g := hInverseData.2.differentiable hInftyNeZero
  have hGradientG (y : EuclideanSpace ℝ (Fin n)) : gradient H (g y) = y :=
    Function.rightInverse_invFun hBij.2 y
  have hGGradient (y : EuclideanSpace ℝ (Fin n)) : g (gradient H y) = y :=
    Function.leftInverse_invFun hBij.1 y
  have hDerivMulRight : fderiv ℝ (gradient H) (g x) * fderiv ℝ g x = 1 := by
    have hChain := fderiv_comp (𝕜 := ℝ) (f := g) (g := gradient H) (x := x)
      hGradientDiff.differentiableAt hgDiff.differentiableAt
    have hComp : gradient H ∘ g = id := funext hGradientG
    calc
      fderiv ℝ (gradient H) (g x) * fderiv ℝ g x =
          (fderiv ℝ (gradient H) (g x)).comp (fderiv ℝ g x) :=
        ContinuousLinearMap.mul_def _ _
      _ = fderiv ℝ (gradient H ∘ g) x := hChain.symm
      _ = fderiv ℝ id x := congrArg (fun k ↦ fderiv ℝ k x) hComp
      _ = 1 := fderiv_id
  have hDerivMulLeft : fderiv ℝ g x * fderiv ℝ (gradient H) (g x) = 1 := by
    have hChain := fderiv_comp (𝕜 := ℝ) (f := gradient H) (g := g) (x := g x)
      hgDiff.differentiableAt hGradientDiff.differentiableAt
    have hComp : g ∘ gradient H = id := funext hGGradient
    calc
      fderiv ℝ g x * fderiv ℝ (gradient H) (g x) =
          (fderiv ℝ g x).comp (fderiv ℝ (gradient H) (g x)) :=
        ContinuousLinearMap.mul_def _ _
      _ = (fderiv ℝ g (gradient H (g x))).comp
          (fderiv ℝ (gradient H) (g x)) := by rw [hGradientG]
      _ = fderiv ℝ (g ∘ gradient H) (g x) := hChain.symm
      _ = fderiv ℝ id (g x) := congrArg (fun k ↦ fderiv ℝ k (g x)) hComp
      _ = 1 := fderiv_id
  have hGradientConjugate : gradient (ConvexAnalysis.conjugate H) = g :=
    gradient_conjugateInfty H theta hH hClose hTheta
  have hToA :
      (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _) A =
        fderiv ℝ (gradient H) (g x) := by
    dsimp only [A]
    exact ConvexAnalysis.toEuclideanCLM_hessian H (g x)
  have hToB :
      (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _) B =
        fderiv ℝ g x := by
    calc
      (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _) B =
          fderiv ℝ (gradient (ConvexAnalysis.conjugate H)) x := by
        dsimp only [B]
        exact ConvexAnalysis.toEuclideanCLM_hessian (ConvexAnalysis.conjugate H) x
      _ = fderiv ℝ g x := congrArg (fun k ↦ fderiv ℝ k x) hGradientConjugate
  have hAB : A * B = 1 := by
    apply (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _).injective
    calc
      _ = (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _) A *
          (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _) B := map_mul _ A B
      _ = fderiv ℝ (gradient H) (g x) * fderiv ℝ g x :=
        congrArg₂ (fun P Q ↦ P * Q) hToA hToB
      _ = 1 := hDerivMulRight
      _ = (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _) 1 := (map_one _).symm
  have hBA : B * A = 1 := by
    apply (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _).injective
    calc
      _ = (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _) B *
          (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _) A := map_mul _ B A
      _ = fderiv ℝ g x * fderiv ℝ (gradient H) (g x) :=
        congrArg₂ (fun P Q ↦ P * Q) hToB hToA
      _ = 1 := hDerivMulLeft
      _ = (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _) 1 := (map_one _).symm
  have hAUnit : IsUnit A := ⟨⟨A, B, hAB, hBA⟩, rfl⟩
  have hADet : IsUnit A.det := A.isUnit_iff_isUnit_det.mp hAUnit
  change B = A⁻¹
  calc
    B = B * 1 := (mul_one B).symm
    _ = B * (A * A⁻¹) := by rw [Matrix.mul_nonsing_inv A hADet]
    _ = (B * A) * A⁻¹ := by rw [Matrix.mul_assoc]
    _ = A⁻¹ := by rw [hBA, one_mul]

/-- The Hessian of a `C∞` real-valued function on Euclidean space is Hermitian. -/
private lemma hessianIsHermitianInfty {n : ℕ}
    (H : EuclideanSpace ℝ (Fin n) → ℝ) (hH : ContDiff ℝ ∞ H)
    (x : EuclideanSpace ℝ (Fin n)) :
    (ConvexAnalysis.hessian H x).IsHermitian := by
  -- Symmetry of the second derivative transfers through the Riesz equivalence.
  have hSecondOrder : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr
      (show (2 : ℕ∞) ≤ (⊤ : ℕ∞) from le_top)
  have hSecondSymmetric : IsSymmSndFDerivAt ℝ H x :=
    hH.contDiffAt.isSymmSndFDerivAt hSecondOrder
  have hInftyNeZero : (∞ : ℕ∞ω) ≠ 0 := by simp
  have hGradientDeriv :
      HasFDerivAt (gradient H) (fderiv ℝ (gradient H) x) x :=
    (gradientContDiffInfty H hH).differentiable hInftyNeZero
      |>.differentiableAt.hasFDerivAt
  let dualMap : EuclideanSpace ℝ (Fin n) →L[ℝ]
      (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
    (toDual ℝ (EuclideanSpace ℝ (Fin n))).toContinuousLinearEquiv.toContinuousLinearMap
  have hSecondDeriv :
      HasFDerivAt (fderiv ℝ H)
        (dualMap.comp (fderiv ℝ (gradient H) x)) x := by
    rw [← toDual_comp_gradient]
    exact dualMap.hasFDerivAt.comp x hGradientDeriv
  have hPair (v w : EuclideanSpace ℝ (Fin n)) :
      ⟪fderiv ℝ (gradient H) x v, w⟫_ℝ = fderiv ℝ (fderiv ℝ H) x v w := by
    rw [hSecondDeriv.fderiv]
    rfl
  rw [← Matrix.isSymmetric_toEuclideanLin_iff]
  intro v w
  rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,
    ConvexAnalysis.toEuclideanCLM_hessian]
  change ⟪fderiv ℝ (gradient H) x v, w⟫_ℝ =
    ⟪v, fderiv ℝ (gradient H) x w⟫_ℝ
  calc
    ⟪fderiv ℝ (gradient H) x v, w⟫_ℝ =
        fderiv ℝ (fderiv ℝ H) x v w := hPair v w
    _ = fderiv ℝ (fderiv ℝ H) x w v := hSecondSymmetric.eq v w
    _ = ⟪fderiv ℝ (gradient H) x w, v⟫_ℝ := (hPair w v).symm
    _ = ⟪v, fderiv ℝ (gradient H) x w⟫_ℝ := real_inner_comm _ _

/-- The smooth conjugate Hessian lies in the reciprocal Loewner interval. -/
private lemma hessian_mem_IccInfty {n : ℕ}
    (H : EuclideanSpace ℝ (Fin n) → ℝ) (theta : ℝ)
    (hH : ContDiff ℝ ∞ H)
    (hClose : ∀ z, ‖ConvexAnalysis.hessian H z - 1‖ ≤ theta)
    (hTheta : theta < 1) (x : EuclideanSpace ℝ (Fin n)) :
    ConvexAnalysis.hessian (ConvexAnalysis.conjugate H) x ∈
      Set.Icc ((1 / (1 + theta) : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))
        ((1 / (1 - theta) : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  have hThetaNonneg : 0 ≤ theta :=
    (norm_nonneg (ConvexAnalysis.hessian H 0 - 1)).trans (hClose 0)
  let z := Function.invFun (gradient H) x
  have hBounds := inverseMatrixOrderBoundsOfNormSubOneLe (θ := theta)
    (ConvexAnalysis.hessian H z) (hessianIsHermitianInfty H hH z)
    hThetaNonneg hTheta (hClose z)
  rw [hessian_conjugateInfty H theta hH hClose hTheta x]
  exact hBounds

/-- The smooth conjugate Hessian differs from the identity by at most
`theta / (1 - theta)`. -/
private lemma hessianNorm_leInfty {n : ℕ}
    (H : EuclideanSpace ℝ (Fin n) → ℝ) (theta : ℝ)
    (hH : ContDiff ℝ ∞ H)
    (hClose : ∀ z, ‖ConvexAnalysis.hessian H z - 1‖ ≤ theta)
    (hTheta : theta < 1) (x : EuclideanSpace ℝ (Fin n)) :
    ‖ConvexAnalysis.hessian (ConvexAnalysis.conjugate H) x - 1‖ ≤
      theta / (1 - theta) := by
  let z := Function.invFun (gradient H) x
  have hBound := inverseMatrixNormSubOneLe (θ := theta)
    (ConvexAnalysis.hessian H z) hTheta (hClose z)
  rw [hessian_conjugateInfty H theta hH hClose hTheta x]
  exact hBound

/-- The quadratic tail of the smooth conjugate remains `C∞`. -/
private lemma conjugateSubContDiffInfty {n : ℕ}
    (H : EuclideanSpace ℝ (Fin n) → ℝ) (theta : ℝ)
    (hH : ContDiff ℝ ∞ H)
    (hClose : ∀ z, ‖ConvexAnalysis.hessian H z - 1‖ ≤ theta)
    (hTheta : theta < 1) :
    ContDiff ℝ ∞ (ConvexAnalysis.conjugate H -
      (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) := by
  have hStandardFormula :
      (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ) =
        fun x ↦ (1 / 2 : ℝ) * ‖x‖ ^ 2 := by
    funext x
    exact standardQuadratic_apply x
  have hStandard : ContDiff ℝ ∞
      (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ) := by
    rw [hStandardFormula]
    exact contDiff_const.mul (contDiff_norm_sq ℝ)
  exact (conjugateContDiffInfty H theta hH hClose hTheta).sub hStandard

/-- Outside the original quadratic tail, the smooth conjugate equals the standard
quadratic. -/
private lemma conjugate_eq_standardQuadratic_of_notMem_tsupportInfty {n : ℕ}
    (H : EuclideanSpace ℝ (Fin n) → ℝ) (theta : ℝ)
    (hH : ContDiff ℝ ∞ H)
    (hClose : ∀ z, ‖ConvexAnalysis.hessian H z - 1‖ ≤ theta)
    (hTheta : theta < 1) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∉ tsupport (H - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ))) :
    ConvexAnalysis.conjugate H x = standardQuadratic x := by
  have hTailZero :
      Filter.EventuallyEq (nhds x)
        (H - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) 0 := by
    rwa [← notMem_tsupport_iff_eventuallyEq]
  have hHEqStandard :
      Filter.EventuallyEq (nhds x) H
        (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ) :=
    hTailZero.mono fun y hy ↦ sub_eq_zero.mp hy
  have hGradientX : gradient H x = x := by
    calc
      gradient H x = gradient (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ) x :=
        hHEqStandard.gradient_eq
      _ = x := congrFun gradient_standardQuadratic x
  have hBij := (gradientInverseDataInfty H theta hH hClose hTheta).1
  have hInverseX : Function.invFun (gradient H) x = x := by
    apply hBij.1
    rw [Function.rightInverse_invFun hBij.2 x, hGradientX]
  have hValueX : H x = standardQuadratic x := hHEqStandard.self_of_nhds
  rw [conjugate_eq_inner_invGradientInfty H theta hH hClose hTheta x,
    hInverseX, hValueX, standardQuadratic_apply, real_inner_self_eq_norm_sq]
  ring

/-- The smooth conjugate quadratic tail is supported inside the original tail. -/
private lemma tsupport_conjugateSub_subsetInfty {n : ℕ}
    (H : EuclideanSpace ℝ (Fin n) → ℝ) (theta : ℝ)
    (hH : ContDiff ℝ ∞ H)
    (hClose : ∀ z, ‖ConvexAnalysis.hessian H z - 1‖ ≤ theta)
    (hTheta : theta < 1) :
    tsupport (ConvexAnalysis.conjugate H -
        (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) ⊆
      tsupport (H - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) := by
  apply closure_minimal
  · intro x hx
    by_contra hxOriginal
    exact hx (sub_eq_zero.mpr
      (conjugate_eq_standardQuadratic_of_notMem_tsupportInfty
        H theta hH hClose hTheta hxOriginal))
  · exact isClosed_closure

/-- A zero original gradient makes the inverse gradient fix the origin. -/
private lemma invGradient_zeroInfty {n : ℕ}
    (H : EuclideanSpace ℝ (Fin n) → ℝ) (theta : ℝ)
    (hH : ContDiff ℝ ∞ H)
    (hClose : ∀ z, ‖ConvexAnalysis.hessian H z - 1‖ ≤ theta)
    (hTheta : theta < 1) (hGradientZero : gradient H 0 = 0) :
    Function.invFun (gradient H) 0 = 0 := by
  have hBij := (gradientInverseDataInfty H theta hH hClose hTheta).1
  apply hBij.1
  rw [Function.rightInverse_invFun hBij.2 0, hGradientZero]

/-- The origin minimizes the smooth conjugate when the original gradient vanishes
there. -/
private lemma conjugate_isMinOnInfty {n : ℕ}
    (H : EuclideanSpace ℝ (Fin n) → ℝ) (theta : ℝ)
    (hH : ContDiff ℝ ∞ H)
    (hClose : ∀ z, ‖ConvexAnalysis.hessian H z - 1‖ ≤ theta)
    (hTheta : theta < 1) (hGradientZero : gradient H 0 = 0) :
    IsMinOn (ConvexAnalysis.conjugate H) Set.univ 0 := by
  rw [isMinOn_univ_iff]
  intro x
  have hThetaNonneg : 0 ≤ theta :=
    (norm_nonneg (ConvexAnalysis.hessian H 0 - 1)).trans (hClose 0)
  let c : ℝ≥0 := ⟨theta, hThetaNonneg⟩
  have hCloseC : ∀ z, ‖ConvexAnalysis.hessian H z - 1‖ ≤ (c : ℝ) := hClose
  have hApprox := gradientApproximatesIdentityInfty H hH c hCloseC
  have hc : (c : ℝ) < 1 := hTheta
  have hBij := (gradientInverseDataInfty H theta hH hClose hTheta).1
  have hMax :=
    (pairingSubUniqueMaximumAtInvGradientInfty H c hH hApprox hc hBij x).1
  have hCompetitor :
      ⟪x, (0 : EuclideanSpace ℝ (Fin n))⟫_ℝ - H 0 ≤
        ⟪x, Function.invFun (gradient H) x⟫_ℝ -
          H (Function.invFun (gradient H) x) := hMax.2 ⟨0, rfl⟩
  have hInverseZero := invGradient_zeroInfty H theta hH hClose hTheta hGradientZero
  calc
    ConvexAnalysis.conjugate H 0 =
        ⟪(0 : EuclideanSpace ℝ (Fin n)), Function.invFun (gradient H) 0⟫_ℝ -
          H (Function.invFun (gradient H) 0) :=
      conjugate_eq_inner_invGradientInfty H theta hH hClose hTheta 0
    _ = -H 0 := by simp [hInverseZero]
    _ = ⟪x, (0 : EuclideanSpace ℝ (Fin n))⟫_ℝ - H 0 := by simp
    _ ≤ ⟪x, Function.invFun (gradient H) x⟫_ℝ -
        H (Function.invFun (gradient H) x) := hCompetitor
    _ = ConvexAnalysis.conjugate H x :=
      (conjugate_eq_inner_invGradientInfty H theta hH hClose hTheta x).symm

/-- The reciprocal Hessian lower bound makes the smooth conjugate strongly convex. -/
private lemma conjugateStrongConvexInfty {n : ℕ}
    (H : EuclideanSpace ℝ (Fin n) → ℝ) (theta : ℝ)
    (hH : ContDiff ℝ ∞ H)
    (hClose : ∀ z, ‖ConvexAnalysis.hessian H z - 1‖ ≤ theta)
    (hTheta : theta < 1) :
    StrongConvexOn Set.univ (1 / (1 + theta)) (ConvexAnalysis.conjugate H) := by
  have hThetaNonneg : 0 ≤ theta :=
    (norm_nonneg (ConvexAnalysis.hessian H 0 - 1)).trans (hClose 0)
  have hm : 0 < 1 / (1 + theta) := by positivity
  have hSmoothTwo : ContDiff ℝ 2 (ConvexAnalysis.conjugate H) :=
    (conjugateContDiffInfty H theta hH hClose hTheta).of_le (by
      exact WithTop.coe_le_coe.mpr
        (show (2 : ℕ∞) ≤ (⊤ : ℕ∞) from le_top))
  refine ContDiff.strongConvexOnOfHessianLowerBound
    (ConvexAnalysis.conjugate H) (1 / (1 + theta)) hSmoothTwo hm ?_
  intro x v
  have hLower := (hessian_mem_IccInfty H theta hH hClose hTheta x).1
  rw [Matrix.le_iff, ← Matrix.isPositive_toEuclideanLin_iff] at hLower
  have hQuadratic := hLower.2 v
  change 0 ≤ ⟪(Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ] _)
    (ConvexAnalysis.hessian (ConvexAnalysis.conjugate H) x -
      (1 / (1 + theta)) • 1) v, v⟫_ℝ at hQuadratic
  rw [map_sub, map_smul, map_one, sub_apply, smul_apply, one_apply_eq_self,
    inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
    ConvexAnalysis.toEuclideanCLM_hessian] at hQuadratic
  linarith

/-- Smooth compact quadratic perturbations with Hessian distance below one have the
full smooth conjugacy interface. -/
theorem smoothConjugateData {n : ℕ}
    (H : EuclideanSpace ℝ (Fin n) → ℝ) (theta : ℝ)
    (hH : ContDiff ℝ ∞ H)
    (hTailSmooth : ContDiff ℝ ∞
      (H - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)))
    (hTailCompact : HasCompactSupport
      (H - (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)))
    (hClose : ∀ z, ‖ConvexAnalysis.hessian H z - 1‖ ≤ theta)
    (hTheta : theta < 1) (hGradientZero : gradient H 0 = 0)
    (hHessianZero : ConvexAnalysis.hessian H 0 = 1) :
    SmoothConjugateData H theta := by
  -- Establish the inverse-gradient and Hessian interfaces once, then package them.
  have hInverseData := gradientInverseDataInfty H theta hH hClose hTheta
  have hConjugateSmooth := conjugateContDiffInfty H theta hH hClose hTheta
  have hGradientConjugate := gradient_conjugateInfty H theta hH hClose hTheta
  have hHessianConjugate := hessian_conjugateInfty H theta hH hClose hTheta
  have hBounds := hessian_mem_IccInfty H theta hH hClose hTheta
  have hNorm := hessianNorm_leInfty H theta hH hClose hTheta
  have hSupport := tsupport_conjugateSub_subsetInfty H theta hH hClose hTheta
  have hCompact : HasCompactSupport
      (ConvexAnalysis.conjugate H -
        (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)) :=
    IsCompact.of_isClosed_subset hTailCompact isClosed_closure hSupport
  have hStrong := conjugateStrongConvexInfty H theta hH hClose hTheta
  have hOriginMin := conjugate_isMinOnInfty H theta hH hClose hTheta hGradientZero
  have hThetaNonneg : 0 ≤ theta :=
    (norm_nonneg (ConvexAnalysis.hessian H 0 - 1)).trans (hClose 0)
  have hm : 0 < 1 / (1 + theta) := by positivity
  have hUnique (x : EuclideanSpace ℝ (Fin n)) :
      IsMinOn (ConvexAnalysis.conjugate H) Set.univ x ↔ x = 0 := by
    constructor
    · intro hx
      exact (hStrong.strictConvexOn hm).eq_of_isMinOn hx hOriginMin
        (Set.mem_univ x) (Set.mem_univ 0)
    · intro hx
      rw [hx]
      exact hOriginMin
  have hInverseZero := invGradient_zeroInfty H theta hH hClose hTheta hGradientZero
  have hHessianAtZero : ConvexAnalysis.hessian (ConvexAnalysis.conjugate H) 0 = 1 := by
    rw [hHessianConjugate 0, hInverseZero, hHessianZero]
    exact inv_one
  exact
    { gradientBijective := hInverseData.1
      conjugateSmooth := hConjugateSmooth
      conjugateTailSmooth := conjugateSubContDiffInfty H theta hH hClose hTheta
      gradientConjugate := hGradientConjugate
      hessianConjugate := hHessianConjugate
      hessianBounds := hBounds
      hessianNorm := hNorm
      supportSubset := hSupport
      compactTail := hCompact
      strongConvex := hStrong
      uniqueMinimizer := hUnique
      hessianZero := hHessianAtZero }

end SmoothConjugacy

end QuadraticTail
