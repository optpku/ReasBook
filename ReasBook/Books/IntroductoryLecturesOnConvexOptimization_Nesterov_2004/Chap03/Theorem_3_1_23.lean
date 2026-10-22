/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_29
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient WithTopConvexAnalysis

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 3.1.23 lies in the chapter's convex composite first-order optimality domain.

Sampled owner-style declarations:
- `ConvexOn.isMinOn_iff_variational_inequality_of_hasGradientAt` in `Chap02/Theorem_2_29`
- `constrainedSubdifferential` and `mem_constrainedSubdifferential_iff` in
  `Chap03/Definition_3_1_5`
- mathlib `ConvexOn.add`

Best owner abstraction:
- `ConvexOn.isMinOn_add_iff_neg_hasGradient_mem_constrainedSubdifferential`; it extends the
  Chapter 2 constrained first-order owner from a single convex differentiable term to a convex
  composite `f + Ψ`, and expresses the nonsmooth term through the chapter's existing constrained
  subdifferential owner instead of a second raw inequality wrapper.

Primitive data:
- a convex feasible set `Q`, already packaged by `ConvexOn ℝ Q f` and `ConvexOn ℝ Q Ψ`
- a smooth convex term `f`
- a convex term `Ψ`
- a feasible candidate minimizer `xStar`
- an explicit gradient witness `HasGradientAt f g xStar`

Derived API:
- the raw inequality bridge
  `ConvexOn.isMinOn_add_iff_variational_inequality_of_hasGradientAt`
- the source-facing gradient specialization
  `isMinOn_add_convex_iff_forall_inner_gradient_add_ge`

Source/core/bridge triage:
- source-facing: the textbook gradient inequality for minimizing `x ↦ f x + Ψ x` on `Q`
- core/canonical: `constrainedSubdifferential` together with
  `ConvexOn.isMinOn_add_iff_neg_hasGradient_mem_constrainedSubdifferential`
- bridge/view: the raw variational inequality and the specialization replacing an explicit
  gradient witness by `∇ f xStar` via `DifferentiableAt.hasGradientAt`

The earlier version fixed the ambient space to `EuclideanSpace ℝ (Fin n)`, repeated the redundant
set-convexity hypothesis `Convex ℝ Q`, and required `DifferentiableOn ℝ f Q` although only the
gradient data at `xStar` enters the optimality criterion. The refined owner theorem below lifts
the statement to the chapter's real inner-product-space setting, keeps the pointwise gradient
witness as primitive data, and reuses the earlier constrained-subdifferential owner for `Ψ`; the
textbook displayed inequality and `∇ f xStar` form remain as thin bridges. -/

namespace ConvexOn

variable {Q : Set E} {f Ψ : E → ℝ} {xStar g : E}

/-- A feasible point minimizes the convex composite `f + Ψ` on `Q` exactly when the negative
gradient witness of `f` belongs to the constrained subdifferential of `Ψ` on `Q` at `xStar`. -/
-- Proof sketch: use the Chapter 2 owner theorem for minimizing `f` on `Q` together with the
-- defining inequality of the constrained subdifferential of `Ψ`; the two affine lower-support
-- inequalities add to the minimizing condition for `f + Ψ`.
theorem isMinOn_add_iff_neg_hasGradient_mem_constrainedSubdifferential
    (hf_conv : ConvexOn ℝ Q f) (hΨ_conv : ConvexOn ℝ Q Ψ)
    (hxStar : xStar ∈ Q) (hf_grad : HasGradientAt f g xStar) :
    IsMinOn (f + Ψ) Q xStar ↔
      -g ∈ ∂[Q] (fun x ↦ (Ψ x : WithTop ℝ))(xStar) := by
  rw [mem_constrainedSubdifferential_iff]
  constructor
  · intro hmin
    refine ⟨hxStar, by simp, ?_⟩
    intro x hx
    let γ : ℝ →ᵃ[ℝ] E := AffineMap.lineMap xStar x
    let u : ℝ → ℝ := fun t ↦ f (γ t)
    let w : ℝ → ℝ := fun t ↦ u t + t * (Ψ x - Ψ xStar)
    have hγ_mem {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : γ t ∈ Q := by
      simpa [γ] using hf_conv.1.lineMap_mem hxStar hx ht
    have hu :
        HasDerivAt u (inner ℝ g (x - xStar)) 0 := by
      have hline : HasDerivAt γ (x - xStar) 0 := by
        simpa [γ] using γ.hasDerivAt
      have hgrad :
          HasFDerivAt f ((InnerProductSpace.toDual ℝ E) g) (γ 0) := by
        simpa [γ] using hf_grad.hasFDerivAt
      simpa [u, γ, hf_grad.fderiv_apply] using hgrad.comp_hasDerivAt 0 hline
    have hw :
        HasDerivAt w (inner ℝ g (x - xStar) + (Ψ x - Ψ xStar)) 0 := by
      simpa [w, u, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_comm, mul_left_comm,
        mul_assoc] using hu.add ((hasDerivAt_id (0 : ℝ)).const_mul (Ψ x - Ψ xStar))
    have hslope_nonneg :
        ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 ≤ slope w 0 t := by
      filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
      have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
      have hmin_t : f xStar + Ψ xStar ≤ f (γ t) + Ψ (γ t) := by
        simpa [γ] using (isMinOn_iff.mp hmin (γ t) (hγ_mem htIcc))
      have hΨ_t :
          Ψ (γ t) ≤ Ψ xStar + t * (Ψ x - Ψ xStar) := by
        have hconv_t :
            Ψ (γ t) ≤ (1 - t) * Ψ xStar + t * Ψ x := by
          simpa [γ, AffineMap.lineMap_apply_module] using
            hΨ_conv.2 hxStar hx (sub_nonneg.mpr ht.2) ht.1.le (by ring)
        linarith
      have hw0le : w 0 ≤ w t := by
        have hbound : f xStar ≤ u t + t * (Ψ x - Ψ xStar) := by
          linarith
        simpa [w, u, γ] using hbound
      have : 0 ≤ (w t - w 0) / (t - 0) := by
        exact div_nonneg (sub_nonneg.mpr hw0le) (sub_nonneg.mpr ht.1.le)
      simpa [slope_def_field, ht.1.ne'] using this
    have hslope_nonneg' :
        ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 ≤ t⁻¹ * (w (0 + t) - w 0) := by
      filter_upwards [hslope_nonneg, self_mem_nhdsWithin] with t ht htpos
      have ht0 : 0 < t := htpos
      have hquot : 0 ≤ (w t - w 0) / t := by
        simpa [slope_def_field, ht0.ne'] using ht
      simpa [div_eq_mul_inv, sub_eq_add_neg, mul_comm, add_comm] using hquot
    have hderiv_nonneg : 0 ≤ inner ℝ g (x - xStar) + (Ψ x - Ψ xStar) := by
      exact ge_of_tendsto hw.tendsto_slope_zero_right hslope_nonneg'
    have hreal' : Ψ xStar - inner ℝ g (x - xStar) ≤ Ψ x := by
      linarith
    have hreal : Ψ xStar + inner ℝ (-g) (x - xStar) ≤ Ψ x := by
      simpa using hreal'
    exact_mod_cast hreal
  · rintro ⟨-, -, hsub⟩
    have hgradWithin : HasGradientWithinAt f g Q xStar := by
      exact (hasGradientWithinAt_iff_hasFDerivWithinAt).2 hf_grad.hasFDerivAt.hasFDerivWithinAt
    refine isMinOn_iff.mpr ?_
    intro x hx
    have hf_lower :
        f xStar + inner ℝ g (x - xStar) ≤ f x := by
      exact hf_conv.lower_tangent_plane_of_hasGradientWithinAt xStar hxStar g hgradWithin x hx
    have hΨ_lower_cast :
        (((Ψ xStar + inner ℝ (-g) (x - xStar) : ℝ) : WithTop ℝ) ≤ (Ψ x : WithTop ℝ)) := by
      simpa [ge_iff_le] using hsub hx
    have hΨ_lower :
        Ψ xStar + inner ℝ (-g) (x - xStar) ≤ Ψ x := by
      exact_mod_cast hΨ_lower_cast
    have hΨ_lower' :
        Ψ xStar - inner ℝ g (x - xStar) ≤ Ψ x := by
      simpa using hΨ_lower
    change f xStar + Ψ xStar ≤ f x + Ψ x
    linarith

/-- A feasible point minimizes the convex composite `f + Ψ` on `Q` exactly when every feasible
displacement satisfies the corresponding raw variational inequality against an explicit gradient
witness for `f` at `xStar`. -/
theorem isMinOn_add_iff_variational_inequality_of_hasGradientAt
    (hf_conv : ConvexOn ℝ Q f) (hΨ_conv : ConvexOn ℝ Q Ψ)
    (hxStar : xStar ∈ Q) (hf_grad : HasGradientAt f g xStar) :
    IsMinOn (f + Ψ) Q xStar ↔
      ∀ x ∈ Q, inner ℝ g (x - xStar) + Ψ x ≥ Ψ xStar := by
  rw [hf_conv.isMinOn_add_iff_neg_hasGradient_mem_constrainedSubdifferential
    hΨ_conv hxStar hf_grad, mem_constrainedSubdifferential_iff]
  constructor
  · intro h x hx
    have hcast : Ψ xStar + inner ℝ (-g) (x - xStar) ≤ Ψ x := by
      exact_mod_cast h.2.2 hx
    have hineq : Ψ xStar + -inner ℝ g (x - xStar) ≤ Ψ x := by
      simpa using hcast
    linarith
  · intro h
    refine ⟨hxStar, by simp, ?_⟩
    intro x hx
    have hineq : inner ℝ g (x - xStar) + Ψ x ≥ Ψ xStar := h x hx
    have hreal : Ψ xStar + -inner ℝ g (x - xStar) ≤ Ψ x := by
      linarith
    have hcast : Ψ xStar + inner ℝ (-g) (x - xStar) ≤ Ψ x := by
      simpa using hreal
    exact_mod_cast hcast

end ConvexOn

/-- Theorem 3.1.23: a point `xStar ∈ Q` solves the convex composite minimization problem
`min_{x ∈ Q} (f x + Ψ x)` if and only if it satisfies the variational inequality
`⟪∇ f xStar, x - xStar⟫ + Ψ x ≥ Ψ xStar` for every feasible point `x ∈ Q`. -/
-- Proof sketch: specialize the owner theorem above with the canonical gradient witness
-- `hf_diff.hasGradientAt`.
theorem isMinOn_add_convex_iff_forall_inner_gradient_add_ge
    {Q : Set E} {f Ψ : E → ℝ}
    (hf_conv : ConvexOn ℝ Q f)
    (hΨ_conv : ConvexOn ℝ Q Ψ)
    {xStar : E} (hxStar : xStar ∈ Q) (hf_diff : DifferentiableAt ℝ f xStar) :
    IsMinOn (f + Ψ) Q xStar ↔
      ∀ x ∈ Q, inner ℝ (∇ f xStar) (x - xStar) + Ψ x ≥ Ψ xStar :=
  hf_conv.isMinOn_add_iff_variational_inequality_of_hasGradientAt hΨ_conv hxStar
    hf_diff.hasGradientAt

end
