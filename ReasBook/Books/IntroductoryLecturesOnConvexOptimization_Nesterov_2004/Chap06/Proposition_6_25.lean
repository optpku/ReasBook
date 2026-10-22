/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_30
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConstrainedArgmin Gradient

universe u v

/- This item lies in the Chapter 6 smoothed-dual / Danskin-gradient domain.

Sampled owner-style declarations:
- `constrainedArgmin` with notation `argmin[Q]` in `Chap01/Definition_1_3_3`, the project owner
  for feasible minimizers of the penalized primal subproblem;
- `extendedRealRealPart` in `Chap03/Definition_3_1_1_3`, the canonical bridge from an
  `EReal`-valued objective to its finite real part;
- mathlib `HasGradientWithinAt` / `gradientWithin`, the canonical within-set gradient owner;
- mathlib `LipschitzOnWith`, the canonical set-restricted Lipschitz owner.

Best owner abstraction:
- source-facing: the item's uniqueness, gradient, and Lipschitz statements for the
  smoothed dual objective `φ_{μ₁}`;
- core/canonical: the penalized primal minimand, the feasible argmin owner `argmin[Q₁]`, the
  `EReal`-valued smoothed dual objective below, `HasGradientWithinAt`, and `LipschitzOnWith`;
- bridge/view: the chosen minimizer section `xμ₁` and the Riesz-vector form
  `(InnerProductSpace.toDual ℝ E₂).symm (A (xμ₁ u))` of the source term `A x_{μ₁}(u)`.

Source/core/bridge triage:
- source-facing: the two proposition statements below;
- core/canonical: `smoothedDualObjectiveMinimand`, `smoothedDualObjective`, and `argmin[Q₁]`;
- bridge/view: the selected minimizer map `xμ₁`.

The workspace currently lacks a usable source-level Chapter 6 owner file for `φ_{μ₁}`, so this
item is stated directly through the canonical argmin and within-gradient owners instead of through
an unavailable upstream wrapper.
-/

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]

/-- The penalized primal minimand
`x ↦ ⟪A x, u⟫ + \hat f(x) + μ₁ d₁(x)` whose feasible minimum defines `φ_{μ₁}(u)`. -/
def smoothedDualObjectiveMinimand
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    (hatf d₁ : E₁ → ℝ) (μ₁ : ℝ) (u : E₂) : E₁ → ℝ :=
  fun x ↦ A x u + hatf x + μ₁ * d₁ x

-- Proof sketch: unfold `smoothedDualObjectiveMinimand`.
/-- Evaluating `smoothedDualObjectiveMinimand` recovers the defining penalized primal subproblem
for the dual point `u`. -/
@[simp] theorem smoothedDualObjectiveMinimand_apply
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    (hatf d₁ : E₁ → ℝ) (μ₁ : ℝ) (u : E₂) (x : E₁) :
    smoothedDualObjectiveMinimand A hatf d₁ μ₁ u x =
      A x u + hatf x + μ₁ * d₁ x := by
  -- This is just the defining equation of the primal slice.
  rfl

/-- The smoothed dual objective
`φ_{μ₁}(u) = -\hat φ(u) + min_{x ∈ Q₁} {⟪A x, u⟫ + \hat f(x) + μ₁ d₁(x)}`,
recorded as an `EReal`-valued function so that its finite real part is available through
`extendedRealRealPart`. -/
def smoothedDualObjective
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) (Q₁ : Set E₁)
    (hatf : E₁ → ℝ) (hatφ : E₂ → ℝ) (d₁ : E₁ → ℝ) (μ₁ : ℝ) : E₂ → EReal :=
  fun u ↦
    ((-hatφ u + sInf (smoothedDualObjectiveMinimand A hatf d₁ μ₁ u '' Q₁)) : ℝ)

-- Proof sketch: unfold `smoothedDualObjective`.
/-- Evaluating `smoothedDualObjective` recovers `-\hat φ(u)` plus the infimum of the penalized
primal minimand over `Q₁`. -/
@[simp] theorem smoothedDualObjective_apply
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) (Q₁ : Set E₁)
    (hatf : E₁ → ℝ) (hatφ : E₂ → ℝ) (d₁ : E₁ → ℝ) (μ₁ : ℝ) (u : E₂) :
    smoothedDualObjective A Q₁ hatf hatφ d₁ μ₁ u =
      ((-hatφ u + sInf (smoothedDualObjectiveMinimand A hatf d₁ μ₁ u '' Q₁)) : ℝ) := by
  -- This is just the defining equation of the smoothed dual value.
  rfl

/-- For each fixed dual point `u`, the penalized primal slice is `μ₁`-strongly convex on `Q₁`. -/
lemma smoothedDualObjectiveMinimand_slice_strongConvexOn
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    {Q₁ : Set E₁} {hatf d₁ : E₁ → ℝ}
    {μ₁ : ℝ} (hμ₁ : 0 < μ₁)
    (hhatf : ConvexOn ℝ Q₁ hatf)
    (hd₁ : StrongConvexOn Q₁ 1 d₁)
    (u : E₂) :
    StrongConvexOn Q₁ μ₁ (smoothedDualObjectiveMinimand A hatf d₁ μ₁ u) := by
  -- First scale the prox term from unit strong convexity to modulus `μ₁`.
  have hscaled : StrongConvexOn Q₁ μ₁ (fun x ↦ μ₁ * d₁ x) := by
    refine ⟨hd₁.1, ?_⟩
    intro x hx y hy a b ha hb hab
    have hd₁_ineq := hd₁.2 hx hy ha hb hab
    have hscaled_ineq := mul_le_mul_of_nonneg_left hd₁_ineq hμ₁.le
    convert hscaled_ineq using 1
    ring_nf
  -- The affine term `x ↦ A x u` is convex, so adding it to `hatf` preserves convexity.
  have hlinear_convex : ConvexOn ℝ Q₁ (fun x : E₁ ↦ A x u) := by
    simpa using ((A.flip u).toLinearMap.convexOn hd₁.1)
  have hperturb_convex : ConvexOn ℝ Q₁ (fun x : E₁ ↦ A x u + hatf x) := by
    simpa [Pi.add_apply, add_assoc, add_left_comm, add_comm] using hlinear_convex.add hhatf
  -- Add the convex perturbation to the scaled strongly convex prox term.
  have hsum : StrongConvexOn Q₁ μ₁ (fun x : E₁ ↦ μ₁ * d₁ x + (A x u + hatf x)) := by
    simpa [StrongConvexOn, Pi.add_apply] using hscaled.add hperturb_convex.uniformConvexOn_zero
  convert hsum using 1
  ext x
  simp [smoothedDualObjectiveMinimand, add_left_comm, add_comm]

/-- Evaluating the smoothed dual objective at a selected primal minimizer replaces the infimum by
the attained slice value. -/
lemma smoothedDualObjective_value_at_selected_argmin
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) {Q₁ : Set E₁}
    {hatf : E₁ → ℝ} {hatφ : E₂ → ℝ} {d₁ : E₁ → ℝ}
    {μ₁ : ℝ} {u : E₂} {x : E₁}
    (hx : x ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf d₁ μ₁ u)) :
    extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ d₁ μ₁) u =
      -hatφ u + A x u + hatf x + μ₁ * d₁ x := by
  -- Unpack the argmin witness into feasibility and exact minimality on the fixed slice.
  rcases mem_constrainedArgmin_iff.mp hx with ⟨hx_mem, hx_min⟩
  have hsInf_eq :
      sInf (smoothedDualObjectiveMinimand A hatf d₁ μ₁ u '' Q₁) =
        smoothedDualObjectiveMinimand A hatf d₁ μ₁ u x := by
    -- The selected minimizer realizes the infimum of the feasible image set.
    have hglb :
        IsGLB
          (smoothedDualObjectiveMinimand A hatf d₁ μ₁ u '' Q₁)
          (smoothedDualObjectiveMinimand A hatf d₁ μ₁ u x) :=
      hx_min.isGLB hx_mem
    have hnonempty :
        (smoothedDualObjectiveMinimand A hatf d₁ μ₁ u '' Q₁).Nonempty := by
      exact ⟨_, ⟨x, hx_mem, rfl⟩⟩
    simpa using hglb.csInf_eq hnonempty
  -- Rewrite the infimum term by the attained value of the chosen minimizer.
  rw [extendedRealRealPart_eq_toReal, smoothedDualObjective_apply, hsInf_eq,
    smoothedDualObjectiveMinimand_apply]
  simpa [add_assoc] using
    (EReal.toReal_coe (-hatφ u + A x u + hatf x + μ₁ * d₁ x))

-- Proof sketch: the affine term `x ↦ A x u` is convex on `Q₁`, `hatf` is convex by assumption,
-- and `μ₁ • d₁` is `μ₁`-strongly convex because `μ₁ > 0`; hence the whole minimand is strongly
-- convex on `Q₁`, so two feasible argmin points must coincide.
/-- The penalized primal minimand defining `x_{μ₁}(u)` has at most one feasible minimizer on
`Q₁` when `\hat f` is convex on `Q₁` and `d₁` is `1`-strongly convex on `Q₁`. -/
theorem smoothedDualObjectiveMinimand_argmin_unique
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    {Q₁ : Set E₁} {hatf d₁ : E₁ → ℝ}
    {μ₁ : ℝ} (hμ₁ : 0 < μ₁)
    (hhatf : ConvexOn ℝ Q₁ hatf)
    (hd₁ : StrongConvexOn Q₁ 1 d₁)
    {u : E₂} {x y : E₁}
    (hx : x ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf d₁ μ₁ u))
    (hy : y ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf d₁ μ₁ u)) :
    x = y := by
  -- Turn both argmin witnesses into feasible minimizers on the same strongly convex slice.
  rcases mem_constrainedArgmin_iff.mp hx with ⟨hx_mem, hx_min⟩
  rcases mem_constrainedArgmin_iff.mp hy with ⟨hy_mem, hy_min⟩
  have hstrict :
      StrictConvexOn ℝ Q₁ (smoothedDualObjectiveMinimand A hatf d₁ μ₁ u) :=
    (smoothedDualObjectiveMinimand_slice_strongConvexOn
      A hμ₁ hhatf hd₁ u).strictConvexOn hμ₁
  -- A strictly convex slice has at most one feasible minimizer.
  exact hstrict.eq_of_isMinOn hx_min hy_min hx_mem hy_mem

/-- Helper for Proposition 6.25: the selected feasible minimizers vary Lipschitz-continuously on
`Q₂` with constant `(1 / μ₁) * ‖A‖`. -/
private lemma selectedArgmin_norm_sub_le
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    {Q₁ : Set E₁} {Q₂ : Set E₂}
    {hatf : E₁ → ℝ} {d₁ : E₁ → ℝ} {μ₁ : ℝ}
    (hμ₁ : 0 < μ₁)
    (hhatf : ConvexOn ℝ Q₁ hatf)
    (hd₁ : StrongConvexOn Q₁ 1 d₁)
    {xμ₁ : E₂ → E₁}
    (hxμ₁ : ∀ ⦃u : E₂⦄, u ∈ Q₂ →
      xμ₁ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf d₁ μ₁ u))
    {u v : E₂} (hu : u ∈ Q₂) (hv : v ∈ Q₂) :
    ‖xμ₁ u - xμ₁ v‖ ≤ ((1 / μ₁) * ‖A‖) * ‖u - v‖ := by
  -- Unpack the two argmin witnesses so the quadratic-growth theorem can be applied slice-wise.
  rcases mem_constrainedArgmin_iff.mp (hxμ₁ hu) with ⟨hxu_mem, hxu_min⟩
  rcases mem_constrainedArgmin_iff.mp (hxμ₁ hv) with ⟨hxv_mem, hxv_min⟩
  have hstrong_u :
      StrongConvexOn Q₁ μ₁ (smoothedDualObjectiveMinimand A hatf d₁ μ₁ u) :=
    smoothedDualObjectiveMinimand_slice_strongConvexOn A hμ₁ hhatf hd₁ u
  have hstrong_v :
      StrongConvexOn Q₁ μ₁ (smoothedDualObjectiveMinimand A hatf d₁ μ₁ v) :=
    smoothedDualObjectiveMinimand_slice_strongConvexOn A hμ₁ hhatf hd₁ v
  -- Quadratic growth at each selected minimizer gives the paired gap inequalities.
  have hquad_u :
      smoothedDualObjectiveMinimand A hatf d₁ μ₁ u (xμ₁ v) ≥
        smoothedDualObjectiveMinimand A hatf d₁ μ₁ u (xμ₁ u) +
          (μ₁ / 2) * ‖xμ₁ v - xμ₁ u‖ ^ (2 : ℕ) :=
    hstrong_u.quadratic_growth_of_isMinOn_of_mem hxu_mem hxu_min (xμ₁ v) hxv_mem
  have hquad_v :
      smoothedDualObjectiveMinimand A hatf d₁ μ₁ v (xμ₁ u) ≥
        smoothedDualObjectiveMinimand A hatf d₁ μ₁ v (xμ₁ v) +
          (μ₁ / 2) * ‖xμ₁ u - xμ₁ v‖ ^ (2 : ℕ) :=
    hstrong_v.quadratic_growth_of_isMinOn_of_mem hxv_mem hxv_min (xμ₁ u) hxu_mem
  have hpair :
      μ₁ * ‖xμ₁ u - xμ₁ v‖ ^ (2 : ℕ) ≤
        A (xμ₁ v - xμ₁ u) (u - v) := by
    -- Adding the two growth bounds cancels the common objective terms and leaves only the
    -- bilinear perturbation induced by `A`.
    have hadd := add_le_add hquad_u hquad_v
    have hnorm_sq :
        ‖xμ₁ v - xμ₁ u‖ ^ (2 : ℕ) = ‖xμ₁ u - xμ₁ v‖ ^ (2 : ℕ) := by
      rw [norm_sub_rev]
    have hrew :
        (smoothedDualObjectiveMinimand A hatf d₁ μ₁ u (xμ₁ u) +
            (μ₁ / 2) * ‖xμ₁ v - xμ₁ u‖ ^ (2 : ℕ)) +
          (smoothedDualObjectiveMinimand A hatf d₁ μ₁ v (xμ₁ v) +
            (μ₁ / 2) * ‖xμ₁ u - xμ₁ v‖ ^ (2 : ℕ)) =
        smoothedDualObjectiveMinimand A hatf d₁ μ₁ u (xμ₁ u) +
          smoothedDualObjectiveMinimand A hatf d₁ μ₁ v (xμ₁ v) +
            μ₁ * ‖xμ₁ u - xμ₁ v‖ ^ (2 : ℕ) := by
      rw [hnorm_sq]
      ring
    rw [hrew] at hadd
    have hcancel :
        smoothedDualObjectiveMinimand A hatf d₁ μ₁ u (xμ₁ v) +
            smoothedDualObjectiveMinimand A hatf d₁ μ₁ v (xμ₁ u) -
              (smoothedDualObjectiveMinimand A hatf d₁ μ₁ u (xμ₁ u) +
                smoothedDualObjectiveMinimand A hatf d₁ μ₁ v (xμ₁ v)) =
          A (xμ₁ v - xμ₁ u) (u - v) := by
      simp [smoothedDualObjectiveMinimand_apply, sub_eq_add_neg]
      ring
    linarith [hadd, hcancel]
  have hpair_le :
      A (xμ₁ v - xμ₁ u) (u - v) ≤ ‖A‖ * ‖xμ₁ v - xμ₁ u‖ * ‖u - v‖ := by
    -- Bound the bilinear perturbation first by the operator norm of the selected functional,
    -- then by the operator norm of `A`.
    have hfunctional :
        ‖A (xμ₁ v - xμ₁ u) (u - v)‖ ≤ ‖A (xμ₁ v - xμ₁ u)‖ * ‖u - v‖ := by
      simpa using (A (xμ₁ v - xμ₁ u)).le_opNorm (u - v)
    have hfunctional' :
        A (xμ₁ v - xμ₁ u) (u - v) ≤ ‖A (xμ₁ v - xμ₁ u)‖ * ‖u - v‖ :=
      le_trans (le_abs_self _) hfunctional
    exact hfunctional'.trans <| by
      gcongr
      exact A.le_opNorm (xμ₁ v - xμ₁ u)
  have hpair' :
      μ₁ * ‖xμ₁ u - xμ₁ v‖ ^ (2 : ℕ) ≤
        ‖A‖ * ‖xμ₁ u - xμ₁ v‖ * ‖u - v‖ := by
    refine hpair.trans ?_
    simpa [norm_sub_rev, mul_assoc, mul_left_comm, mul_comm] using hpair_le
  -- The paired bound is quadratic in `‖xμ₁ u - xμ₁ v‖`, so `nlinarith` isolates the linear
  -- Lipschitz estimate.
  by_cases hzero : xμ₁ u = xμ₁ v
  · simp [hzero]
    positivity
  · have hnorm_pos : 0 < ‖xμ₁ u - xμ₁ v‖ := by
      rw [norm_pos_iff]
      exact sub_ne_zero.mpr hzero
    have hlinear :
        μ₁ * ‖xμ₁ u - xμ₁ v‖ ≤ ‖A‖ * ‖u - v‖ := by
      nlinarith [hμ₁, hnorm_pos, norm_nonneg (u - v), norm_nonneg A, hpair']
    have hdiv :
        ‖xμ₁ u - xμ₁ v‖ ≤ (‖A‖ * ‖u - v‖) / μ₁ := by
      refine (le_div_iff₀ hμ₁).2 ?_
      simpa [mul_comm, mul_left_comm, mul_assoc] using hlinear
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv

/-- Helper for Proposition 6.25: after applying `A` and the Riesz isometry, the selected dual
term is Lipschitz on `Q₂` with constant `(1 / μ₁) * ‖A‖^2`. -/
private lemma selectedArgminDualTerm_norm_sub_le
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    {Q₁ : Set E₁} {Q₂ : Set E₂}
    {hatf : E₁ → ℝ} {d₁ : E₁ → ℝ} {μ₁ : ℝ}
    (hμ₁ : 0 < μ₁)
    (hhatf : ConvexOn ℝ Q₁ hatf)
    (hd₁ : StrongConvexOn Q₁ 1 d₁)
    {xμ₁ : E₂ → E₁}
    (hxμ₁ : ∀ ⦃u : E₂⦄, u ∈ Q₂ →
      xμ₁ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf d₁ μ₁ u))
    {u v : E₂} (hu : u ∈ Q₂) (hv : v ∈ Q₂) :
    ‖(InnerProductSpace.toDual ℝ E₂).symm (A (xμ₁ u)) -
        (InnerProductSpace.toDual ℝ E₂).symm (A (xμ₁ v))‖ ≤
      ((1 / μ₁) * ‖A‖ ^ (2 : ℕ)) * ‖u - v‖ := by
  -- First rewrite the Riesz-vector difference back to the dual norm of `A (xμ₁ u - xμ₁ v)`.
  calc
    ‖(InnerProductSpace.toDual ℝ E₂).symm (A (xμ₁ u)) -
        (InnerProductSpace.toDual ℝ E₂).symm (A (xμ₁ v))‖ =
      ‖A (xμ₁ u - xμ₁ v)‖ := by
        rw [← map_sub, A.map_sub, LinearIsometryEquiv.norm_map]
    _ ≤ ‖A‖ * ‖xμ₁ u - xμ₁ v‖ := A.le_opNorm (xμ₁ u - xμ₁ v)
    _ ≤ ‖A‖ * (((1 / μ₁) * ‖A‖) * ‖u - v‖) := by
        gcongr
        exact selectedArgmin_norm_sub_le A hμ₁ hhatf hd₁ hxμ₁ hu hv
    _ = ((1 / μ₁) * ‖A‖ ^ (2 : ℕ)) * ‖u - v‖ := by ring_nf

/-- Helper for Proposition 6.25: the `v`-slice gap between the point selected at `u` and the
true `v`-slice minimizer is controlled by the quadratic selector stability estimate. -/
private lemma selectedArgminGap_le
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    {Q₁ : Set E₁} {Q₂ : Set E₂}
    {hatf : E₁ → ℝ} {d₁ : E₁ → ℝ} {μ₁ : ℝ}
    (hμ₁ : 0 < μ₁)
    (hhatf : ConvexOn ℝ Q₁ hatf)
    (hd₁ : StrongConvexOn Q₁ 1 d₁)
    {xμ₁ : E₂ → E₁}
    (hxμ₁ : ∀ ⦃u : E₂⦄, u ∈ Q₂ →
      xμ₁ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf d₁ μ₁ u))
    {u v : E₂} (hu : u ∈ Q₂) (hv : v ∈ Q₂) :
    smoothedDualObjectiveMinimand A hatf d₁ μ₁ v (xμ₁ u) -
        smoothedDualObjectiveMinimand A hatf d₁ μ₁ v (xμ₁ v) ≤
      ((1 / μ₁) * ‖A‖ ^ (2 : ℕ)) * ‖u - v‖ ^ (2 : ℕ) := by
  rcases mem_constrainedArgmin_iff.mp (hxμ₁ hu) with ⟨hxu_mem, hxu_min⟩
  rcases mem_constrainedArgmin_iff.mp (hxμ₁ hv) with ⟨hxv_mem, _hxv_min⟩
  have hslice_compare :
      smoothedDualObjectiveMinimand A hatf d₁ μ₁ v (xμ₁ u) -
          smoothedDualObjectiveMinimand A hatf d₁ μ₁ v (xμ₁ v) ≤
        A (xμ₁ u - xμ₁ v) (v - u) := by
    -- Compare the `v`-slice against the `u`-slice, where `xμ₁ u` is already minimal.
    have hmin_u :
        smoothedDualObjectiveMinimand A hatf d₁ μ₁ u (xμ₁ u) ≤
          smoothedDualObjectiveMinimand A hatf d₁ μ₁ u (xμ₁ v) :=
      hxu_min hxv_mem
    have hrew :
        smoothedDualObjectiveMinimand A hatf d₁ μ₁ v (xμ₁ u) -
            smoothedDualObjectiveMinimand A hatf d₁ μ₁ v (xμ₁ v) =
          smoothedDualObjectiveMinimand A hatf d₁ μ₁ u (xμ₁ u) -
            smoothedDualObjectiveMinimand A hatf d₁ μ₁ u (xμ₁ v) +
              A (xμ₁ u - xμ₁ v) (v - u) := by
      simp [smoothedDualObjectiveMinimand_apply, sub_eq_add_neg]
      ring
    rw [hrew]
    linarith
  have hlinear_bound :
      A (xμ₁ u - xμ₁ v) (v - u) ≤
        ((1 / μ₁) * ‖A‖ ^ (2 : ℕ)) * ‖u - v‖ ^ (2 : ℕ) := by
    -- Bound the remaining bilinear perturbation by the operator norm of `A` and the selector
    -- Lipschitz estimate already proved above.
    calc
      A (xμ₁ u - xμ₁ v) (v - u) ≤ ‖A (xμ₁ u - xμ₁ v) (v - u)‖ := le_abs_self _
      _ ≤ ‖A (xμ₁ u - xμ₁ v)‖ * ‖v - u‖ := by
          simpa using (A (xμ₁ u - xμ₁ v)).le_opNorm (v - u)
      _ ≤ ‖A‖ * ‖xμ₁ u - xμ₁ v‖ * ‖v - u‖ := by
          gcongr
          exact A.le_opNorm (xμ₁ u - xμ₁ v)
      _ ≤ ‖A‖ * (((1 / μ₁) * ‖A‖) * ‖u - v‖) * ‖v - u‖ := by
          gcongr
          exact selectedArgmin_norm_sub_le A hμ₁ hhatf hd₁ hxμ₁ hu hv
      _ = ((1 / μ₁) * ‖A‖ ^ (2 : ℕ)) * ‖u - v‖ ^ (2 : ℕ) := by
          rw [norm_sub_rev]
          ring_nf
  exact hslice_compare.trans hlinear_bound

/-- Helper for Proposition 6.25: after evaluating the smoothed dual at the selected minimizers,
the affine remainder is the negative `hatφ` remainder minus the `v`-slice gap. -/
private lemma smoothedDualObjective_remainder_eq_hatφ_remainder_sub_gap
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    {Q₁ : Set E₁} {Q₂ : Set E₂}
    {hatf : E₁ → ℝ} {hatφ : E₂ → ℝ} {d₁ : E₁ → ℝ} {μ₁ : ℝ}
    {xμ₁ : E₂ → E₁}
    (hxμ₁ : ∀ ⦃u : E₂⦄, u ∈ Q₂ →
      xμ₁ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf d₁ μ₁ u))
    {u v : E₂} (hu : u ∈ Q₂) (hv : v ∈ Q₂) :
    extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ d₁ μ₁) v -
        extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ d₁ μ₁) u -
        inner ℝ
          (-gradientWithin hatφ Q₂ u + (InnerProductSpace.toDual ℝ E₂).symm (A (xμ₁ u)))
          (v - u) =
      -(hatφ v - hatφ u - inner ℝ (gradientWithin hatφ Q₂ u) (v - u)) -
        (smoothedDualObjectiveMinimand A hatf d₁ μ₁ v (xμ₁ u) -
          smoothedDualObjectiveMinimand A hatf d₁ μ₁ v (xμ₁ v)) := by
  -- Replace the infimum terms by the attained slice values at the selected minimizers.
  rw [smoothedDualObjective_value_at_selected_argmin A (hx := hxμ₁ hv),
    smoothedDualObjective_value_at_selected_argmin A (hx := hxμ₁ hu)]
  -- The remaining identity is a scalar rearrangement of the `u`- and `v`-slice formulas.
  simp [smoothedDualObjectiveMinimand_apply, InnerProductSpace.toDual_symm_apply, sub_eq_add_neg,
    inner_add_left, inner_neg_left]
  ring

-- Proof sketch: apply the uniqueness theorem above to each fiber `u`, then use a Danskin-type
-- argument for the infimum term in `smoothedDualObjective`, combining it with the assumed
-- differentiability of `hatφ` on `Q₂`; the linear contribution is expressed via the Riesz vector
-- corresponding to the functional `A (xμ₁ u)`.
/-- Proposition 6.25 (1) [Chapter6_2.json:67]: if `\hat φ` is differentiable on `Q₂`, `\hat f`
is convex on `Q₁`, `d₁` is `1`-strongly convex on `Q₁`, and `x_{μ₁}` selects a feasible minimizer
of the canonical argmin owner for each `u ∈ Q₂`, then that minimizer is unique and the finite
real part of `φ_{μ₁}` has within-set gradient `-\nabla \hat φ(u) + A x_{μ₁}(u)`, encoded by the
Riesz-vector form of `A (xμ₁ u)`. -/
theorem smoothedDualObjective_argmin_unique_and_hasGradientWithinAt
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    {Q₁ : Set E₁} {Q₂ : Set E₂}
    {hatf : E₁ → ℝ} {hatφ : E₂ → ℝ} {d₁ : E₁ → ℝ}
    {μ₁ : ℝ} (hμ₁ : 0 < μ₁)
    (hhatf : ConvexOn ℝ Q₁ hatf)
    (hd₁ : StrongConvexOn Q₁ 1 d₁)
    (hhatφ : DifferentiableOn ℝ hatφ Q₂)
    {xμ₁ : E₂ → E₁}
    (hxμ₁ : ∀ ⦃u : E₂⦄, u ∈ Q₂ →
      xμ₁ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf d₁ μ₁ u)) :
    (∀ ⦃u : E₂⦄, u ∈ Q₂ → ∀ ⦃x : E₁⦄,
      x ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf d₁ μ₁ u) → x = xμ₁ u) ∧
    ∀ ⦃u : E₂⦄, u ∈ Q₂ →
      HasGradientWithinAt
        (extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ d₁ μ₁))
        (-gradientWithin hatφ Q₂ u + (InnerProductSpace.toDual ℝ E₂).symm (A (xμ₁ u)))
        Q₂ u := by
  refine ⟨?_, ?_⟩
  · intro u hu x hx
    -- The pointwise selector is unique because each primal slice is strongly convex.
    exact smoothedDualObjectiveMinimand_argmin_unique A hμ₁ hhatf hd₁ hx (hxμ₁ hu)
  · intro u hu
    -- Route correction: normalize the smoothed-dual remainder into the `hatφ` remainder minus the
    -- slice gap before invoking the within-set little-`o` criterion.
    rw [hasGradientWithinAt_iff_isLittleO]
    have hhatφLittleO :
        (fun v : E₂ ↦ hatφ v - hatφ u - inner ℝ (gradientWithin hatφ Q₂ u) (v - u)) =o[
            nhdsWithin u Q₂] fun v ↦ v - u :=
      hasGradientWithinAt_iff_isLittleO.mp ((hhatφ u hu).hasGradientWithinAt)
    rcases mem_constrainedArgmin_iff.mp (hxμ₁ hu) with ⟨hxu_mem, _hxu_min⟩
    have hgapBigO :
        (fun v : E₂ ↦
          smoothedDualObjectiveMinimand A hatf d₁ μ₁ v (xμ₁ u) -
            smoothedDualObjectiveMinimand A hatf d₁ μ₁ v (xμ₁ v)) =O[nhdsWithin u Q₂]
          fun v ↦ (‖v - u‖ : ℝ) ^ (2 : ℕ) := by
      refine Asymptotics.IsBigO.of_bound ((1 / μ₁) * ‖A‖ ^ (2 : ℕ)) ?_
      filter_upwards [self_mem_nhdsWithin] with v hv
      rcases mem_constrainedArgmin_iff.mp (hxμ₁ hv) with ⟨hxv_mem, hxv_min⟩
      have hgap_nonneg :
          0 ≤
            smoothedDualObjectiveMinimand A hatf d₁ μ₁ v (xμ₁ u) -
              smoothedDualObjectiveMinimand A hatf d₁ μ₁ v (xμ₁ v) := by
        have hmin_v :
            smoothedDualObjectiveMinimand A hatf d₁ μ₁ v (xμ₁ v) ≤
              smoothedDualObjectiveMinimand A hatf d₁ μ₁ v (xμ₁ u) :=
          hxv_min hxu_mem
        linarith
      have hgap_le :=
        selectedArgminGap_le A hμ₁ hhatf hd₁ hxμ₁ hu hv
      calc
        ‖smoothedDualObjectiveMinimand A hatf d₁ μ₁ v (xμ₁ u) -
            smoothedDualObjectiveMinimand A hatf d₁ μ₁ v (xμ₁ v)‖ =
            smoothedDualObjectiveMinimand A hatf d₁ μ₁ v (xμ₁ u) -
              smoothedDualObjectiveMinimand A hatf d₁ μ₁ v (xμ₁ v) := by
              rw [Real.norm_of_nonneg hgap_nonneg]
        _ ≤ ((1 / μ₁) * ‖A‖ ^ (2 : ℕ)) * ‖u - v‖ ^ (2 : ℕ) := hgap_le
        _ = ((1 / μ₁) * ‖A‖ ^ (2 : ℕ)) * ‖(‖v - u‖ : ℝ) ^ (2 : ℕ)‖ := by
            rw [norm_sub_rev, Real.norm_eq_abs, abs_of_nonneg]
            positivity
    have hnormSqLittleO :
        (fun v : E₂ ↦ (‖v - u‖ : ℝ) ^ (2 : ℕ)) =o[nhdsWithin u Q₂] fun v ↦ v - u := by
      exact
        (Asymptotics.isLittleO_pow_sub_sub (x₀ := u) (m := 2) (by norm_num)).mono
          nhdsWithin_le_nhds
    have hgapLittleO :
        (fun v : E₂ ↦
          smoothedDualObjectiveMinimand A hatf d₁ μ₁ v (xμ₁ u) -
            smoothedDualObjectiveMinimand A hatf d₁ μ₁ v (xμ₁ v)) =o[nhdsWithin u Q₂]
          fun v ↦ v - u :=
      hgapBigO.trans_isLittleO hnormSqLittleO
    have hsumLittleO :
        (fun v : E₂ ↦
          -(hatφ v - hatφ u - inner ℝ (gradientWithin hatφ Q₂ u) (v - u)) -
            (smoothedDualObjectiveMinimand A hatf d₁ μ₁ v (xμ₁ u) -
              smoothedDualObjectiveMinimand A hatf d₁ μ₁ v (xμ₁ v))) =o[nhdsWithin u Q₂]
          fun v ↦ v - u := by
      simpa [sub_eq_add_neg] using hhatφLittleO.neg_left.add hgapLittleO.neg_left
    have hrewrite :
        (fun v : E₂ ↦
          extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ d₁ μ₁) v -
            extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ d₁ μ₁) u -
            inner ℝ
              (-gradientWithin hatφ Q₂ u + (InnerProductSpace.toDual ℝ E₂).symm (A (xμ₁ u)))
              (v - u)) =ᶠ[nhdsWithin u Q₂]
          (fun v ↦
            -(hatφ v - hatφ u - inner ℝ (gradientWithin hatφ Q₂ u) (v - u)) -
              (smoothedDualObjectiveMinimand A hatf d₁ μ₁ v (xμ₁ u) -
                smoothedDualObjectiveMinimand A hatf d₁ μ₁ v (xμ₁ v))) := by
      filter_upwards [self_mem_nhdsWithin] with v hv
      exact smoothedDualObjective_remainder_eq_hatφ_remainder_sub_gap A hxμ₁ hu hv
    exact hrewrite.trans_isLittleO hsumLittleO

/-- Helper for Proposition 6.25: on a uniquely differentiable feasible set, the canonical
within-gradient of `φ_{μ₁}` matches the explicit source-side formula. -/
private lemma smoothedDualObjective_gradientWithin_eq_explicit
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    {Q₁ : Set E₁} {Q₂ : Set E₂}
    {hatf : E₁ → ℝ} {hatφ : E₂ → ℝ} {d₁ : E₁ → ℝ}
    {μ₁ : ℝ} (hμ₁ : 0 < μ₁)
    (hhatf : ConvexOn ℝ Q₁ hatf)
    (hd₁ : StrongConvexOn Q₁ 1 d₁)
    (hhatφ : DifferentiableOn ℝ hatφ Q₂)
    {xμ₁ : E₂ → E₁}
    (hxμ₁ : ∀ ⦃u : E₂⦄, u ∈ Q₂ →
      xμ₁ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf d₁ μ₁ u))
    {u : E₂} (hu : u ∈ Q₂) (hu_unique : UniqueDiffWithinAt ℝ Q₂ u) :
    gradientWithin
        (extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ d₁ μ₁))
        Q₂ u =
      -gradientWithin hatφ Q₂ u + (InnerProductSpace.toDual ℝ E₂).symm (A (xμ₁ u)) := by
  -- Convert the explicit `HasGradientWithinAt` witness from Proposition 6.25 (1) into the
  -- canonical `gradientWithin` field through uniqueness of `fderivWithin`.
  have hgrad :=
    (smoothedDualObjective_argmin_unique_and_hasGradientWithinAt
      A hμ₁ hhatf hd₁ hhatφ hxμ₁).2 hu
  have hfderiv :
      fderivWithin ℝ
          (extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ d₁ μ₁))
          Q₂ u =
        InnerProductSpace.toDual ℝ E₂
          (-gradientWithin hatφ Q₂ u + (InnerProductSpace.toDual ℝ E₂).symm (A (xμ₁ u))) :=
    hgrad.hasFDerivWithinAt.fderivWithin hu_unique
  simpa [gradientWithin] using
    congrArg (fun f' ↦ (InnerProductSpace.toDual ℝ E₂).symm f') hfderiv

/-- Helper for Proposition 6.25: the Lipschitz estimate for the selected dual term can be
rewritten directly on `edist`, matching the `LipschitzOnWith` surface. -/
private lemma selectedArgminDualTerm_edist_le
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    {Q₁ : Set E₁} {Q₂ : Set E₂}
    {hatf : E₁ → ℝ} {d₁ : E₁ → ℝ} {μ₁ : ℝ}
    (hμ₁ : 0 < μ₁)
    (hhatf : ConvexOn ℝ Q₁ hatf)
    (hd₁ : StrongConvexOn Q₁ 1 d₁)
    {xμ₁ : E₂ → E₁}
    (hxμ₁ : ∀ ⦃u : E₂⦄, u ∈ Q₂ →
      xμ₁ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf d₁ μ₁ u))
    {u v : E₂} (hu : u ∈ Q₂) (hv : v ∈ Q₂) :
    edist ((InnerProductSpace.toDual ℝ E₂).symm (A (xμ₁ u)))
        ((InnerProductSpace.toDual ℝ E₂).symm (A (xμ₁ v))) ≤
      Real.toNNReal ((1 / μ₁) * ‖A‖ ^ (2 : ℕ)) * edist u v := by
  have hnonneg : 0 ≤ ((1 / μ₁) * ‖A‖ ^ (2 : ℕ)) := by
    positivity
  -- Convert the already-proved norm estimate into the metric-space language of
  -- `LipschitzOnWith`.
  have hnndist :
      nndist ((InnerProductSpace.toDual ℝ E₂).symm (A (xμ₁ u)))
          ((InnerProductSpace.toDual ℝ E₂).symm (A (xμ₁ v))) ≤
        Real.toNNReal ((1 / μ₁) * ‖A‖ ^ (2 : ℕ)) * nndist u v := by
    rw [nndist_eq_nnnorm, nndist_eq_nnnorm, ← NNReal.coe_le_coe, NNReal.coe_mul]
    -- After coercing `NNReal` back to `ℝ`, only the nonnegativity normalization of the
    -- coefficient remains.
    calc
      ‖(InnerProductSpace.toDual ℝ E₂).symm (A (xμ₁ u)) -
          (InnerProductSpace.toDual ℝ E₂).symm (A (xμ₁ v))‖ ≤
          ((1 / μ₁) * ‖A‖ ^ (2 : ℕ)) * ‖u - v‖ :=
        selectedArgminDualTerm_norm_sub_le A hμ₁ hhatf hd₁ hxμ₁ hu hv
      _ = max ((1 / μ₁) * ‖A‖ ^ (2 : ℕ)) 0 * ‖u - v‖ := by
        rw [max_eq_left hnonneg]
  rw [edist_nndist, edist_nndist]
  exact_mod_cast hnndist

-- Proof sketch: combine the within-gradient formula above with the assumed Lipschitz control on
-- `u ↦ gradientWithin hatφ Q₂ u`, and estimate the selected-minimizer contribution by the
-- standard strong-convexity bound `μ₁⁻¹ ‖A‖²`.
-- LeanSearch hit for the canonical `gradientWithin` bridge: `HasFDerivWithinAt.fderivWithin`.
/-- Proposition 6.25 (2) [Chapter6_2.json:67]: if, in addition,
`Q₂` is uniquely differentiable and `u ↦ gradientWithin hatφ Q₂ u` is Lipschitz on `Q₂`
with constant `L₂(\hat φ)`, then the canonical within-gradient field of `φ_{μ₁}` is
Lipschitz on `Q₂` with constant
`L₂(\hat φ) + μ₁⁻¹ ‖A‖²`. -/
theorem smoothedDualObjective_gradientWithin_lipschitzOn
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    {Q₁ : Set E₁} {Q₂ : Set E₂}
    {hatf : E₁ → ℝ} {hatφ : E₂ → ℝ} {d₁ : E₁ → ℝ}
    {μ₁ : ℝ} {Lhatφ : NNReal} (hμ₁ : 0 < μ₁)
    (hhatf : ConvexOn ℝ Q₁ hatf)
    (hd₁ : StrongConvexOn Q₁ 1 d₁)
    (hhatφ : DifferentiableOn ℝ hatφ Q₂)
    (hQ₂_unique : UniqueDiffOn ℝ Q₂)
    {xμ₁ : E₂ → E₁}
    (hxμ₁ : ∀ ⦃u : E₂⦄, u ∈ Q₂ →
      xμ₁ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf d₁ μ₁ u))
    (hhatφ_lipschitz :
      LipschitzOnWith Lhatφ (fun u ↦ gradientWithin hatφ Q₂ u) Q₂) :
    LipschitzOnWith
      (Lhatφ + Real.toNNReal ((1 / μ₁) * ‖A‖ ^ (2 : ℕ)))
      (fun u ↦
        gradientWithin
          (extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ d₁ μ₁))
          Q₂ u)
      Q₂ := by
  intro u hu v hv
  -- Rewrite both canonical within-gradients using the explicit formula from Proposition 6.25 (1).
  have hgrad_u :
      (fun u ↦
        gradientWithin
          (extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ d₁ μ₁))
          Q₂ u) u =
        -gradientWithin hatφ Q₂ u + (InnerProductSpace.toDual ℝ E₂).symm (A (xμ₁ u)) := by
    simpa using
      smoothedDualObjective_gradientWithin_eq_explicit
        A hμ₁ hhatf hd₁ hhatφ hxμ₁ hu (hQ₂_unique u hu)
  have hgrad_v :
      (fun u ↦
        gradientWithin
          (extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ d₁ μ₁))
          Q₂ u) v =
        -gradientWithin hatφ Q₂ v + (InnerProductSpace.toDual ℝ E₂).symm (A (xμ₁ v)) := by
    simpa using
      smoothedDualObjective_gradientWithin_eq_explicit
        A hμ₁ hhatf hd₁ hhatφ hxμ₁ hv (hQ₂_unique v hv)
  rw [hgrad_u, hgrad_v]
  have hhatφ_edist :
      edist (-gradientWithin hatφ Q₂ u) (-gradientWithin hatφ Q₂ v) ≤
        Lhatφ * edist u v := by
    simpa using hhatφ_lipschitz hu hv
  have hdual_edist :
      edist ((InnerProductSpace.toDual ℝ E₂).symm (A (xμ₁ u)))
          ((InnerProductSpace.toDual ℝ E₂).symm (A (xμ₁ v))) ≤
        Real.toNNReal ((1 / μ₁) * ‖A‖ ^ (2 : ℕ)) * edist u v :=
    selectedArgminDualTerm_edist_le A hμ₁ hhatf hd₁ hxμ₁ hu hv
  -- The two explicit components are Lipschitz, so their sum is Lipschitz with the summed
  -- constant.
  calc
    edist
        (-gradientWithin hatφ Q₂ u + (InnerProductSpace.toDual ℝ E₂).symm (A (xμ₁ u)))
        (-gradientWithin hatφ Q₂ v + (InnerProductSpace.toDual ℝ E₂).symm (A (xμ₁ v))) ≤
      edist (-gradientWithin hatφ Q₂ u) (-gradientWithin hatφ Q₂ v) +
        edist ((InnerProductSpace.toDual ℝ E₂).symm (A (xμ₁ u)))
          ((InnerProductSpace.toDual ℝ E₂).symm (A (xμ₁ v))) :=
      edist_add_add_le _ _ _ _
    _ ≤
        (Lhatφ + Real.toNNReal ((1 / μ₁) * ‖A‖ ^ (2 : ℕ))) * edist u v := by
      simpa [add_mul] using add_le_add hhatφ_edist hdual_edist

end
