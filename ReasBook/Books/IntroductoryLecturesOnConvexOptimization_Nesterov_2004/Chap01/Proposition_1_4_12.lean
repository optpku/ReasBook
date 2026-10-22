/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_11

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient
open NormedSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
local notation "S" => Metric.sphere (0 : E) 1

/-
Proposition 1.4.12 is `source-facing` in first-order smooth optimization.

Primary domain:
* directional derivatives on a real Hilbert space, minimized over the unit sphere.

Sampled owner-style declarations:
* `HasDerivWithinAt (fun α : ℝ ↦ f (xBar + α • s)) Δ (Set.Ici (0 : ℝ)) 0`
* `lineDeriv ℝ f xBar s`
* `DifferentiableAt.lineDeriv_eq_fderiv`
* `inner_gradient_left`
* `IsMinOn`

Owner abstraction:
* the directional-derivative owner `lineDeriv ℝ f xBar`
* represented, under differentiability, by the gradient vector `∇ f xBar`

Primitive data:
* a differentiable function `f`
* a base point `xBar`

Derived API:
* the lower bound for `lineDeriv ℝ f xBar` on the unit sphere
* the attained value at `-normalize (∇ f xBar)`
* the source-facing minimizer statement on the unit sphere

Source/core/bridge triage:
* source-facing: minimizing the directional derivative over unit directions
* core/canonical: `lineDeriv ℝ f xBar`, `gradient`, `normalize`, `Metric.sphere`, and `IsMinOn`
* bridge/view: `DifferentiableAt.lineDeriv_eq_fderiv` and `inner_gradient_left`

Definition 1.4.11 already fixed the chapter owner for directional derivatives. This file therefore
keeps `lineDeriv` on the public theorem surface and uses `fderiv ℝ f xBar s` only through the
canonical differentiability bridge, not as a second owner for the same notion.
-/

/-- Helper for Proposition 1.4.12: the normalized negative gradient is a unit direction whenever
the gradient is nonzero. -/
-- Proof sketch: rewrite membership in the unit sphere as a norm-one condition and apply
-- `norm_normalize` to `∇ f xBar`, then simplify the minus sign with `norm_neg`.
private lemma neg_normalize_gradient_mem_unitSphere
    {f : E → ℝ} {xBar : E} (hgrad : ∇ f xBar ≠ 0) :
    -normalize (∇ f xBar) ∈ S := by
  -- Turn unit-sphere membership into the scalar norm condition.
  rw [mem_sphere_zero_iff_norm]
  -- The minus sign does not change the norm, and `normalize` has norm one off the origin.
  simpa [norm_neg] using norm_normalize hgrad

/-- Helper for Proposition 1.4.12: along every unit direction, the directional derivative is
bounded below by the negative gradient norm. -/
-- Proof sketch: rewrite `lineDeriv` as `fderiv` using `DifferentiableAt.lineDeriv_eq_fderiv`,
-- then identify `fderiv` with the gradient pairing via `inner_gradient_left`. Turn `s ∈ S` into
-- `‖s‖ = 1` and apply the Cauchy-Schwarz bound `abs_real_inner_le_norm`.
theorem lineDeriv_ge_neg_norm_of_mem_unitSphere
    {f : E → ℝ} {xBar s : E} (hf : DifferentiableAt ℝ f xBar) (hs : s ∈ S) :
    lineDeriv ℝ f xBar s ≥ -‖∇ f xBar‖ := by
  have hlineDeriv :
      fderiv ℝ f xBar s = inner ℝ (∇ f xBar) s := by
    -- Replace the Fréchet derivative by pairing with the gradient.
    symm
    simpa using (inner_gradient_left (y := s) hf)
  have hbound : -(‖∇ f xBar‖ * ‖s‖) ≤ inner ℝ (∇ f xBar) s := by
    -- Cauchy-Schwarz bounds the real inner product from below by the negative product of norms.
    exact neg_le_of_abs_le (by
      simpa [real_inner_comm] using abs_real_inner_le_norm (∇ f xBar) s)
  -- Once `s` is on the unit sphere, its norm simplifies to `1`.
  rw [hf.lineDeriv_eq_fderiv, hlineDeriv]
  rw [mem_sphere_zero_iff_norm] at hs
  simpa [hs] using hbound

/-- Helper for Proposition 1.4.12: the directional derivative at the normalized negative gradient
equals the negative gradient norm when the gradient is nonzero. -/
-- Proof sketch: first derive `DifferentiableAt ℝ f xBar` from `hgrad` by contraposing
-- `gradient_eq_zero_of_not_differentiableAt`. Then rewrite `lineDeriv` as `fderiv`, identify
-- `fderiv` with the gradient pairing, and simplify the resulting inner product against
-- `-normalize (∇ f xBar)` using `norm_normalize`.
theorem lineDeriv_neg_normalize_gradient_eq_neg_norm
    {f : E → ℝ} {xBar : E} (hgrad : ∇ f xBar ≠ 0) :
    lineDeriv ℝ f xBar (-normalize (∇ f xBar)) = -‖∇ f xBar‖ := by
  have hdiff : DifferentiableAt ℝ f xBar := by
    -- A nonzero totalized gradient forces genuine differentiability at `xBar`.
    by_contra hnot_diff
    have hzero : ∇ f xBar = 0 := by
      simpa using gradient_eq_zero_of_not_differentiableAt hnot_diff
    exact hgrad hzero
  have hlineDeriv :
      fderiv ℝ f xBar (-normalize (∇ f xBar)) =
        inner ℝ (∇ f xBar) (-normalize (∇ f xBar)) := by
    -- Rewrite the Fréchet derivative through the gradient pairing.
    symm
    simpa using (inner_gradient_left (y := -normalize (∇ f xBar)) hdiff)
  have hnorm_ne : ‖∇ f xBar‖ ≠ 0 := norm_ne_zero_iff.mpr hgrad
  rw [hdiff.lineDeriv_eq_fderiv, hlineDeriv]
  calc
    inner ℝ (∇ f xBar) (-normalize (∇ f xBar)) =
        -inner ℝ (∇ f xBar) (normalize (∇ f xBar)) := by
      -- Move the sign out of the inner product.
      rw [inner_neg_right]
    _ = -(‖∇ f xBar‖ ^ (2 : ℕ) / ‖∇ f xBar‖) := by
      -- Expand `normalize` once and evaluate the self-inner product as a norm square.
      rw [NormedSpace.normalize, inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp [hnorm_ne]
    _ = -‖∇ f xBar‖ := by
      -- Cancel one copy of the nonzero norm in the quotient.
      field_simp [hnorm_ne]

/-- Proposition 1.4.12: if the gradient at `xBar` is nonzero, then the minimum directional
derivative on the unit sphere is attained at the normalized negative gradient direction.
Concretely, `-normalize (∇ f xBar)` lies on the unit sphere and minimizes `lineDeriv ℝ f xBar`
there. The companion lemmas
`lineDeriv_ge_neg_norm_of_mem_unitSphere` and
`lineDeriv_neg_normalize_gradient_eq_neg_norm` isolate the lower-bound and value computations. -/
-- Proof sketch: first derive `DifferentiableAt ℝ f xBar` from `hgrad` using
-- `gradient_eq_zero_of_not_differentiableAt`. The nonzero-gradient hypothesis then puts
-- `-normalize (∇ f xBar)` on the unit sphere by `norm_normalize`. The value clause is
-- `lineDeriv_neg_normalize_gradient_eq_neg_norm`. For minimality, combine that equality with
-- `lineDeriv_ge_neg_norm_of_mem_unitSphere` and rewrite the result using `isMinOn_iff`.
theorem lineDeriv_isMinOn_unitSphere_at_neg_normalize_gradient
    {f : E → ℝ} {xBar : E} (hgrad : ∇ f xBar ≠ 0) :
    -normalize (∇ f xBar) ∈ S ∧
      IsMinOn (lineDeriv ℝ f xBar) S (-normalize (∇ f xBar)) := by
  have hdiff : DifferentiableAt ℝ f xBar := by
    -- The minimizer formula only makes sense in the differentiable regime.
    by_contra hnot_diff
    have hzero : ∇ f xBar = 0 := by
      simpa using gradient_eq_zero_of_not_differentiableAt hnot_diff
    exact hgrad hzero
  constructor
  · -- The candidate direction is feasible on the unit sphere.
    exact neg_normalize_gradient_mem_unitSphere hgrad
  · rw [isMinOn_iff]
    intro s hs
    -- The candidate value is exactly `-‖∇ f xBar‖`, and every other unit direction is above it.
    rw [lineDeriv_neg_normalize_gradient_eq_neg_norm hgrad]
    exact lineDeriv_ge_neg_norm_of_mem_unitSphere hdiff hs

end
