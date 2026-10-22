/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_16
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_14

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Primary domain: twice continuously differentiable strong-convexity criteria on open convex
subsets of real Hilbert spaces, together with the textbook bridge from `interior Q` to `Q`.

Sampled owner-style declarations before refining this file:
* mathlib `StrongConvexOn`
* mathlib `strongConvexOn_iff_convex`
* project `StrongConvexOnWith` in `Definition_2_14`
* project `StrongConvexOnWith.lower_tangent_quadratic` in `Definition_2_14`
* project `convexOn_iff_hessian_quadratic_form_nonneg` in `Theorem_2_4`

Source/core/bridge triage:
* source-facing: the lower-tangent inequality from `x ∈ interior Q` to arbitrary `y ∈ Q`
* core/canonical: `StrongConvexOnWith p μ U f` on an open convex owner domain `U`
* bridge/view: the Hessian quadratic-form lower bound on that same open convex domain

Primitive data:
* the open convex owner domain `U`
* the source-facing convex set `Q`
* continuity of `f` on `Q`
* `C²` regularity of `f` on the open owner domain

Derived API:
* `StrongConvexOnWith.lower_tangent_quadratic` on the open owner domain
* the Euclidean `StrongConvexOn` bridge used in `Definition_2_15` after finite-dimensional
  specialization

The main public theorem stays source-facing because the textbook statement compares the interior
Hessian bound with a lower-tangent inequality that reaches all the way to `y ∈ Q`, while the
owner predicate `StrongConvexOnWith` governs the intrinsic strong-convexity data on the open
convex domain where the Hessian is evaluated. -/

section

variable (p : Seminorm ℝ E)
variable {μ : ℝ} {U Q : Set E} {f : E → ℝ}

/-- Helper for Theorem 2.12: the affine line `s ↦ x + s • d` has derivative `d`. -/
private theorem line_hasDerivAt (x d : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ x + s • d) d t := by
  -- Differentiate the scalar multiple and then translate by the base point.
  simpa [one_smul] using ((hasDerivAt_id t).smul_const d).const_add x

/-- Helper for Theorem 2.12: scalarizing the gradient along an affine line differentiates to the
Hessian pairing in the line direction. -/
private theorem scalarized_gradient_along_line_hasDerivAt
    {x d u : E} {t : ℝ} (hf_C2 : ContDiffAt ℝ 2 f (x + t • d)) :
    HasDerivAt (fun s : ℝ ↦ inner ℝ (∇ f (x + s • d)) u)
      (inner ℝ (hessian f (x + t • d) d) u) t := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfderiv : DifferentiableAt ℝ (fderiv ℝ f) (x + t • d) := by
    -- A `C²` function has a differentiable Fréchet derivative field.
    have hcont : ContDiffAt ℝ 1 (fderiv ℝ f) (x + t • d) :=
      hf_C2.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    exact hcont.differentiableAt one_ne_zero
  have hgrad : DifferentiableAt ℝ (∇ f) (x + t • d) := by
    -- Rewrite the gradient through the Riesz map to differentiate it.
    simpa [gradient, D] using D.differentiableAt.comp (x + t • d) hfderiv
  have hgradLine :
      HasFDerivAt (fun s : ℝ ↦ ∇ f (x + s • d))
        ((hessian f (x + t • d)).comp (ContinuousLinearMap.toSpanSingleton ℝ d)) t := by
    -- Compose the derivative of the gradient with the derivative of the affine line.
    simpa using (hgrad.hasFDerivAt.comp t (line_hasDerivAt x d t).hasFDerivAt)
  let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) u
  have hscalar :
      HasFDerivAt (fun s : ℝ ↦ φ (∇ f (x + s • d)))
        (φ.comp ((hessian f (x + t • d)).comp (ContinuousLinearMap.toSpanSingleton ℝ d))) t := by
    -- Postcompose the line-gradient map with the scalar functional `v ↦ ⟪v, u⟫`.
    simpa [φ] using ((φ.hasFDerivAt).comp t hgradLine)
  simpa [φ, InnerProductSpace.toDual_apply_apply, real_inner_comm] using hscalar.hasDerivAt

/-- Helper for Theorem 2.12: differentiating the corrected line restriction gives the tangent
model of the quadratic remainder. -/
private theorem corrected_line_hasDerivAt
    (μ : ℝ) {x d : E} {t : ℝ} (hf_C2 : ContDiffAt ℝ 2 f (x + t • d)) :
    HasDerivAt
      (fun s : ℝ ↦ f (x + s • d) - ((μ / 2) * (p d) ^ (2 : ℕ)) * s ^ (2 : ℕ))
      (inner ℝ (∇ f (x + t • d)) d - μ * (p d) ^ (2 : ℕ) * t) t := by
  have hf_C1 : ContDiffAt ℝ 1 f (x + t • d) :=
    hf_C2.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hline :
      HasDerivAt (fun s : ℝ ↦ f (x + s • d)) (inner ℝ (∇ f (x + t • d)) d) t := by
    -- Compose the ambient derivative of `f` with the affine line.
    simpa using
      ((hf_C1.differentiableAt one_ne_zero).hasGradientAt.hasFDerivAt.comp t
        (line_hasDerivAt x d t).hasFDerivAt).hasDerivAt
  have hquad :
      HasDerivAt
        (fun s : ℝ ↦ ((μ / 2) * (p d) ^ (2 : ℕ)) * s ^ (2 : ℕ))
        (μ * (p d) ^ (2 : ℕ) * t) t := by
    -- The quadratic correction differentiates to the expected linear term.
    have hsq : HasDerivAt (fun s : ℝ ↦ s ^ (2 : ℕ)) (2 * t) t := by
      simpa [pow_two, two_mul] using ((hasDerivAt_id t).pow 2)
    convert hsq.const_mul (((μ / 2) * (p d) ^ (2 : ℕ))) using 1
    ring
  -- Subtract the quadratic correction from the line restriction.
  simpa using hline.sub hquad

/-- Helper for Theorem 2.12: differentiating the corrected line derivative gives the Hessian
defect `⟪∇²f(x)d, d⟫ - μ‖d‖²_p`. -/
private theorem corrected_line_deriv_hasDerivAt
    (μ : ℝ) {x d : E} {t : ℝ} (hf_C2 : ContDiffAt ℝ 2 f (x + t • d)) :
    HasDerivAt
      (fun s : ℝ ↦ inner ℝ (∇ f (x + s • d)) d - μ * (p d) ^ (2 : ℕ) * s)
      (inner ℝ (hessian f (x + t • d) d) d - μ * (p d) ^ (2 : ℕ)) t := by
  have hgrad :
      HasDerivAt (fun s : ℝ ↦ inner ℝ (∇ f (x + s • d)) d)
        (inner ℝ (hessian f (x + t • d) d) d) t :=
    scalarized_gradient_along_line_hasDerivAt hf_C2
  have hlin :
      HasDerivAt (fun s : ℝ ↦ μ * (p d) ^ (2 : ℕ) * s)
        (μ * (p d) ^ (2 : ℕ)) t := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (hasDerivAt_id t).const_mul (μ * (p d) ^ (2 : ℕ))
  -- Differentiate the scalarized gradient and subtract the explicit linear correction.
  simpa using hgrad.sub hlin

/-- Helper for Theorem 2.12: a one-variable lower-tangent inequality forces the proposed
derivative field to be monotone on the same interval. -/
private theorem monotoneOn_of_lower_tangent
    {D : Set ℝ} {φ g : ℝ → ℝ}
    (hlower : ∀ s ∈ D, ∀ t ∈ D, φ t ≥ φ s + g s * (t - s)) :
    MonotoneOn g D := by
  intro s hs t ht hst
  rcases eq_or_lt_of_le hst with rfl | hst'
  · rfl
  have hs' := hlower s hs t ht
  have ht' := hlower t ht s hs
  have hineq : 0 ≥ (g s - g t) * (t - s) := by
    linarith
  nlinarith

/-- Helper for Theorem 2.12: under the Hessian lower bound, the corrected line restriction from an
interior base point to an arbitrary feasible point is convex on `[0,1]`. -/
private theorem corrected_segment_convexOn_of_hessian_lower_bound
    (μ : ℝ) (hQ_conv : Convex ℝ Q) (hf_cont : ContinuousOn f Q)
    (hf_C2 : ContDiffOn ℝ 2 f (interior Q))
    (hquad : ∀ x ∈ interior Q, ∀ h : E,
      μ * (p h) ^ 2 ≤ inner ℝ (hessian f x h) h)
    {x y : E} (hx : x ∈ interior Q) (hy : y ∈ Q) :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1)
      (fun t : ℝ ↦ f (x + t • (y - x)) - ((μ / 2) * (p (y - x)) ^ (2 : ℕ)) * t ^ (2 : ℕ)) := by
  let d : E := y - x
  let φ : ℝ → ℝ := fun t ↦ f (x + t • d) - ((μ / 2) * (p d) ^ (2 : ℕ)) * t ^ (2 : ℕ)
  let I : Set ℝ := Set.Icc (0 : ℝ) 1
  have hline_mem_Q : Set.MapsTo (fun t : ℝ ↦ x + t • d) I Q := by
    intro t ht
    have hcombo : (1 - t) • x + t • y ∈ Q :=
      hQ_conv (interior_subset hx) hy (sub_nonneg.mpr ht.2) ht.1 (by linarith)
    have hline_eq : x + t • d = (1 - t) • x + t • y := by
      simp [d, sub_eq_add_neg, smul_add, add_smul, add_left_comm, add_comm]
    change x + t • d ∈ Q
    rw [hline_eq]
    exact hcombo
  have hline_mem_int : ∀ t ∈ interior I, x + t • d ∈ interior Q := by
    intro t ht
    have ht' : t ∈ Set.Ioo (0 : ℝ) 1 := by
      simpa [I] using ht
    have hcombo : (1 - t) • x + t • y ∈ interior Q :=
      hQ_conv.combo_interior_self_mem_interior hx hy
        (sub_pos.mpr ht'.2) ht'.1.le (by linarith)
    have hline_eq : x + t • d = (1 - t) • x + t • y := by
      simp [d, sub_eq_add_neg, smul_add, add_smul, add_left_comm, add_comm]
    change x + t • d ∈ interior Q
    rw [hline_eq]
    exact hcombo
  have hφ_cont : ContinuousOn φ I := by
    have hcont_line : ContinuousOn (fun t : ℝ ↦ f (x + t • d)) I :=
      hf_cont.comp ((continuous_const.add (continuous_id.smul continuous_const)).continuousOn)
        hline_mem_Q
    have hcont_quad : ContinuousOn
        (fun t : ℝ ↦ ((μ / 2) * (p d) ^ (2 : ℕ)) * t ^ (2 : ℕ)) I := by
      fun_prop
    -- The corrected restriction is the difference of two continuous scalar functions.
    simpa [φ] using hcont_line.sub hcont_quad
  have hφ' :
      ∀ t ∈ interior I,
        HasDerivWithinAt φ
          (inner ℝ (∇ f (x + t • d)) d - μ * (p d) ^ (2 : ℕ) * t)
          (interior I) t := by
    intro t ht
    have htC2 : ContDiffAt ℝ 2 f (x + t • d) := by
      exact hf_C2.contDiffAt (isOpen_interior.mem_nhds (hline_mem_int t ht))
    -- On the open interval `(0,1)`, the ambient derivative is also the within-interval derivative.
    exact (corrected_line_hasDerivAt (p := p) (x := x) (d := d) (t := t) μ htC2).hasDerivWithinAt
  have hφ'' :
      ∀ t ∈ interior I,
        HasDerivWithinAt
          (fun s : ℝ ↦ inner ℝ (∇ f (x + s • d)) d - μ * (p d) ^ (2 : ℕ) * s)
          (inner ℝ (hessian f (x + t • d) d) d - μ * (p d) ^ (2 : ℕ))
          (interior I) t := by
    intro t ht
    have htC2 : ContDiffAt ℝ 2 f (x + t • d) := by
      exact hf_C2.contDiffAt (isOpen_interior.mem_nhds (hline_mem_int t ht))
    have hderivAt :=
      corrected_line_deriv_hasDerivAt (p := p) (x := x) (d := d) (t := t) μ htC2
    -- Differentiate the corrected one-dimensional derivative.
    exact hderivAt.hasDerivWithinAt
  have hφ''_nonneg :
      ∀ t ∈ interior I,
        0 ≤ inner ℝ (hessian f (x + t • d) d) d - μ * (p d) ^ (2 : ℕ) := by
    intro t ht
    have htdom : x + t • d ∈ interior Q := hline_mem_int t ht
    -- The Hessian lower bound says exactly that the corrected second derivative is nonnegative.
    linarith [hquad (x + t • d) htdom d]
  -- The corrected line restriction is convex because its second derivative is nonnegative.
  simpa [I, φ] using
    convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc (0 : ℝ) 1) hφ_cont hφ' hφ'' hφ''_nonneg

/-- Helper for Theorem 2.12: the source-facing lower-tangent inequality on a convex set is
equivalent to the Hessian quadratic-form lower bound on the interior. -/
private theorem interior_lower_tangent_quadratic_iff_hessian_quadratic_form_lower_bound_aux
    (μ : ℝ) (hQ_conv : Convex ℝ Q) (hf_cont : ContinuousOn f Q)
    (hf_C2 : ContDiffOn ℝ 2 f (interior Q)) :
    (∀ x : E, x ∈ interior Q → ∀ y : E, y ∈ Q →
      f y ≥ f x + inner ℝ (∇ f x) (y - x) + (μ / 2) * (p (y - x)) ^ 2) ↔
      ∀ x ∈ interior Q, ∀ h : E,
        μ * (p h) ^ 2 ≤ inner ℝ (hessian f x h) h := by
  constructor
  · intro hlower x hx h
    by_cases hh : h = 0
    · -- The zero direction is immediate.
      simp [hh]
    rcases Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hx) with ⟨r, hr_pos, hr_ball⟩
    let δ : ℝ := r / (2 * ‖h‖)
    let I : Set ℝ := Set.Icc (-δ) δ
    have hnorm_pos : 0 < ‖h‖ := norm_pos_iff.mpr hh
    have hδ_pos : 0 < δ := by
      dsimp [δ]
      positivity
    have hzero_mem : (0 : ℝ) ∈ I := by
      dsimp [I]
      constructor <;> linarith
    have hline_mem : Set.MapsTo (fun t : ℝ ↦ x + t • h) I (interior Q) := by
      intro t ht
      apply hr_ball
      rw [Metric.mem_ball, dist_eq_norm]
      have habs : |t| ≤ δ := by
        exact abs_le.mpr ⟨ht.1, ht.2⟩
      have hnorm :
          ‖x + t • h - x‖ = |t| * ‖h‖ := by
        calc
          ‖x + t • h - x‖ = ‖t • h‖ := by
            congr
            abel_nf
          _ = |t| * ‖h‖ := by
            simpa [Real.norm_eq_abs] using norm_smul t h
      have hhalf : δ * ‖h‖ = r / 2 := by
        dsimp [δ]
        field_simp [hnorm_pos.ne']
      have hbound : ‖x + t • h - x‖ < r := by
        rw [hnorm]
        have hle : |t| * ‖h‖ ≤ r / 2 := by
          calc
            |t| * ‖h‖ ≤ δ * ‖h‖ := mul_le_mul_of_nonneg_right habs (norm_nonneg _)
            _ = r / 2 := hhalf
        linarith
      simpa using hbound
    let φ : ℝ → ℝ := fun t ↦ f (x + t • h) - ((μ / 2) * (p h) ^ (2 : ℕ)) * t ^ (2 : ℕ)
    let g : ℝ → ℝ := fun t ↦ inner ℝ (∇ f (x + t • h)) h - μ * (p h) ^ (2 : ℕ) * t
    have hline_lower :
        ∀ s ∈ I, ∀ t ∈ I, φ t ≥ φ s + g s * (t - s) := by
      intro s hs t ht
      have hs_int : x + s • h ∈ interior Q := hline_mem hs
      have ht_int : x + t • h ∈ interior Q := hline_mem ht
      have hbase := hlower (x + s • h) hs_int (x + t • h) (interior_subset ht_int)
      have hsub : x + t • h - (x + s • h) = (t - s) • h := by
        calc
          x + t • h - (x + s • h) = t • h - s • h := by
            abel_nf
          _ = (t - s) • h := by
            rw [sub_smul]
      have hp :
          (p ((t - s) • h)) ^ (2 : ℕ) =
            (t - s) ^ (2 : ℕ) * (p h) ^ (2 : ℕ) := by
        rw [map_smul_eq_mul]
        rw [Real.norm_eq_abs, mul_pow, sq_abs]
      have hbase' :
          f (x + t • h) ≥
            f (x + s • h) + (t - s) * inner ℝ (∇ f (x + s • h)) h +
              ((μ / 2) * (p h) ^ (2 : ℕ)) * (t - s) ^ (2 : ℕ) := by
        rw [hsub, real_inner_smul_right] at hbase
        rw [hp] at hbase
        simpa [mul_assoc, mul_left_comm, mul_comm] using hbase
      -- Repackage the tangent inequality as a one-variable lower support condition.
      dsimp [φ, g]
      linarith
    have hg_mono : MonotoneOn g I :=
      monotoneOn_of_lower_tangent hline_lower
    have hxC2 : ContDiffAt ℝ 2 f x := hf_C2.contDiffAt (isOpen_interior.mem_nhds hx)
    have hderiv :
        HasDerivWithinAt g
          (inner ℝ (hessian f x h) h - μ * (p h) ^ (2 : ℕ))
          I 0 := by
      simpa [g] using
        (corrected_line_deriv_hasDerivAt (p := p) (x := x) (d := h) (t := 0) μ
          (by simpa using hxC2)).hasDerivWithinAt
    have hnonneg : 0 ≤ derivWithin g I 0 := by
      simpa using (hg_mono.derivWithin_nonneg : 0 ≤ derivWithin g I 0)
    have hderiv_eq :
        derivWithin g I 0 = inner ℝ (hessian f x h) h - μ * (p h) ^ (2 : ℕ) := by
      exact hderiv.derivWithin ((uniqueDiffOn_Icc (show -δ < δ by linarith)).uniqueDiffWithinAt
        hzero_mem)
    rw [hderiv_eq] at hnonneg
    linarith
  · intro hquad x hx y hy
    let d : E := y - x
    let φ : ℝ → ℝ := fun t ↦ f (x + t • d) - ((μ / 2) * (p d) ^ (2 : ℕ)) * t ^ (2 : ℕ)
    have hφ_conv :
        ConvexOn ℝ (Set.Icc (0 : ℝ) 1) φ := by
      simpa [φ, d] using
        corrected_segment_convexOn_of_hessian_lower_bound
          (p := p) (Q := Q) (f := f) μ hQ_conv hf_cont hf_C2 hquad hx hy
    have hxC2 : ContDiffAt ℝ 2 f x := hf_C2.contDiffAt (isOpen_interior.mem_nhds hx)
    have hderiv0 :
        HasDerivWithinAt φ (inner ℝ (∇ f x) d) (Set.Icc (0 : ℝ) 1) 0 := by
      -- The quadratic correction has zero derivative at the left endpoint.
      simpa [φ, d] using
        (corrected_line_hasDerivAt (p := p) (x := x) (d := d) (t := 0) μ
          (by simpa using hxC2)).hasDerivWithinAt
    have hslope :=
      hφ_conv.le_slope_of_hasDerivWithinAt (by simp) (by simp) zero_lt_one hderiv0
    have hslope' :
        inner ℝ (∇ f x) d ≤ f (x + 1 • d) - ((μ / 2) * (p d) ^ (2 : ℕ)) - f x := by
      simpa [φ, d, slope] using hslope
    have hslope'' :
        inner ℝ (∇ f x) d ≤ f y - ((μ / 2) * (p d) ^ (2 : ℕ)) - f x := by
      simpa [d] using hslope'
    have hresult :
        f y ≥ f x + inner ℝ (∇ f x) (y - x) + (μ / 2) * (p (y - x)) ^ 2 := by
      linarith [hslope'']
    simpa using hresult

namespace StrongConvexOnWith

/-- On an open convex owner domain, positive-parameter strong convexity with respect to an
arbitrary seminorm is equivalent to the pointwise Hessian quadratic-form lower bound. The
source-facing theorem below specializes this intrinsic owner statement to `U = interior Q` and
then extends the lower-tangent inequality from `x ∈ interior Q` to arbitrary `y ∈ Q`. -/
theorem iff_hessian_quadratic_form_lower_bound
    (hμ : 0 < μ) (hU_open : IsOpen U) (hU_conv : Convex ℝ U) (hf_C2 : ContDiffOn ℝ 2 f U) :
    StrongConvexOnWith p μ U f ↔
      ∀ x ∈ U, ∀ h : E,
        μ * (p h) ^ 2 ≤ inner ℝ (hessian f x h) h := by
  constructor
  · intro hf
    have hf_cont : ContinuousOn f U := hf_C2.continuousOn
    have hlower :
        ∀ x : E, x ∈ interior U → ∀ y : E, y ∈ U →
          f y ≥ f x + inner ℝ (∇ f x) (y - x) + (μ / 2) * (p (y - x)) ^ 2 := by
      intro x hx y hy
      have hxU : x ∈ U := by simpa [hU_open.interior_eq] using hx
      have hxC2 : ContDiffAt ℝ 2 f x := hf_C2.contDiffAt (hU_open.mem_nhds hxU)
      have hdiffx : DifferentiableAt ℝ f x :=
        (hxC2.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).differentiableAt one_ne_zero
      have hgradx : HasGradientAt f (∇ f x) x := hdiffx.hasGradientAt
      -- Strong convexity gives the corrected lower tangent inequality on the owner domain.
      exact hf.lower_tangent_quadratic hxU hy hgradx
    -- Specialize the source-facing equivalence to the open owner domain `U = interior U`.
    simpa [hU_open.interior_eq] using
      (interior_lower_tangent_quadratic_iff_hessian_quadratic_form_lower_bound_aux
        (p := p) (Q := U) (f := f) μ hU_conv hf_cont
        (by simpa [hU_open.interior_eq] using hf_C2)).1 hlower
  · intro hquad
    refine ⟨hU_conv, hμ, ?_⟩
    intro x hx y hy a b ha hb hab
    let d : E := y - x
    let c : ℝ := (μ / 2) * (p d) ^ (2 : ℕ)
    let φ : ℝ → ℝ := fun t ↦ f (x + t • d) - ((μ / 2) * (p d) ^ (2 : ℕ)) * t ^ (2 : ℕ)
    have hx_int : x ∈ interior U := by simpa [hU_open.interior_eq] using hx
    have hφ_conv :
        ConvexOn ℝ (Set.Icc (0 : ℝ) 1) φ := by
      simpa [φ, d, hU_open.interior_eq] using
        corrected_segment_convexOn_of_hessian_lower_bound
          (p := p) (Q := U) (f := f) μ hU_conv hf_C2.continuousOn
          (by simpa [hU_open.interior_eq] using hf_C2)
          (by simpa [hU_open.interior_eq] using hquad) hx_int hy
    have hsegment :
        φ (a • (0 : ℝ) + b • (1 : ℝ)) ≤ a • φ 0 + b • φ 1 := by
      exact hφ_conv.2 (by simp) (by simp) ha hb hab
    have hab' : a = 1 - b := by
      linarith
    have hline_eq : x + b • d = a • x + b • y := by
      calc
        x + b • d = (1 - b) • x + b • y := by
          simp [d, sub_eq_add_neg, smul_add, add_smul, add_left_comm, add_comm]
        _ = a • x + b • y := by
          rw [hab']
    have hp_sym : p d = p (x - y) := by
      simpa [d, sub_eq_add_neg] using (map_neg_eq_map p (x - y))
    have hsegment' :
        f (a • x + b • y) - c * b ^ (2 : ℕ) ≤ a * f x + b * (f y - c) := by
      simpa [φ, c, hline_eq, d, smul_eq_mul] using hsegment
    -- Evaluate convexity of the corrected line restriction at the endpoint weights `a, b`.
    have hresult :
        f (a • x + b • y) ≤
          a • f x + b • f y - a * b * ((μ / 2) * (p (x - y)) ^ (2 : ℕ)) := by
      dsimp [c] at hsegment'
      rw [hp_sym] at hsegment'
      have hab'' : a * b = b - b ^ (2 : ℕ) := by
        nlinarith [hab]
      have hresult' :
          f (a • x + b • y) ≤
            a * f x + b * f y - (b - b ^ (2 : ℕ)) * ((μ / 2) * (p (x - y)) ^ (2 : ℕ)) := by
        linarith [hsegment']
      rw [smul_eq_mul, smul_eq_mul, hab'']
      exact hresult'
    simpa [smul_eq_mul] using hresult

end StrongConvexOnWith

/-- Theorem 2.12 on the canonical owner layer: for a convex set in a real Hilbert space, a
function that is continuous on `Q` and `C²` on `interior Q` satisfies the strong-convexity tangent
inequality with parameter `μ` if and only if its Hessian quadratic form is bounded below by
`μ ‖h‖²_p` at every interior point. The theorem stays at the arbitrary-seminorm owner layer of
`Definition_2_14`; the textbook `ℝⁿ` statement is the finite-dimensional specialization. -/
-- Proof sketch: for the forward implication, restrict `f` to each line `α ↦ x + α • h`,
-- apply the defining lower tangent inequality with `y = x + α • h`, divide by `α ^ 2`, and let
-- `α → 0` to identify the limit with `⟪hessian f x h, h⟫`. For `0 < μ`, the intrinsic owner layer
-- is `StrongConvexOnWith p μ (interior Q) f`, identified above with the same Hessian lower bound
-- on the open convex owner domain `interior Q`.
-- For the displayed source-facing statement, fix `x ∈ interior Q` and `y ∈ Q`, study
-- `t ↦ f (x + t • (y - x))` on `[0,1]`, use convexity of `Q` to keep the segment inside
-- `interior Q` for `t < 1`, integrate the lower bound on the second derivative, and recover the
-- quadratic lower tangent inequality at `t = 1`. No explicit nonempty-interior hypothesis is
-- needed in Lean because both sides quantify only over `x ∈ interior Q`.
theorem interior_lower_tangent_quadratic_iff_hessian_quadratic_form_lower_bound
    (μ : ℝ) (hQ_conv : Convex ℝ Q) (hf_cont : ContinuousOn f Q)
    (hf_C2 : ContDiffOn ℝ 2 f (interior Q)) :
    (∀ x : E, x ∈ interior Q → ∀ y : E, y ∈ Q →
      f y ≥ f x + inner ℝ (∇ f x) (y - x) + (μ / 2) * (p (y - x)) ^ 2) ↔
      ∀ x ∈ interior Q, ∀ h : E,
        μ * (p h) ^ 2 ≤ inner ℝ (hessian f x h) h := by
  -- The source-facing theorem is exactly the private helper proved above.
  simpa using
    interior_lower_tangent_quadratic_iff_hessian_quadratic_form_lower_bound_aux
      (p := p) (Q := Q) (f := f) μ hQ_conv hf_cont hf_C2

end
