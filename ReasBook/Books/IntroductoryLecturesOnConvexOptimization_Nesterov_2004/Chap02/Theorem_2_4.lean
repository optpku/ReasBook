/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_16
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_4_19
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_3

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
noncomputable section

open scoped Gradient

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Primary domain: twice continuously differentiable convexity criteria on open convex subsets of
real Hilbert spaces.

Sampled owner-style declarations:
* mathlib `ConvexOn`
* mathlib `(hessian f x).IsPositive`
* mathlib `ContinuousLinearMap.isPositive_iff`
* Chapter 1 `fderiv_gradient_isSymmetric_of_contDiffAt`
* Chapter 2 `ConvexOn.gradient_monotone`

Best owner abstraction:
* source-facing convexity owner: `ConvexOn ℝ Q f`
* canonical Hessian object at `x`: `hessian f x`

Source/core/bridge triage:
* source-facing: convexity of `f` on the open convex set `Q`
* core/canonical: pointwise positivity of the Hessian operator
* bridge/view: nonnegativity of the associated quadratic form

Primitive data:
* the feasible set `Q`
* the objective `f`
* openness and convexity of `Q`
* `C²` regularity `ContDiffOn ℝ 2 f Q`

Derived API:
* `convexOn_iff_hessian_quadratic_form_nonneg`, obtained as the quadratic-form bridge from the
  canonical Hessian owner
* `convexOn_iff_hessian_isPositive`

The public theorem therefore stays centered on `ConvexOn ℝ Q f` and the owner property
`(hessian f x).IsPositive`. The quadratic-form statement is kept only as
the minimal bridge needed by downstream Hessian-bound files, and the textbook `ℝⁿ` statement is a
direct specialization. -/

section

variable {Q : Set E} {f : E → ℝ}

/-- Helper for Theorem 2.4: on an open set, the within-gradient agrees with the ambient
gradient. -/
private theorem gradientWithin_eq_gradient_of_mem_open
    (hQ_open : IsOpen Q) (hf_C1 : ContDiffOn ℝ 1 f Q) {x : E} (hx : x ∈ Q) :
    gradientWithin f Q x = ∇ f x := by
  -- On an open set, the within-derivative and the ambient derivative agree at differentiable
  -- points, so the corresponding gradients agree as well.
  rw [gradientWithin, gradient]
  congr
  exact fderivWithin_eq_fderiv (hQ_open.uniqueDiffWithinAt hx)
    ((hf_C1.contDiffAt (hQ_open.mem_nhds hx)).differentiableAt_one)

/-- Helper for Theorem 2.4: positivity of the Hessian operator is equivalent to nonnegativity of
its quadratic form at a point of the domain. -/
private theorem hessian_isPositive_iff_quadratic_form_nonneg_at
    (hQ_open : IsOpen Q) (hf_C2 : ContDiffOn ℝ 2 f Q) {x : E} (hx : x ∈ Q) :
    (hessian f x).IsPositive ↔
      ∀ s : E, 0 ≤ inner ℝ (hessian f x s) s := by
  constructor
  · intro hpos s
    -- Positive operators have nonnegative quadratic form on every vector.
    exact hpos.inner_nonneg_left s
  · intro hquad
    -- Recover positivity from the Chapter 1 symmetry owner and the quadratic-form condition.
    exact (ContinuousLinearMap.isPositive_iff _).2
      ⟨fderiv_gradient_isSymmetric_of_contDiffAt (hf_C2.contDiffAt (hQ_open.mem_nhds hx)),
        hquad⟩

/-- Helper for Theorem 2.4: pointwise nonnegativity of the Hessian quadratic form implies the
monotonicity of the ambient gradient on the open convex domain. -/
private theorem gradient_monotone_of_hessian_quadratic_form_nonneg
    (hQ_open : IsOpen Q) (hQ_conv : Convex ℝ Q) (hf_C2 : ContDiffOn ℝ 2 f Q)
    (hquad : ∀ x ∈ Q, ∀ s : E, 0 ≤ inner ℝ (hessian f x s) s) :
    ∀ x ∈ Q, ∀ y ∈ Q, 0 ≤ inner ℝ (∇ f x - ∇ f y) (x - y) := by
  intro x hx y hy
  let d : E := x - y
  let φ := (toDual ℝ E) d
  let g : E → ℝ := fun w ↦ φ (∇ f w)
  have hg_deriv :
      ∀ z ∈ Q,
        HasFDerivWithinAt g (φ.comp (hessian f z)) Q z := by
    intro z hz
    -- Differentiate the scalarized gradient by differentiating `fderiv ℝ f`
    -- and then transporting through the Hilbert-space `toDual` equivalence.
    have hfderiv : DifferentiableAt ℝ (fderiv ℝ f) z := by
      exact
        ((hf_C2.fderiv_of_isOpen hQ_open
          (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableOn
          (by simp) z hz).differentiableAt (hQ_open.mem_nhds hz)
    have hgrad : DifferentiableAt ℝ (∇ f) z := by
      unfold gradient
      simpa using ((toDual ℝ E).symm.differentiableAt.comp z hfderiv)
    have hscalar :
        HasFDerivAt g (φ.comp (hessian f z)) z := by
      simpa [g, φ, Function.comp] using (φ.hasFDerivAt.comp z hgrad.hasFDerivAt)
    exact hscalar.hasFDerivWithinAt
  -- Apply the mean value theorem to the scalarized gradient along the segment from `y` to `x`.
  rcases domain_mvt hg_deriv hQ_conv hy hx with ⟨z, hzseg, hzEq⟩
  have hzQ : z ∈ Q := hQ_conv.segment_subset hy hx hzseg
  have hz_nonneg : 0 ≤ inner ℝ (hessian f z d) d := hquad z hzQ d
  have hleft : g x - g y = inner ℝ d (∇ f x - ∇ f y) := by
    calc
      g x - g y
          = inner ℝ x (∇ f x) - inner ℝ y (∇ f x) -
              (inner ℝ x (∇ f y) - inner ℝ y (∇ f y)) := by
              simp [g, φ, d, InnerProductSpace.toDual_apply_apply, sub_eq_add_neg]
      _ = inner ℝ (x - y) (∇ f x - ∇ f y) := by
            calc
              inner ℝ x (∇ f x) - inner ℝ y (∇ f x) -
                  (inner ℝ x (∇ f y) - inner ℝ y (∇ f y))
                  =
                    (inner ℝ x (∇ f x) - inner ℝ y (∇ f x)) -
                      (inner ℝ x (∇ f y) - inner ℝ y (∇ f y)) := by
                        ring
              _ = inner ℝ (x - y) (∇ f x) - inner ℝ (x - y) (∇ f y) := by
                    rw [inner_sub_left, inner_sub_left]
              _ = inner ℝ (x - y) (∇ f x - ∇ f y) := by
                    rw [inner_sub_right]
      _ = inner ℝ d (∇ f x - ∇ f y) := by
            simp [d]
  have hright :
      (φ.comp (hessian f z)) (x - y) =
        inner ℝ d (hessian f z d) := by
    calc
      (φ.comp (hessian f z)) (x - y)
          =
            inner ℝ x (hessian f z x - hessian f z y) -
              inner ℝ y (hessian f z x - hessian f z y) := by
                simp [d, φ, InnerProductSpace.toDual_apply_apply]
      _ = inner ℝ (x - y) (hessian f z x - hessian f z y) := by
            rw [inner_sub_left]
      _ = inner ℝ (x - y) (hessian f z (x - y)) := by
            rw [map_sub]
      _ = inner ℝ d (hessian f z d) := by
            simp [d]
  have hEq : inner ℝ d (∇ f x - ∇ f y) = inner ℝ d (hessian f z d) := by
    rw [← hleft, hzEq, hright]
  have hEq' : inner ℝ (∇ f x - ∇ f y) d = inner ℝ (hessian f z d) d := by
    simpa [real_inner_comm] using hEq
  have hfinal : 0 ≤ inner ℝ (∇ f x - ∇ f y) d := by
    rw [hEq']
    exact hz_nonneg
  simpa [d] using hfinal

/-- Helper for Theorem 2.4: convexity on the open convex domain forces nonnegativity of every
Hessian quadratic form. -/
private theorem hessian_quadratic_form_nonneg_of_convexOn
    (hQ_open : IsOpen Q) (hf_C2 : ContDiffOn ℝ 2 f Q) (hconv : ConvexOn ℝ Q f) :
    ∀ x ∈ Q, ∀ s : E, 0 ≤ inner ℝ (hessian f x s) s := by
  let hf_C1 : ContDiffOn ℝ 1 f Q := hf_C2.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hmono_within :=
    ConvexOn.gradient_monotone hconv (hf_C1.differentiableOn (by simp))
  have hmono :
      ∀ u ∈ Q, ∀ v ∈ Q, 0 ≤ inner ℝ (∇ f u - ∇ f v) (u - v) := by
    intro u hu v hv
    -- On the open set `Q`, the within-gradient from Theorem 2.3 agrees with the ambient one.
    simpa [gradientWithin_eq_gradient_of_mem_open hQ_open hf_C1 hu,
      gradientWithin_eq_gradient_of_mem_open hQ_open hf_C1 hv] using
      hmono_within hu hv
  intro x hx s
  let γ : ℝ → E := fun t ↦ x + t • s
  let g : ℝ → ℝ := fun t ↦ inner ℝ (∇ f (γ t)) s
  let D : Set ℝ := γ ⁻¹' Q
  have hD_open : IsOpen D := by
    simpa [D, γ] using
      hQ_open.preimage
        (continuous_const.add (continuous_id.smul continuous_const) :
          Continuous (fun t : ℝ ↦ x + t • s))
  have h0D : (0 : ℝ) ∈ D := by
    simp [D, γ, hx]
  rcases Metric.mem_nhds_iff.mp (hD_open.mem_nhds h0D) with ⟨ε, hεpos, hεsub⟩
  let I : Set ℝ := Set.Icc (0 : ℝ) (ε / 2)
  have hhalf_pos : 0 < ε / 2 := by positivity
  have hI_subset : I ⊆ D := by
    intro t ht
    apply hεsub
    rw [Metric.mem_ball, Real.dist_eq]
    have ht_lt : t < ε := by linarith [ht.2, hεpos]
    simpa [abs_of_nonneg ht.1] using ht_lt
  have hg_mono : MonotoneOn g I := by
    intro a ha b hb hab
    have haQ : γ a ∈ Q := hI_subset ha
    have hbQ : γ b ∈ Q := hI_subset hb
    -- Compare the ambient gradients at the two feasible points `γ a` and `γ b`.
    have hpair : 0 ≤ inner ℝ (∇ f (γ b) - ∇ f (γ a)) (γ b - γ a) := hmono _ hbQ _ haQ
    have hγsub : γ b - γ a = (b - a) • s := by
      calc
        γ b - γ a = b • s - a • s := by
          dsimp [γ]
          abel_nf
        _ = (b - a) • s := by
          rw [sub_smul]
    by_cases hab_eq : a = b
    · subst hab_eq
      rfl
    · have hab_lt : a < b := lt_of_le_of_ne hab hab_eq
      have hdiff_pos : 0 < b - a := sub_pos.mpr hab_lt
      rw [hγsub, real_inner_smul_right] at hpair
      have hscalar : 0 ≤ inner ℝ (∇ f (γ b) - ∇ f (γ a)) s := by
        exact nonneg_of_mul_nonneg_right hpair hdiff_pos
      have hrewrite : g b - g a = inner ℝ (∇ f (γ b) - ∇ f (γ a)) s := by
        simp [g, inner_sub_left]
      linarith
  have hderivAt0 : HasDerivAt g (inner ℝ (hessian f x s) s) 0 := by
    -- Differentiate the scalarized gradient along the line `t ↦ x + t • s`.
    let φ := (toDual ℝ E) s
    have hfderiv : DifferentiableAt ℝ (fderiv ℝ f) x := by
      exact
        ((hf_C2.fderiv_of_isOpen hQ_open
          (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableOn
          (by simp) x hx).differentiableAt (hQ_open.mem_nhds hx)
    have hgrad : DifferentiableAt ℝ (∇ f) x := by
      unfold gradient
      simpa using ((toDual ℝ E).symm.differentiableAt.comp x hfderiv)
    have hγ : HasDerivAt γ s 0 := by
      simpa [γ] using
        (HasDerivAt.const_add x
          ((HasDerivAt.smul_const (hasDerivAt_id (0 : ℝ)) s)))
    have hgrad0 : HasFDerivAt (∇ f) (hessian f x) (γ 0) := by
      simpa [γ] using hgrad.hasFDerivAt
    have hgradLine :
        HasFDerivAt (fun t : ℝ ↦ ∇ f (γ t))
          ((hessian f x).comp (ContinuousLinearMap.toSpanSingleton ℝ s)) 0 := by
      simpa [γ] using
        (hgrad0.comp 0 hγ.hasFDerivAt)
    have hscalar :
        HasFDerivAt
          (fun t : ℝ ↦ φ (∇ f (γ t)))
          (φ.comp
            ((hessian f x).comp (ContinuousLinearMap.toSpanSingleton ℝ s))) 0 := by
      simpa [γ] using
        ((φ.hasFDerivAt).comp 0 hgradLine)
    simpa [g, γ, φ, InnerProductSpace.toDual_apply_apply, real_inner_comm] using
      hscalar.hasDerivAt
  have h0I : (0 : ℝ) ∈ I := by
    exact ⟨le_rfl, by positivity⟩
  have hderivWithin :
      derivWithin g I 0 = inner ℝ (hessian f x s) s := by
    exact
      HasDerivWithinAt.derivWithin
        (hderivAt0.hasDerivWithinAt)
        ((uniqueDiffOn_Icc hhalf_pos).uniqueDiffWithinAt h0I)
  have hnonneg : 0 ≤ derivWithin g I 0 := by
    simpa using (hg_mono.derivWithin_nonneg : 0 ≤ derivWithin g I 0)
  rw [hderivWithin] at hnonneg
  exact hnonneg

/-- The Hessian-positivity condition in Theorem 2.4 is equivalently the nonnegativity of the
associated quadratic form at every point of `Q`. -/
-- Proof sketch: the forward direction uses monotonicity of the within-gradient from Theorem 2.3,
-- upgraded to the ambient gradient on the open set `Q`, and differentiates the line restriction
-- `t ↦ ∇ f (x + t • s)` at `t = 0`. The reverse direction first proves ambient gradient
-- monotonicity from the quadratic-form hypothesis by a mean-value argument, then returns to
-- Theorem 2.3 through `gradientWithin`. This is the real-Hilbert-space owner statement; the
-- textbook Euclidean theorem is its finite-dimensional specialization.
theorem convexOn_iff_hessian_quadratic_form_nonneg
    (hQ_open : IsOpen Q) (hQ_conv : Convex ℝ Q) (hf_C2 : ContDiffOn ℝ 2 f Q) :
    ConvexOn ℝ Q f ↔
      ∀ x ∈ Q, ∀ s : E, 0 ≤ inner ℝ (hessian f x s) s := by
  constructor
  · intro hconv
    simpa using hessian_quadratic_form_nonneg_of_convexOn hQ_open hf_C2 hconv
  · intro hquad
    let hf_C1 : ContDiffOn ℝ 1 f Q := hf_C2.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
    have hmono :=
      gradient_monotone_of_hessian_quadratic_form_nonneg hQ_open hQ_conv hf_C2 hquad
    have hmono_within : GradientMonotoneOn Q f := by
      refine fun {x} ↦ ?_
      refine fun {y} ↦ ?_
      intro hx hy
      -- The reverse route first proves ambient gradient monotonicity, then re-enters
      -- Theorem 2.3 through the within-gradient API valid on open sets.
      simpa
          [gradientWithin_eq_gradient_of_mem_open hQ_open hf_C1 hx,
            gradientWithin_eq_gradient_of_mem_open hQ_open hf_C1 hy] using
        hmono x hx y hy
    exact
      ConvexOn.of_gradient_monotone hQ_conv (hf_C1.differentiableOn (by simp)) hmono_within

/-- Theorem 2.4, stated on the canonical real Hilbert-space owner layer: on an open convex set
`Q`, a `C²` function is convex on `Q` if and only if its Hessian is positive at every point of
`Q`; the textbook Euclidean theorem is the finite-dimensional specialization. -/
-- Proof sketch: for the forward direction, restrict `f` to each affine line `t ↦ x + t • s`,
-- use convexity to show that the resulting one-variable `C²` function has nonnegative second
-- derivative, and identify that second derivative with `⟪hessian f x s, s⟫`. For the
-- reverse direction, use the Hessian positivity hypothesis along each segment in the convex set
-- `Q` to obtain convexity of every one-variable restriction, then lift this back to
-- `ConvexOn ℝ Q f`.
theorem convexOn_iff_hessian_isPositive
    (hQ_open : IsOpen Q) (hQ_conv : Convex ℝ Q) (hf_C2 : ContDiffOn ℝ 2 f Q) :
    ConvexOn ℝ Q f ↔
      ∀ x ∈ Q, (hessian f x).IsPositive := by
  constructor
  · intro hconv x hx
    -- First pass through the scalar quadratic-form criterion, then rewrite positivity pointwise.
    simpa using (hessian_isPositive_iff_quadratic_form_nonneg_at hQ_open hf_C2 hx).2
      ((convexOn_iff_hessian_quadratic_form_nonneg hQ_open hQ_conv hf_C2).1 hconv x hx)
  · intro hpos
    -- Translate the operator-valued hypothesis back to the scalar quadratic-form criterion.
    have hquad : ∀ x ∈ Q, ∀ s, 0 ≤ inner ℝ (hessian f x s) s := by
      intro x hx s
      exact
        (hessian_isPositive_iff_quadratic_form_nonneg_at hQ_open hf_C2 hx).1 (hpos x hx) s
    simpa using
      (convexOn_iff_hessian_quadratic_form_nonneg hQ_open hQ_conv hf_C2).2 hquad

end
