/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_4_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_23
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_24
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Lemma_5_1_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Lemma_5_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_12
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_9

-- Declarations for this item will be appended below by the statement pipeline.

open scoped DikinEllipsoidNotation Gradient HessianLocalNorm NewtonDecrement
  SelfConcordantAuxiliaryFunction

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 5.2.1 lies in the Chapter 5 self-concordant minimization / Newton-decrement domain.

Sampled owner declarations:
* `HasPositiveDefiniteHessianOn` in `Definition_5_0_23`, the chapter owner for the
  positive-definite-Hessian regime in which the Newton decrement is evaluated from domain
  membership alone;
* `newtonDecrement`, the notation `λ[f; x | hx]`, and
  `NewtonDecrement.omegaArgOfPosDefMem` in `Definition_5_0_24`, the chapter owner for the Newton
  decrement, its positive-definite-domain theorem surface, and the canonical `ω` argument;
* `hessianLocalNorm` and `hessianLocalNorm_nonneg` in `Definition_5_1_1`, the chapter owner for
  the Hessian local norm;
* `existsUnique_isMinOn_with_suboptimality_bound_of_newtonDecrement_lt_inv` in `Theorem_5_1_13`,
  the chapter minimizer / Newton-decrement owner for the upper `ω_*` bound.

Best owner abstraction:
* source-facing: the minimizer-distance and suboptimality bounds of Theorem 5.2.1;
* core/canonical: `newtonDecrement`, `HasPositiveDefiniteHessianOn`, `hessianLocalNorm`, and the
  chapter self-concordant auxiliary functions;
* bridge/view: the domain-point notation `λ[f; x | hx]` together with the `ω'` / `ω'_*` scalar
  reparameterizations of the same canonical `ω` and `ω_*` arguments.

Primitive data:
* a self-concordant function `f` on `dom` with parameter `Mf`;
* a point `x ∈ dom` and a feasible minimizer `xStar : dom`.
* for the Newton-decrement clauses only, positive definiteness of the Hessian of `f` on `dom`.

Derived API:
* the domain-level Newton decrement `λ[f; x | hx]`;
* the canonical `ω` argument `NewtonDecrement.omegaArgOfPosDefMem Mf f x hx`;
* the canonical `ω_*` argument obtained from the small-decrement hypothesis;
* the local minimizer distance `‖x - xStar‖[f; x]`.

This file stays source-facing. Its Newton-decrement clauses live in the finite-dimensional
positive-definite-Hessian owner layer, while the minimizer-distance clause stays on the weaker
self-concordant/local-norm layer. The refinement removes the file-local duplicate witnesses for
Hessian nondegeneracy from the theorem surface, reusing the Chapter 5 positive-definite-Hessian
owner and the domain-level Newton-decrement bridge directly instead of keeping a parallel
determinant-witness surface. -/

section

variable {dom : Set E} {Mf : NNReal} {f : E → ℝ}
variable [IsSelfConcordantOnWith dom Mf f]

section NewtonDecrementBounds

variable [FiniteDimensional ℝ E]
variable [HasPositiveDefiniteHessianOn dom f]

omit [IsSelfConcordantOnWith dom Mf f] in
/-- Helper for Theorem 5.2.1: the small-Newton-decrement hypothesis forces the self-concordance
parameter to be strictly positive. -/
lemma mf_pos_of_newtonDecrement_lt_inv {x : E} (hx : x ∈ dom)
    (hlambda : λ[f; x | hx] < 1 / (Mf : ℝ)) :
    0 < (Mf : ℝ) := by
  -- The Newton decrement is nonnegative, so `Mf = 0` would make the bound impossible.
  by_contra hMf
  have hMf_nonneg : 0 ≤ (Mf : ℝ) := by
    exact_mod_cast Mf.2
  have hMf_eq_zero : (Mf : ℝ) = 0 := le_antisymm (le_of_not_gt hMf) hMf_nonneg
  have hnonneg : 0 ≤ λ[f; x | hx] := NewtonDecrement.ofPosDefMem_nonneg f x hx
  have hlt0 : λ[f; x | hx] < 0 := by
    simpa [hMf_eq_zero] using hlambda
  linarith

omit [FiniteDimensional ℝ E] [HasPositiveDefiniteHessianOn dom f] in
/-- Helper for Theorem 5.2.1: a minimizer on an open domain is stationary. -/
lemma gradient_eq_zero_at_selfconcordant_minimizer (hopen : IsOpen dom) (xStar : dom)
    (hmin : IsMinOn f dom (xStar : E)) :
    ∇ f (xStar : E) = 0 := by
  -- Convert the constrained minimizer into an ambient local minimizer on the open domain.
  have hlocal : IsLocalMin f (xStar : E) :=
    hmin.isLocalMin (hopen.mem_nhds xStar.2)
  exact isLocalMin_gradient_eq_zero hlocal

/-- Helper for Theorem 5.2.1: the `ω_*` bound from Theorem 5.1.13 transfers from its chosen
minimizer to any supplied minimizer because all minimizers have the same objective value. -/
lemma suboptimality_upper_bound_at_minimizer_of_newtonDecrement_lt_inv
    {x : E} (xStar : dom) (hx : x ∈ dom) (hmin : IsMinOn f dom (xStar : E))
    (hlambda : λ[f; x | hx] < 1 / (Mf : ℝ)) :
    f x - f xStar ≤
      (1 / (Mf : ℝ) ^ (2 : ℕ)) *
        ω_* (NewtonDecrement.omegaStarArgOfPosDefMem Mf f x hx hlambda) := by
  rcases existsUnique_isMinOn_with_suboptimality_bound_of_newtonDecrement_lt_inv
      (Mf := Mf) (f := f) (dom := dom) (x := x) hx hlambda with
    ⟨xOpt, hxOpt, _huniq⟩
  -- Compare the two minimizers by objective value, then transport the theorem-5.1.13 bound.
  have hmin' : ∀ y ∈ dom, f xStar ≤ f y := isMinOn_iff.mp hmin
  have hxOpt' : ∀ y ∈ dom, f xOpt ≤ f y := isMinOn_iff.mp hxOpt.1
  have hvalue : f xStar = f xOpt := by
    apply le_antisymm
    · exact hmin' xOpt xOpt.2
    · exact hxOpt' xStar xStar.2
  simpa [hvalue] using hxOpt.2

omit [FiniteDimensional ℝ E] [HasPositiveDefiniteHessianOn dom f] in
/-- Helper for Theorem 5.2.1: the minimizer-distance hypothesis also forces `M_f` to be
strictly positive. -/
lemma mf_pos_of_minimizerDistance_lt_inv {x : E} (xStar : dom)
    (hr : ‖x - xStar‖[f; x] < 1 / (Mf : ℝ)) :
    0 < (Mf : ℝ) := by
  -- The local norm is nonnegative, so `Mf = 0` would make the strict bound impossible.
  by_contra hMf
  have hMf_nonneg : 0 ≤ (Mf : ℝ) := by
    exact_mod_cast Mf.2
  have hMf_eq_zero : (Mf : ℝ) = 0 := le_antisymm (le_of_not_gt hMf) hMf_nonneg
  have hr_nonneg : 0 ≤ ‖x - xStar‖[f; x] := hessianLocalNorm_nonneg f x (x - xStar)
  have hlt0 : ‖x - xStar‖[f; x] < 0 := by
    simpa [hMf_eq_zero] using hr
  linarith

/-- Helper for Theorem 5.2.1: a quadratic family bounded above by `c` forces the discriminant
estimate `a² ≤ b c`. -/
private theorem sq_le_mul_of_quadratic_family
    {a b c : ℝ} (hb : 0 ≤ b)
    (hline : ∀ t : ℝ, 2 * t * a - t ^ (2 : ℕ) * b ≤ c) :
    a ^ (2 : ℕ) ≤ b * c := by
  sorry

omit [FiniteDimensional ℝ E] [HasPositiveDefiniteHessianOn dom f] in
/-- Helper for Theorem 5.2.1: convexity at the base point `x` makes the linear Taylor term toward
the minimizer nonpositive. -/
lemma minimizer_linear_term_nonpos
    (hself : IsSelfConcordantOnWith dom Mf f)
    {x : E} (xStar : dom) (hx : x ∈ dom) (hmin : IsMinOn f dom (xStar : E)) :
    inner ℝ (∇ f x) (xStar - x) ≤ 0 := by
  have hdiff : DifferentiableAt ℝ f x := by
    -- The Chapter 5 `C³` owner gives an ambient derivative at each interior point.
    exact
      (hself.contDiffOn.contDiffAt (hself.isOpen_domain.mem_nhds hx)).differentiableAt
        (by norm_num : (3 : WithTop ℕ∞) ≠ 0)
  have hgrad :
      gradientWithin f dom x = ∇ f x := by
    -- On the open domain, the within-gradient agrees with the ambient gradient.
    rw [gradientWithin, gradient]
    congr
    exact fderivWithin_eq_fderiv (hself.isOpen_domain.uniqueDiffWithinAt hx) hdiff
  have hsupport :
      f xStar ≥ f x + inner ℝ (∇ f x) (xStar - x) := by
    simpa [hgrad] using
      hself.convexOn.lower_tangent_plane x hx hdiff.differentiableWithinAt (xStar : E) xStar.2
  have hmin_value : f xStar ≤ f x := (isMinOn_iff.mp hmin) x hx
  linarith

/-- Helper for Theorem 5.2.1: the gradient pairing is controlled by the Newton decrement times
the local Hessian norm at `x`. -/
lemma gradient_inner_le_newton_decrement_mul_local_norm
    {x : E} (xStar : dom) (hx : x ∈ dom) :
    inner ℝ (∇ f x) (x - xStar) ≤ λ[f; x | hx] * ‖x - xStar‖[f; x] := by
  sorry

/-- Helper for Theorem 5.2.1: once the Hessian quadratic form is nonnegative, squaring the local
norm recovers it exactly. -/
private theorem sq_hessianLocalNorm_eq_inner_hessian
    {z d : E} (hquad : 0 ≤ inner ℝ d (hessian f z d)) :
    ‖d‖[f; z] ^ (2 : ℕ) = inner ℝ d (hessian f z d) := by
  -- Expand the local norm and use `sqrt(x)^2 = x` on the nonnegative quadratic form.
  simpa [hessianLocalNorm_def] using Real.sq_sqrt hquad

/-- Helper for Theorem 5.2.1: affine lines have the expected derivative. -/
private theorem line_hasDerivAt
    (z d : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ z + s • d) d t := by
  -- Differentiate the scalar parameter and keep the direction fixed.
  simpa [one_smul] using ((hasDerivAt_id t).smul_const d).const_add z

/-- Helper for Theorem 5.2.1: the Hessian is continuous on the self-concordant domain. -/
private theorem hessian_continuousOn
    (hself : IsSelfConcordantOnWith dom Mf f) :
    ContinuousOn (hessian f) dom := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hgrad_contDiff : ContDiffOn ℝ 1 (∇ f) dom := by
    have hfd : ContDiffOn ℝ 1 (fderiv ℝ f) dom :=
      (hself.contDiffOn.of_le
        (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).fderiv_of_isOpen
          hself.isOpen_domain
          (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)
    simpa [gradient, D] using D.contDiff.comp_contDiffOn hfd
  simpa [hessian] using
    (hgrad_contDiff.fderiv_of_isOpen
      hself.isOpen_domain
      (show (0 : WithTop ℕ∞) + 1 ≤ 1 by norm_num)).continuousOn

/-- Helper for Theorem 5.2.1: scalarizing the gradient along an affine line differentiates to the
corresponding Hessian pairing. -/
private theorem scalarized_gradient_line_hasDerivAt
    (hself : IsSelfConcordantOnWith dom Mf f)
    {x d u : E} {t : ℝ} (hxt : x + t • d ∈ dom) :
    HasDerivAt (fun s : ℝ ↦ inner ℝ (∇ f (x + s • d)) u)
      (inner ℝ (hessian f (x + t • d) d) u) t := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfderiv : DifferentiableAt ℝ (fderiv ℝ f) (x + t • d) := by
    have hcont : ContDiffAt ℝ 1 (fderiv ℝ f) (x + t • d) :=
      (hself.contDiffOn.contDiffAt
        (hself.isOpen_domain.mem_nhds hxt)).fderiv_right
          (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 3)
    exact hcont.differentiableAt one_ne_zero
  have hgrad : DifferentiableAt ℝ (∇ f) (x + t • d) := by
    -- Rewrite the gradient through the Riesz map before differentiating it.
    simpa [gradient, D] using D.differentiableAt.comp (x + t • d) hfderiv
  have hgradLine :
      HasFDerivAt (fun s : ℝ ↦ ∇ f (x + s • d))
        ((hessian f (x + t • d)).comp (ContinuousLinearMap.toSpanSingleton ℝ d)) t := by
    -- Compose the gradient derivative with the affine-line derivative.
    simpa using (hgrad.hasFDerivAt.comp t (line_hasDerivAt x d t).hasFDerivAt)
  let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) u
  have hscalar :
      HasFDerivAt (fun s : ℝ ↦ φ (∇ f (x + s • d)))
        (φ.comp ((hessian f (x + t • d)).comp (ContinuousLinearMap.toSpanSingleton ℝ d))) t := by
    -- Postcompose with the scalar functional.
    simpa [φ] using (φ.hasFDerivAt.comp t hgradLine)
  simpa [φ, InnerProductSpace.toDual_apply_apply, real_inner_comm] using hscalar.hasDerivAt

/-- Helper for Theorem 5.2.1: nonnegative scalar dilations scale the local norm linearly at a
domain point. -/
private theorem hessianLocalNorm_smul_nonneg_at_mem
    (hself : IsSelfConcordantOnWith dom Mf f)
    {z d : E} (hz : z ∈ dom) {t : ℝ} (ht : 0 ≤ t) :
    ‖t • d‖[f; z] = t * ‖d‖[f; z] := by
  -- Expand the local norm and simplify the square root of `t²` times the Hessian quadratic form.
  have hquad : 0 ≤ inner ℝ d (hessian f z d) :=
    hself.hessian_posSemidef hz d
  calc
    ‖t • d‖[f; z] = Real.sqrt ((t * t) * inner ℝ d (hessian f z d)) := by
      rw [hessianLocalNorm_def]
      congr 1
      simp [inner_smul_left, inner_smul_right, mul_assoc]
    _ = Real.sqrt (inner ℝ d (hessian f z d)) * Real.sqrt (t * t) := by
      rw [mul_comm, Real.sqrt_mul hquad]
    _ = t * ‖d‖[f; z] := by
      rw [show t * t = t ^ (2 : ℕ) by ring, Real.sqrt_sq_eq_abs, abs_of_nonneg ht,
        hessianLocalNorm_def]
      ring

/-- Helper for Theorem 5.2.1: every point on the chord from `x` to `y` stays in the convex
domain. -/
private theorem segment_point_mem
    (hself : IsSelfConcordantOnWith dom Mf f)
    {x y : E} (hx : x ∈ dom) (hy : y ∈ dom)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    x + t • (y - x) ∈ dom := by
  -- Rewrite the segment point as a convex combination and use domain convexity.
  have hrewrite : x + t • (y - x) = (1 - t) • x + t • y := by
    rw [smul_sub]
    rw [show (1 - t : ℝ) • x = x - t • x by rw [sub_smul, one_smul]]
    abel
  have hconv := hself.convex_domain
  have h1t : 0 ≤ 1 - t := by linarith
  have hsum : (1 - t) + t = 1 := by ring
  rw [hrewrite]
  exact hconv hx hy h1t ht0 hsum

/-- Helper for Theorem 5.2.1: the rational lower integrand integrates to the expected transport
factor. -/
private theorem integral_sq_div_eq_scaled_sq_div
    {r α : ℝ} (hα0 : 0 ≤ α) (hr0 : 0 ≤ r) :
    ∫ t in 0..α, r ^ (2 : ℕ) / (1 + t * (Mf : ℝ) * r) ^ (2 : ℕ) =
      α * r ^ (2 : ℕ) / (1 + α * (Mf : ℝ) * r) := by
  sorry

/-- Helper for Theorem 5.2.1: along a self-concordant segment, the gradient increment paired with
the full chord is bounded below by the source transport factor. -/
private theorem segment_gradient_increment_lower_bound_at_base
    {x y : E} (hx : x ∈ dom) (hy : y ∈ dom)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    let d := y - x
    let r := ‖d‖[f; x]
    inner ℝ (∇ f (x + α • d) - ∇ f x) d ≥
      α * r ^ (2 : ℕ) / (1 + α * (Mf : ℝ) * r) := by
  sorry

omit [FiniteDimensional ℝ E] [HasPositiveDefiniteHessianOn dom f] in
/-- Helper for Theorem 5.2.1: integrating the scalar restriction of `f` along a segment recovers
the gradient pairing integral. -/
private theorem segment_scalar_integral_eq
    (hself : IsSelfConcordantOnWith dom Mf f)
    {x d : E} (hsegment : ∀ t ∈ Set.Icc (0 : ℝ) 1, x + t • d ∈ dom) :
    f (x + d) - f x = ∫ t in 0..1, inner ℝ (∇ f (x + t • d)) d := by
  sorry

omit [FiniteDimensional ℝ E] [HasPositiveDefiniteHessianOn dom f] in
/-- Helper for Theorem 5.2.1: the second scalar integration in the source lower-bound argument
evaluates to the logarithmic `ω` term. -/
private theorem integral_mul_sq_div_eq_omega
    {r : ℝ} (hr0 : 0 ≤ r) (hMf_pos : 0 < (Mf : ℝ)) :
    let tω := selfConcordantOmegaArg Mf r (neg_one_lt_mf_mul_of_nonneg hr0)
    ∫ t in 0..1, t * r ^ (2 : ℕ) / (1 + t * (Mf : ℝ) * r) =
      (1 / ((Mf : ℝ) ^ (2 : ℕ))) * ω tω := by
  sorry

omit [FiniteDimensional ℝ E] [HasPositiveDefiniteHessianOn dom f] in
/-- Helper for Theorem 5.2.1: an admissible local-norm step satisfies the lower Taylor bound with
the `ω` remainder. -/
private theorem taylor_lower_bound_with_selfConcordantOmega_of_minimizerDistance_lt_inv
    (hself : IsSelfConcordantOnWith dom Mf f)
    {x : E} (xStar : dom) (hx : x ∈ dom)
    (hr : ‖x - xStar‖[f; x] < 1 / (Mf : ℝ)) :
    let r := ‖x - xStar‖[f; x]
    let tω := selfConcordantOmegaArg Mf r
      (neg_one_lt_mf_mul_of_nonneg (hessianLocalNorm_nonneg f x (x - xStar)))
    f xStar ≥
      f x + inner ℝ (∇ f x) (xStar - x) + (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω tω := by
  sorry

/-- Helper for Theorem 5.2.1: the source lower-pairing estimate toward the minimizer reduces the
upper half of `(5.2.4)` to explicit scalar algebra. -/
lemma gradient_pairing_lower_bound_to_minimizer
    {x : E} (xStar : dom) (hx : x ∈ dom) (hmin : IsMinOn f dom (xStar : E))
    (hlambda : λ[f; x | hx] < 1 / (Mf : ℝ)) :
    let r := ‖x - xStar‖[f; x]
    r ^ (2 : ℕ) / (1 + (Mf : ℝ) * r) ≤ inner ℝ (∇ f x) (x - xStar) := by
  let r := ‖x - xStar‖[f; x]
  -- Route correction: specialize the source segment-FTC lower bound at `α = 1` and use
  -- stationarity of the minimizer to rewrite the resulting gradient increment.
  have _ := hlambda
  have hgrad0 : ∇ f (xStar : E) = 0 :=
    gradient_eq_zero_at_selfconcordant_minimizer
      (dom := dom) (f := f) (inferInstance : IsSelfConcordantOnWith dom Mf f).isOpen_domain
      xStar hmin
  have hdist_symm : ‖(xStar : E) - x‖[f; x] = r := by
    -- Rewrite the reversed displacement as the negation of `x - xStar`.
    have hz : (xStar : E) - x = -(x - xStar) := by
      abel
    rw [hz, hessianLocalNorm_neg]
  have hpoint : x + (1 : ℝ) • ((xStar : E) - x) = (xStar : E) := by
    simp [sub_eq_add_neg]
  have hseg :
      inner ℝ (∇ f (x + (1 : ℝ) • ((xStar : E) - x)) - ∇ f x) ((xStar : E) - x) ≥
        (1 : ℝ) * ‖(xStar : E) - x‖[f; x] ^ (2 : ℕ) /
          (1 + (1 : ℝ) * (Mf : ℝ) * ‖(xStar : E) - x‖[f; x]) := by
    simpa using
      segment_gradient_increment_lower_bound_at_base
        (Mf := Mf) (f := f) (x := x) (y := (xStar : E)) hx xStar.2
        (α := 1) (by norm_num) (by norm_num)
  have hseg' :
      r ^ (2 : ℕ) / (1 + (Mf : ℝ) * r) ≤
        inner ℝ (∇ f (xStar : E) - ∇ f x) ((xStar : E) - x) := by
    simpa [hpoint, hdist_symm, r, one_mul, mul_assoc, mul_left_comm, mul_comm] using hseg
  calc
    r ^ (2 : ℕ) / (1 + (Mf : ℝ) * r) ≤
        inner ℝ (∇ f (xStar : E) - ∇ f x) ((xStar : E) - x) := hseg'
    _ = inner ℝ (∇ f x) (x - xStar) := by
      rw [hgrad0, zero_sub]
      have hz : (xStar : E) - x = -((x : E) - xStar) := by
        abel
      rw [hz, inner_neg_left, inner_neg_right]
      simp

omit [FiniteDimensional ℝ E] [HasPositiveDefiniteHessianOn dom f] in
/-- Helper for Theorem 5.2.1: under the local minimizer-distance hypothesis `r_*(x) < 1 / M_f`,
the lower side of `(5.2.5)` is the direct Dikin-local Taylor lower bound at the base point `x`.
-/
lemma suboptimality_lower_bound_of_minimizerDistance_lt_inv
    {x : E} (xStar : dom) (hx : x ∈ dom) (hmin : IsMinOn f dom (xStar : E))
    (hr : ‖x - xStar‖[f; x] < 1 / (Mf : ℝ)) :
    let r := ‖x - xStar‖[f; x]
    let tω := selfConcordantOmegaArg Mf r
      (neg_one_lt_mf_mul_of_nonneg (hessianLocalNorm_nonneg f x (x - xStar)))
    ω tω ≤ (Mf : ℝ) ^ (2 : ℕ) * (f x - f xStar) := by
  sorry

omit [FiniteDimensional ℝ E] [HasPositiveDefiniteHessianOn dom f] in
/-- Helper for Theorem 5.2.1: under the local minimizer-distance hypothesis `r_*(x) < 1 / M_f`,
the upper side of `(5.2.5)` is the direct Taylor upper bound with the minimizer linear term
discarded. -/
lemma suboptimality_upper_bound_of_minimizerDistance_lt_inv
    {x : E} (xStar : dom) (hx : x ∈ dom) (hmin : IsMinOn f dom (xStar : E))
    (hr : ‖x - xStar‖[f; x] < 1 / (Mf : ℝ)) :
    let r := ‖x - xStar‖[f; x]
    let τω := selfConcordantOmegaStarArg Mf r (mf_mul_lt_one_of_lt_inv hr)
    (Mf : ℝ) ^ (2 : ℕ) * (f x - f xStar) ≤ ω_* τω := by
  sorry

/-- Helper for Theorem 5.2.1: once the minimizer pairing lower bound is available, the upper
distance bound in `(5.2.4)` is a scalar consequence of the Cauchy adapter. -/
lemma omega_prime_star_upper_from_pairing_lower
    {x : E} (xStar : dom) (hx : x ∈ dom) (hmin : IsMinOn f dom (xStar : E))
    (hlambda : λ[f; x | hx] < 1 / (Mf : ℝ)) :
    let τω := NewtonDecrement.omegaStarArgOfPosDefMem Mf f x hx hlambda
    (Mf : ℝ) * ‖x - xStar‖[f; x] ≤ ω'_* τω := by
  let r := ‖x - xStar‖[f; x]
  let τω := NewtonDecrement.omegaStarArgOfPosDefMem Mf f x hx hlambda
  let τ : ℝ := (Mf : ℝ) * λ[f; x | hx]
  let s : ℝ := (Mf : ℝ) * r
  have hMf_pos : 0 < (Mf : ℝ) :=
    mf_pos_of_newtonDecrement_lt_inv (Mf := Mf) (f := f) hx hlambda
  have hMf_nonneg : 0 ≤ (Mf : ℝ) := hMf_pos.le
  have hr_nonneg : 0 ≤ r := by
    simpa [r] using hessianLocalNorm_nonneg f x (x - xStar)
  by_cases hr_zero : r = 0
  · -- The zero-distance case is immediate because `ω'_*` is nonnegative on `[0, 1)`.
    have hτ_lt_one : τ < 1 := by
      simpa [τω, τ] using τω.property
    have hτ_nonneg : 0 ≤ τ := by
      have hnd_nonneg : 0 ≤ λ[f; x | hx] := NewtonDecrement.ofPosDefMem_nonneg f x hx
      dsimp [τ]
      exact mul_nonneg hMf_nonneg hnd_nonneg
    have hτ_arg_nonneg : 0 ≤ (τω : ℝ) := by
      simpa [τω, τ] using hτ_nonneg
    have hnonneg : 0 ≤ ω'_* τω := by
      exact selfConcordantOmegaPrimeStar_nonneg hτ_arg_nonneg hτ_lt_one
    simpa [r, s, hr_zero, τω, τ, selfConcordantOmegaPrimeStar_apply] using hnonneg
  · have hr_pos : 0 < r := lt_of_le_of_ne hr_nonneg (by simpa [eq_comm] using hr_zero)
    have hpair_lower :
        r ^ (2 : ℕ) / (1 + (Mf : ℝ) * r) ≤ inner ℝ (∇ f x) (x - xStar) := by
      simpa [r] using
        gradient_pairing_lower_bound_to_minimizer
          (Mf := Mf) (f := f) xStar hx hmin hlambda
    have hpair_upper :
        inner ℝ (∇ f x) (x - xStar) ≤ λ[f; x | hx] * r := by
      simpa [r] using
        gradient_inner_le_newton_decrement_mul_local_norm
          (f := f) xStar hx
    have hpair :
        r ^ (2 : ℕ) / (1 + (Mf : ℝ) * r) ≤ λ[f; x | hx] * r :=
      le_trans hpair_lower hpair_upper
    have hden_pos : 0 < 1 + (Mf : ℝ) * r := by positivity
    have hscaled_frac : s / (1 + s) ≤ τ := by
      -- Divide the pairing inequality by the positive local distance, then rescale by `M_f`.
      have hdiv : r / (1 + (Mf : ℝ) * r) ≤ λ[f; x | hx] := by
        have htmp : r ≤ λ[f; x | hx] * (1 + (Mf : ℝ) * r) := by
          have hpair' : r ^ (2 : ℕ) ≤ λ[f; x | hx] * r * (1 + (Mf : ℝ) * r) := by
            exact (div_le_iff₀ hden_pos).1 hpair
          exact (mul_le_mul_iff_of_pos_left hr_pos).1 <| by
            simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hpair'
        exact (div_le_iff₀ hden_pos).2 htmp
      have hmul :=
        mul_le_mul_of_nonneg_left hdiv hMf_nonneg
      simpa [s, τ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
    have hτ_lt_one : τ < 1 := by
      simpa [τω, τ] using τω.property
    have hτ_denom_pos : 0 < 1 - τ := by
      linarith
    have hs_nonneg : 0 ≤ s := by
      exact mul_nonneg hMf_nonneg hr_nonneg
    have hωprime :
        ω'_* τω = τ / (1 - τ) := by
      rw [selfConcordantOmegaPrimeStar_apply]
      simp [τω, τ]
    have hs_mul : s * (1 - τ) ≤ τ := by
      have htmp : s ≤ τ * (1 + s) := by
        exact (div_le_iff₀ (by positivity)).1 hscaled_frac
      nlinarith
    have hs_le : s ≤ τ / (1 - τ) := by
      exact (le_div_iff₀ hτ_denom_pos).2 <| by
        simpa [s, τ, mul_assoc, mul_left_comm, mul_comm] using hs_mul
    calc
      (Mf : ℝ) * ‖x - xStar‖[f; x] = s := by rfl
      _ ≤ τ / (1 - τ) := hs_le
      _ = ω'_* τω := hωprime.symm

-- Proof sketch: apply the lower and upper self-concordant value bounds at the minimizer `xStar`.
-- The lower bound comes from Theorem 5.1.12, while the upper bound is the minimizer estimate from
-- Theorem 5.1.13 specialized to the Newton decrement at `x`.
/-- Theorem 5.2.1: if `xStar` minimizes a self-concordant function `f` on `dom` and the Newton
decrement at `x` is smaller than `1 / M_f`, then the scaled suboptimality
`M_f^2 (f x - f xStar)` lies between `ω(M_f λ_f(x))` and `ω_*(M_f λ_f(x))`. This is the textbook
inequality `(5.2.3)`. -/
theorem selfConcordant_suboptimality_bounds_of_newtonDecrement_lt_inv
    {x : E} (xStar : dom) (hx : x ∈ dom) (hmin : IsMinOn f dom (xStar : E))
    (hlambda : λ[f; x | hx] < 1 / (Mf : ℝ)) :
    let tω := NewtonDecrement.omegaArgOfPosDefMem Mf f x hx
    let τω := NewtonDecrement.omegaStarArgOfPosDefMem Mf f x hx hlambda
    ω tω ≤ (Mf : ℝ) ^ (2 : ℕ) * (f x - f xStar) ∧
      (Mf : ℝ) ^ (2 : ℕ) * (f x - f xStar) ≤ ω_* τω := by
  dsimp
  have hMf_pos : 0 < (Mf : ℝ) :=
    mf_pos_of_newtonDecrement_lt_inv (Mf := Mf) (f := f) hx hlambda
  have hMf_ne : (Mf : ℝ) ≠ 0 := ne_of_gt hMf_pos
  have hMf_eq_zero : ¬ Mf = 0 := by
    intro hMf0
    exact hMf_ne (by exact_mod_cast hMf0)
  have hgrad0 : ∇ f (xStar : E) = 0 :=
    gradient_eq_zero_at_selfconcordant_minimizer
      (dom := dom) (f := f) (inferInstance : IsSelfConcordantOnWith dom Mf f).isOpen_domain
      xStar hmin
  constructor
  · -- Collapse the Taylor model at the minimizer and identify the dual local norm with `λ_f(x)`.
    have hlower_raw :=
      (selfConcordant_value_bounds_of_dualLocalNorm_gradient_sub
        (Mf := Mf) (f := f) (x := (xStar : E)) (y := x) xStar.2 hx).1
    have hlower :
        f x ≥
          f xStar +
            (1 / (Mf : ℝ) ^ (2 : ℕ)) *
              ω (NewtonDecrement.omegaArgOfPosDefMem Mf f x hx) := by
      simpa [firstOrderTaylorModelAt_apply, hgrad0, hMf_eq_zero,
        NewtonDecrement.omegaArgOfPosDefMem] using hlower_raw
    have hgap :
        (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω (NewtonDecrement.omegaArgOfPosDefMem Mf f x hx) ≤
          f x - f xStar := by
      linarith
    have hmul :=
      mul_le_mul_of_nonneg_left hgap (show 0 ≤ (Mf : ℝ) ^ (2 : ℕ) by positivity)
    simpa [div_eq_mul_inv, mul_assoc, hMf_ne, inv_mul_cancel₀, mul_comm, mul_left_comm] using hmul
  · -- Transfer the theorem-5.1.13 `ω_*` bound from its chosen minimizer to `xStar`.
    have hupper :=
      suboptimality_upper_bound_at_minimizer_of_newtonDecrement_lt_inv
        (Mf := Mf) (f := f) xStar hx hmin hlambda
    have hmul :=
      mul_le_mul_of_nonneg_left hupper (show 0 ≤ (Mf : ℝ) ^ (2 : ℕ) by positivity)
    simpa [div_eq_mul_inv, mul_assoc, hMf_ne, inv_mul_cancel₀, mul_comm, mul_left_comm] using hmul

/-- Helper for Theorem 5.2.1: if a nonnegative scalar lies strictly below `ω'(t)`, then its
`ω_*` value is strictly below `ω(t)`. -/
lemma omegaStar_lt_omega_of_lt_omegaDeriv
    {tω : Set.Ioi (-1 : ℝ)} {τω : Set.Iio (1 : ℝ)}
    (htω_nonneg : 0 ≤ (tω : ℝ)) (hτω_nonneg : 0 ≤ (τω : ℝ))
    (hτω_lt : (τω : ℝ) < ω' tω) :
    ω_* τω < ω tω := by
  sorry

/-- Helper for Theorem 5.2.1: the lower half of `(5.2.4)` follows by contradiction from the
value sandwiches `(5.2.3)` and `(5.2.5)`. -/
lemma omega_prime_lower_from_minimizer_transport
    {x : E} (xStar : dom) (hx : x ∈ dom) (hmin : IsMinOn f dom (xStar : E))
    (hlambda : λ[f; x | hx] < 1 / (Mf : ℝ)) :
    let tω := NewtonDecrement.omegaArgOfPosDefMem Mf f x hx
    ω' tω ≤ (Mf : ℝ) * ‖x - xStar‖[f; x] := by
  sorry

-- Proof sketch: combine the gradient-pairing comparison from Theorem 5.1.8 with the Hessian
-- transport estimate from Corollary 5.1.5 to compare the minimizer distance
-- `‖x - xStar‖_x` to the Newton decrement `λ_f(x)`, then rewrite the resulting scalar bounds in
-- terms of `ω'` and `ω'_*`.
/-- The local minimizer distance `‖x - xStar‖_x` satisfies the textbook two-sided estimate
`(5.2.4)` in terms of the Newton decrement `λ_f(x)`. -/
theorem selfConcordant_minimizerDistance_bounds_of_newtonDecrement_lt_inv
    {x : E} (xStar : dom) (hx : x ∈ dom) (hmin : IsMinOn f dom (xStar : E))
    (hlambda : λ[f; x | hx] < 1 / (Mf : ℝ)) :
    let tω := NewtonDecrement.omegaArgOfPosDefMem Mf f x hx
    let τω := NewtonDecrement.omegaStarArgOfPosDefMem Mf f x hx hlambda
    ω' tω ≤ (Mf : ℝ) * ‖x - xStar‖[f; x] ∧
      (Mf : ℝ) * ‖x - xStar‖[f; x] ≤ ω'_* τω := by
  dsimp
  constructor
  · -- Project the Newton-decrement transport estimate from the dedicated minimizer-side helper.
    simpa using
      omega_prime_lower_from_minimizer_transport
        (Mf := Mf) (f := f) xStar hx hmin hlambda
  · -- The upper endpoint follows from the pairing lower bound plus the local Cauchy adapter.
    simpa using
      omega_prime_star_upper_from_pairing_lower
        (Mf := Mf) (f := f) xStar hx hmin hlambda

end NewtonDecrementBounds

-- Proof sketch: apply the lower and upper self-concordant value bounds with `y = xStar`, using
-- the local distance `r_*(x) = ‖x - xStar‖_x` as the step size. The admissibility hypothesis
-- `r_*(x) < 1 / M_f` supplies the upper `ω_*` estimate.
/-- If the local distance from `x` to a minimizer `xStar` is smaller than `1 / M_f`, then the
scaled suboptimality is bounded between `ω(M_f r_*(x))` and `ω_*(M_f r_*(x))`, which is the
textbook inequality `(5.2.5)`. -/
theorem selfConcordant_suboptimality_bounds_of_minimizerDistance_lt_inv
    {x : E} (xStar : dom) (hx : x ∈ dom) (hmin : IsMinOn f dom (xStar : E))
    (hr : ‖x - xStar‖[f; x] < 1 / (Mf : ℝ)) :
    let r := ‖x - xStar‖[f; x]
    let tω := selfConcordantOmegaArg Mf r (by
      exact neg_one_lt_mf_mul_of_nonneg (by
        simpa [r] using hessianLocalNorm_nonneg f x (x - xStar)))
    let τω := selfConcordantOmegaStarArg Mf r (mf_mul_lt_one_of_lt_inv hr)
    ω tω ≤ (Mf : ℝ) ^ (2 : ℕ) * (f x - f xStar) ∧
      (Mf : ℝ) ^ (2 : ℕ) * (f x - f xStar) ≤ ω_* τω := by
  dsimp
  constructor
  · -- The lower endpoint is the direct Dikin-local Taylor lower bound under `hr`.
    simpa using
      suboptimality_lower_bound_of_minimizerDistance_lt_inv
        (Mf := Mf) (f := f) xStar hx hmin hr
  · -- The upper endpoint is the direct Taylor upper bound with the nonpositive linear term
    -- discarded using convexity of `f` and optimality of `xStar`.
    simpa using
      suboptimality_upper_bound_of_minimizerDistance_lt_inv
        (Mf := Mf) (f := f) xStar hx hmin hr

end

end
