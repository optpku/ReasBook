/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Proposition_5_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Corollary_5_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_3_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient HessianLocalNorm DikinEllipsoidNotation

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 5.3.8 lies in the Chapter 5 self-concordant-barrier / local-distance domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantBarrierOnWith` in `Definition_5_3_2`, the chapter owner for
  `ν`-self-concordant barriers;
* `_root_.barrier_parameter_bound_iff_gradient_inner_sq_le` in `Proposition_5_3_3`, the
  canonical pointwise bridge from the barrier parameter inequality to the local
  gradient/local-norm estimate;
* `IsSelfConcordantOnWith.displacement_localNorm_upper_bound` in `Theorem_5_1_5`, the canonical
  Dikin-radius local-norm transport estimate;
* `gradient_difference_inner_ge_hessianLocalNorm_sq_div` in `Theorem_5_1_8`, the canonical
  lower bound for the gradient increment paired with the chord.

Best owner abstraction:
* source-facing: the textbook bound on the local norm of the chord `y - x`;
* core/canonical: `IsSelfConcordantBarrierOnWith dom ν F` together with `‖y - x‖[F; x]`;
* bridge/view: the owner-level barrier-parameter square estimate at `x`, followed by the standard
  self-concordant local-norm comparison along the segment from `x` to `y`.

Primitive data:
* the barrier owner witness `hF : IsSelfConcordantBarrierOnWith dom ν F`;
* points `x, y ∈ dom`;
* the source-facing nonnegativity hypothesis `0 ≤ ⟪∇ F(x), y - x⟫`.

Derived API:
* the local-distance bound `‖y - x‖[F; x] ≤ ν + 2 √ν`.

This theorem is an owner-level barrier estimate, so its public surface belongs in the barrier
namespace instead of as a parallel top-level theorem with the owner repeated in the binder list.
It uses only the Chapter 5 barrier/local-norm owner layer, so the ambient space assumption stays
at the canonical `[CompleteSpace E]` level rather than introducing a finite-dimensional bridge.
-/

-- Proof sketch: let `r := ‖y - x‖[F; x]`. If `r ≤ Real.sqrt ν`, the claim is immediate.
-- Otherwise choose an intermediate point `z = x + α • (y - x)` on the segment from `x` to `y`
-- with `α = Real.sqrt ν / r`, so the initial subsegment from `x` to `z` has `x`-local norm
-- exactly `√ν`. Since the barrier owner inherits an open convex standard-self-concordant domain,
-- both subsegments stay inside `dom`. Use the chapter's standard self-concordant segment
-- estimates on `x → z` to obtain a lower bound for the gradient increment, and combine that with
-- the barrier-parameter bound at `z` plus local-norm transport on `z → y` to control the
-- remaining pairing. The hypothesis `0 ≤ ⟪∇ F(x), y - x⟫` then lets one rearrange the resulting
-- scalar inequality to obtain `r ≤ ν + 2 * Real.sqrt ν`.
namespace IsSelfConcordantBarrierOnWith

section

variable {dom : Set E} {ν : NNReal} {F : E → ℝ}
variable {x y : E}

/-- Helper for Theorem 5.3.8: squaring the Chapter 5 local norm recovers the raw Hessian
quadratic form once that quadratic form is nonnegative. -/
private theorem sq_hessianLocalNorm_eq_inner_hessian
    {z d : E} (hquad : 0 ≤ inner ℝ d (hessian F z d)) :
    ‖d‖[F; z] ^ (2 : ℕ) = inner ℝ d (hessian F z d) := by
  -- The local norm is defined as the square root of the Hessian quadratic form.
  simpa [hessianLocalNorm_def] using Real.sq_sqrt hquad

/-- Helper for Theorem 5.3.8: affine lines have the expected derivative. -/
private theorem line_hasDerivAt {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z d : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ z + s • d) d t := by
  -- Differentiate the scalar parameter and keep the direction fixed.
  simpa [one_smul] using ((hasDerivAt_id t).smul_const d).const_add z

/-- Helper for Theorem 5.3.8: the gradient is continuous on the barrier domain. -/
private theorem gradient_continuousOn
    (hF : IsSelfConcordantBarrierOnWith dom ν F) :
    ContinuousOn (∇ F) dom := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfd_cont : ContinuousOn (fderiv ℝ F) dom := by
    exact
      ((hF.toIsStandardSelfConcordantOn.contDiffOn.of_le
        (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).fderiv_of_isOpen
          hF.toIsStandardSelfConcordantOn.isOpen_domain
          (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).continuousOn
  simpa [gradient, D] using D.continuous.comp_continuousOn hfd_cont

/-- Helper for Theorem 5.3.8: the Hessian is continuous on the barrier domain. -/
private theorem hessian_continuousOn
    (hF : IsSelfConcordantBarrierOnWith dom ν F) :
    ContinuousOn (hessian F) dom := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hgrad_contDiff : ContDiffOn ℝ 1 (∇ F) dom := by
    have hfd : ContDiffOn ℝ 1 (fderiv ℝ F) dom :=
      (hF.toIsStandardSelfConcordantOn.contDiffOn.of_le
        (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).fderiv_of_isOpen
          hF.toIsStandardSelfConcordantOn.isOpen_domain
          (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)
    simpa [gradient, D] using D.contDiff.comp_contDiffOn hfd
  simpa [hessian] using
    (hgrad_contDiff.fderiv_of_isOpen hF.toIsStandardSelfConcordantOn.isOpen_domain
      (show (0 : WithTop ℕ∞) + 1 ≤ 1 by norm_num)).continuousOn

/-- Helper for Theorem 5.3.8: scalarizing the gradient along an affine line differentiates to the
corresponding Hessian pairing. -/
private theorem scalarized_gradient_line_hasDerivAt
    (hF : IsSelfConcordantBarrierOnWith dom ν F)
    {x d u : E} {t : ℝ} (hxt : x + t • d ∈ dom) :
    HasDerivAt (fun s : ℝ ↦ inner ℝ (∇ F (x + s • d)) u)
      (inner ℝ (hessian F (x + t • d) d) u) t := by
  -- Differentiate the gradient line restriction and then postcompose with the scalar functional
  -- `v ↦ ⟪v, u⟫`.
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfderiv : DifferentiableAt ℝ (fderiv ℝ F) (x + t • d) := by
    have hcont : ContDiffAt ℝ 1 (fderiv ℝ F) (x + t • d) :=
      (hF.toIsStandardSelfConcordantOn.contDiffOn.contDiffAt
        (hF.toIsStandardSelfConcordantOn.isOpen_domain.mem_nhds hxt)).fderiv_right
          (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 3)
    exact hcont.differentiableAt one_ne_zero
  have hgrad : DifferentiableAt ℝ (∇ F) (x + t • d) := by
    -- Rewrite the gradient through the Riesz map before differentiating it.
    simpa [gradient, D] using D.differentiableAt.comp (x + t • d) hfderiv
  have hgradLine :
      HasFDerivAt (fun s : ℝ ↦ ∇ F (x + s • d))
        ((hessian F (x + t • d)).comp (ContinuousLinearMap.toSpanSingleton ℝ d)) t := by
    -- Compose the gradient derivative with the affine-line derivative.
    simpa using (hgrad.hasFDerivAt.comp t (line_hasDerivAt x d t).hasFDerivAt)
  let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) u
  have hscalar :
      HasFDerivAt (fun s : ℝ ↦ φ (∇ F (x + s • d)))
        (φ.comp ((hessian F (x + t • d)).comp (ContinuousLinearMap.toSpanSingleton ℝ d))) t := by
    -- Postcompose with the scalar functional.
    simpa [φ] using (φ.hasFDerivAt.comp t hgradLine)
  simpa [φ, InnerProductSpace.toDual_apply_apply, real_inner_comm] using hscalar.hasDerivAt

/-- Helper for Theorem 5.3.8: scaling a direction by a nonnegative scalar scales its local norm.
-/
private theorem hessianLocalNorm_smul_nonneg_at_mem
    (hF : IsSelfConcordantBarrierOnWith dom ν F)
    {z d : E} (hz : z ∈ dom) {t : ℝ} (ht : 0 ≤ t) :
    ‖t • d‖[F; z] = t * ‖d‖[F; z] := by
  -- Expand the local norm, use Hessian nonnegativity at `z`, and simplify the square root of
  -- `t² * ⟪d, ∇²F(z)d⟫`.
  have hquad : 0 ≤ inner ℝ d (hessian F z d) :=
    hF.toIsStandardSelfConcordantOn.hessian_posSemidef hz d
  calc
    ‖t • d‖[F; z] = Real.sqrt ((t * t) * inner ℝ d (hessian F z d)) := by
      rw [hessianLocalNorm_def]
      congr 1
      simp [inner_smul_left, inner_smul_right, mul_assoc]
    _ = Real.sqrt (inner ℝ d (hessian F z d)) * Real.sqrt (t * t) := by
      rw [mul_comm, Real.sqrt_mul hquad]
    _ = t * ‖d‖[F; z] := by
      rw [show t * t = t ^ (2 : ℕ) by ring, Real.sqrt_sq_eq_abs, abs_of_nonneg ht,
        hessianLocalNorm_def]
      ring

/-- Helper for Theorem 5.3.8: every point on the chord from `x` to `y` stays in the convex
domain. -/
private theorem segment_point_mem
    (hF : IsSelfConcordantBarrierOnWith dom ν F)
    {x y : E} (hx : x ∈ dom) (hy : y ∈ dom)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    x + t • (y - x) ∈ dom := by
  -- Rewrite the segment point as the standard convex combination and use domain convexity.
  have hrewrite : x + t • (y - x) = (1 - t) • x + t • y := by
    rw [smul_sub]
    rw [show (1 - t : ℝ) • x = x - t • x by rw [sub_smul, one_smul]]
    abel
  have hconv := hF.toIsStandardSelfConcordantOn.convex_domain
  have h1t : 0 ≤ 1 - t := by linarith
  have hsum : (1 - t) + t = 1 := by ring
  rw [hrewrite]
  exact hconv hx hy h1t ht0 hsum

/-- Helper for Theorem 5.3.8: the rational lower bound `r² / (1 + t r)²` integrates to the
expected factor `α r² / (1 + α r)`. -/
private theorem integral_sq_div_eq_scaled_sq_div
    {r α : ℝ} (hα0 : 0 ≤ α) (hr0 : 0 ≤ r) :
    ∫ t in 0..α, r ^ (2 : ℕ) / (1 + t * r) ^ (2 : ℕ) =
      α * r ^ (2 : ℕ) / (1 + α * r) := by
  have hden : ∀ t ∈ Set.Icc (0 : ℝ) α, 0 < 1 + t * r := by
    intro t ht
    nlinarith [ht.1, hr0]
  have hnum : ContinuousOn (fun t : ℝ ↦ t * r ^ (2 : ℕ) / (1 + t * r))
      (Set.Icc (0 : ℝ) α) := by
    refine (continuousOn_id.mul continuousOn_const).div ?_ ?_
    · exact (show Continuous (fun t : ℝ ↦ 1 + t * r) by continuity).continuousOn
    · intro t ht
      exact (hden t ht).ne'
  have hint :
      IntervalIntegrable
        (fun t : ℝ ↦ r ^ (2 : ℕ) / (1 + t * r) ^ (2 : ℕ))
        MeasureTheory.volume 0 α := by
    have hcont :
        ContinuousOn
          (fun t : ℝ ↦ r ^ (2 : ℕ) / (1 + t * r) ^ (2 : ℕ))
          (Set.Icc (0 : ℝ) α) := by
      refine continuousOn_const.div ?_ ?_
      · exact (show Continuous (fun t : ℝ ↦ (1 + t * r) ^ (2 : ℕ)) by continuity).continuousOn
      · intro t ht
        exact pow_ne_zero 2 (hden t ht).ne'
    exact hcont.intervalIntegrable_of_Icc hα0
  have hderiv :
      ∀ t ∈ Set.Ioo (0 : ℝ) α,
        HasDerivAt
          (fun s : ℝ ↦ s * r ^ (2 : ℕ) / (1 + s * r))
          (r ^ (2 : ℕ) / (1 + t * r) ^ (2 : ℕ)) t := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) α := Set.mem_Icc_of_Ioo ht
    have hden_ne : 1 + t * r ≠ 0 := (hden t ht').ne'
    have hden_deriv :
        HasDerivAt (fun s : ℝ ↦ 1 + s * r) r t := by
      convert (hasDerivAt_const t (1 : ℝ)).add ((hasDerivAt_id t).mul_const r) using 1
      ring
    have hquot :=
      ((hasDerivAt_id t).mul_const (r ^ (2 : ℕ))).div hden_deriv hden_ne
    have hquot_slope :
        ((1 : ℝ) * r ^ (2 : ℕ) * (1 + t * r) - t * r ^ (2 : ℕ) * r) /
            (1 + t * r) ^ (2 : ℕ) =
          r ^ (2 : ℕ) / (1 + t * r) ^ (2 : ℕ) := by
      field_simp [hden_ne]
      ring
    have hquot' :
        HasDerivAt (fun s : ℝ ↦ (s * r ^ (2 : ℕ)) / (1 + s * r))
          (((1 : ℝ) * r ^ (2 : ℕ) * (1 + t * r) - t * r ^ (2 : ℕ) * r) /
            (1 + t * r) ^ (2 : ℕ)) t := by
      simpa using hquot
    exact hquot'.congr_deriv hquot_slope
  have hftc :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hα0 hnum hderiv hint
  calc
    ∫ t in 0..α, r ^ (2 : ℕ) / (1 + t * r) ^ (2 : ℕ)
        = α * r ^ (2 : ℕ) / (1 + α * r) - (0 * r ^ (2 : ℕ) / (1 + 0 * r)) := by
            simpa using hftc
    _ = α * r ^ (2 : ℕ) / (1 + α * r) := by ring

/-- Helper for Theorem 5.3.8: on a subsegment `z = x + α • (y - x)`, the gradient increment
paired with the full chord is bounded below by the textbook transport factor. -/
private theorem gradient_increment_inner_ge_scaled_localNorm_sq_div
    (hF : IsSelfConcordantBarrierOnWith dom ν F)
    {x y : E} (hx : x ∈ dom) (hy : y ∈ dom)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    let d := y - x
    let r := ‖d‖[F; x]
    inner ℝ (∇ F (x + α • d) - ∇ F x) d ≥
      α * r ^ (2 : ℕ) / (1 + α * r) := by
  let d : E := y - x
  let r : ℝ := ‖d‖[F; x]
  have hr0 : 0 ≤ r := by
    simpa [d, r] using hessianLocalNorm_nonneg F x d
  let g : ℝ → ℝ := fun t ↦ inner ℝ (∇ F (x + t • d)) d
  -- Route correction: integrate the scalar gradient line directly and feed the source transport
  -- estimate pointwise along the segment.
  have hg_cont : ContinuousOn g (Set.Icc (0 : ℝ) α) := by
    intro t ht
    have hz : x + t • d ∈ dom := segment_point_mem (hF := hF) hx hy ht.1 (le_trans ht.2 hα1)
    have hderiv_t : HasDerivAt g (inner ℝ d (hessian F (x + t • d) d)) t := by
      simpa [g, real_inner_comm] using
        scalarized_gradient_line_hasDerivAt (hF := hF) (x := x) (d := d) (u := d) hz
    exact hderiv_t.continuousAt.continuousWithinAt
  have hderiv :
      ∀ t ∈ Set.Ioo (0 : ℝ) α,
        HasDerivAt g (inner ℝ d (hessian F (x + t • d) d)) t := by
    intro t ht
    have hz : x + t • d ∈ dom := segment_point_mem (hF := hF) hx hy (le_of_lt ht.1)
      (le_trans (le_of_lt ht.2) hα1)
    simpa [g, real_inner_comm] using
      scalarized_gradient_line_hasDerivAt (hF := hF) (x := x) (d := d) (u := d) hz
  have hderiv_int :
      IntervalIntegrable
        (fun t : ℝ ↦ inner ℝ d (hessian F (x + t • d) d))
        MeasureTheory.volume 0 α := by
    have hcont :
        ContinuousOn
          (fun t : ℝ ↦ inner ℝ d (hessian F (x + t • d) d))
          (Set.Icc (0 : ℝ) α) := by
      intro t ht
      have hz : x + t • d ∈ dom := segment_point_mem (hF := hF) hx hy ht.1
        (le_trans ht.2 hα1)
      have hsmul_cont : ContinuousAt (fun s : ℝ ↦ s • d) t := by
        simpa [one_smul] using ((hasDerivAt_id t).smul_const d).continuousAt
      have hline_cont : ContinuousAt (fun s : ℝ ↦ x + s • d) t := by
        exact ContinuousAt.comp (continuousAt_const.add continuousAt_id) hsmul_cont
      have hhess_cont : ContinuousAt (hessian F) (x + t • d) :=
        (hessian_continuousOn (hF := hF)).continuousAt
          (hF.toIsStandardSelfConcordantOn.isOpen_domain.mem_nhds hz)
      have hhess_line : ContinuousAt (fun s : ℝ ↦ hessian F (x + s • d)) t := by
        refine ContinuousAt.comp hhess_cont ?_
        exact ContinuousAt.comp (continuousAt_const.add continuousAt_id) hsmul_cont
      let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) d
      have happly_line : ContinuousAt (fun s : ℝ ↦ hessian F (x + s • d) d) t := by
        simpa using
          ContinuousAt.comp ((ContinuousLinearMap.apply ℝ E d).continuous.continuousAt) hhess_line
      have hinner_cont :
          ContinuousAt (fun s : ℝ ↦ inner ℝ d (hessian F (x + s • d) d)) t := by
        simpa [φ, InnerProductSpace.toDual_apply_apply, real_inner_comm] using
          ContinuousAt.comp φ.continuous.continuousAt happly_line
      exact hinner_cont.continuousWithinAt
    exact hcont.intervalIntegrable_of_Icc hα0
  have hint_lower :
      IntervalIntegrable
        (fun t : ℝ ↦ r ^ (2 : ℕ) / (1 + t * r) ^ (2 : ℕ))
        MeasureTheory.volume 0 α := by
    have hcont :
        ContinuousOn
          (fun t : ℝ ↦ r ^ (2 : ℕ) / (1 + t * r) ^ (2 : ℕ))
          (Set.Icc (0 : ℝ) α) := by
      refine continuousOn_const.div ?_ ?_
      · exact (show Continuous (fun t : ℝ ↦ (1 + t * r) ^ (2 : ℕ)) by continuity).continuousOn
      · intro t ht
        have : 0 < 1 + t * r := by nlinarith [ht.1, hr0]
        exact pow_ne_zero 2 this.ne'
    exact hcont.intervalIntegrable_of_Icc hα0
  have hpoint :
      ∀ t ∈ Set.Icc (0 : ℝ) α,
        r ^ (2 : ℕ) / (1 + t * r) ^ (2 : ℕ) ≤
          inner ℝ d (hessian F (x + t • d) d) := by
    intro t ht
    have ht1 : t ≤ 1 := le_trans ht.2 hα1
    have hz : x + t • d ∈ dom := segment_point_mem (hF := hF) hx hy ht.1 ht1
    have hquadz : 0 ≤ inner ℝ d (hessian F (x + t • d) d) :=
      hF.toIsStandardSelfConcordantOn.hessian_posSemidef hz d
    have hsub : (x + t • d) - x = t • d := by
      abel
    have hdisp :
        ‖(x + t • d) - x‖[F; x + t • d] ≥
          ‖(x + t • d) - x‖[F; x] / (1 + ‖(x + t • d) - x‖[F; x]) :=
      by
        have hstd : IsSelfConcordantOnWith dom (((1 : NNRealˣ) : NNReal)) F :=
          hF.toIsStandardSelfConcordantOn
        simpa [one_mul] using
          (hstd.displacement_localNorm_lower_bound
            (Mf := (1 : NNRealˣ)) hx hz)
    rw [hsub, hessianLocalNorm_smul_nonneg_at_mem (hF := hF) hz ht.1,
      hessianLocalNorm_smul_nonneg_at_mem (hF := hF) hx ht.1] at hdisp
    have hden_pos : 0 < 1 + t * r := by
      nlinarith [ht.1, hr0]
    have hdir : r / (1 + t * r) ≤ ‖d‖[F; x + t • d] := by
      by_cases ht_zero : t = 0
      · subst ht_zero
        simp [r]
      · have ht_pos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht_zero)
        have hdisp' : t * (r / (1 + t * r)) ≤ t * ‖d‖[F; x + t • d] := by
          simpa [r, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdisp
        exact le_of_mul_le_mul_left hdisp' ht_pos
    have hsq_norm :
        (r / (1 + t * r)) ^ (2 : ℕ) ≤ ‖d‖[F; x + t • d] ^ (2 : ℕ) := by
      have hdir_nonneg : 0 ≤ r / (1 + t * r) := by positivity
      have hnorm_nonneg : 0 ≤ ‖d‖[F; x + t • d] :=
        hessianLocalNorm_nonneg F (x + t • d) d
      nlinarith [hdir, hdir_nonneg, hnorm_nonneg]
    have hfrac :
        (r / (1 + t * r)) ^ (2 : ℕ) =
          r ^ (2 : ℕ) / (1 + t * r) ^ (2 : ℕ) := by
      field_simp [hden_pos.ne']
    calc
      r ^ (2 : ℕ) / (1 + t * r) ^ (2 : ℕ) = (r / (1 + t * r)) ^ (2 : ℕ) := by
        exact hfrac.symm
      _ ≤ ‖d‖[F; x + t • d] ^ (2 : ℕ) := hsq_norm
      _ = inner ℝ d (hessian F (x + t • d) d) := sq_hessianLocalNorm_eq_inner_hessian hquadz
  have hmono :
      ∫ t in 0..α, r ^ (2 : ℕ) / (1 + t * r) ^ (2 : ℕ) ≤
        ∫ t in 0..α, inner ℝ d (hessian F (x + t • d) d) := by
    exact intervalIntegral.integral_mono_on hα0 hint_lower hderiv_int hpoint
  have hftc :
      ∫ t in 0..α, inner ℝ d (hessian F (x + t • d) d) = g α - g 0 := by
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hα0 hg_cont hderiv hderiv_int
  have hcalc :
      α * r ^ (2 : ℕ) / (1 + α * r) ≤ g α - g 0 := by
    calc
      α * r ^ (2 : ℕ) / (1 + α * r)
          = ∫ t in 0..α, r ^ (2 : ℕ) / (1 + t * r) ^ (2 : ℕ) := by
              symm
              exact integral_sq_div_eq_scaled_sq_div hα0 hr0
      _ ≤ ∫ t in 0..α, inner ℝ d (hessian F (x + t • d) d) := hmono
      _ = g α - g 0 := hftc
  simpa [g, d, r, inner_sub_left] using hcalc

/-- Helper for Theorem 5.3.8: when the barrier parameter is zero, the gradient-inner hypothesis
forces the local chord length to vanish. -/
private theorem zero_barrierParameter_forces_zero_localNorm_of_gradient_inner_nonneg
    (hF : IsSelfConcordantBarrierOnWith dom ν F) (hν : ν = 0)
    {x y : E} (hx : x ∈ dom) (hy : y ∈ dom)
    (_hxy_nonneg : inner ℝ (∇ F x) (y - x) ≥ 0) :
    ‖y - x‖[F; x] = 0 := by
  let d : E := y - x
  let r : ℝ := ‖d‖[F; x]
  let β : ℝ := 1 / (2 * (1 + r))
  let z : E := x + β • d
  have hr : 0 ≤ r := by
    simpa [d, r] using hessianLocalNorm_nonneg F x d
  have hβ_pos : 0 < β := by
    -- The auxiliary segment parameter is chosen strictly inside `(0, 1)`.
    dsimp [β]
    positivity
  have hβ_nonneg : 0 ≤ β := le_of_lt hβ_pos
  have hβ_le_one : β ≤ 1 := by
    dsimp [β]
    have hden_ge_one : 1 ≤ 2 * (1 + r) := by nlinarith
    simpa using one_div_le_one_div_of_le zero_lt_one hden_ge_one
  have hz : z ∈ dom := segment_point_mem (hF := hF) hx hy hβ_nonneg hβ_le_one
  have hPosx : (hessian F x).IsPositive :=
    hF.toIsStandardSelfConcordantOn.hessian_isPositive hx
  have hPosz : (hessian F z).IsPositive :=
    hF.toIsStandardSelfConcordantOn.hessian_isPositive hz
  have hsq_x :
      ∀ u : E,
        (inner ℝ (∇ F x) u) ^ (2 : ℕ) ≤ (ν : ℝ) * ‖u‖[F; x] ^ (2 : ℕ) :=
    ((_root_.barrier_parameter_bound_iff_gradient_inner_sq_le hPosx).mp
      (fun u ↦ hF.barrier_parameter_bound hx u))
  have hsq_z :
      ∀ u : E,
        (inner ℝ (∇ F z) u) ^ (2 : ℕ) ≤ (ν : ℝ) * ‖u‖[F; z] ^ (2 : ℕ) :=
    ((_root_.barrier_parameter_bound_iff_gradient_inner_sq_le hPosz).mp
      (fun u ↦ hF.barrier_parameter_bound hz u))
  have hgrad_zero_x : ∀ u : E, inner ℝ (∇ F x) u = 0 := by
    intro u
    have hu : (inner ℝ (∇ F x) u) ^ (2 : ℕ) ≤ 0 := by
      simpa [hν] using hsq_x u
    nlinarith [sq_nonneg (inner ℝ (∇ F x) u)]
  have hgrad_zero_z : ∀ u : E, inner ℝ (∇ F z) u = 0 := by
    intro u
    have hu : (inner ℝ (∇ F z) u) ^ (2 : ℕ) ≤ 0 := by
      simpa [hν] using hsq_z u
    nlinarith [sq_nonneg (inner ℝ (∇ F z) u)]
  have hβr_lt_one : β * r < 1 := by
    -- The chosen step has local radius strictly below the unit Dikin threshold.
    dsimp [β]
    rw [one_div_mul_eq_div]
    have hden_pos : 0 < 2 * (1 + r) := by nlinarith
    rw [div_lt_iff₀ hden_pos]
    nlinarith
  have hz_sub : z - x = β • d := by
    dsimp [z]
    abel
  have hz_dikin : z ∈ W⁰[F; x](1 / (1 : ℝ)) := by
    -- Rewrite the displacement norm of `z - x` using homogeneity at the base point `x`.
    rw [mem_openDikinEllipsoid_iff, hz_sub,
      hessianLocalNorm_smul_nonneg_at_mem (hF := hF) hx hβ_nonneg]
    simpa [d, r]
      using hβr_lt_one
  have hstep :
      inner ℝ (∇ F z - ∇ F x) (z - x) ≥
        ‖z - x‖[F; x] ^ (2 : ℕ) / (1 + ‖z - x‖[F; x]) := by
    have hinc :
        inner ℝ (∇ F z - ∇ F x) d ≥
          β * r ^ (2 : ℕ) / (1 + β * r) := by
      simpa [d, r, z] using
        gradient_increment_inner_ge_scaled_localNorm_sq_div
          (hF := hF) hx hy hβ_nonneg hβ_le_one
    have hstep' : β * (β * r ^ (2 : ℕ) / (1 + β * r)) ≤ β * inner ℝ (∇ F z - ∇ F x) d := by
      exact mul_le_mul_of_nonneg_left hinc hβ_nonneg
    rw [hz_sub, hessianLocalNorm_smul_nonneg_at_mem (hF := hF) hx hβ_nonneg, inner_smul_right]
    calc
      (β * r) ^ (2 : ℕ) / (1 + β * r) = β * (β * r ^ (2 : ℕ) / (1 + β * r)) := by
        field_simp [show 1 + β * r ≠ 0 by nlinarith]
      _ ≤ β * inner ℝ (∇ F z - ∇ F x) d := hstep'
  have hpair_zero : inner ℝ (∇ F z - ∇ F x) (z - x) = 0 := by
    -- Both endpoint gradients vanish when the barrier parameter is zero.
    simp [hz_sub, inner_sub_left, hgrad_zero_x (β • d), hgrad_zero_z (β • d)]
  rw [hpair_zero, hz_sub,
    hessianLocalNorm_smul_nonneg_at_mem (hF := hF) hx hβ_nonneg] at hstep
  have hstep' : (β * r) ^ (2 : ℕ) / (1 + β * r) ≤ 0 := by
    linarith
  have hden_pos : 0 < 1 + β * r := by
    nlinarith
  have hnum_nonpos : (β * r) ^ (2 : ℕ) ≤ 0 := by
    rw [div_le_iff₀ hden_pos] at hstep'
    nlinarith
  have hβr_zero : β * r = 0 := by
    nlinarith [sq_nonneg (β * r), hnum_nonpos]
  have hr_zero : r = 0 := by
    nlinarith [hβ_pos, hβr_zero]
  simpa [d, r] using hr_zero

/-- Helper for Theorem 5.3.8: at an interior point `z`, the remaining chord pairing against the
gradient is strictly below the barrier parameter. -/
private theorem segment_gradient_pairing_lt_barrier_parameter
    (hF : IsSelfConcordantBarrierOnWith dom ν F) (hν : ν ≠ 0)
    {z y : E} (hz : z ∈ dom) (hy : y ∈ dom) :
    inner ℝ (∇ F z) (y - z) < (ν : ℝ) := by
  have hνpos : 0 < (ν : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr hν)
  have htangent :
      let t := 1 - (1 / (ν : ℝ)) * inner ℝ (∇ F z) (y - z)
      0 < t ∧ F y ≥ F z - (ν : ℝ) * Real.log t :=
    (isSelfConcordantBarrierOnWith_iff_logarithmic_taylor_lower_bound
      hF.toIsStandardSelfConcordantOn hνpos).1 hF hz hy
  -- The logarithmic theorem records positivity of the tangent factor, which is exactly the
  -- strict pairing bound needed here.
  dsimp at htangent
  have hscaled : inner ℝ (∇ F z) (y - z) / (ν : ℝ) < 1 := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using htangent.1
  rw [div_lt_iff₀ hνpos] at hscaled
  simpa using hscaled

/-- Theorem 5.3.8: if `F` is a `ν`-self-concordant barrier on `dom` and the gradient pairing
`⟪∇ F(x), y - x⟫` is nonnegative, then the local norm of the chord `y - x` at `x` is bounded by
`ν + 2 √ν`. -/
theorem hessianLocalNorm_sub_le_barrierParameter_add_two_sqrt_of_gradient_inner_nonneg
    (hF : IsSelfConcordantBarrierOnWith dom ν F)
    (hx : x ∈ dom) (hy : y ∈ dom)
    (hxy_nonneg : inner ℝ (∇ F x) (y - x) ≥ 0) :
    ‖y - x‖[F; x] ≤ (ν : ℝ) + 2 * Real.sqrt (ν : ℝ) := by
  let d : E := y - x
  let r : ℝ := ‖d‖[F; x]
  have hr : 0 ≤ r := by
    simpa [d, r] using hessianLocalNorm_nonneg F x d
  by_cases hν : ν = 0
  · -- The zero-parameter case reduces to vanishing local length.
    have hr_zero :
        ‖y - x‖[F; x] = 0 :=
      zero_barrierParameter_forces_zero_localNorm_of_gradient_inner_nonneg
        (hF := hF) hν hx hy hxy_nonneg
    rw [hr_zero]
    simp [hν]
  · have hνpos : 0 < (ν : ℝ) := by
      exact_mod_cast (pos_iff_ne_zero.mpr hν)
    by_cases hr_small : r ≤ Real.sqrt (ν : ℝ)
    · -- If the initial local norm is already below `√ν`, the target bound is immediate.
      simpa [r] using le_trans hr_small (by nlinarith [Real.sqrt_nonneg (ν : ℝ)])
    · have hsqrt_pos : 0 < Real.sqrt (ν : ℝ) := Real.sqrt_pos.mpr hνpos
      have hsqrt_lt_r : Real.sqrt (ν : ℝ) < r := lt_of_not_ge hr_small
      have hr_pos : 0 < r := lt_trans hsqrt_pos hsqrt_lt_r
      let α : ℝ := Real.sqrt (ν : ℝ) / r
      let z : E := x + α • d
      have hα0 : 0 ≤ α := by
        dsimp [α]
        positivity
      have hα1 : α ≤ 1 := by
        -- The chosen interpolation parameter is at most one because `√ν < r`.
        dsimp [α]
        rw [div_le_iff₀ hr_pos]
        simpa using le_of_lt hsqrt_lt_r
      have hz : z ∈ dom := by
        exact segment_point_mem (hF := hF) hx hy hα0 hα1
      have hz_pair_lt : inner ℝ (∇ F z) (y - z) < (ν : ℝ) := by
        exact segment_gradient_pairing_lt_barrier_parameter (hF := hF) hν hz hy
      have hinc :
          inner ℝ (∇ F z - ∇ F x) d ≥
            α * r ^ (2 : ℕ) / (1 + α * r) := by
        simpa [d, r, z] using
          gradient_increment_inner_ge_scaled_localNorm_sq_div
            (hF := hF) hx hy hα0 hα1
      have hy_sub : y - z = (1 - α) • d := by
        -- Rewrite the remaining chord in the collinear parameterization.
        calc
          y - z = y - x - α • (y - x) := by
            dsimp [z, d]
            abel
          _ = (1 - α) • (y - x) := by
            rw [sub_smul, one_smul]
      have h1α_nonneg : 0 ≤ 1 - α := by
        linarith
      have hpair_lower :
          (1 - α) * (α * r ^ (2 : ℕ) / (1 + α * r)) ≤
            inner ℝ (∇ F z) (y - z) := by
        have hsplit :
            inner ℝ (∇ F z) d =
              inner ℝ (∇ F x) d + inner ℝ (∇ F z - ∇ F x) d := by
          calc
            inner ℝ (∇ F z) d = inner ℝ ((∇ F x) + (∇ F z - ∇ F x)) d := by
              congr 1
              abel_nf
            _ = inner ℝ (∇ F x) d + inner ℝ (∇ F z - ∇ F x) d := by
              rw [inner_add_left]
        have hsum :
            α * r ^ (2 : ℕ) / (1 + α * r) ≤ inner ℝ (∇ F z) d := by
          rw [hsplit]
          linarith
        rw [hy_sub, inner_smul_right]
        exact mul_le_mul_of_nonneg_left hsum h1α_nonneg
      have hαr : α * r = Real.sqrt (ν : ℝ) := by
        dsimp [α]
        field_simp [hr_pos.ne']
      have hpair_lower' :
          Real.sqrt (ν : ℝ) * (r - Real.sqrt (ν : ℝ)) / (1 + Real.sqrt (ν : ℝ)) ≤
            inner ℝ (∇ F z) (y - z) := by
        have hrewrite :
            (1 - α) * (α * r ^ (2 : ℕ) / (1 + α * r)) =
              Real.sqrt (ν : ℝ) * (r - Real.sqrt (ν : ℝ)) / (1 + Real.sqrt (ν : ℝ)) := by
          rw [hαr]
          have haux : α * r ^ (2 : ℕ) - α ^ (2 : ℕ) * r ^ (2 : ℕ) =
              r * Real.sqrt (ν : ℝ) - (Real.sqrt (ν : ℝ)) ^ (2 : ℕ) := by
            nlinarith [hαr]
          field_simp [hr_pos.ne']
          nlinarith [haux]
        simpa [hrewrite] using hpair_lower
      have hineq :
          Real.sqrt (ν : ℝ) * (r - Real.sqrt (ν : ℝ)) / (1 + Real.sqrt (ν : ℝ)) <
            (ν : ℝ) := by
        exact lt_of_le_of_lt hpair_lower' hz_pair_lt
      have hmul_lt :
          Real.sqrt (ν : ℝ) * (r - Real.sqrt (ν : ℝ)) <
            (ν : ℝ) * (1 + Real.sqrt (ν : ℝ)) := by
        have hineq' := hineq
        field_simp [show 1 + Real.sqrt (ν : ℝ) ≠ 0 by positivity] at hineq'
        simpa [mul_comm] using hineq'
      have hr_lt : r < (ν : ℝ) + 2 * Real.sqrt (ν : ℝ) := by
        have hsq : (Real.sqrt (ν : ℝ)) ^ (2 : ℕ) = (ν : ℝ) := by
          rw [Real.sq_sqrt]
          exact_mod_cast ν.2
        nlinarith [hmul_lt, hsq, hsqrt_pos]
      exact le_of_lt (by simpa [r] using hr_lt)

end

end IsSelfConcordantBarrierOnWith

end
