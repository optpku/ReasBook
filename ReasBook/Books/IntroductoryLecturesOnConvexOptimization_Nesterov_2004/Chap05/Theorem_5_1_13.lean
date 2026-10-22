/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_4_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_29
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_23
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_24
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Example_5_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.FenchelPrimalExtension
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Lemma_5_1_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_5

open scoped Gradient HessianLocalNorm NewtonDecrement SelfConcordantAuxiliaryFunction

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section

variable {dom : Set E} {Mf : NNReal} {f : E → ℝ}
variable [IsSelfConcordantOnWith dom Mf f] [HasPositiveDefiniteHessianOn dom f]

omit [IsSelfConcordantOnWith dom Mf f] in
/-- Helper for Theorem 5.1.13: the small-Newton-decrement hypothesis forces the
self-concordance parameter to be strictly positive. -/
lemma mf_pos_of_newtonDecrement_lt_inv {x : E} (hx : x ∈ dom)
    (hlambda : λ[f; x | hx] < 1 / (Mf : ℝ)) :
    0 < Mf := by
  -- The Newton decrement is nonnegative, so `Mf = 0` would force the impossible bound
  -- `λ[f; x | hx] < 0`.
  by_contra hMf
  have hMf_nonneg : 0 ≤ (Mf : ℝ) := by
    exact_mod_cast Mf.2
  have hMf_eq_zero : (Mf : ℝ) = 0 := le_antisymm (le_of_not_gt hMf) hMf_nonneg
  have hnonneg : 0 ≤ λ[f; x | hx] := NewtonDecrement.ofPosDefMem_nonneg f x hx
  have hlt0 : λ[f; x | hx] < 0 := by
    simpa [hMf_eq_zero] using hlambda
  linarith

omit [IsSelfConcordantOnWith dom Mf f] [HasPositiveDefiniteHessianOn dom f] in
/-- Helper for Theorem 5.1.13: every minimizer on the open self-concordant domain is
stationary. -/
lemma gradient_eq_zero_of_isMinOn (hself : IsSelfConcordantOnWith dom Mf f)
    (xStar : dom) (hmin : IsMinOn f dom (xStar : E)) :
    ∇ f (xStar : E) = 0 := by
  -- Convert the constrained minimizer into an ambient local minimizer using openness of `dom`.
  have hlocal : IsLocalMin f (xStar : E) :=
    hmin.isLocalMin (hself.isOpen_domain.mem_nhds xStar.2)
  exact isLocalMin_gradient_eq_zero hlocal

omit [IsSelfConcordantOnWith dom Mf f] [HasPositiveDefiniteHessianOn dom f] in
/-- Helper for Theorem 5.1.13: a feasible stationary point minimizes the convex objective on
`dom`. -/
lemma isMinOn_of_gradient_eq_zero (hself : IsSelfConcordantOnWith dom Mf f)
    {xStar : E} (hxStar : xStar ∈ dom)
    (hgrad : ∇ f xStar = 0) :
    IsMinOn f dom xStar := by
  have hdiff : DifferentiableAt ℝ f xStar := by
    -- The self-concordant regularity gives an ambient derivative at every domain point.
    exact (hself.contDiffOn.contDiffAt (hself.isOpen_domain.mem_nhds hxStar)).differentiableAt
      (by norm_num)
  -- Stationarity turns the convex first-order inequality into the minimizer property.
  exact
    (hself.convexOn.isMinOn_iff_gradient_variational_inequality hxStar hdiff).2 <| by
      intro z hz
      simp [hgrad]

omit [IsSelfConcordantOnWith dom Mf f] in
/-- Helper for Theorem 5.1.13: any two feasible minimizers coincide. -/
lemma eq_of_isMinOn_of_isMinOn
    (hself : IsSelfConcordantOnWith dom Mf f)
    (xStar yStar : dom)
    (hxMin : IsMinOn f dom (xStar : E))
    (hyMin : IsMinOn f dom (yStar : E)) :
    xStar = yStar := by
  -- Route correction: prove uniqueness by strict monotonicity of the gradient along the chord,
  -- not by trying to manufacture a global strong-convexity constant.
  have hxGrad : ∇ f (xStar : E) = 0 :=
    gradient_eq_zero_of_isMinOn hself xStar hxMin
  have hyGrad : ∇ f (yStar : E) = 0 :=
    gradient_eq_zero_of_isMinOn hself yStar hyMin
  by_cases hxy : (xStar : E) = (yStar : E)
  · exact Subtype.ext hxy
  · let d : E := (xStar : E) - (yStar : E)
    have hd_ne : d ≠ 0 := by
      exact sub_ne_zero.mpr hxy
    let φ := (InnerProductSpace.toDual ℝ E) d
    let g : E → ℝ := fun w ↦ φ (∇ f w)
    have hg_deriv :
        ∀ z ∈ dom, HasFDerivWithinAt g (φ.comp (hessian f z)) dom z := by
      intro z hz
      have hfderiv : DifferentiableAt ℝ (fderiv ℝ f) z := by
        exact
          ((hself.contDiffOn.of_le
            (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).fderiv_of_isOpen
              hself.isOpen_domain
              (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).differentiableOn
                (by simp) z hz |>.differentiableAt (hself.isOpen_domain.mem_nhds hz)
      have hgrad : DifferentiableAt ℝ (∇ f) z := by
        unfold gradient
        simpa using ((InnerProductSpace.toDual ℝ E).symm.differentiableAt.comp z hfderiv)
      have hscalar : HasFDerivAt g (φ.comp (hessian f z)) z := by
        simpa [g, φ, Function.comp] using (φ.hasFDerivAt.comp z hgrad.hasFDerivAt)
      exact hscalar.hasFDerivWithinAt
    rcases domain_mvt hg_deriv hself.convex_domain yStar.2 xStar.2 with ⟨z, hzseg, hzEq⟩
    have hz : z ∈ dom := hself.convex_domain.segment_subset yStar.2 xStar.2 hzseg
    have hzPos : 0 < inner ℝ d (hessian f z d) := by
      simpa [d, real_inner_comm] using
        (HasPositiveDefiniteHessianOn.posdef hz hd_ne)
    have hleft : g (xStar : E) - g (yStar : E) = 0 := by
      simp [g, φ, hxGrad, hyGrad]
    have hright :
        (φ.comp (hessian f z)) ((xStar : E) - (yStar : E)) =
          inner ℝ d (hessian f z d) := by
      calc
        (φ.comp (hessian f z)) ((xStar : E) - (yStar : E)) =
            φ ((hessian f z) ((xStar : E) - (yStar : E))) := by
              rfl
        _ = inner ℝ d (hessian f z d) := by
              change inner ℝ d ((hessian f z) ((xStar : E) - (yStar : E))) =
                inner ℝ d (hessian f z d)
              rw [show ((xStar : E) - (yStar : E)) = d by rfl]
    have hzero : inner ℝ d (hessian f z d) = 0 := by
      have hzero' : 0 = inner ℝ d (hessian f z d) := by
        simpa [hleft, hright, φ, InnerProductSpace.toDual_apply_apply] using hzEq
      exact hzero'.symm
    linarith

/-- Helper for Theorem 5.1.13: every feasible minimizer inherits the standard `ω_*`
suboptimality bound from the base point `x`. -/
private theorem sq_le_mul_of_quadratic_family
    {a b c : ℝ} (hb : 0 ≤ b)
    (hline : ∀ t : ℝ, 2 * t * a - t ^ (2 : ℕ) * b ≤ c) :
    a ^ (2 : ℕ) ≤ b * c := by
  -- Test the quadratic family at the critical point, with a separate degenerate-coefficient case.
  by_cases hb_zero : b = 0
  · by_cases ha_zero : a = 0
    · simp [ha_zero, hb_zero]
    · have ha_eq_zero : a = 0 := by
        by_contra ha_ne
        have htest := hline ((|c| + 1) / a)
        have hcontr : 2 * (|c| + 1) ≤ c := by
          have hrew : 2 * ((|c| + 1) / a) * a ≤ c := by
            simpa [hb_zero] using htest
          field_simp [ha_ne] at hrew
          linarith
        have habs : c ≤ |c| := le_abs_self c
        have hbad : |c| + 2 ≤ 0 := by
          nlinarith
        have hpos : 0 < |c| + 2 := by
          nlinarith [abs_nonneg c]
        exact (not_le_of_gt hpos) hbad
      exact (ha_zero ha_eq_zero).elim
  · have hb_pos : 0 < b := lt_of_le_of_ne hb (by simpa [eq_comm] using hb_zero)
    have htest := hline (a / b)
    have hrewrite :
        2 * (a / b) * a - (a / b) ^ (2 : ℕ) * b = a ^ (2 : ℕ) / b := by
      field_simp [hb_zero]
      ring
    have hquot : a ^ (2 : ℕ) / b ≤ c := by
      simpa [hrewrite] using htest
    simpa [mul_comm] using (div_le_iff₀ hb_pos).1 hquot

private theorem abs_toDual_apply_le_dualLocalNorm_mul_hessianLocalNorm_ofPosDefMem
    {x : E} (hx : x ∈ dom) (v z : E) :
    |inner ℝ v z| ≤
      HessianDualLocalNorm.ofPosDefMem f hx (InnerProductSpace.toDual ℝ E v) * ‖z‖[f; x] := by
  let H := hessian f x
  let w := H.inverse v
  have hPos : H.IsPositive := HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem hx
  have hInv : H.IsInvertible := hessian_isInvertible_of_det_ne_zero
    (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hx)
  have hHw : H w = v := by
    -- Unfold the inverse witness only once, then keep the rest of the proof in Hessian form.
    dsimp [w, H]
    exact hInv.self_apply_inverse v
  have hquad : 0 ≤ inner ℝ z (H z) := hPos.inner_nonneg_right z
  have hpair_nonneg : 0 ≤ inner ℝ v w := by
    -- Rewrite the inverse-Hessian pairing as the positive quadratic form of `w`.
    calc
      0 ≤ inner ℝ w (H w) := hPos.inner_nonneg_right w
      _ = inner ℝ v w := by rw [hHw, real_inner_comm]
  have hline :
      ∀ t : ℝ,
        2 * t * inner ℝ v z - t ^ (2 : ℕ) * inner ℝ z (H z) ≤ inner ℝ v w := by
    intro t
    have hnonneg : 0 ≤ inner ℝ (t • z - w) (H (t • z - w)) := hPos.inner_nonneg_right (t • z - w)
    have hcross :
        inner ℝ w (H z) = inner ℝ v z := by
      calc
        inner ℝ w (H z) = inner ℝ (H w) z := by
          simpa [real_inner_comm] using hPos.isSymmetric z w
        _ = inner ℝ v z := by rw [hHw]
    have hrewrite :
        inner ℝ (t • z - w) (H (t • z - w)) =
          t ^ (2 : ℕ) * inner ℝ z (H z) - 2 * t * inner ℝ v z + inner ℝ v w := by
      -- Expand the Hessian quadratic form and rewrite the mixed terms through `H w = v`.
      have hleft :
          inner ℝ (t • z) (H w) = t * inner ℝ v z := by
        rw [hHw, real_inner_comm, inner_smul_right]
      have hright :
          inner ℝ w (t • H z) = t * inner ℝ v z := by
        rw [inner_smul_right, hcross]
      have hdiag :
          inner ℝ w (H w) = inner ℝ v w := by
        rw [hHw, real_inner_comm]
      rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right]
      rw [ContinuousLinearMap.map_smul, inner_smul_left, inner_smul_right]
      rw [hleft, hright, hdiag]
      have hstar_t : (starRingEnd ℝ) t = t := by simp
      rw [hstar_t]
      ring_nf
    rw [hrewrite] at hnonneg
    nlinarith
  have hsq_raw :
      (inner ℝ v z) ^ (2 : ℕ) ≤ inner ℝ z (H z) * inner ℝ v w := by
    have hsq := sq_le_mul_of_quadratic_family hquad hline
    simpa [mul_comm] using hsq
  have hdual_sq :
      (HessianDualLocalNorm.ofPosDefMem f hx (InnerProductSpace.toDual ℝ E v)) ^ (2 : ℕ) =
        inner ℝ v w := by
    rw [HessianDualLocalNorm.ofPosDefMem_def]
    simpa [w, H, pow_two, real_inner_comm, InnerProductSpace.toDual_apply_apply] using
      Real.sq_sqrt hpair_nonneg
  have hlocal_sq : ‖z‖[f; x] ^ (2 : ℕ) = inner ℝ z (H z) := by
    -- The fixed-base local norm is the square root of the Hessian quadratic form.
    rw [hessianLocalNorm_def]
    simpa [H] using Real.sq_sqrt hquad
  have hsq_abs :
      |inner ℝ v z| ^ (2 : ℕ) ≤
        (HessianDualLocalNorm.ofPosDefMem f hx (InnerProductSpace.toDual ℝ E v) * ‖z‖[f; x]) ^
          (2 : ℕ) := by
    calc
      |inner ℝ v z| ^ (2 : ℕ) = (inner ℝ v z) ^ (2 : ℕ) := by rw [sq_abs]
      _ ≤ inner ℝ z (H z) * inner ℝ v w := hsq_raw
      _ =
          (HessianDualLocalNorm.ofPosDefMem f hx (InnerProductSpace.toDual ℝ E v)) ^ (2 : ℕ) *
            ‖z‖[f; x] ^ (2 : ℕ) := by rw [hdual_sq, hlocal_sq, mul_comm]
      _ =
          (HessianDualLocalNorm.ofPosDefMem f hx (InnerProductSpace.toDual ℝ E v) *
            ‖z‖[f; x]) ^ (2 : ℕ) := by
        ring
  have hdual_nonneg :
      0 ≤ HessianDualLocalNorm.ofPosDefMem f hx (InnerProductSpace.toDual ℝ E v) := by
    rw [HessianDualLocalNorm.ofPosDefMem_def]
    exact Real.sqrt_nonneg _
  exact le_of_sq_le_sq hsq_abs
    (mul_nonneg hdual_nonneg (hessianLocalNorm_nonneg f x z))

/-- Helper for Theorem 5.1.13: once the Hessian quadratic form is nonnegative, squaring the local
norm recovers it exactly. -/
private theorem sq_hessianLocalNorm_eq_inner_hessian
    {z d : E} (hquad : 0 ≤ inner ℝ d (hessian f z d)) :
    ‖d‖[f; z] ^ (2 : ℕ) = inner ℝ d (hessian f z d) := by
  -- Expand the local norm and use `sqrt(x)^2 = x` on the nonnegative quadratic form.
  simpa [hessianLocalNorm_def] using Real.sq_sqrt hquad

/-- Helper for Theorem 5.1.13: affine lines have the expected derivative. -/
private theorem line_hasDerivAt
    (z d : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ z + s • d) d t := by
  -- Differentiate the scalar parameter and keep the direction fixed.
  simpa [one_smul] using ((hasDerivAt_id t).smul_const d).const_add z

/-- Helper for Theorem 5.1.13: the Hessian is continuous on the self-concordant domain. -/
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

/-- Helper for Theorem 5.1.13: scalarizing the gradient along an affine line differentiates to the
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

/-- Helper for Theorem 5.1.13: differentiating `f` along an admissible affine line recovers the
gradient pairing with the line direction. -/
private theorem value_line_hasDerivAt_of_selfConcordant
    (hself : IsSelfConcordantOnWith dom Mf f)
    {z d : E} {t : ℝ} (hzt : z + t • d ∈ dom) :
    HasDerivAt (fun s : ℝ ↦ f (z + s • d)) (inner ℝ (∇ f (z + t • d)) d) t := by
  have hC1 : ContDiffAt ℝ 1 f (z + t • d) := by
    exact
      (hself.contDiffOn.of_le
        (by norm_num : (1 : WithTop ℕ∞) ≤ 3)).contDiffAt
          (hself.isOpen_domain.mem_nhds hzt)
  have hfdLine :
      HasDerivAt (fun s : ℝ ↦ f (z + s • d)) ((fderiv ℝ f (z + t • d)) d) t := by
    -- Differentiate `f` first, then compose the Fréchet derivative with the affine line.
    simpa using
      ((hC1.differentiableAt one_ne_zero).hasFDerivAt.comp t
        (line_hasDerivAt z d t).hasFDerivAt).hasDerivAt
  -- Differentiate the ambient function first and then compose with the affine line.
  simpa [gradient, InnerProductSpace.toDual_apply_apply] using hfdLine

/-- Helper for Theorem 5.1.13: nonnegative scalar dilations scale the local norm linearly at a
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

/-- Helper for Theorem 5.1.13: every point on the chord from `x` to `y` stays in the convex
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

/-- Helper for Theorem 5.1.13: the rational lower integrand integrates to the expected transport
factor. -/
private theorem integral_sq_div_eq_scaled_sq_div
    {r α : ℝ} (hα0 : 0 ≤ α) (hr0 : 0 ≤ r) :
    ∫ t in 0..α, r ^ (2 : ℕ) / (1 + t * (Mf : ℝ) * r) ^ (2 : ℕ) =
      α * r ^ (2 : ℕ) / (1 + α * (Mf : ℝ) * r) := by
  let a : ℝ := (Mf : ℝ) * r
  have hden : ∀ t ∈ Set.Icc (0 : ℝ) α, 0 < 1 + t * a := by
    intro t ht
    have hmul_nonneg : 0 ≤ t * a := by
      exact mul_nonneg ht.1 (mul_nonneg Mf.2 hr0)
    linarith
  have hnum :
      ContinuousOn (fun t : ℝ ↦ t * r ^ (2 : ℕ) / (1 + t * a))
        (Set.Icc (0 : ℝ) α) := by
    refine (continuousOn_id.mul continuousOn_const).div ?_ ?_
    · exact (show Continuous (fun t : ℝ ↦ 1 + t * a) by continuity).continuousOn
    · intro t ht
      exact (hden t ht).ne'
  have hint :
      IntervalIntegrable
        (fun t : ℝ ↦ r ^ (2 : ℕ) / (1 + t * a) ^ (2 : ℕ))
        MeasureTheory.volume 0 α := by
    have hcont :
        ContinuousOn
          (fun t : ℝ ↦ r ^ (2 : ℕ) / (1 + t * a) ^ (2 : ℕ))
          (Set.Icc (0 : ℝ) α) := by
      refine continuousOn_const.div ?_ ?_
      · exact (show Continuous (fun t : ℝ ↦ (1 + t * a) ^ (2 : ℕ)) by continuity).continuousOn
      · intro t ht
        exact pow_ne_zero 2 (hden t ht).ne'
    exact hcont.intervalIntegrable_of_Icc hα0
  have hderiv :
      ∀ t ∈ Set.Ioo (0 : ℝ) α,
        HasDerivAt
          (fun s : ℝ ↦ s * r ^ (2 : ℕ) / (1 + s * a))
          (r ^ (2 : ℕ) / (1 + t * a) ^ (2 : ℕ)) t := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) α := Set.mem_Icc_of_Ioo ht
    have hden_ne : 1 + t * a ≠ 0 := (hden t ht').ne'
    have hden_deriv :
        HasDerivAt (fun s : ℝ ↦ 1 + s * a) a t := by
      convert (hasDerivAt_const t (1 : ℝ)).add ((hasDerivAt_id t).mul_const a) using 1
      ring
    have hquot :=
      ((hasDerivAt_id t).mul_const (r ^ (2 : ℕ))).div hden_deriv hden_ne
    have hslope :
        ((1 : ℝ) * r ^ (2 : ℕ) * (1 + t * a) - t * r ^ (2 : ℕ) * a) /
            (1 + t * a) ^ (2 : ℕ) =
          r ^ (2 : ℕ) / (1 + t * a) ^ (2 : ℕ) := by
      field_simp [hden_ne]
      ring
    have hquot' :
        HasDerivAt
          (fun s : ℝ ↦ s * r ^ (2 : ℕ) / (1 + s * a))
          (((1 : ℝ) * r ^ (2 : ℕ) * (1 + t * a) - t * r ^ (2 : ℕ) * a) /
            (1 + t * a) ^ (2 : ℕ)) t := by
      simpa using hquot
    exact hquot'.congr_deriv hslope
  have hftc :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hα0 hnum hderiv hint
  calc
    ∫ t in 0..α, r ^ (2 : ℕ) / (1 + t * (Mf : ℝ) * r) ^ (2 : ℕ)
        = ∫ t in 0..α, r ^ (2 : ℕ) / (1 + t * a) ^ (2 : ℕ) := by
            congr with t
            simp [a, mul_assoc, mul_left_comm, mul_comm]
    _ = α * r ^ (2 : ℕ) / (1 + α * a) - (0 * r ^ (2 : ℕ) / (1 + 0 * a)) := by
          simpa using hftc
    _ = α * r ^ (2 : ℕ) / (1 + α * a) := by ring
    _ = α * r ^ (2 : ℕ) / (1 + α * (Mf : ℝ) * r) := by
          simp [a, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Theorem 5.1.13: along a self-concordant segment, the gradient increment paired with
the full chord is bounded below by the source transport factor. -/
private theorem segment_gradient_increment_lower_bound_at_base
    (hMf : Mf ≠ 0) {x y : E} (hx : x ∈ dom) (hy : y ∈ dom)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    let d := y - x
    let r := ‖d‖[f; x]
    inner ℝ (∇ f (x + α • d) - ∇ f x) d ≥
      α * r ^ (2 : ℕ) / (1 + α * (Mf : ℝ) * r) := by
  let hself : IsSelfConcordantOnWith dom Mf f := inferInstance
  let d : E := y - x
  let r : ℝ := ‖d‖[f; x]
  have hMf_pos_nn : 0 < Mf := lt_of_le_of_ne Mf.2 (Ne.symm hMf)
  have hr0 : 0 ≤ r := by
    simpa [d, r] using hessianLocalNorm_nonneg f x d
  let g : ℝ → ℝ := fun t ↦ inner ℝ (∇ f (x + t • d)) d
  -- Route correction: integrate the scalarized gradient line directly and feed the self-concordant
  -- transport estimate pointwise along the segment.
  have hg_cont : ContinuousOn g (Set.Icc (0 : ℝ) α) := by
    intro t ht
    have hz : x + t • d ∈ dom := segment_point_mem hself hx hy ht.1 (le_trans ht.2 hα1)
    have hderiv_t : HasDerivAt g (inner ℝ d (hessian f (x + t • d) d)) t := by
      simpa [g, real_inner_comm] using scalarized_gradient_line_hasDerivAt hself hz
    exact hderiv_t.continuousAt.continuousWithinAt
  have hderiv :
      ∀ t ∈ Set.Ioo (0 : ℝ) α,
        HasDerivAt g (inner ℝ d (hessian f (x + t • d) d)) t := by
    intro t ht
    have hz : x + t • d ∈ dom := segment_point_mem hself hx hy (le_of_lt ht.1)
      (le_trans (le_of_lt ht.2) hα1)
    simpa [g, real_inner_comm] using scalarized_gradient_line_hasDerivAt hself hz
  have hderiv_int :
      IntervalIntegrable
        (fun t : ℝ ↦ inner ℝ d (hessian f (x + t • d) d))
        MeasureTheory.volume 0 α := by
    have hcont :
        ContinuousOn
          (fun t : ℝ ↦ inner ℝ d (hessian f (x + t • d) d))
          (Set.Icc (0 : ℝ) α) := by
      intro t ht
      have hz : x + t • d ∈ dom := segment_point_mem hself hx hy ht.1 (le_trans ht.2 hα1)
      have hline_cont : ContinuousAt (fun s : ℝ ↦ x + s • d) t :=
        (line_hasDerivAt x d t).continuousAt
      have hhess_cont : ContinuousAt (hessian f) (x + t • d) :=
        (hessian_continuousOn (hself := hself)).continuousAt
          (hself.isOpen_domain.mem_nhds hz)
      have hhess_line : ContinuousAt (fun s : ℝ ↦ hessian f (x + s • d)) t := by
        exact ContinuousAt.comp hhess_cont hline_cont
      let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) d
      have happly_line : ContinuousAt (fun s : ℝ ↦ hessian f (x + s • d) d) t := by
        simpa using
          ContinuousAt.comp ((ContinuousLinearMap.apply ℝ E d).continuous.continuousAt) hhess_line
      have hinner_cont :
          ContinuousAt (fun s : ℝ ↦ inner ℝ d (hessian f (x + s • d) d)) t := by
        simpa [φ, InnerProductSpace.toDual_apply_apply, real_inner_comm] using
          ContinuousAt.comp φ.continuous.continuousAt happly_line
      exact hinner_cont.continuousWithinAt
    exact hcont.intervalIntegrable_of_Icc hα0
  have hint_lower :
      IntervalIntegrable
        (fun t : ℝ ↦ r ^ (2 : ℕ) / (1 + t * ((Mf : ℝ) * r)) ^ (2 : ℕ))
        MeasureTheory.volume 0 α := by
    have hcont :
        ContinuousOn
          (fun t : ℝ ↦ r ^ (2 : ℕ) / (1 + t * ((Mf : ℝ) * r)) ^ (2 : ℕ))
          (Set.Icc (0 : ℝ) α) := by
      refine continuousOn_const.div ?_ ?_
      · exact
          (show Continuous (fun t : ℝ ↦ (1 + t * ((Mf : ℝ) * r)) ^ (2 : ℕ)) by continuity).continuousOn
      · intro t ht
        have hmul_nonneg : 0 ≤ t * ((Mf : ℝ) * r) := by
          exact mul_nonneg ht.1 (mul_nonneg Mf.2 hr0)
        have : 0 < 1 + t * ((Mf : ℝ) * r) := by
          linarith
        exact pow_ne_zero 2 this.ne'
    exact hcont.intervalIntegrable_of_Icc hα0
  have hpoint :
      ∀ t ∈ Set.Icc (0 : ℝ) α,
        r ^ (2 : ℕ) / (1 + t * ((Mf : ℝ) * r)) ^ (2 : ℕ) ≤
          inner ℝ d (hessian f (x + t • d) d) := by
    intro t ht
    have ht1 : t ≤ 1 := le_trans ht.2 hα1
    have hz : x + t • d ∈ dom := segment_point_mem hself hx hy ht.1 ht1
    have hquadz : 0 ≤ inner ℝ d (hessian f (x + t • d) d) :=
      hself.hessian_posSemidef hz d
    have hsub : (x + t • d) - x = t • d := by
      abel
    have hdisp :
        ‖(x + t • d) - x‖[f; x + t • d] ≥
          ‖(x + t • d) - x‖[f; x] /
            (1 + (Mf : ℝ) * ‖(x + t • d) - x‖[f; x]) := by
      let MfUnit : NNRealˣ := Units.mk0 Mf (ne_of_gt hMf_pos_nn)
      have hselfUnit : IsSelfConcordantOnWith dom (MfUnit : NNReal) f := by
        simpa [MfUnit] using hself
      simpa [MfUnit] using hselfUnit.displacement_localNorm_lower_bound hx hz
    rw [hsub,
      hessianLocalNorm_smul_nonneg_at_mem (hself := hself) (hz := hz) ht.1,
      hessianLocalNorm_smul_nonneg_at_mem (hself := hself) (hz := hx) ht.1] at hdisp
    have hden_pos : 0 < 1 + t * ((Mf : ℝ) * r) := by
      have hmul_nonneg : 0 ≤ t * ((Mf : ℝ) * r) := by
        exact mul_nonneg ht.1 (mul_nonneg Mf.2 hr0)
      linarith
    have hdir : r / (1 + t * ((Mf : ℝ) * r)) ≤ ‖d‖[f; x + t • d] := by
      by_cases ht_zero : t = 0
      · subst ht_zero
        simp [r]
      · have ht_pos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht_zero)
        have hdisp' : t * (r / (1 + t * ((Mf : ℝ) * r))) ≤ t * ‖d‖[f; x + t • d] := by
          simpa [r, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdisp
        exact le_of_mul_le_mul_left hdisp' ht_pos
    have hsq_norm :
        (r / (1 + t * ((Mf : ℝ) * r))) ^ (2 : ℕ) ≤ ‖d‖[f; x + t • d] ^ (2 : ℕ) := by
      have hdir_nonneg : 0 ≤ r / (1 + t * ((Mf : ℝ) * r)) := by positivity
      have hnorm_nonneg : 0 ≤ ‖d‖[f; x + t • d] := hessianLocalNorm_nonneg f (x + t • d) d
      nlinarith [hdir, hdir_nonneg, hnorm_nonneg]
    have hfrac :
        (r / (1 + t * ((Mf : ℝ) * r))) ^ (2 : ℕ) =
          r ^ (2 : ℕ) / (1 + t * ((Mf : ℝ) * r)) ^ (2 : ℕ) := by
      field_simp [hden_pos.ne']
    calc
      r ^ (2 : ℕ) / (1 + t * ((Mf : ℝ) * r)) ^ (2 : ℕ) =
          (r / (1 + t * ((Mf : ℝ) * r))) ^ (2 : ℕ) := by
            exact hfrac.symm
      _ ≤ ‖d‖[f; x + t • d] ^ (2 : ℕ) := hsq_norm
      _ = inner ℝ d (hessian f (x + t • d) d) := sq_hessianLocalNorm_eq_inner_hessian hquadz
  have hmono :
      ∫ t in 0..α, r ^ (2 : ℕ) / (1 + t * ((Mf : ℝ) * r)) ^ (2 : ℕ) ≤
        ∫ t in 0..α, inner ℝ d (hessian f (x + t • d) d) := by
    exact intervalIntegral.integral_mono_on hα0 hint_lower hderiv_int hpoint
  have hftc :
      ∫ t in 0..α, inner ℝ d (hessian f (x + t • d) d) = g α - g 0 := by
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hα0 hg_cont hderiv hderiv_int
  have hcalc :
      α * r ^ (2 : ℕ) / (1 + α * ((Mf : ℝ) * r)) ≤ g α - g 0 := by
    calc
      α * r ^ (2 : ℕ) / (1 + α * ((Mf : ℝ) * r))
          = ∫ t in 0..α, r ^ (2 : ℕ) / (1 + t * ((Mf : ℝ) * r)) ^ (2 : ℕ) := by
              symm
              simpa [mul_assoc, mul_left_comm, mul_comm] using
                integral_sq_div_eq_scaled_sq_div (Mf := Mf) (r := r) (α := α) hα0 hr0
      _ ≤ ∫ t in 0..α, inner ℝ d (hessian f (x + t • d) d) := hmono
      _ = g α - g 0 := hftc
  -- Rewrite the gradient increment as the endpoint difference of the scalarized line.
  simpa [g, d, r, inner_sub_left, mul_assoc, mul_left_comm, mul_comm] using hcalc

/-- Helper for Theorem 5.1.13: integrating the scalar restriction of `f` along a segment recovers
the gradient pairing integral. -/
private theorem segment_scalar_integral_eq
    (hself : IsSelfConcordantOnWith dom Mf f)
    {x d : E} (hsegment : ∀ t ∈ Set.Icc (0 : ℝ) 1, x + t • d ∈ dom) :
    f (x + d) - f x = ∫ t in 0..1, inner ℝ (∇ f (x + t • d)) d := by
  let g : ℝ → ℝ := fun t ↦ f (x + t • d)
  have hg_cont : ContinuousOn g (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    exact
      (value_line_hasDerivAt_of_selfConcordant hself (hsegment t ht)).continuousAt.continuousWithinAt
  have hderiv :
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt g (inner ℝ (∇ f (x + t • d)) d) t := by
    intro t ht
    simpa [g] using
      value_line_hasDerivAt_of_selfConcordant hself (hsegment t (Set.mem_Icc_of_Ioo ht))
  have hgrad_int :
      IntervalIntegrable (fun t : ℝ ↦ inner ℝ (∇ f (x + t • d)) d) MeasureTheory.volume 0 1 := by
    have hcont :
        ContinuousOn (fun t : ℝ ↦ inner ℝ (∇ f (x + t • d)) d) (Set.Icc (0 : ℝ) 1) := by
      intro t ht
      exact
        (scalarized_gradient_line_hasDerivAt hself (hsegment t ht)).continuousAt.continuousWithinAt
    exact hcont.intervalIntegrable_of_Icc (by norm_num)
  have hftc :
      ∫ t in 0..1, inner ℝ (∇ f (x + t • d)) d = g 1 - g 0 := by
    simpa using
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
        (show (0 : ℝ) ≤ 1 by norm_num) hg_cont hderiv hgrad_int
  simpa [g] using hftc.symm

/-- Helper for Theorem 5.1.13: the second scalar integration in the source lower-bound argument
evaluates to the logarithmic `ω` term. -/
private theorem integral_mul_sq_div_eq_omega
    {r : ℝ} (hr0 : 0 ≤ r) (hMf_pos : 0 < (Mf : ℝ)) :
    let tω := selfConcordantOmegaArg Mf r (neg_one_lt_mf_mul_of_nonneg hr0)
    ∫ t in 0..1, t * r ^ (2 : ℕ) / (1 + t * (Mf : ℝ) * r) =
      (1 / ((Mf : ℝ) ^ (2 : ℕ))) * ω tω := by
  let a : ℝ := (Mf : ℝ)
  have ha_ne : a ≠ 0 := ne_of_gt (by simpa [a] using hMf_pos)
  have hnum :
      ContinuousOn
        (fun t : ℝ ↦ (1 / (a ^ (2 : ℕ))) * (a * t * r - Real.log (1 + a * t * r)))
        (Set.Icc (0 : ℝ) 1) := by
    have hlog :
        ContinuousOn (fun t : ℝ ↦ Real.log (1 + a * t * r)) (Set.Icc (0 : ℝ) 1) := by
      refine Real.continuousOn_log.comp ?_ ?_
      · exact (show Continuous (fun t : ℝ ↦ 1 + a * t * r) by continuity).continuousOn
      · intro t ht
        have harg_pos : 0 < 1 + a * t * r := by
          have ha_nonneg : 0 ≤ a := by
            simpa [a] using hMf_pos.le
          have hmul_nonneg : 0 ≤ a * t * r := by
            exact mul_nonneg (mul_nonneg ha_nonneg ht.1) hr0
          linarith
        exact harg_pos.ne'
    have hlin :
        ContinuousOn (fun t : ℝ ↦ a * t * r) (Set.Icc (0 : ℝ) 1) := by
      exact (show Continuous (fun t : ℝ ↦ a * t * r) by continuity).continuousOn
    -- Keep the antiderivative in the exact source-friendly scalar form.
    refine continuousOn_const.mul ?_
    exact hlin.sub hlog
  have hint :
      IntervalIntegrable
        (fun t : ℝ ↦ t * r ^ (2 : ℕ) / (1 + a * t * r))
        MeasureTheory.volume 0 1 := by
    have hcont :
        ContinuousOn
          (fun t : ℝ ↦ t * r ^ (2 : ℕ) / (1 + a * t * r))
          (Set.Icc (0 : ℝ) 1) := by
      refine (continuousOn_id.mul continuousOn_const).div ?_ ?_
      · exact (show Continuous (fun t : ℝ ↦ 1 + a * t * r) by continuity).continuousOn
      · intro t ht
        have harg_pos : 0 < 1 + a * t * r := by
          have ha_nonneg : 0 ≤ a := by simpa [a] using hMf_pos.le
          have hmul_nonneg : 0 ≤ a * t * r := by
            exact mul_nonneg (mul_nonneg ha_nonneg ht.1) hr0
          linarith
        exact harg_pos.ne'
    exact hcont.intervalIntegrable_of_Icc (by norm_num)
  have hderiv :
      ∀ t ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt
          (fun s : ℝ ↦ (1 / (a ^ (2 : ℕ))) * (a * s * r - Real.log (1 + a * s * r)))
          (t * r ^ (2 : ℕ) / (1 + a * t * r)) t := by
    intro t ht
    have harg_pos : 0 < 1 + a * t * r := by
      have ha_nonneg : 0 ≤ a := by
        simpa [a] using hMf_pos.le
      have hmul_nonneg : 0 ≤ a * t * r := by
        exact mul_nonneg (mul_nonneg ha_nonneg ht.1.le) hr0
      linarith
    have hlog :
        HasDerivAt (fun s : ℝ ↦ Real.log (1 + a * s * r))
          ((a * r) / (1 + a * t * r)) t := by
      have harg :
          HasDerivAt (fun s : ℝ ↦ 1 + a * s * r) (a * r) t := by
        convert
          (hasDerivAt_const t (1 : ℝ)).add ((((hasDerivAt_id t).const_mul a).mul_const r)) using 1
        ring
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (Real.hasDerivAt_log harg_pos.ne').comp t harg
    have hlin :
        HasDerivAt (fun s : ℝ ↦ a * s * r) (a * r) t := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        ((((hasDerivAt_id t).const_mul a).mul_const r))
    have hbase :
        HasDerivAt
          (fun s : ℝ ↦ a * s * r - Real.log (1 + a * s * r))
          ((a * r) - ((a * r) / (1 + a * t * r))) t := by
      exact hlin.sub hlog
    have hscaled :
        HasDerivAt
          (fun s : ℝ ↦ (1 / (a ^ (2 : ℕ))) * (a * s * r - Real.log (1 + a * s * r)))
          ((1 / (a ^ (2 : ℕ))) * ((a * r) - ((a * r) / (1 + a * t * r)))) t := by
      exact hbase.const_mul (1 / (a ^ (2 : ℕ)))
    have hslope :
        ((1 / (a ^ (2 : ℕ))) * ((a * r) - ((a * r) / (1 + a * t * r)))) =
          t * r ^ (2 : ℕ) / (1 + a * t * r) := by
      have hfrac :
          1 - (1 + a * t * r)⁻¹ = (a * t * r) * (1 + a * t * r)⁻¹ := by
        field_simp [ha_ne, harg_pos.ne']
        ring
      calc
        ((1 / (a ^ (2 : ℕ))) * ((a * r) - ((a * r) / (1 + a * t * r))))
            = (1 / (a ^ (2 : ℕ))) * (a * r) * (1 - (1 + a * t * r)⁻¹) := by
                ring_nf
        _ = (1 / (a ^ (2 : ℕ))) * (a * r) * ((a * t * r) * (1 + a * t * r)⁻¹) := by
              rw [hfrac]
        _ = t * r ^ (2 : ℕ) / (1 + a * t * r) := by
              field_simp [ha_ne, harg_pos.ne']
    exact hscaled.congr_deriv hslope
  have hftc :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (show (0 : ℝ) ≤ 1 by norm_num) hnum hderiv hint
  calc
    ∫ t in 0..1, t * r ^ (2 : ℕ) / (1 + t * (Mf : ℝ) * r)
        = ((1 / (a ^ (2 : ℕ))) * (a * 1 * r - Real.log (1 + a * 1 * r))) -
            ((1 / (a ^ (2 : ℕ))) * (a * 0 * r - Real.log (1 + a * 0 * r)) ) := by
            simpa [a, mul_assoc, mul_left_comm, mul_comm] using hftc
    _ = (1 / (a ^ (2 : ℕ))) * (a * r - Real.log (1 + a * r)) := by
      simp
    _ = (1 / ((Mf : ℝ) ^ (2 : ℕ))) *
          ω (selfConcordantOmegaArg Mf r (neg_one_lt_mf_mul_of_nonneg hr0)) := by
      rw [selfConcordantOmega_apply]
      simp [a, mul_comm]

/-- Helper for Theorem 5.1.13: the Taylor remainder from a base point `y` to `z` dominates the
canonical `ω` term built from the base local distance `‖z - y‖[f; y]`. -/
private theorem taylor_lower_bound_from_base_by_local_distance_nonzero
    (hself : IsSelfConcordantOnWith dom Mf f)
    {y z : E} (hMf : Mf ≠ 0) (hy : y ∈ dom) (hz : z ∈ dom) :
    let h := z - y
    let r := ‖h‖[f; y]
    let tω := selfConcordantOmegaArg Mf r
      (neg_one_lt_mf_mul_of_nonneg (hessianLocalNorm_nonneg f y h))
    f z ≥
      f y + inner ℝ (∇ f y) h + (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω tω := by
  let h : E := z - y
  let r : ℝ := ‖h‖[f; y]
  let tω : Set.Ioi (-1 : ℝ) :=
    selfConcordantOmegaArg Mf r
      (neg_one_lt_mf_mul_of_nonneg (hessianLocalNorm_nonneg f y h))
  let ψ : ℝ → ℝ := fun u ↦ inner ℝ (∇ f (y + u • h) - ∇ f y) h
  have hr_nonneg : 0 ≤ r := by
    simpa [r, h] using hessianLocalNorm_nonneg f y (z - y)
  have hMf_pos_nn : 0 < Mf := lt_of_le_of_ne Mf.2 (Ne.symm hMf)
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact_mod_cast hMf_pos_nn
  have hsegment :
      ∀ u ∈ Set.Icc (0 : ℝ) 1, y + u • h ∈ dom := by
    intro u hu
    simpa [h] using segment_point_mem hself hy hz hu.1 hu.2
  have hgradLine_int :
      IntervalIntegrable (fun u : ℝ ↦ inner ℝ (∇ f (y + u • h)) h) MeasureTheory.volume 0 1 := by
    have hcont :
        ContinuousOn (fun u : ℝ ↦ inner ℝ (∇ f (y + u • h)) h) (Set.Icc (0 : ℝ) 1) := by
      intro u hu
      exact (scalarized_gradient_line_hasDerivAt hself (hsegment u hu)).continuousAt.continuousWithinAt
    exact hcont.intervalIntegrable_of_Icc (by norm_num)
  have hconst_int :
      IntervalIntegrable (fun _ : ℝ ↦ inner ℝ (∇ f y) h) MeasureTheory.volume 0 1 := by
    exact intervalIntegral.intervalIntegrable_const
  have hvalue_eq :
      f z - f y = ∫ u in 0..1, inner ℝ (∇ f (y + u • h)) h := by
    have hz_line : y + h = z := by
      dsimp [h]
      abel
    simpa [hz_line] using segment_scalar_integral_eq hself hsegment
  have hψ_cont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1) := by
    intro u hu
    have hcont :
        ContinuousAt (fun s : ℝ ↦ inner ℝ (∇ f (y + s • h)) h) u := by
      exact (scalarized_gradient_line_hasDerivAt hself (hsegment u hu)).continuousAt
    have hψ_eq :
        ψ = fun s : ℝ ↦ inner ℝ (∇ f (y + s • h)) h - inner ℝ (∇ f y) h := by
      ext s
      simp [ψ, inner_sub_left]
    rw [hψ_eq]
    exact (hcont.sub continuousAt_const).continuousWithinAt
  have hintψ :
      IntervalIntegrable ψ MeasureTheory.volume 0 1 := by
    exact hψ_cont.intervalIntegrable_of_Icc (by norm_num)
  have hint_lower :
      IntervalIntegrable
        (fun u : ℝ ↦ u * r ^ (2 : ℕ) / (1 + u * ((Mf : ℝ) * r)))
        MeasureTheory.volume 0 1 := by
    have hcont :
        ContinuousOn
          (fun u : ℝ ↦ u * r ^ (2 : ℕ) / (1 + u * ((Mf : ℝ) * r)))
          (Set.Icc (0 : ℝ) 1) := by
      refine (continuousOn_id.mul continuousOn_const).div ?_ ?_
      · exact (show Continuous (fun u : ℝ ↦ 1 + u * ((Mf : ℝ) * r)) by continuity).continuousOn
      · intro u hu
        have hden_nonneg : 0 ≤ u * ((Mf : ℝ) * r) := by
          exact mul_nonneg hu.1 (mul_nonneg hMf_pos.le hr_nonneg)
        have hden_pos : 0 < 1 + u * ((Mf : ℝ) * r) := by
          linarith
        exact hden_pos.ne'
    exact hcont.intervalIntegrable_of_Icc (by norm_num)
  have hmono :
      ∫ u in 0..1, u * r ^ (2 : ℕ) / (1 + u * ((Mf : ℝ) * r)) ≤
        ∫ u in 0..1, ψ u := by
    refine intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ 1 by norm_num) hint_lower hintψ ?_
    intro u hu
    simpa [h, r, ψ, mul_assoc, mul_left_comm, mul_comm] using
      segment_gradient_increment_lower_bound_at_base
        (Mf := Mf) (f := f) hMf (x := y) (y := z) hy hz (α := u) hu.1 hu.2
  have hgap_eq :
      f z - f y - inner ℝ (∇ f y) h = ∫ u in 0..1, ψ u := by
    calc
      f z - f y - inner ℝ (∇ f y) h
          = (∫ u in 0..1, inner ℝ (∇ f (y + u • h)) h) - ∫ u in 0..1, inner ℝ (∇ f y) h := by
              rw [hvalue_eq]
              simp
      _ = ∫ u in 0..1, (inner ℝ (∇ f (y + u • h)) h - inner ℝ (∇ f y) h) := by
            symm
            exact intervalIntegral.integral_sub hgradLine_int hconst_int
      _ = ∫ u in 0..1, ψ u := by
            refine intervalIntegral.integral_congr ?_
            intro u hu
            simp [ψ, inner_sub_left]
  have hgap :
      (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω tω ≤
        f z - f y - inner ℝ (∇ f y) h := by
    calc
      (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω tω
          = ∫ u in 0..1, u * r ^ (2 : ℕ) / (1 + u * ((Mf : ℝ) * r)) := by
              symm
              simpa [r, tω, mul_assoc, mul_left_comm, mul_comm] using
                integral_mul_sq_div_eq_omega (Mf := Mf) (r := r) hr_nonneg hMf_pos
      _ ≤ ∫ u in 0..1, ψ u := hmono
      _ = f z - f y - inner ℝ (∇ f y) h := hgap_eq.symm
  linarith

/-- Helper for Theorem 5.1.13: the base-point gradient pairing is controlled by the dual local
norm times the base local distance to the comparison point. -/
private theorem gradient_pairing_le_dualLocalNorm_mul_baseDistance
    {y z : E} (hy : y ∈ dom) :
    let δ := HessianDualLocalNorm.ofPosDefMem f hy (InnerProductSpace.toDual ℝ E (∇ f y))
    inner ℝ (∇ f y) (y - z) ≤ δ * ‖z - y‖[f; y] := by
  have hyz : y - z = -(z - y) := by
    abel
  have hnorm : ‖y - z‖[f; y] = ‖z - y‖[f; y] := by
    rw [hyz, hessianLocalNorm_neg]
  have hpair_abs :
      |inner ℝ (∇ f y) (y - z)| ≤
        HessianDualLocalNorm.ofPosDefMem f hy (InnerProductSpace.toDual ℝ E (∇ f y)) *
          ‖y - z‖[f; y] :=
    abs_toDual_apply_le_dualLocalNorm_mul_hessianLocalNorm_ofPosDefMem
      (f := f) hy (∇ f y) (y - z)
  calc
    inner ℝ (∇ f y) (y - z) ≤ |inner ℝ (∇ f y) (y - z)| := le_abs_self _
    _ ≤
        HessianDualLocalNorm.ofPosDefMem f hy (InnerProductSpace.toDual ℝ E (∇ f y)) *
          ‖y - z‖[f; y] := hpair_abs
    _ =
        HessianDualLocalNorm.ofPosDefMem f hy (InnerProductSpace.toDual ℝ E (∇ f y)) *
          ‖z - y‖[f; y] := by
          rw [hnorm]

/-- Helper for Theorem 5.1.13: the scalar Fenchel--Young inequality eliminates the remaining base
distance in favor of the canonical `ω_*` term. -/
private theorem fenchel_eliminate_base_distance
    {r δ : ℝ} (hMf : Mf ≠ 0) (hr : 0 ≤ r) (hδ : δ < 1 / (Mf : ℝ)) :
    let tω := selfConcordantOmegaArg Mf r (neg_one_lt_mf_mul_of_nonneg hr)
    let τω := selfConcordantOmegaStarArg Mf δ (mf_mul_lt_one_of_lt_inv hδ)
    δ * r - (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω tω ≤
      (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω_* τω := by
  let tω := selfConcordantOmegaArg Mf r (neg_one_lt_mf_mul_of_nonneg hr)
  let τω := selfConcordantOmegaStarArg Mf δ (mf_mul_lt_one_of_lt_inv hδ)
  have hMf_pos_nn : 0 < Mf := lt_of_le_of_ne Mf.2 (Ne.symm hMf)
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact_mod_cast hMf_pos_nn
  have hcore :
      ω tω + ω_* τω ≥ ((Mf : ℝ) * δ) * ((Mf : ℝ) * r) := by
    simpa [tω, τω, mul_assoc, mul_left_comm, mul_comm] using
      (selfConcordantOmega_add_selfConcordantOmegaStar_ge_mul
        (t := (Mf : ℝ) * r) (τ := (Mf : ℝ) * δ)
        (by exact mul_nonneg Mf.2 hr) (mf_mul_lt_one_of_lt_inv hδ))
  have hscale : 0 < 1 / (Mf : ℝ) ^ (2 : ℕ) := by
    positivity
  have hscaled :
      (1 / (Mf : ℝ) ^ (2 : ℕ)) * (((Mf : ℝ) * δ) * ((Mf : ℝ) * r)) ≤
        (1 / (Mf : ℝ) ^ (2 : ℕ)) * (ω tω + ω_* τω) := by
    exact mul_le_mul_of_nonneg_left hcore hscale.le
  have hrewrite :
      (1 / (Mf : ℝ) ^ (2 : ℕ)) * (((Mf : ℝ) * δ) * ((Mf : ℝ) * r)) = δ * r := by
    field_simp [hMf_pos.ne']
  linarith [hscaled, hrewrite]

/-- Helper for Theorem 5.1.13: under a nonzero self-concordance parameter, the dual-gradient
smallness hypothesis gives the standard minimizer-side upper `ω_*` bound. -/
private theorem suboptimality_upper_bound_of_dual_gradient_norm_at_minimizer_nonzero
    {xStar y : E} (hself : IsSelfConcordantOnWith dom Mf f)
    (hMf : Mf ≠ 0) (hxStar : xStar ∈ dom) (hmin : IsMinOn f dom xStar) (hy : y ∈ dom)
    (hδ : HessianDualLocalNorm.ofPosDefMem f hy (InnerProductSpace.toDual ℝ E (∇ f y)) <
      1 / (Mf : ℝ)) :
    let τω := selfConcordantOmegaStarArg Mf
      (HessianDualLocalNorm.ofPosDefMem f hy (InnerProductSpace.toDual ℝ E (∇ f y)))
      (mf_mul_lt_one_of_lt_inv hδ)
    f y ≤
      f xStar + (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω_* τω := by
  let h : E := xStar - y
  let r : ℝ := ‖h‖[f; y]
  let δ : ℝ := HessianDualLocalNorm.ofPosDefMem f hy (InnerProductSpace.toDual ℝ E (∇ f y))
  let τω : Set.Iio (1 : ℝ) := selfConcordantOmegaStarArg Mf δ (mf_mul_lt_one_of_lt_inv hδ)
  have hTaylor :
      f xStar ≥
        f y + inner ℝ (∇ f y) h +
          (1 / (Mf : ℝ) ^ (2 : ℕ)) *
            ω (selfConcordantOmegaArg Mf r
              (neg_one_lt_mf_mul_of_nonneg (hessianLocalNorm_nonneg f y h))) := by
    simpa [h, r] using
      taylor_lower_bound_from_base_by_local_distance_nonzero
        (Mf := Mf) (f := f) hself hMf hy hxStar
  have hpair :
      inner ℝ (∇ f y) (y - xStar) ≤ δ * r := by
    simpa [h, r, δ] using
      gradient_pairing_le_dualLocalNorm_mul_baseDistance
        (f := f) (y := y) (z := xStar) hy
  have hfenchel :
      δ * r -
          (1 / (Mf : ℝ) ^ (2 : ℕ)) *
            ω (selfConcordantOmegaArg Mf r
              (neg_one_lt_mf_mul_of_nonneg (hessianLocalNorm_nonneg f y h))) ≤
        (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω_* τω := by
    simpa [δ, r, τω] using
      fenchel_eliminate_base_distance (Mf := Mf) (r := r) (δ := δ) hMf
        (by simpa [r] using hessianLocalNorm_nonneg f y h) hδ
  have hsign : inner ℝ (∇ f y) (y - xStar) = -inner ℝ (∇ f y) h := by
    rw [show y - xStar = -h by
      dsimp [h]
      abel]
    simp
  have hmain :
      f y ≤ f xStar + (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω_* τω := by
    have hTaylor' :
        f y - f xStar ≤
          inner ℝ (∇ f y) (y - xStar) -
            (1 / (Mf : ℝ) ^ (2 : ℕ)) *
              ω (selfConcordantOmegaArg Mf r
                (neg_one_lt_mf_mul_of_nonneg (hessianLocalNorm_nonneg f y h))) := by
      have hTaylor'' :
          f y - f xStar ≤
            -inner ℝ (∇ f y) h -
              (1 / (Mf : ℝ) ^ (2 : ℕ)) *
                ω (selfConcordantOmegaArg Mf r
                  (neg_one_lt_mf_mul_of_nonneg (hessianLocalNorm_nonneg f y h))) := by
        linarith
      calc
        f y - f xStar ≤
            -inner ℝ (∇ f y) h -
              (1 / (Mf : ℝ) ^ (2 : ℕ)) *
                ω (selfConcordantOmegaArg Mf r
                  (neg_one_lt_mf_mul_of_nonneg (hessianLocalNorm_nonneg f y h))) := hTaylor''
        _ = inner ℝ (∇ f y) (y - xStar) -
              (1 / (Mf : ℝ) ^ (2 : ℕ)) *
                ω (selfConcordantOmegaArg Mf r
                  (neg_one_lt_mf_mul_of_nonneg (hessianLocalNorm_nonneg f y h))) := by
              rw [hsign]
    linarith
  simpa [δ, τω, selfConcordantOmegaStar_apply] using hmain

lemma suboptimality_upper_bound_at_minimizer_of_newtonDecrement_lt_inv
    {x : E} (xStar : dom) (hx : x ∈ dom)
    (hmin : IsMinOn f dom (xStar : E))
    (hlambda : λ[f; x | hx] < 1 / (Mf : ℝ)) :
    let τω := NewtonDecrement.omegaStarArgOfPosDefMem Mf f x hx hlambda
    f x - f xStar ≤
      (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω_* τω := by
  dsimp
  have hself : IsSelfConcordantOnWith dom Mf f := inferInstance
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact_mod_cast mf_pos_of_newtonDecrement_lt_inv (Mf := Mf) (f := f) hx hlambda
  have hMf_ne : Mf ≠ 0 := by
    exact ne_of_gt (mf_pos_of_newtonDecrement_lt_inv (Mf := Mf) (f := f) hx hlambda)
  have hupper :
      f x ≤
        f xStar +
          (1 / (Mf : ℝ) ^ (2 : ℕ)) *
            ω_* (NewtonDecrement.omegaStarArgOfPosDefMem Mf f x hx hlambda) := by
    -- View the Newton decrement as the dual local norm of the live gradient covector at `x`.
    simpa [NewtonDecrement.ofPosDefMem, HessianDualLocalNorm.ofPosDefMem,
      NewtonDecrement.omegaStarArgOfPosDefMem] using
      (suboptimality_upper_bound_of_dual_gradient_norm_at_minimizer_nonzero
        (Mf := Mf) (f := f) (xStar := (xStar : E)) (y := x)
        hself hMf_ne xStar.2 hmin hx hlambda)
  -- Rearrange the upper model into the stated suboptimality form.
  exact (sub_le_iff_le_add').2 <| by
    simpa [selfConcordantOmegaStar_apply, NewtonDecrement.omegaStarArgOfPosDefMem] using hupper

/-- Helper for Theorem 5.1.13: the scalar open-domain quadratic counterexample objective is
`x ↦ x² / 2`. -/
private abbrev openQuadraticObjective : ℝ → ℝ :=
  quadraticAffineObjective 0 (0 : ℝ) (1 : ℝ →L[ℝ] ℝ)

/-- Helper for Theorem 5.1.13: expanding the scalar quadratic counterexample gives the usual
`x² / 2` formula. -/
private lemma openQuadraticObjective_eq (x : ℝ) :
    openQuadraticObjective x = x ^ (2 : ℕ) / 2 := by
  -- Unfold the quadratic-affine owner and normalize the scalar expression.
  simp [openQuadraticObjective, quadraticAffineObjective, pow_two]
  ring

/-- Helper for Theorem 5.1.13: the scalar quadratic counterexample has identity Hessian
everywhere. -/
private lemma openQuadraticObjective_hessian_eq (x : ℝ) :
    hessian openQuadraticObjective x = (1 : ℝ →L[ℝ] ℝ) := by
  -- Reuse the global quadratic Hessian formula specialized to the identity operator.
  simpa [openQuadraticObjective] using quadraticAffineObjective_hessian_eq 0 (0 : ℝ)
    (1 : ℝ →L[ℝ] ℝ)
    (by
      simpa using
        (ContinuousLinearMap.isPositive_one : (1 : ℝ →L[ℝ] ℝ).IsPositive).isSelfAdjoint) x

/-- Helper for Theorem 5.1.13: the scalar quadratic counterexample has gradient `∇f(x) = x`. -/
private lemma openQuadraticObjective_gradient_eq (x : ℝ) :
    ∇ openQuadraticObjective x = x := by
  -- Specialize the quadratic gradient formula to the zero affine term and identity Hessian.
  simpa [openQuadraticObjective] using congrFun
    (quadraticAffineObjective_gradient_eq 0 (0 : ℝ) (1 : ℝ →L[ℝ] ℝ)
      (by
        simpa using
          (ContinuousLinearMap.isPositive_one : (1 : ℝ →L[ℝ] ℝ).IsPositive).isSelfAdjoint)) x

/-- Helper for Theorem 5.1.13: the scalar quadratic counterexample is self-concordant on
`(0, ∞)` with parameter `0`. -/
private instance openQuadraticObjective_selfConcordantOnIoi :
    IsSelfConcordantOnWith (Set.Ioi (0 : ℝ)) 0 openQuadraticObjective where
  isOpen_domain := isOpen_Ioi
  contDiffOn := (quadraticAffineObjective_contDiff 0 (0 : ℝ) (1 : ℝ →L[ℝ] ℝ)).contDiffOn
  convexOn := by
    have hC2 : ContDiffOn ℝ 2 openQuadraticObjective (Set.Ioi (0 : ℝ)) := by
      -- The global `C³` quadratic regularity restricts directly to the open half-line.
      exact (quadraticAffineObjective_contDiff 0 (0 : ℝ) (1 : ℝ →L[ℝ] ℝ)).of_le
        (by norm_num) |>.contDiffOn
    -- Convexity follows from the identity Hessian being positive on the open interval.
    refine (convexOn_iff_hessian_isPositive isOpen_Ioi (convex_Ioi (0 : ℝ)) hC2).2 ?_
    intro x hx
    rw [openQuadraticObjective_hessian_eq x]
    simp
  third_deriv_bound := by
    intro x hx u
    -- The third directional derivative vanishes for every quadratic objective.
    rw [quadraticAffineObjective_thirdDirectionalDerivative_eq_zero 0 (0 : ℝ)
      (1 : ℝ →L[ℝ] ℝ) x u]
    simp

/-- Helper for Theorem 5.1.13: the scalar quadratic counterexample has positive-definite Hessian
on `(0, ∞)`. -/
private instance openQuadraticObjective_hasPositiveDefiniteHessianOnIoi :
    HasPositiveDefiniteHessianOn (Set.Ioi (0 : ℝ)) openQuadraticObjective where
  isPositive := by
    intro x hx
    -- The Hessian is the identity map, which is positive.
    rw [openQuadraticObjective_hessian_eq x]
    simp
  posdef := by
    intro x hx u hu
    -- The identity Hessian gives the positive quadratic form `u²` on nonzero directions.
    rw [openQuadraticObjective_hessian_eq x]
    simpa using sq_pos_of_ne_zero hu

/-- Helper for Theorem 5.1.13: at `x = 1 / 2`, the scalar quadratic counterexample has Newton
decrement exactly `1 / 2`. -/
private lemma openQuadraticObjective_newtonDecrement_half
    (hx : (1 / 2 : ℝ) ∈ Set.Ioi (0 : ℝ)) :
    λ[openQuadraticObjective; (1 / 2 : ℝ) | hx] = 1 / 2 := by
  -- Expand the Newton decrement through the explicit gradient and inverse-Hessian formulas.
  rw [NewtonDecrement.ofPosDefMem_def]
  rw [openQuadraticObjective_gradient_eq (1 / 2 : ℝ)]
  have hinv : (hessian openQuadraticObjective (1 / 2 : ℝ)).inverse = (1 : ℝ →L[ℝ] ℝ) := by
    -- The identity operator is its own inverse.
    rw [openQuadraticObjective_hessian_eq]
    change (ContinuousLinearMap.id ℝ ℝ).inverse = ContinuousLinearMap.id ℝ ℝ
    exact ContinuousLinearMap.inverse_id
  rw [hinv]
  norm_num

/-- Helper for Theorem 5.1.13: the scalar quadratic counterexample never attains a minimum on the
open half-line, because moving halfway toward `0` strictly decreases the value. -/
private lemma openQuadraticObjective_not_isMinOn_Ioi
    {x : ℝ} (hx : x ∈ Set.Ioi (0 : ℝ)) :
    ¬ IsMinOn openQuadraticObjective (Set.Ioi (0 : ℝ)) x := by
  intro hmin
  have hx0 : 0 < x := hx
  have hhalf : x / 2 ∈ Set.Ioi (0 : ℝ) := by
    -- Halving preserves strict positivity on the open half-line.
    simpa [Set.mem_Ioi] using half_pos hx0
  have hle : openQuadraticObjective x ≤ openQuadraticObjective (x / 2) := hmin hhalf
  have hlt : openQuadraticObjective (x / 2) < openQuadraticObjective x := by
    -- The explicit `x² / 2` formula shows strict decay under `x ↦ x / 2`.
    rw [openQuadraticObjective_eq (x / 2), openQuadraticObjective_eq x]
    have hsq : 0 < x ^ (2 : ℕ) := by
      nlinarith [sq_pos_of_pos hx0]
    nlinarith
  exact (not_lt_of_ge hle) hlt

/-- Helper refutation for Theorem 5.1.13: under the bare current Chapter 5 owners alone, the
small-Newton-decrement condition does not force attainment on `dom`; the scalar quadratic
objective on `(0, ∞)` is the local counterexample. -/
private theorem openQuadraticObjectiveCounterexample :
    ∃ x : Set.Ioi (0 : ℝ),
      λ[openQuadraticObjective; (x : ℝ) | x.2] < 1 / ((1 : NNReal) : ℝ) ∧
        ¬ ∃ xStar : Set.Ioi (0 : ℝ),
          IsMinOn openQuadraticObjective (Set.Ioi (0 : ℝ)) (xStar : ℝ) := by
  refine ⟨⟨1 / 2, by norm_num⟩, ?_⟩
  constructor
  · -- The explicit Newton decrement value is `1 / 2`, so it is strictly below `1`.
    rw [openQuadraticObjective_newtonDecrement_half]
    norm_num
  · rintro ⟨xStar, hmin⟩
    -- The no-minimizer lemma closes the contradiction for every candidate point.
    exact openQuadraticObjective_not_isMinOn_Ioi xStar.2 hmin

/-- Helper for Theorem 5.1.13: once minimizer attainment is assumed separately, the auxiliary
attained-case route may use that feasible minimizer directly. -/
lemma exists_isMinOn_of_newtonDecrement_lt_inv
    {x : E} (hx : x ∈ dom)
    (_ : λ[f; x | hx] < 1 / (Mf : ℝ))
    (hattain : ∃ xStar : dom, IsMinOn f dom (xStar : E)) :
    ∃ xStar : dom, IsMinOn f dom (xStar : E) := by
  let _ := (inferInstance : IsSelfConcordantOnWith dom Mf f)
  simpa using hattain

-- Proof sketch: once a minimizer is assumed to exist, the small-Newton-decrement hypothesis
-- supplies the canonical `ω_*` upper model at that minimizer, and strict convexity from the
-- positive-definite Hessian gives uniqueness.
/-- Helper for Theorem 5.1.13: if minimizer attainment is given separately, the small-Newton-
decrement hypothesis upgrades that minimizer to a unique one and yields the standard `ω_*`
suboptimality bound. -/
theorem existsUnique_isMinOn_with_suboptimality_bound_of_attainment
    {x : E} (hx : x ∈ dom)
    (hlambda : λ[f; x | hx] < 1 / (Mf : ℝ))
    (hattain : ∃ xStar : dom, IsMinOn f dom (xStar : E)) :
    let τω := NewtonDecrement.omegaStarArgOfPosDefMem Mf f x hx hlambda
    ∃! xStar : dom,
      IsMinOn f dom (xStar : E) ∧
        f x - f xStar ≤
          (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω_* τω := by
  dsimp
  have hself : IsSelfConcordantOnWith dom Mf f := inferInstance
  obtain ⟨xStar, hmin⟩ := exists_isMinOn_of_newtonDecrement_lt_inv hx hlambda hattain
  refine ⟨xStar, ?_, ?_⟩
  · constructor
    · exact hmin
    · simpa using
        suboptimality_upper_bound_at_minimizer_of_newtonDecrement_lt_inv xStar hx hmin hlambda
  · intro yStar hyStar
    exact
      eq_of_isMinOn_of_isMinOn
        hself xStar yStar hmin hyStar.1 |>.symm

/-- Theorem 5.1.13: if `x ∈ dom` satisfies `λ_f(x) < 1 / M_f` and the problem
`min {f(u) | u ∈ dom}` attains a minimum on `dom`, then it admits a unique solution `x_f*`, and
the standard `ω_*` suboptimality bound holds at `x`. The current local Chapter 5 owners still
admit `openQuadraticObjectiveCounterexample`, so this source-facing theorem keeps the missing
attainment premise explicit rather than suppressing the open-domain counterexample. -/
theorem existsUnique_isMinOn_with_suboptimality_bound_of_newtonDecrement_lt_inv
    {x : E} (hx : x ∈ dom)
    (hlambda : λ[f; x | hx] < 1 / (Mf : ℝ))
    (hattain : ∃ xStar : dom, IsMinOn f dom (xStar : E)) :
    let τω := NewtonDecrement.omegaStarArgOfPosDefMem Mf f x hx hlambda
    ∃! xStar : dom,
      IsMinOn f dom (xStar : E) ∧
        f x - f xStar ≤
          (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω_* τω := by
  -- The theorem is exactly the attained-case wrapper already proved above.
  simpa using
    existsUnique_isMinOn_with_suboptimality_bound_of_attainment
      (Mf := Mf) (f := f) hx hlambda hattain

end

end
