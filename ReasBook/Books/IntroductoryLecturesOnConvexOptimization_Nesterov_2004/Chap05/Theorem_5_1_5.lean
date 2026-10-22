/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_12
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_23
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Example_5_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Lemma_5_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.FenchelPrimalExtension

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient HessianLocalNorm DikinEllipsoidNotation WithTopConvexAnalysis

/-
Theorem 5.1.5 belongs to the self-concordance / Dikin-ellipsoid domain.

Sampled owner declarations:
* `hessianLocalNorm` in `Chap05/Definition_5_1_1`, the canonical local Hessian norm;
* `openDikinEllipsoid` together with the notation `W⁰[f; x](r)` in `Chap05/Definition_5_0_13`,
  the Chapter 5 owner for the open local-norm ball;
* `mem_openDikinEllipsoid_iff_hessian_quadratic_lt_sq` in `Chap05/Definition_5_0_14`, the
  textbook quadratic bridge for the same Dikin geometry;
* `IsSelfConcordantOnWith` in `Chap05/Definition_5_1_1`, the chapter owner for quantitative
  self-concordance.

Best owner abstraction:
* source-facing: the open Dikin ellipsoid around `x`;
* core/canonical: `IsSelfConcordantOnWith dom Mf f` together with `‖u‖[f; x]`;
* bridge/view: the membership lemmas for `W⁰[f; x](r)` and its Hessian-quadratic reformulation.

Primitive data:
* a complete real inner-product space `E`;
* a domain `dom`, a real-valued function `f`, a self-concordance constant `Mf`, and
  points `x y : E`.

Derived API:
* the open Dikin ellipsoid `W⁰[f; x](r)`;
* the local displacement norms `‖y - x‖[f; x]` and `‖y - x‖[f; y]`.

This file records the Dikin-ellipsoid and local-norm transport consequences directly as
owner-level methods in `IsSelfConcordantOnWith`, rather than keeping a parallel top-level wrapper
API. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace IsSelfConcordantOnWith

variable {Mf : NNRealˣ} {f : E → WithTop ℝ}

-- Semantic recall note: `lean_leansearch` did not surface a matching mathlib owner for these
-- self-concordant Dikin transport statements, so the public API stays local to this chapter as
-- methods of `IsSelfConcordantOnWith`.

/-- Helper for Theorem 5.1.5: the unit-valued self-concordance parameter is strictly positive
after coercion to `ℝ`. -/
private lemma mf_pos : 0 < (Mf : ℝ) := by
  by_contra hMf
  have hMf_nonneg : 0 ≤ (Mf : ℝ) := by
    exact_mod_cast (show 0 ≤ (Mf : NNReal) by positivity)
  have hMf_eq_zero : (Mf : ℝ) = 0 := le_antisymm (le_of_not_gt hMf) hMf_nonneg
  have hMf_eq_zero_nn : (Mf : NNReal) = 0 := by
    exact_mod_cast hMf_eq_zero
  exact Mf.ne_zero hMf_eq_zero_nn

/-- Helper for Theorem 5.1.5: membership in the open Dikin ellipsoid at reciprocal radius is
exactly the strict local-norm inequality `‖y - x‖[withTopRealPart f; x] < 1 / (Mf : ℝ)`. -/
private lemma exactLocalNorm_lt_invConstant
    {x y : E}
    (hy : y ∈ W⁰[withTopRealPart f; x](1 / (Mf : ℝ))) :
    ‖y - x‖[withTopRealPart f; x] < 1 / (Mf : ℝ) := by
  -- Unpack the Dikin-ellipsoid membership into the exact local-radius inequality.
  simpa using (mem_openDikinEllipsoid_iff (withTopRealPart f) x y (1 / (Mf : ℝ))).1 hy

/-- Helper for Theorem 5.1.5: the exact Dikin factor stays positive under the reciprocal-radius
hypothesis. -/
private lemma exactLocalNormFactor_pos
    {x y : E}
    (hy : y ∈ W⁰[withTopRealPart f; x](1 / (Mf : ℝ))) :
    0 < 1 - (Mf : ℝ) * ‖y - x‖[withTopRealPart f; x] := by
  have hmul_lt_one :
      (Mf : ℝ) * ‖y - x‖[withTopRealPart f; x] < 1 := by
    -- Multiply the exact local-radius inequality by the positive constant `Mf`.
    simpa [mul_comm] using
      (lt_div_iff₀ mf_pos).1
        (@exactLocalNorm_lt_invConstant E _ _ _ Mf f x y hy)
  linarith

/-- Helper for Theorem 5.1.5: the slice quotient feeding the one-dimensional derivative estimate
is bounded by `Mf` at every admissible parameter. -/
private lemma associatedSliceThirdQuotientBound
    (hself : IsSelfConcordantOnWith (dom f) (Mf : NNReal) (withTopRealPart f))
    {x h : E} {t : ℝ}
    (ht : t ∈ associatedUnivariateFunctionDomain (dom f) (withTopRealPart f) x h) :
    |thirdDirectionalDerivative (withTopRealPart f) (x + t • h) h| /
        (2 * ‖h‖[withTopRealPart f; x + t • h] ^ (3 : ℕ)) ≤ (Mf : ℝ) := by
  rcases
    (mem_associatedUnivariateFunctionDomain_iff (dom f) (withTopRealPart f) x h t).1 ht with
    ⟨ht_dom, ht_pos⟩
  have hden_pos : 0 < 2 * ‖h‖[withTopRealPart f; x + t • h] ^ (3 : ℕ) := by
    -- The associated-slice domain records strict positivity of the local norm at the shifted
    -- point, so the cubic denominator is positive.
    have hpow_pos : 0 < ‖h‖[withTopRealPart f; x + t • h] ^ (3 : ℕ) := by
      positivity
    positivity
  -- Divide the self-concordance diagonal bound by the positive denominator.
  refine (div_le_iff₀ hden_pos).2 ?_
  simpa [mul_assoc, mul_left_comm, mul_comm] using hself.third_deriv_bound ht_dom h

/-- Helper for Theorem 5.1.5: every affine parameter `t ∈ [0,1]` yields the corresponding point
on `segment ℝ x y`. -/
private lemma segmentPoint_mem
    {x y : E} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    x + t • (y - x) ∈ segment ℝ x y := by
  -- Rewrite the affine interpolation point into the canonical line-map description of the
  -- segment.
  rw [segment_eq_image_lineMap]
  refine ⟨t, ht, ?_⟩
  simp [AffineMap.lineMap_apply_module', add_comm]

/-- Helper for Theorem 5.1.5: the affine segment parameterization has derivative equal to its
constant direction. -/
private lemma affineSegment_hasDerivAt
    {x d : E} (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ x + s • d) d t := by
  -- Differentiate scalar multiplication and then translate by the fixed base point.
  simpa [one_smul] using ((hasDerivAt_id t).smul_const d).const_add x

/-- Helper for Theorem 5.1.5: a pointwise `C³` hypothesis upgrades the Hessian owner to a
Fréchet-differentiable operator-valued map. -/
private lemma hessian_hasFDerivAt_of_contDiffAt
    {g : E → ℝ} {z : E} (hcontAt : ContDiffAt ℝ 3 g z) :
    HasFDerivAt (hessian g) (fderiv ℝ (hessian g) z) z := by
  -- Differentiate the Hessian field once more after transporting the gradient through the Riesz
  -- isomorphism.
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfderiv_C2 : ContDiffAt ℝ 2 (fderiv ℝ g) z := by
    exact hcontAt.fderiv_right (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)
  have hD_contDiffAt : ContDiffAt ℝ 2 D (fderiv ℝ g z) := by
    exact (D.contDiff.of_le (show (2 : WithTop ℕ∞) ≤ ⊤ by simp)).contDiffAt
  have hgrad_C2 : ContDiffAt ℝ 2 (fun y ↦ ∇ g y) z := by
    simpa [gradient, D] using hD_contDiffAt.comp z hfderiv_C2
  have hhessian_C1 : ContDiffAt ℝ 1 (hessian g) z := by
    simpa [hessian] using
      hgrad_C2.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  -- Convert the `C¹` regularity of the Hessian map into the requested Fréchet derivative.
  exact (hhessian_C1.hasStrictFDerivAt one_ne_zero).hasFDerivAt

/-- Helper for Theorem 5.1.5: the scalarized Hessian quadratic form
`s ↦ inner ℝ v (hessian g (x + s • (y - x)) v)` differentiates to the mixed Hessian-direction
pairing. -/
private lemma segmentScalarizedHessian_hasDerivAt
    {g : E → ℝ} {x y v : E}
    {z : ℝ → E} (hz : z = fun t ↦ x + t • (y - x))
    {t : ℝ}
    (hcontAt : ContDiffAt ℝ 3 g (z t)) :
    HasDerivAt (fun s : ℝ ↦ inner ℝ v (hessian g (z s) v))
      (inner ℝ v ((fderiv ℝ (hessian g) (z t) (y - x)) v)) t := by
  have hzLine : HasDerivAt z (y - x) t := by
    -- Specialize the affine-line derivative to the segment parameterization.
    subst hz
    have hline : HasDerivAt (fun s : ℝ ↦ x + s • (y - x)) (y - x) t :=
      affineSegment_hasDerivAt t
    simpa using hline
  have hhessianDeriv :
      HasFDerivAt (hessian g) (fderiv ℝ (hessian g) (z t)) (z t) :=
    hessian_hasFDerivAt_of_contDiffAt hcontAt
  have happly :
      HasDerivAt (fun s : ℝ ↦ hessian g (z s) v)
        ((fderiv ℝ (hessian g) (z t) (y - x)) v) t := by
    -- Differentiate the Hessian field along the segment and then evaluate it on the fixed
    -- direction `v`.
    have happlyF :
        HasFDerivAt (fun w : E ↦ hessian g w v)
          ((ContinuousLinearMap.apply ℝ E v).comp (fderiv ℝ (hessian g) (z t))) (z t) := by
      exact (ContinuousLinearMap.apply ℝ E v).hasFDerivAt.comp (z t) hhessianDeriv
    simpa using happlyF.comp_hasDerivAt t hzLine
  have hinnerF :
      HasFDerivAt (fun w : E ↦ inner ℝ v w) ((innerSL ℝ) v) (hessian g (z t) v) := by
    -- Postcompose with the scalar pairing against `v`.
    simpa using ((innerSL ℝ) v).hasFDerivAt
  simpa using hinnerF.comp_hasDerivAt t happly

/-- Helper for Theorem 5.1.5: the displacement local norm varies continuously along the affine
segment `t ↦ x + t • (y - x)`. -/
private lemma segmentDisplacementLocalNorm_continuousOn
    {g : E → ℝ} {x y : E}
    {z : ℝ → E} (hz : z = fun t ↦ x + t • (y - x))
    (hcont : ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) 1 →
      ContDiffAt ℝ 3 g (z t)) :
    ContinuousOn (fun t ↦ ‖y - x‖[g; z t]) (Set.Icc (0 : ℝ) 1) := by
  intro t ht
  let d : E := y - x
  let ψ : ℝ → ℝ := fun s ↦ inner ℝ d (hessian g (z s) d)
  have hψ_deriv' :
      HasDerivAt (fun s : ℝ ↦ inner ℝ d (hessian g (z s) d))
        (inner ℝ d ((fderiv ℝ (hessian g) (z t) d) d)) t := by
    -- Differentiate the scalarized Hessian quadratic form first, then retain continuity.
    simpa [d] using
      (@segmentScalarizedHessian_hasDerivAt E _ _ _ g x y d z hz t (hcont ht))
  have hψ_deriv : HasDerivAt ψ (inner ℝ d ((fderiv ℝ (hessian g) (z t) d) d)) t := by
    simpa [ψ] using hψ_deriv'
  have hψ_contAt : ContinuousAt ψ t := hψ_deriv.continuousAt
  have hsqrt_contAt : ContinuousAt Real.sqrt (ψ t) := by
    simpa using Real.continuous_sqrt.continuousAt
  -- The local norm is the square root of that quadratic form, so continuity follows by
  -- composition with `Real.sqrt`.
  simpa [ψ, d, hessianLocalNorm_def] using
    (hsqrt_contAt.comp hψ_contAt).continuousWithinAt

/-- Helper for Theorem 5.1.5: on any positive prefix of the segment from `x` to `y`, the
reciprocal local norm of the displacement changes by at most `(Mf : ℝ) * s`. -/
private lemma segmentReciprocalLocalNorm_absDiff_le_of_positivePrefix
    {domain : Set E} {Mf : NNReal} {g : E → ℝ} {x y : E}
    (hself : IsSelfConcordantOnWith domain Mf g)
    (hx : x ∈ domain) (hy : y ∈ domain) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hprefix : ∀ u ∈ Set.Icc (0 : ℝ) s, 0 < ‖y - x‖[g; x + u • (y - x)]) :
    |(1 / ‖y - x‖[g; x + s • (y - x)]) - (1 / ‖y - x‖[g; x])| ≤ (Mf : ℝ) * s := by
  have hprefix_subset :
      Set.Icc (0 : ℝ) s ⊆ associatedUnivariateFunctionDomain domain g x (y - x) := by
    intro u hu
    refine (mem_associatedUnivariateFunctionDomain_iff domain g x (y - x) u).2 ?_
    have hu_mem : x + u • (y - x) ∈ domain := by
      -- Convexity keeps every point of the positive prefix inside the domain.
      have hu_seg : x + u • (y - x) ∈ segment ℝ x y := by
        exact segmentPoint_mem ⟨hu.1, le_trans hu.2 hs.2⟩
      exact hself.convex_domain.segment_subset hx hy hu_seg
    exact ⟨hu_mem, hprefix u hu⟩
  have hderiv :
      ∀ u ∈ Set.Icc (0 : ℝ) s,
        HasDerivWithinAt (fun u : ℝ ↦ 1 / ‖y - x‖[g; x + u • (y - x)])
          (-(thirdDirectionalDerivative g (x + u • (y - x)) (y - x) /
              (2 * ‖y - x‖[g; x + u • (y - x)] ^ (3 : ℕ))))
          (Set.Icc (0 : ℝ) s)
          u := by
    intro u hu
    -- Restrict the canonical associated-univariate derivative formula to the concrete prefix.
    have hbase :
        HasDerivWithinAt
          (directionalSlice (fun z ↦ 1 / ‖y - x‖[g; z]) x (y - x))
          (-(thirdDirectionalDerivative g (x + u • (y - x)) (y - x) /
              (2 * ‖y - x‖[g; x + u • (y - x)] ^ (3 : ℕ))))
          (associatedUnivariateFunctionDomain domain g x (y - x))
          u := by
      simpa using
        (@associatedUnivariateFunction_hasDerivWithinAt
          E _ _ _ domain g x (y - x) u
          hself.isOpen_domain hself.contDiffOn (hprefix_subset hu))
    exact
      hbase.congr_mono
        (by
          intro t ht
          simp [directionalSlice])
        (by simp [directionalSlice])
        hprefix_subset
  have hbound :
      ∀ u ∈ Set.Icc (0 : ℝ) s,
        ‖-(thirdDirectionalDerivative g (x + u • (y - x)) (y - x) /
            (2 * ‖y - x‖[g; x + u • (y - x)] ^ (3 : ℕ)))‖ ≤ (Mf : ℝ) := by
    intro u hu
    -- The self-concordance quotient bound is exactly the derivative bound on the reciprocal slice.
    have hu_domain :
        x + u • (y - x) ∈ domain := by
      exact (mem_associatedUnivariateFunctionDomain_iff domain g x (y - x) u).1
        (hprefix_subset hu) |>.1
    have hu_pos : 0 < ‖y - x‖[g; x + u • (y - x)] := by
      exact (mem_associatedUnivariateFunctionDomain_iff domain g x (y - x) u).1
        (hprefix_subset hu) |>.2
    have hden_pos : 0 < 2 * ‖y - x‖[g; x + u • (y - x)] ^ (3 : ℕ) := by
      have hpow_pos : 0 < ‖y - x‖[g; x + u • (y - x)] ^ (3 : ℕ) := by
        positivity
      positivity
    have hquot :
        |thirdDirectionalDerivative g (x + u • (y - x)) (y - x)| /
            (2 * ‖y - x‖[g; x + u • (y - x)] ^ (3 : ℕ)) ≤ (Mf : ℝ) := by
      refine (div_le_iff₀ hden_pos).2 ?_
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        hself.third_deriv_bound hu_domain (y - x)
    simpa [Real.norm_eq_abs, abs_neg, abs_of_pos hu_pos] using hquot
  have hmv :
      ‖(1 / ‖y - x‖[g; x + s • (y - x)]) - (1 / ‖y - x‖[g; x + (0 : ℝ) • (y - x)])‖ ≤
        (Mf : ℝ) * ‖s - (0 : ℝ)‖ := by
    -- Apply the one-dimensional mean-value inequality on the convex interval `Set.Icc 0 s`.
    exact
      (convex_Icc (0 : ℝ) s).norm_image_sub_le_of_norm_hasDerivWithin_le
        hderiv hbound
        (by simpa using hs.1)
        (by exact ⟨hs.1, le_rfl⟩)
  have hmv' :
      |(1 / ‖y - x‖[g; x + s • (y - x)]) - (1 / ‖y - x‖[g; x + (0 : ℝ) • (y - x)])| ≤
        (Mf : ℝ) * |s - (0 : ℝ)| := by
    simpa [Real.norm_eq_abs] using hmv
  simpa [hs.1, abs_of_nonneg hs.1] using hmv'

/-- Helper for Theorem 5.1.5: a continuous nonnegative function on `[0,1]` with positive value
at `0` stays positive if every positive prefix satisfies the reciprocal control inequality. -/
private lemma positiveOn_unitInterval_of_prefixReciprocalControl
    {ψ : ℝ → ℝ} {M : ℝ}
    (hcont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1))
    (hM_nonneg : 0 ≤ M)
    (hnonneg : ∀ u ∈ Set.Icc (0 : ℝ) 1, 0 ≤ ψ u)
    (h0 : 0 < ψ 0)
    (hprefix : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (∀ u ∈ Set.Icc (0 : ℝ) s, 0 < ψ u) →
        |(1 / ψ s) - (1 / ψ 0)| ≤ M * s) :
    ∀ u ∈ Set.Icc (0 : ℝ) 1, 0 < ψ u := by
  intro u hu
  by_contra hu_not
  have hu_zero : ψ u = 0 := by
    have hu_nonneg : 0 ≤ ψ u := hnonneg u hu
    linarith
  let zset : Set (Set.Icc (0 : ℝ) 1) := {t | ψ (t : ℝ) = 0}
  have hψcont : Continuous fun t : Set.Icc (0 : ℝ) 1 ↦ ψ (t : ℝ) :=
    (continuousOn_iff_continuous_restrict.mp hcont)
  letI : CompactSpace (Set.Icc (0 : ℝ) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1))
  have hzset_closed : IsClosed zset := by
    -- View the zero set inside the compact interval subtype.
    simpa [zset] using isClosed_singleton.preimage hψcont
  obtain ⟨c, hc_mem, hc_least⟩ := hzset_closed.isCompact.exists_isLeast
    (by
      refine ⟨⟨u, hu⟩, ?_⟩
      simp [zset, hu_zero])
  have hc_zero : ψ (c : ℝ) = 0 := by
    simpa [zset] using hc_mem
  have hc_pos : 0 < (c : ℝ) := by
    -- The least zero cannot occur at the base point because `ψ 0` is positive.
    by_contra hc_not_pos
    have hc_eq_zero : (c : ℝ) = 0 := by
      linarith [c.2.1]
    have : ψ 0 = 0 := by
      simpa [hc_eq_zero] using hc_zero
    exact h0.ne' this
  have hleft_lower :
      ∀ s ∈ Set.Icc (0 : ℝ) 1, s < (c : ℝ) → 1 / (1 / ψ 0 + M) ≤ ψ s := by
    intro s hs hs_lt_c
    have hprefix_pos :
        ∀ v ∈ Set.Icc (0 : ℝ) s, 0 < ψ v := by
      intro v hv
      have hvIcc : v ∈ Set.Icc (0 : ℝ) 1 := ⟨hv.1, le_trans hv.2 hs.2⟩
      have hv_nonneg : 0 ≤ ψ v := hnonneg v hvIcc
      by_contra hv_not
      have hv_zero : ψ v = 0 := by
        linarith
      have hv_mem : (⟨v, hvIcc⟩ : Set.Icc (0 : ℝ) 1) ∈ zset := by
        simp [zset, hv_zero]
      have hcle : (c : ℝ) ≤ v := hc_least hv_mem
      exact not_le_of_gt hs_lt_c (le_trans hcle hv.2)
    have hbound : |(1 / ψ s) - (1 / ψ 0)| ≤ M * s :=
      hprefix s hs hprefix_pos
    have hs_nonneg : 0 ≤ s := hs.1
    have hs_le_one : s ≤ 1 := hs.2
    have hupper_prefix : 1 / ψ s ≤ 1 / ψ 0 + M * s := by
      have hpair := abs_le.mp hbound
      linarith
    have hupper : 1 / ψ s ≤ 1 / ψ 0 + M := by
      have hMs_le : M * s ≤ M := by
        nlinarith
      linarith
    have hs_pos : 0 < ψ s := hprefix_pos s ⟨hs.1, le_rfl⟩
    have hden_pos : 0 < 1 / ψ 0 + M := by
      have hrec_pos : 0 < 1 / ψ 0 := by positivity
      linarith
    exact (one_div_le hs_pos hden_pos).1 hupper
  have hden_pos : 0 < 1 / ψ 0 + M := by
    have hrec_pos : 0 < 1 / ψ 0 := by positivity
    linarith
  have hhalf_pos : 0 < (1 / (1 / ψ 0 + M)) / 2 := by
    positivity
  have hcontAt_c : ContinuousAt (fun t : Set.Icc (0 : ℝ) 1 ↦ ψ (t : ℝ)) c :=
    hψcont.continuousAt
  rcases (Metric.continuousAt_iff.mp hcontAt_c)
      ((1 / (1 / ψ 0 + M)) / 2) hhalf_pos with
    ⟨δ, hδ_pos, hδ⟩
  let η : ℝ := min (δ / 2) ((c : ℝ) / 2)
  have hη_pos : 0 < η := by
    -- Move a positive distance to the left while staying inside the interval and inside the
    -- continuity neighborhood.
    have hδ_half_pos : 0 < δ / 2 := by positivity
    have hc_half_pos : 0 < (c : ℝ) / 2 := by positivity
    exact lt_min hδ_half_pos hc_half_pos
  have hη_nonneg : 0 ≤ η := le_of_lt hη_pos
  have hη_le_delta : η < δ := by
    have : η ≤ δ / 2 := min_le_left _ _
    linarith
  let leftPoint : Set.Icc (0 : ℝ) 1 :=
    ⟨(c : ℝ) - η, by
      constructor
      · have hhalf_le : (c : ℝ) / 2 ≤ (c : ℝ) - η := by
          have hη_le_half : η ≤ (c : ℝ) / 2 := min_le_right _ _
          linarith
        linarith
      · linarith [c.2.2, hη_nonneg]⟩
  have hleft_lt_c : (leftPoint : ℝ) < (c : ℝ) := by
    dsimp [leftPoint]
    linarith
  have hleft_lower_bound : 1 / (1 / ψ 0 + M) ≤ ψ (leftPoint : ℝ) :=
    hleft_lower (leftPoint : ℝ) leftPoint.2 hleft_lt_c
  have hleft_dist : dist leftPoint c < δ := by
    change dist ((c : ℝ) - η) (c : ℝ) < δ
    rw [Real.dist_eq]
    simpa [sub_eq_add_neg, abs_of_nonneg hη_nonneg] using hη_le_delta
  have hclose :
      dist (ψ (leftPoint : ℝ)) (ψ (c : ℝ)) <
        (1 / (1 / ψ 0 + M)) / 2 := by
    exact hδ hleft_dist
  have hfar :
      (1 / (1 / ψ 0 + M)) / 2 ≤ dist (ψ (leftPoint : ℝ)) (ψ (c : ℝ)) := by
    -- The reciprocal bound forces a uniform positive lower bound strictly to the left of the
    -- first zero.
    rw [hc_zero, Real.dist_eq, sub_zero]
    have hleft_nonneg : 0 ≤ ψ (leftPoint : ℝ) := by
      exact hnonneg (leftPoint : ℝ) leftPoint.2
    have : (1 / (1 / ψ 0 + M)) / 2 ≤ ψ (leftPoint : ℝ) := by
      linarith
    rwa [abs_of_nonneg hleft_nonneg]
  exact not_lt_of_ge hfar hclose

/-- Helper for Theorem 5.1.5: if the displacement local norm is positive at `x`, then it stays
positive all along the segment to `y`, and the reciprocal local norm changes by at most `Mf`. -/
private lemma segmentReciprocalComparisonForDisplacement_core
    {domain : Set E} {Mf : NNReal} {g : E → ℝ}
    (hself : IsSelfConcordantOnWith domain Mf g)
    {x y : E} (hx : x ∈ domain) (hy : y ∈ domain)
    (hpos : 0 < ‖y - x‖[g; x]) :
    0 < ‖y - x‖[g; y] ∧
      |(1 / ‖y - x‖[g; y]) - (1 / ‖y - x‖[g; x])| ≤ (Mf : ℝ) := by
  let ψ : ℝ → ℝ := fun u ↦ ‖y - x‖[g; x + u • (y - x)]
  have hline_mem :
      ∀ {u : ℝ}, u ∈ Set.Icc (0 : ℝ) 1 → x + u • (y - x) ∈ domain := by
    intro u hu
    -- Convexity keeps the entire segment inside the domain.
    exact hself.convex_domain.segment_subset hx hy (segmentPoint_mem hu)
  have hψcont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1) := by
    -- The displacement local norm is continuous along the segment.
    simpa [ψ] using
      (@segmentDisplacementLocalNorm_continuousOn
        E _ _ _ g x y (fun t ↦ x + t • (y - x)) rfl
        (fun {t} ht ↦
          hself.contDiffOn.contDiffAt (hself.isOpen_domain.mem_nhds (hline_mem ht))))
  have hψpos :
      ∀ u ∈ Set.Icc (0 : ℝ) 1, 0 < ψ u := by
    -- Route correction: instead of a blow-up contradiction for the reciprocal, package the
    -- prefix estimate as a uniform positive lower bound and contradict a hypothetical first zero.
    refine positiveOn_unitInterval_of_prefixReciprocalControl
      hψcont (show 0 ≤ (Mf : ℝ) by positivity) ?_ ?_ ?_
    · intro u hu
      simpa [ψ] using hessianLocalNorm_nonneg g (x + u • (y - x)) (y - x)
    · simpa [ψ]
    · intro s hs hprefix
      simpa [ψ] using
        (segmentReciprocalLocalNorm_absDiff_le_of_positivePrefix
          hself hx hy hs
          (by
            intro u hu
            simpa [ψ] using hprefix u hu))
  have hy_pos : 0 < ‖y - x‖[g; y] := by
    simpa [ψ] using hψpos 1 (by simp)
  have hfull :
      |(1 / ‖y - x‖[g; x + (1 : ℝ) • (y - x)]) - (1 / ‖y - x‖[g; x])| ≤ (Mf : ℝ) * 1 := by
    -- Once positivity is known on the whole segment, the endpoint estimate is the `s = 1`
    -- specialization of the prefix bound.
    simpa [ψ] using
      (segmentReciprocalLocalNorm_absDiff_le_of_positivePrefix
        hself hx hy (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by simp)
        (by
          intro u hu
          simpa [ψ] using hψpos u hu))
  constructor
  · exact hy_pos
  · simpa using hfull

/-- Helper for Theorem 5.1.5: at any domain point of a self-concordant function, scaling the
displacement scales the local norm by the scalar's absolute value. -/
private lemma hessianLocalNorm_smul_eq_abs
    {domain : Set E} {Mf : NNReal} {g : E → ℝ}
    (hself : IsSelfConcordantOnWith domain Mf g)
    {z u : E} (hz : z ∈ domain) (a : ℝ) :
    ‖a • u‖[g; z] = |a| * ‖u‖[g; z] := by
  have hquad : 0 ≤ inner ℝ u (hessian g z u) := hself.hessian_posSemidef hz u
  -- Pull the scalar out of the Hessian quadratic form before taking square roots.
  calc
    ‖a • u‖[g; z] = Real.sqrt ((a * a) * inner ℝ u (hessian g z u)) := by
      rw [hessianLocalNorm_def]
      congr 1
      simp [inner_smul_left, inner_smul_right, mul_assoc]
    _ = Real.sqrt (inner ℝ u (hessian g z u)) * Real.sqrt (a * a) := by
      rw [mul_comm, Real.sqrt_mul hquad]
    _ = |a| * ‖u‖[g; z] := by
      rw [show a * a = a ^ (2 : ℕ) by ring, Real.sqrt_sq_eq_abs, hessianLocalNorm_def]
      ring

/-- Helper for Theorem 5.1.5: a reciprocal-comparison estimate for two positive local norms
rearranges to the standard lower transport factor. -/
private lemma localNorm_lower_bound_of_reciprocal_comparison
    {a b M : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hcomp : |(1 / b) - (1 / a)| ≤ M) :
    a / (1 + M * a) ≤ b := by
  have hM_nonneg : 0 ≤ M := by
    -- The absolute-value bound already forces the comparison constant to be nonnegative.
    have habs_nonneg : 0 ≤ |(1 / b) - (1 / a)| := abs_nonneg _
    linarith
  have hupper : 1 / b ≤ 1 / a + M := by
    -- Keep only the upper half of the symmetric reciprocal bound.
    have hpair := abs_le.mp hcomp
    linarith
  have hden_pos : 0 < 1 + M * a := by
    -- The denominator in the target factor is positive because `M ≥ 0` and `a > 0`.
    nlinarith
  have hrew : 1 / a + M = (1 + M * a) / a := by
    -- Put the reciprocal upper bound over the common denominator `a`.
    field_simp [ha.ne']
  have hrecip : 1 / b ≤ (1 + M * a) / a := by
    rwa [hrew] at hupper
  have hquot_pos : 0 < (1 + M * a) / a := div_pos hden_pos ha
  have hfinal : 1 / ((1 + M * a) / a) ≤ b :=
    (one_div_le hquot_pos hb).2 hrecip
  -- Inverting the quotient produces the textbook lower factor.
  simpa [one_div_div] using hfinal

/-- Helper for Theorem 5.1.5: the same reciprocal-comparison estimate, together with the
admissibility inequality `a < 1 / M`, rearranges to the standard upper transport factor. -/
private lemma localNorm_upper_bound_of_reciprocal_comparison
    {a b M : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hcomp : |(1 / b) - (1 / a)| ≤ M)
    (haM : a < 1 / M) (hM : 0 < M) :
    b ≤ a / (1 - M * a) := by
  have hlower : 1 / a - M ≤ 1 / b := by
    -- Keep the lower half of the symmetric reciprocal bound.
    have hpair := abs_le.mp hcomp
    linarith
  have hden_pos : 0 < 1 - M * a := by
    -- The admissibility hypothesis is exactly the positivity of the target denominator.
    have hMa_lt_one : M * a < 1 := by
      simpa [mul_comm] using (lt_div_iff₀ hM).1 haM
    linarith
  have hrew : 1 / a - M = (1 - M * a) / a := by
    -- Put the reciprocal lower bound over the common denominator `a`.
    field_simp [ha.ne']
  have hrecip : (1 - M * a) / a ≤ 1 / b := by
    rwa [hrew] at hlower
  have htmp : b * ((1 - M * a) / a) ≤ 1 := by
    -- Multiply by the positive endpoint norm `b`.
    simpa [hb.ne', mul_comm, mul_left_comm, mul_assoc] using
      (mul_le_mul_of_nonneg_left hrecip (le_of_lt hb))
  have htmp' : (b * (1 - M * a)) / a ≤ 1 := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using htmp
  have hmul : b * (1 - M * a) ≤ a := by
    -- Clear the positive denominator `a`.
    simpa using (div_le_iff₀ ha).1 htmp'
  -- Rewrite back to the target upper factor.
  exact (le_div_iff₀ hden_pos).2 <| by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul

/-- Helper for Theorem 5.1.5: shifting the base point of a directional slice rewrites its second
iterated derivative as the Hessian quadratic form at the shifted point. -/
private lemma directionalSlice_iteratedDerivTwo_eq_hessianQuadraticAtShift
    {g : E → ℝ} {x h : E} {t : ℝ}
    (hcontAt : ContDiffAt ℝ 3 g (x + t • h)) :
    iteratedDeriv 2 (directionalSlice g x h) t =
      inner ℝ h (hessian g (x + t • h) h) := by
  -- Translate the slice to the origin so that the chapter's directional-derivative owner
  -- applies at the shifted base point.
  have hshift :
      (fun z : ℝ ↦ directionalSlice g x h (t + z)) =
        directionalSlice g (x + t • h) h := by
    funext z
    simp [directionalSlice, add_smul, add_assoc]
  calc
    iteratedDeriv 2 (directionalSlice g x h) t
        = iteratedDeriv 2 (fun z : ℝ ↦ directionalSlice g x h (t + z)) 0 := by
            simpa using congrArg (fun k : ℝ → ℝ ↦ k 0)
              (iteratedDeriv_comp_const_add 2 (directionalSlice g x h) t).symm
    _ = secondDirectionalDerivative g (x + t • h) h := by
          rw [hshift, secondDirectionalDerivative]
    _ = inner ℝ h (hessian g (x + t • h) h) := by
          exact secondDirectionalDerivative_eq_hessian_quadratic_form
            (hcontAt.of_le (by norm_num))

/-- Helper for Theorem 5.1.5: if the base local norm of the segment displacement vanishes at
`x`, then it also vanishes at every shifted point of the admissible segment. -/
private lemma segmentDisplacementLocalNorm_eq_zero_of_zeroBase
    (hself : IsSelfConcordantOnWith (dom f) (Mf : NNReal) (withTopRealPart f))
    (hx : x ∈ dom f) {y : E} {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hzt : x + t • (y - x) ∈ dom f)
    (ha0 : ‖y - x‖[withTopRealPart f; x] = 0) :
    ‖y - x‖[withTopRealPart f; x + t • (y - x)] = 0 := by
  rcases eq_or_lt_of_le ht.1 with rfl | ht_pos
  · -- At `t = 0`, the shifted point is just `x`, so the claim is the base assumption.
    simpa using ha0
  have hshift_nonneg :
      0 ≤ ‖y - x‖[withTopRealPart f; x + t • (y - x)] :=
    hessianLocalNorm_nonneg (withTopRealPart f) (x + t • (y - x)) (y - x)
  rcases eq_or_lt_of_le hshift_nonneg with hshift_zero | hshift_pos
  · exact hshift_zero.symm
  · -- Route correction: prove the reverse-direction local norm is positive at the shifted point,
    -- then use the reciprocal comparison core to transport that positivity back to `x`.
    have hsub_shift : x - (x + t • (y - x)) = (-t) • (y - x) := by
      calc
        x - (x + t • (y - x)) = -(t • (y - x)) := by abel
        _ = (-t) • (y - x) := by simp
    have hreverse_pos :
        0 < ‖x - (x + t • (y - x))‖[withTopRealPart f; x + t • (y - x)] := by
      rw [hsub_shift, hessianLocalNorm_smul_eq_abs hself hzt (-t)]
      simpa [abs_neg, abs_of_pos ht_pos] using mul_pos ht_pos hshift_pos
    rcases
        segmentReciprocalComparisonForDisplacement_core
          hself hzt hx hreverse_pos with
      ⟨hbase_reverse_pos, _⟩
    have hbase_pos : 0 < ‖y - x‖[withTopRealPart f; x] := by
      rw [hsub_shift, hessianLocalNorm_smul_eq_abs hself hx (-t), ha0] at hbase_reverse_pos
      simpa [abs_neg, abs_of_pos ht_pos] using hbase_reverse_pos
    have hbase_zero_not_pos : ¬ 0 < ‖y - x‖[withTopRealPart f; x] := by
      simpa [ha0]
    exact False.elim (hbase_zero_not_pos hbase_pos)

/-- Helper for Theorem 5.1.5: the displacement local norm at a shifted point is controlled by the
standard reciprocal transport factor measured at the base point. -/
private lemma segmentDisplacementLocalNorm_upperAtShift
    (hself : IsSelfConcordantOnWith (dom f) (Mf : NNReal) (withTopRealPart f))
    (hx : x ∈ dom f) {y : E} {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hzt : x + t • (y - x) ∈ dom f)
    (ha : ‖y - x‖[withTopRealPart f; x] < 1 / (Mf : ℝ)) :
    ‖y - x‖[withTopRealPart f; x + t • (y - x)] ≤
      ‖y - x‖[withTopRealPart f; x] /
        (1 - (Mf : ℝ) * ‖y - x‖[withTopRealPart f; x] * t) := by
  rcases eq_or_lt_of_le ht.1 with rfl | ht_pos
  · -- At the base point there is no transport; the denominator collapses to `1`.
    simp
  let z : E := x + t • (y - x)
  let a : ℝ := ‖y - x‖[withTopRealPart f; x]
  let b : ℝ := ‖y - x‖[withTopRealPart f; z]
  have ha_nonneg : 0 ≤ a := by
    simpa [a] using hessianLocalNorm_nonneg (withTopRealPart f) x (y - x)
  rcases lt_or_eq_of_le ha_nonneg with ha_pos | ha_zero
  · -- Apply the reciprocal comparison core to the shorter segment ending at `z`.
    have hzx_pos : 0 < ‖z - x‖[withTopRealPart f; x] := by
      have hsub : z - x = t • (y - x) := by
        dsimp [z]
        abel
      rw [hsub, hessianLocalNorm_smul_eq_abs hself hx t]
      simpa [a, abs_of_pos ht_pos] using mul_pos ht_pos ha_pos
    rcases
        segmentReciprocalComparisonForDisplacement_core
          hself hx hzt hzx_pos with
      ⟨hzz_pos, hcomp⟩
    have hzx_lt : ‖z - x‖[withTopRealPart f; x] < 1 / (Mf : ℝ) := by
      have hsub : z - x = t • (y - x) := by
        dsimp [z]
        abel
      rw [hsub, hessianLocalNorm_smul_eq_abs hself hx t]
      have : t * a < 1 / (Mf : ℝ) := by
        nlinarith [ha, ht.2, (mf_pos : 0 < (Mf : ℝ))]
      simpa [a, abs_of_pos ht_pos] using this
    have hscaled :
        ‖z - x‖[withTopRealPart f; z] ≤
          ‖z - x‖[withTopRealPart f; x] /
            (1 - (Mf : ℝ) * ‖z - x‖[withTopRealPart f; x]) := by
      exact
        localNorm_upper_bound_of_reciprocal_comparison
          hzx_pos hzz_pos hcomp hzx_lt (mf_pos : 0 < (Mf : ℝ))
    have hsub_x : z - x = t • (y - x) := by
      dsimp [z]
      abel
    have hx_scale : ‖z - x‖[withTopRealPart f; x] = t * a := by
      rw [hsub_x, hessianLocalNorm_smul_eq_abs hself hx t]
      simp [a, abs_of_pos ht_pos]
    have hz_scale : ‖z - x‖[withTopRealPart f; z] = t * b := by
      rw [hsub_x, hessianLocalNorm_smul_eq_abs hself hzt t]
      simp [a, b, z, abs_of_pos ht_pos]
    have hscaled' :
        t * b ≤ (t * a) / (1 - (Mf : ℝ) * a * t) := by
      calc
        t * b = ‖z - x‖[withTopRealPart f; z] := hz_scale.symm
        _ ≤
            ‖z - x‖[withTopRealPart f; x] /
              (1 - (Mf : ℝ) * ‖z - x‖[withTopRealPart f; x]) := hscaled
        _ = (t * a) / (1 - (Mf : ℝ) * a * t) := by
              rw [hx_scale]
              simp [mul_left_comm, mul_comm]
    have hscaled'' :
        t * b ≤ t * (a / (1 - (Mf : ℝ) * a * t)) := by
      rw [mul_div_assoc] at hscaled'
      simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled'
    have hb_le :
        b ≤ a / (1 - (Mf : ℝ) * a * t) := by
      nlinarith [hscaled'', ht_pos]
    simpa [a, b, z] using hb_le
  · -- When the base local norm vanishes, the previous helper shows every shifted local norm
    -- vanishes as well, so the upper bound is immediate.
    have hb_zero : b = 0 := by
      simpa [a, b, z] using
        segmentDisplacementLocalNorm_eq_zero_of_zeroBase hself hx ht hzt
          (by simpa [a] using ha_zero.symm)
    simp [a, b, z, ha_zero.symm, hb_zero]

/-- Helper for Theorem 5.1.5: restricting the directional slice to the admissible segment turns
the second derivative into the transported reciprocal-square model. -/
private lemma segmentSlice_secondDeriv_le_transportModel
    (hself : IsSelfConcordantOnWith (dom f) (Mf : NNReal) (withTopRealPart f))
    (hx : x ∈ dom f) {y : E} {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hzt : x + t • (y - x) ∈ dom f)
    (ha : ‖y - x‖[withTopRealPart f; x] < 1 / (Mf : ℝ)) :
    iteratedDeriv 2 (directionalSlice (withTopRealPart f) x (y - x)) t ≤
      (‖y - x‖[withTopRealPart f; x] /
        (1 - (Mf : ℝ) * ‖y - x‖[withTopRealPart f; x] * t)) ^ (2 : ℕ) := by
  let d : E := y - x
  have hcontAt : ContDiffAt ℝ 3 (withTopRealPart f) (x + t • d) := by
    exact hself.contDiffOn.contDiffAt (hself.isOpen_domain.mem_nhds hzt)
  have hquad_nonneg :
      0 ≤ inner ℝ d (hessian (withTopRealPart f) (x + t • d) d) :=
    hself.hessian_posSemidef hzt d
  have hden_pos : 0 < 1 - (Mf : ℝ) * ‖d‖[withTopRealPart f; x] * t := by
    have hbase_lt_one : (Mf : ℝ) * ‖d‖[withTopRealPart f; x] < 1 := by
      simpa [mul_comm] using (lt_div_iff₀ (mf_pos : 0 < (Mf : ℝ))).1 ha
    have hbase_nonneg : 0 ≤ (Mf : ℝ) * ‖d‖[withTopRealPart f; x] := by
      exact mul_nonneg
        (le_of_lt (mf_pos : 0 < (Mf : ℝ)))
        (hessianLocalNorm_nonneg (withTopRealPart f) x d)
    have hscaled_le :
        (Mf : ℝ) * ‖d‖[withTopRealPart f; x] * t ≤
          (Mf : ℝ) * ‖d‖[withTopRealPart f; x] := by
      simpa [mul_assoc] using (mul_le_of_le_one_right hbase_nonneg ht.2)
    have hscaled_lt_one : (Mf : ℝ) * ‖d‖[withTopRealPart f; x] * t < 1 :=
      lt_of_le_of_lt hscaled_le hbase_lt_one
    linarith
  have hmodel_nonneg :
      0 ≤ ‖d‖[withTopRealPart f; x] /
        (1 - (Mf : ℝ) * ‖d‖[withTopRealPart f; x] * t) := by
    exact div_nonneg
      (hessianLocalNorm_nonneg (withTopRealPart f) x d)
      (le_of_lt hden_pos)
  have htransport :
      ‖d‖[withTopRealPart f; x + t • d] ≤
        ‖d‖[withTopRealPart f; x] /
          (1 - (Mf : ℝ) * ‖d‖[withTopRealPart f; x] * t) := by
    simpa [d] using segmentDisplacementLocalNorm_upperAtShift hself hx ht hzt ha
  have hsquare :
      ‖d‖[withTopRealPart f; x + t • d] ^ (2 : ℕ) ≤
        (‖d‖[withTopRealPart f; x] /
          (1 - (Mf : ℝ) * ‖d‖[withTopRealPart f; x] * t)) ^ (2 : ℕ) := by
    nlinarith [htransport, hessianLocalNorm_nonneg (withTopRealPart f) (x + t • d) d, hmodel_nonneg]
  have hnorm_sq :
      inner ℝ d (hessian (withTopRealPart f) (x + t • d) d) =
        ‖d‖[withTopRealPart f; x + t • d] ^ (2 : ℕ) := by
    symm
    rw [hessianLocalNorm_def]
    simpa [pow_two] using Real.sq_sqrt hquad_nonneg
  -- Rewrite the second slice derivative as the Hessian quadratic form, then compare its square
  -- root by the transported local norm bound.
  calc
    iteratedDeriv 2 (directionalSlice (withTopRealPart f) x (y - x)) t
        = inner ℝ d (hessian (withTopRealPart f) (x + t • d) d) := by
            simpa [d] using
              directionalSlice_iteratedDerivTwo_eq_hessianQuadraticAtShift hcontAt
    _ = ‖d‖[withTopRealPart f; x + t • d] ^ (2 : ℕ) := hnorm_sq
    _ ≤
        (‖d‖[withTopRealPart f; x] /
          (1 - (Mf : ℝ) * ‖d‖[withTopRealPart f; x] * t)) ^ (2 : ℕ) := hsquare
    _ =
        (‖y - x‖[withTopRealPart f; x] /
          (1 - (Mf : ℝ) * ‖y - x‖[withTopRealPart f; x] * t)) ^ (2 : ℕ) := by
            simp [d]

/-- Helper for Theorem 5.1.5: every shorter segment point lies on the segment from `x` to the
admissible endpoint `x + t • (y - x)`. -/
private lemma shiftedSegmentPoint_mem
    {x y : E} {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) t) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    x + s • (y - x) ∈ segment ℝ x (x + t • (y - x)) := by
  rcases eq_or_lt_of_le ht.1 with rfl | ht_pos
  · -- When `t = 0`, the prefix condition forces `s = 0`, so the point is the left endpoint.
    have hs_zero : s = 0 := le_antisymm hs.2 hs.1
    subst hs_zero
    simp
  rw [segment_eq_image_lineMap]
  refine ⟨s / t, ?_, ?_⟩
  · constructor
    · exact div_nonneg hs.1 (le_of_lt ht_pos)
    · have hs_le_t : s ≤ 1 * t := by simpa using hs.2
      simpa using (div_le_iff₀ ht_pos).2 hs_le_t
  · have hscalar : (s / t) * t = s := by
      field_simp [ht_pos.ne']
    -- Express the shorter point with parameter `s / t` on the segment from `x` to `x + t • (y-x)`.
    simp [AffineMap.lineMap_apply_module', smul_smul, hscalar, add_comm]

/-- Helper for Theorem 5.1.5: on any admissible prefix, the transported reciprocal-square model is
uniformly bounded by its endpoint value at `t = 1`. -/
private lemma segmentSlice_secondDeriv_le_uniformConst
    (hself : IsSelfConcordantOnWith (dom f) (Mf : NNReal) (withTopRealPart f))
    {x y : E} (hx : x ∈ dom f) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hzt : x + t • (y - x) ∈ dom f)
    (ha : ‖y - x‖[withTopRealPart f; x] < 1 / (Mf : ℝ)) :
    iteratedDeriv 2 (directionalSlice (withTopRealPart f) x (y - x)) t ≤
      (‖y - x‖[withTopRealPart f; x] /
        (1 - (Mf : ℝ) * ‖y - x‖[withTopRealPart f; x])) ^ (2 : ℕ) := by
  let a : ℝ := ‖y - x‖[withTopRealPart f; x]
  have hmodel := segmentSlice_secondDeriv_le_transportModel hself hx ht hzt ha
  have ha_nonneg : 0 ≤ a := by
    simpa [a] using hessianLocalNorm_nonneg (withTopRealPart f) x (y - x)
  have hMa_lt_one : (Mf : ℝ) * a < 1 := by
    simpa [a, mul_comm] using (lt_div_iff₀ (mf_pos : 0 < (Mf : ℝ))).1 ha
  have hMa_nonneg : 0 ≤ (Mf : ℝ) * a := by
    exact mul_nonneg (le_of_lt (mf_pos : 0 < (Mf : ℝ))) ha_nonneg
  have hscaled_le : (Mf : ℝ) * a * t ≤ (Mf : ℝ) * a := by
    simpa [mul_assoc] using (mul_le_of_le_one_right hMa_nonneg ht.2)
  have hden_t_pos : 0 < 1 - (Mf : ℝ) * a * t := by
    have hscaled_lt_one : (Mf : ℝ) * a * t < 1 := lt_of_le_of_lt hscaled_le hMa_lt_one
    linarith
  have hden_one_pos : 0 < 1 - (Mf : ℝ) * a := by
    linarith
  have hden_mono : 1 - (Mf : ℝ) * a ≤ 1 - (Mf : ℝ) * a * t := by
    linarith
  have hfrac_le :
      a / (1 - (Mf : ℝ) * a * t) ≤ a / (1 - (Mf : ℝ) * a) := by
    gcongr
  have hfrac_nonneg :
      0 ≤ a / (1 - (Mf : ℝ) * a * t) := by
    exact div_nonneg ha_nonneg (le_of_lt hden_t_pos)
  have hendpoint_nonneg :
      0 ≤ a / (1 - (Mf : ℝ) * a) := by
    exact div_nonneg ha_nonneg (le_of_lt hden_one_pos)
  have hsquare_le :
      (a / (1 - (Mf : ℝ) * a * t)) ^ (2 : ℕ) ≤
        (a / (1 - (Mf : ℝ) * a)) ^ (2 : ℕ) := by
    nlinarith [hfrac_le, hfrac_nonneg, hendpoint_nonneg]
  -- First freeze the transported model, then collapse it to the fixed endpoint denominator.
  exact hmodel.trans <| by simpa [a] using hsquare_le

/-- Helper for Theorem 5.1.5: if the endpoint `x + t • (y - x)` stays in the domain, then the
whole prefix segment has the same `C²` directional slice regularity. -/
private lemma directionalSlice_contDiffOn_prefixSegment
    (hself : IsSelfConcordantOnWith (dom f) (Mf : NNReal) (withTopRealPart f))
    {x y : E} (hx : x ∈ dom f) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hzt : x + t • (y - x) ∈ dom f) :
    ContDiffOn ℝ 2 (directionalSlice (withTopRealPart f) x (y - x)) (Set.Icc (0 : ℝ) t) := by
  let d : E := y - x
  have hline :
      Set.Icc (0 : ℝ) t ⊆ (fun s : ℝ ↦ x + s • d) ⁻¹' dom f := by
    intro s hs
    exact hself.convex_domain.segment_subset hx hzt <| by
      simpa [d] using shiftedSegmentPoint_mem hs ht
  have hAffine : ContDiffOn ℝ 2 (fun s : ℝ ↦ x + s • d) (Set.Icc (0 : ℝ) t) := by
    fun_prop
  have hMapsTo : Set.MapsTo (fun s : ℝ ↦ x + s • d) (Set.Icc (0 : ℝ) t) (dom f) := by
    intro s hs
    exact hline hs
  -- Compose the ambient `C³` regularity with the affine prefix parameterization.
  simpa [d, directionalSlice] using
    (hself.contDiffOn.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).comp hAffine hMapsTo

/-- Helper for Theorem 5.1.5: on a short interval starting at `0`, the degree-1 Taylor polynomial
is just the value at `0` plus the first derivative term. -/
private lemma taylorWithinEval_one_eq_atLeftEndpoint
    {ψ : ℝ → ℝ} {ε a : ℝ} (hε : 0 < ε) (hψ : ContDiffAt ℝ 1 ψ 0) :
    taylorWithinEval ψ 1 (Set.Icc (0 : ℝ) ε) 0 a = ψ 0 + a * deriv ψ 0 := by
  -- Expand the degree-1 Taylor polynomial and rewrite the endpoint coefficient to the ordinary
  -- derivative at `0`.
  rw [taylorWithinEval_succ, taylor_within_zero_eval]
  simp only [Nat.factorial_zero, Nat.cast_zero, Nat.cast_one, zero_add, inv_one, sub_zero, one_mul]
  rw [
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hε) hψ (by simp [hε.le]),
    iteratedDeriv_one
  ]
  ring

/-- Helper for Theorem 5.1.5: the directional slice stays uniformly bounded above along every
admissible prefix of the segment once the base local norm is below the reciprocal radius. -/
private lemma segmentSlice_value_upperBound_onAdmissiblePrefix
    (hself : IsSelfConcordantOnWith (dom f) (Mf : NNReal) (withTopRealPart f))
    {x y : E} (hx : x ∈ dom f)
    (ha : ‖y - x‖[withTopRealPart f; x] < 1 / (Mf : ℝ)) :
    ∃ β : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      x + t • (y - x) ∈ dom f →
        directionalSlice (withTopRealPart f) x (y - x) t ≤ β := by
  let d : E := y - x
  let φ : ℝ → ℝ := directionalSlice (withTopRealPart f) x d
  let a : ℝ := ‖d‖[withTopRealPart f; x]
  let K : ℝ := (a / (1 - (Mf : ℝ) * a)) ^ (2 : ℕ)
  have hK_nonneg : 0 ≤ K := by
    positivity
  have hφderiv0 : deriv φ 0 = lineDeriv ℝ (withTopRealPart f) x d := by
    simpa [φ, d] using
      (lineDeriv_eq_deriv_directionalSlice (withTopRealPart f) x d).symm
  have hφcontAt0 : ContDiffAt ℝ 1 φ 0 := by
    have hambient :
        ContDiffAt ℝ 1 (withTopRealPart f) x := by
      exact (hself.contDiffOn.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3)).contDiffAt
        (hself.isOpen_domain.mem_nhds hx)
    have hambient0 :
        ContDiffAt ℝ 1 (withTopRealPart f) (x + (0 : ℝ) • d) := by
      simpa using hambient
    have hAffine : ContDiffAt ℝ 1 (fun s : ℝ ↦ x + s • d) 0 := by
      fun_prop
    -- The slice inherits ordinary differentiability at the left endpoint from the ambient owner.
    simpa [φ, d, directionalSlice] using hambient0.comp 0 hAffine
  refine ⟨φ 0 + |deriv φ 0| + K / 2, ?_⟩
  intro t ht hzt
  rcases eq_or_lt_of_le ht.1 with rfl | ht0
  · -- At the left endpoint there is no remainder term; only the fixed linear and quadratic caps
    -- remain.
    have hKhalf_nonneg : 0 ≤ K / 2 := by positivity
    linarith [abs_nonneg (deriv φ 0)]
  · have hφcont : ContDiffOn ℝ 2 φ (Set.uIcc (0 : ℝ) t) := by
      rw [Set.uIcc_of_lt ht0]
      exact directionalSlice_contDiffOn_prefixSegment hself hx ht hzt
    obtain ⟨ξ, hξ, hTaylor⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv
        (show (0 : ℝ) ≠ t by exact ne_of_lt ht0) hφcont
    rw [Set.uIoo_of_lt ht0] at hξ
    have hξ_mem : ξ ∈ Set.Icc (0 : ℝ) t := ⟨le_of_lt hξ.1, le_of_lt hξ.2⟩
    have hξ_dom : x + ξ • d ∈ dom f := by
      exact hself.convex_domain.segment_subset hx hzt <| by
        simpa [d] using shiftedSegmentPoint_mem hξ_mem ht
    have hξ_unit : ξ ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hξ.1, hξ.2.le.trans ht.2⟩
    have hsecond_le : iteratedDeriv 2 φ ξ ≤ K := by
      simpa [φ, d, a, K] using
        segmentSlice_secondDeriv_le_uniformConst hself hx hξ_unit hξ_dom
          (by simpa [a, d] using ha)
    have hTaylor_eq :
        φ t = φ 0 + t * deriv φ 0 + iteratedDeriv 2 φ ξ * t ^ (2 : ℕ) / 2 := by
      rw [Set.uIcc_of_lt ht0] at hTaylor
      rw [taylorWithinEval_one_eq_atLeftEndpoint ht0 hφcontAt0] at hTaylor
      linarith
    have hlin_bound : t * deriv φ 0 ≤ |deriv φ 0| := by
      calc
        t * deriv φ 0 ≤ |t * deriv φ 0| := le_abs_self _
        _ = |t| * |deriv φ 0| := by rw [abs_mul]
        _ ≤ 1 * |deriv φ 0| := by
          gcongr
          simpa [abs_of_nonneg ht.1] using ht.2
        _ = |deriv φ 0| := by ring
    have hquad_bound : iteratedDeriv 2 φ ξ * t ^ (2 : ℕ) / 2 ≤ K / 2 := by
      have ht_sq_half_nonneg : 0 ≤ t ^ (2 : ℕ) / 2 := by
        positivity
      have hscaled :
          iteratedDeriv 2 φ ξ * (t ^ (2 : ℕ) / 2) ≤ K * (t ^ (2 : ℕ) / 2) := by
        exact mul_le_mul_of_nonneg_right hsecond_le ht_sq_half_nonneg
      have ht_sq_half_le : t ^ (2 : ℕ) / 2 ≤ 1 / 2 := by
        nlinarith [ht.1, ht.2]
      have hKscaled : K * (t ^ (2 : ℕ) / 2) ≤ K * (1 / 2) := by
        exact mul_le_mul_of_nonneg_left ht_sq_half_le hK_nonneg
      have hbound : iteratedDeriv 2 φ ξ * (t ^ (2 : ℕ) / 2) ≤ K * (1 / 2) :=
        le_trans hscaled hKscaled
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hbound
    -- Package the first-order Taylor term and the bounded quadratic remainder into one scalar.
    linarith

/-- Helper for Theorem 5.1.5: a uniform upper bound on the directional slice turns the
admissible-prefix set into a closed subset of the unit interval. -/
private lemma admissiblePrefix_isClosed_of_sliceUpperBound
    (hf_closedConvex : ClosedConvexFunction f) {x y : E} {β : ℝ}
    (hβ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      x + t • (y - x) ∈ dom f →
        directionalSlice (withTopRealPart f) x (y - x) t ≤ β) :
    IsClosed {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ x + t • (y - x) ∈ dom f} := by
  let z : ℝ → E := fun t ↦ x + t • (y - x)
  let γ : ℝ → E × ℝ := fun t ↦ (z t, β)
  have hE_closed : IsClosed (constrainedEpigraph (dom f) f) := hf_closedConvex.2.1
  have hγ_cont : Continuous γ := by
    -- The affine segment map is continuous.
    continuity
  have hset :
      {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ x + t • (y - x) ∈ dom f} =
        Set.Icc (0 : ℝ) 1 ∩ γ ⁻¹' constrainedEpigraph (dom f) f := by
    ext t
    constructor
    · rintro ⟨ht, htdom⟩
      refine ⟨ht, ?_⟩
      refine mem_constrainedEpigraph_iff.2 ⟨htdom, ?_⟩
      exact (withTopRealPart_le_iff htdom).1 (hβ t ht htdom)
    · intro ht
      refine ⟨ht.1, ?_⟩
      exact (mem_constrainedEpigraph_iff.mp ht.2).1
  -- Rewrite the admissible-prefix set as an interval intersection with a closed sublevel preimage.
  rw [hset]
  exact isClosed_Icc.inter (hE_closed.preimage hγ_cont)

/-- Helper for Theorem 5.1.5: every point of the reciprocal-radius open Dikin ellipsoid around a
point of the effective domain of a closed self-concordant objective remains in the effective
domain. This is the source-faithful extended-value backend for the public Dikin-domain inclusion.
-/
theorem openDikinEllipsoid_inv_constant_subset_effectiveDomain
    (hf_closedConvex : ClosedConvexFunction f)
    (hself : IsSelfConcordantOnWith (dom f) (Mf : NNReal) (withTopRealPart f))
    {x y : E} (hx : x ∈ dom f)
    (hxy : y ∈ W⁰[withTopRealPart f; x](1 / (Mf : ℝ))) :
    y ∈ dom f := by
  let d : E := y - x
  let z : ℝ → E := fun t ↦ x + t • d
  have ha : ‖d‖[withTopRealPart f; x] < 1 / (Mf : ℝ) := by
    -- Unpack the Dikin-ball hypothesis once and freeze the base local radius.
    simpa [d] using exactLocalNorm_lt_invConstant hxy
  rcases
      segmentSlice_value_upperBound_onAdmissiblePrefix
        hself hx (by simpa [d] using ha) with
    ⟨β, hβ⟩
  let A : Set (Set.Icc (0 : ℝ) 1) := {t | z t.1 ∈ dom f}
  have hA_open : IsOpen A := by
    -- Pull the open domain back along the affine segment map and then restrict to the interval.
    have hz_cont : Continuous z := by
      continuity
    let U : Set ℝ := {t : ℝ | z t ∈ dom f}
    have hU_open : IsOpen U := hself.isOpen_domain.preimage hz_cont
    have hA_eq : A = Subtype.val ⁻¹' U := by
      ext t
      rfl
    rw [hA_eq]
    exact hU_open.preimage continuous_subtype_val
  have hA_closed : IsClosed A := by
    -- The bounded-slice helper turns the admissible-prefix set into a closed interval slice.
    have hclosed :
        IsClosed {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ z t ∈ dom f} := by
      simpa [z, d] using
        admissiblePrefix_isClosed_of_sliceUpperBound
          hf_closedConvex hβ
    have hA_eq :
        A = Subtype.val ⁻¹' {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ z t ∈ dom f} := by
      ext t
      constructor
      · intro ht
        exact ⟨t.2, ht⟩
      · intro ht
        exact ht.2
    rw [hA_eq]
    exact hclosed.preimage continuous_subtype_val
  have hA_nonempty : A.Nonempty := by
    -- The left endpoint belongs to the domain by hypothesis.
    refine ⟨⟨0, by simp⟩, ?_⟩
    simpa [A, z, d] using hx
  have hA_eq_univ : A = Set.univ := by
    -- The closed and open admissible-prefix set contains `0`, so preconnectedness forces it to be
    -- the whole interval.
    letI : PreconnectedSpace (Set.Icc (0 : ℝ) 1) :=
      Subtype.preconnectedSpace isPreconnected_Icc
    exact IsClopen.eq_univ ⟨hA_closed, hA_open⟩ hA_nonempty
  have hA_one : z 1 ∈ dom f := by
    -- Evaluate the clopen conclusion at the right endpoint `1`.
    have hone_mem : (⟨1, by simp⟩ : Set.Icc (0 : ℝ) 1) ∈ A := by
      simp [hA_eq_univ]
    simpa [A] using hone_mem
  -- The segment endpoint at `t = 1` is exactly `y`.
  simpa [z, d] using hA_one

section SourceFaithfulPublicAPI

variable {domain : Set E} {f : E → ℝ}
variable {Mf : NNRealˣ}

/-
Theorem 5.1.5 is exposed in two layers. Clause `(1)` lives on the source-faithful extended-value
owner `f : E → WithTop ℝ`, with `ClosedConvexFunction f` carrying the effective-domain semantics
that rule out the false open-domain counterexamples for bare seminorm Dikin balls. Clauses `(2)`
and `(3)` stay on the real-valued owner `IsSelfConcordantOnWith domain (Mf : NNReal) f`; the
real-valued positive-definite-Hessian form of clause `(1)` is kept below only as a compatibility
wrapper for existing downstream imports.
-/
/-- Helper for Theorem 5.1.5: self-concordance on an open domain only depends on the restriction
of the ambient real-valued function to that domain. -/
private theorem selfConcordantOnWith_congrEqOnLocal
    {domain : Set E} {Mf : NNReal} {g₁ g₂ : E → ℝ}
    (h : IsSelfConcordantOnWith domain Mf g₁) (hEq : Set.EqOn g₁ g₂ domain) :
    IsSelfConcordantOnWith domain Mf g₂ := by
  refine
    { isOpen_domain := h.isOpen_domain
      contDiffOn := (contDiffOn_congr fun x hx ↦ (hEq hx).symm).2 h.contDiffOn
      convexOn := h.convexOn.congr hEq
      third_deriv_bound := ?_ }
  intro x hx u
  -- Upgrade equality on the open domain to neighborhood equality at the evaluation point.
  have hEqAt : g₂ =ᶠ[nhds x] g₁ := by
    refine Filter.mem_of_superset (h.isOpen_domain.mem_nhds hx) ?_
    intro z hz
    exact (hEq hz).symm
  have hG₁ContDiffAt : ContDiffAt ℝ 3 g₁ x :=
    h.contDiffOn.contDiffAt (h.isOpen_domain.mem_nhds hx)
  have hG₂ContDiffAt : ContDiffAt ℝ 3 g₂ x :=
    hG₁ContDiffAt.congr_of_eventuallyEq hEqAt
  -- Transport both the third derivative and the Hessian local norm through that neighborhood
  -- equality before reusing the original self-concordance bound.
  have hthird :
      thirdDirectionalDerivative g₂ x u = thirdDirectionalDerivative g₁ x u := by
    have hiter : iteratedFDeriv ℝ 3 g₂ x = iteratedFDeriv ℝ 3 g₁ x :=
      (Filter.EventuallyEq.iteratedFDeriv ℝ hEqAt 3).eq_of_nhds
    simpa [thirdDirectionalDerivative_eq_iteratedFDeriv hG₂ContDiffAt,
      thirdDirectionalDerivative_eq_iteratedFDeriv hG₁ContDiffAt] using
      congrArg (fun A ↦ A fun _ ↦ u) hiter
  have hhess : hessian g₂ x = hessian g₁ x := by
    simpa [hessian] using (hEqAt.gradient.fderiv_eq (𝕜 := ℝ))
  have hnorm : hessianLocalNorm g₂ x u = hessianLocalNorm g₁ x u := by
    simp [hessianLocalNorm_def, hhess]
  calc
    |thirdDirectionalDerivative g₂ x u| = |thirdDirectionalDerivative g₁ x u| := by
      rw [hthird]
    _ ≤ 2 * (Mf : ℝ) * hessianLocalNorm g₁ x u ^ (3 : ℕ) := h.third_deriv_bound hx u
    _ = 2 * (Mf : ℝ) * hessianLocalNorm g₂ x u ^ (3 : ℕ) := by
      rw [hnorm]

/-- Helper for Theorem 5.1.5: if two real-valued objectives agree on the open domain, then the
open Dikin ellipsoid at a base point inside that domain is the same for both objectives. -/
private theorem mem_openDikinEllipsoid_iff_of_eqOn_openDomain
    {domain : Set E} {Mf : NNReal} {g₁ g₂ : E → ℝ}
    (hself : IsSelfConcordantOnWith domain Mf g₁)
    (hEq : Set.EqOn g₁ g₂ domain)
    {x y : E} (hx : x ∈ domain) {r : ℝ} :
    y ∈ W⁰[g₁; x](r) ↔ y ∈ W⁰[g₂; x](r) := by
  -- Upgrade equality on the open domain to neighborhood equality at the common base point.
  have hEqAt : g₂ =ᶠ[nhds x] g₁ := by
    refine Filter.mem_of_superset (hself.isOpen_domain.mem_nhds hx) ?_
    intro z hz
    exact (hEq hz).symm
  have hhess : hessian g₂ x = hessian g₁ x := by
    simpa [hessian] using (hEqAt.gradient.fderiv_eq (𝕜 := ℝ))
  have hnorm : ‖y - x‖[g₂; x] = ‖y - x‖[g₁; x] := by
    simp [hessianLocalNorm_def, hhess]
  -- Both Dikin conditions reduce to the same strict local-norm inequality at `x`.
  rw [mem_openDikinEllipsoid_iff, mem_openDikinEllipsoid_iff, hnorm]

/-- Helper for Theorem 5.1.5: the primal `+∞`-extension carries the same self-concordance data as
the original real-valued function on `domain = dom (fenchelPrimalExtension domain f)`. -/
private theorem primalExtensionSelfConcordant
    (hself : IsSelfConcordantOnWith domain (Mf : NNReal) f) :
    IsSelfConcordantOnWith (dom (fenchelPrimalExtension domain f)) (Mf : NNReal)
      (withTopRealPart (fenchelPrimalExtension domain f)) := by
  -- Route correction: transport self-concordance through equality on the open domain instead of
  -- rebuilding the extended-value regularity data from scratch.
  have hEq :
      Set.EqOn f (withTopRealPart (fenchelPrimalExtension domain f)) domain := by
    intro z hz
    symm
    simpa using
      withTopRealPart_fenchelPrimalExtension_apply_of_mem (Q := domain) (f := f) hz
  simpa [dom_fenchelPrimalExtension] using
    selfConcordantOnWith_congrEqOnLocal hself hEq

/-- Theorem 5.1.5 (1): every point of the reciprocal-radius open Dikin ellipsoid around a point
of `domain` remains in `domain`, provided the canonical `+∞`-extension is a closed convex
function. This is the public real-valued Chapter 5 surface corresponding to the source-faithful
effective-domain theorem above. -/
theorem openDikinEllipsoid_inv_constant_subset
    (hf_closedConvex : ClosedConvexFunction (fenchelPrimalExtension domain f))
    (hself : IsSelfConcordantOnWith domain (Mf : NNReal) f)
    {x y : E} (hx : x ∈ domain)
    (hxy : y ∈ W⁰[f; x](1 / (Mf : ℝ))) :
    y ∈ domain := by
  let F : E → WithTop ℝ := fenchelPrimalExtension domain f
  have hEq : Set.EqOn f (withTopRealPart F) domain := by
    intro z hz
    symm
    simpa [F] using
      withTopRealPart_fenchelPrimalExtension_apply_of_mem (Q := domain) (f := f) hz
  have hselfF :
      IsSelfConcordantOnWith (dom F) (Mf : NNReal) (withTopRealPart F) := by
    -- Transport the source self-concordance owner to the finite real part of the primal
    -- extension, whose effective domain is exactly `domain`.
    simpa [F] using primalExtensionSelfConcordant (domain := domain) (f := f) (Mf := Mf) hself
  have hxyF : y ∈ W⁰[withTopRealPart F; x](1 / (Mf : ℝ)) := by
    -- Rewrite the Dikin-ball hypothesis through the local norm equality at the base point `x`.
    exact
      (mem_openDikinEllipsoid_iff_of_eqOn_openDomain
        (domain := domain) (Mf := (Mf : NNReal)) (g₁ := f) (g₂ := withTopRealPart F)
        hself hEq hx).1 hxy
  -- Apply the extended-value domain theorem and then rewrite its effective-domain conclusion.
  simpa [F, dom_fenchelPrimalExtension] using
    openDikinEllipsoid_inv_constant_subset_effectiveDomain
      (f := F) (Mf := Mf) hf_closedConvex hselfF
      (x := x) (y := y) (by simpa [F, dom_fenchelPrimalExtension] using hx) hxyF

/-- Theorem 5.1.5 (2): for points `x, y ∈ dom`, the endpoint local norm of the displacement is
bounded below by the standard transport factor `‖y - x‖_x / (1 + M_f ‖y - x‖_x)`. -/
theorem displacement_localNorm_lower_bound
    (hself : IsSelfConcordantOnWith domain (Mf : NNReal) f)
    {x y : E} (hx : x ∈ domain) (hy : y ∈ domain) :
    ‖y - x‖[f; y] ≥
      ‖y - x‖[f; x] /
        (1 + (Mf : ℝ) * ‖y - x‖[f; x]) := by
  let a : ℝ := ‖y - x‖[f; x]
  have ha_nonneg : 0 ≤ a := by
    simpa [a] using hessianLocalNorm_nonneg f x (y - x)
  rcases lt_or_eq_of_le ha_nonneg with ha_pos | ha0
  · -- In the positive case, apply the reciprocal comparison core and rearrange the scalar bound.
    rcases
        segmentReciprocalComparisonForDisplacement_core hself hx hy
          (by simpa [a] using ha_pos) with
      ⟨hb_pos, hcomp⟩
    simpa [a] using
      localNorm_lower_bound_of_reciprocal_comparison ha_pos hb_pos hcomp
  · -- If the base local norm vanishes, the claimed lower bound is just nonnegativity at `y`.
    have hx_zero : ‖y - x‖[f; x] = 0 := by
      simpa [a] using ha0.symm
    have hy_nonneg : 0 ≤ ‖y - x‖[f; y] :=
      hessianLocalNorm_nonneg f y (y - x)
    simpa [hx_zero] using hy_nonneg

/-- Theorem 5.1.5 (3): if `x, y ∈ dom` and `‖y - x‖_x < 1 / M_f`, then the terminal local norm
satisfies the standard upper transport factor
`‖y - x‖_y ≤ ‖y - x‖_x / (1 - M_f ‖y - x‖_x)`. -/
theorem displacement_localNorm_upper_bound
    (hself : IsSelfConcordantOnWith domain (Mf : NNReal) f) {x y : E}
    (hx : x ∈ domain) (hy : y ∈ domain)
    (hxy : ‖y - x‖[f; x] < 1 / (Mf : ℝ)) :
    ‖y - x‖[f; y] ≤
      ‖y - x‖[f; x] /
        (1 - (Mf : ℝ) * ‖y - x‖[f; x]) := by
  let a : ℝ := ‖y - x‖[f; x]
  have ha_nonneg : 0 ≤ a := by
    simpa [a] using hessianLocalNorm_nonneg f x (y - x)
  rcases lt_or_eq_of_le ha_nonneg with ha_pos | ha0
  · -- With positive endpoint norms, the reciprocal comparison rearranges to the upper factor.
    rcases
        segmentReciprocalComparisonForDisplacement_core hself hx hy
          (by simpa [a] using ha_pos) with
      ⟨hb_pos, hcomp⟩
    simpa [a] using
      localNorm_upper_bound_of_reciprocal_comparison ha_pos hb_pos hcomp
        (by simpa [a] using hxy) (mf_pos : 0 < (Mf : ℝ))
  · -- If the base local norm vanishes, positivity at `y` would force positivity back at `x`.
    have hx_zero : ‖y - x‖[f; x] = 0 := by
      simpa [a] using ha0.symm
    have hy_nonneg : 0 ≤ ‖y - x‖[f; y] :=
      hessianLocalNorm_nonneg f y (y - x)
    have hy_not_pos : ¬ 0 < ‖y - x‖[f; y] := by
      intro hy_pos
      have hswap_pos : 0 < ‖x - y‖[f; y] := by
        have hsub : x - y = -(y - x) := by abel
        rw [hsub, hessianLocalNorm_neg]
        exact hy_pos
      rcases
          segmentReciprocalComparisonForDisplacement_core hself hy hx hswap_pos with
        ⟨hx_pos, _⟩
      have : 0 < ‖y - x‖[f; x] := by
        have hsub : x - y = -(y - x) := by abel
        rw [hsub, hessianLocalNorm_neg] at hx_pos
        exact hx_pos
      simpa [hx_zero] using this
    have hy_zero : ‖y - x‖[f; y] = 0 := by
      linarith
    simp [hx_zero, hy_zero]

-- The theorem surface above is the canonical Chapter 5 owner API. The packaged
-- `UnconstrainedSelfConcordantMinimizationProblem` view below specializes clauses `(2)` and `(3)`
-- to the problem objective on its feasible set.

/-- Compatibility wrapper: apply Theorem 5.1.5 (2) to the problem objective on its feasible set.
-/
theorem problem_displacement_localNorm_lower_bound
    (problem : UnconstrainedSelfConcordantMinimizationProblem E)
    (hMf : problem.selfConcordanceConstant ≠ 0)
    {x y : E} (hx : x ∈ problem.feasibleSet) (hy : y ∈ problem.feasibleSet) :
    let Mf : NNRealˣ := Units.mk0 problem.selfConcordanceConstant hMf
    ‖y - x‖[problem.objective; y] ≥
      ‖y - x‖[problem.objective; x] /
        (1 + (Mf : ℝ) * ‖y - x‖[problem.objective; x]) := by
  -- Package the problem constant as a positive unit and specialize the owner theorem.
  dsimp
  let Mf : NNRealˣ := Units.mk0 problem.selfConcordanceConstant hMf
  have hself :
      IsSelfConcordantOnWith problem.feasibleSet (Mf : NNReal) problem.objective := by
    simpa [Mf] using problem.toIsSelfConcordantOnWith
  simpa [Mf] using
    displacement_localNorm_lower_bound hself hx hy

/-- Compatibility wrapper: apply Theorem 5.1.5 (3) to the problem objective on its feasible set.
-/
theorem problem_displacement_localNorm_upper_bound
    (problem : UnconstrainedSelfConcordantMinimizationProblem E)
    (hMf : problem.selfConcordanceConstant ≠ 0)
    {x y : E} (hx : x ∈ problem.feasibleSet) (hy : y ∈ problem.feasibleSet) :
    let Mf : NNRealˣ := Units.mk0 problem.selfConcordanceConstant hMf
    ‖y - x‖[problem.objective; x] < 1 / (Mf : ℝ) →
      ‖y - x‖[problem.objective; y] ≤
        ‖y - x‖[problem.objective; x] /
          (1 - (Mf : ℝ) * ‖y - x‖[problem.objective; x]) := by
  -- Package the problem constant as a positive unit and specialize the owner theorem.
  dsimp
  let Mf : NNRealˣ := Units.mk0 problem.selfConcordanceConstant hMf
  intro hxy
  have hself :
      IsSelfConcordantOnWith problem.feasibleSet (Mf : NNReal) problem.objective := by
    simpa [Mf] using problem.toIsSelfConcordantOnWith
  simpa [Mf] using
    displacement_localNorm_upper_bound hself hx hy hxy

end SourceFaithfulPublicAPI

end IsSelfConcordantOnWith

end
