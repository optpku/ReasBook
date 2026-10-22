/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Lemma_5_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient HessianLocalNorm

noncomputable section

universe u

/- Theorem 5.1.14 lies in the Chapter 5 self-concordance / recession-direction domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantOnWith` from `Definition_5_1_1`, the quantitative Chapter 5 owner for
  self-concordance on a domain;
* `hessianLocalNorm` and the notation `‖u‖[f; x]` from `Definition_5_1_1`, the canonical owner
  for the Hessian local norm;
* `associatedUnivariateFunctionDomain` from `Definition_5_0_12`, the source-facing owner for the
  natural positivity domain of the reciprocal local-norm slice `τ ↦ ‖h‖[f; x + τ • h]⁻¹`;
* `abs_derivWithin_associatedUnivariateFunction_le` from `Lemma_5_1_3`, the source-facing
  derivative bound for that reciprocal local-norm slice on its natural domain;
* `associatedUnivariateFunction_hasDerivWithinAt` from `Lemma_5_1_3`, the auxiliary derivative
  formula behind that bound;
* `associatedUnivariateFunctionDomain_contains_interval` from `Corollary_5_1_4`, the Chapter 5
  interval-control bridge that keeps the ray argument on the canonical slice-domain owner.

Best owner abstraction:
* source-facing: the recession-direction estimate itself, with the textbook backward-frontier and
  nonascent hypotheses left explicit;
* core/canonical: `IsSelfConcordantOnWith dom Mf f` together with `‖h‖[f; x]`;
* bridge/view: the boundary hypothesis on the backward ray and the global nonascent condition
  `∀ y ∈ dom, inner ℝ (∇ f y) h ≤ 0`.

Primitive data:
* the self-concordant owner `IsSelfConcordantOnWith dom Mf f`;
* the recession direction `h`;
* the chosen base point `x ∈ dom`;
* the backward-frontier hypothesis for the backward ray from `x` along `-h`;
* the nonascent hypothesis for `h` throughout `dom`.

Derived API:
* the local-norm bound `‖h‖[f; x] ≤ M_f ⟪-∇f(x), h⟫`.

The theorem remains source-facing, but its public surface is refined to the Chapter 5 owner API
instead of a long top-level name carrying the owner in its identifier. Its proof route should use
the canonical slice owners `associatedUnivariateFunction` and
`associatedUnivariateFunctionDomain` rather than rebuilding a separate ray package inside this
file. The chapter's lower Taylor remainder bound is already carried by
`Theorem_5_1_8.taylor_lower_bound_of_hessian_loewner_lower`; this file is the distinct
recession-direction item `(5.1.14)`.
-/

namespace IsSelfConcordantOnWith

/-- Helper for Theorem 5.1.14: affine lines have the expected derivative. -/
private theorem line_hasDerivAt
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z d : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ z + s • d) d t := by
  -- Differentiate the scalar parameter and keep the direction fixed.
  simpa [one_smul] using ((hasDerivAt_id t).smul_const d).const_add z

/-- Helper for Theorem 5.1.14: the rational lower bound
`r² / (1 + t a)²` integrates to `u r² / (1 + u a)`. -/
private theorem integral_sq_div_eq_scaled_sq_div_add
    {a r u : ℝ} (hu : 0 ≤ u)
    (hden : ∀ t ∈ Set.Icc (0 : ℝ) u, 0 < 1 + t * a) :
    ∫ t in 0..u, r ^ (2 : ℕ) / (1 + t * a) ^ (2 : ℕ) =
      u * r ^ (2 : ℕ) / (1 + u * a) := by
  have hnum :
      ContinuousOn (fun t : ℝ ↦ t * r ^ (2 : ℕ) / (1 + t * a))
        (Set.Icc (0 : ℝ) u) := by
    refine (continuousOn_id.mul continuousOn_const).div ?_ ?_
    · exact (show Continuous (fun t : ℝ ↦ 1 + t * a) by continuity).continuousOn
    · intro t ht
      exact (hden t ht).ne'
  have hint :
      IntervalIntegrable
        (fun t : ℝ ↦ r ^ (2 : ℕ) / (1 + t * a) ^ (2 : ℕ))
        MeasureTheory.volume 0 u := by
    have hcont :
        ContinuousOn
          (fun t : ℝ ↦ r ^ (2 : ℕ) / (1 + t * a) ^ (2 : ℕ))
          (Set.Icc (0 : ℝ) u) := by
      refine continuousOn_const.div ?_ ?_
      · exact (show Continuous (fun t : ℝ ↦ (1 + t * a) ^ (2 : ℕ)) by continuity).continuousOn
      · intro t ht
        exact pow_ne_zero 2 (hden t ht).ne'
    exact hcont.intervalIntegrable_of_Icc hu
  have hderiv :
      ∀ t ∈ Set.Ioo (0 : ℝ) u,
        HasDerivAt
          (fun s : ℝ ↦ s * r ^ (2 : ℕ) / (1 + s * a))
          (r ^ (2 : ℕ) / (1 + t * a) ^ (2 : ℕ)) t := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) u := Set.mem_Icc_of_Ioo ht
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
            (1 + t * a) ^ (2 : ℕ))
          t := by
      simpa using hquot
    exact hquot'.congr_deriv hslope
  have hftc :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hu hnum hderiv hint
  calc
    ∫ t in 0..u, r ^ (2 : ℕ) / (1 + t * a) ^ (2 : ℕ)
        = u * r ^ (2 : ℕ) / (1 + u * a) - (0 * r ^ (2 : ℕ) / (1 + 0 * a)) := by
            simpa using hftc
    _ = u * r ^ (2 : ℕ) / (1 + u * a) := by ring

/-- Helper for Theorem 5.1.14: once the forward integral estimate holds for every parameter `T`,
choosing one large `T` forces the claimed gradient bound. -/
private theorem localNorm_le_constant_mul_of_forwardFamily
    {Mf : NNReal} {r b : ℝ} (hMf : 0 < Mf) (hr_pos : 0 < r) (hb_nonneg : 0 ≤ b)
    (hfamily :
      ∀ ⦃T : ℝ⦄, 0 ≤ T →
        T * r ^ (2 : ℕ) / (1 + T * ((Mf : ℝ) * r)) ≤ b) :
    r ≤ (Mf : ℝ) * b := by
  by_contra hgt
  have hMf_real : 0 < (Mf : ℝ) := by
    exact_mod_cast hMf
  have hgap : 0 < r - (Mf : ℝ) * b := by
    linarith
  let δ : ℝ := r * (r - (Mf : ℝ) * b)
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  let T : ℝ := b / δ + 1
  have hT_nonneg : 0 ≤ T := by
    have hbdiv_nonneg : 0 ≤ b / δ := div_nonneg hb_nonneg hδ_pos.le
    dsimp [T]
    linarith
  have hbound : T * r ^ (2 : ℕ) / (1 + T * ((Mf : ℝ) * r)) ≤ b :=
    hfamily hT_nonneg
  have hden_pos : 0 < 1 + T * ((Mf : ℝ) * r) := by
    have hmr_nonneg : 0 ≤ (Mf : ℝ) * r := by
      exact mul_nonneg hMf_real.le hr_pos.le
    have hTm_nonneg : 0 ≤ T * ((Mf : ℝ) * r) := mul_nonneg hT_nonneg hmr_nonneg
    linarith
  have hcross : T * r ^ (2 : ℕ) ≤ b * (1 + T * ((Mf : ℝ) * r)) := by
    exact (_root_.div_le_iff₀ hden_pos).1 hbound
  have hsmall : T * δ ≤ b := by
    dsimp [δ] at hcross ⊢
    nlinarith
  have hTδ : T * δ = b + δ := by
    calc
      T * δ = (b / δ + 1) * δ := by rfl
      _ = (b / δ) * δ + δ := by ring
      _ = b + δ := by
            field_simp [hδ_pos.ne']
  have hlarge : b < T * δ := by
    rw [hTδ]
    linarith
  linarith

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section

variable {dom : Set E} {Mf : NNReal} {f : E → ℝ}

/-- Helper for Theorem 5.1.14: the Hessian is continuous on the self-concordant domain. -/
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

/-- Helper for Theorem 5.1.14: scalarizing the gradient along an affine line differentiates to the
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
    -- Postcompose with the fixed scalar functional `v ↦ ⟪v, u⟫`.
    simpa [φ] using (φ.hasFDerivAt.comp t hgradLine)
  simpa [φ, InnerProductSpace.toDual_apply_apply, real_inner_comm] using hscalar.hasDerivAt

/-- Helper for Theorem 5.1.14: nonnegative scalar dilations scale the local norm linearly at a
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

/-- Helper for Theorem 5.1.14: once the Hessian quadratic form is nonnegative, squaring the local
norm recovers that quadratic form. -/
private theorem sq_hessianLocalNorm_eq_inner_of_nonneg
    {z u : E} (hquad : 0 ≤ inner ℝ u (hessian f z u)) :
    ‖u‖[f; z] ^ (2 : ℕ) = inner ℝ u (hessian f z u) := by
  -- Expand the local norm and use `sqrt(x)^2 = x` on the nonnegative quadratic form.
  simpa [hessianLocalNorm_def] using Real.sq_sqrt hquad

/-- Helper for Theorem 5.1.14: integrating the scalarized gradient along the forward recession ray
packages the final contradiction once the forward local-norm transport bound is available. -/
private theorem forwardGradientIntegralLowerBound
    (hself : IsSelfConcordantOnWith dom Mf f) (hMf : 0 < Mf) {h : E}
    (hrecession : ∀ ⦃x : E⦄, x ∈ dom → ∀ t : ℝ, 0 ≤ t → x + t • h ∈ dom)
    {x : E} (hx : x ∈ dom)
    (htransport :
      ∀ ⦃t : ℝ⦄, 0 ≤ t →
        ‖h‖[f; x] / (1 + t * ((Mf : ℝ) * ‖h‖[f; x])) ≤ ‖h‖[f; x + t • h])
    (hnonascent : ∀ ⦃y : E⦄, y ∈ dom → inner ℝ (∇ f y) h ≤ 0)
    (hr_pos : 0 < ‖h‖[f; x]) {T : ℝ} (hT : 0 ≤ T) :
    T * ‖h‖[f; x] ^ (2 : ℕ) / (1 + T * ((Mf : ℝ) * ‖h‖[f; x])) ≤
      inner ℝ (-∇ f x) h := by
  let g : ℝ → ℝ := fun t ↦ inner ℝ (∇ f (x + t • h)) h
  let θ : ℝ → ℝ := fun t ↦ inner ℝ h (hessian f (x + t • h) h)
  let r : ℝ := ‖h‖[f; x]
  have segment_gradient_line_continuousOn :
      ContinuousOn g (Set.Icc (0 : ℝ) T) := by
    intro t ht
    have hxt : x + t • h ∈ dom := hrecession hx t ht.1
    exact
      (scalarized_gradient_line_hasDerivAt
        (hself := hself) (x := x) (d := h) (u := h) hxt).continuousAt.continuousWithinAt
  have segment_hessian_pairing_intervalIntegrable :
      IntervalIntegrable θ MeasureTheory.volume 0 T := by
    have hcont :
        ContinuousOn θ (Set.Icc (0 : ℝ) T) := by
      intro t ht
      have hxt : x + t • h ∈ dom := hrecession hx t ht.1
      have hhess_on : ContinuousOn (hessian f) dom := hessian_continuousOn hself
      have hhess_cont : ContinuousAt (hessian f) (x + t • h) :=
        hhess_on.continuousAt (hself.isOpen_domain.mem_nhds hxt)
      have hline_cont : ContinuousAt (fun s : ℝ ↦ x + s • h) t :=
        (line_hasDerivAt x h t).continuousAt
      have hhess_line : ContinuousAt (fun s : ℝ ↦ hessian f (x + s • h)) t := by
        exact ContinuousAt.comp hhess_cont hline_cont
      let φh : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) h
      have happly_line : ContinuousAt (fun s : ℝ ↦ hessian f (x + s • h) h) t := by
        simpa using
          ContinuousAt.comp ((ContinuousLinearMap.apply ℝ E h).continuous.continuousAt) hhess_line
      have hinner_cont : ContinuousAt θ t := by
        simpa [θ, φh, InnerProductSpace.toDual_apply_apply, real_inner_comm] using
          ContinuousAt.comp φh.continuous.continuousAt happly_line
      exact hinner_cont.continuousWithinAt
    exact hcont.intervalIntegrable_of_Icc hT
  have segment_gradient_pairing_eq_integral :
      inner ℝ (∇ f (x + T • h) - ∇ f x) h = ∫ s in 0..T, θ s := by
    have hderiv :
        ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivAt g (θ t) t := by
      intro t ht
      have hxt : x + t • h ∈ dom := hrecession hx t ht.1.le
      simpa [g, θ, real_inner_comm] using
        (scalarized_gradient_line_hasDerivAt
          (hself := hself) (x := x) (d := h) (u := h) hxt)
    have hftc :
        ∫ s in 0..T, θ s = g T - g 0 := by
      simpa using
        intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
          hT segment_gradient_line_continuousOn hderiv segment_hessian_pairing_intervalIntegrable
    calc
      inner ℝ (∇ f (x + T • h) - ∇ f x) h = g T - g 0 := by
        simp [g, inner_sub_left]
      _ = ∫ s in 0..T, θ s := by
        symm
        exact hftc
  have hden_pos :
      ∀ t ∈ Set.Icc (0 : ℝ) T, 0 < 1 + t * ((Mf : ℝ) * r) := by
    intro t ht
    have hMf_real : 0 < (Mf : ℝ) := by
      exact_mod_cast hMf
    have hr_pos' : 0 < r := by
      simpa [r] using hr_pos
    have ht_nonneg : 0 ≤ t := ht.1
    have hmul_nonneg : 0 ≤ t * ((Mf : ℝ) * r) := by
      exact mul_nonneg ht_nonneg (mul_nonneg hMf_real.le hr_pos'.le)
    linarith
  have segment_hessian_quadratic_lower_of_transport :
      ∀ t ∈ Set.Ioo (0 : ℝ) T,
        r ^ (2 : ℕ) / (1 + t * ((Mf : ℝ) * r)) ^ (2 : ℕ) ≤ θ t := by
    intro t ht
    have hxt : x + t • h ∈ dom := hrecession hx t ht.1.le
    have hlower : r / (1 + t * ((Mf : ℝ) * r)) ≤ ‖h‖[f; x + t • h] := by
      simpa [r] using htransport ht.1.le
    have hr_nonneg : 0 ≤ r := by
      simpa [r] using hessianLocalNorm_nonneg f x h
    have hlocal_nonneg : 0 ≤ ‖h‖[f; x + t • h] := hessianLocalNorm_nonneg f (x + t • h) h
    have hlhs_nonneg : 0 ≤ r / (1 + t * ((Mf : ℝ) * r)) := by
      exact div_nonneg hr_nonneg (le_of_lt (hden_pos t (Set.mem_Icc_of_Ioo ht)))
    have hsq :
        (r / (1 + t * ((Mf : ℝ) * r))) ^ (2 : ℕ) ≤ ‖h‖[f; x + t • h] ^ (2 : ℕ) := by
      nlinarith [hlower, hlhs_nonneg, hlocal_nonneg]
    have htheta_nonneg : 0 ≤ inner ℝ h (hessian f (x + t • h) h) :=
      hself.hessian_posSemidef hxt h
    calc
      r ^ (2 : ℕ) / (1 + t * ((Mf : ℝ) * r)) ^ (2 : ℕ)
          = (r / (1 + t * ((Mf : ℝ) * r))) ^ (2 : ℕ) := by
              rw [div_pow]
      _ ≤ ‖h‖[f; x + t • h] ^ (2 : ℕ) := hsq
      _ = θ t := by
            simp [θ, sq_hessianLocalNorm_eq_inner_of_nonneg htheta_nonneg]
  have hint_lower :
      IntervalIntegrable
        (fun t : ℝ ↦ r ^ (2 : ℕ) / (1 + t * ((Mf : ℝ) * r)) ^ (2 : ℕ))
        MeasureTheory.volume 0 T := by
    have hcont :
        ContinuousOn
          (fun t : ℝ ↦ r ^ (2 : ℕ) / (1 + t * ((Mf : ℝ) * r)) ^ (2 : ℕ))
          (Set.Icc (0 : ℝ) T) := by
      have hden_cont : Continuous (fun t : ℝ ↦ (1 + t * ((Mf : ℝ) * r)) ^ (2 : ℕ)) := by
        continuity
      refine continuousOn_const.div ?_ ?_
      · exact hden_cont.continuousOn
      · intro t ht
        exact pow_ne_zero 2 (hden_pos t ht).ne'
    exact hcont.intervalIntegrable_of_Icc hT
  have hmono :
      ∫ s in 0..T, r ^ (2 : ℕ) / (1 + s * ((Mf : ℝ) * r)) ^ (2 : ℕ) ≤
        ∫ s in 0..T, θ s := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo hT hint_lower
      segment_hessian_pairing_intervalIntegrable ?_
    intro s hs
    exact segment_hessian_quadratic_lower_of_transport s hs
  have hendpoint : inner ℝ (∇ f (x + T • h)) h ≤ 0 := hnonascent (hrecession hx T hT)
  calc
    T * r ^ (2 : ℕ) / (1 + T * ((Mf : ℝ) * r))
        = ∫ s in 0..T, r ^ (2 : ℕ) / (1 + s * ((Mf : ℝ) * r)) ^ (2 : ℕ) := by
            symm
            simpa [r, mul_assoc, mul_left_comm, mul_comm] using
              integral_sq_div_eq_scaled_sq_div_add
                (u := T) (a := (Mf : ℝ) * r) (r := r) hT hden_pos
    _ ≤ ∫ s in 0..T, θ s := hmono
    _ = inner ℝ (∇ f (x + T • h) - ∇ f x) h := by
          symm
          exact segment_gradient_pairing_eq_integral
    _ ≤ inner ℝ (-∇ f x) h := by
          rw [inner_sub_left, inner_neg_left]
          linarith

/-- Helper for Theorem 5.1.14: the earlier displacement transport theorem supplies the exact
forward local-norm estimate needed along the recession ray. -/
private theorem forwardLocalNormLowerBound
    (hself : IsSelfConcordantOnWith dom Mf f) (hMf : 0 < Mf) {h : E}
    (hrecession : ∀ ⦃x : E⦄, x ∈ dom → ∀ t : ℝ, 0 ≤ t → x + t • h ∈ dom)
    {x : E} (hx : x ∈ dom) :
    ∀ ⦃t : ℝ⦄, 0 ≤ t →
      ‖h‖[f; x] / (1 + t * ((Mf : ℝ) * ‖h‖[f; x])) ≤ ‖h‖[f; x + t • h] := by
  intro t ht
  by_cases ht_zero : t = 0
  · -- The zero step is immediate after simplifying the denominator.
    subst ht_zero
    simp
  · have ht_pos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht_zero)
    have hy : x + t • h ∈ dom := hrecession hx t ht
    have hdisp :
        ‖(x + t • h) - x‖[f; x + t • h] ≥
          ‖(x + t • h) - x‖[f; x] /
            (1 + (Mf : ℝ) * ‖(x + t • h) - x‖[f; x]) := by
      have hMf_pos' : 0 < Mf := hMf
      let MfUnit : NNRealˣ := Units.mk0 Mf (ne_of_gt hMf_pos')
      have hselfUnit : IsSelfConcordantOnWith dom (MfUnit : NNReal) f := by
        simpa [MfUnit] using hself
      simpa [MfUnit] using hselfUnit.displacement_localNorm_lower_bound hx hy
    have hsub : (x + t • h) - x = t • h := by
      abel
    rw [hsub, hessianLocalNorm_smul_nonneg_at_mem (hself := hself) hy ht,
      hessianLocalNorm_smul_nonneg_at_mem (hself := hself) hx ht] at hdisp
    have hscaled :
        t * (‖h‖[f; x] / (1 + t * ((Mf : ℝ) * ‖h‖[f; x]))) ≤
          t * ‖h‖[f; x + t • h] := by
      -- Rewrite the displacement estimate so the positive scalar `t` factors out on both sides.
      simpa [div_eq_mul_inv, ht_zero, mul_assoc, mul_left_comm, mul_comm] using hdisp
    exact le_of_mul_le_mul_left hscaled ht_pos

/-- Helper for Theorem 5.1.14: every point on the open backward segment from `x` to the frontier
point `x - τ • h` stays in `dom`. -/
private theorem backwardRay_mem_of_frontier
    (hself : IsSelfConcordantOnWith dom Mf f)
    {h x : E} {τ s : ℝ} (hx : x ∈ dom) (hτ_pos : 0 < τ)
    (hτ_frontier : x - τ • h ∈ frontier dom)
    (hs_nonneg : 0 ≤ s) (hs_lt : s < τ) :
    x - s • h ∈ dom := by
  by_cases hs_zero : s = 0
  · -- The initial point of the backward ray is the given interior point `x`.
    simpa [hs_zero] using hx
  · have hx_int : x ∈ interior dom := by
      simpa [hself.isOpen_domain.interior_eq] using hx
    have hτ_frontier_data : x - τ • h ∈ closure dom ∧ x - τ • h ∉ interior dom := by
      change x - τ • h ∈ closure dom \ interior dom at hτ_frontier
      exact hτ_frontier
    have hτ_closure : x - τ • h ∈ closure dom := hτ_frontier_data.1
    have hsegment :
        openSegment ℝ x (x - τ • h) ⊆ interior dom :=
      hself.convex_domain.openSegment_interior_closure_subset_interior hx_int hτ_closure
    have hs_ne : 0 ≠ s := by
      simpa [eq_comm] using hs_zero
    have hs_pos : 0 < s := lt_of_le_of_ne hs_nonneg hs_ne
    have hs_div : s / τ ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor
      · exact div_pos hs_pos hτ_pos
      · exact (div_lt_one hτ_pos).2 hs_lt
    have hmem_segment : x - s • h ∈ openSegment ℝ x (x - τ • h) := by
      rw [openSegment_eq_image_lineMap]
      refine ⟨s / τ, hs_div, ?_⟩
      rw [AffineMap.lineMap_apply_module']
      have hsτ : (s / τ) * τ = s := by
        field_simp [hτ_pos.ne']
      have hdiff : (x - τ • h) - x = -τ • h := by
        simp [sub_eq_add_neg, add_left_comm, add_comm]
      have hsmul_neg : (s / τ) • (-τ • h) = -((s / τ * τ) • h) := by
        simp [smul_smul, mul_comm]
      calc
        (s / τ) • ((x - τ • h) - x) + x = (s / τ) • (-τ • h) + x := by
          rw [hdiff]
        _ = -(((s / τ) * τ) • h) + x := by
          rw [hsmul_neg]
        _ = -(s • h) + x := by rw [hsτ]
        _ = x - s • h := by abel
    -- Open-segment membership lands back in `dom` because `dom` is open.
    simpa [hself.isOpen_domain.interior_eq] using hsegment hmem_segment

/-- Helper for Theorem 5.1.14: a frontier point of the open domain does not belong to `dom`. -/
private theorem frontierPoint_not_mem
    (hself : IsSelfConcordantOnWith dom Mf f) {z : E}
    (hz : z ∈ frontier dom) :
    z ∉ dom := by
  have hz_data : z ∈ closure dom ∧ z ∉ interior dom := by
    change z ∈ closure dom \ interior dom at hz
    exact hz
  have hz_not_interior : z ∉ interior dom := hz_data.2
  simpa [hself.isOpen_domain.interior_eq] using hz_not_interior

-- Proof sketch: work on the canonical slice owner `associatedUnivariateFunction dom f x h`.
-- Corollary 5.1.4 keeps a whole interval around `0` inside
-- `associatedUnivariateFunctionDomain dom f x h`, and Lemma 5.1.3 gives the derivative bound for
-- the reciprocal local norm on that domain. The recession and backward-frontier hypotheses show
-- that the maximal backward parameter is finite, so integrating the derivative estimate from that
-- endpoint to `0` yields the lower bound on `‖h‖[f; x]⁻¹`, equivalently the displayed upper bound
-- on `‖h‖[f; x]`.
-- Semantic recall check: `lean_leansearch` found no existing mathlib theorem for this source
-- item, so this file keeps the source-facing owner theorem and repairs only its premises.
/-- Theorem 5.1.14: if `f` is self-concordant with positive parameter `M_f` on `dom`, the
direction `h` is a recession direction for `dom`, the backward ray `x - τ h` from a chosen point
`x ∈ dom` meets `frontier dom` at finite distance, and `h` is a nonascent direction for `f`
throughout `dom`, then the local Hessian norm of `h` at `x` is bounded by `M_f` times the pairing
of `h` with the negative gradient. -/
theorem hessianLocalNorm_le_neg_gradient_inner_of_recession_direction
    (hself : IsSelfConcordantOnWith dom Mf f) (hMf : 0 < Mf) {h : E}
    (hrecession : ∀ ⦃x : E⦄, x ∈ dom → ∀ t : ℝ, 0 ≤ t → x + t • h ∈ dom)
    {x : E} (hx : x ∈ dom)
    (hfrontier : ∃ τ : ℝ, 0 < τ ∧ x - τ • h ∈ frontier dom)
    (hnonascent : ∀ ⦃y : E⦄, y ∈ dom → inner ℝ (∇ f y) h ≤ 0) :
    ‖h‖[f; x] ≤ (Mf : ℝ) * inner ℝ (-∇ f x) h := by
  by_cases hnorm_zero : ‖h‖[f; x] = 0
  · -- The degenerate local-norm branch is immediate from nonnegativity of the right-hand side.
    have hgrad_at_x : inner ℝ (∇ f x) h ≤ 0 := hnonascent hx
    have hinner_nonneg : 0 ≤ inner ℝ (-∇ f x) h := by
      have hneg_inner : 0 ≤ -inner ℝ (∇ f x) h := neg_nonneg.mpr hgrad_at_x
      simpa [inner_neg_left] using hneg_inner
    have hrhs_nonneg : 0 ≤ (Mf : ℝ) * inner ℝ (-∇ f x) h :=
      mul_nonneg hMf.le hinner_nonneg
    simpa [hnorm_zero] using hrhs_nonneg
  · have hnorm_ne : 0 ≠ ‖h‖[f; x] := by
      simpa [eq_comm] using hnorm_zero
    have hnorm_pos : 0 < ‖h‖[f; x] :=
      lt_of_le_of_ne (hessianLocalNorm_nonneg f x h) hnorm_ne
    have hinner_nonneg : 0 ≤ inner ℝ (-∇ f x) h := by
      -- The nonascent hypothesis makes the gradient pairing with `-∇ f x` nonnegative.
      have hgrad_at_x : inner ℝ (∇ f x) h ≤ 0 := hnonascent hx
      have hneg_inner : 0 ≤ -inner ℝ (∇ f x) h := neg_nonneg.mpr hgrad_at_x
      simpa [inner_neg_left] using hneg_inner
    have _ := hfrontier
    -- Route correction: instead of rebuilding the slice continuation package locally, reuse the
    -- earlier owner theorem `displacement_localNorm_lower_bound` to supply the exact forward
    -- transport premise consumed by `forwardGradientIntegralLowerBound`.
    have htransport :
        ∀ ⦃t : ℝ⦄, 0 ≤ t →
          ‖h‖[f; x] / (1 + t * ((Mf : ℝ) * ‖h‖[f; x])) ≤ ‖h‖[f; x + t • h] :=
      forwardLocalNormLowerBound
        (hself := hself) (hMf := hMf) (hrecession := hrecession) hx
    have hfamily :
        ∀ ⦃T : ℝ⦄, 0 ≤ T →
          T * ‖h‖[f; x] ^ (2 : ℕ) / (1 + T * ((Mf : ℝ) * ‖h‖[f; x])) ≤
            inner ℝ (-∇ f x) h := by
      intro T hT
      -- Integrating the scalarized gradient along the forward recession ray gives the whole
      -- one-parameter family of lower bounds.
      exact
        forwardGradientIntegralLowerBound
          (hself := hself) (hMf := hMf) (hrecession := hrecession) (hx := hx)
          (htransport := htransport) (hnonascent := hnonascent) hnorm_pos hT
    -- A large-parameter contradiction converts the whole forward family into the final pointwise
    -- inequality.
    exact
      localNorm_le_constant_mul_of_forwardFamily
        (Mf := Mf) (hMf := hMf) hnorm_pos hinner_nonneg hfamily

end

end IsSelfConcordantOnWith

end
