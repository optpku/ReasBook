/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_4_2
import Mathlib.Analysis.InnerProductSpace.ProdL2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Topology
open scoped WithTopConvexAnalysis

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
/-- Helper for Theorem 3.1.15: an interior effective-domain point admits a closed ball still
contained in the interior of the effective domain. -/
lemma exists_closedBall_subset_interior_of_mem_interior
    {f : E → WithTop ℝ} {x0 : E} (hx0 : x0 ∈ interior (dom f)) :
    ∃ rho > 0, Metric.closedBall x0 rho ⊆ interior (dom f) := by
  -- Shrink the open interior neighborhood so the whole closed ball still stays inside it.
  rcases Metric.mem_nhds_iff.1 (isOpen_interior.mem_nhds hx0) with ⟨r, hr, hrsub⟩
  refine ⟨r / 2, half_pos hr, ?_⟩
  intro y hy
  exact hrsub (Metric.closedBall_subset_ball (half_lt_self hr) hy)

omit [InnerProductSpace ℝ E] in
/-- Helper for Theorem 3.1.15: the base epigraph point over a closed ball around `x0` is a
boundary point of that constrained epigraph. -/
lemma basepoint_mem_frontier_constrainedEpigraph_closedBall
    {f : E → WithTop ℝ} {x0 : E} {rho : ℝ} (hrho : 0 < rho)
    (hball : Metric.closedBall x0 rho ⊆ interior (dom f)) :
    (x0, withTopRealPart f x0) ∈
      frontier (constrainedEpigraph (Metric.closedBall x0 rho) f) := by
  have hx0_ball : x0 ∈ Metric.closedBall x0 rho := Metric.mem_closedBall_self hrho.le
  have hx0_dom : x0 ∈ dom f := interior_subset (hball hx0_ball)
  rw [frontier_eq_closure_inter_closure]
  constructor
  · -- The basepoint itself lies in the constrained epigraph, hence in its closure.
    exact subset_closure <| mem_constrainedEpigraph_iff.2
      ⟨hx0_ball, by
        simpa using le_of_eq (coe_withTopRealPart (f := f) hx0_dom).symm⟩
  · -- Lowering only the height coordinate leaves every neighborhood through the complement.
    refine Metric.mem_closure_iff.2 ?_
    intro ε hε
    refine ⟨(x0, withTopRealPart f x0 - ε / 2), ?_, ?_⟩
    · intro hmem
      rcases mem_constrainedEpigraph_iff.1 hmem with ⟨_, hle⟩
      have hlt : withTopRealPart f x0 - ε / 2 < withTopRealPart f x0 := by
        linarith
      rw [← coe_withTopRealPart hx0_dom] at hle
      have hle_real : withTopRealPart f x0 ≤ withTopRealPart f x0 - ε / 2 := by
        exact_mod_cast hle
      linarith
    · rw [Prod.dist_eq, dist_self, max_eq_right]
      · rw [Real.dist_eq]
        have hhalf_lt : ε / 2 < ε := by
          linarith
        simpa [abs_of_nonneg (by linarith : 0 ≤ ε / 2)] using hhalf_lt
      · exact dist_nonneg

local notation "Z" => WithLp 2 (E × ℝ)
local notation "eZ" => WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ

/-- Helper for Theorem 3.1.15: on the real height coordinate, the real inner product is ordinary
multiplication. -/
lemma real_inner_scalar_eq_mul (a t : ℝ) : inner ℝ a t = a * t := by
  exact RCLike.inner_apply' (𝕜 := ℝ) a t

/-- Helper for Theorem 3.1.15: transport the raw-product frontier point to the `L²` product
owner used by the supporting-nesterovHyperplane theorem. -/
lemma basepoint_mem_frontier_constrainedEpigraph_closedBall_prodL2
    {f : E → WithTop ℝ} {x0 : E} {rho : ℝ} (hrho : 0 < rho)
    (hball : Metric.closedBall x0 rho ⊆ interior (dom f)) :
    WithLp.toLp 2 (x0, withTopRealPart f x0) ∈
      frontier (eZ ⁻¹' constrainedEpigraph (Metric.closedBall x0 rho) f) := by
  let e : Z ≃L[ℝ] E × ℝ := WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ
  -- Transport the raw frontier statement across the product `L²` homeomorphism.
  have hraw :
      (x0, withTopRealPart f x0) ∈
        frontier (constrainedEpigraph (Metric.closedBall x0 rho) f) :=
    basepoint_mem_frontier_constrainedEpigraph_closedBall hrho hball
  have hpre :
      e.toHomeomorph ⁻¹' frontier (constrainedEpigraph (Metric.closedBall x0 rho) f) =
        frontier (e ⁻¹' constrainedEpigraph (Metric.closedBall x0 rho) f) :=
    Homeomorph.preimage_frontier e.toHomeomorph
      (constrainedEpigraph (Metric.closedBall x0 rho) f)
  have hraw' :
      e.symm (x0, withTopRealPart f x0) ∈
        frontier (e ⁻¹' constrainedEpigraph (Metric.closedBall x0 rho) f) := by
    rw [← hpre]
    exact hraw
  simpa using hraw'

/-- Helper for Theorem 3.1.15: rewrite the supporting-nesterovHyperplane inequality on the `L²` product
owner into the pair-coordinate inequality used by the textbook epigraph argument. -/
lemma supporting_hyperplane_component_inequality_prodL2
    {Q : Set Z} {n : Z} {γ : ℝ}
    (hQ : IsSupportingHyperplane Q n γ)
    {x : E} {τ : ℝ} (hz : WithLp.toLp 2 (x, τ) ∈ Q) :
    inner ℝ n.fst x + n.snd * τ ≤ γ := by
  -- Rewrite the ambient `WithLp` inner product into the pair coordinates `(x, τ)`.
  have hineq : inner ℝ n (WithLp.toLp 2 (x, τ)) ≤ γ := hQ.le_offset hz
  have hineq' : inner ℝ n.fst x + inner ℝ n.snd τ ≤ γ := by
    simpa [WithLp.prod_inner_apply] using hineq
  rw [real_inner_scalar_eq_mul] at hineq'
  exact hineq'

/-- Helper for Theorem 3.1.15: the supporting normal of the local constrained epigraph has
strictly negative height component. -/
lemma supporting_hyperplane_snd_neg_of_constrainedEpigraph_closedBall
    {f : E → WithTop ℝ} {x0 : E} {rho : ℝ} (hrho : 0 < rho)
    (hball : Metric.closedBall x0 rho ⊆ interior (dom f))
    {n : Z} {γ : ℝ}
    (hz0 : WithLp.toLp 2 (x0, withTopRealPart f x0) ∈ nesterovHyperplane n γ)
    (hsupport : IsSupportingHyperplane
      (eZ ⁻¹' constrainedEpigraph (Metric.closedBall x0 rho) f) n γ) :
    n.snd < 0 := by
  let e : Z ≃L[ℝ] E × ℝ := WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ
  have hx0_ball : x0 ∈ Metric.closedBall x0 rho := Metric.mem_closedBall_self hrho.le
  have hx0_dom : x0 ∈ dom f := interior_subset (hball hx0_ball)
  have hcontact : inner ℝ n.fst x0 + n.snd * withTopRealPart f x0 = γ := by
    -- The supporting nesterovHyperplane meets the constrained epigraph at the basepoint.
    have hcontact' : inner ℝ n.fst x0 + inner ℝ n.snd (withTopRealPart f x0) = γ := by
      simpa [WithLp.prod_inner_apply] using hz0
    rw [real_inner_scalar_eq_mul] at hcontact'
    exact hcontact'
  have hsnd_nonpos : n.snd ≤ 0 := by
    -- Testing the support inequality along the vertical ray gives the nonpositive sign.
    have hz1 :
        WithLp.toLp 2 (x0, withTopRealPart f x0 + 1) ∈
          e ⁻¹' constrainedEpigraph (Metric.closedBall x0 rho) f := by
      have hmem :
          (x0, withTopRealPart f x0 + 1) ∈
            constrainedEpigraph (Metric.closedBall x0 rho) f := by
        exact mem_constrainedEpigraph_iff.2
          ⟨hx0_ball, by
            rw [← coe_withTopRealPart (f := f) hx0_dom]
            exact_mod_cast (show withTopRealPart f x0 ≤ withTopRealPart f x0 + 1 by linarith)⟩
      simpa [Set.preimage, e] using hmem
    have hineq1 :
        inner ℝ n.fst x0 + n.snd * (withTopRealPart f x0 + 1) ≤ γ :=
      supporting_hyperplane_component_inequality_prodL2 hsupport hz1
    linarith
  by_contra hsnd_nonneg
  have hsnd_zero : n.snd = 0 := by linarith
  have hfst_ne_zero : n.fst ≠ 0 := by
    intro hfst_zero
    apply hsupport.ne_zero
    apply e.injective
    change (n.fst, n.snd) = (0, 0)
    simp [hfst_zero, hsnd_zero]
  let s : ℝ := rho / (2 * ‖n.fst‖)
  have hs_pos : 0 < s := by
    dsimp [s]
    exact div_pos hrho (mul_pos zero_lt_two (norm_pos_iff.mpr hfst_ne_zero))
  have hs_norm : ‖s • n.fst‖ = rho / 2 := by
    dsimp [s]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs_pos.le]
    have hcalc : (rho / (2 * ‖n.fst‖)) * ‖n.fst‖ = rho / 2 := by
      field_simp [norm_ne_zero_iff.mpr hfst_ne_zero]
    simpa using hcalc
  let xPlus : E := x0 + s • n.fst
  have hxPlus_ball : xPlus ∈ Metric.closedBall x0 rho := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hxPlus_dist : ‖xPlus - x0‖ = rho / 2 := by
      simp [xPlus, hs_norm, sub_eq_add_neg, add_assoc]
    linarith [hxPlus_dist, hrho]
  have hxPlus_dom : xPlus ∈ dom f := interior_subset (hball hxPlus_ball)
  have hzPlus :
      WithLp.toLp 2 (xPlus, withTopRealPart f xPlus) ∈
        e ⁻¹' constrainedEpigraph (Metric.closedBall x0 rho) f := by
    have hmem :
        (xPlus, withTopRealPart f xPlus) ∈
          constrainedEpigraph (Metric.closedBall x0 rho) f := by
      exact mem_constrainedEpigraph_iff.2
        ⟨hxPlus_ball, by
          simpa using le_of_eq (coe_withTopRealPart (f := f) hxPlus_dom).symm⟩
    simpa [Set.preimage, e] using hmem
  have hineqPlus :
      inner ℝ n.fst xPlus + n.snd * withTopRealPart f xPlus ≤ γ :=
    supporting_hyperplane_component_inequality_prodL2 hsupport hzPlus
  have hcontr : s * ‖n.fst‖ ^ 2 ≤ 0 := by
    rw [hsnd_zero] at hineqPlus hcontact
    have hxPlus_shift :
        inner ℝ n.fst xPlus = inner ℝ n.fst x0 + s * ‖n.fst‖ ^ 2 := by
      -- Moving in the `n.fst` direction changes the supporting functional by `s ‖n.fst‖²`.
      dsimp [xPlus]
      rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    linarith
  have hstrict : 0 < s * ‖n.fst‖ ^ 2 := by
    have hnorm_sq_pos : 0 < ‖n.fst‖ ^ 2 := by
      positivity
    positivity
  linarith

/-- Helper for Theorem 3.1.15: a local affine support inequality on a closed ball extends to the
whole effective domain by convexity along segments from `x0`. -/
lemma global_support_of_local_support_closedBall
    {f : E → WithTop ℝ} (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    {x0 : E} (hx0 : x0 ∈ dom f) {rho : ℝ} (hrho : 0 < rho) {g : E}
    (hlocal : ∀ ⦃x : E⦄, x ∈ Metric.closedBall x0 rho →
      withTopRealPart f x0 + inner ℝ g (x - x0) ≤ withTopRealPart f x) :
    ∀ ⦃y : E⦄, y ∈ dom f →
      withTopRealPart f x0 + inner ℝ g (y - x0) ≤ withTopRealPart f y := by
  intro y hy
  by_cases hy_eq : y = x0
  · subst hy_eq
    simp
  · let t : ℝ := min 1 (rho / ‖y - x0‖)
    let z : E := (1 - t) • x0 + t • y
    have hy_sub_ne : y - x0 ≠ 0 := sub_ne_zero.mpr hy_eq
    have hnorm_pos : 0 < ‖y - x0‖ := norm_pos_iff.mpr hy_sub_ne
    have ht_pos : 0 < t := by
      exact lt_min zero_lt_one (div_pos hrho hnorm_pos)
    have ht_le_one : t ≤ 1 := min_le_left _ _
    have hz_eq : z - x0 = t • (y - x0) := by
      dsimp [z, t]
      simp [sub_eq_add_neg, add_comm, add_left_comm, smul_add, add_smul]
    have hz_dom : z ∈ dom f := by
      -- Follow the segment from `x0` to `y` inside the convex effective domain.
      dsimp [z, t]
      exact hf.1 hx0 hy (sub_nonneg.mpr ht_le_one) ht_pos.le (by linarith)
    have hz_closedBall : z ∈ Metric.closedBall x0 rho := by
      rw [Metric.mem_closedBall, dist_eq_norm, hz_eq, norm_smul, Real.norm_of_nonneg ht_pos.le]
      have ht_mul : t * ‖y - x0‖ ≤ rho := by
        have hmul :
            t * ‖y - x0‖ ≤ (rho / ‖y - x0‖) * ‖y - x0‖ :=
          mul_le_mul_of_nonneg_right (min_le_right 1 (rho / ‖y - x0‖)) hnorm_pos.le
        have hrewrite : (rho / ‖y - x0‖) * ‖y - x0‖ = rho := by
          field_simp [hnorm_pos.ne']
        simpa [hrewrite, mul_comm, mul_left_comm, mul_assoc] using hmul
      simpa using ht_mul
    have hlocal_z : withTopRealPart f x0 + inner ℝ g (z - x0) ≤ withTopRealPart f z :=
      hlocal hz_closedBall
    have hconv_z :
        withTopRealPart f z ≤
          (1 - t) * withTopRealPart f x0 + t * withTopRealPart f y := by
      dsimp [z, t]
      exact hf.2 hx0 hy (sub_nonneg.mpr ht_le_one) ht_pos.le (by linarith)
    have hlocal_y :
        withTopRealPart f x0 + t * inner ℝ g (y - x0) ≤ withTopRealPart f z := by
      simpa [hz_eq, real_inner_smul_right, mul_comm, mul_left_comm, mul_assoc] using hlocal_z
    have hscaled :
        t * (withTopRealPart f x0 + inner ℝ g (y - x0)) ≤ t * withTopRealPart f y := by
      nlinarith
    nlinarith

/-- Helper for Theorem 3.1.15: convexity gives a Lipschitz ball around every interior point of
the effective domain. -/
lemma exists_lipschitz_ball_subset_effectiveDomain_of_mem_interior
    [FiniteDimensional ℝ E] {f : E → WithTop ℝ}
    (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    {x0 : E} (hx0 : x0 ∈ interior (dom f)) :
    ∃ r > 0, Metric.ball x0 r ⊆ dom f ∧
      ∃ K : NNReal, LipschitzOnWith K (withTopRealPart f) (Metric.ball x0 r) := by
  -- Start from the canonical local-Lipschitz theorem on the interior and shrink to a metric ball.
  obtain ⟨K, s, hs, hK⟩ := hf.locallyLipschitzOn_interior hx0
  rcases Metric.mem_nhdsWithin_iff.1 hs with ⟨r1, hr1, hr1sub⟩
  rcases Metric.mem_nhds_iff.1 (isOpen_interior.mem_nhds hx0) with ⟨r2, hr2, hr2sub⟩
  refine ⟨min r1 r2, lt_min hr1 hr2, ?_, K, hK.mono ?_⟩
  · intro y hy
    exact interior_subset <| hr2sub (Metric.ball_subset_ball (min_le_right _ _) hy)
  · intro y hy
    exact hr1sub ⟨Metric.ball_subset_ball (min_le_left _ _) hy,
      hr2sub (Metric.ball_subset_ball (min_le_right _ _) hy)⟩

/-- Helper for Theorem 3.1.15: the supporting nesterovHyperplane of the local closed-ball epigraph yields
an affine lower support on that closed ball. -/
lemma exists_local_affine_support_on_closedBall_of_convexOn_of_mem_interior
    [FiniteDimensional ℝ E] {f : E → WithTop ℝ}
    (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    {x0 : E} (hx0 : x0 ∈ interior (dom f)) :
    ∃ rho > 0, ∃ g : E, ∀ ⦃x : E⦄, x ∈ Metric.closedBall x0 rho →
      withTopRealPart f x0 + inner ℝ g (x - x0) ≤ withTopRealPart f x := by
  -- Route correction: keep the textbook support-nesterovHyperplane proof, but transport the constrained
  -- epigraph once to the `WithLp 2 (E × ℝ)` owner before applying Theorem 3.1.14.
  obtain ⟨r, hr, hball_dom, K, hK⟩ :=
    exists_lipschitz_ball_subset_effectiveDomain_of_mem_interior hf hx0
  let rho : ℝ := r / 2
  let e : Z ≃L[ℝ] E × ℝ := WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ
  have hrho : 0 < rho := by
    dsimp [rho]
    exact half_pos hr
  have hclosed_subset_ball : Metric.closedBall x0 rho ⊆ Metric.ball x0 r := by
    dsimp [rho]
    exact Metric.closedBall_subset_ball (half_lt_self hr)
  have hball :
      Metric.closedBall x0 rho ⊆ interior (dom f) := by
    intro y hy
    have hy_ball : y ∈ Metric.ball x0 r := hclosed_subset_ball hy
    exact mem_interior_iff_mem_nhds.2 <|
      Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hy_ball) hball_dom
  have hcont_closedBall : ContinuousOn (withTopRealPart f) (Metric.closedBall x0 rho) :=
    hK.continuousOn.mono hclosed_subset_ball
  have hdom_closedBall : Metric.closedBall x0 rho ⊆ dom f := fun y hy ↦ interior_subset (hball hy)
  have hclosed_raw :
      IsClosed (constrainedEpigraph (Metric.closedBall x0 rho) f) := by
    rw [constrainedEpigraph_eq_epigraph_withTopRealPart hdom_closedBall]
    exact IsClosed.epigraph Metric.isClosed_closedBall hcont_closedBall
  have hconvOn_closedBall : ConvexOn ℝ (Metric.closedBall x0 rho) (withTopRealPart f) :=
    by
      refine ⟨convex_closedBall x0 rho, ?_⟩
      intro x hx y hy a b ha hb hab
      exact hf.2 (hdom_closedBall hx) (hdom_closedBall hy) ha hb hab
  have hconv_raw :
      Convex ℝ (constrainedEpigraph (Metric.closedBall x0 rho) f) := by
    rw [constrainedEpigraph_eq_epigraph_withTopRealPart hdom_closedBall]
    exact (convexOn_iff_convex_epigraph).1 hconvOn_closedBall
  let Qrho : Set Z := e ⁻¹' constrainedEpigraph (Metric.closedBall x0 rho) f
  have hz0_frontier :
      WithLp.toLp 2 (x0, withTopRealPart f x0) ∈ frontier Qrho := by
    simpa [Qrho] using
      basepoint_mem_frontier_constrainedEpigraph_closedBall_prodL2 hrho hball
  have hclosed_Qrho : IsClosed Qrho := by
    simpa [Qrho] using hclosed_raw.preimage e.continuous
  have hconv_Qrho : Convex ℝ Qrho := by
    simpa [Qrho] using hconv_raw.linear_preimage e.toLinearMap
  obtain ⟨n, γ, hz0, hsupport⟩ :=
    exists_supporting_hyperplane_at_boundary_point_of_closed_convex
      Qrho hclosed_Qrho hconv_Qrho hz0_frontier
  have hsnd_neg :
      n.snd < 0 :=
    supporting_hyperplane_snd_neg_of_constrainedEpigraph_closedBall hrho hball hz0 hsupport
  let g : E := (-n.snd)⁻¹ • n.fst
  refine ⟨rho, hrho, g, ?_⟩
  intro x hx
  have hx_dom : x ∈ dom f := hdom_closedBall hx
  have hz :
      WithLp.toLp 2 (x, withTopRealPart f x) ∈ Qrho := by
    have hmem :
        (x, withTopRealPart f x) ∈ constrainedEpigraph (Metric.closedBall x0 rho) f := by
      exact mem_constrainedEpigraph_iff.2
        ⟨hx, by
          simpa using le_of_eq (coe_withTopRealPart (f := f) hx_dom).symm⟩
    simpa [Qrho, Set.preimage, e] using hmem
  have hineq :
      inner ℝ n.fst x + n.snd * withTopRealPart f x ≤ γ :=
    supporting_hyperplane_component_inequality_prodL2 hsupport hz
  have hcontact :
      inner ℝ n.fst x0 + n.snd * withTopRealPart f x0 = γ := by
    -- Rewrite the contact condition at the basepoint into the pair coordinates.
    have hcontact' : inner ℝ n.fst x0 + inner ℝ n.snd (withTopRealPart f x0) = γ := by
      simpa [WithLp.prod_inner_apply] using hz0
    rw [real_inner_scalar_eq_mul] at hcontact'
    exact hcontact'
  let a : ℝ := -n.snd
  have ha_pos : 0 < a := by
    dsimp [a]
    linarith
  have hdiff0 :
      inner ℝ n.fst x - inner ℝ n.fst x0 ≤
        n.snd * (withTopRealPart f x0 - withTopRealPart f x) := by
    linarith
  have hdiff0' :
      inner ℝ n.fst x - inner ℝ n.fst x0 ≤
        a * (withTopRealPart f x - withTopRealPart f x0) := by
    dsimp [a]
    have hrewrite :
        n.snd * (withTopRealPart f x0 - withTopRealPart f x) =
          (-n.snd) * (withTopRealPart f x - withTopRealPart f x0) := by
      ring
    rw [hrewrite] at hdiff0
    exact hdiff0
  have hdiff :
      inner ℝ n.fst (x - x0) ≤ a * (withTopRealPart f x - withTopRealPart f x0) := by
    simpa [inner_sub_right] using hdiff0'
  have hscaled : a⁻¹ * inner ℝ n.fst (x - x0) ≤ withTopRealPart f x - withTopRealPart f x0 := by
    have hmul :
        a⁻¹ * inner ℝ n.fst (x - x0) ≤
          a⁻¹ * (a * (withTopRealPart f x - withTopRealPart f x0)) :=
      mul_le_mul_of_nonneg_left hdiff (inv_nonneg.mpr ha_pos.le)
    simpa [ha_pos.ne', mul_assoc] using hmul
  -- Divide by the positive height coefficient and rewrite the result as the affine support claim.
  have hgineq : inner ℝ g (x - x0) ≤ withTopRealPart f x - withTopRealPart f x0 := by
    simpa [g, a, real_inner_smul_left] using hscaled
  linarith

/-- Helper for Theorem 3.1.15: a convex function admits a subgradient at every interior point of
its effective domain. -/
lemma subdifferential_nonempty_of_convexOn_of_mem_interior
    [FiniteDimensional ℝ E] {f : E → WithTop ℝ}
    (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    {x0 : E} (hx0 : x0 ∈ interior (dom f)) :
    (∂ f(x0)).Nonempty := by
  -- The supporting nesterovHyperplane of the local closed-ball epigraph yields a local affine support.
  obtain ⟨rho, hrho, g, hlocal⟩ :=
    exists_local_affine_support_on_closedBall_of_convexOn_of_mem_interior hf hx0
  refine ⟨g, mem_subdifferential_iff.mpr ?_⟩
  constructor
  · exact interior_subset hx0
  · intro y hy
    -- Convexity propagates the local affine support to every point of the effective domain.
    have hglobal :=
      global_support_of_local_support_closedBall hf (interior_subset hx0) hrho hlocal hy
    rw [← coe_withTopRealPart hy, ← coe_withTopRealPart (interior_subset hx0)]
    exact_mod_cast hglobal

/-- Helper for Theorem 3.1.15: every subgradient at `x0` is bounded in norm by any local
Lipschitz constant on a ball around `x0`. -/
lemma norm_le_of_mem_subdifferential_of_lipschitz_ball
    {f : E → WithTop ℝ} {x0 g : E} {r : ℝ} {K : NNReal}
    (hr : 0 < r) (hball : Metric.ball x0 r ⊆ dom f)
    (hK : LipschitzOnWith K (withTopRealPart f) (Metric.ball x0 r))
    (hg : g ∈ ∂ f(x0)) :
    ‖g‖ ≤ K := by
  by_cases hg_zero : g = 0
  · simp [hg_zero]
  · let u : E := ‖g‖⁻¹ • g
    let y : E := x0 + (r / 2) • u
    have hu_norm : ‖u‖ = 1 := by
      dsimp [u]
      calc
        ‖‖g‖⁻¹ • g‖ = |‖g‖⁻¹| * ‖g‖ := norm_smul _ _
        _ = ‖g‖⁻¹ * ‖g‖ := by
          rw [abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
        _ = 1 := by
          field_simp [norm_ne_zero_iff.mpr hg_zero]
    have hy_dist : dist y x0 = r / 2 := by
      rw [dist_eq_norm]
      calc
        ‖y - x0‖ = ‖(r / 2) • u‖ := by
          simp [y, u, sub_eq_add_neg, add_assoc]
        _ = |r / 2| * ‖u‖ := norm_smul _ _
        _ = r / 2 := by
          rw [abs_of_nonneg (by linarith : 0 ≤ r / 2)]
          simp [hu_norm]
    have hy_ball : y ∈ Metric.ball x0 r := by
      rw [Metric.mem_ball]
      linarith [hy_dist, hr]
    have hx0_ball : x0 ∈ Metric.ball x0 r := Metric.mem_ball_self hr
    have hx0_dom : x0 ∈ dom f := (mem_subdifferential_iff.mp hg).mem_dom
    have hy_dom : y ∈ dom f := hball hy_ball
    have hsub : f y ≥ f x0 + (inner ℝ g (y - x0) : WithTop ℝ) :=
      (mem_subdifferential_iff.mp hg).2 hy_dom
    have hy_sub : y - x0 = (r / 2) • u := by
      simp [y, u, sub_eq_add_neg, add_assoc]
    have hinner :
        inner ℝ g (y - x0) = (r / 2) * ‖g‖ := by
      rw [hy_sub, real_inner_smul_right]
      dsimp [u]
      calc
        (r / 2) * inner ℝ g (‖g‖⁻¹ • g) = (r / 2) * (‖g‖⁻¹ * inner ℝ g g) := by
          rw [real_inner_smul_right]
        _ = (r / 2) * ‖g‖ := by
          rw [real_inner_self_eq_norm_sq]
          field_simp [norm_ne_zero_iff.mpr hg_zero]
    have hlower :
        (r / 2) * ‖g‖ ≤ withTopRealPart f y - withTopRealPart f x0 := by
      rw [← coe_withTopRealPart hy_dom, ← coe_withTopRealPart hx0_dom, hinner] at hsub
      have hreal : withTopRealPart f x0 + (r / 2) * ‖g‖ ≤ withTopRealPart f y := by
        exact_mod_cast hsub
      linarith
    have hdist :
        dist (withTopRealPart f y) (withTopRealPart f x0) ≤ K * dist y x0 :=
      hK.dist_le_mul y hy_ball x0 hx0_ball
    have hupper_abs :
        |withTopRealPart f y - withTopRealPart f x0| ≤ K * (r / 2) := by
      simpa [Real.dist_eq, hy_dist] using hdist
    have hupper :
        withTopRealPart f y - withTopRealPart f x0 ≤ K * (r / 2) := by
      exact le_trans (le_abs_self _) hupper_abs
    nlinarith

/- Theorem 3.1.15 lies in the chapter's extended-valued convex-subdifferential domain.

Primary domain:
- convex analysis of `ℝ ∪ {+∞}`-valued functions on finite-dimensional real inner-product spaces.

Sampled owner-style declarations:
- `dom` and `withTopRealPart` in `Definition_3_3`, the chapter owners for the effective domain
  and finite-value representative;
- `IsSubgradientAt` and `subdifferential` in `Definition_3_1_5`, the chapter owners for
  extended-valued subgradients and their set-valued envelope;
- `ConvexOn.locallyLipschitzOn_interior` in mathlib, the canonical local regularity theorem for
  convex real-valued functions on the interior of a convex set;
- `exists_supporting_affineHyperplane_at_boundary_point_of_closed_convex` in `Theorem_3_1_4_2`,
  the chapter's owner-level supporting-nesterovHyperplane theorem on finite-dimensional real
  inner-product spaces.

Best owner abstraction:
- source-facing theorem on the existing owner surface
  `ConvexOn ℝ (dom f) (withTopRealPart f)` and `∂ f(x0)`.

Primitive data:
- the convexity hypothesis `hf : ConvexOn ℝ (dom f) (withTopRealPart f)`;
- the interior-domain hypothesis `hx0 : x0 ∈ interior (dom f)`.

Derived API:
- nonemptiness and boundedness of `∂ f(x0)`.

Source/core/bridge triage:
- source-facing: the textbook theorem that interior effective-domain points admit a nonempty
  bounded subdifferential;
- core/canonical: the owner declarations `dom`, `withTopRealPart`, and `subdifferential`;
- bridge/view: local Lipschitz control from `ConvexOn.locallyLipschitzOn_interior` and the
  finite-dimensional supporting-nesterovHyperplane bridge from `Theorem_3_1_4_2`.

The previous file rebuilt local copies of the effective domain, the subgradient predicate, and the
subdifferential set, even though those notions are already owned upstream in `Definition_3_1_5`.
The neighboring source-facing subdifferential files already live on the intrinsic real
inner-product-space owner layer rather than a local `EuclideanSpace ℝ (Fin n)` model. This
refinement aligns Theorem 3.1.15 with that owner layer, keeping the same mathematics while
deleting the remaining concrete-model wrapper.
-/

/-- Theorem 3 1 15: generalized from the textbook Euclidean setting, if an `ℝ ∪ {+∞}`-valued
convex function on a finite-dimensional real inner-product space is finite at an interior point
`x₀` of its effective domain, then the subdifferential `∂f(x₀)` is nonempty and bounded. The
textbook statement is the specialization `E = EuclideanSpace ℝ (Fin n)`. -/
-- Proof sketch: local convex regularity gives a neighborhood of `x₀` on which the finite-value
-- representative `withTopRealPart f` is Lipschitz. A supporting nesterovHyperplane to the epigraph at
-- `(f x₀, x₀)` then yields one subgradient, and the same local Lipschitz bound controls the norm
-- of every subgradient.
theorem subdifferential_nonempty_and_isBounded_of_convexOn_effectiveDomain_of_mem_interior
    [FiniteDimensional ℝ E] {f : E → WithTop ℝ}
    (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    {x0 : E} (hx0 : x0 ∈ interior (dom f)) :
    (∂ f(x0)).Nonempty ∧ Bornology.IsBounded (∂ f(x0)) := by
  -- First produce one subgradient by supporting a local closed-ball epigraph.
  have hnonempty : (∂ f(x0)).Nonempty :=
    subdifferential_nonempty_of_convexOn_of_mem_interior hf hx0
  -- Then use the local Lipschitz ball from Theorem 3.1.11 to bound every subgradient uniformly.
  obtain ⟨r, hr, hball, K, hK⟩ :=
    exists_lipschitz_ball_subset_effectiveDomain_of_mem_interior hf hx0
  refine
    ⟨hnonempty,
      (Metric.isBounded_closedBall :
          Bornology.IsBounded (Metric.closedBall (0 : E) K)).subset ?_⟩
  intro g hg
  rw [Metric.mem_closedBall, dist_zero_right]
  exact norm_le_of_mem_subdifferential_of_lipschitz_ball hr hball hK hg

end
