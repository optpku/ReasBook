/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_14

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient HessianLocalNorm

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Corollary 5.3.2 lies in the Chapter 5 self-concordant-barrier / recession-direction domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantBarrierOnWith` from `Definition_5_3_2`, the barrier owner;
* `IsSelfConcordantOnWith.hessianLocalNorm_le_neg_gradient_inner_of_recession_direction` from
  `Theorem_5_1_14`, the canonical self-concordant recession-direction estimate used here;
* `hessianLocalNorm` and `‖u‖[F; x]` from `Definition_5_1_1`, the canonical local-norm owner.

Source/core/bridge triage:
* source-facing: the barrier specialization of the recession-direction estimate;
* core/canonical: `IsSelfConcordantBarrierOnWith dom ν F`, viewed through its parent
  `IsSelfConcordantOnWith dom 1 F`;
* bridge/view: the barrier-specific derivation of the nonascent and backward-frontier hypotheses
  needed to apply Theorem 5.1.14.

This corollary is a barrier-owner specialization of the Chapter 5 recession-direction estimate, so
its public surface should live on `IsSelfConcordantBarrierOnWith` rather than as a parallel
top-level theorem repeating the owner theorem's name. -/

namespace IsSelfConcordantBarrierOnWith

section

variable {dom : Set E} {ν : NNReal} {F : E → ℝ}
variable {h x : E}

/-- Helper for Corollary 5.3.2: evaluating the barrier inequality on a scaled direction produces
the expected scalar quadratic family. -/
private theorem barrier_expression_smul
    {z u : E} (t : ℝ) :
    2 * inner ℝ (∇ F z) (t • u) - inner ℝ (t • u) (hessian F z (t • u)) =
      2 * t * inner ℝ (∇ F z) u - t ^ (2 : ℕ) * inner ℝ u (hessian F z u) := by
  -- Pull the scalar through the gradient pairing and the Hessian quadratic form.
  simp [inner_smul_left, inner_smul_right, pow_two, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Corollary 5.3.2: a scalar quadratic family bounded above by `ν` forces the
discriminant estimate `a² ≤ ν b`. -/
private theorem sq_le_mul_of_barrier_line_family
    {a b ν : ℝ} (hb : 0 ≤ b)
    (hline : ∀ t : ℝ, 2 * t * a - t ^ (2 : ℕ) * b ≤ ν) :
    a ^ (2 : ℕ) ≤ ν * b := by
  by_cases hb0 : b = 0
  · by_cases ha0 : a = 0
    · simp [ha0, hb0]
    · have htest := hline ((ν + 1) / (2 * a))
      have hcontr : ν + 1 ≤ ν := by
        have hrew : 2 * ((ν + 1) / (2 * a)) * a ≤ ν := by
          simpa [hb0] using htest
        field_simp [ha0] at hrew
        linarith
      linarith
  · have hb_pos : 0 < b := lt_of_le_of_ne hb (by simpa [eq_comm] using hb0)
    have hb_ne : b ≠ 0 := ne_of_gt hb_pos
    have htest := hline (a / b)
    have hquot : a ^ (2 : ℕ) / b ≤ ν := by
      have hrewrite :
          2 * (a / b) * a - (a / b) ^ (2 : ℕ) * b = a ^ (2 : ℕ) / b := by
        field_simp [hb_ne]
        ring
      simpa [hrewrite] using htest
    exact (_root_.div_le_iff₀ hb_pos).1 hquot

omit [CompleteSpace E] in
/-- Helper for Corollary 5.3.2: differentiating the affine line `z + t • h` returns the fixed
direction `h`. -/
private theorem line_hasDerivAt
    (z h : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ z + s • h) h t := by
  -- The affine line is the sum of a constant and a scalar multiple of the identity.
  simpa [one_smul] using ((hasDerivAt_id t).smul_const h).const_add z

/-- Helper for Corollary 5.3.2: scalarizing the gradient along a feasible line differentiates to
the corresponding Hessian pairing. -/
private theorem gradient_pairing_line_hasDerivAt
    (hF : IsSelfConcordantBarrierOnWith dom ν F)
    {z h : E} {t : ℝ} (hzt : z + t • h ∈ dom) :
    HasDerivAt (fun s : ℝ ↦ inner ℝ (∇ F (z + s • h)) h)
      (inner ℝ (hessian F (z + t • h) h) h) t := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfderiv : DifferentiableAt ℝ (fderiv ℝ F) (z + t • h) := by
    -- A `C²` barrier objective has a differentiable Fréchet derivative field on its open domain.
    have hcont : ContDiffAt ℝ 1 (fderiv ℝ F) (z + t • h) :=
      (hF.toIsStandardSelfConcordantOn.contDiffOn.of_le (by norm_num)).contDiffAt
          (hF.toIsStandardSelfConcordantOn.isOpen_domain.mem_nhds hzt)
        |>.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    exact hcont.differentiableAt one_ne_zero
  have hgrad : DifferentiableAt ℝ (∇ F) (z + t • h) := by
    -- Rewrite the gradient through the Riesz map before differentiating it.
    simpa [gradient, D] using D.differentiableAt.comp (z + t • h) hfderiv
  have hgradLine :
      HasFDerivAt (fun s : ℝ ↦ ∇ F (z + s • h))
        ((hessian F (z + t • h)).comp (ContinuousLinearMap.toSpanSingleton ℝ h)) t := by
    -- Compose the gradient derivative with the affine-line derivative.
    simpa using (hgrad.hasFDerivAt.comp t (line_hasDerivAt z h t).hasFDerivAt)
  let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) h
  have hscalar :
      HasFDerivAt (fun s : ℝ ↦ φ (∇ F (z + s • h)))
        (φ.comp ((hessian F (z + t • h)).comp (ContinuousLinearMap.toSpanSingleton ℝ h))) t := by
    -- Postcompose with the scalar functional `v ↦ ⟪v, h⟫`.
    simpa [φ] using ((φ.hasFDerivAt).comp t hgradLine)
  simpa [φ, InnerProductSpace.toDual_apply_apply, real_inner_comm] using hscalar.hasDerivAt

/-- Helper for Corollary 5.3.2: the barrier-parameter inequality implies the pointwise quadratic
estimate `⟪∇F(z), h⟫² ≤ ν ⟪h, ∇²F(z)h⟫`. -/
private theorem gradient_pairing_sq_le_barrier_parameter_hessian_pairing
    (hF : IsSelfConcordantBarrierOnWith dom ν F)
    {z h : E} (hz : z ∈ dom) :
    (inner ℝ (∇ F z) h) ^ (2 : ℕ) ≤
      (ν : ℝ) * inner ℝ h (hessian F z h) := by
  have hquad : 0 ≤ inner ℝ h (hessian F z h) :=
    hF.toIsStandardSelfConcordantOn.hessian_posSemidef hz h
  have hline :
      ∀ t : ℝ,
        2 * t * inner ℝ (∇ F z) h - t ^ (2 : ℕ) * inner ℝ h (hessian F z h) ≤ (ν : ℝ) := by
    intro t
    have hbound := hF.barrier_parameter_bound hz (t • h)
    rw [barrier_expression_smul] at hbound
    exact hbound
  -- Evaluating the owner inequality on all scalar multiples of `h` yields the discriminant bound.
  exact sq_le_mul_of_barrier_line_family hquad hline

/-- Helper for Corollary 5.3.2: along any feasible forward ray, the gradient pairing with the ray
direction is nonpositive. -/
private theorem inner_gradient_nonpos_of_recession_direction_aux
    (hF : IsSelfConcordantBarrierOnWith dom ν F)
    {z h : E} (hforward : ∀ τ : ℝ, 0 ≤ τ → z + τ • h ∈ dom)
    (hz : z ∈ dom) :
    inner ℝ (∇ F z) h ≤ 0 := by
  let g : ℝ → ℝ := fun t ↦ inner ℝ (∇ F (z + t • h)) h
  have hg_cont : ContinuousOn g (Set.Ici (0 : ℝ)) := by
    intro t ht
    have hzt : z + t • h ∈ dom := hforward t ht
    have hcontAt :=
      (gradient_pairing_line_hasDerivAt (hF := hF) (z := z) (h := h) hzt).continuousAt
    exact hcontAt.continuousWithinAt
  have hg_diff : DifferentiableOn ℝ g (Set.Ioi (0 : ℝ)) := by
    intro t ht
    have hzt : z + t • h ∈ dom := hforward t (le_of_lt ht)
    have hdiffAt :=
      (gradient_pairing_line_hasDerivAt (hF := hF) (z := z) (h := h) hzt).differentiableAt
    exact hdiffAt.differentiableWithinAt
  have hg_deriv_nonneg : ∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ deriv g t := by
    intro t ht
    have hzt : z + t • h ∈ dom := hforward t (le_of_lt ht)
    have hquad := hF.toIsStandardSelfConcordantOn.hessian_posSemidef hzt h
    rw [(gradient_pairing_line_hasDerivAt (hF := hF) (z := z) (h := h) hzt).deriv]
    simpa [g, real_inner_comm] using hquad
  have hg_mono : MonotoneOn g (Set.Ici (0 : ℝ)) := by
    -- The Hessian positivity makes the scalar gradient pairing monotone along the forward ray.
    refine monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ)) hg_cont ?_ ?_
    · simpa [interior_Ici] using hg_diff
    · simpa [interior_Ici] using hg_deriv_nonneg
  by_cases hν : ν = 0
  · have hsq :=
      gradient_pairing_sq_le_barrier_parameter_hessian_pairing (hF := hF) (z := z) (h := h) hz
    have hν_real : (ν : ℝ) = 0 := by exact_mod_cast hν
    have hsq_zero : (g 0) ^ (2 : ℕ) ≤ 0 := by
      simpa [g, hν_real] using hsq
    have hg_zero : g 0 = 0 := by
      nlinarith [sq_nonneg (g 0), hsq_zero]
    simpa [g] using hg_zero.le
  · have hν_pos : 0 < (ν : ℝ) := by
      exact_mod_cast (pos_iff_ne_zero.mpr hν)
    by_contra hg0_pos
    have hg0_pos' : 0 < g 0 := by
      simpa [g] using lt_of_not_ge hg0_pos
    have hg_pos : ∀ t ∈ Set.Ici (0 : ℝ), 0 < g t := by
      intro t ht
      have hmono := hg_mono (show (0 : ℝ) ∈ Set.Ici (0 : ℝ) by simp) ht (by simpa using ht)
      exact lt_of_lt_of_le hg0_pos' hmono
    let q : ℝ → ℝ := fun t ↦ (g t)⁻¹ + t / (ν : ℝ)
    have hq_cont : ContinuousOn q (Set.Ici (0 : ℝ)) := by
      intro t ht
      have hgt_ne : g t ≠ 0 := (hg_pos t ht).ne'
      have hg_contAt : ContinuousAt g t := by
        have hzt : z + t • h ∈ dom := hforward t ht
        exact (gradient_pairing_line_hasDerivAt (hF := hF) (z := z) (h := h) hzt).continuousAt
      have hlinCont : ContinuousAt (fun s : ℝ ↦ s / (ν : ℝ)) t := by
        simpa [div_eq_mul_inv] using
          ((continuousAt_id : ContinuousAt (fun s : ℝ ↦ s) t).mul continuousAt_const)
      -- The reciprocal correction term is continuous wherever the scalar pairing stays positive.
      simpa [q] using ((hg_contAt.inv₀ hgt_ne).add hlinCont).continuousWithinAt
    have hq_hasDerivAt :
        ∀ t ∈ Set.Ioi (0 : ℝ),
          HasDerivAt q (-(deriv g t) / (g t) ^ (2 : ℕ) + 1 / (ν : ℝ)) t := by
      intro t ht
      have hzt : z + t • h ∈ dom := hforward t (le_of_lt ht)
      have hgt_ne : g t ≠ 0 := (hg_pos t (by simpa using (le_of_lt ht))).ne'
      have hg_hasDerivAt :
          HasDerivAt g (inner ℝ (hessian F (z + t • h) h) h) t := by
        simpa [g] using gradient_pairing_line_hasDerivAt (hF := hF) (z := z) (h := h) hzt
      have hginv :
          HasDerivAt (fun s : ℝ ↦ (g s)⁻¹) (-(deriv g t) / (g t) ^ (2 : ℕ)) t := by
        have hg_deriv : deriv g t = inner ℝ (hessian F (z + t • h) h) h := by
          rw [hg_hasDerivAt.deriv]
        simpa [hg_deriv] using hg_hasDerivAt.inv hgt_ne
      have hlin :
          HasDerivAt (fun s : ℝ ↦ s / (ν : ℝ)) (1 / (ν : ℝ)) t := by
        simpa [one_div, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using
          (hasDerivAt_id t).const_mul ((ν : ℝ)⁻¹)
      -- Differentiate the reciprocal correction term entrywise.
      simpa [q] using hginv.add hlin
    have hq_diff : DifferentiableOn ℝ q (Set.Ioi (0 : ℝ)) := by
      intro t ht
      exact (hq_hasDerivAt t ht).differentiableAt.differentiableWithinAt
    have hq_deriv_nonpos : ∀ t ∈ Set.Ioi (0 : ℝ), deriv q t ≤ 0 := by
      intro t ht
      have hzt : z + t • h ∈ dom := hforward t (le_of_lt ht)
      have hgt_pos : 0 < g t := hg_pos t (by simpa using (le_of_lt ht))
      have hg_hasDerivAt :
          HasDerivAt g (inner ℝ (hessian F (z + t • h) h) h) t := by
        simpa [g] using gradient_pairing_line_hasDerivAt (hF := hF) (z := z) (h := h) hzt
      have hsq :
          (g t) ^ (2 : ℕ) ≤ (ν : ℝ) * deriv g t := by
        have hquad :=
          gradient_pairing_sq_le_barrier_parameter_hessian_pairing
            (hF := hF) (z := z + t • h) (h := h) hzt
        have hg_deriv : deriv g t = inner ℝ (hessian F (z + t • h) h) h := by
          rw [hg_hasDerivAt.deriv]
        have hhess_eq : inner ℝ h (hessian F (z + t • h) h) = deriv g t := by
          rw [real_inner_comm, hg_deriv]
        simpa [g, hhess_eq] using hquad
      have hgt_sq_pos : 0 < (g t) ^ (2 : ℕ) := sq_pos_iff.mpr hgt_pos.ne'
      have hbase : 1 / (ν : ℝ) ≤ deriv g t / (g t) ^ (2 : ℕ) := by
        refine (_root_.le_div_iff₀ hgt_sq_pos).2 ?_
        have hdiv :
            (g t) ^ (2 : ℕ) / (ν : ℝ) ≤ deriv g t := by
          exact (_root_.div_le_iff₀ hν_pos).2 (by simpa [mul_comm] using hsq)
        simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv
      rw [(hq_hasDerivAt t ht).deriv]
      calc
        -(deriv g t) / (g t) ^ (2 : ℕ) + 1 / (ν : ℝ)
            = 1 / (ν : ℝ) - deriv g t / (g t) ^ (2 : ℕ) := by ring
        _ ≤ 0 := sub_nonpos.mpr hbase
    have hq_antitone : AntitoneOn q (Set.Ici (0 : ℝ)) := by
      -- The correction `1 / g + t / ν` has nonpositive derivative, hence decreases on the ray.
      refine antitoneOn_of_deriv_nonpos (convex_Ici (0 : ℝ)) hq_cont ?_ ?_
      · simpa [interior_Ici] using hq_diff
      · simpa [interior_Ici] using hq_deriv_nonpos
    let T : ℝ := (ν : ℝ) / (g 0) + 1
    have hT_nonneg : 0 ≤ T := by
      dsimp [T]
      positivity
    have hq_upper : q T ≤ q 0 := by
      exact hq_antitone (show (0 : ℝ) ∈ Set.Ici (0 : ℝ) by simp)
        (show T ∈ Set.Ici (0 : ℝ) by simpa [T] using hT_nonneg) hT_nonneg
    have hq_lower : T / (ν : ℝ) < q T := by
      have hgt_pos : 0 < g T := hg_pos T (by simpa [T] using hT_nonneg)
      dsimp [q]
      have hrecip_pos : 0 < (g T)⁻¹ := inv_pos.mpr hgt_pos
      linarith
    have hbad : T / (ν : ℝ) < 1 / (g 0) := by
      have hq_upper' : q T ≤ 1 / g 0 := by
        simpa [q] using hq_upper
      exact lt_of_lt_of_le hq_lower hq_upper'
    have hT_eval : T / (ν : ℝ) = 1 / (g 0) + 1 / (ν : ℝ) := by
      dsimp [T]
      field_simp [hν_pos.ne', hg0_pos'.ne']
    have hν_inv_pos : 0 < 1 / (ν : ℝ) := one_div_pos.mpr hν_pos
    rw [hT_eval] at hbad
    linarith

/-- Helper for Corollary 5.3.2: either the whole backward ray from `x` stays in the domain, or
the first obstruction lies on the frontier. -/
private theorem backward_frontier_or_backward_ray
    (hF : IsSelfConcordantBarrierOnWith dom ν F) (hx : x ∈ dom) {h : E} :
    (∀ τ : ℝ, 0 ≤ τ → x - τ • h ∈ dom) ∨ ∃ τ : ℝ, 0 < τ ∧ x - τ • h ∈ frontier dom := by
  classical
  let line : ℝ → E := fun τ ↦ x - τ • h
  have hline_cont : Continuous line := by
    simpa [line, sub_eq_add_neg] using
      (continuous_const.add
        (continuous_id.smul (continuous_const : Continuous fun _ : ℝ ↦ (-h : E))))
  by_cases hfull : ∀ τ : ℝ, 0 ≤ τ → x - τ • h ∈ dom
  · exact Or.inl hfull
  · right
    push Not at hfull
    rcases hfull with ⟨τbad, hτbad_nonneg, hτbad_not_mem⟩
    let S : Set ℝ := {τ : ℝ | 0 ≤ τ ∧ x - τ • h ∈ dom}
    have hS_nonempty : S.Nonempty := by
      refine ⟨0, ?_⟩
      simp [S, hx]
    have hS_bdd : BddAbove S := by
      refine ⟨τbad, ?_⟩
      intro s hs
      rcases hs with ⟨hs_nonneg, hs_mem⟩
      by_contra hs_gt
      have hs_pos : 0 < s := lt_of_le_of_lt hτbad_nonneg (lt_of_not_ge hs_gt)
      have hfrac : τbad / s ∈ Set.Icc (0 : ℝ) 1 := by
        refine ⟨div_nonneg hτbad_nonneg hs_pos.le, ?_⟩
        field_simp [hs_pos.ne']
        linarith [lt_of_not_ge hs_gt]
      have hsegment :
          x + (τbad / s) • ((x - s • h) - x) ∈ dom :=
        hF.toIsStandardSelfConcordantOn.convex_domain.add_smul_sub_mem hx hs_mem hfrac
      have hs_ne : s ≠ 0 := hs_pos.ne'
      have hmul : (τbad / s) * s = τbad := by
        field_simp [hs_ne]
      have hrewrite :
          x + (τbad / s) • ((x - s • h) - x) = x - τbad • h := by
        calc
          x + (τbad / s) • ((x - s • h) - x)
              = x - (((τbad / s) * s) • h) := by
                  simp [sub_eq_add_neg, smul_smul, mul_comm]
          _ = x - τbad • h := by rw [hmul]
      exact hτbad_not_mem (hrewrite ▸ hsegment)
    let τ0 : ℝ := sSup S
    have hτ0_closure : τ0 ∈ closure S :=
      csSup_mem_closure hS_nonempty hS_bdd
    have hτ0_nonneg : 0 ≤ τ0 := by
      exact le_csSup hS_bdd (by simp [S, hx])
    have hopen : IsOpen dom := hF.toIsStandardSelfConcordantOn.isOpen_domain
    have hzero_mem : x - (0 : ℝ) • h ∈ dom := by
      simpa using hx
    have hpreimage : {τ : ℝ | line τ ∈ dom} ∈ nhds (0 : ℝ) := by
      exact hline_cont.continuousAt.preimage_mem_nhds (hopen.mem_nhds hzero_mem)
    rcases Metric.mem_nhds_iff.mp hpreimage with ⟨ε, hε_pos, hε_ball⟩
    let δ : ℝ := ε / 2
    have hδ_pos : 0 < δ := by
      dsimp [δ]
      positivity
    have hδ_mem : x - δ • h ∈ dom := by
      apply hε_ball
      rw [Metric.mem_ball, Real.dist_eq]
      have hδ_lt : δ < ε := by
        dsimp [δ]
        linarith
      simpa [abs_of_nonneg hδ_pos.le] using hδ_lt
    have hδ_in_S : δ ∈ S := ⟨hδ_pos.le, hδ_mem⟩
    have hτ0_pos : 0 < τ0 := lt_of_lt_of_le hδ_pos (le_csSup hS_bdd hδ_in_S)
    have hτ0_closure_dom : x - τ0 • h ∈ closure dom := by
      have hmaps : Set.MapsTo (fun τ : ℝ ↦ x - τ • h) S dom := by
        intro τ hτ
        exact hτ.2
      exact map_mem_closure (f := line) hline_cont hτ0_closure hmaps
    have hτ0_not_mem : x - τ0 • h ∉ dom := by
      intro hτ0_mem
      have hpreimage0 : {τ : ℝ | line τ ∈ dom} ∈ nhds τ0 := by
        exact (hline_cont.continuousAt).preimage_mem_nhds (hopen.mem_nhds hτ0_mem)
      rcases Metric.mem_nhds_iff.mp hpreimage0 with ⟨ε0, hε0_pos, hε0_ball⟩
      let τ1 : ℝ := τ0 + ε0 / 2
      have hτ1_nonneg : 0 ≤ τ1 := by
        dsimp [τ1]
        positivity
      have hτ1_mem : x - τ1 • h ∈ dom := by
        apply hε0_ball
        rw [Metric.mem_ball, Real.dist_eq]
        have hhalf_nonneg : 0 ≤ ε0 / 2 := by positivity
        have hhalf_lt : ε0 / 2 < ε0 := by linarith
        rw [show τ1 - τ0 = ε0 / 2 by simp [τ1], abs_of_nonneg hhalf_nonneg]
        exact hhalf_lt
      have hτ1_in_S : τ1 ∈ S := ⟨hτ1_nonneg, hτ1_mem⟩
      have hτ1_le : τ1 ≤ τ0 := le_csSup hS_bdd hτ1_in_S
      have : τ0 + ε0 / 2 ≤ τ0 := by simpa [τ1] using hτ1_le
      linarith
    refine ⟨τ0, hτ0_pos, ?_⟩
    -- The supremum point is in the closure but not in the open domain, hence on the frontier.
    rw [frontier, hopen.interior_eq]
    exact ⟨hτ0_closure_dom, hτ0_not_mem⟩

/-- Helper for Corollary 5.3.2: if both the forward and backward rays through `x` stay in the
domain, then both the gradient pairing and the Hessian pairing in direction `h` vanish at `x`. -/
private theorem hessian_pairing_eq_zero_of_two_sided_recession
    (hF : IsSelfConcordantBarrierOnWith dom ν F)
    {x h : E}
    (hforward : ∀ τ : ℝ, 0 ≤ τ → x + τ • h ∈ dom)
    (hbackward : ∀ τ : ℝ, 0 ≤ τ → x - τ • h ∈ dom)
    (hx : x ∈ dom) :
    inner ℝ (∇ F x) h = 0 ∧ inner ℝ h (hessian F x h) = 0 := by
  let g : ℝ → ℝ := fun t ↦ inner ℝ (∇ F (x + t • h)) h
  have hforward_nonpos :
      inner ℝ (∇ F x) h ≤ 0 :=
    inner_gradient_nonpos_of_recession_direction_aux (hF := hF) (z := x) (h := h) hforward hx
  have hbackward_nonpos :
      inner ℝ (∇ F x) (-h) ≤ 0 := by
    have hbackward_forward : ∀ τ : ℝ, 0 ≤ τ → x + τ • (-h) ∈ dom := by
      intro τ hτ
      simpa [sub_eq_add_neg] using hbackward τ hτ
    exact
      inner_gradient_nonpos_of_recession_direction_aux
        (hF := hF) (z := x) (h := -h) hbackward_forward hx
  have hforward_nonneg : 0 ≤ inner ℝ (∇ F x) h := by
    exact neg_nonpos.mp <| by simpa [inner_neg_right] using hbackward_nonpos
  have hgrad_zero : inner ℝ (∇ F x) h = 0 := le_antisymm hforward_nonpos hforward_nonneg
  constructor
  · exact hgrad_zero
  · have hquad_nonneg : 0 ≤ inner ℝ h (hessian F x h) :=
      hF.toIsStandardSelfConcordantOn.hessian_posSemidef hx h
    by_contra hhess_zero
    have hhess_pos : 0 < inner ℝ h (hessian F x h) := by
      exact lt_of_le_of_ne hquad_nonneg (by simpa [eq_comm] using hhess_zero)
    have hderiv0 :
        HasDerivAt g (inner ℝ (hessian F x h) h) 0 :=
      by
        simpa [g] using
          gradient_pairing_line_hasDerivAt
            (hF := hF) (z := x) (h := h) (t := 0) (by simpa using hx)
    have hderiv0_pos : 0 < deriv g 0 := by
      rw [hderiv0.deriv]
      simpa [g, real_inner_comm] using hhess_pos
    have hsign :
        {t : ℝ | SignType.sign (g t) = SignType.sign t} ∈ nhds (0 : ℝ) := by
      have hsign_eventually :=
        eventually_nhdsWithin_sign_eq_of_deriv_pos
          (f := g) hderiv0_pos (by simpa [g] using hgrad_zero)
      simpa using
        hsign_eventually
    rcases Metric.mem_nhds_iff.mp hsign with ⟨ε, hε_pos, hε_ball⟩
    let t : ℝ := ε / 2
    have ht_pos : 0 < t := by
      dsimp [t]
      positivity
    have ht_mem_ball : t ∈ Metric.ball (0 : ℝ) ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      rw [sub_zero, abs_of_nonneg ht_pos.le]
      dsimp [t]
      linarith
    have hsign_t : SignType.sign (g t) = SignType.sign t := hε_ball ht_mem_ball
    have hgt_pos : 0 < g t := by
      have : SignType.sign (g t) = 1 := by simpa [sign_pos ht_pos] using hsign_t
      exact sign_eq_one_iff.mp this
    have hxt : x + t • h ∈ dom := hforward t ht_pos.le
    have hshift_forward : ∀ τ : ℝ, 0 ≤ τ → (x + t • h) + τ • h ∈ dom := by
      intro τ hτ
      have hsum : 0 ≤ t + τ := add_nonneg ht_pos.le hτ
      simpa [add_assoc, add_smul] using hforward (t + τ) hsum
    have hshift_nonpos :
        inner ℝ (∇ F (x + t • h)) h ≤ 0 :=
      inner_gradient_nonpos_of_recession_direction_aux
        (hF := hF) (z := x + t • h) (h := h) hshift_forward hxt
    exact not_lt_of_ge hshift_nonpos hgt_pos

-- Proof sketch: use inequality `(5.3.10)` to show that every recession direction is a
-- nonascent direction for a self-concordant barrier. If the backward ray from `x` in direction
-- `h` hits `frontier dom` at finite distance, apply the owner theorem
-- `IsSelfConcordantOnWith.hessianLocalNorm_le_neg_gradient_inner_of_recession_direction` to the
-- inherited standard self-concordant structure with parameter `1`; if `dom` contains the whole
-- line `x + ℝ • h`, then `F` is constant along that line and both sides vanish.
/-- Corollary 5.3.2: if `F` is a `ν`-self-concordant barrier on `dom` and `h` is a recession
direction of `dom`, then at every `x ∈ dom` the Hessian local norm of `h` is bounded by the
pairing of `h` with the negative gradient. -/
theorem hessianLocalNorm_le_neg_gradient_inner_of_recession_direction
    (hF : IsSelfConcordantBarrierOnWith dom ν F)
    (hrecession : ∀ ⦃y : E⦄, y ∈ dom → ∀ τ : ℝ, 0 ≤ τ → y + τ • h ∈ dom)
    (hx : x ∈ dom)
    :
    ‖h‖[F; x] ≤ inner ℝ (-∇ F x) h := by
  let hself : IsSelfConcordantOnWith dom 1 F := hF.toIsStandardSelfConcordantOn
  have hnonascent :
      ∀ ⦃y : E⦄, y ∈ dom → inner ℝ (∇ F y) h ≤ 0 := by
    intro y hy
    exact
      inner_gradient_nonpos_of_recession_direction_aux
        (hF := hF) (z := y) (h := h) (fun τ hτ ↦ hrecession hy τ hτ) hy
  rcases backward_frontier_or_backward_ray (hF := hF) (x := x) (h := h) hx with
    hbackward | ⟨τ, hτ_pos, hτ_frontier⟩
  · have hvanish :=
      hessian_pairing_eq_zero_of_two_sided_recession
        (hF := hF) (x := x) (h := h)
        (fun τ hτ ↦ hrecession hx τ hτ) hbackward hx
    rcases hvanish with ⟨hgrad_zero, hhess_zero⟩
    have hnorm_zero : ‖h‖[F; x] = 0 := by
      -- In the full-line case, the local norm collapses because the Hessian pairing vanishes.
      rw [hessianLocalNorm_def, hhess_zero]
      simp
    -- The right-hand side vanishes as well because the gradient pairing is zero.
    simp [hnorm_zero, inner_neg_left, hgrad_zero]
  · -- In the frontier case, reduce to the Chapter 5 self-concordant owner theorem with `M_f = 1`.
    simpa using
      hself.hessianLocalNorm_le_neg_gradient_inner_of_recession_direction
        (hMf := by norm_num)
        hrecession hx ⟨τ, hτ_pos, hτ_frontier⟩ hnonascent

-- Proof sketch: combine the owner-level local-norm bound above with the nonnegativity of the
-- Hessian local norm. This turns the recession-direction estimate into a direct nonpositivity
-- statement for the gradient pairing itself.
/-- For a self-concordant barrier, the gradient pairing with any recession direction of the
domain is nonpositive. -/
theorem inner_gradient_nonpos_of_recession_direction
    (hF : IsSelfConcordantBarrierOnWith dom ν F)
    (hrecession : ∀ ⦃y : E⦄, y ∈ dom → ∀ τ : ℝ, 0 ≤ τ → y + τ • h ∈ dom)
    (hx : x ∈ dom)
    :
    inner ℝ (∇ F x) h ≤ 0 := by
  have hbound :=
    hF.hessianLocalNorm_le_neg_gradient_inner_of_recession_direction hrecession hx
  have hneg : 0 ≤ inner ℝ (-∇ F x) h :=
    le_trans (hessianLocalNorm_nonneg F x h) hbound
  exact neg_nonneg.mp <| by simpa [inner_neg_left] using hneg

end

end IsSelfConcordantBarrierOnWith

end
