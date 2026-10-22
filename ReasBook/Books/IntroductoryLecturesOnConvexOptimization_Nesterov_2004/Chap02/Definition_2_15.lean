/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_4_19
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_14
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_12

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Primary domain: strong convexity on convex subsets of a complete real inner-product space,
expressed through intrinsic Loewner lower bounds on the Hessian operator.

Sampled owner-style declarations before refining this file:
* project `hessian` in `Definition_1_4_16`
* mathlib `StrongConvexOn`
* project `strongConvexOnWith_normSeminorm_iff` in `Definition_2_14`
* project `interior_lower_tangent_quadratic_iff_hessian_quadratic_form_lower_bound` in
  `Theorem_2_12`

Best owner abstraction on the intrinsic Hilbert-space layer:
* `StrongConvexOn Q μ f`

Primitive data:
* the convex set `Q` with nonempty interior
* the parameter `μ > 0`
* continuity of `f` on `Q`
* `C²` regularity of `f` on `interior Q`

Derived API:
* the pointwise Loewner lower bound `μ • id ℝ E ≤ hessian f x`, obtained by rewriting the
  quadratic-form criterion already owned by `Theorem_2_12`
* the ambient-norm bridge back to the chapter source-facing owner
  `StrongConvexOnWith (normSeminorm ℝ E) μ Q f`

Source/core/bridge triage:
* source-facing: the intrinsic Hessian characterization of strong convexity
* core/canonical: `StrongConvexOn Q μ f`
* bridge/view: the comparison with `StrongConvexOnWith (normSeminorm ℝ E) μ Q f`
-/

section

variable {μ : ℝ} {Q : Set E} {f : E → ℝ}
variable (hμ : 0 < μ) (hQ_conv : Convex ℝ Q) (hQ_int : (interior Q).Nonempty)
variable (hf_cont : ContinuousOn f Q) (hf_C2 : ContDiffOn ℝ 2 f (interior Q))

-- Proof sketch: rewrite `μ • id ≤ H` as nonnegativity of `H - μ • id` using the Loewner order
-- from `ContinuousLinearMap.le_def`, then use `ContinuousLinearMap.nonneg_iff_isPositive` and the
-- self-adjointness of the Hessian of a `C²` real function to identify positivity of
-- `H - μ • id` with nonnegativity of its quadratic form. Combine this intrinsic operator
-- reformulation with `interior_lower_tangent_quadratic_iff_hessian_quadratic_form_lower_bound`
-- and the ambient-norm bridge `strongConvexOnWith_normSeminorm_iff`.

/-- Helper for Definition 2.15: at an interior point, the Loewner lower bound on the Hessian is
equivalent to the corresponding quadratic-form inequality. -/
lemma hessian_loewner_lower_bound_iff_quadratic_form_lower_bound
    (hμ : 0 < μ) (hf_C2 : ContDiffOn ℝ 2 f (interior Q))
    {x : E} (hx : x ∈ interior Q) :
    μ • (1 : E →L[ℝ] E) ≤ hessian f x ↔
      ∀ h : E, μ * ‖h‖ ^ (2 : ℕ) ≤ inner ℝ (hessian f x h) h := by
  -- Rewrite the order relation as positivity of the shifted Hessian operator.
  rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_iff]
  constructor
  · intro hshift h
    -- The quadratic form of the shifted operator is exactly the Hessian form minus `μ ‖h‖²`.
    have hh : 0 ≤ inner ℝ ((hessian f x - μ • (1 : E →L[ℝ] E)) h) h := hshift.2 h
    simpa [inner_sub_left, inner_smul_left, inner_self_eq_norm_sq_to_K, mul_assoc, mul_left_comm,
      mul_comm] using hh
  · intro hquad
    -- Symmetry comes from the `C²` Hessian symmetry and the identity operator is symmetric.
    refine ⟨?_, ?_⟩
    · exact
        (fderiv_gradient_isSymmetric_of_contDiffAt
          (hf_C2.contDiffAt (isOpen_interior.mem_nhds hx))).sub
          (ContinuousLinearMap.isPositive_one.smul_of_nonneg hμ.le).isSymmetric
    · intro h
      -- The assumed quadratic-form bound rewrites directly to positivity of `∇²f(x) - μ id`.
      have hh : μ * ‖h‖ ^ (2 : ℕ) ≤ inner ℝ (hessian f x h) h := hquad h
      simpa [inner_sub_left, inner_smul_left, inner_self_eq_norm_sq_to_K, mul_assoc,
        mul_left_comm, mul_comm] using sub_nonneg.mpr hh

/-- Helper for Definition 2.15: strong convexity on `Q` is equivalent to the interior Hessian
quadratic-form lower bound. -/
lemma strongConvexOn_iff_hessian_quadratic_form_lower_bound
    (hμ : 0 < μ) (hQ_conv : Convex ℝ Q) (hQ_int : (interior Q).Nonempty)
    (hf_cont : ContinuousOn f Q) (hf_C2 : ContDiffOn ℝ 2 f (interior Q)) :
    StrongConvexOn Q μ f ↔
      ∀ x ∈ interior Q, ∀ h : E, μ * ‖h‖ ^ (2 : ℕ) ≤ inner ℝ (hessian f x h) h := by
  constructor
  · intro hstrong
    -- Strong convexity gives the corrected tangent inequality at every interior base point.
    have hlower :
        ∀ x : E, x ∈ interior Q → ∀ y : E, y ∈ Q →
          f y ≥ f x + inner ℝ (∇ f x) (y - x) + (μ / 2) * ‖y - x‖ ^ (2 : ℕ) := by
      intro x hx y hy
      have hxQ : x ∈ Q := interior_subset hx
      have hC2x : ContDiffAt ℝ 2 f x := hf_C2.contDiffAt (isOpen_interior.mem_nhds hx)
      have hdiffx : DifferentiableAt ℝ f x :=
        (hC2x.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).differentiableAt one_ne_zero
      have hgradx : HasGradientAt f (∇ f x) x := hdiffx.hasGradientAt
      exact
        StrongConvexOn.lower_tangent_quadratic_of_hasGradientAt
          (hf := hstrong) hxQ hy hgradx
    -- Theorem 2.12 converts the lower tangent inequality into the Hessian lower bound.
    simpa using
      (interior_lower_tangent_quadratic_iff_hessian_quadratic_form_lower_bound
        (p := normSeminorm ℝ E) (Q := Q) (f := f) μ hQ_conv hf_cont hf_C2).1 hlower
  · intro hquad
    -- First recover strong convexity on the open owner domain `interior Q`.
    have hstrongWith_int : StrongConvexOnWith (normSeminorm ℝ E) μ (interior Q) f := by
      refine
        (StrongConvexOnWith.iff_hessian_quadratic_form_lower_bound
          (p := normSeminorm ℝ E) (U := interior Q) (f := f)
          hμ isOpen_interior hQ_conv.interior hf_C2).2 ?_
      simpa using hquad
    have hstrong_int : StrongConvexOn (interior Q) μ f := by
      exact (strongConvexOnWith_normSeminorm_iff.mp hstrongWith_int).2
    rcases hQ_int with ⟨x₀, hx₀⟩
    have hx₀Q : x₀ ∈ Q := interior_subset hx₀
    refine ⟨hQ_conv, ?_⟩
    intro x hx y hy a b ha hb hab
    let xt : ℝ → E := fun t ↦ (1 - t) • x + t • x₀
    let yt : ℝ → E := fun t ↦ (1 - t) • y + t • x₀
    let zt : ℝ → E := fun t ↦ a • xt t + b • yt t
    let corr : ℝ → ℝ := fun t ↦ ((a * b) * (μ / 2)) * ‖xt t - yt t‖ ^ (2 : ℕ)
    let ψ : ℝ → ℝ := fun t ↦ a * f (xt t) + b * f (yt t) - corr t - f (zt t)
    have hxtQ : Set.MapsTo xt (Set.Icc (0 : ℝ) 1) Q := by
      intro t ht
      exact hQ_conv hx hx₀Q (sub_nonneg.mpr ht.2) ht.1 (by linarith)
    have hytQ : Set.MapsTo yt (Set.Icc (0 : ℝ) 1) Q := by
      intro t ht
      exact hQ_conv hy hx₀Q (sub_nonneg.mpr ht.2) ht.1 (by linarith)
    have hztQ : Set.MapsTo zt (Set.Icc (0 : ℝ) 1) Q := by
      intro t ht
      exact hQ_conv (hxtQ ht) (hytQ ht) ha hb hab
    have hxt_int : ∀ t ∈ Set.Ioc (0 : ℝ) 1, xt t ∈ interior Q := by
      intro t ht
      exact hQ_conv.combo_self_interior_mem_interior hx hx₀ (sub_nonneg.mpr ht.2) ht.1
        (by linarith)
    have hyt_int : ∀ t ∈ Set.Ioc (0 : ℝ) 1, yt t ∈ interior Q := by
      intro t ht
      exact hQ_conv.combo_self_interior_mem_interior hy hx₀ (sub_nonneg.mpr ht.2) ht.1
        (by linarith)
    have hzt_int : ∀ t ∈ Set.Ioc (0 : ℝ) 1, zt t ∈ interior Q := by
      intro t ht
      exact hstrong_int.1 (hxt_int t ht) (hyt_int t ht) ha hb hab
    have hxt_cont : Continuous xt := by
      simpa [xt] using
        ((continuous_const.sub continuous_id).smul continuous_const).add
          (continuous_id.smul continuous_const)
    have hyt_cont : Continuous yt := by
      simpa [yt] using
        ((continuous_const.sub continuous_id).smul continuous_const).add
          (continuous_id.smul continuous_const)
    have hzt_cont : Continuous zt := by
      simpa [zt] using (continuous_const.smul hxt_cont).add (continuous_const.smul hyt_cont)
    have hcorr_cont : Continuous corr := by
      simpa [corr] using (((hxt_cont.sub hyt_cont).norm.pow (2 : ℕ)).const_mul
        ((a * b) * (μ / 2)))
    have hψ_cont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1) := by
      have hfx_cont : ContinuousOn (fun t ↦ f (xt t)) (Set.Icc (0 : ℝ) 1) :=
        hf_cont.comp hxt_cont.continuousOn hxtQ
      have hfy_cont : ContinuousOn (fun t ↦ f (yt t)) (Set.Icc (0 : ℝ) 1) :=
        hf_cont.comp hyt_cont.continuousOn hytQ
      have hfz_cont : ContinuousOn (fun t ↦ f (zt t)) (Set.Icc (0 : ℝ) 1) :=
        hf_cont.comp hzt_cont.continuousOn hztQ
      -- The boundary extension is a one-parameter limit of the interior strong-convexity gap.
      simpa [ψ] using
        (((hfx_cont.const_mul a).add (hfy_cont.const_mul b)).sub hcorr_cont.continuousOn).sub
          hfz_cont
    have hψ_nonneg : ∀ t ∈ Set.Ioc (0 : ℝ) 1, 0 ≤ ψ t := by
      intro t ht
      have hstrong_t :
          f (zt t) ≤
            a * f (xt t) + b * f (yt t) -
              a * b * ((μ / 2) * ‖xt t - yt t‖ ^ (2 : ℕ)) :=
        hstrong_int.2 (hxt_int t ht) (hyt_int t ht) ha hb hab
      have hstrong_t' : f (zt t) ≤ a * f (xt t) + b * f (yt t) - corr t := by
        simpa [corr, mul_assoc, mul_left_comm, mul_comm] using hstrong_t
      exact sub_nonneg.mpr hstrong_t'
    have hψ_tendsto :
        Filter.Tendsto ψ (nhdsWithin 0 (Set.Ioc (0 : ℝ) 1)) (nhds (ψ 0)) := by
      have hcont0 : ContinuousWithinAt ψ (Set.Icc (0 : ℝ) 1) 0 :=
        hψ_cont.continuousWithinAt (by simp)
      exact tendsto_nhdsWithin_mono_left (f := ψ) (a := 0)
        (s := Set.Ioc (0 : ℝ) 1) (t := Set.Icc (0 : ℝ) 1)
        (by intro t ht; exact ⟨ht.1.le, ht.2⟩) hcont0.tendsto
    have hneBot : Filter.NeBot (nhdsWithin 0 (Set.Ioc (0 : ℝ) 1)) := by
      have hclosure : (0 : ℝ) ∈ closure (Set.Ioc (0 : ℝ) 1) := by
        rw [closure_Ioc zero_ne_one]
        simp
      exact mem_closure_iff_nhdsWithin_neBot.mp hclosure
    have hψ0_nonneg : 0 ≤ ψ 0 := by
      letI := hneBot
      refine ge_of_tendsto hψ_tendsto ?_
      exact Filter.mem_of_superset self_mem_nhdsWithin (fun t ht => hψ_nonneg t ht)
    -- Evaluate the limiting inequality at `t = 0` to recover the target segment inequality.
    have hψ0_le :
        f (zt 0) ≤ a * f (xt 0) + b * f (yt 0) - corr 0 := by
      exact sub_nonneg.mp hψ0_nonneg
    simpa [xt, yt, zt, corr, mul_assoc, mul_left_comm, mul_comm] using hψ0_le

/-- Definition 2.15: on a convex set with nonempty interior in a complete real inner-product
space, the intrinsic Hessian lower bound `μ • id ≤ ∇² f(x)` on `interior Q` is exactly mathlib's
canonical strong-convexity predicate, under the standard `μ > 0`, continuity, and `C²`
hypotheses. -/
theorem strongConvexOn_iff_hessian_lower_bound
    (hμ : 0 < μ) (hQ_conv : Convex ℝ Q) (hQ_int : (interior Q).Nonempty)
    (hf_cont : ContinuousOn f Q) (hf_C2 : ContDiffOn ℝ 2 f (interior Q)) :
    StrongConvexOn Q μ f ↔
      ∀ x ∈ interior Q, μ • (1 : E →L[ℝ] E) ≤ hessian f x := by
  -- Reduce the operator-valued statement to the scalar quadratic-form criterion.
  rw [strongConvexOn_iff_hessian_quadratic_form_lower_bound hμ hQ_conv hQ_int hf_cont hf_C2]
  constructor
  · intro hquad x hx
    -- The pointwise Hessian lower bound is exactly the quadratic-form bound at each interior point.
    exact
      (hessian_loewner_lower_bound_iff_quadratic_form_lower_bound
        hμ hf_C2 hx).2 (hquad x hx)
  · intro hbound x hx h
    -- Conversely, the Loewner bound immediately implies the scalar bound on every direction.
    exact
      (hessian_loewner_lower_bound_iff_quadratic_form_lower_bound
        hμ hf_C2 hx).1 (hbound x hx) h

/-- Companion bridge: the same Hessian lower bound can be read through the chapter owner
predicate `StrongConvexOnWith`, specialized to the ambient norm. -/
theorem strongConvexOnWith_normSeminorm_iff_hessian_lower_bound
    (hμ : 0 < μ) (hQ_conv : Convex ℝ Q) (hQ_int : (interior Q).Nonempty)
    (hf_cont : ContinuousOn f Q) (hf_C2 : ContDiffOn ℝ 2 f (interior Q)) :
    StrongConvexOnWith (normSeminorm ℝ E) μ Q f ↔
      ∀ x ∈ interior Q, μ • (1 : E →L[ℝ] E) ≤ hessian f x := by
  have h :=
    strongConvexOn_iff_hessian_lower_bound hμ hQ_conv hQ_int hf_cont hf_C2
  simpa [strongConvexOnWith_normSeminorm_iff, hμ] using h

end
