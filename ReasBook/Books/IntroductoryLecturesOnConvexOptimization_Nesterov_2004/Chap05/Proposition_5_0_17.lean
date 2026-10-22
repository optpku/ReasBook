/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_21
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient HessianLocalNorm SelfConcordantAuxiliaryFunction

noncomputable section

universe u

/- Proposition 5.0.17 lies in the Chapter 5 lower-remainder / self-concordance domain.

Sampled owner declarations in this domain:
* `thirdDirectionalDerivative` and `directionalSlice` from `Definition_5_0_10`, the chapter
  source-facing cubic-directional owner and its affine-line restriction;
* mathlib `iteratedDerivWithin`, the canonical one-variable owner for the auxiliary one-sided
  reverse-slice derivative on `Set.Ici (0 : ℝ)`;
* `hessianLocalNorm` and the notation `‖u‖[f; x]` from `Definition_5_1_1`, the chapter owner
  for the local Hessian norm;
* `taylor_lower_bound_of_hessian_loewner_lower` from `Theorem_5_1_8`, the nearby owner-level
  lower-remainder theorem already stated on genuine interior data.

Source/core/bridge triage:
* source-facing: the cubic bound on `thirdDirectionalDerivative f x u` at points `x ∈ dom`;
* core/canonical: the chapter owners `thirdDirectionalDerivative f x u` and `‖u‖[f; x]`;
* bridge/view: the one-sided reverse-slice derivative
  `iteratedDerivWithin 3 (directionalSlice f x (-u)) (Set.Ici (0 : ℝ)) 0`.

Primitive data:
* an open domain `dom` and a `C³` function on `dom`;
* a positive self-concordance parameter `Mf`;
* the global lower remainder inequality with the source-facing `ω` term.

Derived API:
* the auxiliary one-sided reverse-slice cubic bound along a reverse ray inside `dom`;
* the source-facing cubic estimate for `thirdDirectionalDerivative`;
* its absolute-value companion and the resulting owner-level bridge to
  `IsSelfConcordantOnWith`.

The public proposition must therefore live on `thirdDirectionalDerivative`, with the reverse-slice
within-derivative kept only as a private bridge used to encode the one-sided proof route. The
parameter must also be positive: when `Mf = 0`, the nearby Chapter 5 remainder API switches to
the quadratic remainder `r² / 2`, so the cubic conclusion below is false. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Auxiliary bridge: the one-sided third derivative at the origin of the reverse directional slice
`α ↦ f (x - α • u)` agrees with the negative of `thirdDirectionalDerivative f x u` when `f` is
genuinely `C³` at `x`. -/
-- Proof sketch: apply the one-variable chain rule three times to the map
-- `α ↦ f (x - α • u)`. Each differentiation contributes a factor `-1`, so the third derivative
-- picks up the sign `(-1)^3 = -1`, and `iteratedDerivWithin` on `Set.Ici (0 : ℝ)` agrees with the
-- unrestricted derivative at `0` because `f` is `C³` there.
omit [CompleteSpace E] in
private theorem reverse_directionalSlice_thirdDerivWithin_eq_neg
    {f : E → ℝ} {x u : E} (hf : ContDiffAt ℝ 3 f x) :
    iteratedDerivWithin 3 (directionalSlice f x (-u)) (Set.Ici (0 : ℝ)) 0 =
      -thirdDirectionalDerivative f x u := by
  -- Compose the ambient `C³` regularity with the reverse affine line.
  have hslice : ContDiffAt ℝ 3 (directionalSlice f x (-u)) 0 := by
    have hs :
        directionalSlice f x (-u) = fun α : ℝ ↦ f (x - α • u) := by
      funext α
      simp [directionalSlice, sub_eq_add_neg]
    have hline : ContDiffAt ℝ 3 (fun α : ℝ ↦ x - α • u) 0 := by
      fun_prop
    have hf_line : ContDiffAt ℝ 3 f ((fun α : ℝ ↦ x - α • u) 0) := by
      simpa using hf
    rw [hs]
    simpa [Function.comp] using hf_line.comp 0 hline
  -- On `Ici 0`, the one-sided iterated derivative agrees with the ordinary one at the endpoint.
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici (0 : ℝ)) hslice Set.self_mem_Ici]
  simpa [thirdDirectionalDerivative] using thirdDirectionalDerivative_neg f x u

/-- Helper for Proposition 5.0.17: a `C²` scalar field on a Hilbert space has a differentiable
gradient at the base point. This is the chapter-local bridge needed to identify the reverse-slice
second derivative with the Hessian quadratic form. -/
private theorem differentiableAt_gradient_of_contDiffAt_two
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    DifferentiableAt ℝ (∇ f) x := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ f) x := by
    -- A `C²` scalar field has a differentiable first derivative.
    exact
      (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))).differentiableAt
        one_ne_zero
  -- Rewrite the gradient through the Riesz map so the chain rule applies directly.
  change DifferentiableAt ℝ (fun y ↦ D (fderiv ℝ f y)) x
  exact (D.hasFDerivAt.comp x hfdiff.hasFDerivAt).differentiableAt

/-- Helper for Proposition 5.0.17: along a nonnegative scalar dilation, the Chapter 5 local norm
scales linearly. This is the reverse-ray rewrite needed to evaluate the remainder hypothesis on
`y = x - α • u`. -/
private theorem hessianLocalNorm_smul_nonneg
    {f : E → ℝ} {x u : E} {a : ℝ} (ha : 0 ≤ a) :
    ‖a • u‖[f; x] = a * ‖u‖[f; x] := by
  let q : ℝ := inner ℝ u (hessian f x u)
  have hquad : inner ℝ (a • u) (hessian f x (a • u)) = a ^ (2 : ℕ) * q := by
    -- Pull the scalar through the Hessian quadratic form before taking square roots.
    simp [q, inner_smul_left, inner_smul_right, pow_two, mul_assoc]
  by_cases hq : 0 ≤ q
  · -- When the quadratic form is nonnegative, `sqrt` is multiplicative on the scaled term.
    calc
      ‖a • u‖[f; x] = Real.sqrt (a ^ (2 : ℕ) * q) := by
        rw [hessianLocalNorm_def, hquad]
      _ = Real.sqrt (a ^ (2 : ℕ)) * Real.sqrt q := by
        rw [Real.sqrt_mul (sq_nonneg a)]
      _ = a * ‖u‖[f; x] := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ha, hessianLocalNorm_def]
  · have hq' : q ≤ 0 := le_of_not_ge hq
    have hscaled_nonpos : a ^ (2 : ℕ) * q ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg a) hq'
    -- When the quadratic form is nonpositive, both square roots collapse to `0`.
    rw [hessianLocalNorm_def, hessianLocalNorm_def, hquad,
      Real.sqrt_eq_zero_of_nonpos hscaled_nonpos, Real.sqrt_eq_zero_of_nonpos hq']
    ring

/-- Helper for Proposition 5.0.17: the reverse slice has the expected second one-sided derivative
at the origin, namely the Hessian quadratic form in the direction `u`. -/
private theorem reverse_directionalSlice_secondDerivWithin_eq_hessian_quadratic_form
    {f : E → ℝ} {x u : E} (hf : ContDiffAt ℝ 3 f x) :
    iteratedDerivWithin 2 (directionalSlice f x (-u)) (Set.Ici (0 : ℝ)) 0 =
      inner ℝ u (hessian f x u) := by
  have hslice : ContDiffAt ℝ 2 (directionalSlice f x (-u)) 0 := by
    -- Restrict the ambient `C²` regularity to the reverse affine line.
    have hs : directionalSlice f x (-u) = fun α : ℝ ↦ f (x - α • u) := by
      funext α
      simp [directionalSlice, sub_eq_add_neg]
    have hline : ContDiffAt ℝ 2 (fun α : ℝ ↦ x - α • u) 0 := by
      fun_prop
    have hfx2 : ContDiffAt ℝ 2 f ((fun α : ℝ ↦ x - α • u) 0) := by
      simpa using hf.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
    rw [hs]
    simpa using hfx2.comp 0 hline
  have hdiff : DifferentiableAt ℝ f x :=
    hf.differentiableAt (by norm_num : (3 : WithTop ℕ∞) ≠ 0)
  have hgrad : DifferentiableAt ℝ (∇ f) x :=
    differentiableAt_gradient_of_contDiffAt_two
      (hf.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
  -- The one-sided second derivative on `Ici 0` agrees with the ordinary second derivative.
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici (0 : ℝ)) hslice Set.self_mem_Ici]
  calc
    iteratedDeriv 2 (directionalSlice f x (-u)) 0 =
        secondDirectionalDerivative f x (-u) := by
          simp [secondDirectionalDerivative]
    _ = inner ℝ (-u) (hessian f x (-u)) := by
          exact secondDirectionalDerivative_eq_hessian_quadratic_form hdiff hgrad
    _ = inner ℝ u (hessian f x u) := by
          simp

/-- Helper for Proposition 5.0.17: composing a `C³` ambient function with the reverse affine ray
through `x` keeps `C³` regularity on every short closed reverse interval. -/
private theorem reverse_directionalSlice_contDiffOn_Icc
    {dom : Set E} {f : E → ℝ} {x u : E} {ε : ℝ}
    (hcont : ContDiffOn ℝ 3 f dom)
    (hline : Set.Icc (0 : ℝ) ε ⊆ (fun α : ℝ ↦ x - α • u) ⁻¹' dom) :
    ContDiffOn ℝ 3 (directionalSlice f x (-u)) (Set.Icc (0 : ℝ) ε) := by
  have hs : directionalSlice f x (-u) = fun α : ℝ ↦ f (x - α • u) := by
    funext α
    simp [directionalSlice, sub_eq_add_neg]
  have hAffine : ContDiffOn ℝ 3 (fun α : ℝ ↦ x - α • u) (Set.Icc (0 : ℝ) ε) := by
    fun_prop
  have hMapsTo : Set.MapsTo (fun α : ℝ ↦ x - α • u) (Set.Icc (0 : ℝ) ε) dom := by
    intro α hα
    exact hline hα
  -- Compose the ambient regularity with the reverse affine line.
  rw [hs]
  simpa using hcont.comp hAffine hMapsTo

/-- Helper for Proposition 5.0.17: at the left endpoint `0`, the iterated derivative on the
fixed short interval `Set.Icc 0 ε` agrees with the one-sided derivative on `Set.Ici 0`. This is
the fixed-set transport needed before comparing Taylor coefficients. -/
private theorem left_endpoint_iteratedDerivWithin_Icc_eq_Ici
    {ψ : ℝ → ℝ} {ε : ℝ} {n : ℕ} (hε : 0 < ε) (hψ : ContDiffAt ℝ n ψ 0) :
    iteratedDerivWithin n ψ (Set.Icc (0 : ℝ) ε) 0 =
      iteratedDerivWithin n ψ (Set.Ici (0 : ℝ)) 0 := by
  -- Both endpoint derivatives reduce to the ordinary iterated derivative at `0`.
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hε) hψ (by simp [hε.le]),
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici (0 : ℝ)) hψ (by simp)]

/-- Helper for Proposition 5.0.17: the degree-2 Taylor polynomial on `Set.Icc 0 ε` expands using
the one-sided endpoint derivatives on `Set.Ici 0`. -/
private theorem left_endpoint_taylorWithinEval_two_eq
    {ψ : ℝ → ℝ} {ε a : ℝ} (hε : 0 < ε) (hψ : ContDiffAt ℝ 2 ψ 0) :
    taylorWithinEval ψ 2 (Set.Icc (0 : ℝ) ε) 0 a =
      ψ 0 + a * deriv ψ 0 +
        (a ^ (2 : ℕ) / 2) * iteratedDerivWithin 2 ψ (Set.Ici (0 : ℝ)) 0 := by
  -- Expand the order-2 Taylor polynomial and rewrite both endpoint coefficients to `Set.Ici 0`.
  rw [taylorWithinEval_succ, taylorWithinEval_succ, taylor_within_zero_eval]
  simp only [Nat.factorial_zero, Nat.factorial_one, Nat.cast_zero, Nat.cast_one, zero_add,
    one_mul, sub_zero]
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hε)
      (hψ.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)) (by simp [hε.le])]
  rw [iteratedDeriv_one]
  rw [left_endpoint_iteratedDerivWithin_Icc_eq_Ici (n := 2) hε hψ]
  ring_nf

/-- Helper for Proposition 5.0.17: the degree-3 Taylor polynomial on `Set.Icc 0 ε` expands using
the one-sided endpoint derivatives on `Set.Ici 0`. -/
private theorem left_endpoint_taylorWithinEval_three_eq
    {ψ : ℝ → ℝ} {ε a : ℝ} (hε : 0 < ε) (hψ : ContDiffAt ℝ 3 ψ 0) :
    taylorWithinEval ψ 3 (Set.Icc (0 : ℝ) ε) 0 a =
      ψ 0 + a * deriv ψ 0 +
        (a ^ (2 : ℕ) / 2) * iteratedDerivWithin 2 ψ (Set.Ici (0 : ℝ)) 0 +
        (a ^ (3 : ℕ) / 6) * iteratedDerivWithin 3 ψ (Set.Ici (0 : ℝ)) 0 := by
  -- Expand once more and transport the cubic endpoint coefficient from `Icc` to `Ici`.
  rw [taylorWithinEval_succ,
    left_endpoint_taylorWithinEval_two_eq hε
      (hψ.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_ofNat, sub_zero]
  rw [left_endpoint_iteratedDerivWithin_Icc_eq_Ici (n := 3) hε hψ]
  ring_nf

/-- Helper for Proposition 5.0.17: on a fixed interval `Set.Icc 0 ε`, a cubic lower model forces
the quadratic endpoint coefficient on `Set.Ici 0` to dominate the source quantity `r²`. -/
private theorem second_derivWithin_zero_ge_of_fixed_interval_cubic_lower_model
    {ψ : ℝ → ℝ} {ε r c : ℝ}
    (hε : 0 < ε)
    (hψcont : ContDiffOn ℝ 2 ψ (Set.Icc (0 : ℝ) ε))
    (hψcontAt : ContDiffAt ℝ 2 ψ 0)
    (hlower :
      ∀ a ∈ Set.Icc (0 : ℝ) ε,
        ψ a - ψ 0 - deriv ψ 0 * a ≥
          r ^ (2 : ℕ) * a ^ (2 : ℕ) / 2 - c * a ^ (3 : ℕ) / 3) :
    r ^ (2 : ℕ) ≤ iteratedDerivWithin 2 ψ (Set.Ici (0 : ℝ)) 0 := by
  let D2 : ℝ := iteratedDerivWithin 2 ψ (Set.Ici (0 : ℝ)) 0
  let R2 : ℝ → ℝ := fun a ↦
    (ψ a - taylorWithinEval ψ 2 (Set.Icc (0 : ℝ) ε) 0 a) / a ^ (2 : ℕ)
  have hR2_tendsto : Filter.Tendsto R2 (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds 0) := by
    have hbase := Real.taylor_tendsto (s := Set.Icc (0 : ℝ) ε) (x₀ := (0 : ℝ))
      (convex_Icc (0 : ℝ) ε) (by simp [hε.le]) hψcont
    have hsmall : Set.Icc (0 : ℝ) ε ∈ nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) := by
      -- Restrict the Taylor limit from the closed interval to the right-neighborhood filter.
      refine Filter.mem_of_superset
        (Filter.inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hε))) ?_
      intro x hx
      rcases hx with ⟨hxpos, hxlt⟩
      exact ⟨le_of_lt hxpos, le_of_lt hxlt⟩
    exact Filter.Tendsto.mono_left (by simpa [R2] using hbase) <|
      (nhdsWithin_le_iff).2 hsmall
  by_contra hD2
  have hgap : 0 < r ^ (2 : ℕ) - D2 := sub_pos.mpr (lt_of_not_ge hD2)
  let η : ℝ := (r ^ (2 : ℕ) - D2) / 8
  have hηpos : 0 < η := by
    dsimp [η]
    nlinarith
  have hR2_small : ∀ᶠ a in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)), |R2 a| < η := by
    -- The Taylor remainder quotient tends to `0`, so it is eventually smaller than `η`.
    filter_upwards [hR2_tendsto.eventually (Ioo_mem_nhds (neg_lt_zero.mpr hηpos) hηpos)] with
      a ha
    simpa [abs_lt] using ha
  have hsmall_a :
      ∀ᶠ a in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        a ∈ Set.Ioo (0 : ℝ) (min ε (η / (|c| + 1))) := by
    have hupper : 0 < min ε (η / (|c| + 1)) := by
      refine lt_min hε ?_
      have hden : 0 < |c| + 1 := by positivity
      exact div_pos hηpos hden
    exact Ioo_mem_nhdsGT hupper
  have hset :
      {a : ℝ | |R2 a| < η ∧ a ∈ Set.Ioo (0 : ℝ) (min ε (η / (|c| + 1)))} ∈
        nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) := hR2_small.and hsmall_a
  obtain ⟨a, ha_mem⟩ := Filter.nonempty_of_mem hset
  rcases ha_mem with ⟨haR2, haIoo⟩
  have ha : a ∈ Set.Icc (0 : ℝ) ε := by
    refine ⟨le_of_lt haIoo.1, ?_⟩
    exact le_of_lt (lt_of_lt_of_le haIoo.2 (min_le_left _ _))
  have haneq : a ≠ 0 := ne_of_gt haIoo.1
  have hrewrite_R2 :
      R2 a = (ψ a - ψ 0 - deriv ψ 0 * a) / a ^ (2 : ℕ) - D2 / 2 := by
    -- Rewrite the degree-2 Taylor polynomial into the explicit endpoint coefficient form.
    dsimp [R2, D2]
    rw [left_endpoint_taylorWithinEval_two_eq hε hψcontAt]
    field_simp [haneq]
    ring
  have hmain : r ^ (2 : ℕ) / 2 - c * a / 3 ≤ R2 a + D2 / 2 := by
    have hmodel := hlower a ha
    have ha2pos : 0 < a ^ (2 : ℕ) := by positivity
    -- Divide the lower model by `a²` and express the quotient through `R2`.
    have hdiv :
        (r ^ (2 : ℕ) * a ^ (2 : ℕ) / 2 - c * a ^ (3 : ℕ) / 3) / a ^ (2 : ℕ) ≤
          (ψ a - ψ 0 - deriv ψ 0 * a) / a ^ (2 : ℕ) := by
      exact (div_le_div_iff_of_pos_right ha2pos).2 hmodel
    have hleft :
        (r ^ (2 : ℕ) * a ^ (2 : ℕ) / 2 - c * a ^ (3 : ℕ) / 3) / a ^ (2 : ℕ) =
          r ^ (2 : ℕ) / 2 - c * a / 3 := by
      field_simp [haneq]
    have hright :
        (ψ a - ψ 0 - deriv ψ 0 * a) / a ^ (2 : ℕ) = R2 a + D2 / 2 := by
      linarith [hrewrite_R2]
    rw [hleft, hright] at hdiv
    exact hdiv
  have hR2_upper : R2 a < η := (abs_lt.mp haR2).2
  have hca_upper : c * a / 3 < η := by
    have ha_small : a < η / (|c| + 1) := lt_of_lt_of_le haIoo.2 (min_le_right _ _)
    have hcoeff : |c| < |c| + 1 := by
      nlinarith [abs_nonneg c]
    have hcoeff_mul_lt : |c| * a < (|c| + 1) * a := by
      exact mul_lt_mul_of_pos_right hcoeff haIoo.1
    have hupper_mul : (|c| + 1) * a < η := by
      have hden : 0 < |c| + 1 := by positivity
      exact (lt_div_iff₀' hden).1 ha_small
    have habs_mul_lt : |c| * a < η := lt_trans hcoeff_mul_lt hupper_mul
    have hca_le : c * a / 3 ≤ |c| * a / 3 := by
      nlinarith [le_abs_self c, haIoo.1.le]
    have habs_div_lt : |c| * a / 3 < η := by
      nlinarith [habs_mul_lt, hηpos]
    exact lt_of_le_of_lt hca_le habs_div_lt
  have hgap_le : r ^ (2 : ℕ) - D2 ≤ 2 * R2 a + 2 * (c * a / 3) := by
    nlinarith [hmain]
  have hupper_rhs : 2 * R2 a + 2 * (c * a / 3) < 4 * η := by
    nlinarith [hR2_upper, hca_upper]
  have hgap_lt : r ^ (2 : ℕ) - D2 < 4 * η := lt_of_le_of_lt hgap_le hupper_rhs
  have hfour_lt : 4 * η < r ^ (2 : ℕ) - D2 := by
    dsimp [η]
    nlinarith [hgap]
  exact (not_lt_of_ge hgap_lt.le) hfour_lt

/-- Helper for Proposition 5.0.17: once the reverse-slice quadratic coefficient is bounded below
by `‖u‖[f; x]^2`, the Hessian identity upgrades that bound to an exact equality. -/
private theorem reverse_slice_second_coeff_eq_local_norm_sq
    {f : E → ℝ} {x u : E} {ψ : ℝ → ℝ}
    (hbound : ‖u‖[f; x] ^ (2 : ℕ) ≤ iteratedDerivWithin 2 ψ (Set.Ici (0 : ℝ)) 0)
    (hψsecond :
      iteratedDerivWithin 2 ψ (Set.Ici (0 : ℝ)) 0 = inner ℝ u (hessian f x u)) :
    iteratedDerivWithin 2 ψ (Set.Ici (0 : ℝ)) 0 = ‖u‖[f; x] ^ (2 : ℕ) := by
  have hquad_nonneg : 0 ≤ inner ℝ u (hessian f x u) := by
    rw [← hψsecond]
    exact le_trans (by positivity) hbound
  -- The reverse-slice coefficient is the Hessian quadratic form, whose square root is the local
  -- norm from the Chapter 5 owner.
  have hnorm_sq : ‖u‖[f; x] ^ (2 : ℕ) = inner ℝ u (hessian f x u) := by
    simpa [hessianLocalNorm_def] using Real.sq_sqrt hquad_nonneg
  linarith

/-- Helper for Proposition 5.0.17: after the quadratic endpoint coefficient has been identified
exactly as `r²`, the fixed-interval cubic remainder quotient yields the bound `-D₃ ≤ 2 c`. -/
private theorem third_derivWithin_zero_neg_le_of_fixed_interval_cubic_lower_model
    {ψ : ℝ → ℝ} {ε r c : ℝ}
    (hε : 0 < ε)
    (hψcont : ContDiffOn ℝ 3 ψ (Set.Icc (0 : ℝ) ε))
    (hψcontAt : ContDiffAt ℝ 3 ψ 0)
    (hlower :
      ∀ a ∈ Set.Icc (0 : ℝ) ε,
        ψ a - ψ 0 - deriv ψ 0 * a ≥
          r ^ (2 : ℕ) * a ^ (2 : ℕ) / 2 - c * a ^ (3 : ℕ) / 3)
    (hsecond :
      iteratedDerivWithin 2 ψ (Set.Ici (0 : ℝ)) 0 = r ^ (2 : ℕ)) :
    -iteratedDerivWithin 3 ψ (Set.Ici (0 : ℝ)) 0 ≤ 2 * c := by
  let D3 : ℝ := iteratedDerivWithin 3 ψ (Set.Ici (0 : ℝ)) 0
  let R3 : ℝ → ℝ := fun a ↦
    (ψ a - taylorWithinEval ψ 3 (Set.Icc (0 : ℝ) ε) 0 a) / a ^ (3 : ℕ)
  have hR3_tendsto : Filter.Tendsto R3 (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds 0) := by
    have hbase := Real.taylor_tendsto (s := Set.Icc (0 : ℝ) ε) (x₀ := (0 : ℝ))
      (convex_Icc (0 : ℝ) ε) (by simp [hε.le]) hψcont
    have hsmall : Set.Icc (0 : ℝ) ε ∈ nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) := by
      -- Restrict the Taylor limit from the fixed interval to the right-neighborhood filter.
      refine Filter.mem_of_superset
        (Filter.inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hε))) ?_
      intro x hx
      rcases hx with ⟨hxpos, hxlt⟩
      exact ⟨le_of_lt hxpos, le_of_lt hxlt⟩
    exact Filter.Tendsto.mono_left (by simpa [R3] using hbase) <|
      (nhdsWithin_le_iff).2 hsmall
  by_contra hD3
  have hgap : 0 < -D3 - 2 * c := by
    have : 2 * c < -D3 := by linarith
    linarith
  let η : ℝ := (-D3 - 2 * c) / 12
  have hηpos : 0 < η := by
    dsimp [η]
    nlinarith
  have hR3_small : ∀ᶠ a in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)), R3 a < η := by
    -- The cubic Taylor remainder quotient also tends to `0`.
    filter_upwards [hR3_tendsto.eventually (Ioo_mem_nhds (neg_lt_zero.mpr hηpos) hηpos)] with
      a ha
    exact ha.2
  have hsmall_a :
      ∀ᶠ a in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)), a ∈ Set.Ioo (0 : ℝ) ε := by
    exact Ioo_mem_nhdsGT hε
  have hset : {a : ℝ | R3 a < η ∧ a ∈ Set.Ioo (0 : ℝ) ε} ∈
      nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) := hR3_small.and hsmall_a
  obtain ⟨a, ha_mem⟩ := Filter.nonempty_of_mem hset
  rcases ha_mem with ⟨haR3, haIoo⟩
  have ha : a ∈ Set.Icc (0 : ℝ) ε := ⟨le_of_lt haIoo.1, le_of_lt haIoo.2⟩
  have haneq : a ≠ 0 := ne_of_gt haIoo.1
  have hrewrite_R3 :
      R3 a =
        (ψ a - ψ 0 - deriv ψ 0 * a - (a ^ (2 : ℕ) / 2) * r ^ (2 : ℕ)) / a ^ (3 : ℕ) - D3 / 6 := by
    -- Rewrite the degree-3 Taylor polynomial using the already identified quadratic coefficient.
    dsimp [R3, D3]
    rw [left_endpoint_taylorWithinEval_three_eq hε hψcontAt, hsecond]
    field_simp [haneq]
    ring
  have hmain : -(c / 3) - D3 / 6 ≤ R3 a := by
    have hmodel := hlower a ha
    have ha3pos : 0 < a ^ (3 : ℕ) := by
      exact pow_pos haIoo.1 _
    -- Subtract the exact quadratic term and divide by `a³`.
    have hsub :
        ψ a - ψ 0 - deriv ψ 0 * a - (a ^ (2 : ℕ) / 2) * r ^ (2 : ℕ) ≥ -(c * a ^ (3 : ℕ) / 3) := by
      nlinarith [hmodel]
    have hdiv :
        (-(c * a ^ (3 : ℕ) / 3)) / a ^ (3 : ℕ) ≤
          (ψ a - ψ 0 - deriv ψ 0 * a - (a ^ (2 : ℕ) / 2) * r ^ (2 : ℕ)) / a ^ (3 : ℕ) := by
      exact (div_le_div_iff_of_pos_right ha3pos).2 hsub
    have hleft : (-(c * a ^ (3 : ℕ) / 3)) / a ^ (3 : ℕ) = -(c / 3) := by
      field_simp [haneq]
    have hright :
        (ψ a - ψ 0 - deriv ψ 0 * a - (a ^ (2 : ℕ) / 2) * r ^ (2 : ℕ)) / a ^ (3 : ℕ) =
          R3 a + D3 / 6 := by
      linarith [hrewrite_R3]
    rw [hleft, hright] at hdiv
    linarith
  have hlower_R3 : 2 * η ≤ R3 a := by
    dsimp [η] at *
    nlinarith [hmain]
  nlinarith [hlower_R3, haR3, hηpos]

/-- Helper for Proposition 5.0.17: on the nonnegative half-line, the auxiliary function `ω`
dominates its quadratic Taylor polynomial minus the cubic correction from the source proof. -/
private theorem selfConcordantOmega_ge_quadratic_sub_cubic_of_nonneg
    (tω : Set.Ioi (-1 : ℝ)) (htω : 0 ≤ (tω : ℝ)) :
    (tω : ℝ) ^ (2 : ℕ) / 2 - (tω : ℝ) ^ (3 : ℕ) / 3 ≤ ω tω := by
  let g : ℝ → ℝ := fun s ↦ s - Real.log (1 + s) - s ^ (2 : ℕ) / 2 + s ^ (3 : ℕ) / 3
  have hg_hasDerivAt :
      ∀ s : ℝ, 0 ≤ s → HasDerivAt g (1 - 1 / (1 + s) - s + s ^ (2 : ℕ)) s := by
    intro s hs0
    have hs1_ne : 1 + s ≠ 0 := by
      linarith
    have hω_hasDeriv :
        HasDerivAt (fun y : ℝ ↦ y - Real.log (1 + y)) (1 - (1 + s)⁻¹) s := by
      -- Differentiate the explicit formula for `ω` directly on the nonnegative half-line.
      simpa using
        (hasDerivAt_id s).sub
          ((Real.hasDerivAt_log hs1_ne).comp s ((hasDerivAt_id s).const_add 1))
    have hsq_hasDeriv :
        HasDerivAt (fun y : ℝ ↦ y ^ (2 : ℕ) / 2) s s := by
      simpa [pow_two, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (((hasDerivAt_id s).pow 2).div_const (2 : ℝ))
    have hcube_hasDeriv :
        HasDerivAt (fun y : ℝ ↦ y ^ (3 : ℕ) / 3) (s ^ (2 : ℕ)) s := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (((hasDerivAt_id s).pow 3).div_const (3 : ℝ))
    -- Combining the three elementary derivatives gives the derivative of the cubic comparison
    -- function used in the source proof.
    change HasDerivAt
      (fun y : ℝ ↦ (y - Real.log (1 + y)) - y ^ (2 : ℕ) / 2 + y ^ (3 : ℕ) / 3)
      (1 - 1 / (1 + s) - s + s ^ (2 : ℕ)) s
    convert (hω_hasDeriv.sub hsq_hasDeriv).add hcube_hasDeriv using 1
    ring_nf
  have hg_cont : ContinuousOn g (Set.Ici (0 : ℝ)) := by
    intro s hs
    -- The scalar comparison function is smooth on `Ici 0` because the logarithm sees `1 + s > 0`.
    exact (hg_hasDerivAt s (by simpa using hs)).continuousAt.continuousWithinAt
  have hg_diff : DifferentiableOn ℝ g (Set.Ioi (0 : ℝ)) := by
    intro s hs
    -- Differentiate the explicit scalar model term-by-term on the open half-line.
    have hs0 : 0 ≤ s := by
      linarith [show 0 < s by simpa using hs]
    have hdiffAt : DifferentiableAt ℝ g s := (hg_hasDerivAt s hs0).differentiableAt
    exact hdiffAt.differentiableWithinAt
  have hg_deriv_nonneg : ∀ s ∈ Set.Ioi (0 : ℝ), 0 ≤ deriv g s := by
    intro s hs
    have hs0 : 0 < s := by simpa using hs
    calc
      0 ≤ s ^ (3 : ℕ) / (1 + s) := by
        exact div_nonneg (pow_nonneg hs0.le _) (by linarith)
      _ = deriv g s := by
        rw [(hg_hasDerivAt s hs0.le).deriv]
        have hs1_ne : 1 + s ≠ 0 := by
          linarith
        field_simp [hs1_ne]
        ring
  have hg_mono : MonotoneOn g (Set.Ici (0 : ℝ)) := by
    -- Nonnegativity of the derivative on the interior makes the scalar model monotone.
    refine monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ)) hg_cont ?_ ?_
    · simpa [interior_Ici] using hg_diff
    · simpa [interior_Ici] using hg_deriv_nonneg
  have hg_nonneg : 0 ≤ g tω := by
    have hzero : g 0 = 0 := by
      simp [g]
    have hmono :
        g 0 ≤ g tω := hg_mono
          (show (0 : ℝ) ∈ Set.Ici (0 : ℝ) by simp)
          (show ((tω : Set.Ioi (-1 : ℝ)) : ℝ) ∈ Set.Ici (0 : ℝ) by simpa using htω)
          (show (0 : ℝ) ≤ (tω : ℝ) by simpa using htω)
    simpa [hzero] using hmono
  have hg_rewrite :
      0 ≤ ω tω - (tω : ℝ) ^ (2 : ℕ) / 2 + (tω : ℝ) ^ (3 : ℕ) / 3 := by
    -- Re-expand `g` at the endpoint to recover the source-facing `ω` expression.
    simpa [g, selfConcordantOmega_apply] using hg_nonneg
  linarith

/-- Helper for Proposition 5.0.17: after scaling by `M_f`, the auxiliary function `ω` still
dominates the quadratic-minus-cubic scalar model from the source proof. -/
private theorem scaled_selfConcordantOmega_ge_quadratic_sub_cubic
    {Mf : NNReal} (hMf : 0 < Mf) {t : ℝ} (ht : 0 ≤ t) :
    t ^ (2 : ℕ) / 2 - (Mf : ℝ) * t ^ (3 : ℕ) / 3 ≤
      (1 / (Mf : ℝ) ^ (2 : ℕ)) *
        ω (selfConcordantOmegaArg Mf t (neg_one_lt_mf_mul_of_nonneg ht)) := by
  have hMf' : 0 < (Mf : ℝ) := by
    exact_mod_cast hMf
  let sω : Set.Ioi (-1 : ℝ) := selfConcordantOmegaArg Mf t (neg_one_lt_mf_mul_of_nonneg ht)
  have hsω_nonneg : 0 ≤ (sω : ℝ) := by
    simpa [sω] using mul_nonneg hMf'.le ht
  have hsω :
      (sω : ℝ) ^ (2 : ℕ) / 2 - (sω : ℝ) ^ (3 : ℕ) / 3 ≤ ω sω :=
    selfConcordantOmega_ge_quadratic_sub_cubic_of_nonneg sω hsω_nonneg
  have hcoeff_nonneg : 0 ≤ 1 / (Mf : ℝ) ^ (2 : ℕ) := by
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hsω hcoeff_nonneg
  have hMf_sq_ne : (Mf : ℝ) ^ (2 : ℕ) ≠ 0 := by
    positivity
  -- Divide the base scalar model by `M_f^2` and simplify the two coefficients explicitly.
  have hrewrite :
      (1 / (Mf : ℝ) ^ (2 : ℕ)) *
          (((sω : ℝ) ^ (2 : ℕ)) / 2 - ((sω : ℝ) ^ (3 : ℕ)) / 3) =
        t ^ (2 : ℕ) / 2 - (Mf : ℝ) * t ^ (3 : ℕ) / 3 := by
    have hcoe : (sω : ℝ) = (Mf : ℝ) * t := by
      simp [sω]
    rw [hcoe]
    field_simp [hMf_sq_ne]
  have hrewrite_rhs :
      (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω sω =
        (1 / (Mf : ℝ) ^ (2 : ℕ)) *
          ω (selfConcordantOmegaArg Mf t (neg_one_lt_mf_mul_of_nonneg ht)) := by
    simp [sω]
  rwa [hrewrite, hrewrite_rhs] at hscaled

/-- Helper for Proposition 5.0.17: evaluating the global lower remainder bound at
`y = x - a • u` packages the reverse ray into the scalar quadratic-minus-cubic lower model needed
for the endpoint Taylor argument. -/
private theorem reverse_slice_lower_model_on_Icc
    {dom : Set E} {Mf : NNReal} {f : E → ℝ} {x u : E} {a ε : ℝ}
    (hMf : 0 < Mf)
    (hremainder :
      ∀ ⦃y : E⦄, y ∈ dom →
        (1 / (Mf : ℝ) ^ (2 : ℕ)) *
            ω (selfConcordantOmegaArg Mf ‖y - x‖[f; x]
              (neg_one_lt_mf_mul_of_nonneg
                (hessianLocalNorm_nonneg f x (y - x)))) ≤
          f y - f x - inner ℝ (∇ f x) (y - x))
    (hline : Set.Icc (0 : ℝ) ε ⊆ (fun α : ℝ ↦ x - α • u) ⁻¹' dom)
    (hψderiv :
      deriv (directionalSlice f x (-u)) 0 = -inner ℝ (∇ f x) u)
    (ha : a ∈ Set.Icc (0 : ℝ) ε) :
    let ψ : ℝ → ℝ := directionalSlice f x (-u)
    ψ a - ψ 0 - deriv ψ 0 * a ≥
      ‖u‖[f; x] ^ (2 : ℕ) * a ^ (2 : ℕ) / 2 -
        ((Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ)) * a ^ (3 : ℕ) / 3 := by
  let ψ : ℝ → ℝ := directionalSlice f x (-u)
  have hy : x - a • u ∈ dom := hline ha
  have hnorm :
      ‖(x - a • u) - x‖[f; x] = a * ‖u‖[f; x] := by
    -- The reverse-ray increment is `-a • u`, and the local norm is even and homogeneous.
    calc
      ‖(x - a • u) - x‖[f; x] = ‖-(a • u)‖[f; x] := by simp [sub_eq_add_neg]
      _ = ‖a • u‖[f; x] := by simp
      _ = a * ‖u‖[f; x] := hessianLocalNorm_smul_nonneg (f := f) (x := x) (u := u) ha.1
  have hscalar :
      ‖(x - a • u) - x‖[f; x] ^ (2 : ℕ) / 2 -
          (Mf : ℝ) * ‖(x - a • u) - x‖[f; x] ^ (3 : ℕ) / 3 ≤
        (1 / (Mf : ℝ) ^ (2 : ℕ)) *
          ω (selfConcordantOmegaArg Mf ‖(x - a • u) - x‖[f; x]
            (neg_one_lt_mf_mul_of_nonneg
              (hessianLocalNorm_nonneg f x ((x - a • u) - x)))) := by
    exact
      scaled_selfConcordantOmega_ge_quadratic_sub_cubic
        (Mf := Mf) hMf
        (t := ‖(x - a • u) - x‖[f; x])
        (hessianLocalNorm_nonneg f x ((x - a • u) - x))
  have hgap :
      (1 / (Mf : ℝ) ^ (2 : ℕ)) *
          ω (selfConcordantOmegaArg Mf ‖(x - a • u) - x‖[f; x]
            (neg_one_lt_mf_mul_of_nonneg
              (hessianLocalNorm_nonneg f x ((x - a • u) - x)))) ≤
        ψ a - ψ 0 - deriv ψ 0 * a := by
    -- Rewrite the ambient remainder gap as the reverse-slice gap at parameter `a`.
    simpa [ψ, directionalSlice, hψderiv, sub_eq_add_neg, inner_smul_right, mul_comm, mul_left_comm,
      mul_assoc] using hremainder hy
  have hmodel :
      ‖(x - a • u) - x‖[f; x] ^ (2 : ℕ) / 2 -
          (Mf : ℝ) * ‖(x - a • u) - x‖[f; x] ^ (3 : ℕ) / 3 =
        ‖u‖[f; x] ^ (2 : ℕ) * a ^ (2 : ℕ) / 2 -
          ((Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ)) * a ^ (3 : ℕ) / 3 := by
    rw [hnorm]
    ring
  have hfinal := le_trans hscalar hgap
  rwa [hmodel] at hfinal

/- Private reverse-slice bound used to prove Proposition 5.0.17: if the lower Taylor remainder
bound holds at the base point `x`, with positive parameter `M_f`, and the reverse ray from `x` in
direction `u` stays in `dom` near `0`, then the negative one-sided third derivative of
`α ↦ f (x - α • u)` at `0` is bounded above by `2 M_f ‖u‖_x^3`. -/
private theorem reverse_directionalSlice_thirdDerivWithin_bound_of_remainder_lower_bound
    {dom : Set E} {Mf : NNReal} {f : E → ℝ} {x u : E}
    (hf : ContDiffAt ℝ 3 f x)
    (hcont : ContDiffOn ℝ 3 f dom)
    (hMf : 0 < Mf)
    (hremainder :
      ∀ ⦃y : E⦄, y ∈ dom →
        (1 / (Mf : ℝ) ^ (2 : ℕ)) *
            ω (selfConcordantOmegaArg Mf ‖y - x‖[f; x]
              (neg_one_lt_mf_mul_of_nonneg
                (hessianLocalNorm_nonneg f x (y - x)))) ≤
          f y - f x - inner ℝ (∇ f x) (y - x))
    (hline : ∃ ε > 0, Set.Icc (0 : ℝ) ε ⊆ (fun α : ℝ ↦ x - α • u) ⁻¹' dom) :
    -iteratedDerivWithin 3 (directionalSlice f x (-u)) (Set.Ici (0 : ℝ)) 0 ≤
      2 * (Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ) := by
  rcases hline with ⟨ε, hεpos, hεsub⟩
  let ψ : ℝ → ℝ := directionalSlice f x (-u)
  have hψcont : ContDiffOn ℝ 3 ψ (Set.Icc (0 : ℝ) ε) := by
    -- Restrict the ambient `C³` owner to the short reverse interval supplied by `hline`.
    simpa [ψ] using reverse_directionalSlice_contDiffOn_Icc (f := f) (x := x) (u := u) hcont hεsub
  have hψsecond :
      iteratedDerivWithin 2 ψ (Set.Ici (0 : ℝ)) 0 = inner ℝ u (hessian f x u) := by
    -- The second one-sided derivative already matches the Hessian quadratic form.
    simpa [ψ] using
      reverse_directionalSlice_secondDerivWithin_eq_hessian_quadratic_form (f := f) (x := x)
        (u := u) hf
  have hψderiv :
      deriv ψ 0 = -inner ℝ (∇ f x) u := by
    have hfx1 : DifferentiableAt ℝ f x :=
      hf.differentiableAt (by norm_num : (3 : WithTop ℕ∞) ≠ 0)
    -- Rewrite the reverse-slice derivative through the line-derivative / gradient pairing API.
    calc
      deriv ψ 0 = lineDeriv ℝ f x (-u) := rfl
      _ = fderiv ℝ f x (-u) := hfx1.lineDeriv_eq_fderiv
      _ = inner ℝ (∇ f x) (-u) := by rw [← inner_gradient_left hfx1]
      _ = -inner ℝ (∇ f x) u := by simp
  have hlower_model :
      ∀ a ∈ Set.Icc (0 : ℝ) ε,
        ψ a - ψ 0 - deriv ψ 0 * a ≥
          ‖u‖[f; x] ^ (2 : ℕ) * a ^ (2 : ℕ) / 2 -
            ((Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ)) * a ^ (3 : ℕ) / 3 := by
    intro a ha
    -- Evaluate the ambient remainder bound on the reverse ray to obtain the one-variable model.
    simpa [ψ] using
      reverse_slice_lower_model_on_Icc (f := f) (x := x) (u := u) (Mf := Mf) (ε := ε)
        hMf hremainder hεsub hψderiv ha
  have hψcontAt : ContDiffAt ℝ 3 ψ 0 := by
    -- The reverse slice is genuinely `C³` at the endpoint because the ambient map is `C³` at `x`.
    have hslice : ContDiffAt ℝ 3 (directionalSlice f x (-u)) 0 := by
      have hs : directionalSlice f x (-u) = fun α : ℝ ↦ f (x - α • u) := by
        funext α
        simp [directionalSlice, sub_eq_add_neg]
      have hline : ContDiffAt ℝ 3 (fun α : ℝ ↦ x - α • u) 0 := by
        fun_prop
      have hfx3 : ContDiffAt ℝ 3 f ((fun α : ℝ ↦ x - α • u) 0) := by
        simpa using hf
      rw [hs]
      simpa using hfx3.comp 0 hline
    simpa [ψ] using hslice
  have hψsecond_Icc :
      iteratedDerivWithin 2 ψ (Set.Icc (0 : ℝ) ε) 0 =
        iteratedDerivWithin 2 ψ (Set.Ici (0 : ℝ)) 0 := by
    -- Normalize the quadratic endpoint coefficient to the fixed one-sided derivative.
    exact left_endpoint_iteratedDerivWithin_Icc_eq_Ici (n := 2) hεpos
      (hψcontAt.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
  have hψthird_Icc :
      iteratedDerivWithin 3 ψ (Set.Icc (0 : ℝ) ε) 0 =
        iteratedDerivWithin 3 ψ (Set.Ici (0 : ℝ)) 0 := by
    -- Normalize the cubic endpoint coefficient to the fixed one-sided derivative.
    exact left_endpoint_iteratedDerivWithin_Icc_eq_Ici (n := 3) hεpos hψcontAt
  have hTaylor2 :
      ∀ a : ℝ,
        taylorWithinEval ψ 2 (Set.Icc (0 : ℝ) ε) 0 a =
          ψ 0 + a * deriv ψ 0 +
            (a ^ (2 : ℕ) / 2) * iteratedDerivWithin 2 ψ (Set.Ici (0 : ℝ)) 0 := by
    intro a
    -- This is the fixed-interval quadratic Taylor polynomial needed for the coefficient limit.
    exact left_endpoint_taylorWithinEval_two_eq hεpos
      (hψcontAt.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
  have hTaylor3 :
      ∀ a : ℝ,
        taylorWithinEval ψ 3 (Set.Icc (0 : ℝ) ε) 0 a =
          ψ 0 + a * deriv ψ 0 +
            (a ^ (2 : ℕ) / 2) * iteratedDerivWithin 2 ψ (Set.Ici (0 : ℝ)) 0 +
            (a ^ (3 : ℕ) / 6) * iteratedDerivWithin 3 ψ (Set.Ici (0 : ℝ)) 0 := by
    intro a
    -- This is the fixed-interval cubic Taylor polynomial needed for the final endpoint bound.
    exact left_endpoint_taylorWithinEval_three_eq hεpos hψcontAt
  -- Route correction: the previous attempts stalled at shrinking-interval transport. The fixed
  -- interval `Set.Icc 0 ε` now carries the full source-faithful coefficient extraction, so the
  -- remaining work is the scalar Taylor-quotient comparison on `𝓝[>] 0`.
  have hψsecond_ge :
      ‖u‖[f; x] ^ (2 : ℕ) ≤ iteratedDerivWithin 2 ψ (Set.Ici (0 : ℝ)) 0 := by
    -- First extract the quadratic endpoint coefficient from the cubic lower model.
    exact
      second_derivWithin_zero_ge_of_fixed_interval_cubic_lower_model
        (ψ := ψ) (ε := ε) (r := ‖u‖[f; x]) (c := (Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ))
        hεpos
        (hψcont.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
        (hψcontAt.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
        hlower_model
  have hψsecond_eq :
      iteratedDerivWithin 2 ψ (Set.Ici (0 : ℝ)) 0 = ‖u‖[f; x] ^ (2 : ℕ) := by
    -- Then rewrite that coefficient through the Hessian quadratic form and the local norm owner.
    exact reverse_slice_second_coeff_eq_local_norm_sq (f := f) (x := x) (u := u) (ψ := ψ)
      hψsecond_ge hψsecond
  -- Finally, the cubic Taylor quotient gives the source bound on the negative third coefficient.
  have hψthird_bound :
      -iteratedDerivWithin 3 ψ (Set.Ici (0 : ℝ)) 0 ≤
        2 * (Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ) := by
    simpa [ψ, mul_assoc] using
      (third_derivWithin_zero_neg_le_of_fixed_interval_cubic_lower_model
        (ψ := ψ) (ε := ε) (r := ‖u‖[f; x]) (c := (Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ))
        hεpos hψcont hψcontAt hlower_model hψsecond_eq)
  exact hψthird_bound

-- Proof sketch: openness of `dom` upgrades `ContDiffOn ℝ 3 f dom` to `ContDiffAt ℝ 3 f x`,
-- and provides a small two-sided ball around `x` inside `dom`; restricting that ball to the
-- reverse ray gives the private reverse-slice bound above. Rewriting the resulting one-sided
-- derivative by `reverse_directionalSlice_thirdDerivWithin_eq_neg` recovers the source-facing
-- cubic estimate on `thirdDirectionalDerivative f x u`.
/-- Proposition 5.0.17: if the global lower Taylor remainder bound from
`Theorem_5_1_8.taylor_lower_bound_of_hessian_loewner_lower` holds on an open domain `dom` for a
`C³` function `f`, with positive parameter `M_f`, then at every point `x ∈ dom` the chapter owner
`thirdDirectionalDerivative f x u` is bounded above by
`2 M_f ‖u‖_x^3`. -/
theorem thirdDirectionalDerivative_le_of_global_remainder_lower_bound
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    (hopen : IsOpen dom)
    (hcont : ContDiffOn ℝ 3 f dom)
    (hMf : 0 < Mf)
    (hremainder :
      ∀ ⦃x y : E⦄ (_ : x ∈ dom) (_ : y ∈ dom),
        (1 / (Mf : ℝ) ^ (2 : ℕ)) *
            ω (selfConcordantOmegaArg Mf ‖y - x‖[f; x]
              (neg_one_lt_mf_mul_of_nonneg
                (hessianLocalNorm_nonneg f x (y - x)))) ≤
          f y - f x - inner ℝ (∇ f x) (y - x))
    (x u : E) (hx : x ∈ dom) :
    thirdDirectionalDerivative f x u ≤
      2 * (Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ) := by
  have hf : ContDiffAt ℝ 3 f x := hcont.contDiffAt (hopen.mem_nhds hx)
  have hline :
      ∃ ε > 0, Set.Icc (0 : ℝ) ε ⊆ (fun α : ℝ ↦ x - α • u) ⁻¹' dom := by
    let g : ℝ → E := fun α ↦ x - α • u
    -- Openness of `dom` gives a neighborhood of `0` along the reverse affine line.
    have hpre : g ⁻¹' dom ∈ nhds (0 : ℝ) := by
      have hg : ContinuousAt g 0 := by
        fun_prop
      have hx0 : g 0 ∈ dom := by
        simpa [g] using hx
      simpa [g] using hg.preimage_mem_nhds (hopen.mem_nhds hx0)
    rcases Metric.mem_nhds_iff.mp hpre with ⟨δ, hδ, hδsub⟩
    refine ⟨δ / 2, by positivity, ?_⟩
    intro α hα
    have hαlt : α < δ := by
      nlinarith [hα.2, hδ]
    have hball : α ∈ Metric.ball (0 : ℝ) δ := by
      simpa [Metric.ball, Real.dist_eq, abs_of_nonneg hα.1] using hαlt
    exact hδsub hball
  have hbound :
      -iteratedDerivWithin 3 (directionalSlice f x (-u)) (Set.Ici (0 : ℝ)) 0 ≤
        2 * (Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ) :=
    reverse_directionalSlice_thirdDerivWithin_bound_of_remainder_lower_bound
      hf hcont hMf (fun hy hy_mem ↦ hremainder hx hy_mem) hline
  -- Rewrite the reverse-slice within-derivative back to the chapter owner.
  simpa [reverse_directionalSlice_thirdDerivWithin_eq_neg (f := f) (x := x) (u := u) hf] using
    hbound

/-- Under the same hypotheses as Proposition 5.0.17, the third directional derivative is bounded
in absolute value by `2 M_f ‖u‖_x^3`. This is the exact cubic field used by the chapter owner
`IsSelfConcordantOnWith`. -/
theorem thirdDirectionalDerivative_abs_le_of_global_remainder_lower_bound
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    (hopen : IsOpen dom)
    (hcont : ContDiffOn ℝ 3 f dom)
    (hMf : 0 < Mf)
    (hremainder :
      ∀ ⦃x y : E⦄ (_ : x ∈ dom) (_ : y ∈ dom),
        (1 / (Mf : ℝ) ^ (2 : ℕ)) *
            ω (selfConcordantOmegaArg Mf ‖y - x‖[f; x]
              (neg_one_lt_mf_mul_of_nonneg
                (hessianLocalNorm_nonneg f x (y - x)))) ≤
          f y - f x - inner ℝ (∇ f x) (y - x))
    (x u : E) (hx : x ∈ dom) :
    |thirdDirectionalDerivative f x u| ≤
      2 * (Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ) := by
  have hupper :
      thirdDirectionalDerivative f x u ≤
        2 * (Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ) :=
    thirdDirectionalDerivative_le_of_global_remainder_lower_bound
      hopen hcont hMf hremainder x u hx
  have hneg :
      -thirdDirectionalDerivative f x u ≤
        2 * (Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ) := by
    simpa using
      (thirdDirectionalDerivative_le_of_global_remainder_lower_bound
        hopen hcont hMf hremainder x (-u) hx)
  rw [abs_le]
  constructor
  · linarith
  · exact hupper

namespace IsSelfConcordantOnWith

/-- If the global lower Taylor remainder bound from
`Theorem_5_1_8.taylor_lower_bound_of_hessian_loewner_lower` holds on an open domain with convex
underlying set for a `C³` function with positive parameter `M_f`, then the function is
self-concordant on that domain with constant `M_f`. This is the canonical owner-level bridge from
Proposition 5.0.17 to `IsSelfConcordantOnWith`. -/
theorem of_global_remainder_lower_bound
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    (hopen : IsOpen dom)
    (hcont : ContDiffOn ℝ 3 f dom)
    (hdom : Convex ℝ dom)
    (hMf : 0 < Mf)
    (hremainder :
      ∀ ⦃x y : E⦄ (_ : x ∈ dom) (_ : y ∈ dom),
        (1 / (Mf : ℝ) ^ (2 : ℕ)) *
            ω (selfConcordantOmegaArg Mf ‖y - x‖[f; x]
              (neg_one_lt_mf_mul_of_nonneg
                (hessianLocalNorm_nonneg f x (y - x)))) ≤
          f y - f x - inner ℝ (∇ f x) (y - x)) :
    IsSelfConcordantOnWith dom Mf f where
  isOpen_domain := hopen
  contDiffOn := hcont
  convexOn := by
    have hcont₁ : ContDiffOn ℝ 1 f dom := hcont.of_le (by norm_num)
    refine (convexOn_iff_lower_tangent_plane_of_contDiffOn hdom hcont₁).2 ?_
    intro x hx y hy
    have hMf' : 0 < (Mf : ℝ) := by
      exact_mod_cast hMf
    have hgrad :
        gradientWithin f dom x = ∇ f x := by
      rw [gradientWithin, gradient]
      congr
      exact fderivWithin_eq_fderiv (hopen.uniqueDiffWithinAt hx)
        ((hcont₁.contDiffAt (hopen.mem_nhds hx)).differentiableAt_one)
    have homega_nonneg :
        0 ≤ ω (selfConcordantOmegaArg Mf ‖y - x‖[f; x]
          (neg_one_lt_mf_mul_of_nonneg
            (hessianLocalNorm_nonneg f x (y - x)))) := by
      rw [selfConcordantOmega_apply, coe_selfConcordantOmegaArg]
      have harg_nonneg : 0 ≤ (Mf : ℝ) * ‖y - x‖[f; x] := by
        exact mul_nonneg hMf'.le (hessianLocalNorm_nonneg f x (y - x))
      have hlog :
          Real.log (1 + (Mf : ℝ) * ‖y - x‖[f; x]) ≤
            (Mf : ℝ) * ‖y - x‖[f; x] := by
        have hpos : 0 < 1 + (Mf : ℝ) * ‖y - x‖[f; x] := by positivity
        simpa using Real.log_le_sub_one_of_pos hpos
      linarith
    have hgap_nonneg :
        0 ≤ f y - f x - inner ℝ (∇ f x) (y - x) := by
      have hcoeff_nonneg : 0 ≤ 1 / (Mf : ℝ) ^ (2 : ℕ) := by positivity
      exact le_trans (mul_nonneg hcoeff_nonneg homega_nonneg) (hremainder hx hy)
    have hlower :
        f y ≥ f x + inner ℝ (∇ f x) (y - x) := by
      linarith
    simpa [hgrad] using hlower
  third_deriv_bound := fun {x} hx u ↦
    thirdDirectionalDerivative_abs_le_of_global_remainder_lower_bound
      hopen hcont hMf hremainder x u hx

end IsSelfConcordantOnWith

end
