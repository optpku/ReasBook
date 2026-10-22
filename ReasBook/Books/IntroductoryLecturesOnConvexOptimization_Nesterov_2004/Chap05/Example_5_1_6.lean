/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_15
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Corollary_5_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_2_8
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient HessianLocalNorm

noncomputable section

universe u

/- Example 5.1.6 lies in the Chapter 5 self-concordance / strong-convexity / Hessian-Lipschitz
domain.

Sampled owner-style declarations:
* `StrongConvexOn`, the canonical owner for whole-space strong convexity;
* `HasLipschitzContinuousHessian` and the theorem-surface notation `f ∈ C22[L₃]` from
  `Definition_5_0_7`, the canonical chapter owner for whole-space Hessian-Lipschitz smoothness;
* `fderiv ℝ (hessian f) x u` from `Definition_5_0_8`, the canonical Chapter 5 owner for the
  directional derivative of the Hessian operator;
* `IsSelfConcordantOnWith.of_thirdDerivative_operator_le` from `Corollary_5_1_1`, the canonical
  owner-level bridge from the operator inequality to `IsSelfConcordantOnWith`;
* `IsSelfConcordantOnWith` from `Definition_5_1_1`, the stronger Chapter 5 owner that packages
  open-convex `C³` self-concordance data.

Source/core/bridge triage:
* source-facing: the Hessian-operator inequality
  `D³f(x)[u] ≤ (L₃ / (σ₂ * √σ₂)) ‖u‖_{∇² f(x)} ∇²f(x)` at a point `x`, obtained from
  `StrongConvexOn Set.univ σ2 f`, `f ∈ C22[L3]`, and the pointwise `C³` regularity needed to
  interpret `D³f(x)[u]`;
* core/canonical: `StrongConvexOn Set.univ σ2 f`, `f ∈ C22[L3]`, `fderiv ℝ (hessian f) x u`,
  `hessian f x`, and `‖u‖[f; x]`;
* bridge/view: `IsSelfConcordantOnWith.of_thirdDerivative_operator_le`, which converts this
  source-facing operator inequality into the Chapter 5 owner `IsSelfConcordantOnWith`.

Primitive data:
* the objective `f`;
* the strong-convexity parameter `σ₂`;
* the Hessian-Lipschitz constant `L₃`;
* the owner hypotheses `StrongConvexOn Set.univ σ2 f` and `f ∈ C22[L3]`;
* the pointwise regularity witness `ContDiffAt ℝ 3 f x`, needed to interpret the operator
  `fderiv ℝ (hessian f) x u` as the genuine third derivative `D³f(x)[u]`.

Derived API:
* the operator inequality
  `fderiv ℝ (hessian f) x u ≤
    ((L₃ / (σ₂ * √σ₂)) ‖u‖_{∇² f(x)}) • ∇² f(x)`;
* under the extra bridge hypothesis `ContDiff ℝ 3 f`, the Chapter 5 owner
  `IsSelfConcordantOnWith Set.univ
    (Real.toNNReal ((L3 : ℝ) / (2 * σ2 * Real.sqrt σ2))) f`.

This refinement keeps Example 5.1.6 itself at the source-facing `StrongConvexOn + C22[L₃]`
layer and exposes its main conclusion directly on the canonical Hessian owner
`fderiv ℝ (hessian f) x u`. The stronger global `C³` packaging into
`IsSelfConcordantOnWith` remains a separate bridge theorem obtained through
`IsSelfConcordantOnWith.of_thirdDerivative_operator_le`. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section

variable {f : E → ℝ} {σ2 : ℝ} {L3 : NNReal}

namespace StrongConvexOn

variable (hf_strong : StrongConvexOn Set.univ σ2 f) (hσ2 : 0 < σ2) (hf_hessian : f ∈ C22[L3])
include hf_strong hσ2 hf_hessian

omit hf_strong hσ2 hf_hessian in
/-- Helper for Example 5.1.6: a `C³` point gives the Fréchet derivative of the Hessian map at
that point. -/
private lemma hessian_hasFDerivAt_of_contDiffAt {x : E}
    (h_contDiffAt : ContDiffAt ℝ 3 f x) :
    HasFDerivAt (hessian f) (fderiv ℝ (hessian f) x) x := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfderiv_C2 : ContDiffAt ℝ 2 (fderiv ℝ f) x := by
    -- First differentiate `f` once and keep the two remaining derivatives.
    exact h_contDiffAt.fderiv_right (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)
  have hgrad_C2 : ContDiffAt ℝ 2 (∇ f) x := by
    -- Rewrite the gradient through the Riesz map before differentiating again.
    simpa [gradient, D] using D.contDiff.contDiffAt.comp x hfderiv_C2
  have hhessian_C1 : ContDiffAt ℝ 1 (hessian f) x := by
    -- One more derivative of the gradient is exactly the Hessian owner.
    simpa [hessian] using
      hgrad_C2.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  -- Convert the `C¹` regularity of the Hessian map into the required Fréchet derivative.
  exact (hhessian_C1.hasStrictFDerivAt one_ne_zero).hasFDerivAt

/-- Helper for Example 5.1.6: strong convexity on `Set.univ` gives the pointwise Hessian lower
bound `σ₂ • I ≤ ∇² f(x)`. -/
private lemma hessian_lower_bound_at_point {x : E} :
    σ2 • (1 : E →L[ℝ] E) ≤ hessian f x := by
  -- Read the whole-space strong-convexity hypothesis through the canonical Chapter 2 Hessian
  -- lower-bound characterization.
  have hiff :=
    strongConvexOn_iff_hessian_lower_bound
      (E := E) (Q := Set.univ) (f := f) hσ2 convex_univ
      (by simp)
      (by
        simpa using (hf_hessian.contDiff.continuous.continuousOn : ContinuousOn f Set.univ))
      (by simpa [interior_univ] using (hf_hessian.contDiff.contDiffOn : ContDiffOn ℝ 2 f Set.univ))
  exact (hiff.mp hf_strong) x (by simp [interior_univ])

/-- Helper for Example 5.1.6: the Hessian lower bound yields the quadratic-form comparison
`σ₂ ‖v‖² ≤ ⟪v, ∇²f(x)v⟫`. -/
private lemma hessian_quadratic_form_lower_bound_at_point {x v : E} :
    σ2 * ‖v‖ ^ (2 : ℕ) ≤ inner ℝ v (hessian f x v) := by
  -- Convert the operator lower bound into the corresponding scalar quadratic-form bound.
  have hiff :=
    hessian_loewner_lower_bound_iff_quadratic_form_lower_bound
      (E := E) (Q := Set.univ) (f := f) hσ2
      (by simpa [interior_univ] using (hf_hessian.contDiff.contDiffOn : ContDiffOn ℝ 2 f Set.univ))
      (x := x) (by simp [interior_univ])
  simpa [real_inner_comm] using (hiff.1 (hessian_lower_bound_at_point (f := f) (σ2 := σ2)
    (L3 := L3) hf_strong hσ2 hf_hessian) v)

/-- Helper for Example 5.1.6: strong convexity converts the ambient norm into the Hessian local
norm by the textbook factor `1 / √σ₂`. -/
private lemma norm_le_hessianLocalNorm_div_sqrt {x v : E} :
    ‖v‖ ≤ ‖v‖[f; x] / Real.sqrt σ2 := by
  -- Take square roots in the Hessian quadratic-form lower bound and divide by `√σ₂`.
  have hquad :
      σ2 * ‖v‖ ^ (2 : ℕ) ≤ inner ℝ v (hessian f x v) :=
    hessian_quadratic_form_lower_bound_at_point (f := f) (σ2 := σ2) (L3 := L3)
      hf_strong hσ2 hf_hessian
  have hsqrt :
      Real.sqrt σ2 * ‖v‖ ≤ ‖v‖[f; x] := by
    calc
      Real.sqrt σ2 * ‖v‖ = Real.sqrt (σ2 * ‖v‖ ^ (2 : ℕ)) := by
        rw [Real.sqrt_mul (show 0 ≤ σ2 by linarith)]
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg v)]
      _ ≤ Real.sqrt (inner ℝ v (hessian f x v)) := Real.sqrt_le_sqrt hquad
      _ = ‖v‖[f; x] := by rw [hessianLocalNorm_def]
  exact (le_div_iff₀ (Real.sqrt_pos.2 hσ2)).2 (by simpa [mul_comm] using hsqrt)

omit hf_strong hσ2 hf_hessian [CompleteSpace E] in
/-- Helper for Example 5.1.6: the affine line `s ↦ x + s • d` has derivative `d`. -/
private lemma affine_segment_hasDerivAt
    {x d : E} (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ x + s • d) d t := by
  -- Differentiate scalar multiplication and then translate by the base point.
  simpa [one_smul] using ((hasDerivAt_id t).smul_const d).const_add x

omit hf_strong hσ2 hf_hessian in
/-- Helper for Example 5.1.6: the scalar Hessian-direction pairing is the corresponding
evaluation of the third iterated derivative. -/
private lemma hessian_direction_pairing_eq_iteratedFDeriv
    {x d w v : E} (h_contDiffAt : ContDiffAt ℝ 3 f x) :
    inner ℝ v ((fderiv ℝ (hessian f) x d) w) = iteratedFDeriv ℝ 3 f x ![d, w, v] := by
  let line : ℝ → E := fun s ↦ x + s • d
  let φ : ℝ → ℝ := fun s ↦ inner ℝ v (hessian f (line s) w)
  let ψ : ℝ → ℝ := fun s ↦ iteratedFDeriv ℝ 2 f (line s) ![w, v]
  obtain ⟨u, hu, hcontOn⟩ :=
    h_contDiffAt.contDiffOn (m := 3) (by simp) (by intro h; simp at h)
  obtain ⟨s, hs_sub, hs_open, hxs⟩ := mem_nhds_iff.mp hu
  have hs_contOn : ContDiffOn ℝ 3 f s := hcontOn.mono hs_sub
  have hEqOn : ∀ y ∈ s, inner ℝ v (hessian f y w) = iteratedFDeriv ℝ 2 f y ![w, v] := by
    intro y hy
    -- Rewrite the Hessian pairing through the second iterated derivative on a local `C³`
    -- neighborhood of `x`.
    have hy_cont : ContDiffAt ℝ 3 f y := hs_contOn.contDiffAt (hs_open.mem_nhds hy)
    have hfderiv_C2 : ContDiffAt ℝ 2 (fderiv ℝ f) y := by
      exact hy_cont.fderiv_right (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)
    have hfderiv_diff : DifferentiableAt ℝ (fderiv ℝ f) y := by
      exact hfderiv_C2.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
    let D : StrongDual ℝ E →L[ℝ] E :=
      (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
    have hgrad_hasFDeriv :
        HasFDerivAt (∇ f)
          (D.comp (fderiv ℝ (fderiv ℝ f) y)) y := by
      simpa [gradient, D] using D.hasFDerivAt.comp y hfderiv_diff.hasFDerivAt
    rw [hessian, hgrad_hasFDeriv.fderiv]
    simp only [ContinuousLinearMap.comp_apply]
    rw [real_inner_comm]
    calc
      inner ℝ
          ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv
            ((fderiv ℝ (fderiv ℝ f) y) w)) v
          = ((fderiv ℝ (fderiv ℝ f) y) w) v := by
              simp [InnerProductSpace.toDual_symm_apply]
      _ = iteratedFDeriv ℝ 2 f y ![w, v] := by
            simp [iteratedFDeriv_two_apply]
  have hline_mem : ∀ᶠ t in nhds (0 : ℝ), line t ∈ s := by
    let hline0 : ContinuousAt line 0 :=
      (affine_segment_hasDerivAt (x := x) (d := d) 0).continuousAt
    exact hline0.tendsto.eventually (hs_open.mem_nhds (by simpa [line] using hxs))
  have hEq : ψ =ᶠ[nhds (0 : ℝ)] φ := by
    filter_upwards [hline_mem] with t ht
    simp [ψ, φ, line, hEqOn _ ht]
  have hφ :
      HasDerivAt φ (inner ℝ v ((fderiv ℝ (hessian f) x d) w)) 0 := by
    have hxLine : HasDerivAt line d 0 := by
      simpa [line] using affine_segment_hasDerivAt (x := x) (d := d) 0
    have hhessianDeriv :
        HasFDerivAt (hessian f) (fderiv ℝ (hessian f) (line 0)) (line 0) := by
      simpa [line] using hessian_hasFDerivAt_of_contDiffAt (f := f) (x := x) h_contDiffAt
    have happly :
        HasDerivAt (fun t : ℝ ↦ hessian f (line t) w)
          ((fderiv ℝ (hessian f) (line 0) d) w) 0 := by
      -- Differentiate the Hessian map along the affine line and then evaluate it on `w`.
      have happlyF :
          HasFDerivAt (fun y : E ↦ hessian f y w)
            ((ContinuousLinearMap.apply ℝ E w).comp (fderiv ℝ (hessian f) (line 0))) (line 0) := by
        exact (ContinuousLinearMap.apply ℝ E w).hasFDerivAt.comp (line 0) hhessianDeriv
      simpa using happlyF.comp_hasDerivAt 0 hxLine
    have hinnerF :
        HasFDerivAt (fun y : E ↦ inner ℝ v y) ((innerSL ℝ) v) (hessian f (line 0) w) := by
      simpa using ((innerSL ℝ) v).hasFDerivAt
    -- The scalar pairing is the composition of the Hessian line with the fixed inner-product
    -- functional against `v`.
    simpa [φ, line] using hinnerF.comp_hasDerivAt 0 happly
  have hiter2_C1 : ContDiffAt ℝ 1 (iteratedFDeriv ℝ 2 f) x := by
    exact h_contDiffAt.iteratedFDeriv_right (m := 1) (i := 2)
      (by norm_num : (1 : WithTop ℕ∞) + 2 ≤ 3)
  have hiter2_deriv :
      HasFDerivAt (iteratedFDeriv ℝ 2 f) (fderiv ℝ (iteratedFDeriv ℝ 2 f) x) x := by
    exact (hiter2_C1.hasStrictFDerivAt one_ne_zero).hasFDerivAt
  have hψ :
      HasDerivAt ψ (((fderiv ℝ (iteratedFDeriv ℝ 2 f) x) d) ![w, v]) 0 := by
    have hline0 : HasDerivAt line d 0 := by
      simpa [line] using affine_segment_hasDerivAt (x := x) (d := d) 0
    have hcomp :
        HasDerivAt (fun t : ℝ ↦ iteratedFDeriv ℝ 2 f (line t))
          ((fderiv ℝ (iteratedFDeriv ℝ 2 f) x) d) 0 := by
      simpa [line] using
        hiter2_deriv.comp_hasDerivAt_of_eq 0 hline0 (by simp [line])
    -- Evaluate the derivative of the bilinear iterated derivative on the ordered pair `(w, v)`.
    simpa [ψ] using
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E) ℝ ![w, v]).hasFDerivAt.comp_hasDerivAt
        0 hcomp)
  have hψ_from_φ : HasDerivAt ψ (inner ℝ v ((fderiv ℝ (hessian f) x d) w)) 0 :=
    hφ.congr_of_eventuallyEq hEq
  have hsame :
      inner ℝ v ((fderiv ℝ (hessian f) x d) w) =
        ((fderiv ℝ (iteratedFDeriv ℝ 2 f) x) d) ![w, v] :=
    hψ_from_φ.unique hψ
  -- Rewrite the derivative of the second iterated derivative back to the canonical third-order
  -- owner.
  simpa [iteratedFDeriv_succ_apply_left] using hsame

omit hf_strong hσ2 hf_hessian [CompleteSpace E] in
/-- Helper for Example 5.1.6: under `C³` regularity, the third iterated derivative is symmetric
in its last two arguments. -/
private lemma iteratedFDeriv_three_swap23_at
    {x u₁ u₂ u₃ : E} (h_contDiffAt : ContDiffAt ℝ 3 f x) :
    iteratedFDeriv ℝ 3 f x ![u₁, u₂, u₃] =
      iteratedFDeriv ℝ 3 f x ![u₁, u₃, u₂] := by
  obtain ⟨u, hu, hcontOn⟩ :=
    h_contDiffAt.contDiffOn (m := 3) (by simp) (by intro h; simp at h)
  obtain ⟨s, hs_sub, hs_open, hxs⟩ := mem_nhds_iff.mp hu
  have hs_contOn : ContDiffOn ℝ 3 f s := hcontOn.mono hs_sub
  let c : E → ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ := iteratedFDeriv ℝ 2 f
  have hvanish :
      (fun y ↦ c y ![u₂, u₃] - c y ![u₃, u₂]) =ᶠ[nhds x] fun _ ↦ 0 := by
    filter_upwards [hs_open.mem_nhds hxs] with y hy
    -- Nearby second derivatives are symmetric, so the antisymmetric part vanishes.
    have hycont : ContDiffAt ℝ 2 f y := by
      exact (hs_contOn.of_le (by norm_num)).contDiffAt (hs_open.mem_nhds hy)
    have hysymm : IsSymmSndFDerivAt ℝ f y := hycont.isSymmSndFDerivAt (by norm_num)
    have hyEq : iteratedFDeriv ℝ 2 f y ![u₂, u₃] = iteratedFDeriv ℝ 2 f y ![u₃, u₂] :=
      hysymm.iteratedFDeriv_cons
    simp [c, hyEq]
  have hc_diff : DifferentiableAt ℝ c x := by
    have hc_contDiff : ContDiffAt ℝ 1 c x := by
      exact h_contDiffAt.iteratedFDeriv_right (m := 1) (i := 2)
        (by norm_num : (1 : WithTop ℕ∞) + 2 ≤ 3)
    exact hc_contDiff.differentiableAt one_ne_zero
  have hderivZero :
      fderiv ℝ (fun y ↦ c y ![u₂, u₃] - c y ![u₃, u₂]) x = 0 := by
    -- Replace the function by the eventually equal constant zero function.
    rw [hvanish.fderiv_eq]
    simp
  have hderivEval :
      ((fderiv ℝ c x).flipMultilinear ![u₂, u₃]) u₁ =
        ((fderiv ℝ c x).flipMultilinear ![u₃, u₂]) u₁ := by
    have hzeroApplied :
        (fderiv ℝ (fun y ↦ c y ![u₂, u₃] - c y ![u₃, u₂]) x) u₁ = 0 := by
      simpa using congrArg (fun L : E →L[ℝ] ℝ => L u₁) hderivZero
    have h23diff : DifferentiableAt ℝ (fun y ↦ c y ![u₂, u₃]) x :=
      hc_diff.continuousMultilinear_apply_const ![u₂, u₃]
    have h32diff : DifferentiableAt ℝ (fun y ↦ c y ![u₃, u₂]) x :=
      hc_diff.continuousMultilinear_apply_const ![u₃, u₂]
    have hzeroApplied' :
        (((fderiv ℝ c x).flipMultilinear ![u₂, u₃] -
            (fderiv ℝ c x).flipMultilinear ![u₃, u₂]) u₁) = 0 := by
      rw [← fderiv_continuousMultilinear_apply_const hc_diff,
        ← fderiv_continuousMultilinear_apply_const hc_diff,
        ← fderiv_sub h23diff h32diff]
      exact hzeroApplied
    exact sub_eq_zero.mp hzeroApplied'
  simpa [c, iteratedFDeriv_succ_apply_left] using hderivEval

omit hf_strong hσ2 hf_hessian in
/-- Helper for Example 5.1.6: the directional derivative of the Hessian is symmetric in its two
operator slots. -/
private lemma directional_hessian_isSymmetric {x u : E}
    (h_contDiffAt : ContDiffAt ℝ 3 f x) :
    (fderiv ℝ (hessian f) x u : E →ₗ[ℝ] E).IsSymmetric := by
  intro v w
  -- Route correction: normalize both pairings to the third iterated derivative, then swap the
  -- last two arguments instead of differentiating Hessian symmetry directly along a line.
  calc
    inner ℝ ((fderiv ℝ (hessian f) x u) v) w
        = inner ℝ w ((fderiv ℝ (hessian f) x u) v) := by
            rw [real_inner_comm]
    _ = iteratedFDeriv ℝ 3 f x ![u, v, w] :=
          hessian_direction_pairing_eq_iteratedFDeriv
            (f := f) (x := x) (d := u) (w := v) (v := w) h_contDiffAt
    _ = iteratedFDeriv ℝ 3 f x ![u, w, v] :=
          iteratedFDeriv_three_swap23_at
            (f := f) (x := x) (u₁ := u) (u₂ := v) (u₃ := w) h_contDiffAt
    _ = inner ℝ v ((fderiv ℝ (hessian f) x u) w) :=
          (hessian_direction_pairing_eq_iteratedFDeriv
            (f := f) (x := x) (d := u) (w := w) (v := v) h_contDiffAt).symm

/-- Helper for Example 5.1.6: the operator norm bound coming from `C22[L₃]`, together with the
strong-convexity norm conversion, yields the scalar quadratic-form estimate needed for the final
Loewner-order comparison. -/
private lemma directional_hessian_quadratic_form_le {x u v : E} :
    inner ℝ ((fderiv ℝ (hessian f) x u) v) v ≤
      (((L3 : ℝ) / (σ2 * Real.sqrt σ2)) * ‖u‖[f; x]) * inner ℝ v (hessian f x v) := by
  have hderiv_norm :
      ‖fderiv ℝ (hessian f) x‖ ≤ (L3 : ℝ) := by
    simpa using
      (norm_fderiv_le_of_lipschitz ℝ
        (HasLipschitzContinuousHessian.lipschitz hf_hessian) (x₀ := x))
  have hu_norm :
      ‖u‖ ≤ ‖u‖[f; x] / Real.sqrt σ2 :=
    norm_le_hessianLocalNorm_div_sqrt (f := f) (σ2 := σ2) (L3 := L3)
      hf_strong hσ2 hf_hessian
  have hv_quad :
      σ2 * ‖v‖ ^ (2 : ℕ) ≤ inner ℝ v (hessian f x v) :=
    hessian_quadratic_form_lower_bound_at_point (f := f) (σ2 := σ2) (L3 := L3)
      hf_strong hσ2 hf_hessian
  have hA_norm :
      ‖fderiv ℝ (hessian f) x u‖ ≤ (L3 : ℝ) * ‖u‖ := by
    calc
      ‖fderiv ℝ (hessian f) x u‖ ≤ ‖fderiv ℝ (hessian f) x‖ * ‖u‖ := by
        exact ContinuousLinearMap.le_opNorm (fderiv ℝ (hessian f) x) u
      _ ≤ (L3 : ℝ) * ‖u‖ := by
        gcongr
  have hv_nonneg : 0 ≤ inner ℝ v (hessian f x v) := by
    have hσ_norm_nonneg : 0 ≤ σ2 * ‖v‖ ^ (2 : ℕ) := by positivity
    exact le_trans hσ_norm_nonneg hv_quad
  have hnorm_sq_le :
      ((L3 : ℝ) * ‖u‖) * ‖v‖ ^ (2 : ℕ) ≤
        (((L3 : ℝ) / σ2) * ‖u‖) * inner ℝ v (hessian f x v) := by
    have hbase : ‖v‖ ^ (2 : ℕ) ≤ inner ℝ v (hessian f x v) / σ2 := by
      exact (le_div_iff₀ hσ2).2 <| by simpa [mul_comm] using hv_quad
    have hA_nonneg : 0 ≤ (L3 : ℝ) * ‖u‖ := by positivity
    exact
      (mul_le_mul_of_nonneg_left hbase hA_nonneg).trans_eq <| by
        ring_nf
  have hcoeff_le :
      (((L3 : ℝ) / σ2) * ‖u‖) * inner ℝ v (hessian f x v) ≤
        (((L3 : ℝ) / (σ2 * Real.sqrt σ2)) * ‖u‖[f; x]) * inner ℝ v (hessian f x v) := by
    have hmain :
        ((L3 : ℝ) / σ2) * ‖u‖ ≤
          ((L3 : ℝ) / (σ2 * Real.sqrt σ2)) * ‖u‖[f; x] := by
      have hstep :
          ((L3 : ℝ) / σ2) * ‖u‖ ≤
            ((L3 : ℝ) / σ2) * (‖u‖[f; x] / Real.sqrt σ2) := by
        exact mul_le_mul_of_nonneg_left hu_norm (by positivity)
      calc
        ((L3 : ℝ) / σ2) * ‖u‖
            ≤ ((L3 : ℝ) / σ2) * (‖u‖[f; x] / Real.sqrt σ2) := hstep
        _ = ((L3 : ℝ) / (σ2 * Real.sqrt σ2)) * ‖u‖[f; x] := by
          field_simp [hσ2.ne', Real.sqrt_ne_zero'.2 hσ2]
    exact mul_le_mul_of_nonneg_right hmain hv_nonneg
  -- Start from the operator-norm control on `D(∇²f)(x)` and rewrite the ambient norms using the
  -- strong-convexity lower bound on `∇²f(x)`.
  calc
    inner ℝ ((fderiv ℝ (hessian f) x u) v) v
        ≤ |inner ℝ ((fderiv ℝ (hessian f) x u) v) v| := le_abs_self _
    _ ≤ ‖(fderiv ℝ (hessian f) x u) v‖ * ‖v‖ := by
          simpa [real_inner_comm] using abs_real_inner_le_norm ((fderiv ℝ (hessian f) x u) v) v
    _ ≤ (‖fderiv ℝ (hessian f) x u‖ * ‖v‖) * ‖v‖ := by
          gcongr
          exact ContinuousLinearMap.le_opNorm (fderiv ℝ (hessian f) x u) v
    _ = ‖fderiv ℝ (hessian f) x u‖ * ‖v‖ ^ (2 : ℕ) := by ring
    _ ≤ ((L3 : ℝ) * ‖u‖) * ‖v‖ ^ (2 : ℕ) := by
          gcongr
    _ ≤ (((L3 : ℝ) / σ2) * ‖u‖) * inner ℝ v (hessian f x v) := hnorm_sq_le
    _ ≤ (((L3 : ℝ) / (σ2 * Real.sqrt σ2)) * ‖u‖[f; x]) * inner ℝ v (hessian f x v) := hcoeff_le

-- Proof sketch: use `ContDiffAt ℝ 3 f x` to identify `fderiv ℝ (hessian f) x u` with the genuine
-- directional third derivative operator `D³f(x)[u]`. The `C22[L₃]` hypothesis gives the operator
-- norm bound `‖D³f(x)[u]‖ ≤ L₃ ‖u‖`, while strong convexity yields the Loewner lower bound
-- `σ₂ • 1 ≤ hessian f x`, hence `‖v‖ ≤ ‖v‖[f; x] / √σ₂` for every `v`. Applying this estimate to
-- both slots of the bilinear operator `D³f(x)[u]` gives
-- `D³f(x)[u] ≤ (L₃ / (σ₂ * √σ₂)) ‖u‖[f; x] • ∇²f(x)`.
/-- Example 5.1.6: if `f` is strongly convex on all of `E` with parameter `σ₂`, belongs to the
chapter smoothness class `C22[L₃]`, and is `C³` at `x`, then the directional derivative of its
Hessian satisfies the operator inequality
`D³f(x)[u] ≤ (L₃ / (σ₂ * √σ₂)) ‖u‖_{∇² f(x)} ∇²f(x)`. This keeps the example at the
source-facing operator layer used by Corollary 5.1.1. -/
theorem thirdDerivative_operator_le_of_mem_C22
    {x u : E} (h_contDiffAt : ContDiffAt ℝ 3 f x) :
    fderiv ℝ (hessian f) x u ≤
      (((L3 : ℝ) / (σ2 * Real.sqrt σ2)) * ‖u‖[f; x]) • hessian f x := by
  -- Package the scalar quadratic-form estimate as positivity of the operator gap.
  rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_iff]
  constructor
  · have hH_symm :
        (hessian f x : E →ₗ[ℝ] E).IsSymmetric := by
        simpa using
          fderiv_gradient_isSymmetric_of_contDiffAt
            (h_contDiffAt.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
    have hA_symm :
        (fderiv ℝ (hessian f) x u : E →ₗ[ℝ] E).IsSymmetric :=
      directional_hessian_isSymmetric (f := f) h_contDiffAt
    exact
      (LinearMap.IsSymmetric.smul
        (c := (((L3 : ℝ) / (σ2 * Real.sqrt σ2)) * ‖u‖[f; x]))
        (by simp) hH_symm).sub hA_symm
  · intro v
    -- The source proof has already reduced the problem to the scalar Hessian quadratic-form
    -- comparison in the test direction `v`.
    have hquad :
        inner ℝ ((fderiv ℝ (hessian f) x u) v) v ≤
          (((L3 : ℝ) / (σ2 * Real.sqrt σ2)) * ‖u‖[f; x]) * inner ℝ v (hessian f x v) :=
      directional_hessian_quadratic_form_le (f := f) (σ2 := σ2) (L3 := L3)
        hf_strong hσ2 hf_hessian
    simpa [inner_sub_left, inner_smul_left, real_inner_comm, mul_assoc, mul_left_comm, mul_comm]
      using sub_nonneg.mpr hquad

-- Proof sketch: use `IsSelfConcordantOnWith.of_thirdDerivative_operator_le` with
-- `dom = Set.univ`.
-- The preceding theorem supplies the operator inequality with coefficient
-- `2 * (L₃ / (2 * σ₂ * √σ₂))`, while `hf_strong` gives convexity on `Set.univ` and the global
-- hypothesis `h_contDiff` provides the required `C³` regularity on `Set.univ`.
/-- Bridge theorem: adding the separate `C³` hypothesis upgrades the operator estimate from
Example 5.1.6 to the Chapter 5 owner `IsSelfConcordantOnWith`; the modulus is converted to the
owner `strongConvexSelfConcordanceConstant σ₂ L₃`. -/
theorem isSelfConcordantOnWith_of_mem_C22_contDiff
    (h_contDiff : ContDiff ℝ 3 f) :
    IsSelfConcordantOnWith Set.univ
      (strongConvexSelfConcordanceConstant σ2 L3) f := by
  refine IsSelfConcordantOnWith.of_thirdDerivative_operator_le isOpen_univ ?_ ?_ ?_
  · simpa using h_contDiff.contDiffOn
  · simpa [strongConvexOn_zero] using (hf_strong.mono hσ2.le : StrongConvexOn Set.univ 0 f)
  · intro x _hx u
    change fderiv ℝ (hessian f) x u ≤
      (2 * (strongConvexSelfConcordanceConstant σ2 L3 : ℝ) * ‖u‖[f; x]) •
        hessian f x
    have hthird :
        fderiv ℝ (hessian f) x u ≤
          (((L3 : ℝ) / (σ2 * Real.sqrt σ2)) * ‖u‖[f; x]) • hessian f x :=
      hf_strong.thirdDerivative_operator_le_of_mem_C22 hσ2 hf_hessian
        (show ContDiffAt ℝ 3 f x from h_contDiff.contDiffAt)
    rw [two_mul_coe_strongConvexSelfConcordanceConstant hσ2]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hthird

omit hf_strong hσ2 hf_hessian

end StrongConvexOn

end
