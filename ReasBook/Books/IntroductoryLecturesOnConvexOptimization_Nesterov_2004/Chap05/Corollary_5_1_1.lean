/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient HessianLocalNorm

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {dom : Set E} {Mf : NNReal} {f : E → ℝ}

/-
Corollary 5.1.1 lies in the Chapter 5 self-concordance differential-inequality domain.

Sampled owner-style declarations in this domain:
* `hessian` from `Chap01/Definition_1_4_16`, the chapter owner for the Hessian operator;
* `thirdDirectionalDerivative` from `Chap05/Definition_5_0_10`, the source-facing owner for the
  diagonal third derivative;
* `hessianLocalNorm` and the notation `‖u‖[f; x]` from `Chap05/Definition_5_1_1`;
* `IsSelfConcordantOnWith.third_deriv_bound` from `Chap05/Definition_5_1_1`, the chapter owner
  field whose surface this corollary compares with the Hessian-operator inequality.

Source/core/bridge triage:
* source-facing: the textbook equivalence between the cubic self-concordance bound and the Loewner
  operator inequality;
* core/canonical: `hessian`, `thirdDirectionalDerivative`, and `hessianLocalNorm`;
* bridge/view: this corollary translating between those two source-facing formulations.

Primitive data:
* the objective `f`;
* the domain `dom`;
* the self-concordance constant `Mf`.

Derived API:
* the owner hypothesis `IsSelfConcordantOnWith dom Mf f`;
* the operator inequality `fderiv ℝ (hessian f) x u ≤ (2 M_f ‖u‖[f; x]) • hessian f x`.

This file therefore stays at the source-facing corollary layer, but it reuses the chapter owners
instead of restating the same mathematics through raw `iteratedFDeriv`, `Real.sqrt`, and
`fderiv ℝ (∇ f)` formulas. -/

-- Proof sketch: under the standing open-domain, `C³`, and convexity assumptions, the owner
-- `IsSelfConcordantOnWith dom Mf f` is equivalent to its defining cubic bound. Polarize that
-- bound to obtain the quadratic-form estimate for the bilinear form `D³f(x)[u]`, then translate
-- it into Loewner order for the corresponding Hessian-direction operator. Conversely, evaluate
-- the operator inequality on the quadratic form at `u` and `-u` to recover the absolute cubic
-- bound, then rebuild the owner with the standing structural hypotheses.
namespace IsSelfConcordantOnWith

/-- Helper for Corollary 5 1 1: a pointwise `C³` hypothesis upgrades the Hessian map to a
genuinely Fréchet-differentiable operator-valued map. -/
private lemma hessian_hasFDerivAt_of_contDiffAt
    {f : E → ℝ} {x : E} (hcontAt : ContDiffAt ℝ 3 f x) :
    HasFDerivAt (hessian f) (fderiv ℝ (hessian f) x) x := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfderiv_C2 : ContDiffAt ℝ 2 (fderiv ℝ f) x := by
    -- First differentiate `f` once and keep the two remaining derivatives.
    exact hcontAt.fderiv_right (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)
  have hgrad_C2 : ContDiffAt ℝ 2 (∇ f) x := by
    -- Rewrite the gradient through the Riesz map before differentiating again.
    simpa [gradient, D] using D.contDiff.contDiffAt.comp x hfderiv_C2
  have hhessian_C1 : ContDiffAt ℝ 1 (hessian f) x := by
    -- One more derivative of the gradient is exactly the Hessian owner.
    simpa [hessian] using
      hgrad_C2.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  -- Convert the `C¹` regularity of the Hessian map into the required Fréchet derivative.
  exact (hhessian_C1.hasStrictFDerivAt one_ne_zero).hasFDerivAt

/-- Helper for Corollary 5 1 1: when the Hessian quadratic form is nonnegative, the square of the
local norm rewrites back to that quadratic form. -/
private lemma sq_hessianLocalNorm_eq_inner_of_nonneg
    {f : E → ℝ} {x u : E} (hquad : 0 ≤ inner ℝ u (hessian f x u)) :
    ‖u‖[f; x] ^ (2 : ℕ) = inner ℝ u (hessian f x u) := by
  -- Expand the local norm and use `sqrt(x)^2 = x` on the nonnegative Hessian quadratic form.
  simpa [hessianLocalNorm_def] using Real.sq_sqrt hquad

/-- Helper for Corollary 5 1 1: the affine line `s ↦ x + s • d` has derivative `d`. -/
private lemma affine_segment_hasDerivAt
    {x d : E} (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ x + s • d) d t := by
  -- Differentiate scalar multiplication and then translate by the base point.
  simpa [one_smul] using ((hasDerivAt_id t).smul_const d).const_add x

/-- Helper for Corollary 5 1 1: the scalar Hessian-direction pairing is the corresponding
evaluation of the third iterated derivative. -/
private lemma hessian_direction_pairing_eq_iteratedFDeriv
    {f : E → ℝ} {x d w v : E}
    (hcontAt : ContDiffAt ℝ 3 f x) :
    inner ℝ v ((fderiv ℝ (hessian f) x d) w) = iteratedFDeriv ℝ 3 f x ![d, w, v] := by
  let line : ℝ → E := fun s ↦ x + s • d
  let φ : ℝ → ℝ := fun s ↦ inner ℝ v (hessian f (line s) w)
  let ψ : ℝ → ℝ := fun s ↦ iteratedFDeriv ℝ 2 f (line s) ![w, v]
  obtain ⟨u, hu, hcontOn⟩ :=
    hcontAt.contDiffOn (m := 3) (by simp) (by intro h; simp at h)
  obtain ⟨s, hs_sub, hs_open, hxs⟩ := mem_nhds_iff.mp hu
  have hs_contOn : ContDiffOn ℝ 3 f s := hcontOn.mono hs_sub
  have hEqOn : ∀ y ∈ s, inner ℝ v (hessian f y w) = iteratedFDeriv ℝ 2 f y ![w, v] := by
    intro y hy
    -- On a local `C³` neighborhood, the Hessian pairing is exactly the second iterated
    -- derivative evaluated on the ordered pair `(w, v)`.
    have hy_cont : ContDiffAt ℝ 3 f y := hs_contOn.contDiffAt (hs_open.mem_nhds hy)
    have hfderiv_C2 : ContDiffAt ℝ 2 (fderiv ℝ f) y := by
      exact hy_cont.fderiv_right (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)
    have hfderiv_diff : DifferentiableAt ℝ (fderiv ℝ f) y := by
      exact hfderiv_C2.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
    have hgrad_hasFDeriv :
        HasFDerivAt (∇ f)
          (((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
            (fderiv ℝ (fderiv ℝ f) y)) y := by
      simpa [gradient] using
        (((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap).hasFDerivAt.comp
          y hfderiv_diff.hasFDerivAt)
    rw [hessian, hgrad_hasFDeriv.fderiv]
    simp only [ContinuousLinearMap.comp_apply]
    rw [real_inner_comm]
    calc
      inner ℝ
          ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv
            ((fderiv ℝ (fderiv ℝ f) y) w)) v
          = ((fderiv ℝ (fderiv ℝ f) y) w) v := by
              simpa using
                (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := E) (x := v)
                  (y := ((fderiv ℝ (fderiv ℝ f) y) w)))
      _ = iteratedFDeriv ℝ 2 f y ![w, v] := by
            simpa [iteratedFDeriv_two_apply]
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
      simpa [line] using hessian_hasFDerivAt_of_contDiffAt (f := f) (x := x) hcontAt
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
    exact hcontAt.iteratedFDeriv_right (m := 1) (i := 2)
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
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E) ℝ ![w, v]).hasFDerivAt.comp_hasDerivAt 0
        hcomp)
  have hψ_from_φ : HasDerivAt ψ (inner ℝ v ((fderiv ℝ (hessian f) x d) w)) 0 :=
    hφ.congr_of_eventuallyEq hEq
  have hsame :
      inner ℝ v ((fderiv ℝ (hessian f) x d) w) =
        ((fderiv ℝ (iteratedFDeriv ℝ 2 f) x) d) ![w, v] :=
    hψ_from_φ.unique hψ
  -- Rewrite the derivative of the second iterated derivative back to the canonical
  -- third-order owner.
  simpa [iteratedFDeriv_succ_apply_left] using hsame

/-- Helper for Corollary 5 1 1: under `C³` regularity, the third iterated derivative is symmetric
in its first two arguments. -/
private lemma iteratedFDeriv_three_swap12_at
    {f : E → ℝ} {x u₁ u₂ u₃ : E} (hcontAt : ContDiffAt ℝ 3 f x) :
    iteratedFDeriv ℝ 3 f x ![u₁, u₂, u₃] =
      iteratedFDeriv ℝ 3 f x ![u₂, u₁, u₃] := by
  let g : E → E →L[ℝ] ℝ := fderiv ℝ f
  -- View the third derivative as the second derivative of `fderiv ℝ f`, then invoke symmetry of
  -- second derivatives for the intermediate operator-valued map.
  have hgcont : ContDiffAt ℝ 2 g x := by
    simpa [g] using hcontAt.fderiv_right (m := 2) (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)
  have hgsymm : IsSymmSndFDerivAt ℝ g x := hgcont.isSymmSndFDerivAt (by norm_num)
  have hswap :
      (fderiv ℝ (fderiv ℝ g) x u₁ u₂) u₃ =
        (fderiv ℝ (fderiv ℝ g) x u₂ u₁) u₃ := by
    exact congrArg (fun L : E →L[ℝ] ℝ => L u₃) (hgsymm.eq u₁ u₂)
  simpa [g, iteratedFDeriv_succ_apply_right, iteratedFDeriv_two_apply] using hswap

/-- Helper for Corollary 5 1 1: under `C³` regularity, the third iterated derivative is symmetric
in its last two arguments. -/
private lemma iteratedFDeriv_three_swap23_at
    {f : E → ℝ} {x u₁ u₂ u₃ : E} (hcontAt : ContDiffAt ℝ 3 f x) :
    iteratedFDeriv ℝ 3 f x ![u₁, u₂, u₃] =
      iteratedFDeriv ℝ 3 f x ![u₁, u₃, u₂] := by
  obtain ⟨u, hu, hcontOn⟩ :=
    hcontAt.contDiffOn (m := 3) (by simp) (by intro h; simp at h)
  obtain ⟨s, hs_sub, hs_open, hxs⟩ := mem_nhds_iff.mp hu
  have hs_contOn : ContDiffOn ℝ 3 f s := hcontOn.mono hs_sub
  let c : E → ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ := iteratedFDeriv ℝ 2 f
  -- The second derivative is symmetric at nearby points, so the antisymmetric part vanishes on a
  -- neighborhood of `x`, and therefore so does its derivative at `x`.
  have hvanish :
      (fun y ↦ c y ![u₂, u₃] - c y ![u₃, u₂]) =ᶠ[nhds x] fun _ ↦ 0 := by
    filter_upwards [hs_open.mem_nhds hxs] with y hy
    have hycont : ContDiffAt ℝ 2 f y := by
      exact (hs_contOn.of_le (by norm_num)).contDiffAt (hs_open.mem_nhds hy)
    have hysymm : IsSymmSndFDerivAt ℝ f y := hycont.isSymmSndFDerivAt (by norm_num)
    have hyEq : iteratedFDeriv ℝ 2 f y ![u₂, u₃] = iteratedFDeriv ℝ 2 f y ![u₃, u₂] :=
      hysymm.iteratedFDeriv_cons
    simpa [c, hyEq]
  have hc_diff : DifferentiableAt ℝ c x := by
    have hc_contDiff : ContDiffAt ℝ 1 c x := by
      exact hcontAt.iteratedFDeriv_right (m := 1) (i := 2)
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

/-- Helper for Corollary 5 1 1: the Hessian-direction operator is symmetric in its last two
slots. -/
private lemma third_derivative_operator_isSymmetric
    {f : E → ℝ} {x d : E} (hcontAt : ContDiffAt ℝ 3 f x) :
    (fderiv ℝ (hessian f) x d).IsSymmetric := by
  intro v w
  -- Identify both pairings with the same third iterated derivative and swap the last two slots.
  calc
    inner ℝ ((fderiv ℝ (hessian f) x d) v) w
        = inner ℝ w ((fderiv ℝ (hessian f) x d) v) := by
            rw [real_inner_comm]
    _ = iteratedFDeriv ℝ 3 f x ![d, v, w] :=
          hessian_direction_pairing_eq_iteratedFDeriv
            (f := f) (x := x) (d := d) (w := v) (v := w) hcontAt
    _ = iteratedFDeriv ℝ 3 f x ![d, w, v] :=
          iteratedFDeriv_three_swap23_at
            (f := f) (x := x) (u₁ := d) (u₂ := v) (u₃ := w) hcontAt
    _ = inner ℝ v ((fderiv ℝ (hessian f) x d) w) :=
          (hessian_direction_pairing_eq_iteratedFDeriv
            (f := f) (x := x) (d := d) (w := w) (v := v) hcontAt).symm

/-- Helper for Corollary 5 1 1: the Hessian bilinear form at `x`, written in the operator-first
convention used by the positive-operator API. -/
private def hessianBilinAt (f : E → ℝ) (x : E) : LinearMap.BilinForm ℝ E :=
  ((innerSL ℝ).comp (hessian f x)).toBilinForm

/-- Helper for Corollary 5 1 1: evaluating `hessianBilinAt` pairs the Hessian image of the first
argument with the second argument. -/
private lemma hessianBilinAt_apply (f : E → ℝ) (x u v : E) :
    hessianBilinAt f x u v = inner ℝ (hessian f x u) v :=
  rfl

/-- Helper for Corollary 5 1 1: a zero Hessian local norm is equivalent to vanishing under the
Hessian operator itself. -/
private lemma hessian_localRadical_iff_hessian_eq_zero
    {f : E → ℝ} {x u : E} (hxPos : (hessian f x).IsPositive) :
    ‖u‖[f; x] = 0 ↔ hessian f x u = 0 := by
  let B : LinearMap.BilinForm ℝ E := hessianBilinAt f x
  have hB_nonneg : ∀ a : E, 0 ≤ (B a) a := by
    intro a
    simpa [B, hessianBilinAt_apply, real_inner_comm] using hxPos.inner_nonneg_right a
  have hB_symm : LinearMap.IsSymm B := by
    rw [← LinearMap.BilinForm.isSymm_iff]
    rw [LinearMap.BilinForm.isSymm_def]
    intro a b
    change inner ℝ (hessian f x a) b = inner ℝ (hessian f x b) a
    simpa [real_inner_comm] using hxPos.isSymmetric a b
  constructor
  · intro hu
    have hu_quad_nonneg : 0 ≤ inner ℝ u (hessian f x u) := hxPos.inner_nonneg_right u
    have hu_sq :
        ‖u‖[f; x] ^ (2 : ℕ) = inner ℝ u (hessian f x u) :=
      sq_hessianLocalNorm_eq_inner_of_nonneg (f := f) (x := x) (u := u) hu_quad_nonneg
    have hu_quad : (B u) u = 0 := by
      have hu_sq_zero : ‖u‖[f; x] ^ (2 : ℕ) = 0 := by simp [hu]
      have hu_inner_zero : inner ℝ u (hessian f x u) = 0 := by
        nlinarith [hu_sq, hu_sq_zero]
      simpa [B, hessianBilinAt_apply, real_inner_comm] using hu_inner_zero
    have hu_ker : u ∈ LinearMap.ker B :=
      (LinearMap.BilinForm.apply_apply_same_eq_zero_iff B hB_nonneg hB_symm).1 hu_quad
    have hu_ker' : B u = 0 := by simpa [LinearMap.mem_ker] using hu_ker
    have hself_zero : inner ℝ (hessian f x u) (hessian f x u) = 0 := by
      simpa [B, hessianBilinAt_apply] using
        congrArg (fun L : E →ₗ[ℝ] ℝ => L (hessian f x u)) hu_ker'
    exact inner_self_eq_zero.mp hself_zero
  · intro hu
    have hu_sq :
        ‖u‖[f; x] ^ (2 : ℕ) = 0 := by
      rw [sq_hessianLocalNorm_eq_inner_of_nonneg (f := f) (x := x) (u := u)
        (hxPos.inner_nonneg_right u)]
      simp [hu]
    have hu_nonneg : 0 ≤ ‖u‖[f; x] := hessianLocalNorm_nonneg f x u
    nlinarith

/-- Helper for Corollary 5 1 1: a zero Hessian local norm is equivalent to annihilating every
Hessian bilinear pairing at the base point. -/
private lemma hessian_localRadical_iff_annihilates_hessian
    {f : E → ℝ} {x u : E} (hxPos : (hessian f x).IsPositive) :
    ‖u‖[f; x] = 0 ↔ ∀ z : E, inner ℝ u (hessian f x z) = 0 := by
  constructor
  · intro hu z
    have hHu : hessian f x u = 0 :=
      (hessian_localRadical_iff_hessian_eq_zero (f := f) (x := x) (u := u) hxPos).1 hu
    have hsym : inner ℝ (hessian f x u) z = inner ℝ u (hessian f x z) := by
      simpa [real_inner_comm] using hxPos.isSymmetric u z
    simpa [hHu] using hsym.symm
  · intro hu
    have huu : inner ℝ u (hessian f x u) = 0 := hu u
    have hu_sq :
        ‖u‖[f; x] ^ (2 : ℕ) = 0 := by
      rw [sq_hessianLocalNorm_eq_inner_of_nonneg (f := f) (x := x) (u := u)
        (hxPos.inner_nonneg_right u)]
      simp [huu]
    have hu_nonneg : 0 ≤ ‖u‖[f; x] := hessianLocalNorm_nonneg f x u
    nlinarith

/-- Helper for Corollary 5 1 1: the Hessian local radical at `x` is the submodule of directions
that annihilate every Hessian pairing. -/
private def hessianLocalRadicalSubmodule (f : E → ℝ) (x : E) : Submodule ℝ E where
  carrier := {u : E | ∀ z : E, inner ℝ u (hessian f x z) = 0}
  zero_mem' := by
    intro z
    simp
  add_mem' := by
    intro u v hu hv z
    rw [inner_add_left]
    simp [hu z, hv z]
  smul_mem' := by
    intro a u hu z
    simp [inner_smul_left, hu z]

/-- Helper for Corollary 5 1 1: membership in the Hessian local radical submodule is exactly the
raw annihilator predicate used by the earlier vanishing lemmas. -/
private lemma mem_hessianLocalRadicalSubmodule_iff
    {f : E → ℝ} {x u : E} :
    u ∈ hessianLocalRadicalSubmodule f x ↔
      ∀ z : E, inner ℝ u (hessian f x z) = 0 := by
  rfl

/-- Helper for Corollary 5 1 1: under Hessian positivity, the local-radical submodule matches the
zero local-norm directions. -/
private lemma mem_hessianLocalRadicalSubmodule_iff_localNorm_eq_zero
    {f : E → ℝ} {x u : E} (hxPos : (hessian f x).IsPositive) :
    u ∈ hessianLocalRadicalSubmodule f x ↔ ‖u‖[f; x] = 0 := by
  -- Repackage the earlier pointwise radical criterion through the canonical submodule.
  rw [mem_hessianLocalRadicalSubmodule_iff]
  exact (hessian_localRadical_iff_annihilates_hessian (f := f) (x := x) (u := u) hxPos).symm

/-- Helper for Corollary 5 1 1: adding a Hessian-radical direction only rescales the local norm by
the scalar on the transverse direction. -/
private lemma hessianLocalNorm_add_smul_of_localRadical
    {f : E → ℝ} {x u w : E} (hxPos : (hessian f x).IsPositive)
    (hu : ∀ z : E, inner ℝ u (hessian f x z) = 0) (t : ℝ) :
    ‖u + t • w‖[f; x] = |t| * ‖w‖[f; x] := by
  have hHu : hessian f x u = 0 :=
    (hessian_localRadical_iff_hessian_eq_zero (f := f) (x := x) (u := u) hxPos).1
      ((hessian_localRadical_iff_annihilates_hessian (f := f) (x := x) (u := u) hxPos).2 hu)
  have hquad :
      inner ℝ (u + t • w) (hessian f x (u + t • w)) =
        t ^ (2 : ℕ) * inner ℝ w (hessian f x w) := by
    calc
      inner ℝ (u + t • w) (hessian f x (u + t • w))
          = inner ℝ (u + t • w) (t • hessian f x w) := by simp [hHu, map_add]
      _ = inner ℝ u (t • hessian f x w) + inner ℝ (t • w) (t • hessian f x w) := by
            rw [inner_add_left]
      _ = t * inner ℝ u (hessian f x w) + t * (t * inner ℝ w (hessian f x w)) := by
            simp [inner_smul_left, inner_smul_right]
      _ = t ^ (2 : ℕ) * inner ℝ w (hessian f x w) := by
            simp [hu w, pow_two, mul_assoc]
  have hw_quad_nonneg : 0 ≤ inner ℝ w (hessian f x w) := hxPos.inner_nonneg_right w
  -- Expand both local norms and use the exact quadratic identity coming from the radical
  -- annihilation of the mixed terms.
  rw [hessianLocalNorm_def, hquad, hessianLocalNorm_def]
  rw [Real.sqrt_mul (sq_nonneg t)]
  simp [Real.sqrt_sq_eq_abs]

/-- Helper for Corollary 5 1 1: the Hessian pairing obeys the local-norm Cauchy-Schwarz
inequality after rewriting the positive quadratic form through `‖·‖[f; x]`. -/
private lemma hessianPairing_sq_le_localNorm
    {f : E → ℝ} {x d v : E} (hxPos : (hessian f x).IsPositive) :
    (inner ℝ d (hessian f x v)) ^ (2 : ℕ) ≤
      ‖d‖[f; x] ^ (2 : ℕ) * ‖v‖[f; x] ^ (2 : ℕ) := by
  let B : LinearMap.BilinForm ℝ E := hessianBilinAt f x
  have hB_nonneg : ∀ a : E, 0 ≤ B a a := by
    intro a
    simpa [B, hessianBilinAt_apply, real_inner_comm] using hxPos.inner_nonneg_right a
  have hB_symm : LinearMap.IsSymm B := by
    -- The Hessian bilinear form is symmetric because the Hessian operator is self-adjoint.
    rw [← LinearMap.BilinForm.isSymm_iff]
    rw [LinearMap.BilinForm.isSymm_def]
    intro a b
    simpa [B, hessianBilinAt_apply, real_inner_comm] using hxPos.isSymmetric a b
  have hsq :
      (B d v) ^ (2 : ℕ) ≤ (B d d) * (B v v) :=
    B.apply_sq_le_of_symm hB_nonneg hB_symm d v
  have hBdv :
      B d v = inner ℝ d (hessian f x v) := by
    simpa [B, hessianBilinAt_apply, real_inner_comm] using hxPos.isSymmetric d v
  have hd_sq :
      B d d = ‖d‖[f; x] ^ (2 : ℕ) := by
    rw [hessianBilinAt_apply, real_inner_comm]
    symm
    exact sq_hessianLocalNorm_eq_inner_of_nonneg (f := f) (x := x) (u := d)
      (hxPos.inner_nonneg_right d)
  have hv_sq :
      B v v = ‖v‖[f; x] ^ (2 : ℕ) := by
    rw [hessianBilinAt_apply, real_inner_comm]
    symm
    exact sq_hessianLocalNorm_eq_inner_of_nonneg (f := f) (x := x) (u := v)
      (hxPos.inner_nonneg_right v)
  -- Rewrite the bilinear-form Schwarz inequality back into the Hessian/local-norm spelling.
  have hsq' :
      (inner ℝ d (hessian f x v)) ^ (2 : ℕ) ≤ ‖d‖[f; x] ^ (2 : ℕ) * ‖v‖[f; x] ^ (2 : ℕ) := by
    rw [← hBdv]
    simpa [hd_sq, hv_sq] using hsq
  exact hsq'

/-- Helper for Corollary 5 1 1: the Hessian local norm scales by the absolute value of the scalar
once the pointwise Hessian is positive semidefinite. -/
private lemma hessianLocalNorm_smul_eq_abs_of_isPositive
    {f : E → ℝ} {x u : E} (hxPos : (hessian f x).IsPositive) (a : ℝ) :
    ‖a • u‖[f; x] = |a| * ‖u‖[f; x] := by
  have hquad : 0 ≤ inner ℝ u (hessian f x u) := hxPos.inner_nonneg_right u
  -- Expand the scaled quadratic form before taking square roots.
  calc
    ‖a • u‖[f; x] = Real.sqrt ((a * a) * inner ℝ u (hessian f x u)) := by
      rw [hessianLocalNorm_def]
      congr 1
      simp [inner_smul_left, inner_smul_right, mul_assoc]
    _ = Real.sqrt (inner ℝ u (hessian f x u)) * Real.sqrt (a * a) := by
      rw [mul_comm, Real.sqrt_mul hquad]
    _ = |a| * ‖u‖[f; x] := by
      rw [show a * a = a ^ (2 : ℕ) by ring, Real.sqrt_sq_eq_abs, hessianLocalNorm_def]
      ring

/-- Helper for Corollary 5 1 1: subtracting the Hessian-bilinear projection of `d` onto `v`
produces a local-orthogonal residual and the corresponding Pythagorean identity. -/
private lemma hessianProjectionSplit
    {f : E → ℝ} {x d v : E} (hxPos : (hessian f x).IsPositive)
    (hv : ‖v‖[f; x] ≠ 0) :
    let α : ℝ := inner ℝ d (hessian f x v) / ‖v‖[f; x] ^ (2 : ℕ)
    let w : E := d - α • v
    inner ℝ w (hessian f x v) = 0 ∧
      ‖d‖[f; x] ^ (2 : ℕ) = ‖w‖[f; x] ^ (2 : ℕ) + (α * ‖v‖[f; x]) ^ (2 : ℕ) := by
  let α : ℝ := inner ℝ d (hessian f x v) / ‖v‖[f; x] ^ (2 : ℕ)
  let w : E := d - α • v
  have hv_sq_nonneg : 0 ≤ inner ℝ v (hessian f x v) := hxPos.inner_nonneg_right v
  have hv_sq :
      ‖v‖[f; x] ^ (2 : ℕ) = inner ℝ v (hessian f x v) :=
    sq_hessianLocalNorm_eq_inner_of_nonneg (f := f) (x := x) (u := v) hv_sq_nonneg
  have hv_sq_ne : ‖v‖[f; x] ^ (2 : ℕ) ≠ 0 := by
    exact pow_ne_zero 2 hv
  have hα :
      α * ‖v‖[f; x] ^ (2 : ℕ) = inner ℝ d (hessian f x v) := by
    dsimp [α]
    field_simp [hv_sq_ne]
  have horth :
      inner ℝ w (hessian f x v) = 0 := by
    -- The projection coefficient `α` is chosen to cancel the mixed Hessian pairing with `v`.
    calc
      inner ℝ w (hessian f x v)
          = inner ℝ d (hessian f x v) - α * inner ℝ v (hessian f x v) := by
              simp [w, inner_sub_left, inner_smul_left]
      _ = inner ℝ d (hessian f x v) - α * ‖v‖[f; x] ^ (2 : ℕ) := by
            rw [hv_sq]
      _ = 0 := by nlinarith [hα]
  have horth' :
      inner ℝ v (hessian f x w) = 0 := by
    -- Symmetry of the positive Hessian operator moves the orthogonality to the other slot.
    have hsym : inner ℝ v (hessian f x w) = inner ℝ w (hessian f x v) := by
      simpa [real_inner_comm] using hxPos.isSymmetric w v
    simpa [horth] using hsym
  have hw_sq_nonneg : 0 ≤ inner ℝ w (hessian f x w) := hxPos.inner_nonneg_right w
  have hw_sq :
      ‖w‖[f; x] ^ (2 : ℕ) = inner ℝ w (hessian f x w) :=
    sq_hessianLocalNorm_eq_inner_of_nonneg (f := f) (x := x) (u := w) hw_sq_nonneg
  have hd_sq_nonneg : 0 ≤ inner ℝ d (hessian f x d) := hxPos.inner_nonneg_right d
  have hd_sq :
      ‖d‖[f; x] ^ (2 : ℕ) = inner ℝ d (hessian f x d) :=
    sq_hessianLocalNorm_eq_inner_of_nonneg (f := f) (x := x) (u := d) hd_sq_nonneg
  have hd_eq : d = w + α • v := by
    -- Rewrite `d` back as the residual plus its Hessian projection onto `v`.
    dsimp [w]
    abel_nf
  have hpyth_inner :
      inner ℝ d (hessian f x d) =
        inner ℝ w (hessian f x w) + (α * ‖v‖[f; x]) ^ (2 : ℕ) := by
    -- Expand the Hessian quadratic form of the decomposition and cancel the mixed terms.
    calc
      inner ℝ d (hessian f x d)
          = inner ℝ (w + α • v) (hessian f x (w + α • v)) := by rw [hd_eq]
      _ = inner ℝ (w + α • v) (hessian f x w + α • hessian f x v) := by
            simp [map_add]
      _ = inner ℝ w (hessian f x w) + α * inner ℝ w (hessian f x v) +
            α * inner ℝ v (hessian f x w) + α * (α * inner ℝ v (hessian f x v)) := by
              simp [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
              ring
      _ = inner ℝ w (hessian f x w) + α * (α * inner ℝ v (hessian f x v)) := by
            simp [horth, horth']
      _ = inner ℝ w (hessian f x w) + α ^ (2 : ℕ) * ‖v‖[f; x] ^ (2 : ℕ) := by
            rw [hv_sq]
            ring
      _ = inner ℝ w (hessian f x w) + (α * ‖v‖[f; x]) ^ (2 : ℕ) := by ring
  constructor
  · exact horth
  · rw [hd_sq, hw_sq]
    exact hpyth_inner

/-- Helper for Corollary 5 1 1: a local-orthonormal pair for the Hessian quadratic form models
the local norm by the Euclidean norm of the coefficients. -/
private lemma hessianLocalNorm_sq_of_localOrthonormalPair
    {f : E → ℝ} {x e₁ e₂ : E} (hxPos : (hessian f x).IsPositive)
    (he₁ : ‖e₁‖[f; x] = 1) (he₂ : ‖e₂‖[f; x] = 1)
    (horth : inner ℝ e₁ (hessian f x e₂) = 0) :
    ∀ a b : ℝ, ‖a • e₁ + b • e₂‖[f; x] ^ (2 : ℕ) = a ^ (2 : ℕ) + b ^ (2 : ℕ) := by
  have he₁_sq_nonneg : 0 ≤ inner ℝ e₁ (hessian f x e₁) := hxPos.inner_nonneg_right e₁
  have he₂_sq_nonneg : 0 ≤ inner ℝ e₂ (hessian f x e₂) := hxPos.inner_nonneg_right e₂
  have he₁_sq : inner ℝ e₁ (hessian f x e₁) = 1 := by
    simpa [he₁] using
      (sq_hessianLocalNorm_eq_inner_of_nonneg
        (f := f) (x := x) (u := e₁) he₁_sq_nonneg).symm
  have he₂_sq : inner ℝ e₂ (hessian f x e₂) = 1 := by
    simpa [he₂] using
      (sq_hessianLocalNorm_eq_inner_of_nonneg
        (f := f) (x := x) (u := e₂) he₂_sq_nonneg).symm
  have horth' : inner ℝ e₂ (hessian f x e₁) = 0 := by
    -- Symmetry moves the orthogonality relation to the opposite Hessian slot.
    have hsym : inner ℝ e₂ (hessian f x e₁) = inner ℝ e₁ (hessian f x e₂) := by
      simpa [real_inner_comm] using (hxPos.isSymmetric e₂ e₁).symm
    simpa [horth] using hsym
  intro a b
  have hab_nonneg : 0 ≤ inner ℝ (a • e₁ + b • e₂) (hessian f x (a • e₁ + b • e₂)) :=
    hxPos.inner_nonneg_right (a • e₁ + b • e₂)
  -- Expand the Hessian quadratic form in the local-orthonormal basis and cancel the cross terms.
  rw [sq_hessianLocalNorm_eq_inner_of_nonneg (f := f) (x := x) (u := a • e₁ + b • e₂) hab_nonneg]
  simp [map_add, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, horth,
    horth', he₁_sq, he₂_sq, pow_two]

/-- Helper for Corollary 5 1 1: a trilinear map is additive in its first slot. -/
private lemma trilinearApplyAddFirst
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (a₁ a₂ b c : E) :
    T ![a₁ + a₂, b, c] = T ![a₁, b, c] + T ![a₂, b, c] := by
  -- Rewrite the first-slot addition through the `Fin 3` `cons` API.
  simpa using T.cons_add ![b, c] a₁ a₂

/-- Helper for Corollary 5 1 1: a trilinear map is additive in its second slot. -/
private lemma trilinearApplyAddSecond
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (a b₁ b₂ c : E) :
    T ![a, b₁ + b₂, c] = T ![a, b₁, c] + T ![a, b₂, c] := by
  -- Curry once so that the second slot becomes the first slot of a bilinear map.
  simpa using (T.curryLeft a).cons_add ![c] b₁ b₂

/-- Helper for Corollary 5 1 1: a trilinear map is additive in its third slot. -/
private lemma trilinearApplyAddThird
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (a b c₁ c₂ : E) :
    T ![a, b, c₁ + c₂] = T ![a, b, c₁] + T ![a, b, c₂] := by
  -- Curry on the right so the last slot is an ordinary linear map.
  simpa using (T.curryRight ![a, b]).map_add c₁ c₂

/-- Helper for Corollary 5 1 1: a trilinear map is homogeneous in its first slot. -/
private lemma trilinearApplySmulFirst
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (t : ℝ) (a b c : E) :
    T ![t • a, b, c] = t * T ![a, b, c] := by
  -- Rewrite the first-slot scaling through the `Fin 3` `cons` API.
  simpa [smul_eq_mul] using T.cons_smul ![b, c] t a

/-- Helper for Corollary 5 1 1: a trilinear map is homogeneous in its second slot. -/
private lemma trilinearApplySmulSecond
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (t : ℝ) (a b c : E) :
    T ![a, t • b, c] = t * T ![a, b, c] := by
  -- Curry once so the second slot becomes the first slot of a bilinear map.
  simpa [smul_eq_mul] using (T.curryLeft a).cons_smul ![c] t b

/-- Helper for Corollary 5 1 1: a trilinear map is homogeneous in its third slot. -/
private lemma trilinearApplySmulThird
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (t : ℝ) (a b c : E) :
    T ![a, b, t • c] = t * T ![a, b, c] := by
  have hvec : Function.update ![a, b, c] 2 (t • c) = ![a, b, t • c] := by
    -- Normalize the third-slot update to the vector literal used throughout the chapter file.
    ext i
    fin_cases i <;> rfl
  have hself : Function.update ![a, b, c] 2 c = ![a, b, c] := by
    -- The untouched third slot rewrites back to the original vector literal.
    ext i
    fin_cases i <;> rfl
  rw [← hvec, T.map_update_smul, hself]
  simp [smul_eq_mul]

/-- Helper for Corollary 5 1 1: the centered second difference of a symmetric trilinear form
isolates its `(u,w,w)` coefficient. -/
private lemma symmetricTrilinear_centeredSecondDifference
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (hswap12 : ∀ a b c : E, T ![a, b, c] = T ![b, a, c])
    (hswap23 : ∀ a b c : E, T ![a, b, c] = T ![a, c, b])
    (u w : E) (t : ℝ) :
    T ![u + t • w, u + t • w, u + t • w] +
        T ![u - t • w, u - t • w, u - t • w] -
          2 * T ![u, u, u] =
      6 * t ^ (2 : ℕ) * T ![u, w, w] := by
  have hplus :
      T ![u + t • w, u + t • w, u + t • w]
        = T ![u, u, u] + t * T ![u, u, w] + t * T ![u, w, u] + t * (t * T ![u, w, w]) +
            (t * T ![w, u, u] + t * (t * T ![w, u, w]) + t * (t * T ![w, w, u]) +
              t * (t * (t * T ![w, w, w]))) := by
    -- Expand the three `u + t • w` slots one at a time so every monomial appears explicitly.
    rw [trilinearApplyAddFirst]
    rw [trilinearApplyAddSecond, trilinearApplyAddSecond]
    rw [trilinearApplyAddThird, trilinearApplyAddThird, trilinearApplyAddThird,
      trilinearApplyAddThird]
    rw [trilinearApplySmulThird, trilinearApplySmulThird, trilinearApplySmulThird,
      trilinearApplySmulThird]
    rw [trilinearApplySmulSecond, trilinearApplySmulSecond,
      trilinearApplySmulSecond, trilinearApplySmulSecond,
      trilinearApplySmulFirst, trilinearApplySmulFirst,
      trilinearApplySmulFirst, trilinearApplySmulFirst]
    ring
  have hminus :
      T ![u - t • w, u - t • w, u - t • w]
        = T ![u, u, u] + (-t) * T ![u, u, w] + (-t) * T ![u, w, u] +
            (-t) * ((-t) * T ![u, w, w]) +
            ((-t) * T ![w, u, u] + (-t) * ((-t) * T ![w, u, w]) +
              (-t) * ((-t) * T ![w, w, u]) + (-t) * ((-t) * ((-t) * T ![w, w, w]))) := by
    -- Rewrite `u - t • w` as `u + (-t) • w` and repeat the same slotwise expansion.
    rw [show u - t • w = u + (-t) • w by simp [sub_eq_add_neg]]
    rw [trilinearApplyAddFirst]
    rw [trilinearApplyAddSecond, trilinearApplyAddSecond]
    rw [trilinearApplyAddThird, trilinearApplyAddThird, trilinearApplyAddThird,
      trilinearApplyAddThird]
    rw [trilinearApplySmulThird, trilinearApplySmulThird, trilinearApplySmulThird,
      trilinearApplySmulThird]
    rw [trilinearApplySmulSecond, trilinearApplySmulSecond,
      trilinearApplySmulSecond, trilinearApplySmulSecond,
      trilinearApplySmulFirst, trilinearApplySmulFirst,
      trilinearApplySmulFirst, trilinearApplySmulFirst]
    ring
  rw [hplus, hminus]
  -- Collapse the three two-`w` monomials to the common symmetric representative `T[u,w,w]`.
  rw [hswap23 u w u, hswap12 w u u, hswap23 u w u, hswap12 w u w, hswap23 w w u,
    hswap12 w u w]
  ring

/-- Helper for Corollary 5 1 1: the third iterated derivative vanishes in the `(u,w,w)` slot
pattern when `u` lies in the Hessian local radical. -/
private lemma iteratedFDeriv_vanishes_on_hessian_localRadical
    {Mf : NNReal} {f : E → ℝ} {x u w : E}
    (hcontAt : ContDiffAt ℝ 3 f x)
    (hxPos : (hessian f x).IsPositive)
    (hdiag_x : ∀ z : E,
      |thirdDirectionalDerivative f x z| ≤
        2 * (Mf : ℝ) * ‖z‖[f; x] ^ (3 : ℕ))
    (hu : ∀ z : E, inner ℝ u (hessian f x z) = 0) :
    iteratedFDeriv ℝ 3 f x ![u, w, w] = 0 := by
  let T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ := iteratedFDeriv ℝ 3 f x
  have huNorm : ‖u‖[f; x] = 0 :=
    (hessian_localRadical_iff_annihilates_hessian (f := f) (x := x) (u := u) hxPos).2 hu
  have huConst : (fun _ : Fin 3 ↦ u) = ![u, u, u] := by
    ext i
    fin_cases i <;> rfl
  have huuu : T ![u, u, u] = 0 := by
    have hdiag_u : |T ![u, u, u]| ≤ 0 := by
      -- The diagonal cubic bound collapses to zero because `u` has zero Hessian local norm.
      simpa [T, thirdDirectionalDerivative_eq_iteratedFDeriv hcontAt, huConst, huNorm] using
        hdiag_x u
    exact abs_eq_zero.mp (le_antisymm hdiag_u (abs_nonneg _))
  have hswap12 :
      ∀ a b c : E, T ![a, b, c] = T ![b, a, c] := by
    intro a b c
    simpa [T] using
      iteratedFDeriv_three_swap12_at
        (f := f) (x := x) (u₁ := a) (u₂ := b) (u₃ := c) hcontAt
  have hswap23 :
      ∀ a b c : E, T ![a, b, c] = T ![a, c, b] := by
    intro a b c
    simpa [T] using
      iteratedFDeriv_three_swap23_at
        (f := f) (x := x) (u₁ := a) (u₂ := b) (u₃ := c) hcontAt
  have hplusDiag (t : ℝ) :
      |T ![u + t • w, u + t • w, u + t • w]| ≤
        2 * (Mf : ℝ) * (|t| * ‖w‖[f; x]) ^ (3 : ℕ) := by
    have hconst : (fun _ : Fin 3 ↦ u + t • w) = ![u + t • w, u + t • w, u + t • w] := by
      ext i
      fin_cases i <;> rfl
    have hnorm :
        ‖u + t • w‖[f; x] = |t| * ‖w‖[f; x] :=
      hessianLocalNorm_add_smul_of_localRadical
        (f := f) (x := x) (u := u) (w := w) hxPos hu t
    -- Rewrite the source-facing diagonal bound on the translated direction back to
    -- `iteratedFDeriv`.
    simpa [T, thirdDirectionalDerivative_eq_iteratedFDeriv hcontAt, hconst, hnorm] using
      hdiag_x (u + t • w)
  have hminusDiag (t : ℝ) :
      |T ![u - t • w, u - t • w, u - t • w]| ≤
        2 * (Mf : ℝ) * (|t| * ‖w‖[f; x]) ^ (3 : ℕ) := by
    have hconst : (fun _ : Fin 3 ↦ u - t • w) = ![u - t • w, u - t • w, u - t • w] := by
      ext i
      fin_cases i <;> rfl
    have hnorm :
        ‖u - t • w‖[f; x] = |t| * ‖w‖[f; x] := by
      calc
        ‖u - t • w‖[f; x] = ‖u + (-t) • w‖[f; x] := by simp [sub_eq_add_neg]
        _ = |-t| * ‖w‖[f; x] :=
          hessianLocalNorm_add_smul_of_localRadical
            (f := f) (x := x) (u := u) (w := w) hxPos hu (-t)
        _ = |t| * ‖w‖[f; x] := by simp
    -- The same local-radical norm collapse applies to the reflected direction `u - t • w`.
    simpa [T, thirdDirectionalDerivative_eq_iteratedFDeriv hcontAt, hconst, hnorm] using
      hdiag_x (u - t • w)
  have hcoeffBound (t : ℝ) :
      |6 * t ^ (2 : ℕ) * T ![u, w, w]| ≤
        4 * (Mf : ℝ) * (|t| * ‖w‖[f; x]) ^ (3 : ℕ) := by
    have hcenter :
        T ![u + t • w, u + t • w, u + t • w] +
            T ![u - t • w, u - t • w, u - t • w] =
          6 * t ^ (2 : ℕ) * T ![u, w, w] := by
      simpa [huuu] using
        symmetricTrilinear_centeredSecondDifference T hswap12 hswap23 u w t
    rw [← hcenter]
    calc
      |T ![u + t • w, u + t • w, u + t • w] +
          T ![u - t • w, u - t • w, u - t • w]|
          ≤ |T ![u + t • w, u + t • w, u + t • w]| +
              |T ![u - t • w, u - t • w, u - t • w]| := abs_add_le _ _
      _ ≤ 2 * (Mf : ℝ) * (|t| * ‖w‖[f; x]) ^ (3 : ℕ) +
            2 * (Mf : ℝ) * (|t| * ‖w‖[f; x]) ^ (3 : ℕ) := by
          gcongr
          · exact hplusDiag t
          · exact hminusDiag t
      _ = 4 * (Mf : ℝ) * (|t| * ‖w‖[f; x]) ^ (3 : ℕ) := by ring
  have hsmall (t : ℝ) (ht : 0 < t) :
      |T ![u, w, w]| ≤ ((2 * (Mf : ℝ) * ‖w‖[f; x] ^ (3 : ℕ)) / 3) * t := by
    have hnorm_nonneg : 0 ≤ ‖w‖[f; x] := hessianLocalNorm_nonneg f x w
    have hcoeff := hcoeffBound t
    have hcoeff' :
        6 * t ^ (2 : ℕ) * |T ![u, w, w]| ≤
          4 * (Mf : ℝ) * t ^ (3 : ℕ) * ‖w‖[f; x] ^ (3 : ℕ) := by
      have hleft :
          |6 * t ^ (2 : ℕ) * T ![u, w, w]| =
            6 * t ^ (2 : ℕ) * |T ![u, w, w]| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (show 0 ≤ (6 : ℝ) by norm_num),
          abs_of_nonneg (pow_two_nonneg t)]
      have hright :
          4 * (Mf : ℝ) * (|t| * ‖w‖[f; x]) ^ (3 : ℕ) =
            4 * (Mf : ℝ) * t ^ (3 : ℕ) * ‖w‖[f; x] ^ (3 : ℕ) := by
        rw [abs_of_pos ht]
        ring
      rwa [hleft, hright] at hcoeff
    have ht_sq_pos : 0 < t ^ (2 : ℕ) := by positivity
    have hfactored :
        t ^ (2 : ℕ) * (6 * |T ![u, w, w]|) ≤
          t ^ (2 : ℕ) * (4 * (Mf : ℝ) * t * ‖w‖[f; x] ^ (3 : ℕ)) := by
      nlinarith [hcoeff']
    have hlinear :
        6 * |T ![u, w, w]| ≤ 4 * (Mf : ℝ) * t * ‖w‖[f; x] ^ (3 : ℕ) :=
      by nlinarith [hfactored, ht_sq_pos]
    nlinarith
  by_cases hzero : T ![u, w, w] = 0
  · simpa [T] using hzero
  have habs_pos : 0 < |T ![u, w, w]| := abs_pos.mpr hzero
  let K : ℝ := ((2 * (Mf : ℝ) * ‖w‖[f; x] ^ (3 : ℕ)) / 3)
  have hK_nonneg : 0 ≤ K := by
    have hMf_nonneg : 0 ≤ (Mf : ℝ) := by exact_mod_cast Mf.2
    have hw_nonneg : 0 ≤ ‖w‖[f; x] := hessianLocalNorm_nonneg f x w
    have hw_pow_nonneg : 0 ≤ ‖w‖[f; x] ^ (3 : ℕ) := pow_nonneg hw_nonneg _
    dsimp [K]
    nlinarith
  have hK_pos : 0 < K + 1 := by
    nlinarith
  let t0 : ℝ := |T ![u, w, w]| / (K + 1)
  have ht0_pos : 0 < t0 := by
    -- Choose an explicit positive step where the linear bound forces a contradiction.
    dsimp [t0]
    exact div_pos habs_pos hK_pos
  have hbound0 := hsmall t0 ht0_pos
  have hbound0' : |T ![u, w, w]| ≤ K * (|T ![u, w, w]| / (K + 1)) := by
    simpa [K, t0] using hbound0
  have hmul :
      (K + 1) * |T ![u, w, w]| ≤ K * |T ![u, w, w]| := by
    have hmul0 := mul_le_mul_of_nonneg_left hbound0' hK_pos.le
    have hrhs : (K + 1) * (K * (|T ![u, w, w]| / (K + 1))) = K * |T ![u, w, w]| := by
      field_simp [hK_pos.ne']
    rwa [hrhs] at hmul0
  nlinarith

/-- Helper for Corollary 5 1 1: if a Hessian-radical direction occupies the first slot, then the
entire symmetric third derivative vanishes. -/
private lemma iteratedFDeriv_firstSlot_zero_of_hessian_localRadical
    {Mf : NNReal} {f : E → ℝ} {x u v w : E}
    (hcontAt : ContDiffAt ℝ 3 f x)
    (hxPos : (hessian f x).IsPositive)
    (hdiag_x : ∀ z : E,
      |thirdDirectionalDerivative f x z| ≤
        2 * (Mf : ℝ) * ‖z‖[f; x] ^ (3 : ℕ))
    (hu : ∀ z : E, inner ℝ u (hessian f x z) = 0) :
    iteratedFDeriv ℝ 3 f x ![u, v, w] = 0 := by
  let T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ := iteratedFDeriv ℝ 3 f x
  have hvv : T ![u, v, v] = 0 := by
    simpa [T] using
      iteratedFDeriv_vanishes_on_hessian_localRadical
        (Mf := Mf) (f := f) (x := x) (u := u) (w := v) hcontAt hxPos hdiag_x hu
  have hww : T ![u, w, w] = 0 := by
    simpa [T] using
      iteratedFDeriv_vanishes_on_hessian_localRadical
        (Mf := Mf) (f := f) (x := x) (u := u) (w := w) hcontAt hxPos hdiag_x hu
  have hsumZero : T ![u, v + w, v + w] = 0 := by
    simpa [T] using
      iteratedFDeriv_vanishes_on_hessian_localRadical
        (Mf := Mf) (f := f) (x := x) (u := u) (w := v + w) hcontAt hxPos hdiag_x hu
  have hsumExpand :
      T ![u, v + w, v + w] =
        T ![u, v, v] + T ![u, v, w] + T ![u, w, v] + T ![u, w, w] := by
    have hfirst :
        Function.update ![u, v, v + w] 1 (v + w) = ![u, v + w, v + w] := by
      ext i
      fin_cases i <;> rfl
    have hsecond :
        Function.update ![u, v, v] 2 (v + w) = ![u, v, v + w] := by
      ext i
      fin_cases i <;> rfl
    have hthird :
        Function.update ![u, w, v] 2 (v + w) = ![u, w, v + w] := by
      ext i
      fin_cases i <;> rfl
    have hfourth :
        Function.update ![u, v, v + w] 1 v = ![u, v, v + w] := by
      ext i
      fin_cases i <;> rfl
    have hfifth :
        Function.update ![u, v, v + w] 1 w = ![u, w, v + w] := by
      ext i
      fin_cases i <;> rfl
    have hsix : Function.update ![u, v, v] 2 v = ![u, v, v] := by
      ext i
      fin_cases i <;> rfl
    have hseven : Function.update ![u, v, v] 2 w = ![u, v, w] := by
      ext i
      fin_cases i <;> rfl
    have height : Function.update ![u, w, v] 2 v = ![u, w, v] := by
      ext i
      fin_cases i <;> rfl
    have hnine : Function.update ![u, w, v] 2 w = ![u, w, w] := by
      ext i
      fin_cases i <;> rfl
    -- Expand the second slot first and then the third slot in each summand.
    rw [← hfirst, T.map_update_add, hfourth, hfifth,
      ← hsecond, ← hthird, T.map_update_add, T.map_update_add]
    rw [hsix, hseven, height, hnine]
    simp [add_left_comm, add_comm]
  have hswap23 :
      T ![u, w, v] = T ![u, v, w] := by
    simpa [T] using
      (iteratedFDeriv_three_swap23_at
        (f := f) (x := x) (u₁ := u) (u₂ := w) (u₃ := v) hcontAt)
  -- The `v + w` diagonal expansion leaves only the two equal cross terms, so they must vanish.
  rw [hsumExpand, hvv, hww, hswap23, zero_add, add_zero] at hsumZero
  nlinarith

/-- Helper for Corollary 5 1 1: if the repeated direction lies in the Hessian local radical, then
the `(d,v,v)` third-derivative slot pattern also vanishes after swapping the first two slots. -/
private lemma iteratedFDeriv_dvv_vanishes_on_hessian_localRadical
    {Mf : NNReal} {f : E → ℝ} {x d v : E}
    (hcontAt : ContDiffAt ℝ 3 f x)
    (hxPos : (hessian f x).IsPositive)
    (hdiag_x : ∀ z : E,
      |thirdDirectionalDerivative f x z| ≤
        2 * (Mf : ℝ) * ‖z‖[f; x] ^ (3 : ℕ))
    (hv : ∀ z : E, inner ℝ v (hessian f x z) = 0) :
    iteratedFDeriv ℝ 3 f x ![d, v, v] = 0 := by
  -- Swap the Hessian-radical direction into the first slot, apply the stronger vanishing helper,
  -- and swap back only at the API level.
  calc
    iteratedFDeriv ℝ 3 f x ![d, v, v]
        = iteratedFDeriv ℝ 3 f x ![v, d, v] := by
            simpa using
              (iteratedFDeriv_three_swap12_at
                (f := f) (x := x) (u₁ := d) (u₂ := v) (u₃ := v) hcontAt)
    _ = 0 := by
          exact
            iteratedFDeriv_firstSlot_zero_of_hessian_localRadical
              (Mf := Mf) (f := f) (x := x) (u := v) (v := d) (w := v)
              hcontAt hxPos hdiag_x hv

/-- Helper for Corollary 5 1 1: dividing a nonzero coefficient pair by its Euclidean radius
produces a unit-circle pair and factors that radius back out of the vector combination. -/
private lemma normModel2D_normalizeCoeffs
    {e₁ e₂ : E} {a b r : ℝ}
    (hr : r = Real.sqrt (a ^ (2 : ℕ) + b ^ (2 : ℕ))) (hr_ne : r ≠ 0) :
    a • e₁ + b • e₂ = r • ((a / r) • e₁ + (b / r) • e₂) ∧
      (a / r) ^ (2 : ℕ) + (b / r) ^ (2 : ℕ) = 1 := by
  constructor
  · -- Factor the common Euclidean radius out of the two coefficients.
    have ha : r * (a / r) = a := by
      field_simp [hr_ne]
    have hb : r * (b / r) = b := by
      field_simp [hr_ne]
    calc
      a • e₁ + b • e₂ = (r * (a / r)) • e₁ + (r * (b / r)) • e₂ := by rw [ha, hb]
      _ = r • ((a / r) • e₁) + r • ((b / r) • e₂) := by simp [smul_smul]
      _ = r • ((a / r) • e₁ + (b / r) • e₂) := by rw [smul_add]
  · -- Dividing by the Euclidean radius puts the coefficient pair on the unit circle.
    have hsq : r ^ (2 : ℕ) = a ^ (2 : ℕ) + b ^ (2 : ℕ) := by
      rw [hr]
      exact Real.sq_sqrt (by positivity)
    rw [pow_two, pow_two]
    field_simp [hr_ne]
    nlinarith [hsq]

/-- Helper for Corollary 5 1 1: on a normalized 2D Hessian model, the unresolved core estimate is
the pure unit-circle repeated-slot bound. -/
private lemma unitCircleDiagonalSampleBound
    {x e₁ e₂ : E}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (Mf : NNReal) (f : E → ℝ)
    (hnorm_model :
      ∀ a b : ℝ, ‖a • e₁ + b • e₂‖[f; x] ^ (2 : ℕ) = a ^ (2 : ℕ) + b ^ (2 : ℕ))
    (hdiag :
      ∀ z : E, |T ![z, z, z]| ≤ 2 * (Mf : ℝ) * ‖z‖[f; x] ^ (3 : ℕ)) :
    ∀ c s : ℝ, c ^ (2 : ℕ) + s ^ (2 : ℕ) = 1 →
      |T ![c • e₁ + s • e₂, c • e₁ + s • e₂, c • e₁ + s • e₂]| ≤ 2 * (Mf : ℝ) := by
  intro c s hunit
  have hnorm_sq : ‖c • e₁ + s • e₂‖[f; x] ^ (2 : ℕ) = 1 := by
    rw [hnorm_model, hunit]
  have hnorm_nonneg : 0 ≤ ‖c • e₁ + s • e₂‖[f; x] :=
    hessianLocalNorm_nonneg f x (c • e₁ + s • e₂)
  have hnorm_eq : ‖c • e₁ + s • e₂‖[f; x] = 1 := by
    nlinarith
  -- Specialize the diagonal cubic bound to a unit vector in the normalized 2D model.
  simpa [hnorm_eq] using hdiag (c • e₁ + s • e₂)

/-- Helper for Corollary 5 1 1: a symmetric trilinear form recovers its `(u,w,w)` coefficient from
the three diagonal samples at the `±60°` unit-circle directions around `u`. -/
private lemma symmetricTrilinear_sixtyDegreeInterpolation
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (hswap12 : ∀ a b c : E, T ![a, b, c] = T ![b, a, c])
    (hswap23 : ∀ a b c : E, T ![a, b, c] = T ![a, c, b])
    (u w : E) :
    T ![u, w, w] =
      (4 / 9 : ℝ) *
          (T ![(1 / 2 : ℝ) • u + (Real.sqrt 3 / 2 : ℝ) • w,
              (1 / 2 : ℝ) • u + (Real.sqrt 3 / 2 : ℝ) • w,
              (1 / 2 : ℝ) • u + (Real.sqrt 3 / 2 : ℝ) • w] +
            T ![(1 / 2 : ℝ) • u - (Real.sqrt 3 / 2 : ℝ) • w,
              (1 / 2 : ℝ) • u - (Real.sqrt 3 / 2 : ℝ) • w,
              (1 / 2 : ℝ) • u - (Real.sqrt 3 / 2 : ℝ) • w]) -
        (1 / 9 : ℝ) * T ![u, u, u] := by
  have hcentered :=
    symmetricTrilinear_centeredSecondDifference T hswap12 hswap23 u w (Real.sqrt 3)
  have hplusScale :
      T ![u + Real.sqrt 3 • w, u + Real.sqrt 3 • w, u + Real.sqrt 3 • w] =
        8 *
          T ![(1 / 2 : ℝ) • u + (Real.sqrt 3 / 2 : ℝ) • w,
            (1 / 2 : ℝ) • u + (Real.sqrt 3 / 2 : ℝ) • w,
            (1 / 2 : ℝ) • u + (Real.sqrt 3 / 2 : ℝ) • w] := by
    -- Rewrite the `+√3` direction as twice the normalized `+60°` unit-circle direction.
    have huv :
        u + Real.sqrt 3 • w =
          (2 : ℝ) • ((1 / 2 : ℝ) • u + (Real.sqrt 3 / 2 : ℝ) • w) := by
      simp [smul_add, smul_smul]
      ring
    rw [huv]
    rw [trilinearApplySmulFirst, trilinearApplySmulSecond, trilinearApplySmulThird]
    ring
  have hminusScale :
      T ![u - Real.sqrt 3 • w, u - Real.sqrt 3 • w, u - Real.sqrt 3 • w] =
        8 *
          T ![(1 / 2 : ℝ) • u - (Real.sqrt 3 / 2 : ℝ) • w,
            (1 / 2 : ℝ) • u - (Real.sqrt 3 / 2 : ℝ) • w,
            (1 / 2 : ℝ) • u - (Real.sqrt 3 / 2 : ℝ) • w] := by
    -- The reflected `-60°` direction scales in the same way.
    have huv :
        u - Real.sqrt 3 • w =
          (2 : ℝ) • ((1 / 2 : ℝ) • u - (Real.sqrt 3 / 2 : ℝ) • w) := by
      simp [smul_add, smul_smul, sub_eq_add_neg]
      ring
    rw [huv]
    rw [trilinearApplySmulFirst, trilinearApplySmulSecond, trilinearApplySmulThird]
    ring
  -- Substitute the normalized `±60°` samples into the centered second-difference identity and
  -- solve the resulting scalar equation for `T[u,w,w]`.
  rw [hplusScale, hminusScale] at hcentered
  have hsqrt_sq : (Real.sqrt 3) ^ (2 : ℕ) = 3 := by
    rw [show (Real.sqrt 3) ^ (2 : ℕ) = (Real.sqrt 3) ^ 2 by rfl]
    rw [Real.sq_sqrt (by positivity)]
  have hcentered' :
      18 * T ![u, w, w] =
        8 *
          (T ![(1 / 2 : ℝ) • u + (Real.sqrt 3 / 2 : ℝ) • w,
              (1 / 2 : ℝ) • u + (Real.sqrt 3 / 2 : ℝ) • w,
              (1 / 2 : ℝ) • u + (Real.sqrt 3 / 2 : ℝ) • w] +
            T ![(1 / 2 : ℝ) • u - (Real.sqrt 3 / 2 : ℝ) • w,
              (1 / 2 : ℝ) • u - (Real.sqrt 3 / 2 : ℝ) • w,
              (1 / 2 : ℝ) • u - (Real.sqrt 3 / 2 : ℝ) • w]) -
          2 * T ![u, u, u] := by
    rw [hsqrt_sq] at hcentered
    linarith
  linarith

/-- Helper for Corollary 5 1 1: the diagonal value of a symmetric trilinear map on
`a • e₁ + b • e₂` expands into the four basis monomials. -/
private lemma symmetricTrilinear_diagonalOnTwoVectors
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (hswap12 : ∀ a b c : E, T ![a, b, c] = T ![b, a, c])
    (hswap23 : ∀ a b c : E, T ![a, b, c] = T ![a, c, b])
    (e₁ e₂ : E) (a b : ℝ) :
    T ![a • e₁ + b • e₂, a • e₁ + b • e₂, a • e₁ + b • e₂] =
      a ^ (3 : ℕ) * T ![e₁, e₁, e₁] +
        3 * a ^ (2 : ℕ) * b * T ![e₁, e₁, e₂] +
          3 * a * b ^ (2 : ℕ) * T ![e₁, e₂, e₂] +
            b ^ (3 : ℕ) * T ![e₂, e₂, e₂] := by
  -- Expand the three identical slots once and normalize the mixed monomials via symmetry.
  rw [trilinearApplyAddFirst]
  rw [trilinearApplyAddSecond, trilinearApplyAddSecond]
  rw [trilinearApplyAddThird, trilinearApplyAddThird, trilinearApplyAddThird,
    trilinearApplyAddThird]
  rw [trilinearApplySmulThird, trilinearApplySmulThird, trilinearApplySmulThird,
    trilinearApplySmulThird]
  rw [trilinearApplySmulSecond, trilinearApplySmulSecond, trilinearApplySmulSecond,
    trilinearApplySmulSecond]
  rw [trilinearApplySmulFirst, trilinearApplySmulFirst, trilinearApplySmulFirst,
    trilinearApplySmulFirst, trilinearApplySmulFirst, trilinearApplySmulFirst,
    trilinearApplySmulFirst,
    trilinearApplySmulFirst]
  rw [trilinearApplySmulThird, trilinearApplySmulThird, trilinearApplySmulThird,
    trilinearApplySmulThird]
  rw [trilinearApplySmulSecond, trilinearApplySmulSecond, trilinearApplySmulSecond,
    trilinearApplySmulSecond]
  rw [hswap23 e₁ e₂ e₁, hswap12 e₂ e₁ e₁, hswap23 e₁ e₂ e₁, hswap12 e₂ e₁ e₂,
    hswap23 e₂ e₂ e₁, hswap12 e₂ e₁ e₂]
  ring

/-- Helper for Corollary 5 1 1: a first-quadrant unit-circle coefficient pair lifts to the
cubic-angle parameters used by the three-sample interpolation identity. -/
private lemma firstQuadrantUnitCircle_hasThirdAngleParameters
    {c s : ℝ} (hc_nonneg : 0 ≤ c) (hs_nonneg : 0 ≤ s)
    (hunit : c ^ (2 : ℕ) + s ^ (2 : ℕ) = 1) :
    ∃ sa ca : ℝ,
      sa ^ (2 : ℕ) + ca ^ (2 : ℕ) = 1 ∧
        s = 4 * ca ^ (3 : ℕ) - 3 * ca ∧
          c = 3 * sa - 4 * sa ^ (3 : ℕ) := by
  let θ : ℝ := Real.arcsin c / 3
  refine ⟨Real.sin θ, Real.cos θ, ?_, ?_, ?_⟩
  · -- The lifted pair still lies on the Euclidean unit circle.
    simpa [θ] using Real.sin_sq_add_cos_sq θ
  · -- The cosine triple-angle identity recovers the second coefficient `s`.
    have hc_lower : -1 ≤ c := by nlinarith
    have hc_upper : c ≤ 1 := by nlinarith [hunit]
    have hθ_three : Real.arcsin c = 3 * θ := by
      dsimp [θ]
      ring
    have hsqrt :
        Real.sqrt (1 - c ^ (2 : ℕ)) = s := by
      apply (Real.sqrt_eq_iff_eq_sq ?_ hs_nonneg).2
      · nlinarith [hunit]
      · nlinarith [hunit]
    calc
      s = Real.sqrt (1 - c ^ (2 : ℕ)) := by symm; exact hsqrt
      _ = Real.cos (Real.arcsin c) := by symm; exact Real.cos_arcsin c
      _ = Real.cos (3 * θ) := by rw [hθ_three]
      _ = 4 * Real.cos θ ^ (3 : ℕ) - 3 * Real.cos θ := by rw [Real.cos_three_mul]
  · -- The sine triple-angle identity recovers the first coefficient `c`.
    have hc_lower : -1 ≤ c := by nlinarith
    have hc_upper : c ≤ 1 := by nlinarith [hunit]
    have hθ_three : Real.arcsin c = 3 * θ := by
      dsimp [θ]
      ring
    calc
      c = Real.sin (Real.arcsin c) := by
            symm
            exact Real.sin_arcsin hc_lower hc_upper
      _ = Real.sin (3 * θ) := by rw [hθ_three]
      _ = 3 * Real.sin θ - 4 * Real.sin θ ^ (3 : ℕ) := by rw [Real.sin_three_mul]

/-- Helper for Corollary 5 1 1: the mixed repeated-slot coefficient `T[c • e₁ + s • e₂, e₂, e₂]`
is an explicit convex combination of three diagonal unit-circle samples after a cubic-angle
reparameterization. -/
private lemma symmetricTrilinear_thirdAngleInterpolation
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (hswap12 : ∀ a b c : E, T ![a, b, c] = T ![b, a, c])
    (hswap23 : ∀ a b c : E, T ![a, b, c] = T ![a, c, b])
    {x e₁ e₂ : E} {sa ca c s : ℝ}
    (hsq : sa ^ (2 : ℕ) + ca ^ (2 : ℕ) = 1)
    (hs : s = 4 * ca ^ (3 : ℕ) - 3 * ca)
    (hc : c = 3 * sa - 4 * sa ^ (3 : ℕ)) :
    let l₀ : ℝ := (4 * sa ^ (2 : ℕ) - 3) ^ (2 : ℕ) / 9
    let l₁ : ℝ := (4 : ℝ) / 9 * sa ^ (2 : ℕ) * (sa + Real.sqrt 3 * ca) ^ (2 : ℕ)
    let l₂ : ℝ := (4 : ℝ) / 9 * sa ^ (2 : ℕ) * (sa - Real.sqrt 3 * ca) ^ (2 : ℕ)
    let v₀ : E := sa • e₁ + ca • e₂
    let v₁ : E :=
      (-sa / 2 + (Real.sqrt 3 / 2) * ca) • e₁ + (-ca / 2 - (Real.sqrt 3 / 2) * sa) • e₂
    let v₂ : E :=
      (-sa / 2 - (Real.sqrt 3 / 2) * ca) • e₁ + (-ca / 2 + (Real.sqrt 3 / 2) * sa) • e₂
    T ![c • e₁ + s • e₂, e₂, e₂] =
      l₀ * T ![v₀, v₀, v₀] + l₁ * T ![v₁, v₁, v₁] + l₂ * T ![v₂, v₂, v₂] := by
  -- Route correction: rewrite everything in the fixed basis `(e₁,e₂)` and compare the four
  -- canonical basis monomials instead of reviving the rotated-frame interpolation.
  dsimp
  set l₀ : ℝ := (4 * sa ^ (2 : ℕ) - 3) ^ (2 : ℕ) / 9
  set l₁ : ℝ := (4 : ℝ) / 9 * sa ^ (2 : ℕ) * (sa + Real.sqrt 3 * ca) ^ (2 : ℕ)
  set l₂ : ℝ := (4 : ℝ) / 9 * sa ^ (2 : ℕ) * (sa - Real.sqrt 3 * ca) ^ (2 : ℕ)
  set a₁ : ℝ := -sa / 2 + (Real.sqrt 3 / 2) * ca
  set b₁ : ℝ := -ca / 2 - (Real.sqrt 3 / 2) * sa
  set a₂ : ℝ := -sa / 2 - (Real.sqrt 3 / 2) * ca
  set b₂ : ℝ := -ca / 2 + (Real.sqrt 3 / 2) * sa
  set v₀ : E := sa • e₁ + ca • e₂
  set v₁ : E := a₁ • e₁ + b₁ • e₂
  set v₂ : E := a₂ • e₁ + b₂ • e₂
  set A : ℝ := T ![e₁, e₁, e₁]
  set B : ℝ := T ![e₁, e₁, e₂]
  set C : ℝ := T ![e₁, e₂, e₂]
  set D : ℝ := T ![e₂, e₂, e₂]
  have hsqrt_sq : (Real.sqrt 3) ^ (2 : ℕ) = 3 := by
    rw [show (Real.sqrt 3) ^ (2 : ℕ) = (Real.sqrt 3) ^ 2 by rfl]
    rw [Real.sq_sqrt (by positivity)]
  have hsq' : sa * sa + ca * ca = 1 := by
    simpa [pow_two] using hsq
  have hsqrt_sq' : Real.sqrt 3 * Real.sqrt 3 = 3 := by
    simpa [pow_two] using hsqrt_sq
  have hca2 : ca ^ (2 : ℕ) = 1 - sa ^ (2 : ℕ) := by
    nlinarith [hsq]
  have hca3 : ca ^ (3 : ℕ) = ca * (1 - sa ^ (2 : ℕ)) := by
    rw [show ca ^ (3 : ℕ) = ca * ca ^ (2 : ℕ) by ring, hca2]
  have hca4 : ca ^ (4 : ℕ) = (1 - sa ^ (2 : ℕ)) ^ (2 : ℕ) := by
    rw [show ca ^ (4 : ℕ) = (ca ^ (2 : ℕ)) ^ (2 : ℕ) by ring, hca2]
  have hca5 : ca ^ (5 : ℕ) = ca * (1 - sa ^ (2 : ℕ)) ^ (2 : ℕ) := by
    rw [show ca ^ (5 : ℕ) = ca * ca ^ (4 : ℕ) by ring, hca4]
  have hsqrt_four : (Real.sqrt 3) ^ (4 : ℕ) = 9 := by
    calc
      (Real.sqrt 3) ^ (4 : ℕ) = ((Real.sqrt 3) ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
      _ = 9 := by rw [hsqrt_sq]; norm_num
  have hleft :
      T ![c • e₁ + s • e₂, e₂, e₂] = c * C + s * D := by
    -- The left side only uses the canonical basis monomials with two `e₂` slots.
    rw [trilinearApplyAddFirst, trilinearApplySmulFirst, trilinearApplySmulFirst]
  have hv₀ :
      T ![v₀, v₀, v₀] =
        sa ^ (3 : ℕ) * A +
          3 * sa ^ (2 : ℕ) * ca * B +
            3 * sa * ca ^ (2 : ℕ) * C +
              ca ^ (3 : ℕ) * D := by
    -- The first sample is the direct diagonal expansion of `(sa,ca)`.
    simpa [v₀, A, B, C, D] using
      symmetricTrilinear_diagonalOnTwoVectors T hswap12 hswap23 e₁ e₂ sa ca
  have hv₁ :
      T ![v₁, v₁, v₁] =
        a₁ ^ (3 : ℕ) * A +
          3 * a₁ ^ (2 : ℕ) * b₁ * B +
            3 * a₁ * b₁ ^ (2 : ℕ) * C +
              b₁ ^ (3 : ℕ) * D := by
    -- The second sample uses the same diagonal expansion at the rotated coefficients.
    simpa [v₁, a₁, b₁, A, B, C, D] using
      symmetricTrilinear_diagonalOnTwoVectors T hswap12 hswap23 e₁ e₂ a₁ b₁
  have hv₂ :
      T ![v₂, v₂, v₂] =
        a₂ ^ (3 : ℕ) * A +
          3 * a₂ ^ (2 : ℕ) * b₂ * B +
            3 * a₂ * b₂ ^ (2 : ℕ) * C +
              b₂ ^ (3 : ℕ) * D := by
    -- The third sample is the reflected rotated coefficient pair.
    simpa [v₂, a₂, b₂, A, B, C, D] using
      symmetricTrilinear_diagonalOnTwoVectors T hswap12 hswap23 e₁ e₂ a₂ b₂
  have hA :
      l₀ * sa ^ (3 : ℕ) + l₁ * a₁ ^ (3 : ℕ) + l₂ * a₂ ^ (3 : ℕ) = 0 := by
    -- The `T[e₁,e₁,e₁]` coefficient cancels from the three-sample combination.
    simp [l₀, l₁, l₂, a₁, a₂]
    ring_nf
    rw [hsqrt_four, hsqrt_sq, hca4, hca2]
    ring_nf
  have hB :
      l₀ * (3 * sa ^ (2 : ℕ) * ca) +
        l₁ * (3 * a₁ ^ (2 : ℕ) * b₁) +
          l₂ * (3 * a₂ ^ (2 : ℕ) * b₂) = 0 := by
    -- The `T[e₁,e₁,e₂]` coefficient cancels for the same reason.
    simp [l₀, l₁, l₂, a₁, b₁, a₂, b₂]
    ring_nf
    rw [hsqrt_four, hsqrt_sq, hca5, hca3]
    ring_nf
  have hC :
      l₀ * (3 * sa * ca ^ (2 : ℕ)) +
        l₁ * (3 * a₁ * b₁ ^ (2 : ℕ)) +
          l₂ * (3 * a₂ * b₂ ^ (2 : ℕ)) = c := by
    -- The surviving `T[e₁,e₂,e₂]` coefficient is exactly the cubic-angle sine expression.
    rw [hc]
    simp [l₀, l₁, l₂, a₁, b₁, a₂, b₂]
    ring_nf
    rw [hsqrt_four, hsqrt_sq, hca4, hca2]
    ring_nf
  have hD :
      l₀ * ca ^ (3 : ℕ) + l₁ * b₁ ^ (3 : ℕ) + l₂ * b₂ ^ (3 : ℕ) = s := by
    -- The surviving `T[e₂,e₂,e₂]` coefficient is exactly the cubic-angle cosine expression.
    rw [hs]
    simp [l₀, l₁, l₂, b₁, b₂]
    ring_nf
    rw [hsqrt_four, hsqrt_sq, hca5, hca3]
    ring_nf
  rw [hleft, hv₀, hv₁, hv₂]
  -- Regroup the diagonal expansions by the four canonical basis monomials and use the scalar
  -- coefficient identities proved above.
  have hcollect :
      l₀ * (sa ^ (3 : ℕ) * A + 3 * sa ^ (2 : ℕ) * ca * B + 3 * sa * ca ^ (2 : ℕ) * C +
          ca ^ (3 : ℕ) * D) +
        l₁ * (a₁ ^ (3 : ℕ) * A + 3 * a₁ ^ (2 : ℕ) * b₁ * B + 3 * a₁ * b₁ ^ (2 : ℕ) * C +
          b₁ ^ (3 : ℕ) * D) +
          l₂ * (a₂ ^ (3 : ℕ) * A + 3 * a₂ ^ (2 : ℕ) * b₂ * B +
            3 * a₂ * b₂ ^ (2 : ℕ) * C + b₂ ^ (3 : ℕ) * D) =
        (l₀ * sa ^ (3 : ℕ) + l₁ * a₁ ^ (3 : ℕ) + l₂ * a₂ ^ (3 : ℕ)) * A +
          (l₀ * (3 * sa ^ (2 : ℕ) * ca) + l₁ * (3 * a₁ ^ (2 : ℕ) * b₁) +
            l₂ * (3 * a₂ ^ (2 : ℕ) * b₂)) * B +
              (l₀ * (3 * sa * ca ^ (2 : ℕ)) + l₁ * (3 * a₁ * b₁ ^ (2 : ℕ)) +
                l₂ * (3 * a₂ * b₂ ^ (2 : ℕ))) * C +
                  (l₀ * ca ^ (3 : ℕ) + l₁ * b₁ ^ (3 : ℕ) + l₂ * b₂ ^ (3 : ℕ)) * D := by
    ring
  rw [hcollect, hA, hB, hC, hD]
  ring

/-- Helper for Corollary 5 1 1: in the first-quadrant unit-circle case, the mixed repeated-slot
term is bounded by the diagonal cubic bound through the three-sample interpolation formula. -/
private lemma symmetricTrilinear_unitCircle_dvvBound_onNormModel2D_nonneg
    {x e₁ e₂ : E}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (hswap12 : ∀ a b c : E, T ![a, b, c] = T ![b, a, c])
    (hswap23 : ∀ a b c : E, T ![a, b, c] = T ![a, c, b])
    (Mf : NNReal) (f : E → ℝ)
    (hnorm_model :
      ∀ a b : ℝ, ‖a • e₁ + b • e₂‖[f; x] ^ (2 : ℕ) = a ^ (2 : ℕ) + b ^ (2 : ℕ))
    (hdiag :
      ∀ z : E, |T ![z, z, z]| ≤ 2 * (Mf : ℝ) * ‖z‖[f; x] ^ (3 : ℕ))
    {c s : ℝ} (hc_nonneg : 0 ≤ c) (hs_nonneg : 0 ≤ s)
    (hunit : c ^ (2 : ℕ) + s ^ (2 : ℕ) = 1) :
    |T ![c • e₁ + s • e₂, e₂, e₂]| ≤ 2 * (Mf : ℝ) := by
  obtain ⟨sa, ca, hsq, hs, hc⟩ :=
    firstQuadrantUnitCircle_hasThirdAngleParameters hc_nonneg hs_nonneg hunit
  have hsqrt_sq : (Real.sqrt 3) ^ (2 : ℕ) = 3 := by
    rw [show (Real.sqrt 3) ^ (2 : ℕ) = (Real.sqrt 3) ^ 2 by rfl]
    rw [Real.sq_sqrt (by positivity)]
  have hsq' : sa * sa + ca * ca = 1 := by
    simpa [pow_two] using hsq
  have hca2 : ca ^ (2 : ℕ) = 1 - sa ^ (2 : ℕ) := by
    nlinarith [hsq]
  set l₀ : ℝ := (4 * sa ^ (2 : ℕ) - 3) ^ (2 : ℕ) / 9
  set l₁ : ℝ := (4 : ℝ) / 9 * sa ^ (2 : ℕ) * (sa + Real.sqrt 3 * ca) ^ (2 : ℕ)
  set l₂ : ℝ := (4 : ℝ) / 9 * sa ^ (2 : ℕ) * (sa - Real.sqrt 3 * ca) ^ (2 : ℕ)
  set a₁ : ℝ := -sa / 2 + (Real.sqrt 3 / 2) * ca
  set b₁ : ℝ := -ca / 2 - (Real.sqrt 3 / 2) * sa
  set a₂ : ℝ := -sa / 2 - (Real.sqrt 3 / 2) * ca
  set b₂ : ℝ := -ca / 2 + (Real.sqrt 3 / 2) * sa
  set v₀ : E := sa • e₁ + ca • e₂
  set v₁ : E := a₁ • e₁ + b₁ • e₂
  set v₂ : E := a₂ • e₁ + b₂ • e₂
  have hv₀_unit : sa ^ (2 : ℕ) + ca ^ (2 : ℕ) = 1 := hsq
  have hv₁_unit : a₁ ^ (2 : ℕ) + b₁ ^ (2 : ℕ) = 1 := by
    -- The second sample is a Euclidean rotation of `(sa,ca)`.
    simp [a₁, b₁]
    ring_nf
    rw [hsqrt_sq, hca2]
    ring_nf
  have hv₂_unit : a₂ ^ (2 : ℕ) + b₂ ^ (2 : ℕ) = 1 := by
    -- The third sample is the opposite Euclidean rotation of `(sa,ca)`.
    simp [a₂, b₂]
    ring_nf
    rw [hsqrt_sq, hca2]
    ring_nf
  have hbound₀ :
      |T ![v₀, v₀, v₀]| ≤ 2 * (Mf : ℝ) := by
    -- Each diagonal sample lies on the normalized unit circle, so the diagonal bound loses the
    -- norm factor.
    simpa [v₀] using unitCircleDiagonalSampleBound T Mf f hnorm_model hdiag sa ca hv₀_unit
  have hbound₁ :
      |T ![v₁, v₁, v₁]| ≤ 2 * (Mf : ℝ) := by
    simpa [v₁] using unitCircleDiagonalSampleBound T Mf f hnorm_model hdiag a₁ b₁ hv₁_unit
  have hbound₂ :
      |T ![v₂, v₂, v₂]| ≤ 2 * (Mf : ℝ) := by
    simpa [v₂] using unitCircleDiagonalSampleBound T Mf f hnorm_model hdiag a₂ b₂ hv₂_unit
  have hl₀_nonneg : 0 ≤ l₀ := by
    -- The interpolation weights are manifestly nonnegative squares.
    positivity
  have hl₁_nonneg : 0 ≤ l₁ := by
    positivity
  have hl₂_nonneg : 0 ≤ l₂ := by
    positivity
  have hweights :
      l₀ + l₁ + l₂ = 1 := by
    -- The three interpolation weights form a partition of unity.
    simp [l₀, l₁, l₂]
    ring_nf
    rw [hsqrt_sq, hca2]
    ring_nf
  have hinterp :=
    symmetricTrilinear_thirdAngleInterpolation T hswap12 hswap23
      (x := x) (e₁ := e₁) (e₂ := e₂) (sa := sa) (ca := ca) (c := c) (s := s) hsq hs hc
  have hinterp' :
      T ![c • e₁ + s • e₂, e₂, e₂] =
        l₀ * T ![v₀, v₀, v₀] + l₁ * T ![v₁, v₁, v₁] + l₂ * T ![v₂, v₂, v₂] := by
    simpa [l₀, l₁, l₂, v₀, v₁, v₂, a₁, b₁, a₂, b₂] using hinterp
  rw [hinterp']
  have habs₀ : |l₀ * T ![v₀, v₀, v₀]| = l₀ * |T ![v₀, v₀, v₀]| := by
    rw [abs_mul, abs_of_nonneg hl₀_nonneg]
  have habs₁ : |l₁ * T ![v₁, v₁, v₁]| = l₁ * |T ![v₁, v₁, v₁]| := by
    rw [abs_mul, abs_of_nonneg hl₁_nonneg]
  have habs₂ : |l₂ * T ![v₂, v₂, v₂]| = l₂ * |T ![v₂, v₂, v₂]| := by
    rw [abs_mul, abs_of_nonneg hl₂_nonneg]
  -- Apply the triangle inequality and then collapse the convex combination of the three sample
  -- bounds.
  have htri :
      |l₀ * T ![v₀, v₀, v₀] + l₁ * T ![v₁, v₁, v₁] + l₂ * T ![v₂, v₂, v₂]| ≤
        |l₀ * T ![v₀, v₀, v₀]| + |l₁ * T ![v₁, v₁, v₁]| + |l₂ * T ![v₂, v₂, v₂]| := by
    calc
      |l₀ * T ![v₀, v₀, v₀] + l₁ * T ![v₁, v₁, v₁] + l₂ * T ![v₂, v₂, v₂]|
          = |l₀ * T ![v₀, v₀, v₀] + (l₁ * T ![v₁, v₁, v₁] + l₂ * T ![v₂, v₂, v₂])| := by
              ring_nf
      _ ≤ |l₀ * T ![v₀, v₀, v₀]| + |l₁ * T ![v₁, v₁, v₁] + l₂ * T ![v₂, v₂, v₂]| :=
            abs_add_le _ _
      _ ≤ |l₀ * T ![v₀, v₀, v₀]| +
            (|l₁ * T ![v₁, v₁, v₁]| + |l₂ * T ![v₂, v₂, v₂]|) := by
              gcongr
              exact abs_add_le _ _
      _ = |l₀ * T ![v₀, v₀, v₀]| + |l₁ * T ![v₁, v₁, v₁]| + |l₂ * T ![v₂, v₂, v₂]| := by
            simp [add_assoc]
  calc
    |l₀ * T ![v₀, v₀, v₀] + l₁ * T ![v₁, v₁, v₁] + l₂ * T ![v₂, v₂, v₂]|
        ≤ |l₀ * T ![v₀, v₀, v₀]| + |l₁ * T ![v₁, v₁, v₁]| + |l₂ * T ![v₂, v₂, v₂]| :=
          htri
    _ = l₀ * |T ![v₀, v₀, v₀]| + l₁ * |T ![v₁, v₁, v₁]| + l₂ * |T ![v₂, v₂, v₂]| := by
          rw [habs₀, habs₁, habs₂]
    _ ≤ l₀ * (2 * (Mf : ℝ)) + l₁ * (2 * (Mf : ℝ)) + l₂ * (2 * (Mf : ℝ)) := by
          gcongr
    _ = (l₀ + l₁ + l₂) * (2 * (Mf : ℝ)) := by ring
    _ = 2 * (Mf : ℝ) := by rw [hweights]; ring

private lemma symmetricTrilinear_unitCircle_dvvBound_onNormModel2D
    {x e₁ e₂ : E}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (hswap12 : ∀ a b c : E, T ![a, b, c] = T ![b, a, c])
    (hswap23 : ∀ a b c : E, T ![a, b, c] = T ![a, c, b])
    (Mf : NNReal) (f : E → ℝ)
    (hnorm_model :
      ∀ a b : ℝ, ‖a • e₁ + b • e₂‖[f; x] ^ (2 : ℕ) = a ^ (2 : ℕ) + b ^ (2 : ℕ))
    (hdiag :
      ∀ z : E, |T ![z, z, z]| ≤ 2 * (Mf : ℝ) * ‖z‖[f; x] ^ (3 : ℕ)) :
    ∀ c s : ℝ, c ^ (2 : ℕ) + s ^ (2 : ℕ) = 1 →
      |T ![c • e₁ + s • e₂, e₂, e₂]| ≤ 2 * (Mf : ℝ) := by
  intro c s hunit
  let σc : ℝ := if 0 ≤ c then 1 else -1
  let σs : ℝ := if 0 ≤ s then 1 else -1
  let e₁' : E := σc • e₁
  let e₂' : E := σs • e₂
  have hσc_sq : σc ^ (2 : ℕ) = 1 := by
    dsimp [σc]
    split_ifs <;> norm_num
  have hσs_sq : σs ^ (2 : ℕ) = 1 := by
    dsimp [σs]
    split_ifs <;> norm_num
  have hc_nonneg : 0 ≤ |c| := abs_nonneg c
  have hs_nonneg : 0 ≤ |s| := abs_nonneg s
  have hunit_abs : |c| ^ (2 : ℕ) + |s| ^ (2 : ℕ) = 1 := by
    simpa [pow_two] using hunit
  have hc_sign : c = σc * |c| := by
    dsimp [σc]
    split_ifs with hc
    · rw [abs_of_nonneg hc]
      ring
    · have hc_lt : c < 0 := lt_of_not_ge hc
      rw [abs_of_neg hc_lt]
      ring
  have hs_sign : s = σs * |s| := by
    dsimp [σs]
    split_ifs with hs
    · rw [abs_of_nonneg hs]
      ring
    · have hs_lt : s < 0 := lt_of_not_ge hs
      rw [abs_of_neg hs_lt]
      ring
  have hnorm_model' :
      ∀ a b : ℝ, ‖a • e₁' + b • e₂'‖[f; x] ^ (2 : ℕ) = a ^ (2 : ℕ) + b ^ (2 : ℕ) := by
    intro a b
    -- Flipping basis-vector signs preserves the same normalized 2D norm model.
    dsimp [e₁', e₂']
    calc
      ‖a • (σc • e₁) + b • (σs • e₂)‖[f; x] ^ (2 : ℕ)
          = ‖(a * σc) • e₁ + (b * σs) • e₂‖[f; x] ^ (2 : ℕ) := by
              simp [smul_smul]
      _ = (a * σc) ^ (2 : ℕ) + (b * σs) ^ (2 : ℕ) := hnorm_model (a * σc) (b * σs)
      _ = a ^ (2 : ℕ) + b ^ (2 : ℕ) := by
            nlinarith [hσc_sq, hσs_sq]
  have hrew :
      T ![|c| • e₁' + |s| • e₂', e₂', e₂'] = T ![c • e₁ + s • e₂, e₂, e₂] := by
    -- The first slot is unchanged by the signed basis flip, and the repeated slots square away
    -- the sign on `e₂`.
    dsimp [e₁', e₂']
    rw [trilinearApplySmulSecond, trilinearApplySmulThird]
    have hfirst :
        |c| • (σc • e₁) + |s| • (σs • e₂) = c • e₁ + s • e₂ := by
      rw [smul_smul, smul_smul, mul_comm |c| σc, mul_comm |s| σs, ← hc_sign, ← hs_sign]
    rw [hfirst]
    calc
      σs * (σs * T ![c • e₁ + s • e₂, e₂, e₂])
          = (σs ^ (2 : ℕ)) * T ![c • e₁ + s • e₂, e₂, e₂] := by ring
      _ = T ![c • e₁ + s • e₂, e₂, e₂] := by rw [hσs_sq]; ring
  -- Route correction: reduce the arbitrary-sign unit-circle case to the first-quadrant case by
  -- flipping the basis vectors, then apply the explicit three-sample interpolation bound there.
  have hbound_abs :
      |T ![|c| • e₁' + |s| • e₂', e₂', e₂']| ≤ 2 * (Mf : ℝ) :=
    symmetricTrilinear_unitCircle_dvvBound_onNormModel2D_nonneg
      (T := T) (e₁ := e₁') (e₂ := e₂')
      hswap12 hswap23 (Mf := Mf) (f := f) hnorm_model' hdiag
      hc_nonneg hs_nonneg hunit_abs
  rw [← hrew]
  exact hbound_abs

/-- Helper for Corollary 5 1 1: after normalizing the coefficients to the unit circle, the pure
2D unit-circle estimate immediately rescales back to arbitrary coefficients. -/
private lemma symmetricTrilinear_dvvBound_ofDiagonalBound_onNormModel2D
    {x e₁ e₂ : E}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (hswap12 : ∀ a b c : E, T ![a, b, c] = T ![b, a, c])
    (hswap23 : ∀ a b c : E, T ![a, b, c] = T ![a, c, b])
    (Mf : NNReal) (f : E → ℝ)
    (hnorm_model :
      ∀ a b : ℝ, ‖a • e₁ + b • e₂‖[f; x] ^ (2 : ℕ) = a ^ (2 : ℕ) + b ^ (2 : ℕ))
    (hdiag :
      ∀ z : E, |T ![z, z, z]| ≤ 2 * (Mf : ℝ) * ‖z‖[f; x] ^ (3 : ℕ)) :
    ∀ a b : ℝ,
      |T ![a • e₁ + b • e₂, e₂, e₂]| ≤
        2 * (Mf : ℝ) * Real.sqrt (a ^ (2 : ℕ) + b ^ (2 : ℕ)) := by
  intro a b
  let r : ℝ := Real.sqrt (a ^ (2 : ℕ) + b ^ (2 : ℕ))
  by_cases hr : r = 0
  · have hsq : r ^ (2 : ℕ) = 0 := by simpa [hr]
    have hab : a ^ (2 : ℕ) + b ^ (2 : ℕ) = 0 := by
      change (Real.sqrt (a ^ (2 : ℕ) + b ^ (2 : ℕ))) ^ (2 : ℕ) = 0 at hsq
      rw [Real.sq_sqrt (by positivity)] at hsq
      exact hsq
    have ha : a = 0 := by
      nlinarith [sq_nonneg a, sq_nonneg b, hab]
    have hb : b = 0 := by
      nlinarith [sq_nonneg a, sq_nonneg b, hab]
    have hzeroVec : T ![0, e₂, e₂] = 0 := by
      simpa using trilinearApplySmulFirst T 0 e₁ e₂ e₂
    -- In the zero-radius branch, both coefficients vanish and the bound is immediate.
    have hleft : |T ![a • e₁ + b • e₂, e₂, e₂]| = 0 := by
      rw [ha, hb]
      simp [hzeroVec]
    rw [hleft]
    simp [ha, hb]
  · obtain ⟨hvec, hunit⟩ :=
      normModel2D_normalizeCoeffs (e₁ := e₁) (e₂ := e₂) (a := a) (b := b) (r := r) rfl hr
    have hunitBound :
        |T ![(a / r) • e₁ + (b / r) • e₂, e₂, e₂]| ≤ 2 * (Mf : ℝ) :=
      symmetricTrilinear_unitCircle_dvvBound_onNormModel2D
        (T := T) (e₁ := e₁) (e₂ := e₂)
        hswap12 hswap23 (Mf := Mf) (f := f) hnorm_model hdiag
        (a / r) (b / r) hunit
    -- Pull the scalar `r` back out of the first slot and use that `r` is a square root.
    calc
      |T ![a • e₁ + b • e₂, e₂, e₂]|
          = |T ![r • ((a / r) • e₁ + (b / r) • e₂), e₂, e₂]| := by rw [hvec]
      _ = |r * T ![(a / r) • e₁ + (b / r) • e₂, e₂, e₂]| := by
            rw [trilinearApplySmulFirst]
      _ = |r| * |T ![(a / r) • e₁ + (b / r) • e₂, e₂, e₂]| := by rw [abs_mul]
      _ ≤ |r| * (2 * (Mf : ℝ)) := by
            gcongr
      _ = 2 * (Mf : ℝ) * Real.sqrt (a ^ (2 : ℕ) + b ^ (2 : ℕ)) := by
            rw [abs_of_nonneg (by
              dsimp [r]
              exact Real.sqrt_nonneg _)]
            dsimp [r]
            ring

/-- Helper for Corollary 5 1 1: once the third iterated derivative factors through the Hessian
radical, the remaining blocker is the sharp Banach-type estimate on the quotient local Hilbert
norm. -/
private lemma symmetric_trilinear_dvv_bound_of_diagonal_bound
    {Mf : NNReal} {f : E → ℝ} {x : E}
    (hcontAt : ContDiffAt ℝ 3 f x)
    (hxPos : (hessian f x).IsPositive)
    (hdiag_iter : ∀ z : E,
      |iteratedFDeriv ℝ 3 f x ![z, z, z]| ≤
        2 * (Mf : ℝ) * ‖z‖[f; x] ^ (3 : ℕ)) :
    ∀ d v : E,
      |iteratedFDeriv ℝ 3 f x ![d, v, v]| ≤
        2 * (Mf : ℝ) * ‖d‖[f; x] * ‖v‖[f; x] ^ (2 : ℕ) := by
  intro d v
  by_cases hd : ‖d‖[f; x] = 0
  · have hd_ann :
        ∀ z : E, inner ℝ d (hessian f x z) = 0 :=
      (hessian_localRadical_iff_annihilates_hessian (f := f) (x := x) (u := d) hxPos).1 hd
    have hzero :
        iteratedFDeriv ℝ 3 f x ![d, v, v] = 0 :=
      iteratedFDeriv_vanishes_on_hessian_localRadical
        (Mf := Mf) (f := f) (x := x) (u := d) (w := v) hcontAt hxPos
        (fun z ↦ by
          have hconst : (fun _ : Fin 3 ↦ z) = ![z, z, z] := by
            ext i
            fin_cases i <;> rfl
          simpa [thirdDirectionalDerivative_eq_iteratedFDeriv hcontAt, hconst] using
            hdiag_iter z)
        hd_ann
    -- Once the first slot is radical, the mixed third derivative is zero and the target bound is
    -- immediate because the right-hand side also vanishes.
    simpa [hzero, hd]
  by_cases hv : ‖v‖[f; x] = 0
  · have hv_ann :
        ∀ z : E, inner ℝ v (hessian f x z) = 0 :=
      (hessian_localRadical_iff_annihilates_hessian (f := f) (x := x) (u := v) hxPos).1 hv
    have hzero :
        iteratedFDeriv ℝ 3 f x ![d, v, v] = 0 :=
      iteratedFDeriv_dvv_vanishes_on_hessian_localRadical
        (Mf := Mf) (f := f) (x := x) (d := d) (v := v) hcontAt hxPos
        (fun z ↦ by
          have hconst : (fun _ : Fin 3 ↦ z) = ![z, z, z] := by
            ext i
            fin_cases i <;> rfl
          simpa [thirdDirectionalDerivative_eq_iteratedFDeriv hcontAt, hconst] using
            hdiag_iter z)
        hv_ann
    -- The repeated-slot radical case is the same after one symmetry swap.
    simpa [hzero, hv]
  have hd_pos : 0 < ‖d‖[f; x] :=
    lt_of_le_of_ne (hessianLocalNorm_nonneg f x d) (by
      intro hzero
      exact hd hzero.symm)
  have hv_pos : 0 < ‖v‖[f; x] :=
    lt_of_le_of_ne (hessianLocalNorm_nonneg f x v) (by
      intro hzero
      exact hv hzero.symm)
  have _hd_nonzero : ‖d‖[f; x] ≠ 0 := ne_of_gt hd_pos
  have _hv_nonzero : ‖v‖[f; x] ≠ 0 := ne_of_gt hv_pos
  let α : ℝ := inner ℝ d (hessian f x v) / ‖v‖[f; x] ^ (2 : ℕ)
  let w : E := d - α • v
  have hsplit :
      inner ℝ w (hessian f x v) = 0 ∧
        ‖d‖[f; x] ^ (2 : ℕ) = ‖w‖[f; x] ^ (2 : ℕ) + (α * ‖v‖[f; x]) ^ (2 : ℕ) := by
    simpa [α, w] using
      hessianProjectionSplit (f := f) (x := x) (d := d) (v := v) hxPos hv
  obtain ⟨horth, hpyth⟩ := hsplit
  have hd_eq : d = w + α • v := by
    -- Rewrite the original direction into the orthogonal residual plus the `v`-component.
    dsimp [w]
    abel_nf
  by_cases hw : ‖w‖[f; x] = 0
  · have hw_ann :
        ∀ z : E, inner ℝ w (hessian f x z) = 0 :=
      (hessian_localRadical_iff_annihilates_hessian (f := f) (x := x) (u := w) hxPos).1 hw
    have hw_zero :
        iteratedFDeriv ℝ 3 f x ![w, v, v] = 0 :=
      iteratedFDeriv_vanishes_on_hessian_localRadical
        (Mf := Mf) (f := f) (x := x) (u := w) (w := v) hcontAt hxPos
        (fun z ↦ by
          have hconst : (fun _ : Fin 3 ↦ z) = ![z, z, z] := by
            ext i
            fin_cases i <;> rfl
          simpa [thirdDirectionalDerivative_eq_iteratedFDeriv hcontAt, hconst] using
            hdiag_iter z)
        hw_ann
    have hd_abs : ‖d‖[f; x] = |α| * ‖v‖[f; x] := by
      have hd_sq :
          ‖d‖[f; x] ^ (2 : ℕ) = (α * ‖v‖[f; x]) ^ (2 : ℕ) := by
        simpa [hw] using hpyth
      have hsqrt := congrArg Real.sqrt hd_sq
      simpa [Real.sqrt_sq_eq_abs, abs_mul, abs_of_nonneg (hessianLocalNorm_nonneg f x d),
        abs_of_nonneg (hessianLocalNorm_nonneg f x v)] using hsqrt
    -- Once the residual is radical, only the diagonal `v` contribution survives.
    calc
      |iteratedFDeriv ℝ 3 f x ![d, v, v]|
          = |iteratedFDeriv ℝ 3 f x ![w + α • v, v, v]| := by rw [hd_eq]
      _ = |iteratedFDeriv ℝ 3 f x ![w, v, v] + iteratedFDeriv ℝ 3 f x ![α • v, v, v]| := by
            rw [trilinearApplyAddFirst]
      _ = |α * iteratedFDeriv ℝ 3 f x ![v, v, v]| := by
            rw [hw_zero, trilinearApplySmulFirst]
            simp
      _ = |α| * |iteratedFDeriv ℝ 3 f x ![v, v, v]| := by rw [abs_mul]
      _ ≤ |α| * (2 * (Mf : ℝ) * ‖v‖[f; x] ^ (3 : ℕ)) := by
            gcongr
            exact hdiag_iter v
      _ = 2 * (Mf : ℝ) * (|α| * ‖v‖[f; x]) * ‖v‖[f; x] ^ (2 : ℕ) := by
            ring
      _ = 2 * (Mf : ℝ) * ‖d‖[f; x] * ‖v‖[f; x] ^ (2 : ℕ) := by
            rw [← hd_abs]
  have hw_pos : 0 < ‖w‖[f; x] :=
    lt_of_le_of_ne (hessianLocalNorm_nonneg f x w) (by
      intro hzero
      exact hw hzero.symm)
  let e₁ : E := (‖w‖[f; x])⁻¹ • w
  let e₂ : E := (‖v‖[f; x])⁻¹ • v
  have he₁_norm : ‖e₁‖[f; x] = 1 := by
    -- Normalize the nonradical residual direction.
    dsimp [e₁]
    rw [hessianLocalNorm_smul_eq_abs_of_isPositive (f := f) (x := x) (u := w) hxPos]
    simp [abs_of_pos (inv_pos.mpr hw_pos), hw_pos.ne']
  have he₂_norm : ‖e₂‖[f; x] = 1 := by
    -- Normalize the original repeated direction.
    dsimp [e₂]
    rw [hessianLocalNorm_smul_eq_abs_of_isPositive (f := f) (x := x) (u := v) hxPos]
    simp [abs_of_pos (inv_pos.mpr hv_pos), hv_pos.ne']
  have he₁e₂_orth : inner ℝ e₁ (hessian f x e₂) = 0 := by
    -- The normalized pair remains orthogonal for the Hessian bilinear form.
    simp [e₁, e₂, inner_smul_left, inner_smul_right, horth]
  have hnorm_model :
      ∀ a b : ℝ, ‖a • e₁ + b • e₂‖[f; x] ^ (2 : ℕ) = a ^ (2 : ℕ) + b ^ (2 : ℕ) :=
    hessianLocalNorm_sq_of_localOrthonormalPair
      (f := f) (x := x) (e₁ := e₁) (e₂ := e₂) hxPos he₁_norm he₂_norm he₁e₂_orth
  have hw_scale : ‖w‖[f; x] • e₁ = w := by
    -- Rescaling the normalized residual recovers the original residual vector.
    dsimp [e₁]
    rw [smul_smul, mul_inv_cancel₀ hw_pos.ne', one_smul]
  have hv_scale : (α * ‖v‖[f; x]) • e₂ = α • v := by
    -- Rescaling the normalized repeated direction recovers its original `α`-multiple.
    dsimp [e₂]
    rw [smul_smul, mul_assoc, mul_inv_cancel₀ hv_pos.ne', mul_one]
  have hd_model :
      d = ‖w‖[f; x] • e₁ + (α * ‖v‖[f; x]) • e₂ := by
    -- The orthogonal split is now expressed in the normalized local-orthonormal basis.
    calc
      d = w + α • v := hd_eq
      _ = ‖w‖[f; x] • e₁ + (α * ‖v‖[f; x]) • e₂ := by
            rw [hw_scale, hv_scale]
  have hv_scale' : ‖v‖[f; x] • e₂ = v := by
    -- Rescaling the normalized repeated direction recovers the original repeated vector.
    dsimp [e₂]
    rw [smul_smul, mul_inv_cancel₀ hv_pos.ne', one_smul]
  let T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ := iteratedFDeriv ℝ 3 f x
  have hswap12 :
      ∀ a b c : E, T ![a, b, c] = T ![b, a, c] := by
    intro a b c
    simpa [T] using
      iteratedFDeriv_three_swap12_at
        (f := f) (x := x) (u₁ := a) (u₂ := b) (u₃ := c) hcontAt
  have hswap23 :
      ∀ a b c : E, T ![a, b, c] = T ![a, c, b] := by
    intro a b c
    simpa [T] using
      iteratedFDeriv_three_swap23_at
        (f := f) (x := x) (u₁ := a) (u₂ := b) (u₃ := c) hcontAt
  have hdiag_model :
      ∀ z : E, |T ![z, z, z]| ≤ 2 * (Mf : ℝ) * ‖z‖[f; x] ^ (3 : ℕ) := by
    intro z
    simpa [T] using hdiag_iter z
  have hmodel_bound :
      |T ![‖w‖[f; x] • e₁ + (α * ‖v‖[f; x]) • e₂, e₂, e₂]| ≤
        2 * (Mf : ℝ) *
          Real.sqrt (‖w‖[f; x] ^ (2 : ℕ) + (α * ‖v‖[f; x]) ^ (2 : ℕ)) :=
    symmetricTrilinear_dvvBound_ofDiagonalBound_onNormModel2D
      (T := T) (e₁ := e₁) (e₂ := e₂)
      hswap12 hswap23 (Mf := Mf) (f := f) hnorm_model hdiag_model
      ‖w‖[f; x] (α * ‖v‖[f; x])
  have hroot :
      Real.sqrt (‖w‖[f; x] ^ (2 : ℕ) + (α * ‖v‖[f; x]) ^ (2 : ℕ)) = ‖d‖[f; x] := by
    -- The orthogonal decomposition identifies the Euclidean model radius with `‖d‖[f; x]`.
    have hsqrt := congrArg Real.sqrt hpyth.symm
    simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg (hessianLocalNorm_nonneg f x d)] using hsqrt
  -- Route correction: the main theorem is now reduced to the unit-circle 2D lemma above, plus the
  -- already-verified normalization and scaling rewrites in the model `(e₁, e₂)`.
  calc
    |iteratedFDeriv ℝ 3 f x ![d, v, v]| = |T ![d, v, v]| := by rfl
    _ = |T ![‖w‖[f; x] • e₁ + (α * ‖v‖[f; x]) • e₂, v, v]| := by rw [hd_model]
    _ = |T ![‖w‖[f; x] • e₁ + (α * ‖v‖[f; x]) • e₂, ‖v‖[f; x] • e₂, ‖v‖[f; x] • e₂]| := by
          have hslots :
              ![‖w‖[f; x] • e₁ + (α * ‖v‖[f; x]) • e₂, v, v] =
                ![‖w‖[f; x] • e₁ + (α * ‖v‖[f; x]) • e₂,
                  ‖v‖[f; x] • e₂, ‖v‖[f; x] • e₂] := by
            ext i
            fin_cases i <;> simp [hv_scale']
          rw [hslots]
    _ = |‖v‖[f; x] * (‖v‖[f; x] *
          T ![‖w‖[f; x] • e₁ + (α * ‖v‖[f; x]) • e₂, e₂, e₂])| := by
          rw [trilinearApplySmulSecond, trilinearApplySmulThird]
    _ = ‖v‖[f; x] ^ (2 : ℕ) *
          |T ![‖w‖[f; x] • e₁ + (α * ‖v‖[f; x]) • e₂, e₂, e₂]| := by
          simp [pow_two, abs_of_nonneg (hessianLocalNorm_nonneg f x v), mul_assoc, mul_comm]
    _ ≤ ‖v‖[f; x] ^ (2 : ℕ) *
          (2 * (Mf : ℝ) *
            Real.sqrt (‖w‖[f; x] ^ (2 : ℕ) + (α * ‖v‖[f; x]) ^ (2 : ℕ))) := by
          gcongr
    _ = 2 * (Mf : ℝ) *
          Real.sqrt (‖w‖[f; x] ^ (2 : ℕ) + (α * ‖v‖[f; x]) ^ (2 : ℕ)) *
            ‖v‖[f; x] ^ (2 : ℕ) := by
          ring
    _ = 2 * (Mf : ℝ) * ‖d‖[f; x] * ‖v‖[f; x] ^ (2 : ℕ) := by rw [hroot]

/-- Helper for Corollary 5 1 1: the diagonal self-concordance bound should control the exact
mixed third-derivative slot pattern needed to test the Hessian-direction operator on quadratic
forms. -/
private lemma iteratedFDeriv_dvv_bound_of_third_deriv_bound
    {Mf : NNReal} {f : E → ℝ} {x : E}
    (hcontAt : ContDiffAt ℝ 3 f x)
    (hxPos : (hessian f x).IsPositive)
    (hdiag_x : ∀ u : E,
      |thirdDirectionalDerivative f x u| ≤
        2 * (Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ)) :
    ∀ d v : E,
      |iteratedFDeriv ℝ 3 f x ![d, v, v]| ≤
        2 * (Mf : ℝ) * ‖d‖[f; x] * ‖v‖[f; x] ^ (2 : ℕ) := by
  intro d v
  have hdiag_iter :
        ∀ z : E,
        |iteratedFDeriv ℝ 3 f x ![z, z, z]| ≤
          2 * (Mf : ℝ) * ‖z‖[f; x] ^ (3 : ℕ) := by
    intro z
    have hconst : (fun _ : Fin 3 ↦ z) = ![z, z, z] := by
      ext i
      fin_cases i <;> rfl
    -- Rewrite the textbook diagonal third derivative through the iterated derivative owner.
    simpa [thirdDirectionalDerivative_eq_iteratedFDeriv hcontAt, hconst] using hdiag_x z
  -- Route correction: the radical-vanishing step is now closed, so the frontier is exactly the
  -- sharp quotient-Hilbert estimate isolated in the dedicated helper above.
  exact symmetric_trilinear_dvv_bound_of_diagonal_bound
    (Mf := Mf) (f := f) (x := x) hcontAt hxPos hdiag_iter d v

/-- Helper for Corollary 5 1 1: the mixed scalar Hessian-direction pairing inherits the exact
quadratic-form bound needed for the forward Loewner argument. -/
private lemma mixed_hessian_pairing_bound_of_third_deriv_bound
    {Mf : NNReal} {f : E → ℝ} {x : E}
    (hcontAt : ContDiffAt ℝ 3 f x)
    (hxPos : (hessian f x).IsPositive)
    (hdiag_x : ∀ u : E,
      |thirdDirectionalDerivative f x u| ≤
        2 * (Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ)) :
    ∀ d v : E,
      |inner ℝ v ((fderiv ℝ (hessian f) x d) v)| ≤
        2 * (Mf : ℝ) * ‖d‖[f; x] * inner ℝ v (hessian f x v) := by
  intro d v
  have hv_quad_nonneg : 0 ≤ inner ℝ v (hessian f x v) :=
    hxPos.inner_nonneg_right v
  have hv_sq :
      ‖v‖[f; x] ^ (2 : ℕ) = inner ℝ v (hessian f x v) :=
    sq_hessianLocalNorm_eq_inner_of_nonneg hv_quad_nonneg
  have hiter :=
    iteratedFDeriv_dvv_bound_of_third_deriv_bound
      (Mf := Mf) (f := f) (x := x) hcontAt hxPos hdiag_x d v
  have hpair :
      inner ℝ v ((fderiv ℝ (hessian f) x d) v) = iteratedFDeriv ℝ 3 f x ![d, v, v] :=
    hessian_direction_pairing_eq_iteratedFDeriv
      (f := f) (x := x) (d := d) (w := v) (v := v) hcontAt
  -- Rewrite the mixed iterated-derivative bound through the scalar Hessian-direction pairing.
  calc
    |inner ℝ v ((fderiv ℝ (hessian f) x d) v)|
        = |iteratedFDeriv ℝ 3 f x ![d, v, v]| := by
            rw [hpair]
    _ ≤ 2 * (Mf : ℝ) * ‖d‖[f; x] * ‖v‖[f; x] ^ (2 : ℕ) := hiter
    _ = 2 * (Mf : ℝ) * ‖d‖[f; x] * inner ℝ v (hessian f x v) := by
          rw [hv_sq]

/-- Corollary 5.1.1, forward direction: the Chapter 5 owner `IsSelfConcordantOnWith dom Mf f`
implies the Hessian-direction operator inequality
`D³f(x)[u] ≤ 2 M_f ‖u‖_{∇² f(x)} ∇² f(x)` on `dom`. -/
theorem thirdDerivative_operator_le
    (hself : IsSelfConcordantOnWith dom Mf f) {x : E} (hx : x ∈ dom) (u : E) :
    fderiv ℝ (hessian f) x u ≤
      (2 * (Mf : ℝ) * ‖u‖[f; x]) • hessian f x := by
  have hcontAt : ContDiffAt ℝ 3 f x :=
    hself.contDiffOn.contDiffAt (hself.isOpen_domain.mem_nhds hx)
  have hxPos : (hessian f x).IsPositive := hself.hessian_isPositive hx
  rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_iff]
  constructor
  · -- The gap operator is symmetric because both the Hessian and its directional derivative are.
    intro v w
    have hhessSymm : inner ℝ (hessian f x v) w = inner ℝ v (hessian f x w) := by
      simpa using hxPos.isSymmetric v w
    have hderivSymm :
        inner ℝ (fderiv ℝ (hessian f) x u v) w =
          inner ℝ v (fderiv ℝ (hessian f) x u w) := by
      simpa using
        (third_derivative_operator_isSymmetric (f := f) (x := x) (d := u) hcontAt) v w
    calc
      inner ℝ (((2 * (Mf : ℝ) * ‖u‖[f; x]) • hessian f x - fderiv ℝ (hessian f) x u) v) w
          = (2 * (Mf : ℝ) * ‖u‖[f; x]) * inner ℝ (hessian f x v) w -
              inner ℝ (fderiv ℝ (hessian f) x u v) w := by
                simp [inner_sub_left, inner_smul_left]
      _ = (2 * (Mf : ℝ) * ‖u‖[f; x]) * inner ℝ v (hessian f x w) -
            inner ℝ v (fderiv ℝ (hessian f) x u w) := by
              rw [hhessSymm, hderivSymm]
      _ = inner ℝ v
            (((2 * (Mf : ℝ) * ‖u‖[f; x]) • hessian f x - fderiv ℝ (hessian f) x u) w) := by
              simp [inner_sub_right, inner_smul_right]
  · intro v
    have hpairBound :
        |inner ℝ v ((fderiv ℝ (hessian f) x u) v)| ≤
          2 * (Mf : ℝ) * ‖u‖[f; x] * inner ℝ v (hessian f x v) :=
      mixed_hessian_pairing_bound_of_third_deriv_bound
        (Mf := Mf) (f := f) (x := x) hcontAt hxPos (fun z ↦ hself.third_deriv_bound hx z) u v
    have hle :
        inner ℝ v ((fderiv ℝ (hessian f) x u) v) ≤
          2 * (Mf : ℝ) * ‖u‖[f; x] * inner ℝ v (hessian f x v) :=
      (abs_le.mp hpairBound).2
    -- Testing the gap operator on `v` reduces to the scalar mixed bound above.
    have hrewrite :
        inner ℝ (((2 * (Mf : ℝ) * ‖u‖[f; x]) • hessian f x - fderiv ℝ (hessian f) x u) v) v =
          (2 * (Mf : ℝ) * ‖u‖[f; x]) * inner ℝ v (hessian f x v) -
            inner ℝ v ((fderiv ℝ (hessian f) x u) v) := by
      simp [real_inner_comm, inner_sub_left, inner_smul_left]
    rw [hrewrite]
    linarith

/-- Corollary 5.1.1, converse direction: under the standing open-domain, `C³`, and convexity
assumptions, the Hessian-direction operator inequality reconstructs
`IsSelfConcordantOnWith dom Mf f`. -/
theorem of_thirdDerivative_operator_le
    (h_open : IsOpen dom) (h_contDiff : ContDiffOn ℝ 3 f dom) (h_convexOn : ConvexOn ℝ dom f)
    (hoperator : ∀ ⦃x : E⦄ (_hx : x ∈ dom) (u : E),
      fderiv ℝ (hessian f) x u ≤
        (2 * (Mf : ℝ) * ‖u‖[f; x]) • hessian f x) :
    IsSelfConcordantOnWith dom Mf f := by
  refine
    { isOpen_domain := h_open
      contDiffOn := h_contDiff
      convexOn := h_convexOn
      third_deriv_bound := ?_ }
  intro x hx u
  have hC2 : ContDiffOn ℝ 2 f dom := h_contDiff.of_le (by norm_num)
  have hxPos : (hessian f x).IsPositive :=
    ((convexOn_iff_hessian_isPositive h_open h_convexOn.1 hC2).1 h_convexOn) x hx
  have hcontAt : ContDiffAt ℝ 3 f x := h_contDiff.contDiffAt (h_open.mem_nhds hx)
  have hpair :
      inner ℝ u ((fderiv ℝ (hessian f) x u) u) = iteratedFDeriv ℝ 3 f x ![u, u, u] :=
    hessian_direction_pairing_eq_iteratedFDeriv
      (f := f) (x := x) (d := u) (w := u) (v := u) hcontAt
  have hu_quad_nonneg : 0 ≤ inner ℝ u (hessian f x u) :=
    hxPos.inner_nonneg_right u
  have hu_sq :
      ‖u‖[f; x] ^ (2 : ℕ) = inner ℝ u (hessian f x u) :=
    sq_hessianLocalNorm_eq_inner_of_nonneg hu_quad_nonneg
  have hupper_operator := hoperator hx u
  have hlower_operator := hoperator hx (-u)
  rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_iff]
    at hupper_operator hlower_operator
  obtain ⟨_, hupper_quad⟩ := hupper_operator
  obtain ⟨_, hlower_quad⟩ := hlower_operator
  have hupper_scalar :
      inner ℝ u ((fderiv ℝ (hessian f) x u) u) ≤
        2 * (Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ) := by
    have hrewrite :
        0 ≤
          (2 * (Mf : ℝ) * ‖u‖[f; x]) * inner ℝ u (hessian f x u) -
            inner ℝ u ((fderiv ℝ (hessian f) x u) u) := by
      simpa [real_inner_comm, inner_sub_left, inner_smul_left] using hupper_quad u
    calc
      inner ℝ u ((fderiv ℝ (hessian f) x u) u)
          ≤ (2 * (Mf : ℝ) * ‖u‖[f; x]) * inner ℝ u (hessian f x u) := by
              linarith
      _ = (2 * (Mf : ℝ) * ‖u‖[f; x]) * ‖u‖[f; x] ^ (2 : ℕ) := by
            rw [← hu_sq]
      _ = 2 * (Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ) := by
            ring_nf
  have hlower_scalar :
      -(2 * (Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ)) ≤
        inner ℝ u ((fderiv ℝ (hessian f) x u) u) := by
    have hrewrite :
        0 ≤
          (2 * (Mf : ℝ) * ‖-u‖[f; x]) * inner ℝ u (hessian f x u) +
            inner ℝ u ((fderiv ℝ (hessian f) x u) u) := by
      have hneg :
          fderiv ℝ (hessian f) x (-u) = -fderiv ℝ (hessian f) x u := by
        simpa using (fderiv ℝ (hessian f) x).map_neg u
      simpa [hneg, hessianLocalNorm_neg, real_inner_comm, inner_add_left, inner_smul_left,
        sub_eq_add_neg]
        using hlower_quad u
    have hrewrite_cube :
        (2 * (Mf : ℝ) * ‖-u‖[f; x]) * inner ℝ u (hessian f x u) =
          2 * (Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ) := by
      rw [hessianLocalNorm_neg, ← hu_sq]
      ring_nf
    linarith
  have habs :
      |inner ℝ u ((fderiv ℝ (hessian f) x u) u)| ≤
        2 * (Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ) := by
    exact abs_le.mpr ⟨hlower_scalar, hupper_scalar⟩
  have hconst : (fun _ : Fin 3 ↦ u) = ![u, u, u] := by
    ext i
    fin_cases i <;> rfl
  -- Rewrite the scalar Hessian-direction pairing back to the textbook third directional derivative.
  rw [thirdDirectionalDerivative_eq_iteratedFDeriv hcontAt, hconst]
  simpa [hpair] using habs

end IsSelfConcordantOnWith

/-- Corollary 5 1 1: for a thrice continuously differentiable convex function on an open convex
domain, the quantitative self-concordance owner `IsSelfConcordantOnWith dom Mf f` is equivalent
to the Loewner-order bound `D³f(x)[u] ≤ 2 M_f ‖u‖_{∇² f(x)} ∇² f(x)` on the directional
derivative of the Hessian. -/
theorem selfConcordant_iff_thirdDerivative_operator_le
    (h_open : IsOpen dom) (h_contDiff : ContDiffOn ℝ 3 f dom) (h_convexOn : ConvexOn ℝ dom f) :
    IsSelfConcordantOnWith dom Mf f ↔
      ∀ ⦃x : E⦄ (_hx : x ∈ dom) (u : E),
        fderiv ℝ (hessian f) x u ≤
          (2 * (Mf : ℝ) * ‖u‖[f; x]) • hessian f x := by
  constructor
  · intro hself x hx u
    exact hself.thirdDerivative_operator_le hx u
  · intro hoperator
    exact
      IsSelfConcordantOnWith.of_thirdDerivative_operator_le
        h_open h_contDiff h_convexOn hoperator

end
