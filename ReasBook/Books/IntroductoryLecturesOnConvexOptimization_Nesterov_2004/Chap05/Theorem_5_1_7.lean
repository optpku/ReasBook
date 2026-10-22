/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Lemma_5_1_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient HessianLocalNorm DikinEllipsoidNotation

noncomputable section

universe u

/-
Theorem 5.1.7 lies in the Chapter 5 self-concordance / Hessian-comparison domain.

Sampled owner-style declarations in this domain:
* `hessian` from `Chap01/Definition_1_4_16`, the canonical second-order owner replacing the raw
  `fderiv ℝ (∇ f)` surface;
* `thirdDirectionalDerivative` from `Chap05/Definition_5_0_10`, the source-facing Chapter 5 owner
  for the cubic derivative `D³f(x)[u,u,u]`;
* `hessianLocalNorm` and the notation `‖u‖[f; x]` from `Definition_5_1_1`, the chapter owner for
  the Hessian local norm;
* `openDikinEllipsoid` together with the notation `W⁰[f; x](r)` and
  `mem_openDikinEllipsoid_iff` from `Definition_5_0_13`, the owner and bridge for the
  Dikin-radius hypothesis `y ∈ W⁰[f; x](1 / M_f)`;
* `selfConcordant_diagonal_bound_iff_trilinear_bound` from `Lemma_5_1_2`, the canonical bridge
  from the Chapter 5 cubic owner surface to the full trilinear third-derivative estimate;
* `selfConcordant_iff_thirdDerivative_operator_le` from `Corollary_5_1_1`, the operator-level
  bridge from the same cubic owner surface to a Hessian differential inequality;
* `IsSelfConcordantOnWith.hessian_loewner_bounds_of_mem_openDikinEllipsoid` from
  `Proposition_5_0_15`, the stronger operator-level comparison theorem under the bundled owner
  `IsSelfConcordantOnWith dom Mf f`.

Source/core/bridge triage:
* source-facing: the segment-local Hessian operator comparison at `x` and `y`;
* core/canonical: `hessian f z`, `‖u‖[f; z]`, and `W⁰[f; x](r)`;
* bridge/view: `mem_openDikinEllipsoid_iff`, the scalarized quadratic-form inequalities obtained
  by testing the operator bounds on a direction `h`, and the stronger bundled-owner Loewner
  comparison from `Proposition_5_0_15`.

Primitive data:
* an open set `dom` containing the segment from `x` to `y`;
* `C³` regularity of `f` on `dom`;
* pointwise positivity of the Hessian along the segment from `x` to `y`;
* the Chapter 5 diagonal cubic bound on `thirdDirectionalDerivative f z u` along that segment;
* the Dikin-radius membership of `y`.

Derived API:
* the lower and upper Loewner-order comparison of the endpoint Hessians;
* the quadratic-form inequalities obtained from that operator comparison by evaluating on a
  direction `h`.

This theorem remains source-facing because the sampled bundled owner
`IsSelfConcordantOnWith dom Mf f` from `Definition_5_1_1` would strengthen the assumptions to a
global convex-domain self-concordance hypothesis. The refinement therefore keeps the original
segment-local semantics but moves the main public surface from the quadratic-form bridge to the
canonical Hessian owner already used by `hessianLocalNorm`, `openDikinEllipsoid`, and the nearby
Loewner-order API. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Helper for Theorem 5.1.7: the open-Dikin hypothesis already forces the exact local radius
below the reciprocal constant. -/
private lemma exact_local_radius_lt_inv_constant
    {Mf : NNReal} {f : E → ℝ} {x y : E}
    (hy : y ∈ W⁰[f; x](1 / (Mf : ℝ))) :
    ‖y - x‖[f; x] < 1 / (Mf : ℝ) := by
  -- Unpack the open-Dikin condition to recover the exact-radius inequality.
  simpa using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hy

/-- Helper for Theorem 5.1.7: the exact Dikin factor is positive under the open-Dikin
hypothesis. -/
private lemma exact_local_radius_factor_pos
    {Mf : NNReal} {f : E → ℝ} {x y : E}
    (hy : y ∈ W⁰[f; x](1 / (Mf : ℝ))) :
    0 < 1 - (Mf : ℝ) * ‖y - x‖[f; x] := by
  -- First isolate the exact-radius estimate forced by the Dikin-step hypothesis.
  have hρ_lt_inv : ‖y - x‖[f; x] < 1 / (Mf : ℝ) :=
    exact_local_radius_lt_inv_constant (f := f) (Mf := Mf) hy
  have hρ_nonneg : 0 ≤ ‖y - x‖[f; x] := hessianLocalNorm_nonneg f x (y - x)
  have hMf_nonneg : 0 ≤ (Mf : ℝ) := Mf.2
  have hMf_pos : 0 < (Mf : ℝ) := by
    -- If `Mf = 0`, the reciprocal-radius inequality would force a negative local norm.
    by_contra hMf_nonpos
    have hMf_eq_zero : (Mf : ℝ) = 0 := le_antisymm (le_of_not_gt hMf_nonpos) hMf_nonneg
    have hρ_lt_zero : ‖y - x‖[f; x] < 0 := by
      simpa [hMf_eq_zero] using hρ_lt_inv
    exact not_lt_of_ge hρ_nonneg hρ_lt_zero
  have hmul_lt_one : (Mf : ℝ) * ‖y - x‖[f; x] < 1 := by
    -- Multiply the exact-radius estimate by the positive constant `Mf`.
    have hmul : ‖y - x‖[f; x] * (Mf : ℝ) < 1 := by
      exact (lt_div_iff₀ hMf_pos).1 hρ_lt_inv
    simpa [mul_comm] using hmul
  linarith

/-- Helper for Theorem 5.1.7: once the endpoint scalar quadratic-form bounds are available in
every direction, the corresponding Loewner-order inequalities follow. -/
private lemma loewner_bounds_of_scalarized_hessian_bounds
    {f : E → ℝ} {x y : E} {coeff : ℝ}
    (hxPos : (hessian f x).IsPositive) (hyPos : (hessian f y).IsPositive)
    (hlower :
      ∀ v : E, coeff * inner ℝ v (hessian f x v) ≤ inner ℝ v (hessian f y v))
    (hupper :
      ∀ v : E, inner ℝ v (hessian f y v) ≤ coeff⁻¹ * inner ℝ v (hessian f x v)) :
    coeff • hessian f x ≤ hessian f y ∧
      hessian f y ≤ coeff⁻¹ • hessian f x := by
  constructor
  · -- Rewrite the lower Loewner claim as positivity of `∇²f(y) - coeff • ∇²f(x)`.
    rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_iff]
    constructor
    · intro u v
      have hySymm : inner ℝ (hessian f y u) v = inner ℝ u (hessian f y v) := by
        simpa using hyPos.isSymmetric u v
      have hxSymm : inner ℝ (hessian f x u) v = inner ℝ u (hessian f x v) := by
        simpa using hxPos.isSymmetric u v
      calc
        inner ℝ ((hessian f y - coeff • hessian f x) u) v =
            inner ℝ (hessian f y u) v - coeff * inner ℝ (hessian f x u) v := by
              simp [inner_sub_left, inner_smul_left]
        _ =
            inner ℝ u (hessian f y v) - coeff * inner ℝ u (hessian f x v) := by
              rw [hySymm, hxSymm]
        _ = inner ℝ u ((hessian f y - coeff • hessian f x) v) := by
              simp [inner_sub_right, inner_smul_right]
    · intro u
      have hySymm : inner ℝ (hessian f y u) u = inner ℝ u (hessian f y u) := by
        simpa using hyPos.isSymmetric u u
      have hxSymm : inner ℝ (hessian f x u) u = inner ℝ u (hessian f x u) := by
        simpa using hxPos.isSymmetric u u
      have hrewrite :
          inner ℝ ((hessian f y - coeff • hessian f x) u) u =
            inner ℝ u (hessian f y u) - coeff * inner ℝ u (hessian f x u) := by
        calc
          inner ℝ ((hessian f y - coeff • hessian f x) u) u
              = inner ℝ (hessian f y u) u - coeff * inner ℝ (hessian f x u) u := by
                  simp [inner_sub_left, inner_smul_left]
          _ = inner ℝ u (hessian f y u) - coeff * inner ℝ u (hessian f x u) := by
                  rw [hySymm, hxSymm]
      rw [hrewrite]
      linarith [hlower u]
  · -- Rewrite the upper Loewner claim as positivity of `coeff⁻¹ • ∇²f(x) - ∇²f(y)`.
    rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_iff]
    constructor
    · intro u v
      have hxSymm : inner ℝ (hessian f x u) v = inner ℝ u (hessian f x v) := by
        simpa using hxPos.isSymmetric u v
      have hySymm : inner ℝ (hessian f y u) v = inner ℝ u (hessian f y v) := by
        simpa using hyPos.isSymmetric u v
      calc
        inner ℝ ((coeff⁻¹ • hessian f x - hessian f y) u) v =
            coeff⁻¹ * inner ℝ (hessian f x u) v - inner ℝ (hessian f y u) v := by
              simp [inner_sub_left, inner_smul_left]
        _ =
            coeff⁻¹ * inner ℝ u (hessian f x v) - inner ℝ u (hessian f y v) := by
              rw [hxSymm, hySymm]
        _ = inner ℝ u ((coeff⁻¹ • hessian f x - hessian f y) v) := by
              simp [inner_sub_right, inner_smul_right]
    · intro u
      have hxSymm : inner ℝ (hessian f x u) u = inner ℝ u (hessian f x u) := by
        simpa using hxPos.isSymmetric u u
      have hySymm : inner ℝ (hessian f y u) u = inner ℝ u (hessian f y u) := by
        simpa using hyPos.isSymmetric u u
      have hrewrite :
          inner ℝ ((coeff⁻¹ • hessian f x - hessian f y) u) u =
            coeff⁻¹ * inner ℝ u (hessian f x u) - inner ℝ u (hessian f y u) := by
        calc
          inner ℝ ((coeff⁻¹ • hessian f x - hessian f y) u) u
              = coeff⁻¹ * inner ℝ (hessian f x u) u - inner ℝ (hessian f y u) u := by
                  simp [inner_sub_left, inner_smul_left]
          _ = coeff⁻¹ * inner ℝ u (hessian f x u) - inner ℝ u (hessian f y u) := by
                  rw [hxSymm, hySymm]
      rw [hrewrite]
      linarith [hupper u]

/-- Helper for Theorem 5.1.7: every affine parameter `t ∈ [0,1]` produces the corresponding
segment point `x + t • (y - x)` inside `segment ℝ x y`. -/
private lemma segment_point_mem_segment
    {x y : E} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    x + t • (y - x) ∈ segment ℝ x y := by
  -- Rewrite the affine segment point into the canonical convex-combination form.
  rw [segment_eq_image_lineMap]
  refine ⟨t, ht, ?_⟩
  simp [AffineMap.lineMap_apply_module', add_comm]

/-- Helper for Theorem 5.1.7: along the segment, the diagonal third-derivative quotient in the
displacement direction is bounded by `Mf`. -/
private lemma segment_diagonal_slice_quotient_le
    {Mf : NNReal} {f : E → ℝ} {x y : E}
    (hthird : ∀ ⦃z : E⦄ (_hz : z ∈ segment ℝ x y) (u : E),
      |thirdDirectionalDerivative f z u| ≤
        2 * (Mf : ℝ) * ‖u‖[f; z] ^ (3 : ℕ))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |thirdDirectionalDerivative f (x + t • (y - x)) (y - x)| /
        (2 * ‖y - x‖[f; x + t • (y - x)] ^ (3 : ℕ)) ≤
      (Mf : ℝ) := by
  let z : E := x + t • (y - x)
  have hz_segment : z ∈ segment ℝ x y := by
    simpa [z] using segment_point_mem_segment (x := x) (y := y) ht
  have hbound :
      |thirdDirectionalDerivative f z (y - x)| ≤
        2 * (Mf : ℝ) * ‖y - x‖[f; z] ^ (3 : ℕ) :=
    hthird hz_segment (y - x)
  by_cases hnorm : ‖y - x‖[f; z] = 0
  · -- If the local norm vanishes, the diagonal cubic bound already forces the numerator to vanish.
    have hnum_nonpos : |thirdDirectionalDerivative f z (y - x)| ≤ 0 := by
      simpa [hnorm] using hbound
    have hnum_eq_zero : |thirdDirectionalDerivative f z (y - x)| = 0 :=
      le_antisymm hnum_nonpos (abs_nonneg _)
    simp [z, hnorm, hnum_eq_zero]
  · -- Otherwise divide the diagonal cubic estimate by the positive denominator.
    have hnorm_pos : 0 < ‖y - x‖[f; z] := by
      exact lt_of_le_of_ne (hessianLocalNorm_nonneg f z (y - x)) (Ne.symm hnorm)
    have hden_pos : 0 < 2 * ‖y - x‖[f; z] ^ (3 : ℕ) := by
      positivity
    refine (div_le_iff₀ hden_pos).2 ?_
    simpa [z, mul_assoc, mul_left_comm, mul_comm] using hbound

/-- Helper for Theorem 5.1.7: the affine segment parameterization `t ↦ x + t • d` has derivative
`d`. -/
private lemma affine_segment_hasDerivAt
    {x d : E} (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ x + s • d) d t := by
  -- Differentiate scalar multiplication and then translate by the base point.
  simpa [one_smul] using ((hasDerivAt_id t).smul_const d).const_add x

/-- Helper for Theorem 5.1.7: a pointwise `C³` hypothesis upgrades the Hessian map to a genuinely
Fréchet-differentiable operator-valued map. -/
private lemma hessian_hasFDerivAt_of_contDiffAt
    {f : E → ℝ} {z : E} (hcontAt : ContDiffAt ℝ 3 f z) :
    HasFDerivAt (hessian f) (fderiv ℝ (hessian f) z) z := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfderiv_C2 : ContDiffAt ℝ 2 (fderiv ℝ f) z := by
    -- First differentiate `f` once and retain two more derivatives.
    exact hcontAt.fderiv_right (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)
  have hgrad_C2 : ContDiffAt ℝ 2 (∇ f) z := by
    -- Rewrite the gradient through the Riesz map before differentiating again.
    simpa [gradient, D] using D.contDiff.contDiffAt.comp z hfderiv_C2
  have hhessian_C1 : ContDiffAt ℝ 1 (hessian f) z := by
    -- One more derivative of the gradient is exactly the Hessian owner.
    simpa [hessian] using
      hgrad_C2.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  -- Convert the `C¹` regularity of the Hessian map into the required Fréchet derivative.
  exact (hhessian_C1.hasStrictFDerivAt one_ne_zero).hasFDerivAt

/-- Helper for Theorem 5.1.7: the scalarized Hessian quadratic form
`t ↦ inner ℝ v (hessian f (x + t • (y - x)) v)` differentiates to the mixed Hessian-direction
pairing. -/
private lemma segment_scalarized_hessian_hasDerivAt
    {f : E → ℝ} {x y v : E}
    {z : ℝ → E} (hz : z = fun t ↦ x + t • (y - x))
    {t : ℝ}
    (hcontAt : ContDiffAt ℝ 3 f (z t)) :
    HasDerivAt (fun s : ℝ ↦ inner ℝ v (hessian f (z s) v))
      (inner ℝ v ((fderiv ℝ (hessian f) (z t) (y - x)) v)) t := by
  have hzLine : HasDerivAt z (y - x) t := by
    -- Specialize the affine-line derivative to the segment parameterization.
    subst hz
    simpa using affine_segment_hasDerivAt (x := x) (d := y - x) t
  have hhessianDeriv :
      HasFDerivAt (hessian f) (fderiv ℝ (hessian f) (z t)) (z t) :=
    hessian_hasFDerivAt_of_contDiffAt hcontAt
  have happly :
      HasDerivAt (fun s : ℝ ↦ hessian f (z s) v)
        ((fderiv ℝ (hessian f) (z t) (y - x)) v) t := by
    -- Differentiate the Hessian map along the segment and then evaluate it on `v`.
    have happlyF :
        HasFDerivAt (fun w : E ↦ hessian f w v)
          ((ContinuousLinearMap.apply ℝ E v).comp (fderiv ℝ (hessian f) (z t))) (z t) := by
      exact (ContinuousLinearMap.apply ℝ E v).hasFDerivAt.comp (z t) hhessianDeriv
    simpa using happlyF.comp_hasDerivAt t hzLine
  -- Postcompose with the linear functional `w ↦ inner ℝ v w`.
  have hinnerF :
      HasFDerivAt (fun w : E ↦ inner ℝ v w) ((innerSL ℝ) v) (hessian f (z t) v) := by
    simpa using ((innerSL ℝ) v).hasFDerivAt
  simpa using hinnerF.comp_hasDerivAt t happly

/-- Helper for Theorem 5.1.7: when the Hessian quadratic form is nonnegative, the square of the
local norm rewrites back to that quadratic form. -/
private lemma sq_hessianLocalNorm_eq_inner_of_nonneg
    {f : E → ℝ} {z u : E} (hquad : 0 ≤ inner ℝ u (hessian f z u)) :
    ‖u‖[f; z] ^ (2 : ℕ) = inner ℝ u (hessian f z u) := by
  -- Expand the local norm and use `sqrt(x)^2 = x` on the nonnegative Hessian quadratic form.
  simpa [hessianLocalNorm_def] using Real.sq_sqrt hquad

/-- Helper for Theorem 5.1.7: under `C³` regularity, the third iterated derivative is symmetric
in its first two arguments. -/
private lemma iteratedFDeriv_three_swap12_at
    {f : E → ℝ} {z u₁ u₂ u₃ : E} (hcontAt : ContDiffAt ℝ 3 f z) :
    iteratedFDeriv ℝ 3 f z ![u₁, u₂, u₃] =
      iteratedFDeriv ℝ 3 f z ![u₂, u₁, u₃] := by
  let g : E → E →L[ℝ] ℝ := fderiv ℝ f
  -- View the third derivative as the second derivative of `fderiv ℝ f`, then apply symmetry of
  -- second derivatives for the intermediate operator-valued map.
  have hgcont : ContDiffAt ℝ 2 g z := by
    simpa [g] using hcontAt.fderiv_right (m := 2) (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)
  have hgsymm : IsSymmSndFDerivAt ℝ g z := hgcont.isSymmSndFDerivAt (by norm_num)
  have hswap :
      (fderiv ℝ (fderiv ℝ g) z u₁ u₂) u₃ =
        (fderiv ℝ (fderiv ℝ g) z u₂ u₁) u₃ := by
    exact congrArg (fun L : E →L[ℝ] ℝ => L u₃) (hgsymm.eq u₁ u₂)
  simpa [g, iteratedFDeriv_succ_apply_right, iteratedFDeriv_two_apply] using hswap

/-- Helper for Theorem 5.1.7: under `C³` regularity, the third iterated derivative is symmetric
in its last two arguments. -/
private lemma iteratedFDeriv_three_swap23_at
    {f : E → ℝ} {z u₁ u₂ u₃ : E} (hcontAt : ContDiffAt ℝ 3 f z) :
    iteratedFDeriv ℝ 3 f z ![u₁, u₂, u₃] =
      iteratedFDeriv ℝ 3 f z ![u₁, u₃, u₂] := by
  obtain ⟨u, hu, hcontOn⟩ :=
    hcontAt.contDiffOn (m := 3) (by simp) (by intro h; simp at h)
  obtain ⟨s, hs_sub, hs_open, hzs⟩ := mem_nhds_iff.mp hu
  have hs_contOn : ContDiffOn ℝ 3 f s := hcontOn.mono hs_sub
  let c : E → ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ := iteratedFDeriv ℝ 2 f
  -- The second derivative is symmetric at nearby points, so the antisymmetric part vanishes on a
  -- neighborhood of `z`, and therefore so does its derivative at `z`.
  have hvanish :
      (fun y ↦ c y ![u₂, u₃] - c y ![u₃, u₂]) =ᶠ[nhds z] fun _ ↦ 0 := by
    filter_upwards [hs_open.mem_nhds hzs] with y hy
    have hycont : ContDiffAt ℝ 2 f y := by
      exact (hs_contOn.of_le (by norm_num)).contDiffAt (hs_open.mem_nhds hy)
    have hysymm : IsSymmSndFDerivAt ℝ f y := hycont.isSymmSndFDerivAt (by norm_num)
    have hyEq : iteratedFDeriv ℝ 2 f y ![u₂, u₃] = iteratedFDeriv ℝ 2 f y ![u₃, u₂] :=
      hysymm.iteratedFDeriv_cons
    simp [c, hyEq]
  have hc_diff : DifferentiableAt ℝ c z := by
    have hc_contDiff : ContDiffAt ℝ 1 c z := by
      exact hcontAt.iteratedFDeriv_right (m := 1) (i := 2)
        (by norm_num : (1 : WithTop ℕ∞) + 2 ≤ 3)
    exact hc_contDiff.differentiableAt one_ne_zero
  have hderivZero :
      fderiv ℝ (fun y ↦ c y ![u₂, u₃] - c y ![u₃, u₂]) z = 0 := by
    -- Replace the function by the eventually equal constant zero function.
    rw [hvanish.fderiv_eq]
    simp
  have hderivEval :
      ((fderiv ℝ c z).flipMultilinear ![u₂, u₃]) u₁ =
        ((fderiv ℝ c z).flipMultilinear ![u₃, u₂]) u₁ := by
    have hzeroApplied :
        (fderiv ℝ (fun y ↦ c y ![u₂, u₃] - c y ![u₃, u₂]) z) u₁ = 0 := by
      simpa using congrArg (fun L : E →L[ℝ] ℝ => L u₁) hderivZero
    have h23diff : DifferentiableAt ℝ (fun y ↦ c y ![u₂, u₃]) z :=
      hc_diff.continuousMultilinear_apply_const ![u₂, u₃]
    have h32diff : DifferentiableAt ℝ (fun y ↦ c y ![u₃, u₂]) z :=
      hc_diff.continuousMultilinear_apply_const ![u₃, u₂]
    have hzeroApplied' :
        (((fderiv ℝ c z).flipMultilinear ![u₂, u₃] -
            (fderiv ℝ c z).flipMultilinear ![u₃, u₂]) u₁) = 0 := by
      rw [← fderiv_continuousMultilinear_apply_const hc_diff,
        ← fderiv_continuousMultilinear_apply_const hc_diff,
        ← fderiv_sub h23diff h32diff]
      exact hzeroApplied
    exact sub_eq_zero.mp hzeroApplied'
  simpa [c, iteratedFDeriv_succ_apply_left] using hderivEval

/-- Helper for Theorem 5.1.7: the Hessian bilinear form at `z`, written in the operator-first
convention used by the positive-operator API. -/
private def hessianBilinAt (f : E → ℝ) (z : E) : LinearMap.BilinForm ℝ E :=
  ((innerSL ℝ).comp (hessian f z)).toBilinForm

/-- Helper for Theorem 5.1.7: evaluating `hessianBilinAt` pairs the Hessian image of the first
argument with the second argument. -/
private lemma hessianBilinAt_apply (f : E → ℝ) (z u v : E) :
    hessianBilinAt f z u v = inner ℝ (hessian f z u) v :=
  rfl

/-- Helper for Theorem 5.1.7: a zero Hessian local norm is equivalent to vanishing under the
Hessian operator itself. -/
private lemma hessian_localRadical_iff_hessian_eq_zero
    {f : E → ℝ} {z u : E} (hzPos : (hessian f z).IsPositive) :
    ‖u‖[f; z] = 0 ↔ hessian f z u = 0 := by
  let B : LinearMap.BilinForm ℝ E := hessianBilinAt f z
  have hB_nonneg : ∀ a : E, 0 ≤ (B a) a := by
    intro a
    simpa [B, hessianBilinAt_apply, real_inner_comm] using hzPos.inner_nonneg_right a
  have hB_symm : LinearMap.IsSymm B := by
    rw [← LinearMap.BilinForm.isSymm_iff]
    rw [LinearMap.BilinForm.isSymm_def]
    intro a b
    change inner ℝ (hessian f z a) b = inner ℝ (hessian f z b) a
    simpa [real_inner_comm] using hzPos.isSymmetric a b
  constructor
  · intro hu
    have hu_quad_nonneg : 0 ≤ inner ℝ u (hessian f z u) := hzPos.inner_nonneg_right u
    have hu_sq :
        ‖u‖[f; z] ^ (2 : ℕ) = inner ℝ u (hessian f z u) :=
      sq_hessianLocalNorm_eq_inner_of_nonneg (f := f) (z := z) (u := u) hu_quad_nonneg
    have hu_quad : (B u) u = 0 := by
      have hu_sq_zero : ‖u‖[f; z] ^ (2 : ℕ) = 0 := by simp [hu]
      have hu_inner_zero : inner ℝ u (hessian f z u) = 0 := by
        nlinarith [hu_sq, hu_sq_zero]
      simpa [B, hessianBilinAt_apply, real_inner_comm] using hu_inner_zero
    have hu_ker : u ∈ LinearMap.ker B :=
      (LinearMap.BilinForm.apply_apply_same_eq_zero_iff B hB_nonneg hB_symm).1 hu_quad
    have hu_ker' : B u = 0 := by simpa [LinearMap.mem_ker] using hu_ker
    have hself_zero : inner ℝ (hessian f z u) (hessian f z u) = 0 := by
      simpa [B, hessianBilinAt_apply] using
        congrArg (fun L : E →ₗ[ℝ] ℝ => L (hessian f z u)) hu_ker'
    exact inner_self_eq_zero.mp hself_zero
  · intro hu
    have hu_sq :
        ‖u‖[f; z] ^ (2 : ℕ) = 0 := by
      rw [sq_hessianLocalNorm_eq_inner_of_nonneg (f := f) (z := z) (u := u)
        (hzPos.inner_nonneg_right u)]
      simp [hu]
    have hu_nonneg : 0 ≤ ‖u‖[f; z] := hessianLocalNorm_nonneg f z u
    nlinarith

/-- Helper for Theorem 5.1.7: a zero Hessian local norm is equivalent to annihilating every
Hessian bilinear pairing at the base point. -/
private lemma hessian_localRadical_iff_annihilates_hessian
    {f : E → ℝ} {z u : E} (hzPos : (hessian f z).IsPositive) :
    ‖u‖[f; z] = 0 ↔ ∀ w : E, inner ℝ u (hessian f z w) = 0 := by
  constructor
  · intro hu w
    have hHu : hessian f z u = 0 :=
      (hessian_localRadical_iff_hessian_eq_zero (f := f) (z := z) (u := u) hzPos).1 hu
    have hsym : inner ℝ (hessian f z u) w = inner ℝ u (hessian f z w) := by
      simpa [real_inner_comm] using hzPos.isSymmetric u w
    simpa [hHu] using hsym.symm
  · intro hu
    have huu : inner ℝ u (hessian f z u) = 0 := hu u
    have hu_sq :
        ‖u‖[f; z] ^ (2 : ℕ) = 0 := by
      rw [sq_hessianLocalNorm_eq_inner_of_nonneg (f := f) (z := z) (u := u)
        (hzPos.inner_nonneg_right u)]
      simp [huu]
    have hu_nonneg : 0 ≤ ‖u‖[f; z] := hessianLocalNorm_nonneg f z u
    nlinarith

/-- Helper for Theorem 5.1.7: adding a Hessian-radical direction only rescales the local norm by
the scalar on the transverse direction. -/
private lemma hessianLocalNorm_add_smul_of_localRadical
    {f : E → ℝ} {z u w : E} (hzPos : (hessian f z).IsPositive)
    (hu : ∀ a : E, inner ℝ u (hessian f z a) = 0) (t : ℝ) :
    ‖u + t • w‖[f; z] = |t| * ‖w‖[f; z] := by
  have hHu : hessian f z u = 0 :=
    (hessian_localRadical_iff_hessian_eq_zero (f := f) (z := z) (u := u) hzPos).1
      ((hessian_localRadical_iff_annihilates_hessian (f := f) (z := z) (u := u) hzPos).2 hu)
  have hquad :
      inner ℝ (u + t • w) (hessian f z (u + t • w)) =
        t ^ (2 : ℕ) * inner ℝ w (hessian f z w) := by
    calc
      inner ℝ (u + t • w) (hessian f z (u + t • w))
          = inner ℝ (u + t • w) (t • hessian f z w) := by simp [hHu, map_add]
      _ = inner ℝ u (t • hessian f z w) + inner ℝ (t • w) (t • hessian f z w) := by
            rw [inner_add_left]
      _ = t * inner ℝ u (hessian f z w) + t * (t * inner ℝ w (hessian f z w)) := by
            simp [inner_smul_left, inner_smul_right]
      _ = t ^ (2 : ℕ) * inner ℝ w (hessian f z w) := by
            simp [hu w, pow_two, mul_assoc]
  have hw_quad_nonneg : 0 ≤ inner ℝ w (hessian f z w) := hzPos.inner_nonneg_right w
  -- Expand both local norms and use the exact quadratic identity coming from the radical
  -- annihilation of the mixed terms.
  rw [hessianLocalNorm_def, hquad, hessianLocalNorm_def]
  rw [Real.sqrt_mul (sq_nonneg t)]
  simp [Real.sqrt_sq_eq_abs]

/-- Helper for Theorem 5.1.7: a trilinear map is additive in its first slot. -/
private lemma trilinearApplyAddFirst
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (a₁ a₂ b c : E) :
    T ![a₁ + a₂, b, c] = T ![a₁, b, c] + T ![a₂, b, c] := by
  -- Rewrite the first-slot addition through the `Fin 3` `cons` API.
  simpa using T.cons_add ![b, c] a₁ a₂

/-- Helper for Theorem 5.1.7: a trilinear map is additive in its second slot. -/
private lemma trilinearApplyAddSecond
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (a b₁ b₂ c : E) :
    T ![a, b₁ + b₂, c] = T ![a, b₁, c] + T ![a, b₂, c] := by
  -- Curry once so that the second slot becomes the first slot of a bilinear map.
  simpa using (T.curryLeft a).cons_add ![c] b₁ b₂

/-- Helper for Theorem 5.1.7: a trilinear map is additive in its third slot. -/
private lemma trilinearApplyAddThird
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (a b c₁ c₂ : E) :
    T ![a, b, c₁ + c₂] = T ![a, b, c₁] + T ![a, b, c₂] := by
  -- Curry on the right so the last slot is an ordinary linear map.
  simpa using (T.curryRight ![a, b]).map_add c₁ c₂

/-- Helper for Theorem 5.1.7: a trilinear map is homogeneous in its first slot. -/
private lemma trilinearApplySmulFirst
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (t : ℝ) (a b c : E) :
    T ![t • a, b, c] = t * T ![a, b, c] := by
  -- Rewrite the first-slot scaling through the `Fin 3` `cons` API.
  simpa [smul_eq_mul] using T.cons_smul ![b, c] t a

/-- Helper for Theorem 5.1.7: a trilinear map is homogeneous in its second slot. -/
private lemma trilinearApplySmulSecond
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (t : ℝ) (a b c : E) :
    T ![a, t • b, c] = t * T ![a, b, c] := by
  -- Curry once so the second slot becomes the first slot of a bilinear map.
  simpa [smul_eq_mul] using (T.curryLeft a).cons_smul ![c] t b

/-- Helper for Theorem 5.1.7: a trilinear map is homogeneous in its third slot. -/
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

/-- Helper for Theorem 5.1.7: the centered second difference of a symmetric trilinear form
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

/-- Helper for Theorem 5.1.7: the third iterated derivative vanishes in the `(u,w,w)` slot
pattern when `u` lies in the Hessian local radical. -/
private lemma iteratedFDeriv_vanishes_on_hessian_localRadical
    {Mf : NNReal} {f : E → ℝ} {z u w : E}
    (hcontAt : ContDiffAt ℝ 3 f z)
    (hzPos : (hessian f z).IsPositive)
    (hdiag_z : ∀ a : E,
      |thirdDirectionalDerivative f z a| ≤
        2 * (Mf : ℝ) * ‖a‖[f; z] ^ (3 : ℕ))
    (hu : ∀ a : E, inner ℝ u (hessian f z a) = 0) :
    iteratedFDeriv ℝ 3 f z ![u, w, w] = 0 := by
  let T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ := iteratedFDeriv ℝ 3 f z
  have huNorm : ‖u‖[f; z] = 0 :=
    (hessian_localRadical_iff_annihilates_hessian (f := f) (z := z) (u := u) hzPos).2 hu
  have huConst : (fun _ : Fin 3 ↦ u) = ![u, u, u] := by
    ext i
    fin_cases i <;> rfl
  have huuu : T ![u, u, u] = 0 := by
    have hdiag_u : |T ![u, u, u]| ≤ 0 := by
      -- The diagonal cubic bound collapses to zero because `u` has zero Hessian local norm.
      simpa [T, thirdDirectionalDerivative_eq_iteratedFDeriv hcontAt, huConst, huNorm] using
        hdiag_z u
    exact abs_eq_zero.mp (le_antisymm hdiag_u (abs_nonneg _))
  have hswap12 :
      ∀ a b c : E, T ![a, b, c] = T ![b, a, c] := by
    intro a b c
    simpa [T] using
      iteratedFDeriv_three_swap12_at
        (f := f) (z := z) (u₁ := a) (u₂ := b) (u₃ := c) hcontAt
  have hswap23 :
      ∀ a b c : E, T ![a, b, c] = T ![a, c, b] := by
    intro a b c
    simpa [T] using
      iteratedFDeriv_three_swap23_at
        (f := f) (z := z) (u₁ := a) (u₂ := b) (u₃ := c) hcontAt
  have hplusDiag (t : ℝ) :
      |T ![u + t • w, u + t • w, u + t • w]| ≤
        2 * (Mf : ℝ) * (|t| * ‖w‖[f; z]) ^ (3 : ℕ) := by
    have hconst : (fun _ : Fin 3 ↦ u + t • w) = ![u + t • w, u + t • w, u + t • w] := by
      ext i
      fin_cases i <;> rfl
    have hnorm :
        ‖u + t • w‖[f; z] = |t| * ‖w‖[f; z] :=
      hessianLocalNorm_add_smul_of_localRadical
        (f := f) (z := z) (u := u) (w := w) hzPos hu t
    -- Rewrite the source-facing diagonal bound on the translated direction back to
    -- `iteratedFDeriv`.
    simpa [T, thirdDirectionalDerivative_eq_iteratedFDeriv hcontAt, hconst, hnorm] using
      hdiag_z (u + t • w)
  have hminusDiag (t : ℝ) :
      |T ![u - t • w, u - t • w, u - t • w]| ≤
        2 * (Mf : ℝ) * (|t| * ‖w‖[f; z]) ^ (3 : ℕ) := by
    have hconst : (fun _ : Fin 3 ↦ u - t • w) = ![u - t • w, u - t • w, u - t • w] := by
      ext i
      fin_cases i <;> rfl
    have hnorm :
        ‖u - t • w‖[f; z] = |t| * ‖w‖[f; z] := by
      calc
        ‖u - t • w‖[f; z] = ‖u + (-t) • w‖[f; z] := by simp [sub_eq_add_neg]
        _ = |-t| * ‖w‖[f; z] :=
          hessianLocalNorm_add_smul_of_localRadical
            (f := f) (z := z) (u := u) (w := w) hzPos hu (-t)
        _ = |t| * ‖w‖[f; z] := by simp
    -- The same local-radical norm collapse applies to the reflected direction `u - t • w`.
    simpa [T, thirdDirectionalDerivative_eq_iteratedFDeriv hcontAt, hconst, hnorm] using
      hdiag_z (u - t • w)
  have hcoeffBound (t : ℝ) :
      |6 * t ^ (2 : ℕ) * T ![u, w, w]| ≤
        4 * (Mf : ℝ) * (|t| * ‖w‖[f; z]) ^ (3 : ℕ) := by
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
      _ ≤ 2 * (Mf : ℝ) * (|t| * ‖w‖[f; z]) ^ (3 : ℕ) +
            2 * (Mf : ℝ) * (|t| * ‖w‖[f; z]) ^ (3 : ℕ) := by
          gcongr
          · exact hplusDiag t
          · exact hminusDiag t
      _ = 4 * (Mf : ℝ) * (|t| * ‖w‖[f; z]) ^ (3 : ℕ) := by ring
  have hsmall (t : ℝ) (ht : 0 < t) :
      |T ![u, w, w]| ≤ ((2 * (Mf : ℝ) * ‖w‖[f; z] ^ (3 : ℕ)) / 3) * t := by
    have hcoeff := hcoeffBound t
    have hcoeff' :
        6 * t ^ (2 : ℕ) * |T ![u, w, w]| ≤
          4 * (Mf : ℝ) * t ^ (3 : ℕ) * ‖w‖[f; z] ^ (3 : ℕ) := by
      have hleft :
          |6 * t ^ (2 : ℕ) * T ![u, w, w]| =
            6 * t ^ (2 : ℕ) * |T ![u, w, w]| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (show 0 ≤ (6 : ℝ) by norm_num),
          abs_of_nonneg (pow_two_nonneg t)]
      have hright :
          4 * (Mf : ℝ) * (|t| * ‖w‖[f; z]) ^ (3 : ℕ) =
            4 * (Mf : ℝ) * t ^ (3 : ℕ) * ‖w‖[f; z] ^ (3 : ℕ) := by
        rw [abs_of_pos ht]
        ring
      rwa [hleft, hright] at hcoeff
    have ht_sq_pos : 0 < t ^ (2 : ℕ) := by positivity
    have hfactored :
        t ^ (2 : ℕ) * (6 * |T ![u, w, w]|) ≤
          t ^ (2 : ℕ) * (4 * (Mf : ℝ) * t * ‖w‖[f; z] ^ (3 : ℕ)) := by
      nlinarith [hcoeff']
    have hlinear :
        6 * |T ![u, w, w]| ≤ 4 * (Mf : ℝ) * t * ‖w‖[f; z] ^ (3 : ℕ) :=
      by nlinarith [hfactored, ht_sq_pos]
    nlinarith
  by_cases hzero : T ![u, w, w] = 0
  · simpa [T] using hzero
  have habs_pos : 0 < |T ![u, w, w]| := abs_pos.mpr hzero
  let K : ℝ := ((2 * (Mf : ℝ) * ‖w‖[f; z] ^ (3 : ℕ)) / 3)
  have hK_nonneg : 0 ≤ K := by
    have hMf_nonneg : 0 ≤ (Mf : ℝ) := by exact_mod_cast Mf.2
    have hw_nonneg : 0 ≤ ‖w‖[f; z] := hessianLocalNorm_nonneg f z w
    have hw_pow_nonneg : 0 ≤ ‖w‖[f; z] ^ (3 : ℕ) := pow_nonneg hw_nonneg _
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

/-- Helper for Theorem 5.1.7: if a Hessian-radical direction occupies the first slot, then the
entire symmetric third derivative vanishes. -/
private lemma iteratedFDeriv_firstSlot_zero_of_hessian_localRadical
    {Mf : NNReal} {f : E → ℝ} {z u v w : E}
    (hcontAt : ContDiffAt ℝ 3 f z)
    (hzPos : (hessian f z).IsPositive)
    (hdiag_z : ∀ a : E,
      |thirdDirectionalDerivative f z a| ≤
        2 * (Mf : ℝ) * ‖a‖[f; z] ^ (3 : ℕ))
    (hu : ∀ a : E, inner ℝ u (hessian f z a) = 0) :
    iteratedFDeriv ℝ 3 f z ![u, v, w] = 0 := by
  let T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ := iteratedFDeriv ℝ 3 f z
  have hvv : T ![u, v, v] = 0 := by
    simpa [T] using
      iteratedFDeriv_vanishes_on_hessian_localRadical
        (Mf := Mf) (f := f) (z := z) (u := u) (w := v) hcontAt hzPos hdiag_z hu
  have hww : T ![u, w, w] = 0 := by
    simpa [T] using
      iteratedFDeriv_vanishes_on_hessian_localRadical
        (Mf := Mf) (f := f) (z := z) (u := u) (w := w) hcontAt hzPos hdiag_z hu
  have hsumZero : T ![u, v + w, v + w] = 0 := by
    simpa [T] using
      iteratedFDeriv_vanishes_on_hessian_localRadical
        (Mf := Mf) (f := f) (z := z) (u := u) (w := v + w) hcontAt hzPos hdiag_z hu
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
        (f := f) (z := z) (u₁ := u) (u₂ := w) (u₃ := v) hcontAt)
  -- The `v + w` diagonal expansion leaves only the two equal cross terms, so they must vanish.
  rw [hsumExpand, hvv, hww, hswap23, zero_add, add_zero] at hsumZero
  nlinarith

/-- Helper for Theorem 5.1.7: if the repeated direction lies in the Hessian local radical, then
the `(d,v,v)` third-derivative slot pattern also vanishes after swapping the first two slots. -/
private lemma iteratedFDeriv_dvv_vanishes_on_hessian_localRadical
    {Mf : NNReal} {f : E → ℝ} {z d v : E}
    (hcontAt : ContDiffAt ℝ 3 f z)
    (hzPos : (hessian f z).IsPositive)
    (hdiag_z : ∀ a : E,
      |thirdDirectionalDerivative f z a| ≤
        2 * (Mf : ℝ) * ‖a‖[f; z] ^ (3 : ℕ))
    (hv : ∀ a : E, inner ℝ v (hessian f z a) = 0) :
    iteratedFDeriv ℝ 3 f z ![d, v, v] = 0 := by
  -- Swap the Hessian-radical direction into the first slot, apply the stronger vanishing helper,
  -- and swap back only at the API level.
  calc
    iteratedFDeriv ℝ 3 f z ![d, v, v]
        = iteratedFDeriv ℝ 3 f z ![v, d, v] := by
            simpa using
              (iteratedFDeriv_three_swap12_at
                (f := f) (z := z) (u₁ := d) (u₂ := v) (u₃ := v) hcontAt)
    _ = 0 := by
          exact
            iteratedFDeriv_firstSlot_zero_of_hessian_localRadical
              (Mf := Mf) (f := f) (z := z) (u := v) (v := d) (w := v)
              hcontAt hzPos hdiag_z hv

/-- Helper for Theorem 5.1.7: the Hessian pairing obeys the local-norm Cauchy-Schwarz
inequality after rewriting the positive quadratic form through `‖·‖[f; z]`. -/
private lemma hessianPairing_sq_le_localNorm
    {f : E → ℝ} {z d v : E} (hzPos : (hessian f z).IsPositive) :
    (inner ℝ d (hessian f z v)) ^ (2 : ℕ) ≤
      ‖d‖[f; z] ^ (2 : ℕ) * ‖v‖[f; z] ^ (2 : ℕ) := by
  let B : LinearMap.BilinForm ℝ E := hessianBilinAt f z
  have hB_nonneg : ∀ a : E, 0 ≤ B a a := by
    intro a
    simpa [B, hessianBilinAt_apply, real_inner_comm] using hzPos.inner_nonneg_right a
  have hB_symm : LinearMap.IsSymm B := by
    -- The Hessian bilinear form is symmetric because the Hessian operator is self-adjoint.
    rw [← LinearMap.BilinForm.isSymm_iff]
    rw [LinearMap.BilinForm.isSymm_def]
    intro a b
    simpa [B, hessianBilinAt_apply, real_inner_comm] using hzPos.isSymmetric a b
  have hsq :
      (B d v) ^ (2 : ℕ) ≤ (B d d) * (B v v) :=
    B.apply_sq_le_of_symm hB_nonneg hB_symm d v
  have hBdv :
      B d v = inner ℝ d (hessian f z v) := by
    simpa [B, hessianBilinAt_apply, real_inner_comm] using hzPos.isSymmetric d v
  have hd_sq :
      B d d = ‖d‖[f; z] ^ (2 : ℕ) := by
    rw [hessianBilinAt_apply, real_inner_comm]
    symm
    exact sq_hessianLocalNorm_eq_inner_of_nonneg (f := f) (z := z) (u := d)
      (hzPos.inner_nonneg_right d)
  have hv_sq :
      B v v = ‖v‖[f; z] ^ (2 : ℕ) := by
    rw [hessianBilinAt_apply, real_inner_comm]
    symm
    exact sq_hessianLocalNorm_eq_inner_of_nonneg (f := f) (z := z) (u := v)
      (hzPos.inner_nonneg_right v)
  -- Rewrite the bilinear-form Schwarz inequality back into the Hessian/local-norm spelling.
  have hsq' :
      (inner ℝ d (hessian f z v)) ^ (2 : ℕ) ≤ ‖d‖[f; z] ^ (2 : ℕ) * ‖v‖[f; z] ^ (2 : ℕ) := by
    rw [← hBdv]
    simpa [hd_sq, hv_sq] using hsq
  exact hsq'

/-- Helper for Theorem 5.1.7: the Hessian local norm scales by the absolute value of the scalar
once the pointwise Hessian is positive semidefinite. -/
private lemma hessianLocalNorm_smul_eq_abs_of_isPositive
    {f : E → ℝ} {z u : E} (hzPos : (hessian f z).IsPositive) (a : ℝ) :
    ‖a • u‖[f; z] = |a| * ‖u‖[f; z] := by
  have hquad : 0 ≤ inner ℝ u (hessian f z u) := hzPos.inner_nonneg_right u
  -- Expand the scaled quadratic form before taking square roots.
  calc
    ‖a • u‖[f; z] = Real.sqrt ((a * a) * inner ℝ u (hessian f z u)) := by
      rw [hessianLocalNorm_def]
      congr 1
      simp [inner_smul_left, inner_smul_right, mul_assoc]
    _ = Real.sqrt (inner ℝ u (hessian f z u)) * Real.sqrt (a * a) := by
      rw [mul_comm, Real.sqrt_mul hquad]
    _ = |a| * ‖u‖[f; z] := by
      rw [show a * a = a ^ (2 : ℕ) by ring, Real.sqrt_sq_eq_abs, hessianLocalNorm_def]
      ring

/-- Helper for Theorem 5.1.7: subtracting the Hessian-bilinear projection of `d` onto `v`
produces a local-orthogonal residual and the corresponding Pythagorean identity. -/
private lemma hessianProjectionSplit
    {f : E → ℝ} {z d v : E} (hzPos : (hessian f z).IsPositive)
    (hv : ‖v‖[f; z] ≠ 0) :
    let α : ℝ := inner ℝ d (hessian f z v) / ‖v‖[f; z] ^ (2 : ℕ)
    let w : E := d - α • v
    inner ℝ w (hessian f z v) = 0 ∧
      ‖d‖[f; z] ^ (2 : ℕ) = ‖w‖[f; z] ^ (2 : ℕ) + (α * ‖v‖[f; z]) ^ (2 : ℕ) := by
  let α : ℝ := inner ℝ d (hessian f z v) / ‖v‖[f; z] ^ (2 : ℕ)
  let w : E := d - α • v
  have hv_sq_nonneg : 0 ≤ inner ℝ v (hessian f z v) := hzPos.inner_nonneg_right v
  have hv_sq :
      ‖v‖[f; z] ^ (2 : ℕ) = inner ℝ v (hessian f z v) :=
    sq_hessianLocalNorm_eq_inner_of_nonneg (f := f) (z := z) (u := v) hv_sq_nonneg
  have hv_sq_ne : ‖v‖[f; z] ^ (2 : ℕ) ≠ 0 := by
    exact pow_ne_zero 2 hv
  have hα :
      α * ‖v‖[f; z] ^ (2 : ℕ) = inner ℝ d (hessian f z v) := by
    dsimp [α]
    field_simp [hv_sq_ne]
  have horth :
      inner ℝ w (hessian f z v) = 0 := by
    -- The projection coefficient `α` is chosen to cancel the mixed Hessian pairing with `v`.
    calc
      inner ℝ w (hessian f z v)
          = inner ℝ d (hessian f z v) - α * inner ℝ v (hessian f z v) := by
              simp [w, inner_sub_left, inner_smul_left]
      _ = inner ℝ d (hessian f z v) - α * ‖v‖[f; z] ^ (2 : ℕ) := by
            rw [hv_sq]
      _ = 0 := by nlinarith [hα]
  have horth' :
      inner ℝ v (hessian f z w) = 0 := by
    -- Symmetry of the positive Hessian operator moves the orthogonality to the other slot.
    have hsym : inner ℝ v (hessian f z w) = inner ℝ w (hessian f z v) := by
      simpa [real_inner_comm] using hzPos.isSymmetric w v
    simpa [horth] using hsym
  have hw_sq_nonneg : 0 ≤ inner ℝ w (hessian f z w) := hzPos.inner_nonneg_right w
  have hw_sq :
      ‖w‖[f; z] ^ (2 : ℕ) = inner ℝ w (hessian f z w) :=
    sq_hessianLocalNorm_eq_inner_of_nonneg (f := f) (z := z) (u := w) hw_sq_nonneg
  have hd_sq_nonneg : 0 ≤ inner ℝ d (hessian f z d) := hzPos.inner_nonneg_right d
  have hd_sq :
      ‖d‖[f; z] ^ (2 : ℕ) = inner ℝ d (hessian f z d) :=
    sq_hessianLocalNorm_eq_inner_of_nonneg (f := f) (z := z) (u := d) hd_sq_nonneg
  have hd_eq : d = w + α • v := by
    -- Rewrite `d` back as the residual plus its Hessian projection onto `v`.
    dsimp [w]
    abel_nf
  have hpyth_inner :
      inner ℝ d (hessian f z d) =
        inner ℝ w (hessian f z w) + (α * ‖v‖[f; z]) ^ (2 : ℕ) := by
    calc
      inner ℝ d (hessian f z d)
          = inner ℝ (w + α • v) (hessian f z (w + α • v)) := by rw [hd_eq]
      _ = inner ℝ w (hessian f z w) +
            α * inner ℝ w (hessian f z v) +
            α * inner ℝ v (hessian f z w) +
            α * (α * inner ℝ v (hessian f z v)) := by
              simp [map_add, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
              ring
      _ = inner ℝ w (hessian f z w) + α * (α * inner ℝ v (hessian f z v)) := by
            simp [horth, horth']
      _ = inner ℝ w (hessian f z w) + (α * ‖v‖[f; z]) ^ (2 : ℕ) := by
            rw [← hv_sq]
            ring
  constructor
  · exact horth
  · rw [hd_sq, hw_sq]
    exact hpyth_inner

/-- Helper for Theorem 5.1.7: a local-orthonormal pair for the Hessian quadratic form models
the local norm by the Euclidean norm of the coefficients. -/
private lemma hessianLocalNorm_sq_of_localOrthonormalPair
    {f : E → ℝ} {z e₁ e₂ : E} (hzPos : (hessian f z).IsPositive)
    (he₁ : ‖e₁‖[f; z] = 1) (he₂ : ‖e₂‖[f; z] = 1)
    (horth : inner ℝ e₁ (hessian f z e₂) = 0) :
    ∀ a b : ℝ, ‖a • e₁ + b • e₂‖[f; z] ^ (2 : ℕ) = a ^ (2 : ℕ) + b ^ (2 : ℕ) := by
  have he₁_sq_nonneg : 0 ≤ inner ℝ e₁ (hessian f z e₁) := hzPos.inner_nonneg_right e₁
  have he₂_sq_nonneg : 0 ≤ inner ℝ e₂ (hessian f z e₂) := hzPos.inner_nonneg_right e₂
  have he₁_sq : inner ℝ e₁ (hessian f z e₁) = 1 := by
    simpa [he₁] using
      (sq_hessianLocalNorm_eq_inner_of_nonneg
        (f := f) (z := z) (u := e₁) he₁_sq_nonneg).symm
  have he₂_sq : inner ℝ e₂ (hessian f z e₂) = 1 := by
    simpa [he₂] using
      (sq_hessianLocalNorm_eq_inner_of_nonneg
        (f := f) (z := z) (u := e₂) he₂_sq_nonneg).symm
  have horth' : inner ℝ e₂ (hessian f z e₁) = 0 := by
    -- Symmetry moves the orthogonality relation to the opposite Hessian slot.
    have hsym : inner ℝ e₂ (hessian f z e₁) = inner ℝ e₁ (hessian f z e₂) := by
      simpa [real_inner_comm] using (hzPos.isSymmetric e₂ e₁).symm
    simpa [horth] using hsym
  intro a b
  have hab_nonneg : 0 ≤ inner ℝ (a • e₁ + b • e₂) (hessian f z (a • e₁ + b • e₂)) :=
    hzPos.inner_nonneg_right (a • e₁ + b • e₂)
  -- Expand the Hessian quadratic form in the local-orthonormal basis and cancel the cross terms.
  rw [sq_hessianLocalNorm_eq_inner_of_nonneg (f := f) (z := z) (u := a • e₁ + b • e₂) hab_nonneg]
  simp [map_add, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, horth,
    horth', he₁_sq, he₂_sq, pow_two]

/-- Helper for Theorem 5.1.7: dividing a nonzero coefficient pair by its Euclidean radius
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

/-- Helper for Theorem 5.1.7: on a normalized 2D Hessian model, the unresolved core estimate is
the pure unit-circle repeated-slot bound. -/
private lemma unitCircleDiagonalSampleBound
    {z e₁ e₂ : E}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (Mf : NNReal) (f : E → ℝ)
    (hnorm_model :
      ∀ a b : ℝ, ‖a • e₁ + b • e₂‖[f; z] ^ (2 : ℕ) = a ^ (2 : ℕ) + b ^ (2 : ℕ))
    (hdiag :
      ∀ a : E, |T ![a, a, a]| ≤ 2 * (Mf : ℝ) * ‖a‖[f; z] ^ (3 : ℕ)) :
    ∀ c s : ℝ, c ^ (2 : ℕ) + s ^ (2 : ℕ) = 1 →
      |T ![c • e₁ + s • e₂, c • e₁ + s • e₂, c • e₁ + s • e₂]| ≤ 2 * (Mf : ℝ) := by
  intro c s hunit
  have hnorm_sq : ‖c • e₁ + s • e₂‖[f; z] ^ (2 : ℕ) = 1 := by
    rw [hnorm_model, hunit]
  have hnorm_nonneg : 0 ≤ ‖c • e₁ + s • e₂‖[f; z] :=
    hessianLocalNorm_nonneg f z (c • e₁ + s • e₂)
  have hnorm_eq : ‖c • e₁ + s • e₂‖[f; z] = 1 := by
    nlinarith
  -- Specialize the diagonal cubic bound to a unit vector in the normalized 2D model.
  simpa [hnorm_eq] using hdiag (c • e₁ + s • e₂)

/-- Helper for Theorem 5.1.7: a symmetric trilinear map recovers its `(u,w,w)` coefficient from
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

/-- Helper for Theorem 5.1.7: the diagonal value of a symmetric trilinear map on
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
    trilinearApplySmulFirst, trilinearApplySmulFirst]
  rw [trilinearApplySmulThird, trilinearApplySmulThird, trilinearApplySmulThird,
    trilinearApplySmulThird]
  rw [trilinearApplySmulSecond, trilinearApplySmulSecond, trilinearApplySmulSecond,
    trilinearApplySmulSecond]
  rw [hswap23 e₁ e₂ e₁, hswap12 e₂ e₁ e₁, hswap23 e₁ e₂ e₁, hswap12 e₂ e₁ e₂,
    hswap23 e₂ e₂ e₁, hswap12 e₂ e₁ e₂]
  ring

/-- Helper for Theorem 5.1.7: a first-quadrant unit-circle coefficient pair lifts to the
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
      _ = Real.cos (Real.arcsin c) := by
            symm
            exact Real.cos_arcsin c
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

/-- Helper for Theorem 5.1.7: the mixed repeated-slot coefficient `T[c • e₁ + s • e₂, e₂, e₂]`
is an explicit convex combination of three diagonal unit-circle samples after a cubic-angle
reparameterization. -/
private lemma symmetricTrilinear_thirdAngleInterpolation
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (hswap12 : ∀ a b c : E, T ![a, b, c] = T ![b, a, c])
    (hswap23 : ∀ a b c : E, T ![a, b, c] = T ![a, c, b])
    {e₁ e₂ : E} {sa ca c s : ℝ}
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

/-- Helper for Theorem 5.1.7: in the first-quadrant unit-circle case, the mixed repeated-slot
term is bounded by the diagonal cubic bound through the three-sample interpolation formula. -/
private lemma symmetricTrilinear_unitCircle_dvvBound_onNormModel2D_nonneg
    {z e₁ e₂ : E}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (hswap12 : ∀ a b c : E, T ![a, b, c] = T ![b, a, c])
    (hswap23 : ∀ a b c : E, T ![a, b, c] = T ![a, c, b])
    (Mf : NNReal) (f : E → ℝ)
    (hnorm_model :
      ∀ a b : ℝ, ‖a • e₁ + b • e₂‖[f; z] ^ (2 : ℕ) = a ^ (2 : ℕ) + b ^ (2 : ℕ))
    (hdiag :
      ∀ a : E, |T ![a, a, a]| ≤ 2 * (Mf : ℝ) * ‖a‖[f; z] ^ (3 : ℕ))
    {c s : ℝ} (hc_nonneg : 0 ≤ c) (hs_nonneg : 0 ≤ s)
    (hunit : c ^ (2 : ℕ) + s ^ (2 : ℕ) = 1) :
    |T ![c • e₁ + s • e₂, e₂, e₂]| ≤ 2 * (Mf : ℝ) := by
  obtain ⟨sa, ca, hsq, hs, hc⟩ :=
    firstQuadrantUnitCircle_hasThirdAngleParameters hc_nonneg hs_nonneg hunit
  have hsqrt_sq : (Real.sqrt 3) ^ (2 : ℕ) = 3 := by
    rw [show (Real.sqrt 3) ^ (2 : ℕ) = (Real.sqrt 3) ^ 2 by rfl]
    rw [Real.sq_sqrt (by positivity)]
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
  have hl₀_nonneg : 0 ≤ l₀ := by positivity
  have hl₁_nonneg : 0 ≤ l₁ := by positivity
  have hl₂_nonneg : 0 ≤ l₂ := by positivity
  have hweights :
      l₀ + l₁ + l₂ = 1 := by
    -- The three interpolation weights form a partition of unity.
    simp [l₀, l₁, l₂]
    ring_nf
    rw [hsqrt_sq, hca2]
    ring_nf
  have hinterp :=
    symmetricTrilinear_thirdAngleInterpolation T hswap12 hswap23
      (e₁ := e₁) (e₂ := e₂) (sa := sa) (ca := ca) (c := c) (s := s) hsq hs hc
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

/-- Helper for Theorem 5.1.7: flipping the signs of the orthonormal basis reduces the general
unit-circle estimate to the first-quadrant case. -/
private lemma symmetricTrilinear_unitCircle_dvvBound_onNormModel2D
    {z e₁ e₂ : E}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (hswap12 : ∀ a b c : E, T ![a, b, c] = T ![b, a, c])
    (hswap23 : ∀ a b c : E, T ![a, b, c] = T ![a, c, b])
    (Mf : NNReal) (f : E → ℝ)
    (hnorm_model :
      ∀ a b : ℝ, ‖a • e₁ + b • e₂‖[f; z] ^ (2 : ℕ) = a ^ (2 : ℕ) + b ^ (2 : ℕ))
    (hdiag :
      ∀ a : E, |T ![a, a, a]| ≤ 2 * (Mf : ℝ) * ‖a‖[f; z] ^ (3 : ℕ)) :
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
      ∀ a b : ℝ, ‖a • e₁' + b • e₂'‖[f; z] ^ (2 : ℕ) = a ^ (2 : ℕ) + b ^ (2 : ℕ) := by
    intro a b
    -- Flipping basis-vector signs preserves the same normalized 2D norm model.
    dsimp [e₁', e₂']
    calc
      ‖a • (σc • e₁) + b • (σs • e₂)‖[f; z] ^ (2 : ℕ)
          = ‖(a * σc) • e₁ + (b * σs) • e₂‖[f; z] ^ (2 : ℕ) := by
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

/-- Helper for Theorem 5.1.7: after normalizing the coefficients to the unit circle, the pure
2D unit-circle estimate immediately rescales back to arbitrary coefficients. -/
private lemma symmetricTrilinear_dvvBound_ofDiagonalBound_onNormModel2D
    {z e₁ e₂ : E}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (hswap12 : ∀ a b c : E, T ![a, b, c] = T ![b, a, c])
    (hswap23 : ∀ a b c : E, T ![a, b, c] = T ![a, c, b])
    (Mf : NNReal) (f : E → ℝ)
    (hnorm_model :
      ∀ a b : ℝ, ‖a • e₁ + b • e₂‖[f; z] ^ (2 : ℕ) = a ^ (2 : ℕ) + b ^ (2 : ℕ))
    (hdiag :
      ∀ a : E, |T ![a, a, a]| ≤ 2 * (Mf : ℝ) * ‖a‖[f; z] ^ (3 : ℕ)) :
    ∀ a b : ℝ,
      |T ![a • e₁ + b • e₂, e₂, e₂]| ≤
        2 * (Mf : ℝ) * Real.sqrt (a ^ (2 : ℕ) + b ^ (2 : ℕ)) := by
  intro a b
  let r : ℝ := Real.sqrt (a ^ (2 : ℕ) + b ^ (2 : ℕ))
  by_cases hr : r = 0
  · have hsq : r ^ (2 : ℕ) = 0 := by simp [hr]
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

/-- Helper for Theorem 5.1.7: the diagonal cubic bound controls the exact mixed slot pattern
`(d,v,v)` at a single point. -/
private lemma symmetric_trilinear_dvv_bound_of_diagonal_bound
    {Mf : NNReal} {f : E → ℝ} {z : E}
    (hcontAt : ContDiffAt ℝ 3 f z)
    (hzPos : (hessian f z).IsPositive)
    (hdiag_iter : ∀ a : E,
      |iteratedFDeriv ℝ 3 f z ![a, a, a]| ≤
        2 * (Mf : ℝ) * ‖a‖[f; z] ^ (3 : ℕ)) :
    ∀ d v : E,
      |iteratedFDeriv ℝ 3 f z ![d, v, v]| ≤
        2 * (Mf : ℝ) * ‖d‖[f; z] * ‖v‖[f; z] ^ (2 : ℕ) := by
  intro d v
  by_cases hd : ‖d‖[f; z] = 0
  · have hd_ann :
        ∀ a : E, inner ℝ d (hessian f z a) = 0 :=
      (hessian_localRadical_iff_annihilates_hessian (f := f) (z := z) (u := d) hzPos).1 hd
    have hzero :
        iteratedFDeriv ℝ 3 f z ![d, v, v] = 0 :=
      iteratedFDeriv_vanishes_on_hessian_localRadical
        (Mf := Mf) (f := f) (z := z) (u := d) (w := v) hcontAt hzPos
        (fun a ↦ by
          have hconst : (fun _ : Fin 3 ↦ a) = ![a, a, a] := by
            ext i
            fin_cases i <;> rfl
          simpa [thirdDirectionalDerivative_eq_iteratedFDeriv hcontAt, hconst] using hdiag_iter a)
        hd_ann
    -- Once the first slot is radical, the mixed third derivative is zero and the target bound is
    -- immediate because the right-hand side also vanishes.
    simp [hzero, hd]
  by_cases hv : ‖v‖[f; z] = 0
  · have hv_ann :
        ∀ a : E, inner ℝ v (hessian f z a) = 0 :=
      (hessian_localRadical_iff_annihilates_hessian (f := f) (z := z) (u := v) hzPos).1 hv
    have hzero :
        iteratedFDeriv ℝ 3 f z ![d, v, v] = 0 :=
      iteratedFDeriv_dvv_vanishes_on_hessian_localRadical
        (Mf := Mf) (f := f) (z := z) (d := d) (v := v) hcontAt hzPos
        (fun a ↦ by
          have hconst : (fun _ : Fin 3 ↦ a) = ![a, a, a] := by
            ext i
            fin_cases i <;> rfl
          simpa [thirdDirectionalDerivative_eq_iteratedFDeriv hcontAt, hconst] using hdiag_iter a)
        hv_ann
    -- The repeated-slot radical case is the same after one symmetry swap.
    simp [hzero, hv]
  have hd_pos : 0 < ‖d‖[f; z] :=
    lt_of_le_of_ne (hessianLocalNorm_nonneg f z d) (by
      intro hzero
      exact hd hzero.symm)
  have hv_pos : 0 < ‖v‖[f; z] :=
    lt_of_le_of_ne (hessianLocalNorm_nonneg f z v) (by
      intro hzero
      exact hv hzero.symm)
  let α : ℝ := inner ℝ d (hessian f z v) / ‖v‖[f; z] ^ (2 : ℕ)
  let w : E := d - α • v
  have hsplit :
      inner ℝ w (hessian f z v) = 0 ∧
        ‖d‖[f; z] ^ (2 : ℕ) = ‖w‖[f; z] ^ (2 : ℕ) + (α * ‖v‖[f; z]) ^ (2 : ℕ) := by
    simpa [α, w] using
      hessianProjectionSplit (f := f) (z := z) (d := d) (v := v) hzPos hv
  obtain ⟨horth, hpyth⟩ := hsplit
  have hd_eq : d = w + α • v := by
    -- Rewrite the original direction into the orthogonal residual plus the `v`-component.
    dsimp [w]
    abel_nf
  by_cases hw : ‖w‖[f; z] = 0
  · have hw_ann :
        ∀ a : E, inner ℝ w (hessian f z a) = 0 :=
      (hessian_localRadical_iff_annihilates_hessian (f := f) (z := z) (u := w) hzPos).1 hw
    have hw_zero :
        iteratedFDeriv ℝ 3 f z ![w, v, v] = 0 :=
      iteratedFDeriv_vanishes_on_hessian_localRadical
        (Mf := Mf) (f := f) (z := z) (u := w) (w := v) hcontAt hzPos
        (fun a ↦ by
          have hconst : (fun _ : Fin 3 ↦ a) = ![a, a, a] := by
            ext i
            fin_cases i <;> rfl
          simpa [thirdDirectionalDerivative_eq_iteratedFDeriv hcontAt, hconst] using
            hdiag_iter a)
        hw_ann
    have hd_abs : ‖d‖[f; z] = |α| * ‖v‖[f; z] := by
      have hd_sq :
          ‖d‖[f; z] ^ (2 : ℕ) = (α * ‖v‖[f; z]) ^ (2 : ℕ) := by
        simpa [hw] using hpyth
      have hsqrt := congrArg Real.sqrt hd_sq
      simpa [Real.sqrt_sq_eq_abs, abs_mul, abs_of_nonneg (hessianLocalNorm_nonneg f z d),
        abs_of_nonneg (hessianLocalNorm_nonneg f z v)] using hsqrt
    -- Once the residual is radical, only the diagonal `v` contribution survives.
    calc
      |iteratedFDeriv ℝ 3 f z ![d, v, v]|
          = |iteratedFDeriv ℝ 3 f z ![w + α • v, v, v]| := by rw [hd_eq]
      _ = |iteratedFDeriv ℝ 3 f z ![w, v, v] + iteratedFDeriv ℝ 3 f z ![α • v, v, v]| := by
            rw [trilinearApplyAddFirst]
      _ = |α * iteratedFDeriv ℝ 3 f z ![v, v, v]| := by
            rw [hw_zero, trilinearApplySmulFirst]
            simp
      _ = |α| * |iteratedFDeriv ℝ 3 f z ![v, v, v]| := by rw [abs_mul]
      _ ≤ |α| * (2 * (Mf : ℝ) * ‖v‖[f; z] ^ (3 : ℕ)) := by
            gcongr
            exact hdiag_iter v
      _ = 2 * (Mf : ℝ) * (|α| * ‖v‖[f; z]) * ‖v‖[f; z] ^ (2 : ℕ) := by
            ring
      _ = 2 * (Mf : ℝ) * ‖d‖[f; z] * ‖v‖[f; z] ^ (2 : ℕ) := by
            rw [← hd_abs]
  have hw_pos : 0 < ‖w‖[f; z] :=
    lt_of_le_of_ne (hessianLocalNorm_nonneg f z w) (by
      intro hzero
      exact hw hzero.symm)
  let e₁ : E := (‖w‖[f; z])⁻¹ • w
  let e₂ : E := (‖v‖[f; z])⁻¹ • v
  have he₁_norm : ‖e₁‖[f; z] = 1 := by
    -- Normalize the nonradical residual direction.
    dsimp [e₁]
    rw [hessianLocalNorm_smul_eq_abs_of_isPositive (f := f) (z := z) (u := w) hzPos]
    simp [abs_of_pos (inv_pos.mpr hw_pos), hw_pos.ne']
  have he₂_norm : ‖e₂‖[f; z] = 1 := by
    -- Normalize the original repeated direction.
    dsimp [e₂]
    rw [hessianLocalNorm_smul_eq_abs_of_isPositive (f := f) (z := z) (u := v) hzPos]
    simp [abs_of_pos (inv_pos.mpr hv_pos), hv_pos.ne']
  have he₁e₂_orth : inner ℝ e₁ (hessian f z e₂) = 0 := by
    -- The normalized pair remains orthogonal for the Hessian bilinear form.
    simp [e₁, e₂, inner_smul_left, inner_smul_right, horth]
  have hnorm_model :
      ∀ a b : ℝ, ‖a • e₁ + b • e₂‖[f; z] ^ (2 : ℕ) = a ^ (2 : ℕ) + b ^ (2 : ℕ) :=
    hessianLocalNorm_sq_of_localOrthonormalPair
      (f := f) (z := z) (e₁ := e₁) (e₂ := e₂) hzPos he₁_norm he₂_norm he₁e₂_orth
  have hw_scale : ‖w‖[f; z] • e₁ = w := by
    -- Rescaling the normalized residual recovers the original residual vector.
    dsimp [e₁]
    rw [smul_smul, mul_inv_cancel₀ hw_pos.ne', one_smul]
  have hv_scale : (α * ‖v‖[f; z]) • e₂ = α • v := by
    -- Rescaling the normalized repeated direction recovers its original `α`-multiple.
    dsimp [e₂]
    rw [smul_smul, mul_assoc, mul_inv_cancel₀ hv_pos.ne', mul_one]
  have hd_model :
      d = ‖w‖[f; z] • e₁ + (α * ‖v‖[f; z]) • e₂ := by
    -- The orthogonal split is now expressed in the normalized local-orthonormal basis.
    calc
      d = w + α • v := hd_eq
      _ = ‖w‖[f; z] • e₁ + (α * ‖v‖[f; z]) • e₂ := by
            rw [hw_scale, hv_scale]
  have hv_scale' : ‖v‖[f; z] • e₂ = v := by
    -- Rescaling the normalized repeated direction recovers the original repeated vector.
    dsimp [e₂]
    rw [smul_smul, mul_inv_cancel₀ hv_pos.ne', one_smul]
  let T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ := iteratedFDeriv ℝ 3 f z
  have hswap12 :
      ∀ a b c : E, T ![a, b, c] = T ![b, a, c] := by
    intro a b c
    simpa [T] using
      iteratedFDeriv_three_swap12_at
        (f := f) (z := z) (u₁ := a) (u₂ := b) (u₃ := c) hcontAt
  have hswap23 :
      ∀ a b c : E, T ![a, b, c] = T ![a, c, b] := by
    intro a b c
    simpa [T] using
      iteratedFDeriv_three_swap23_at
        (f := f) (z := z) (u₁ := a) (u₂ := b) (u₃ := c) hcontAt
  have hdiag_model :
      ∀ a : E, |T ![a, a, a]| ≤ 2 * (Mf : ℝ) * ‖a‖[f; z] ^ (3 : ℕ) := by
    intro a
    simpa [T] using hdiag_iter a
  have hmodel_bound :
      |T ![‖w‖[f; z] • e₁ + (α * ‖v‖[f; z]) • e₂, e₂, e₂]| ≤
        2 * (Mf : ℝ) *
          Real.sqrt (‖w‖[f; z] ^ (2 : ℕ) + (α * ‖v‖[f; z]) ^ (2 : ℕ)) :=
    symmetricTrilinear_dvvBound_ofDiagonalBound_onNormModel2D
      (T := T) (e₁ := e₁) (e₂ := e₂)
      hswap12 hswap23 (Mf := Mf) (f := f) hnorm_model hdiag_model
      ‖w‖[f; z] (α * ‖v‖[f; z])
  have hroot :
      Real.sqrt (‖w‖[f; z] ^ (2 : ℕ) + (α * ‖v‖[f; z]) ^ (2 : ℕ)) = ‖d‖[f; z] := by
    -- The orthogonal decomposition identifies the Euclidean model radius with `‖d‖[f; z]`.
    have hsqrt := congrArg Real.sqrt hpyth.symm
    simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg (hessianLocalNorm_nonneg f z d)] using hsqrt
  -- Route correction: the main theorem is now reduced to the unit-circle 2D lemma above, plus the
  -- already-verified normalization and scaling rewrites in the model `(e₁, e₂)`.
  calc
    |iteratedFDeriv ℝ 3 f z ![d, v, v]| = |T ![d, v, v]| := by rfl
    _ = |T ![‖w‖[f; z] • e₁ + (α * ‖v‖[f; z]) • e₂, v, v]| := by rw [hd_model]
    _ = |T ![‖w‖[f; z] • e₁ + (α * ‖v‖[f; z]) • e₂, ‖v‖[f; z] • e₂, ‖v‖[f; z] • e₂]| := by
          have hslots :
              ![‖w‖[f; z] • e₁ + (α * ‖v‖[f; z]) • e₂, v, v] =
                ![‖w‖[f; z] • e₁ + (α * ‖v‖[f; z]) • e₂,
                  ‖v‖[f; z] • e₂, ‖v‖[f; z] • e₂] := by
            ext i
            fin_cases i <;> simp [hv_scale']
          rw [hslots]
    _ = |‖v‖[f; z] * (‖v‖[f; z] *
          T ![‖w‖[f; z] • e₁ + (α * ‖v‖[f; z]) • e₂, e₂, e₂])| := by
          rw [trilinearApplySmulSecond, trilinearApplySmulThird]
    _ = ‖v‖[f; z] ^ (2 : ℕ) *
          |T ![‖w‖[f; z] • e₁ + (α * ‖v‖[f; z]) • e₂, e₂, e₂]| := by
          simp [pow_two, abs_of_nonneg (hessianLocalNorm_nonneg f z v), mul_assoc, mul_comm]
    _ ≤ ‖v‖[f; z] ^ (2 : ℕ) *
          (2 * (Mf : ℝ) *
            Real.sqrt (‖w‖[f; z] ^ (2 : ℕ) + (α * ‖v‖[f; z]) ^ (2 : ℕ))) := by
          gcongr
    _ = 2 * (Mf : ℝ) *
          Real.sqrt (‖w‖[f; z] ^ (2 : ℕ) + (α * ‖v‖[f; z]) ^ (2 : ℕ)) *
            ‖v‖[f; z] ^ (2 : ℕ) := by
          ring
    _ = 2 * (Mf : ℝ) * ‖d‖[f; z] * ‖v‖[f; z] ^ (2 : ℕ) := by rw [hroot]

/-- Helper for Theorem 5.1.7: the diagonal Chapter 5 cubic bound should upgrade to the local
mixed third-derivative estimate in the exact `(d,v,v)` slot pattern used by the segment ODE. -/
private lemma pointwise_iteratedFDeriv_dvv_bound_of_diagonal
    {Mf : NNReal} {f : E → ℝ} {z : E}
    (hcontAt : ContDiffAt ℝ 3 f z)
    (hzPos : (hessian f z).IsPositive)
    (hdiag_z : ∀ u : E,
      |thirdDirectionalDerivative f z u| ≤
        2 * (Mf : ℝ) * ‖u‖[f; z] ^ (3 : ℕ)) :
    ∀ d v : E,
      |iteratedFDeriv ℝ 3 f z ![d, v, v]| ≤
        2 * (Mf : ℝ) * ‖d‖[f; z] * ‖v‖[f; z] ^ (2 : ℕ) := by
  intro d v
  have hdiag_iter :
      ∀ u : E,
        |iteratedFDeriv ℝ 3 f z ![u, u, u]| ≤
          2 * (Mf : ℝ) * ‖u‖[f; z] ^ (3 : ℕ) := by
    intro u
    have hconst : (fun _ : Fin 3 ↦ u) = ![u, u, u] := by
      ext i
      fin_cases i <;> rfl
    -- Rewrite the textbook diagonal third derivative through the iterated derivative owner.
    simpa [thirdDirectionalDerivative_eq_iteratedFDeriv hcontAt, hconst] using hdiag_z u
  -- Route correction: the diagonal-to-`(d,v,v)` bridge is now provided by the local symmetric
  -- trilinear estimate, so the theorem only needs this one wrapper rewrite.
  exact symmetric_trilinear_dvv_bound_of_diagonal_bound
    (Mf := Mf) (f := f) (z := z) hcontAt hzPos hdiag_iter d v

/-- Helper for Theorem 5.1.7: the scalar Hessian-direction pairing is the quadratic-slot
evaluation of the third iterated derivative. -/
private lemma pointwise_mixed_hessian_pairing_eq_iteratedFDeriv
    {f : E → ℝ} {z d v : E}
    (hcontAt : ContDiffAt ℝ 3 f z) :
    inner ℝ v ((fderiv ℝ (hessian f) z d) v) = iteratedFDeriv ℝ 3 f z ![d, v, v] := by
  let line : ℝ → E := fun s ↦ z + s • d
  let φ : ℝ → ℝ := fun s ↦ inner ℝ v (hessian f (line s) v)
  let ψ : ℝ → ℝ := fun s ↦ iteratedFDeriv ℝ 2 f (line s) ![v, v]
  obtain ⟨u, hu, hcontOn⟩ :=
    hcontAt.contDiffOn (m := 3) (by simp) (by intro h; simp at h)
  obtain ⟨s, hs_sub, hs_open, hzs⟩ := mem_nhds_iff.mp hu
  have hs_contOn : ContDiffOn ℝ 3 f s := hcontOn.mono hs_sub
  have hEqOn : ∀ w ∈ s, inner ℝ v (hessian f w v) = iteratedFDeriv ℝ 2 f w ![v, v] := by
    intro w hw
    -- On a local `C³` neighborhood, the Hessian quadratic form is exactly the second iterated
    -- derivative evaluated on the repeated direction `v`.
    have hw_cont : ContDiffAt ℝ 3 f w := hs_contOn.contDiffAt (hs_open.mem_nhds hw)
    have hfderiv_C2 : ContDiffAt ℝ 2 (fderiv ℝ f) w := by
      exact hw_cont.fderiv_right (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)
    have hfderiv_diff : DifferentiableAt ℝ (fderiv ℝ f) w := by
      exact hfderiv_C2.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
    have hgrad_hasFDeriv :
        HasFDerivAt (∇ f)
          (((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
            (fderiv ℝ (fderiv ℝ f) w)) w := by
      simpa [gradient] using
        (((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap).hasFDerivAt.comp
          w hfderiv_diff.hasFDerivAt)
    rw [hessian, hgrad_hasFDeriv.fderiv]
    simp only [ContinuousLinearMap.comp_apply]
    rw [real_inner_comm]
    calc
      inner ℝ
          ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv
            ((fderiv ℝ (fderiv ℝ f) w) v)) v
          = ((fderiv ℝ (fderiv ℝ f) w) v) v := by
              simpa using
                (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := E) (x := v)
                  (y := ((fderiv ℝ (fderiv ℝ f) w) v)))
      _ = iteratedFDeriv ℝ 2 f w ![v, v] := by
            simpa [iteratedFDeriv_two_apply]
  have hline_mem : ∀ᶠ t in nhds (0 : ℝ), line t ∈ s := by
    let hline0 : ContinuousAt line 0 :=
      (affine_segment_hasDerivAt (x := z) (d := d) 0).continuousAt
    exact hline0.tendsto.eventually (hs_open.mem_nhds (by simpa [line] using hzs))
  have hEq : ψ =ᶠ[nhds (0 : ℝ)] φ := by
    filter_upwards [hline_mem] with t ht
    simp [ψ, φ, line, hEqOn _ ht]
  have hφ :
      HasDerivAt φ (inner ℝ v ((fderiv ℝ (hessian f) z d) v)) 0 := by
    have hzLine : HasDerivAt line d 0 := by
      simpa [line] using affine_segment_hasDerivAt (x := z) (d := d) 0
    have hhessianDeriv :
        HasFDerivAt (hessian f) (fderiv ℝ (hessian f) (line 0)) (line 0) := by
      simpa [line] using hessian_hasFDerivAt_of_contDiffAt (f := f) (z := z) hcontAt
    have happly :
        HasDerivAt (fun t : ℝ ↦ hessian f (line t) v)
          ((fderiv ℝ (hessian f) (line 0) d) v) 0 := by
      -- Differentiate the operator-valued Hessian map along the affine line and then evaluate
      -- it on the fixed direction `v`.
      have happlyF :
          HasFDerivAt (fun w : E ↦ hessian f w v)
            ((ContinuousLinearMap.apply ℝ E v).comp (fderiv ℝ (hessian f) (line 0))) (line 0) := by
        exact (ContinuousLinearMap.apply ℝ E v).hasFDerivAt.comp (line 0) hhessianDeriv
      simpa using happlyF.comp_hasDerivAt 0 hzLine
    have hinnerF :
        HasFDerivAt (fun w : E ↦ inner ℝ v w) ((innerSL ℝ) v) (hessian f (line 0) v) := by
      simpa using ((innerSL ℝ) v).hasFDerivAt
    -- The scalar pairing `φ` is the composition of the Hessian line with the fixed inner-product
    -- functional against `v`.
    simpa [φ, line] using hinnerF.comp_hasDerivAt 0 happly
  have hiter2_C1 : ContDiffAt ℝ 1 (iteratedFDeriv ℝ 2 f) z := by
    exact hcontAt.iteratedFDeriv_right (m := 1) (i := 2)
      (by norm_num : (1 : WithTop ℕ∞) + 2 ≤ 3)
  have hiter2_deriv :
      HasFDerivAt (iteratedFDeriv ℝ 2 f) (fderiv ℝ (iteratedFDeriv ℝ 2 f) z) z := by
    exact (hiter2_C1.hasStrictFDerivAt one_ne_zero).hasFDerivAt
  have hψ :
      HasDerivAt ψ (((fderiv ℝ (iteratedFDeriv ℝ 2 f) z) d) ![v, v]) 0 := by
    have hline0 : HasDerivAt line d 0 := by
      simpa [line] using affine_segment_hasDerivAt (x := z) (d := d) 0
    have hcomp :
        HasDerivAt (fun t : ℝ ↦ iteratedFDeriv ℝ 2 f (line t))
          ((fderiv ℝ (iteratedFDeriv ℝ 2 f) z) d) 0 := by
      simpa [line] using
        hiter2_deriv.comp_hasDerivAt_of_eq 0 hline0 (by simp [line])
    -- Evaluate the derivative of the bilinear iterated derivative on the repeated direction `v`.
    simpa [ψ] using
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E) ℝ ![v, v]).hasFDerivAt.comp_hasDerivAt 0
        hcomp)
  have hψ_from_φ : HasDerivAt ψ (inner ℝ v ((fderiv ℝ (hessian f) z d) v)) 0 :=
    hφ.congr_of_eventuallyEq hEq
  have hsame :
      inner ℝ v ((fderiv ℝ (hessian f) z d) v) =
        ((fderiv ℝ (iteratedFDeriv ℝ 2 f) z) d) ![v, v] :=
    hψ_from_φ.unique hψ
  -- Rewrite the iterated derivative derivative back to the canonical third-order owner.
  simpa [iteratedFDeriv_succ_apply_left] using hsame

/-- Helper for Theorem 5.1.7: the pointwise mixed third-derivative bound specializes to the
scalar Hessian-direction pairing needed for the segment ODE. -/
private lemma pointwise_mixed_hessian_pairing_bound_of_diagonal
    {Mf : NNReal} {f : E → ℝ} {z : E}
    (hcontAt : ContDiffAt ℝ 3 f z)
    (hzPos : (hessian f z).IsPositive)
    (hdiag_z : ∀ u : E,
      |thirdDirectionalDerivative f z u| ≤
        2 * (Mf : ℝ) * ‖u‖[f; z] ^ (3 : ℕ)) :
    ∀ d v : E,
      |inner ℝ v ((fderiv ℝ (hessian f) z d) v)| ≤
        2 * (Mf : ℝ) * ‖d‖[f; z] * inner ℝ v (hessian f z v) := by
  intro d v
  have hv_quad_nonneg : 0 ≤ inner ℝ v (hessian f z v) :=
    hzPos.inner_nonneg_right v
  have hv_sq :
      ‖v‖[f; z] ^ (2 : ℕ) = inner ℝ v (hessian f z v) :=
    sq_hessianLocalNorm_eq_inner_of_nonneg hv_quad_nonneg
  have htrilinear :=
    pointwise_iteratedFDeriv_dvv_bound_of_diagonal
      (Mf := Mf) (f := f) (z := z) hcontAt hzPos hdiag_z d v
  have hpair_eq :
      inner ℝ v ((fderiv ℝ (hessian f) z d) v) = iteratedFDeriv ℝ 3 f z ![d, v, v] :=
    pointwise_mixed_hessian_pairing_eq_iteratedFDeriv (f := f) (z := z) (d := d) (v := v) hcontAt
  -- After isolating the exact scalar adapter, the fixed-point multilinear bound closes the
  -- pairing estimate by rewriting `‖v‖[f; z]^2` back to the Hessian quadratic form.
  calc
    |inner ℝ v ((fderiv ℝ (hessian f) z d) v)|
        = |iteratedFDeriv ℝ 3 f z ![d, v, v]| := by rw [hpair_eq]
    _ ≤ 2 * (Mf : ℝ) * ‖d‖[f; z] * ‖v‖[f; z] ^ (2 : ℕ) := htrilinear
    _ = 2 * (Mf : ℝ) * ‖d‖[f; z] * inner ℝ v (hessian f z v) := by rw [hv_sq]

/-- Helper for Theorem 5.1.7: evaluating the pointwise scalar pairing inequality produces the
scalar differential inequality for the Hessian quadratic form along the segment. -/
private lemma segment_scalarized_hessian_deriv_bounds
    {Mf : NNReal} {f : E → ℝ} {x y : E}
    {z : ℝ → E} (hz : z = fun t ↦ x + t • (y - x))
    (hcont : ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) 1 → ContDiffAt ℝ 3 f (z t))
    (hpsd : ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) 1 → (hessian f (z t)).IsPositive)
    (hthird : ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) 1 → ∀ u : E,
      |thirdDirectionalDerivative f (z t) u| ≤
        2 * (Mf : ℝ) * ‖u‖[f; z t] ^ (3 : ℕ)) :
    ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) 1 → ∀ v : E,
      let ψ : ℝ → ℝ := fun s ↦ inner ℝ v (hessian f (z s) v);
      -2 * (Mf : ℝ) * ‖y - x‖[f; z t] * ψ t ≤ deriv ψ t ∧
        deriv ψ t ≤ 2 * (Mf : ℝ) * ‖y - x‖[f; z t] * ψ t := by
  intro t ht v
  let ψ : ℝ → ℝ := fun s ↦ inner ℝ v (hessian f (z s) v)
  let c : ℝ := 2 * (Mf : ℝ) * ‖y - x‖[f; z t]
  have hpsi_derivAt :
      HasDerivAt ψ (inner ℝ v ((fderiv ℝ (hessian f) (z t) (y - x)) v)) t := by
    -- Differentiate the scalarized Hessian quadratic form along the affine segment.
    simpa [ψ] using
      segment_scalarized_hessian_hasDerivAt
        (f := f) (x := x) (y := y) (v := v) (z := z) hz (hcont ht)
  have hpsi_deriv :
      deriv ψ t = inner ℝ v ((fderiv ℝ (hessian f) (z t) (y - x)) v) := by
    exact hpsi_derivAt.deriv
  have hpair_bound :
      |inner ℝ v ((fderiv ℝ (hessian f) (z t) (y - x)) v)| ≤ c * ψ t := by
    -- The source-faithful mixed scalar bridge gives the exact absolute derivative control.
    simpa [ψ, c] using
      pointwise_mixed_hessian_pairing_bound_of_diagonal
      (Mf := Mf) (f := f) (z := z t) (hcontAt := hcont ht) (hzPos := hpsd ht)
      (hdiag_z := hthird ht) (y - x) v
  have habs_deriv :
      |deriv ψ t| ≤ c * ψ t := by
    simpa [hpsi_deriv] using hpair_bound
  rcases abs_le.mp habs_deriv with ⟨hlower, hupper⟩
  constructor
  · -- Unpack the absolute-value estimate into the lower scalar differential inequality.
    simpa [c, ψ, mul_assoc] using hlower
  · -- The upper scalar differential inequality is the other half of the same absolute-value bound.
    simpa [c, ψ, mul_assoc] using hupper

/-- Helper for Theorem 5.1.7: once the scalar derivative bounds along the segment are available,
the remaining source-faithful task is to combine them with the local-norm transport factor and
evaluate the resulting weighted monotonicity at the endpoints. -/
private lemma segmentReciprocalLocalNorm_prefixLowerBound
    {dom : Set E} {Mf : NNReal} {f : E → ℝ} {x y : E}
    (hdom_open : IsOpen dom)
    (hcont : ContDiffOn ℝ 3 f dom)
    (hsegment : segment ℝ x y ⊆ dom)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hprefix : ∀ u ∈ Set.Icc (0 : ℝ) s, 0 < ‖y - x‖[f; x + u • (y - x)])
    (hbound :
      ∀ {u : ℝ}, u ∈ Set.Icc (0 : ℝ) s →
        |thirdDirectionalDerivative f (x + u • (y - x)) (y - x)| /
            (2 * ‖y - x‖[f; x + u • (y - x)] ^ (3 : ℕ)) ≤
          (Mf : ℝ)) :
    (1 / ‖y - x‖[f; x]) - (Mf : ℝ) * s ≤
      (‖y - x‖[f; x + s • (y - x)])⁻¹ := by
  let d : E := y - x
  let D : Set ℝ := Set.Icc (0 : ℝ) s
  let g : ℝ → ℝ := directionalSlice (fun z : E ↦ (‖d‖[f; z])⁻¹) x d
  have hsubset_slice : D ⊆ associatedUnivariateFunctionDomain dom f x d := by
    intro u hu
    have hu01 : u ∈ Set.Icc (0 : ℝ) 1 := ⟨hu.1, hu.2.trans hs.2⟩
    refine (mem_associatedUnivariateFunctionDomain_iff dom f x d u).2 ?_
    constructor
    · exact hsegment (by simpa [d] using segment_point_mem_segment (x := x) (y := y) hu01)
    · simpa [D, d] using hprefix u hu
  have hderivWithin :
      ∀ t ∈ D,
        HasDerivWithinAt g
          (-(thirdDirectionalDerivative f (x + t • d) d /
              (2 * ‖d‖[f; x + t • d] ^ (3 : ℕ))))
          D
          t := by
    intro t ht
    have ht_slice : t ∈ associatedUnivariateFunctionDomain dom f x d := hsubset_slice ht
    -- Restrict the Chapter 5 reciprocal-slice derivative formula to the current positive prefix.
    simpa [g] using
      (associatedUnivariateFunction_hasDerivWithinAt
        (dom := dom) (f := f) (x := x) (h := d) hdom_open hcont ht_slice).mono hsubset_slice
  have hderivInterior :
      ∀ t ∈ interior D,
        HasDerivWithinAt g
          (-(thirdDirectionalDerivative f (x + t • d) d /
              (2 * ‖d‖[f; x + t • d] ^ (3 : ℕ))))
          (interior D)
          t := by
    intro t ht
    -- On interior points we may shrink the derivative set further to `interior D`.
    exact (hderivWithin t (interior_subset ht)).mono interior_subset
  have hcontOn : ContinuousOn g D := by
    intro t ht
    -- Every point of the positive prefix inherits continuity from the derivative formula there.
    exact (hderivWithin t ht).continuousWithinAt
  have hdiffOn : DifferentiableOn ℝ g (interior D) := by
    intro t ht
    -- The restricted derivative formula also supplies differentiability on the interval interior.
    exact (hderivInterior t ht).differentiableWithinAt
  have hderiv_ge : ∀ t ∈ interior D, -(Mf : ℝ) ≤ deriv g t := by
    intro t ht
    rw [deriv_eqOn isOpen_interior hderivInterior ht]
    have hden_pos : 0 < 2 * ‖d‖[f; x + t • d] ^ (3 : ℕ) := by
      have htD : t ∈ D := interior_subset ht
      have hnorm_pos : 0 < ‖d‖[f; x + t • d] := by
        simpa [D, d] using hprefix t htD
      positivity
    have hq :
        |thirdDirectionalDerivative f (x + t • d) d| /
            (2 * ‖d‖[f; x + t • d] ^ (3 : ℕ)) ≤
          (Mf : ℝ) :=
      hbound (interior_subset ht)
    have hq' :
        |thirdDirectionalDerivative f (x + t • d) d /
            (2 * ‖d‖[f; x + t • d] ^ (3 : ℕ))| ≤
          (Mf : ℝ) := by
      simpa [abs_div, abs_of_pos hden_pos, abs_abs] using hq
    -- The absolute quotient bound yields the affine lower derivative bound for the reciprocal
    -- local norm.
    linarith [(abs_le.mp hq').2]
  have hgrowth :
      (-(Mf : ℝ)) * (s - 0) ≤ g s - g 0 := by
    exact
      (convex_Icc (0 : ℝ) s).mul_sub_le_image_sub_of_le_deriv
        hcontOn hdiffOn hderiv_ge 0 (by simpa [D] using hs.1) s
        (by simpa [D] using show s ∈ Set.Icc (0 : ℝ) s from ⟨hs.1, le_rfl⟩) hs.1
  -- Evaluate the monotone affine lower bound at the prefix endpoints.
  simpa [g, directionalSlice, d] using hgrowth

/-- Helper for Theorem 5.1.7: once the scalar derivative bounds along the segment are available,
the remaining source-faithful task is to combine them with the local-norm transport factor and
evaluate the resulting weighted monotonicity at the endpoints. -/
private lemma segment_weight_factor_pos
    {Mf : NNReal} {f : E → ℝ} {x y : E}
    (hr_lt : ‖y - x‖[f; x] < 1 / (Mf : ℝ))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 < 1 - t * ((Mf : ℝ) * ‖y - x‖[f; x]) := by
  -- The endpoint Dikin factor controls every intermediate factor because `t ∈ [0, 1]`.
  have hMf_nonneg : 0 ≤ (Mf : ℝ) := Mf.2
  have hr_nonneg : 0 ≤ ‖y - x‖[f; x] := hessianLocalNorm_nonneg f x (y - x)
  have ha_nonneg : 0 ≤ (Mf : ℝ) * ‖y - x‖[f; x] := mul_nonneg hMf_nonneg hr_nonneg
  have ha_lt_one : (Mf : ℝ) * ‖y - x‖[f; x] < 1 := by
    by_cases hMf_zero : (Mf : ℝ) = 0
    · norm_num [hMf_zero]
    · have hMf_pos : 0 < (Mf : ℝ) := by
        exact lt_of_le_of_ne hMf_nonneg (by simpa [eq_comm] using hMf_zero)
      have hmul : ‖y - x‖[f; x] * (Mf : ℝ) < 1 := by
        exact (lt_div_iff₀ hMf_pos).1 hr_lt
      simpa [mul_comm] using hmul
  have hta_le_a : t * ((Mf : ℝ) * ‖y - x‖[f; x]) ≤ (Mf : ℝ) * ‖y - x‖[f; x] := by
    simpa using mul_le_mul_of_nonneg_right ht.2 ha_nonneg
  linarith

/-- Helper for Theorem 5.1.7: the displacement local norm varies continuously along the affine
segment `t ↦ x + t • (y - x)`. -/
private lemma segmentDisplacementLocalNorm_continuousOn
    {f : E → ℝ} {x y : E}
    {z : ℝ → E} (hz : z = fun t ↦ x + t • (y - x))
    (hcont : ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) 1 → ContDiffAt ℝ 3 f (z t)) :
    ContinuousOn (fun t ↦ ‖y - x‖[f; z t]) (Set.Icc (0 : ℝ) 1) := by
  intro t ht
  let d : E := y - x
  let ψ : ℝ → ℝ := fun s ↦ inner ℝ d (hessian f (z s) d)
  have hψ_contAt : ContinuousAt ψ t := by
    -- Differentiate the scalarized Hessian quadratic form first, then retain continuity.
    exact
      (segment_scalarized_hessian_hasDerivAt
        (f := f) (x := x) (y := y) (v := d) (z := z) hz (hcont ht)).continuousAt
  -- The local norm is the square root of that quadratic form, so continuity follows by
  -- composition with `Real.sqrt`.
  simpa [ψ, d, hessianLocalNorm_def] using
    (Real.continuous_sqrt.continuousAt.comp hψ_contAt).continuousWithinAt

/-- Helper for Theorem 5.1.7: the reciprocal local norm admits the same affine lower transport
bound on any positive subsegment, not only on prefixes starting at `t = 0`. -/
private lemma segmentReciprocalLocalNorm_lowerBound_between
    {dom : Set E} {Mf : NNReal} {f : E → ℝ} {x y : E}
    (hdom_open : IsOpen dom)
    (hcont : ContDiffOn ℝ 3 f dom)
    (hsegment : segment ℝ x y ⊆ dom)
    (hpsd : ∀ ⦃z : E⦄, z ∈ segment ℝ x y → (hessian f z).IsPositive)
    (hthird : ∀ ⦃z : E⦄ (_hz : z ∈ segment ℝ x y) (u : E),
      |thirdDirectionalDerivative f z u| ≤
        2 * (Mf : ℝ) * ‖u‖[f; z] ^ (3 : ℕ))
    {s t : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hst : s ≤ t)
    (hpos : ∀ u ∈ Set.Icc s t, 0 < ‖y - x‖[f; x + u • (y - x)]) :
    (‖y - x‖[f; x + s • (y - x)])⁻¹ - (Mf : ℝ) * (t - s) ≤
      (‖y - x‖[f; x + t • (y - x)])⁻¹ := by
  by_cases hst_eq : t = s
  · -- When the subinterval collapses, the claimed transport inequality is just equality.
    subst hst_eq
    simp
  have hts_pos : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hst (Ne.symm hst_eq))
  let d : E := y - x
  let x' : E := x + s • d
  let y' : E := x + t • d
  have hx'_segment : x' ∈ segment ℝ x y := by
    simpa [x', d] using segment_point_mem_segment (x := x) (y := y) hs
  have hy'_segment : y' ∈ segment ℝ x y := by
    simpa [y', d] using segment_point_mem_segment (x := x) (y := y) ht
  have hsubsegment : segment ℝ x' y' ⊆ dom := by
    -- Any point on the smaller segment still lies on the original segment `[x,y]`.
    intro z hz
    have hconv : Convex ℝ (segment ℝ x y) := by
      simpa using convex_segment (𝕜 := ℝ) x y
    exact hsegment (hconv.segment_subset hx'_segment hy'_segment hz)
  have hyx_eq : y' - x' = (t - s) • d := by
    -- The subsegment displacement is the original direction scaled by `t - s`.
    calc
      y' - x' = t • d - s • d := by simp [x', y']
      _ = (t - s) • d := by
        simp [sub_eq_add_neg, add_smul]
  have hsub_point_eq :
      ∀ u : ℝ, x' + u • (y' - x') = x + (s + u * (t - s)) • d := by
    intro u
    -- Re-express the subsegment parameterization inside the original affine chart.
    calc
      x' + u • (y' - x') = x + s • d + (u * (t - s)) • d := by
        dsimp [x']
        rw [hyx_eq, smul_smul]
      _ = x + (s • d + (u * (t - s)) • d) := by abel_nf
      _ = x + (s + u * (t - s)) • d := by rw [← add_smul]
  have hsub_point_eq' :
      ∀ u : ℝ, x' + u • ((t - s) • d) = x + (s + u * (t - s)) • d := by
    intro u
    calc
      x' + u • ((t - s) • d) = x + s • d + (u * (t - s)) • d := by
        dsimp [x']
        rw [smul_smul]
      _ = x + (s • d + (u * (t - s)) • d) := by abel_nf
      _ = x + (s + u * (t - s)) • d := by rw [← add_smul]
  have hprefix_sub :
      ∀ u ∈ Set.Icc (0 : ℝ) 1, 0 < ‖y' - x'‖[f; x' + u • (y' - x')] := by
    intro u hu
    have hu_param : s + u * (t - s) ∈ Set.Icc s t := by
      constructor <;> nlinarith [hu.1, hu.2, hst]
    have hu01 : s + u * (t - s) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · linarith [hs.1, hu_param.1]
      · linarith [ht.2, hu_param.2]
    have hpoint_pos :
        0 < ‖d‖[f; x + (s + u * (t - s)) • d] :=
      hpos _ hu_param
    have hpoint_psd :
        (hessian f (x' + u • (y' - x'))).IsPositive := by
      have hpoint_segment : x' + u • (y' - x') ∈ segment ℝ x y := by
        rw [hsub_point_eq]
        simpa [d] using segment_point_mem_segment (x := x) (y := y) hu01
      exact hpsd hpoint_segment
    have hpoint_psd' :
        (hessian f (x + (s + u * (t - s)) • d)).IsPositive := by
      simpa [hsub_point_eq] using hpoint_psd
    -- Positivity transports from the original direction `d` to the scaled subsegment direction.
    have hnorm_eq :
        ‖y' - x'‖[f; x' + u • (y' - x')] =
          (t - s) * ‖d‖[f; x + (s + u * (t - s)) • d] := by
      calc
      ‖y' - x'‖[f; x' + u • (y' - x')] =
          ‖(t - s) • d‖[f; x + (s + u * (t - s)) • d] := by
            rw [hyx_eq, hsub_point_eq']
      _ = |t - s| * ‖d‖[f; x + (s + u * (t - s)) • d] := by
            rw [hessianLocalNorm_smul_eq_abs_of_isPositive
              (f := f) (z := x + (s + u * (t - s)) • d) (u := d) hpoint_psd']
      _ = (t - s) * ‖d‖[f; x + (s + u * (t - s)) • d] := by
            rw [abs_of_nonneg hts_pos.le]
    rw [hnorm_eq]
    exact mul_pos hts_pos hpoint_pos
  have hbound_sub :
      ∀ {u : ℝ}, u ∈ Set.Icc (0 : ℝ) 1 →
        |thirdDirectionalDerivative f (x' + u • (y' - x')) (y' - x')| /
            (2 * ‖y' - x'‖[f; x' + u • (y' - x')] ^ (3 : ℕ)) ≤
          (Mf : ℝ) := by
    intro u hu
    have hu_param : s + u * (t - s) ∈ Set.Icc s t := by
      constructor <;> nlinarith [hu.1, hu.2, hst]
    have hu01 : s + u * (t - s) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · linarith [hs.1, hu_param.1]
      · linarith [ht.2, hu_param.2]
    have hpoint_segment : x' + u • (y' - x') ∈ segment ℝ x y := by
      rw [hsub_point_eq]
      simpa [d] using segment_point_mem_segment (x := x) (y := y) hu01
    have hpoint_psd :
        (hessian f (x' + u • (y' - x'))).IsPositive :=
      hpsd hpoint_segment
    have hpoint_psd' :
        (hessian f (x + (s + u * (t - s)) • d)).IsPositive := by
      simpa [hsub_point_eq] using hpoint_psd
    have hraw :
        |thirdDirectionalDerivative f (x' + u • (y' - x')) (y' - x')| ≤
          2 * (Mf : ℝ) * ‖y' - x'‖[f; x' + u • (y' - x')] ^ (3 : ℕ) :=
      hthird hpoint_segment (y' - x')
    have hden_pos :
        0 < 2 * ‖y' - x'‖[f; x' + u • (y' - x')] ^ (3 : ℕ) := by
      have hnorm_eq :
          ‖y' - x'‖[f; x' + u • (y' - x')] =
            (t - s) * ‖d‖[f; x + (s + u * (t - s)) • d] := by
        calc
          ‖y' - x'‖[f; x' + u • (y' - x')] =
              ‖(t - s) • d‖[f; x + (s + u * (t - s)) • d] := by
                rw [hyx_eq, hsub_point_eq']
          _ = |t - s| * ‖d‖[f; x + (s + u * (t - s)) • d] := by
                rw [hessianLocalNorm_smul_eq_abs_of_isPositive
                  (f := f) (z := x + (s + u * (t - s)) • d) (u := d) hpoint_psd']
          _ = (t - s) * ‖d‖[f; x + (s + u * (t - s)) • d] := by
                rw [abs_of_nonneg hts_pos.le]
      rw [hnorm_eq]
      have hpoint_pos :
          0 < ‖d‖[f; x + (s + u * (t - s)) • d] := hpos _ hu_param
      have hscale_pos :
          0 < (t - s) * ‖d‖[f; x + (s + u * (t - s)) • d] := by
        exact mul_pos hts_pos hpoint_pos
      have hpow_pos :
          0 < ((t - s) * ‖d‖[f; x + (s + u * (t - s)) • d]) ^ (3 : ℕ) :=
        pow_pos hscale_pos _
      positivity
    -- Divide the pointwise cubic control for the subsegment direction by its positive denominator.
    exact (div_le_iff₀ hden_pos).2 (by simpa [mul_assoc, mul_left_comm, mul_comm] using hraw)
  have hprefix :=
    segmentReciprocalLocalNorm_prefixLowerBound
      (dom := dom) (Mf := Mf) (f := f) (x := x') (y := y')
      hdom_open hcont hsubsegment (s := 1) (by simp) hprefix_sub hbound_sub
  have hx'_psd : (hessian f x').IsPositive := hpsd hx'_segment
  have hy'_psd : (hessian f y').IsPositive := hpsd hy'_segment
  have hs_pos : 0 < ‖d‖[f; x'] := by
    simpa [x', d] using hpos s ⟨le_rfl, hst⟩
  have ht_pos : 0 < ‖d‖[f; y'] := by
    simpa [y', d] using hpos t ⟨hst, le_rfl⟩
  have hs_scale : ‖y' - x'‖[f; x'] = (t - s) * ‖d‖[f; x'] := by
    rw [hyx_eq, hessianLocalNorm_smul_eq_abs_of_isPositive (f := f) (z := x') (u := d) hx'_psd,
      abs_of_nonneg hts_pos.le]
  have ht_scale : ‖y' - x'‖[f; y'] = (t - s) * ‖d‖[f; y'] := by
    rw [hyx_eq, hessianLocalNorm_smul_eq_abs_of_isPositive (f := f) (z := y') (u := d) hy'_psd,
      abs_of_nonneg hts_pos.le]
  have hs_cancel :
      (t - s) * (1 / ((t - s) * ‖d‖[f; x'])) = (‖d‖[f; x'])⁻¹ := by
    field_simp [hts_pos.ne', hs_pos.ne']
  have ht_cancel :
      (t - s) * (1 / ((t - s) * ‖d‖[f; y'])) = (‖d‖[f; y'])⁻¹ := by
    field_simp [hts_pos.ne', ht_pos.ne']
  have hmul :
      (t - s) * (1 / ((t - s) * ‖d‖[f; x']) - (Mf : ℝ)) ≤
        (t - s) * (1 / ((t - s) * ‖d‖[f; y'])) := by
    -- Multiply the subsegment prefix estimate by the positive interval length `t - s`.
    simpa [hs_scale, ht_scale] using mul_le_mul_of_nonneg_left hprefix hts_pos.le
  -- Cancelling the common positive factor recovers the original-direction transport inequality.
  calc
    (‖d‖[f; x'])⁻¹ - (Mf : ℝ) * (t - s)
        = (t - s) * (1 / ((t - s) * ‖d‖[f; x']) - (Mf : ℝ)) := by
            field_simp [hts_pos.ne', hs_pos.ne']
    _ ≤ (t - s) * (1 / ((t - s) * ‖d‖[f; y'])) := hmul
    _ = (‖d‖[f; y'])⁻¹ := ht_cancel

/-- Helper for Theorem 5.1.7: once the weighted scalarized Hessian slices are monotone on
`[0,1]`, evaluating them at `0` and `1` gives the endpoint quadratic-form bounds. -/
private lemma scalarized_hessian_endpoint_bounds_of_weighted_monotonicity
    {a : ℝ} {ψ : ℝ → ℝ}
    (ha_pos : 0 < 1 - a)
    (hmono : MonotoneOn (fun t : ℝ ↦ ψ t / (1 - t * a) ^ (2 : ℕ)) (Set.Icc (0 : ℝ) 1))
    (hanti : AntitoneOn (fun t : ℝ ↦ (1 - t * a) ^ (2 : ℕ) * ψ t) (Set.Icc (0 : ℝ) 1)) :
    ((1 - a) ^ (2 : ℕ)) * ψ 0 ≤ ψ 1 ∧
      ψ 1 ≤ ((1 - a) ^ (2 : ℕ))⁻¹ * ψ 0 := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hmono_eval := hmono (by simp) (by simp) h01
  have hanti_eval := hanti (by simp) (by simp) h01
  constructor
  · -- Compare the increasing weighted reciprocal at the two endpoints.
    have hrewrite :
        ψ 0 ≤ ψ 1 / (1 - a) ^ (2 : ℕ) := by
      simpa using hmono_eval
    have hfactor_pos : 0 < (1 - a) ^ (2 : ℕ) := by positivity
    simpa [mul_comm] using (le_div_iff₀ hfactor_pos).mp hrewrite
  · -- Compare the decreasing weighted direct quantity at the two endpoints.
    have hrewrite :
        (1 - a) ^ (2 : ℕ) * ψ 1 ≤ ψ 0 := by
      simpa using hanti_eval
    have hmul : ψ 1 * (1 - a) ^ (2 : ℕ) ≤ ψ 0 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hrewrite
    simpa [div_eq_mul_inv, mul_comm] using
      (le_div_iff₀ (show 0 < (1 - a) ^ (2 : ℕ) by positivity)).2 hmul

/-- Helper for Theorem 5.1.7: the two-point reciprocal transport inequality globalizes to the
full segment-local norm bound against the exact comparison factor. -/
private lemma segmentDisplacementLocalNorm_transportBound
    {Mf : NNReal} {f : E → ℝ} {x y : E} {z : ℝ → E}
    (hz : z = fun t ↦ x + t • (y - x))
    (hr_lt : ‖y - x‖[f; x] < 1 / (Mf : ℝ))
    (hη_cont : ContinuousOn (fun t ↦ ‖y - x‖[f; z t]) (Set.Icc (0 : ℝ) 1))
    (hrecip_between :
      ∀ {s t : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 → s ≤ t →
        (∀ u ∈ Set.Icc s t, 0 < ‖y - x‖[f; z u]) →
          (‖y - x‖[f; z s])⁻¹ - (Mf : ℝ) * (t - s) ≤
            (‖y - x‖[f; z t])⁻¹) :
    ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) 1 →
      ‖y - x‖[f; z t] ≤
        ‖y - x‖[f; x] / (1 - t * ((Mf : ℝ) * ‖y - x‖[f; x])) := by
  let η : ℝ → ℝ := fun s ↦ ‖y - x‖[f; z s]
  let r : ℝ := ‖y - x‖[f; x]
  let q : ℝ → ℝ := fun s ↦ 1 - s * ((Mf : ℝ) * r)
  let b : ℝ → ℝ := fun s ↦ r / q s
  have hη_nonneg : ∀ s : ℝ, 0 ≤ η s := by
    intro s
    exact hessianLocalNorm_nonneg f (z s) (y - x)
  have hη0 : η 0 = r := by
    subst hz
    simp [η, r]
  have hq_pos : ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 → 0 < q s := by
    intro s hs
    simpa [q, r] using segment_weight_factor_pos (Mf := Mf) (f := f) (x := x) (y := y) hr_lt hs
  have hq_cont : Continuous q := by
    -- Proof comment: the comparison denominator is the affine map `s ↦ 1 - s * ((Mf : ℝ) * r)`.
    simpa [q, r, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm,
      mul_comm] using
      (continuous_const.add (continuous_id.mul continuous_const).neg : Continuous fun s : ℝ ↦
        1 + -(s * ((Mf : ℝ) * r)))
  have hb_cont : ContinuousOn b (Set.Icc (0 : ℝ) 1) := by
    intro s hs
    -- Proof comment: the exact comparison profile is continuous because the affine denominator
    -- stays strictly positive on the whole segment.
    exact
      (continuous_const.continuousAt.div hq_cont.continuousAt
        (by simpa [q] using (hq_pos hs).ne')).continuousWithinAt
  have hF_cont : ContinuousOn (fun s ↦ η s - b s) (Set.Icc (0 : ℝ) 1) := hη_cont.sub hb_cont
  letI : CompactSpace (Set.Icc (0 : ℝ) 1) := isCompact_iff_compactSpace.mp isCompact_Icc
  have hη_sub : Continuous fun u : Set.Icc (0 : ℝ) 1 ↦ η u := by
    simpa [Set.restrict_apply] using
      (continuousOn_iff_continuous_restrict.mp hη_cont)
  have hb_sub : Continuous fun u : Set.Icc (0 : ℝ) 1 ↦ b u := by
    simpa [Set.restrict_apply] using
      (continuousOn_iff_continuous_restrict.mp hb_cont)
  intro t ht
  by_cases hr0 : r = 0
  · -- Proof comment: when the base local norm is zero, the last zero before `t` would force a
    -- contradiction with the reciprocal lower-transport inequality unless the whole segment norm
    -- stays zero up to `t`.
    by_cases hηt0 : η t = 0
    · simp [η, r, b, q, hr0, hηt0]
    have hηt_pos : 0 < η t := lt_of_le_of_ne (hη_nonneg t) (by simpa [eq_comm] using hηt0)
    let Z : Set (Set.Icc (0 : ℝ) 1) := {u | (u : ℝ) ≤ t ∧ η u = 0}
    have hZ_closed : IsClosed Z := by
      -- Proof comment: the zero set on the compact interval is closed, so it has a greatest
      -- element before the positive endpoint witness.
      simpa [Z, Set.setOf_and] using
        (isClosed_le continuous_subtype_val continuous_const).inter
          (isClosed_eq hη_sub continuous_const)
    have hZ_nonempty : Z.Nonempty := by
      refine ⟨⟨0, by simp⟩, ?_⟩
      simpa [Z, hη0, hr0] using ht.1
    obtain ⟨τsub, hτgreatest⟩ :=
      (isCompact_univ.of_isClosed_subset hZ_closed (Set.subset_univ Z)).exists_isGreatest
        hZ_nonempty
    have hτmem : τsub ∈ Z := hτgreatest.1
    have hτmax : ∀ {u : Set.Icc (0 : ℝ) 1}, u ∈ Z → u ≤ τsub := by
      intro u hu
      exact hτgreatest.2 hu
    have hτIcc : (τsub : ℝ) ∈ Set.Icc (0 : ℝ) 1 := τsub.2
    have hτ_le_t : (τsub : ℝ) ≤ t := hτmem.1
    have hητ_zero : η τsub = 0 := hτmem.2
    have hτ_lt_t : (τsub : ℝ) < t := by
      by_contra hnot
      have ht_le_τ : t ≤ τsub := not_lt.mp hnot
      have ht_eq_τ : t = τsub := le_antisymm ht_le_τ hτ_le_t
      exact hηt0 (by simpa [ht_eq_τ] using hητ_zero)
    let A : ℝ := (η t)⁻¹ + (Mf : ℝ) * (t - τsub) + 1
    have hA_pos : 0 < A := by
      have hMf_nonneg : 0 ≤ (Mf : ℝ) := Mf.2
      have h_inv_pos : 0 < (η t)⁻¹ := inv_pos.mpr hηt_pos
      nlinarith
    let κ : ℝ := min (η t / 2) (1 / A)
    have hκ_pos : 0 < κ := by
      refine lt_min ?_ ?_
      · nlinarith
      · exact one_div_pos.mpr hA_pos
    have hκ_lt_ηt : κ < η t := by
      have hhalf_lt : η t / 2 < η t := by nlinarith
      exact lt_of_le_of_lt (min_le_left _ _) hhalf_lt
    have hη_cont_τt : ContinuousOn η (Set.Icc (τsub : ℝ) t) := by
      exact hη_cont.mono fun s hs ↦ ⟨le_trans hτIcc.1 hs.1, le_trans hs.2 ht.2⟩
    have hκ_mem : κ ∈ Set.Icc (η τsub) (η t) := by
      rw [hητ_zero]
      exact ⟨hκ_pos.le, hκ_lt_ηt.le⟩
    obtain ⟨u, huIccτt, huη⟩ :=
      intermediate_value_Icc hτ_le_t hη_cont_τt hκ_mem
    have huIcc : u ∈ Set.Icc (0 : ℝ) 1 := by
      exact ⟨le_trans hτIcc.1 huIccτt.1, le_trans huIccτt.2 ht.2⟩
    have hτ_lt_u : (τsub : ℝ) < u := by
      have hu_ne : u ≠ τsub := by
        intro hu_eq
        exact hκ_pos.ne' <| by simpa [hu_eq, hητ_zero] using huη.symm
      exact lt_of_le_of_ne huIccτt.1 hu_ne.symm
    have hpos_ut : ∀ s ∈ Set.Icc u t, 0 < η s := by
      intro s hs
      have hsIcc : s ∈ Set.Icc (0 : ℝ) 1 := by
        exact ⟨le_trans huIcc.1 hs.1, le_trans hs.2 ht.2⟩
      have hs_nonzero : η s ≠ 0 := by
        intro hs_zero
        have hsZ : (⟨s, hsIcc⟩ : Set.Icc (0 : ℝ) 1) ∈ Z := by
          exact ⟨hs.2, hs_zero⟩
        have hs_le_τ : s ≤ τsub := hτmax hsZ
        exact not_le_of_gt (lt_of_lt_of_le hτ_lt_u hs.1) hs_le_τ
      exact lt_of_le_of_ne (hη_nonneg s) hs_nonzero.symm
    have hrecip : (η u)⁻¹ - (Mf : ℝ) * (t - u) ≤ (η t)⁻¹ := by
      simpa [η] using hrecip_between huIcc ht huIccτt.2 hpos_ut
    have hκ_le_inv : κ ≤ 1 / A := min_le_right _ _
    have hA_le_κinv : A ≤ κ⁻¹ := by
      have htmp : (1 / A)⁻¹ ≤ κ⁻¹ :=
        (inv_le_inv₀ (one_div_pos.mpr hA_pos) hκ_pos).2 hκ_le_inv
      simpa [A, one_div, inv_inv] using htmp
    have : False := by
      rw [huη] at hrecip
      have hA_strict : (η t)⁻¹ + (Mf : ℝ) * (t - u) < A := by
        nlinarith [Mf.2, hτ_lt_u]
      linarith [hA_le_κinv, hA_strict]
    exact False.elim this
  · have hr_pos : 0 < r := by
      have hr_nonneg : 0 ≤ r := by simpa [hη0] using hη_nonneg 0
      exact lt_of_le_of_ne hr_nonneg (by simpa [eq_comm] using hr0)
    by_cases hbad : b t < η t
    · -- Proof comment: if the comparison fails first at `t`, take the greatest equality point
      -- before `t`; the two-point reciprocal bridge then propagates the comparison past that
      -- boundary, contradicting the strict failure at a midpoint.
      let C : Set (Set.Icc (0 : ℝ) 1) := {u | (u : ℝ) ≤ t ∧ η u = b u}
      have hC_closed : IsClosed C := by
        simpa [C, Set.setOf_and] using
          (isClosed_le continuous_subtype_val continuous_const).inter
            (isClosed_eq hη_sub hb_sub)
      have hC_nonempty : C.Nonempty := by
        refine ⟨⟨0, by simp⟩, ?_⟩
        simpa [C, hη0, b, q] using ht.1
      obtain ⟨τsub, hτgreatest⟩ :=
        (isCompact_univ.of_isClosed_subset hC_closed (Set.subset_univ C)).exists_isGreatest
          hC_nonempty
      have hτmem : τsub ∈ C := hτgreatest.1
      have hτmax : ∀ {u : Set.Icc (0 : ℝ) 1}, u ∈ C → u ≤ τsub := by
        intro u hu
        exact hτgreatest.2 hu
      have hτIcc : (τsub : ℝ) ∈ Set.Icc (0 : ℝ) 1 := τsub.2
      have hτ_le_t : (τsub : ℝ) ≤ t := hτmem.1
      have hτ_eq : η τsub = b τsub := hτmem.2
      have hτ_lt_t : (τsub : ℝ) < t := by
        by_contra hnot
        have ht_le_τ : t ≤ τsub := not_lt.mp hnot
        have ht_eq_τ : t = τsub := le_antisymm ht_le_τ hτ_le_t
        have ht_eq_bound : η t = b t := by
          simpa [ht_eq_τ] using hτ_eq
        exact (not_lt_of_ge ht_eq_bound.le hbad).elim
      have hafter :
          ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 → (τsub : ℝ) < s → s ≤ t → b s < η s := by
        intro s hs hτs hst
        by_contra hs_bad
        have hs_le : η s ≤ b s := le_of_not_gt hs_bad
        by_cases hs_eq : η s = b s
        · have hsC : (⟨s, hs⟩ : Set.Icc (0 : ℝ) 1) ∈ C := by
            exact ⟨hst, hs_eq⟩
          have hs_le_τ : s ≤ τsub := hτmax hsC
          exact not_le_of_gt hτs hs_le_τ
        · have hFs_neg : η s - b s < 0 := by
            have hs_lt : η s < b s := lt_of_le_of_ne hs_le (by simpa [eq_comm] using hs_eq)
            linarith
          have hFt_pos : 0 < η t - b t := by linarith
          have hF_cont_st : ContinuousOn (fun u ↦ η u - b u) (Set.Icc s t) := by
            exact hF_cont.mono fun u hu ↦ ⟨le_trans hs.1 hu.1, le_trans hu.2 ht.2⟩
          have hzero_mem : (0 : ℝ) ∈ Set.Icc ((η s - b s)) (η t - b t) := by
            constructor <;> linarith
          obtain ⟨u, huIccst, hu_zero⟩ :=
            intermediate_value_Icc hst hF_cont_st hzero_mem
          have huIcc : u ∈ Set.Icc (0 : ℝ) 1 := by
            exact ⟨le_trans hs.1 huIccst.1, le_trans huIccst.2 ht.2⟩
          have huC : (⟨u, huIcc⟩ : Set.Icc (0 : ℝ) 1) ∈ C := by
            exact ⟨huIccst.2, sub_eq_zero.mp hu_zero⟩
          have hu_le_τ : u ≤ τsub := hτmax huC
          exact not_le_of_gt (lt_of_lt_of_le hτs huIccst.1) hu_le_τ
      let u : ℝ := ((τsub : ℝ) + t) / 2
      have huIcc : u ∈ Set.Icc (0 : ℝ) 1 := by
        constructor <;> dsimp [u] <;> linarith [hτIcc.1, hτIcc.2, ht.1, ht.2, hτ_le_t]
      have hτ_le_u : (τsub : ℝ) ≤ u := by
        dsimp [u]
        linarith
      have hu_le_t : u ≤ t := by
        dsimp [u]
        linarith
      have hτ_lt_u : (τsub : ℝ) < u := by
        dsimp [u]
        linarith
      have hu_bad : b u < η u := hafter huIcc hτ_lt_u hu_le_t
      have hpos_τu : ∀ s ∈ Set.Icc (τsub : ℝ) u, 0 < η s := by
        intro s hs
        have hsIcc : s ∈ Set.Icc (0 : ℝ) 1 := by
          exact ⟨le_trans hτIcc.1 hs.1, le_trans hs.2 huIcc.2⟩
        rcases eq_or_lt_of_le hs.1 with rfl | hτs
        · rw [hτ_eq]
          dsimp [b]
          exact div_pos hr_pos (hq_pos hτIcc)
        · have hs_bad : b s < η s := hafter hsIcc hτs (le_trans hs.2 hu_le_t)
          exact lt_trans (div_pos hr_pos (hq_pos hsIcc)) hs_bad
      have hηu_pos : 0 < η u := hpos_τu u ⟨hτ_le_u, le_rfl⟩
      have hτinv : (η τsub)⁻¹ = q τsub / r := by
        rw [hτ_eq]
        change (r / q τsub)⁻¹ = q τsub / r
        field_simp [hr_pos.ne', (hq_pos hτIcc).ne']
      have hq_rewrite : q τsub / r - (Mf : ℝ) * (u - τsub) = q u / r := by
        field_simp [q, hr_pos.ne']
        ring
      have hupperInv : q u / r ≤ (η u)⁻¹ := by
        have hrecip := hrecip_between hτIcc huIcc hτ_le_u hpos_τu
        rw [hτinv, hq_rewrite] at hrecip
        exact hrecip
      have hru_inv : (r / q u)⁻¹ = q u / r := by
        field_simp [hr_pos.ne', (hq_pos huIcc).ne']
      have hbound : η u ≤ b u := by
        have hupperInv' : (r / q u)⁻¹ ≤ (η u)⁻¹ := by
          rwa [hru_inv]
        change η u ≤ r / q u
        exact (inv_le_inv₀ (div_pos hr_pos (hq_pos huIcc)) hηu_pos).1 hupperInv'
      exact (not_lt_of_ge hbound hu_bad).elim
    · exact le_of_not_gt hbad

/-- Helper for Theorem 5.1.7: once the scalar derivative bounds along the segment are available,
the remaining source-faithful task is to evaluate the weighted monotonicity at the endpoints. -/
private lemma weighted_scalarized_hessian_endpoint_bounds
    {Mf : NNReal} {f : E → ℝ} {x y : E}
    {z : ℝ → E} (hz : z = fun t ↦ x + t • (y - x))
    (hfactor_pos : 0 < 1 - (Mf : ℝ) * ‖y - x‖[f; x])
    (hweighted :
      ∀ v : E,
        let ψ : ℝ → ℝ := fun s ↦ inner ℝ v (hessian f (z s) v);
        MonotoneOn
            (fun t ↦ ψ t / (1 - t * ((Mf : ℝ) * ‖y - x‖[f; x])) ^ (2 : ℕ))
            (Set.Icc (0 : ℝ) 1) ∧
          AntitoneOn
            (fun t ↦ (1 - t * ((Mf : ℝ) * ‖y - x‖[f; x])) ^ (2 : ℕ) * ψ t)
            (Set.Icc (0 : ℝ) 1)) :
    let r := ‖y - x‖[f; x]
    (∀ v : E,
      ((1 - (Mf : ℝ) * r) ^ (2 : ℕ)) * inner ℝ v (hessian f x v) ≤
        inner ℝ v (hessian f y v)) ∧
    (∀ v : E,
      inner ℝ v (hessian f y v) ≤
        ((1 - (Mf : ℝ) * r) ^ (2 : ℕ))⁻¹ * inner ℝ v (hessian f x v)) := by
  let r := ‖y - x‖[f; x]
  let a : ℝ := (Mf : ℝ) * r
  have ha_pos : 0 < 1 - a := by
    simpa [a, r] using hfactor_pos
  subst hz
  constructor
  · intro v
    -- Evaluate the increasing weighted reciprocal slice at the segment endpoints.
    rcases hweighted v with ⟨hmono, hanti⟩
    have hbounds :=
      scalarized_hessian_endpoint_bounds_of_weighted_monotonicity
        (a := a)
        (ψ := fun s ↦ inner ℝ v (hessian f (x + s • (y - x)) v))
        ha_pos hmono hanti
    have hz0 : x + (0 : ℝ) • (y - x) = x := by simp
    have hz1 : x + (1 : ℝ) • (y - x) = y := by
      simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
    simpa [a, r, hz0, hz1] using hbounds.1
  · intro v
    -- Evaluate the decreasing weighted direct slice at the segment endpoints.
    rcases hweighted v with ⟨hmono, hanti⟩
    have hbounds :=
      scalarized_hessian_endpoint_bounds_of_weighted_monotonicity
        (a := a)
        (ψ := fun s ↦ inner ℝ v (hessian f (x + s • (y - x)) v))
        ha_pos hmono hanti
    have hz0 : x + (0 : ℝ) • (y - x) = x := by simp
    have hz1 : x + (1 : ℝ) • (y - x) = y := by
      simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
    simpa [a, r, hz0, hz1] using hbounds.2

/-- Helper for Theorem 5.1.7: once the displacement local norm is globally controlled by the
exact transport factor on `[0,1]`, the weighted scalarized Hessian slices have the monotonicity
needed for endpoint extraction. -/
private lemma weightedScalarizedHessianMonotonicity_of_transport
    {Mf : NNReal} {f : E → ℝ} {x y : E} {z : ℝ → E}
    (hz : z = fun t ↦ x + t • (y - x))
    (hr_lt : ‖y - x‖[f; x] < 1 / (Mf : ℝ))
    (hcont : ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) 1 → ContDiffAt ℝ 3 f (z t))
    (hpsd : ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) 1 → (hessian f (z t)).IsPositive)
    (hpsi_deriv_bounds :
      ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) 1 → ∀ v : E,
        let ψ : ℝ → ℝ := fun s ↦ inner ℝ v (hessian f (z s) v);
        -2 * (Mf : ℝ) * ‖y - x‖[f; z t] * ψ t ≤ deriv ψ t ∧
          deriv ψ t ≤ 2 * (Mf : ℝ) * ‖y - x‖[f; z t] * ψ t)
    (hη_bound :
      ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) 1 →
        ‖y - x‖[f; z t] ≤
          ‖y - x‖[f; x] / (1 - t * ((Mf : ℝ) * ‖y - x‖[f; x]))) :
    ∀ v : E,
      let ψ : ℝ → ℝ := fun s ↦ inner ℝ v (hessian f (z s) v);
      MonotoneOn
          (fun t ↦ ψ t / (1 - t * ((Mf : ℝ) * ‖y - x‖[f; x])) ^ (2 : ℕ))
          (Set.Icc (0 : ℝ) 1) ∧
        AntitoneOn
          (fun t ↦ (1 - t * ((Mf : ℝ) * ‖y - x‖[f; x])) ^ (2 : ℕ) * ψ t)
          (Set.Icc (0 : ℝ) 1) := by
  intro v
  let ψ : ℝ → ℝ := fun s ↦ inner ℝ v (hessian f (z s) v)
  let a : ℝ := (Mf : ℝ) * ‖y - x‖[f; x]
  let q : ℝ → ℝ := fun t ↦ 1 - t * a
  let gUp : ℝ → ℝ := fun t ↦ ψ t / q t ^ (2 : ℕ)
  let gDown : ℝ → ℝ := fun t ↦ q t ^ (2 : ℕ) * ψ t
  have hψ_cont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    -- Proof comment: differentiability of the scalarized Hessian slice gives continuity on the
    -- whole closed interval.
    exact
      (segment_scalarized_hessian_hasDerivAt
        (f := f) (x := x) (y := y) (v := v) (z := z) hz (hcont ht)).continuousAt.continuousWithinAt
  have hq_cont : Continuous q := by
    -- Proof comment: the weight factor is the affine map `t ↦ 1 - t * a`.
    simpa [q, a, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
      mul_assoc] using
      (continuous_const.add (continuous_id.mul continuous_const).neg : Continuous fun t : ℝ ↦
        1 + -(t * a))
  have hgUp_cont : ContinuousOn gUp (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    have hq_pos : 0 < q t := by
      simpa [q, a] using segment_weight_factor_pos (Mf := Mf) (f := f) (x := x) (y := y) hr_lt ht
    -- Proof comment: positivity of the transport factor rules out denominator zeros.
    exact
      (hψ_cont t ht).div ((hq_cont.pow 2).continuousAt.continuousWithinAt)
        (by simpa using hq_pos.ne')
  have hgDown_cont : ContinuousOn gDown (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    -- Proof comment: the direct weighted slice is a product of continuous factors.
    exact ((hq_cont.pow 2).continuousAt.continuousWithinAt).mul (hψ_cont t ht)
  have hmono : MonotoneOn gUp (Set.Icc (0 : ℝ) 1) := by
    refine
      monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) 1)
        (f' := fun t ↦ ((deriv ψ t) * q t + 2 * a * ψ t) / q t ^ (3 : ℕ)) hgUp_cont ?_ ?_
    · intro t ht
      have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := interior_subset ht
      have hq_derivAt : HasDerivAt q (-a) t := by
        simpa [q, a, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
          mul_assoc] using
          (((hasDerivAt_id t).mul_const a).neg.const_add 1)
      have hψ_derivAt : HasDerivAt ψ (deriv ψ t) t := by
        have hψ_base :=
          segment_scalarized_hessian_hasDerivAt
            (f := f) (x := x) (y := y) (v := v) (z := z) hz (hcont htIcc)
        have hψ_deriv :
            deriv ψ t = inner ℝ v ((fderiv ℝ (hessian f) (z t) (y - x)) v) :=
          hψ_base.deriv
        exact hψ_deriv.symm ▸ hψ_base
      have hq_pos : 0 < q t := by
        simpa [q, a] using
          segment_weight_factor_pos (Mf := Mf) (f := f) (x := x) (y := y) hr_lt htIcc
      have hquot :
          HasDerivAt gUp
            (((deriv ψ t) * q t ^ (2 : ℕ) - ψ t * (2 * q t * (-a))) / (q t ^ (2 : ℕ)) ^ (2 : ℕ))
            t := by
        simpa [gUp] using
          hψ_derivAt.div (hq_derivAt.pow 2) (show q t ^ (2 : ℕ) ≠ 0 by positivity)
      -- Proof comment: the quotient-rule coefficient is rewritten into the normalized
      -- `(q * ψ' + 2 a ψ) / q^3` form that matches the differential inequality.
      convert hquot.hasDerivWithinAt using 1
      · have hq_ne : q t ≠ 0 := ne_of_gt hq_pos
        field_simp [hq_ne]
        ring
    · intro t ht
      have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := interior_subset ht
      have hq_pos : 0 < q t := by
        simpa [q, a] using
          segment_weight_factor_pos (Mf := Mf) (f := f) (x := x) (y := y) hr_lt htIcc
      have hψ_nonneg : 0 ≤ ψ t := by
        simpa [ψ] using (hpsd htIcc).inner_nonneg_right v
      rcases hpsi_deriv_bounds htIcc v with ⟨hlower, hupper⟩
      have hη_mul :
          ‖y - x‖[f; z t] * ψ t ≤
            (‖y - x‖[f; x] / q t) * ψ t := by
        exact mul_le_mul_of_nonneg_right (hη_bound htIcc) hψ_nonneg
      have hscale_nonneg : 0 ≤ 2 * (Mf : ℝ) := by positivity
      have hlower' :
          -(2 * (Mf : ℝ) * ((‖y - x‖[f; x] / q t) * ψ t)) ≤ deriv ψ t := by
        have hmul :
            2 * (Mf : ℝ) * (‖y - x‖[f; z t] * ψ t) ≤
              2 * (Mf : ℝ) * ((‖y - x‖[f; x] / q t) * ψ t) :=
          mul_le_mul_of_nonneg_left hη_mul hscale_nonneg
        linarith
      have hmul := mul_le_mul_of_nonneg_right hlower' hq_pos.le
      have hrewrite :
          (-(2 * (Mf : ℝ) * ((‖y - x‖[f; x] / q t) * ψ t))) * q t =
            -(2 * a * ψ t) := by
        have hq_ne : q t ≠ 0 := ne_of_gt hq_pos
        field_simp [a, hq_ne]
        ring
      rw [hrewrite] at hmul
      have hnum_nonneg : 0 ≤ (deriv ψ t) * q t + 2 * a * ψ t := by
        linarith
      have hden_pos : 0 < q t ^ (3 : ℕ) := by positivity
      exact div_nonneg hnum_nonneg hden_pos.le
  have hanti : AntitoneOn gDown (Set.Icc (0 : ℝ) 1) := by
    refine
      antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (0 : ℝ) 1)
        (f' := fun t ↦ q t * (q t * deriv ψ t - 2 * a * ψ t)) hgDown_cont ?_ ?_
    · intro t ht
      have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := interior_subset ht
      have hq_derivAt : HasDerivAt q (-a) t := by
        simpa [q, a, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
          mul_assoc] using
          (((hasDerivAt_id t).mul_const a).neg.const_add 1)
      have hψ_derivAt : HasDerivAt ψ (deriv ψ t) t := by
        have hψ_base :=
          segment_scalarized_hessian_hasDerivAt
            (f := f) (x := x) (y := y) (v := v) (z := z) hz (hcont htIcc)
        have hψ_deriv :
            deriv ψ t = inner ℝ v ((fderiv ℝ (hessian f) (z t) (y - x)) v) :=
          hψ_base.deriv
        exact hψ_deriv.symm ▸ hψ_base
      have hprod :
          HasDerivAt gDown ((2 * q t * (-a)) * ψ t + q t ^ (2 : ℕ) * deriv ψ t) t := by
        simpa [gDown] using (hq_derivAt.pow 2).mul hψ_derivAt
      -- Proof comment: the product-rule coefficient factors as `q * (q * ψ' - 2 a ψ)`.
      convert hprod.hasDerivWithinAt using 1
      · ring
    · intro t ht
      have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := interior_subset ht
      have hq_pos : 0 < q t := by
        simpa [q, a] using segment_weight_factor_pos (Mf := Mf) (f := f) (x := x) (y := y) hr_lt htIcc
      have hψ_nonneg : 0 ≤ ψ t := by
        simpa [ψ] using (hpsd htIcc).inner_nonneg_right v
      rcases hpsi_deriv_bounds htIcc v with ⟨hlower, hupper⟩
      have hη_mul :
          ‖y - x‖[f; z t] * ψ t ≤
            (‖y - x‖[f; x] / q t) * ψ t := by
        exact mul_le_mul_of_nonneg_right (hη_bound htIcc) hψ_nonneg
      have hscale_nonneg : 0 ≤ 2 * (Mf : ℝ) := by positivity
      have hupper' :
          deriv ψ t ≤ 2 * (Mf : ℝ) * ((‖y - x‖[f; x] / q t) * ψ t) := by
        have hmul :
            2 * (Mf : ℝ) * (‖y - x‖[f; z t] * ψ t) ≤
              2 * (Mf : ℝ) * ((‖y - x‖[f; x] / q t) * ψ t) :=
          mul_le_mul_of_nonneg_left hη_mul hscale_nonneg
        exact le_trans (by simpa [mul_assoc] using hupper) hmul
      have hmul := mul_le_mul_of_nonneg_right hupper' hq_pos.le
      have hrewrite :
          (2 * (Mf : ℝ) * ((‖y - x‖[f; x] / q t) * ψ t)) * q t =
            2 * a * ψ t := by
        have hq_ne : q t ≠ 0 := ne_of_gt hq_pos
        field_simp [a, hq_ne]
        ring
      rw [hrewrite] at hmul
      have hinner_nonpos : q t * deriv ψ t - 2 * a * ψ t ≤ 0 := by
        linarith
      exact mul_nonpos_of_nonneg_of_nonpos hq_pos.le hinner_nonpos
  -- Proof comment: the derivative-sign lemmas now feed directly into the endpoint extractor.
  exact ⟨by simpa [gUp, q, ψ], by simpa [gDown, q, ψ] using hanti⟩

/-- Helper for Theorem 5.1.7: the segment ODE argument yields the endpoint quadratic-form bounds
for every test direction. -/
private lemma scalarized_hessian_quadratic_bounds_along_segment
    {dom : Set E} {Mf : NNReal} {f : E → ℝ} {x y : E}
    (hdom_open : IsOpen dom)
    (hcont : ContDiffOn ℝ 3 f dom)
    (hsegment : segment ℝ x y ⊆ dom)
    (hpsd : ∀ ⦃z : E⦄, z ∈ segment ℝ x y → (hessian f z).IsPositive)
    (hthird : ∀ ⦃z : E⦄ (_hz : z ∈ segment ℝ x y) (u : E),
      |thirdDirectionalDerivative f z u| ≤
        2 * (Mf : ℝ) * ‖u‖[f; z] ^ (3 : ℕ))
    (hy : y ∈ W⁰[f; x](1 / (Mf : ℝ))) :
    let r := ‖y - x‖[f; x]
    (∀ v : E,
      ((1 - (Mf : ℝ) * r) ^ (2 : ℕ)) * inner ℝ v (hessian f x v) ≤
        inner ℝ v (hessian f y v)) ∧
    (∀ v : E,
      inner ℝ v (hessian f y v) ≤
        ((1 - (Mf : ℝ) * r) ^ (2 : ℕ))⁻¹ * inner ℝ v (hessian f x v)) := by
  let r := ‖y - x‖[f; x]
  let d := y - x
  let z : ℝ → E := fun t ↦ x + t • d
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using exact_local_radius_lt_inv_constant (f := f) (Mf := Mf) hy
  have hfactor_pos : 0 < 1 - (Mf : ℝ) * r := by
    simpa [r] using exact_local_radius_factor_pos (f := f) (Mf := Mf) hy
  have hxPos : (hessian f x).IsPositive := hpsd (left_mem_segment ℝ x y)
  have hyPos : (hessian f y).IsPositive := hpsd (right_mem_segment ℝ x y)
  have hz_segment : ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) 1 → z t ∈ segment ℝ x y := by
    intro t ht
    simpa [z, d] using segment_point_mem_segment (x := x) (y := y) ht
  have hz_dom : ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) 1 → z t ∈ dom := by
    intro t ht
    exact hsegment (hz_segment ht)
  have hdiag_slice :
      ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) 1 →
        |thirdDirectionalDerivative f (z t) d| /
            (2 * ‖d‖[f; z t] ^ (3 : ℕ)) ≤ (Mf : ℝ) := by
    intro t ht
    simpa [z, d] using
      segment_diagonal_slice_quotient_le
        (f := f) (Mf := Mf) (x := x) (y := y) hthird ht
  have hcont_segment : ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) 1 → ContDiffAt ℝ 3 f (z t) := by
    intro t ht
    exact hcont.contDiffAt (hdom_open.mem_nhds (hz_dom ht))
  have hpsd_segment : ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) 1 → (hessian f (z t)).IsPositive := by
    intro t ht
    exact hpsd (hz_segment ht)
  have hthird_segment :
      ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) 1 → ∀ u : E,
        |thirdDirectionalDerivative f (z t) u| ≤
          2 * (Mf : ℝ) * ‖u‖[f; z t] ^ (3 : ℕ) := by
    intro t ht u
    exact hthird (hz_segment ht) u
  have hpsi_deriv_bounds :
      ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) 1 → ∀ v : E,
        let ψ : ℝ → ℝ := fun s ↦ inner ℝ v (hessian f (z s) v);
        -2 * (Mf : ℝ) * ‖d‖[f; z t] * ψ t ≤ deriv ψ t ∧
          deriv ψ t ≤ 2 * (Mf : ℝ) * ‖d‖[f; z t] * ψ t := by
    intro t ht v
    simpa [d] using
      segment_scalarized_hessian_deriv_bounds
        (Mf := Mf) (f := f) (x := x) (y := y) (z := z) rfl
        hcont_segment hpsd_segment hthird_segment ht v
  -- Route correction: the mixed-slot scalar ODE bound is now isolated as `hpsi_deriv_bounds`.
  -- The remaining source-faithful blocker is the weighted interval argument: build the weighted
  -- monotonicity from `hdiag_slice`, `hpsi_deriv_bounds`, and the missing segment-local norm
  -- transport estimate, then feed it into the endpoint extractor below.
  have _ := hxPos
  have _ := hyPos
  have hweighted :
      ∀ v : E,
        let ψ : ℝ → ℝ := fun s ↦ inner ℝ v (hessian f (z s) v);
        MonotoneOn
            (fun t ↦ ψ t / (1 - t * ((Mf : ℝ) * r)) ^ (2 : ℕ))
            (Set.Icc (0 : ℝ) 1) ∧
          AntitoneOn
            (fun t ↦ (1 - t * ((Mf : ℝ) * r)) ^ (2 : ℕ) * ψ t)
            (Set.Icc (0 : ℝ) 1) := by
    intro v
    have hη_cont : ContinuousOn (fun t ↦ ‖d‖[f; z t]) (Set.Icc (0 : ℝ) 1) := by
      -- The continuation step can now use continuity of the displacement local norm explicitly.
      simpa [d] using
        segmentDisplacementLocalNorm_continuousOn
          (f := f) (x := x) (y := y) (z := z) rfl hcont_segment
    have hrecip_between :
        ∀ {s t : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 → s ≤ t →
          (∀ u ∈ Set.Icc s t, 0 < ‖d‖[f; z u]) →
            (‖d‖[f; z s])⁻¹ - (Mf : ℝ) * (t - s) ≤
              (‖d‖[f; z t])⁻¹ := by
      intro s t hs ht hst hpos
      -- The new two-point bridge removes the rigid dependence on prefixes from `t = 0`.
      simpa [d, z] using
        segmentReciprocalLocalNorm_lowerBound_between
          (dom := dom) (Mf := Mf) (f := f) (x := x) (y := y)
          hdom_open hcont hsegment hpsd hthird hs ht hst hpos
    have hη_bound :
        ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) 1 →
          ‖d‖[f; z t] ≤ r / (1 - t * ((Mf : ℝ) * r)) := by
      -- Proof comment: the local continuity and the two-point reciprocal bridge suffice to
      -- globalize the source transport factor on the whole segment.
      intro t ht
      simpa [d, z, r] using
        segmentDisplacementLocalNorm_transportBound
          (Mf := Mf) (f := f) (x := x) (y := y) (z := z) rfl
          hr_lt hη_cont hrecip_between ht
    -- Route correction: the weighted quotient/product derivative algebra is now factored out.
    -- Only the segment-wide transport estimate `hη_bound` remains to be supplied.
    simpa [d, z, r] using
      weightedScalarizedHessianMonotonicity_of_transport
        (Mf := Mf) (f := f) (x := x) (y := y) (z := z) rfl
        hr_lt hcont_segment hpsd_segment hpsi_deriv_bounds hη_bound v
  simpa [r, d, z] using
    weighted_scalarized_hessian_endpoint_bounds
      (Mf := Mf) (f := f) (x := x) (y := y) (z := z) rfl hfactor_pos
      hweighted

-- Proof sketch: for each fixed direction `h`, scalarize the Hessian operator along the segment by
-- `ψ_h(t) = inner ℝ h (hessian f (x + t • (y - x)) h)`. The diagonal Chapter 5 cubic bound on
-- `thirdDirectionalDerivative` converts, via the standard local bridge to the Hessian
-- differential inequality, into control of `|ψ_h'(t)|` by the local norm of `y - x` at the
-- intermediate point times `ψ_h(t)`. Use the Dikin-radius hypothesis
-- `y ∈ W⁰[f; x](1 / M_f)` together with the standard local norm comparison along
-- the segment to obtain
-- `|ψ_h'(t)| ≤ 2 M_f r / (1 - t M_f r) * ψ_h(t)`, integrate the differential inequality for
-- `log ψ_h(t)`, and then reassemble the resulting pointwise quadratic-form bounds into the
-- Loewner-order comparison of the endpoint Hessians. The Dikin-radius hypothesis already rules
-- out the degenerate `Mf = 0` case, since then `W⁰[f; x](1 / (Mf : ℝ))` is empty.
/-- Theorem 5.1.7: if `f` is `C³` on an open set containing the segment from `x` to `y`, its
third directional derivative satisfies the Chapter 5 local-norm bound with constant `M_f` along
that segment, the Hessian is positive along the segment, and `y ∈ W⁰[f; x](1 / M_f)`, then with
`r = ‖y - x‖[f; x]` the Hessians at `x` and `y` satisfy the Loewner-order bounds
`(1 - M_f r)^2 • ∇²f(x) ≤ ∇²f(y) ≤ (1 - M_f r)⁻² • ∇²f(x)`. -/
theorem hessian_loewner_bounds_along_segment
    {dom : Set E} {Mf : NNReal} {f : E → ℝ} {x y : E}
    (hdom_open : IsOpen dom)
    (hcont : ContDiffOn ℝ 3 f dom)
    (hsegment : segment ℝ x y ⊆ dom)
    (hpsd : ∀ ⦃z : E⦄, z ∈ segment ℝ x y → (hessian f z).IsPositive)
    (hthird : ∀ ⦃z : E⦄ (_hz : z ∈ segment ℝ x y) (u : E),
      |thirdDirectionalDerivative f z u| ≤
        2 * (Mf : ℝ) * ‖u‖[f; z] ^ (3 : ℕ))
    (hy : y ∈ W⁰[f; x](1 / (Mf : ℝ))) :
    let r := ‖y - x‖[f; x]
    ((1 - (Mf : ℝ) * r) ^ (2 : ℕ)) • hessian f x ≤ hessian f y ∧
      hessian f y ≤ ((1 - (Mf : ℝ) * r) ^ (2 : ℕ))⁻¹ • hessian f x := by
  let r := ‖y - x‖[f; x]
  have hxPos : (hessian f x).IsPositive := hpsd (left_mem_segment ℝ x y)
  have hyPos : (hessian f y).IsPositive := hpsd (right_mem_segment ℝ x y)
  -- Reduce the operator comparison to the scalarized quadratic-form bounds at the exact radius.
  have hscalar :
      (∀ v : E,
        ((1 - (Mf : ℝ) * r) ^ (2 : ℕ)) * inner ℝ v (hessian f x v) ≤
          inner ℝ v (hessian f y v)) ∧
      (∀ v : E,
        inner ℝ v (hessian f y v) ≤
          ((1 - (Mf : ℝ) * r) ^ (2 : ℕ))⁻¹ * inner ℝ v (hessian f x v)) := by
    simpa [r] using
      scalarized_hessian_quadratic_bounds_along_segment
        hdom_open hcont hsegment hpsd hthird hy
  rcases hscalar with ⟨hlower, hupper⟩
  -- Reassemble the scalarized bounds into the two Loewner-order inequalities.
  simpa [r] using
    loewner_bounds_of_scalarized_hessian_bounds
      (f := f)
      (x := x)
      (y := y)
      (coeff := ((1 - (Mf : ℝ) * r) ^ (2 : ℕ)))
      hxPos hyPos hlower hupper

end
