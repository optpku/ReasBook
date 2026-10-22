/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The ambient exponential transform attached to a barrier candidate `F` and positive parameter
`p`. -/
def barrierExponentialTransform (p : NNRealˣ) (F : E → ℝ) : E → ℝ :=
  fun x ↦ Real.exp (-F x / (p : ℝ))

/- Lemma 5.3.1 lies in the Chapter 5 self-concordant-barrier / exponential-transform domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantOnWith` and `IsStandardSelfConcordantOn` in `Definition_5_1_1`, the chapter
  owners for self-concordance on an open convex domain;
* `IsSelfConcordantBarrierOnWith` in `Definition_5_3_2`, the chapter owner for a
  `ν`-self-concordant barrier;
* `_root_.barrier_parameter_bound_iff_gradient_inner_sq_le` in `Proposition_5_3_3`, the
  canonical pointwise reformulation of the barrier inequality;
* `isSelfConcordantBarrierOnWith_iff_logarithmic_taylor_lower_bound` in `Theorem_5_3_7`, the
  later source-facing barrier characterization obtained from the same owner.

Best owner abstraction:
* core/canonical: `IsSelfConcordantBarrierOnWith`;
* source-facing: the numbered equivalence between the barrier owner and concavity of the
  exponential transform when the underlying function is already standard self-concordant;
* bridge/view: the ambient exponential-transform owner
  `barrierExponentialTransform p F` together with the owner-level concavity theorem for barrier
  parameters `p ≥ ν`.

Primitive data:
* a domain `dom`;
* a function `F`;
* a barrier parameter `p`;
* the ambient exponential transform `barrierExponentialTransform p F` for `p : NNRealˣ`;
* either the barrier owner `IsSelfConcordantBarrierOnWith dom ν F` or the standard
  self-concordance owner `IsStandardSelfConcordantOn dom F` together with the displayed concavity
  condition.

Derived API:
* concavity of `barrierExponentialTransform p F` for every positive `p ≥ ν`;
* the source-facing equivalence at `p = ν`.

Source/core/bridge triage:
* source-facing: the equivalence in Lemma 5.3.1;
* core/canonical: `IsSelfConcordantBarrierOnWith dom ν F`;
* bridge/view: owner-level concavity of the exponential transform.

This refinement therefore places the auxiliary concavity statement in the barrier owner namespace
and leaves the numbered equivalence as the public source-facing theorem. -/

namespace IsSelfConcordantBarrierOnWith

/-- Helper for Lemma 5.3.1: a `C²` real-valued function on a Hilbert space has a differentiable
gradient at the base point. -/
private theorem differentiableAt_gradient_of_contDiffAt_two
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    DifferentiableAt ℝ (∇ f) x := by
  -- Rewrite the gradient through the inverse Riesz isomorphism and differentiate `fderiv`.
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ f) x := by
    exact
      (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))).differentiableAt
        one_ne_zero
  change DifferentiableAt ℝ (fun y ↦ D (fderiv ℝ f y)) x
  exact (D.hasFDerivAt.comp x hfdiff.hasFDerivAt).differentiableAt

/-- Helper for Lemma 5.3.1: evaluating the barrier expression on a scaled direction produces the
expected scalar quadratic family. -/
private theorem barrier_expression_smul
    {F : E → ℝ} {x u : E} (t : ℝ) :
    2 * inner ℝ (∇ F x) (t • u) - inner ℝ (t • u) (hessian F x (t • u)) =
      2 * t * inner ℝ (∇ F x) u - t ^ (2 : ℕ) * inner ℝ u (hessian F x u) := by
  -- Pull the scalar through the gradient pairing and the Hessian quadratic form.
  simp [inner_smul_left, inner_smul_right, pow_two,
    mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Lemma 5.3.1: a scalar quadratic family bounded above by `μ` forces the
discriminant-style estimate `a² ≤ μ b`. -/
private theorem sq_le_mul_of_barrier_line_family
    {a b μ : ℝ} (hb : 0 ≤ b)
    (hline : ∀ t : ℝ, 2 * t * a - t ^ (2 : ℕ) * b ≤ μ) :
    a ^ (2 : ℕ) ≤ μ * b := by
  by_cases hb0 : b = 0
  · -- When the quadratic term vanishes, the linear family can stay bounded above only if `a = 0`.
    by_cases ha0 : a = 0
    · simp [ha0, hb0]
    · let t : ℝ := (|μ| + 1) / (2 * a)
      have ht_eval : 2 * t * a - t ^ (2 : ℕ) * b = |μ| + 1 := by
        dsimp [t]
        rw [hb0]
        field_simp [ha0]
        ring
      have hbound : |μ| + 1 ≤ μ := by
        simpa [ht_eval] using hline t
      have habs : μ < |μ| + 1 := by
        exact lt_of_le_of_lt (le_abs_self μ) (lt_add_of_pos_right _ zero_lt_one)
      exfalso
      exact (not_le_of_gt habs) hbound
  · have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    have hspecial := hline (a / b)
    have hmul : b * (2 * (a / b) * a - (a / b) ^ (2 : ℕ) * b) ≤ b * μ :=
      mul_le_mul_of_nonneg_left hspecial hb
    have hsimplified : a ^ (2 : ℕ) ≤ b * μ := by
      field_simp [hb_pos.ne'] at hmul
      nlinarith
    simpa [mul_comm] using hsimplified

/-- Helper for Lemma 5.3.1: the squared estimate `a² ≤ μ s²` implies the original affine-quadratic
barrier inequality `2 a - s² ≤ μ`. -/
private theorem barrier_line_of_sq_le_mul
    {a s : ℝ} {μ : NNReal} (_hs : 0 ≤ s)
    (hsq : a ^ (2 : ℕ) ≤ (μ : ℝ) * s ^ (2 : ℕ)) :
    2 * a - s ^ (2 : ℕ) ≤ (μ : ℝ) := by
  -- Compare `4 a²` to `(μ + s²)²` using the nonnegative square `(μ - s²)²`.
  have hμ : 0 ≤ (μ : ℝ) := by
    exact_mod_cast μ.2
  have haux : 4 * a ^ (2 : ℕ) ≤ ((μ : ℝ) + s ^ (2 : ℕ)) ^ (2 : ℕ) := by
    nlinarith [hsq, sq_nonneg ((μ : ℝ) - s ^ (2 : ℕ))]
  have hsum_nonneg : 0 ≤ (μ : ℝ) + s ^ (2 : ℕ) := by
    nlinarith
  nlinarith [haux, hsum_nonneg]

/-- Helper for Lemma 5.3.1: the scalar model `t ↦ -exp (-t / p)` has derivative
`exp (-t / p) / p`. -/
private theorem scalar_neg_exp_neg_div_deriv
    {p : NNRealˣ} {t : ℝ} :
    deriv (fun z : ℝ ↦ -Real.exp (-z / (p : ℝ))) t =
      Real.exp (-t / (p : ℝ)) / (p : ℝ) := by
  -- Differentiate the scalar model by the one-dimensional chain rule.
  have hdiv :
      HasDerivAt (fun z : ℝ ↦ z / (p : ℝ)) (1 / (p : ℝ)) t := by
    simpa [div_eq_mul_inv] using (hasDerivAt_id t).mul_const ((p : ℝ)⁻¹)
  have hneg_div :
      HasDerivAt (fun z : ℝ ↦ -z / (p : ℝ)) (-(1 / (p : ℝ))) t := by
    simpa [div_eq_mul_inv, neg_mul] using hdiv.neg
  have hExp :
      HasDerivAt (fun z : ℝ ↦ Real.exp (-z / (p : ℝ)))
        (Real.exp (-t / (p : ℝ)) * (-(1 / (p : ℝ)))) t := by
    simpa using hneg_div.exp
  have hmodel :
      HasDerivAt (fun z : ℝ ↦ -Real.exp (-z / (p : ℝ)))
        (Real.exp (-t / (p : ℝ)) / (p : ℝ)) t := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hExp.neg
  exact hmodel.deriv

/-- Helper for Lemma 5.3.1: the scalar model `t ↦ -exp (-t / p)` has second derivative
`-exp (-t / p) / p²`. -/
private theorem scalar_neg_exp_neg_div_iteratedDeriv_two
    {p : NNRealˣ} {t : ℝ} :
    iteratedDeriv 2 (fun z : ℝ ↦ -Real.exp (-z / (p : ℝ))) t =
      -(Real.exp (-t / (p : ℝ)) / ((p : ℝ) ^ (2 : ℕ))) := by
  -- Differentiate the explicit first derivative one more time.
  have hderiv_eq :
      deriv (fun z : ℝ ↦ -Real.exp (-z / (p : ℝ))) =
        fun z ↦ Real.exp (-z / (p : ℝ)) / (p : ℝ) := by
    funext z
    exact scalar_neg_exp_neg_div_deriv (p := p) (t := z)
  have hdiv :
      HasDerivAt (fun z : ℝ ↦ z / (p : ℝ)) (1 / (p : ℝ)) t := by
    simpa [div_eq_mul_inv] using (hasDerivAt_id t).mul_const ((p : ℝ)⁻¹)
  have hneg_div :
      HasDerivAt (fun z : ℝ ↦ -z / (p : ℝ)) (-(1 / (p : ℝ))) t := by
    simpa [div_eq_mul_inv, neg_mul] using hdiv.neg
  have hExp :
      HasDerivAt (fun z : ℝ ↦ Real.exp (-z / (p : ℝ)))
        (Real.exp (-t / (p : ℝ)) * (-(1 / (p : ℝ)))) t := by
    simpa using hneg_div.exp
  have hsecond :
      HasDerivAt (fun z : ℝ ↦ Real.exp (-z / (p : ℝ)) / (p : ℝ))
        (-(Real.exp (-t / (p : ℝ)) / ((p : ℝ) ^ (2 : ℕ)))) t := by
    simpa [div_eq_mul_inv, pow_two, mul_comm, mul_left_comm, mul_assoc] using
      hExp.mul_const ((p : ℝ)⁻¹)
  calc
    iteratedDeriv 2 (fun z : ℝ ↦ -Real.exp (-z / (p : ℝ))) t =
        deriv (deriv (fun z : ℝ ↦ -Real.exp (-z / (p : ℝ)))) t := by
          simp [iteratedDeriv_succ]
    _ = deriv (fun z ↦ Real.exp (-z / (p : ℝ)) / (p : ℝ)) t := by
          rw [hderiv_eq]
    _ = -(Real.exp (-t / (p : ℝ)) / ((p : ℝ) ^ (2 : ℕ))) := hsecond.deriv

/-- Helper for Lemma 5.3.1: at a point with positive Hessian, the barrier inequality is
equivalent to the gradient-square estimate against the raw Hessian quadratic form. -/
theorem gradient_sq_le_mul_hessian_iff_barrier_bound
    {F : E → ℝ} {x : E} {μ : NNReal} (hPos : (hessian F x).IsPositive) :
    (∀ u : E,
      2 * inner ℝ (∇ F x) u - inner ℝ u (hessian F x u) ≤ (μ : ℝ)) ↔
      ∀ u : E,
        (inner ℝ (∇ F x) u) ^ (2 : ℕ) ≤
          (μ : ℝ) * inner ℝ u (hessian F x u) := by
  constructor
  · intro hbound u
    -- Evaluate the barrier family on the line `t ↦ x + t u` and apply the scalar discriminant
    -- estimate.
    have hb : 0 ≤ inner ℝ u (hessian F x u) := by
      simpa [real_inner_comm] using hPos.inner_nonneg_right u
    have hline :
        ∀ t : ℝ,
          2 * t * inner ℝ (∇ F x) u - t ^ (2 : ℕ) * inner ℝ u (hessian F x u) ≤ (μ : ℝ) := by
      intro t
      have htu := hbound (t • u)
      rw [barrier_expression_smul] at htu
      exact htu
    simpa using sq_le_mul_of_barrier_line_family hb hline
  · intro hsq u
    -- Recover the original affine-quadratic inequality by rewriting the Hessian term as a square.
    let s : ℝ := Real.sqrt (inner ℝ u (hessian F x u))
    have hs_nonneg : 0 ≤ s := by
      exact Real.sqrt_nonneg _
    have hb : 0 ≤ inner ℝ u (hessian F x u) := by
      simpa [real_inner_comm] using hPos.inner_nonneg_right u
    have hsq' :
        (inner ℝ (∇ F x) u) ^ (2 : ℕ) ≤ (μ : ℝ) * s ^ (2 : ℕ) := by
      simpa [s, Real.sq_sqrt hb] using hsq u
    have hline := barrier_line_of_sq_le_mul hs_nonneg hsq'
    simpa [s, Real.sq_sqrt hb] using hline

/-- Helper for Lemma 5.3.1: if `F` is `C²` at `x`, then the negative exponential transform is
also `C²` at `x`. -/
private theorem contDiffAt_neg_barrier_exponential_transform
    {p : NNRealˣ} {F : E → ℝ} {x : E} (hF2 : ContDiffAt ℝ 2 F x) :
    ContDiffAt ℝ 2 (fun y ↦ -barrierExponentialTransform p F y) x := by
  -- The transform is obtained from `F` by negation, scaling by the constant `1 / p`,
  -- exponentiation, and one final negation.
  simpa [barrierExponentialTransform] using (((hF2.neg.div_const (p : ℝ)).exp).neg)

/-- Helper for Lemma 5.3.1: a `C²` function on `dom` has a `C²` negative exponential transform on
the same domain. -/
private theorem contDiffOn_neg_barrier_exponential_transform
    {dom : Set E} {p : NNRealˣ} {F : E → ℝ} (hF2 : ContDiffOn ℝ 2 F dom) :
    ContDiffOn ℝ 2 (fun y ↦ -barrierExponentialTransform p F y) dom := by
  intro x hx
  -- The pointwise transform rule can be applied at each point of the domain.
  simpa [barrierExponentialTransform] using (((hF2 x hx).neg.div_const (p : ℝ)).exp).neg

/-- Helper for Lemma 5.3.1: the Hessian quadratic form of the negative exponential transform is
the textbook factor `ξ_p(x) / p²` times `p ⟪u, ∇²F(x)u⟫ - ⟪∇F(x), u⟫²`. -/
private theorem neg_barrier_exponential_transform_hessian_quadratic_form
    {p : NNRealˣ} {F : E → ℝ} {x u : E} (hF2 : ContDiffAt ℝ 2 F x) :
    inner ℝ u (hessian (fun y ↦ -barrierExponentialTransform p F y) x u) =
      barrierExponentialTransform p F x / ((p : ℝ) ^ (2 : ℕ)) *
        ((p : ℝ) * inner ℝ u (hessian F x u) - (inner ℝ (∇ F x) u) ^ (2 : ℕ)) := by
  let φ : ℝ → ℝ := directionalSlice F x u
  let G : E → ℝ := fun y ↦ -barrierExponentialTransform p F y
  let g : ℝ → ℝ := fun z ↦ -Real.exp (-z / (p : ℝ))
  have hline2 :
      ContDiffAt ℝ 2 (fun t : ℝ ↦ x + t • u) 0 := by
    simpa using
      (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const) :
        ContDiffAt ℝ 2 (fun t : ℝ ↦ x + t • u) 0)
  have hφ2 : ContDiffAt ℝ 2 φ 0 := by
    -- Restrict `F` to the affine line through `x` in direction `u`.
    have hF2_line : ContDiffAt ℝ 2 F ((fun t : ℝ ↦ x + t • u) 0) := by
      simpa using hF2
    simpa [φ, directionalSlice] using hF2_line.comp 0 hline2
  have hG2 : ContDiffAt ℝ 2 G x :=
    contDiffAt_neg_barrier_exponential_transform hF2
  have hF_diff : DifferentiableAt ℝ F x := by
    exact hF2.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hG_diff : DifferentiableAt ℝ G x := by
    exact hG2.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hF_grad_diff : DifferentiableAt ℝ (∇ F) x :=
    differentiableAt_gradient_of_contDiffAt_two hF2
  have hG_grad_diff : DifferentiableAt ℝ (∇ G) x :=
    differentiableAt_gradient_of_contDiffAt_two hG2
  have hslice_deriv :
      deriv φ 0 = inner ℝ (∇ F x) u := by
    -- The first derivative of the scalar slice is the gradient pairing in direction `u`.
    calc
      deriv φ 0 = lineDeriv ℝ F x u := by
        rfl
      _ = fderiv ℝ F x u := hF_diff.lineDeriv_eq_fderiv
      _ = inner ℝ (∇ F x) u := by
        rw [← inner_gradient_left hF_diff]
  have hslice_second :
      iteratedDeriv 2 φ 0 = inner ℝ u (hessian F x u) := by
    -- The second slice derivative is the Hessian quadratic form.
    simpa [φ, secondDirectionalDerivative] using
      (secondDirectionalDerivative_eq_hessian_quadratic_form
        (f := F) (x := x) (u := u) hF2)
  have hG_slice :
      secondDirectionalDerivative G x u = inner ℝ u (hessian G x u) := by
    simpa [G, secondDirectionalDerivative] using
      (secondDirectionalDerivative_eq_hessian_quadratic_form
        (f := G) (x := x) (u := u) hG2)
  have hg2 :
      ContDiffAt ℝ 2 g (φ 0) := by
    -- The scalar model `z ↦ -exp (-z / p)` is smooth everywhere.
    simpa [g] using
      ((((contDiffAt_id.neg.div_const (p : ℝ)).exp).neg) :
        ContDiffAt ℝ 2 (fun z : ℝ ↦ -Real.exp (-z / (p : ℝ))) (φ 0))
  have hcomp :
      iteratedDeriv 2 (fun t : ℝ ↦ g (φ t)) 0 =
        iteratedDeriv 2 g (φ 0) * deriv φ 0 ^ (2 : ℕ) +
          deriv g (φ 0) * iteratedDeriv 2 φ 0 := by
    simpa using iteratedDeriv_comp_two (g := g) (f := φ) hg2 hφ2
  have hphi0 : φ 0 = F x := by
    simp [φ]
  have hscalar :
      iteratedDeriv 2 (fun t : ℝ ↦ g (φ t)) 0 =
        barrierExponentialTransform p F x / ((p : ℝ) ^ (2 : ℕ)) *
          ((p : ℝ) * inner ℝ u (hessian F x u) - (inner ℝ (∇ F x) u) ^ (2 : ℕ)) := by
    rw [hcomp, scalar_neg_exp_neg_div_iteratedDeriv_two (p := p), scalar_neg_exp_neg_div_deriv]
    rw [hslice_deriv, hslice_second, hphi0]
    -- Rearrange the scalar chain-rule formula into the textbook factorization.
    field_simp [show (p : ℝ) ≠ 0 by exact_mod_cast Units.ne_zero p]
    ring
    have harg : -(F x * (p : ℝ)⁻¹) = -F x / (p : ℝ) := by
      rw [div_eq_mul_inv]
      ring
    simp [harg, barrierExponentialTransform, mul_comm, mul_left_comm, mul_assoc]
  -- Translate the slice identity back to the ambient Hessian quadratic form.
  calc
    inner ℝ u (hessian G x u) = secondDirectionalDerivative G x u := by
      symm
      exact hG_slice
    _ = iteratedDeriv 2 (fun t : ℝ ↦ g (φ t)) 0 := by
      rfl
    _ = barrierExponentialTransform p F x / ((p : ℝ) ^ (2 : ℕ)) *
          ((p : ℝ) * inner ℝ u (hessian F x u) - (inner ℝ (∇ F x) u) ^ (2 : ℕ)) := hscalar

/-- Helper for Lemma 5.3.1: concavity of `ξ_p` implies the pointwise estimate
`⟪∇F(x), u⟫² ≤ p ⟪u, ∇²F(x)u⟫`. -/
theorem gradient_sq_le_mul_hessian_of_concave_barrier_exponential_transform
    {dom : Set E} {p : NNRealˣ} {F : E → ℝ}
    (hFsc : IsStandardSelfConcordantOn dom F) {x : E} (hx : x ∈ dom)
    (hconc : ConcaveOn ℝ dom (barrierExponentialTransform p F)) :
    ∀ u : E,
      (inner ℝ (∇ F x) u) ^ (2 : ℕ) ≤ (p : ℝ) * inner ℝ u (hessian F x u) := by
  intro u
  have hconv :
      ConvexOn ℝ dom (fun y ↦ -barrierExponentialTransform p F y) := by
    -- Negating a concave function produces a convex one on the same domain.
    exact neg_convexOn_iff.mpr hconc
  have hF2 :
      ContDiffOn ℝ 2 F dom := hFsc.contDiffOn.of_le (by norm_num)
  have hG2 :
      ContDiffOn ℝ 2 (fun y ↦ -barrierExponentialTransform p F y) dom :=
    contDiffOn_neg_barrier_exponential_transform hF2
  have hquad_nonneg :
      0 ≤ inner ℝ u (hessian (fun y ↦ -barrierExponentialTransform p F y) x u) := by
    simpa [real_inner_comm] using
      ((convexOn_iff_hessian_quadratic_form_nonneg hFsc.isOpen_domain hFsc.convex_domain hG2).1
        hconv) x hx u
  rw [neg_barrier_exponential_transform_hessian_quadratic_form
    (p := p) (F := F) (x := x) (u := u) (hF2 := hF2.contDiffAt (hFsc.isOpen_domain.mem_nhds hx))]
    at hquad_nonneg
  have hfactor_pos :
      0 < barrierExponentialTransform p F x / ((p : ℝ) ^ (2 : ℕ)) := by
    have hnum : 0 < barrierExponentialTransform p F x := by
      dsimp [barrierExponentialTransform]
      positivity
    have hp_pos : 0 < (p : NNReal) := by
      exact pos_iff_ne_zero.mpr (Units.ne_zero p)
    have hp_pos_real : 0 < (p : ℝ) := by
      exact_mod_cast hp_pos
    have hden : 0 < ((p : ℝ) ^ (2 : ℕ)) := by
      nlinarith
    exact div_pos hnum hden
  have hbracket_nonneg :
      0 ≤ (p : ℝ) * inner ℝ u (hessian F x u) - (inner ℝ (∇ F x) u) ^ (2 : ℕ) := by
    exact (mul_nonneg_iff_of_pos_left hfactor_pos).mp hquad_nonneg
  linarith

-- Proof sketch: compute the Hessian quadratic form of `x ↦ exp (-(F x / p))`; the displayed
-- formula in the text shows that concavity follows from the barrier inequality with parameter
-- `ν`, and if `p ≥ ν` then the same estimate remains valid with `p` in place of `ν`.
/-- If `F` is a `ν`-self-concordant barrier on `dom`, then every exponential transform
`x ↦ exp (-(F x / p))` with positive `p ≥ ν` is concave on `dom`. This is the owner-level concavity
companion to Lemma `5.3.1`. -/
theorem concaveOn_exp_neg_div
    {dom : Set E} {ν : NNReal} {p : NNRealˣ} {F : E → ℝ}
    (hF : IsSelfConcordantBarrierOnWith dom ν F) (hνp : ν ≤ (p : NNReal)) :
    ConcaveOn ℝ dom (barrierExponentialTransform p F) := by
  let hstd : IsStandardSelfConcordantOn dom F := hF.toIsStandardSelfConcordantOn
  have hF2 : ContDiffOn ℝ 2 F dom := hstd.contDiffOn.of_le (by norm_num)
  have hG2 :
      ContDiffOn ℝ 2 (fun y ↦ -barrierExponentialTransform p F y) dom :=
    contDiffOn_neg_barrier_exponential_transform hF2
  have hconv_neg :
      ConvexOn ℝ dom (fun y ↦ -barrierExponentialTransform p F y) := by
    refine
      (convexOn_iff_hessian_quadratic_form_nonneg hstd.isOpen_domain hstd.convex_domain hG2).2 ?_
    intro x hx u
    -- Promote the barrier inequality from parameter `ν` to parameter `p` inside the Hessian
    -- factorization of the negative exponential transform.
    have hPos : (hessian F x).IsPositive := hstd.hessian_isPositive hx
    have hsq_ν :
        (inner ℝ (∇ F x) u) ^ (2 : ℕ) ≤
          (ν : ℝ) * inner ℝ u (hessian F x u) := by
      exact
        (gradient_sq_le_mul_hessian_iff_barrier_bound (F := F) (x := x) (μ := ν) hPos).1
          (fun v ↦ hF.barrier_parameter_bound hx v) u
    have hquad_nonneg : 0 ≤ inner ℝ u (hessian F x u) := hstd.hessian_posSemidef hx u
    have hνp' : (ν : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast hνp
    have hsq_p :
        (inner ℝ (∇ F x) u) ^ (2 : ℕ) ≤
          (p : ℝ) * inner ℝ u (hessian F x u) := by
      nlinarith
    have hbracket_nonneg :
        0 ≤ (p : ℝ) * inner ℝ u (hessian F x u) - (inner ℝ (∇ F x) u) ^ (2 : ℕ) := by
      linarith
    have hfactor_nonneg :
        0 ≤ barrierExponentialTransform p F x / ((p : ℝ) ^ (2 : ℕ)) := by
      dsimp [barrierExponentialTransform]
      positivity
    have hquad_target :
        0 ≤ inner ℝ u (hessian (fun y ↦ -barrierExponentialTransform p F y) x u) := by
      rw [neg_barrier_exponential_transform_hessian_quadratic_form
        (p := p) (F := F) (x := x) (u := u)
        (hF2 := hF2.contDiffAt (hstd.isOpen_domain.mem_nhds hx))]
      exact mul_nonneg hfactor_nonneg hbracket_nonneg
    simpa [real_inner_comm] using hquad_target
  -- Negating back turns convexity of `-ξ_p` into concavity of `ξ_p`.
  exact neg_convexOn_iff.mp hconv_neg

end IsSelfConcordantBarrierOnWith

-- Proof sketch: for the forward implication, specialize the Hessian computation of
-- `x ↦ exp (-(F x / ν))` and rewrite the concavity condition as the barrier inequality from
-- Definition 5.3.2. For the reverse implication, the same computation turns concavity of
-- `x ↦ exp (-(F x / ν))` into the barrier-parameter bound, while the standard self-concordance
-- assumption supplies the remaining part of the barrier structure. The positivity hypothesis on
-- `ν` is essential, because the owner-level transform in the auxiliary API is only defined for a
-- positive parameter, but the numbered equivalence is stated directly with the textbook function
-- `x ↦ exp (-(F x / ν))`.
/-- Lemma 5.3.1: for a standard self-concordant function `F` on `dom` and a positive barrier
parameter `ν`, being a `ν`-self-concordant barrier is equivalent to concavity of the exponential
transform `x ↦ exp (-(F x / ν))` on `dom`. -/
theorem isSelfConcordantBarrierOnWith_iff_concaveOn_exp_neg_div
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    (hFsc : IsStandardSelfConcordantOn dom F) (hν : 0 < (ν : ℝ)) :
    IsSelfConcordantBarrierOnWith dom ν F ↔
      ConcaveOn ℝ dom (fun x ↦ Real.exp (-(F x / (ν : ℝ)))) := by
  let νu : NNRealˣ := Units.mk0 ν (by exact_mod_cast ne_of_gt hν)
  constructor
  · intro hF
    -- Specialize the owner-level theorem to the positive unit `νu`.
    have hνu_val : ((νu : NNReal) : ℝ) = (ν : ℝ) := by
      simp [νu]
    have htransform_eq :
        barrierExponentialTransform νu F =
          fun x ↦ Real.exp (-(F x / (((νu : NNReal)) : ℝ))) := by
      funext x
      simp [barrierExponentialTransform, neg_div]
    have hconc :
        ConcaveOn ℝ dom (barrierExponentialTransform νu F) :=
      hF.concaveOn_exp_neg_div (show ν ≤ (νu : NNReal) by simp [νu])
    have hconc_text :
        ConcaveOn ℝ dom (fun x ↦ Real.exp (-(F x / (((νu : NNReal)) : ℝ)))) := by
      simpa [htransform_eq] using hconc
    simpa [hνu_val] using hconc_text
  · intro hconc
    have hνu_val : ((νu : NNReal) : ℝ) = (ν : ℝ) := by
      simp [νu]
    have htransform_eq :
        barrierExponentialTransform νu F =
          fun x ↦ Real.exp (-(F x / (((νu : NNReal)) : ℝ))) := by
      funext x
      simp [barrierExponentialTransform, neg_div]
    have hconc_text :
        ConcaveOn ℝ dom (fun x ↦ Real.exp (-(F x / (((νu : NNReal)) : ℝ)))) := by
      simpa [hνu_val] using hconc
    have hconc_u :
        ConcaveOn ℝ dom (barrierExponentialTransform νu F) := by
      simpa [htransform_eq] using hconc_text
    refine
      { toIsStandardSelfConcordantOn := hFsc
        barrier_parameter_bound := ?_ }
    intro x hx u
    -- Recover the barrier inequality from concavity by passing through the gradient-square bound.
    have hsq_u :
        ∀ v : E,
          (inner ℝ (∇ F x) v) ^ (2 : ℕ) ≤
            (ν : ℝ) * inner ℝ v (hessian F x v) := by
      intro v
      simpa [νu] using
        (IsSelfConcordantBarrierOnWith.gradient_sq_le_mul_hessian_of_concave_barrier_exponential_transform
          (dom := dom) (p := νu) (F := F) hFsc hx hconc_u v)
    exact
      (IsSelfConcordantBarrierOnWith.gradient_sq_le_mul_hessian_iff_barrier_bound
        (F := F) (x := x) (μ := ν) (hFsc.hessian_isPositive hx)).2 hsq_u u

end
