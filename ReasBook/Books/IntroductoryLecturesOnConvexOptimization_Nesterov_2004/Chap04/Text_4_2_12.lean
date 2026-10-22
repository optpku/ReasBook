/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Algorithm_1_7_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Lemma_1_5_11
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_15
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient
open NewtonSystem (AdmissiblePoint step)

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Text 4.2.12 lies in the real-Hilbert-space Newton / Hessian-Lipschitz domain.

Sampled owner declarations:
* `StrongConvexOn` in `Chap03/Definition_3_2_2`, the chapter owner for whole-space strong
  convexity
* `strongConvexOn_iff_hessian_lower_bound` in `Chap02/Definition_2_15`, the chapter bridge from
  the textbook Hessian quadratic-form lower bound to `StrongConvexOn`
* `NewtonSystem.AdmissiblePoint` and `NewtonSystem.step` in `Chap01/Algorithm_1_7_1`, the owner
  Newton domain and update for the stationarity system `∇ f = 0`
* `HasLipschitzContinuousHessian L3 f` and the notation `f ∈ C22[L3]` in `Definition_4_2_7`,
  the chapter owner for `C²` regularity plus global Hessian-Lipschitz control

Source/core/bridge triage:
* source-facing: the quadratic-gradient threshold region and the resulting Newton-step estimate
  from Text 4.2.12
* core/canonical: `StrongConvexOn Set.univ σ2 f`, `NewtonSystem.AdmissiblePoint (∇ f)`,
  `NewtonSystem.step (∇ f)`, and `f ∈ C22[L3]`
* bridge/view: the admissibility bridge from whole-space strong convexity plus `C²` regularity to
  `AdmissiblePoint (∇ f)`, while the quadratic-decrease estimate itself still uses `f ∈ C22[L3]`

Primitive data:
* a modulus `σ2`
* a Hessian-Lipschitz constant `L3`
* a function `f`
* the owner hypotheses `StrongConvexOn Set.univ σ2 f` and `f ∈ C22[L3]`
* for the admissibility bridge only, the weaker `C²` datum supplied by `hf_hessian.contDiff`

Derived API:
* the admissible-point witness for the Newton system `∇ f = 0`, exposed at the weaker
  strong-convexity-plus-`C²` layer
* the canonical Newton update `NewtonSystem.step (∇ f)`
* the quadratic-gradient threshold region and the decrease estimate on that region

The previous file introduced a second public owner for the Hessian lower bound and rebuilt the
Newton step from a local inverse-Hessian equivalence. This refinement keeps the source-facing
threshold region, states the main result directly on the canonical strong-convexity and
Newton-system owners, and keeps the admissibility bridge at the weaker `C²` layer needed for
Hessian nondegeneracy rather than at the full `C22[L3]` layer. -/

/-- The gradient-based threshold region `𝒬_g` from Text 4.2.12, written in multiplication form so
that the degenerate case `L₃ = 0` still gives the intended whole-space threshold. -/
def quadraticGradientRegion
    (f : E → ℝ) (σ2 : ℝ) (L3 : NNReal) : Set E :=
  {x | 4 * (L3 : ℝ) * ‖∇ f x‖ ≤ σ2 ^ (2 : ℕ)}

-- Proof sketch: unfold `quadraticGradientRegion`.
/-- Membership in `quadraticGradientRegion f σ₂ L₃` is exactly the threshold inequality
`4 L₃ ‖∇ f(x)‖ ≤ σ₂²`. -/
theorem mem_quadraticGradientRegion_iff
    {f : E → ℝ} {σ2 : ℝ} {L3 : NNReal} {x : E} :
    x ∈ quadraticGradientRegion f σ2 L3 ↔
      4 * (L3 : ℝ) * ‖∇ f x‖ ≤ σ2 ^ (2 : ℕ) :=
  Iff.rfl

section

variable [FiniteDimensional ℝ E]

namespace StrongConvexOn

omit [FiniteDimensional ℝ E] in
/-- Helper for Text 4 2 12: whole-space strong convexity forces each Hessian to expand norms by
at least the strong-convexity modulus. -/
private theorem hessian_apply_norm_ge_sigma_mul_norm
    {σ2 : ℝ} {f : E → ℝ}
    (hf : StrongConvexOn Set.univ σ2 f) (hσ2 : 0 < σ2)
    (hf_C2 : ContDiff ℝ 2 f) (x u : E) :
    σ2 * ‖u‖ ≤ ‖(fderiv ℝ (∇ f) x) u‖ := by
  have hbound :
      σ2 • (1 : E →L[ℝ] E) ≤ hessian f x := by
    -- Specialize the Chapter 2 Hessian bridge to `Set.univ`.
    have hiff :=
      (strongConvexOn_iff_hessian_lower_bound
        (E := E) (μ := σ2) (Q := Set.univ) (f := f)
        hσ2 convex_univ
        (by simp)
        hf_C2.continuous.continuousOn
        (by simpa using hf_C2.contDiffOn)).1 hf
    simpa using hiff x (by simp)
  have hquad :
      σ2 * ‖u‖ ^ (2 : ℕ) ≤ inner ℝ (hessian f x u) u := by
    -- Convert the Loewner lower bound into the corresponding quadratic-form inequality.
    exact
      (hessian_loewner_lower_bound_iff_quadratic_form_lower_bound
        (Q := Set.univ) (f := f) hσ2 (by simpa using hf_C2.contDiffOn)
        (x := x) (by simp)).1 hbound u
  by_cases hu : u = 0
  · simp [hu]
  -- For nonzero `u`, combine the quadratic-form lower bound with Cauchy-Schwarz and cancel `‖u‖`.
  · have hinner_le : inner ℝ (hessian f x u) u ≤ ‖hessian f x u‖ * ‖u‖ := by
      exact le_trans (le_abs_self _) <| by
        simpa [real_inner_comm] using abs_real_inner_le_norm (hessian f x u) u
    have hmul : σ2 * ‖u‖ ^ (2 : ℕ) ≤ ‖hessian f x u‖ * ‖u‖ := le_trans hquad hinner_le
    have hu_norm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hmul' : σ2 * ‖u‖ * ‖u‖ ≤ ‖hessian f x u‖ * ‖u‖ := by
      simpa [pow_two, mul_assoc] using hmul
    have hdiv := (mul_le_mul_iff_of_pos_right hu_norm_pos).mp hmul'
    simpa [hessian] using hdiv

private theorem gradient_det_ne_zero
    {σ2 : ℝ} {f : E → ℝ}
    (hf : StrongConvexOn Set.univ σ2 f) (hσ2 : 0 < σ2)
    (hf_C2 : ContDiff ℝ 2 f) (x : E) :
    (fderiv ℝ (∇ f) x).det ≠ 0 := by
  -- A nonzero kernel vector would contradict the Hessian norm lower bound.
  rw [ne_eq, LinearMap.det_eq_zero_iff_ker_ne_bot]
  intro hker
  obtain ⟨u, hu_mem, hu_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hu_zero : (fderiv ℝ (∇ f) x) u = 0 := hu_mem
  have hnorm_le : σ2 * ‖u‖ ≤ 0 := by
    simpa [hu_zero] using hf.hessian_apply_norm_ge_sigma_mul_norm hσ2 hf_C2 x u
  have hprod_pos : 0 < σ2 * ‖u‖ := by
    positivity
  linarith

/-- Whole-space strong convexity and `C²` regularity canonically place every point in the
admissible Newton domain for the stationarity system `∇ f = 0`. -/
abbrev admissiblePoint
    {σ2 : ℝ} {f : E → ℝ}
    (hf : StrongConvexOn Set.univ σ2 f) (hσ2 : 0 < σ2)
    (hf_C2 : ContDiff ℝ 2 f) (x : E) :
    AdmissiblePoint (∇ f) :=
  ⟨x, hf.gradient_det_ne_zero hσ2 hf_C2 x⟩

/-- Helper for Text 4 2 12: the canonical Newton step solves the linearized stationarity equation
at the base point. -/
private theorem step_linearization_eq_neg_gradient
    {σ2 : ℝ} {f : E → ℝ}
    (hf : StrongConvexOn Set.univ σ2 f) (hσ2 : 0 < σ2)
    (hf_C2 : ContDiff ℝ 2 f) (x : E) :
    (fderiv ℝ (∇ f) x)
      (step (∇ f) (hf.admissiblePoint hσ2 hf_C2 x) - x) = - ∇ f x := by
  let p : AdmissiblePoint (∇ f) := hf.admissiblePoint hσ2 hf_C2 x
  let A : E →L[ℝ] E := fderiv ℝ (∇ f) x
  let e := A.toContinuousLinearEquivOfDetNeZero p.property
  have hstep :
      step (∇ f) p - x = - e.symm (∇ f x) := by
    -- Expand the Newton update and cancel the base point.
    simp [NewtonSystem.step_def, p, A, e, sub_eq_add_neg, add_left_comm, add_comm]
  -- Applying the linearization recovers the negative gradient exactly.
  calc
    (fderiv ℝ (∇ f) x) (step (∇ f) p - x)
      = A (-e.symm (∇ f x)) := by simpa [A] using congrArg A hstep
    _ = -A (e.symm (∇ f x)) := by simp
    _ = -∇ f x := by
      -- The inverse equivalence evaluates back to the original gradient vector.
      have he_apply : A (e.symm (∇ f x)) = ∇ f x :=
        e.apply_symm_apply (∇ f x)
      rw [he_apply]

-- Proof sketch: fix `x` in the threshold region, write the Newton step as
-- `T = NewtonSystem.step (∇ f) x`, use the integral Hessian remainder formula together with the
-- `L₃`-Lipschitz bound on `x ↦ ∇² f(x)` to estimate `‖∇ f(T)‖`, and use strong convexity to
-- control the inverse Hessian norm by `σ₂⁻¹`.
/-- Text 4 2 12: if `f ∈ C22[L₃]` is `σ₂`-strongly convex on `Set.univ`, then every point `x`
in the threshold region `𝒬_g = {x : 4 L₃ ‖∇ f(x)‖ ≤ σ₂²}` satisfies the quadratic gradient
decrease estimate
`‖∇ f(T(x))‖ ≤ (4 L₃ / σ₂²) ‖∇ f(x)‖²`
for the canonical Newton step `T(x) = NewtonSystem.step (∇ f) x` at the admissible point
supplied by `hf.admissiblePoint hσ₂ hf_hessian.contDiff x`. Under `f ∈ C22[L₃]`, this is the
canonical-owner reformulation of the textbook Hessian-lower-bound statement from
Definition 2.15. In this Hilbert-space formalization the textbook dual norm is identified with
the ambient norm. -/
theorem gradient_norm_newton_step_quadratic_decrease_on_region
    {σ2 : ℝ} {L3 : NNReal} {f : E → ℝ}
    (hf : StrongConvexOn Set.univ σ2 f) (hσ2 : 0 < σ2)
    (hf_hessian : f ∈ C22[L3])
    (x : E) (hx : x ∈ quadraticGradientRegion f σ2 L3) :
    ‖∇ f (step (∇ f) (hf.admissiblePoint hσ2 hf_hessian.contDiff x))‖ ≤
      (4 * (L3 : ℝ) / σ2 ^ (2 : ℕ)) * ‖∇ f x‖ ^ (2 : ℕ) := by
  let p : AdmissiblePoint (∇ f) := hf.admissiblePoint hσ2 hf_hessian.contDiff x
  let T : E := step (∇ f) p
  have hstep_lin : hessian f x (T - x) = -∇ f x := by
    -- The Newton correction exactly cancels the linearized gradient.
    simpa [hessian, T, p] using hf.step_linearization_eq_neg_gradient hσ2 hf_hessian.contDiff x
  have hdeviation := HasLipschitzContinuousHessian.gradient_deviation_le hf_hessian x T
  have hgrad_le : ‖∇ f T‖ ≤ ((L3 : ℝ) / 2) * ‖T - x‖ ^ (2 : ℕ) := by
    -- Rewrite the Chapter 1 Taylor remainder bound using the Newton cancellation identity.
    calc
      ‖∇ f T‖ = ‖∇ f T - ∇ f x - hessian f x (T - x)‖ := by
        rw [hstep_lin]
        simp
      _ ≤ ((L3 : ℝ) / 2) * ‖T - x‖ ^ (2 : ℕ) := hdeviation
  have hstep_norm : σ2 * ‖T - x‖ ≤ ‖∇ f x‖ := by
    -- Strong convexity bounds the Newton displacement by the inverse Hessian margin.
    calc
      σ2 * ‖T - x‖ ≤ ‖hessian f x (T - x)‖ := by
        simpa [hessian] using
          hf.hessian_apply_norm_ge_sigma_mul_norm hσ2 hf_hessian.contDiff x (T - x)
      _ = ‖∇ f x‖ := by rw [hstep_lin]; simp
  have hstep_dist : ‖T - x‖ ≤ ‖∇ f x‖ / σ2 := by
    exact (le_div_iff₀ hσ2).2 (by simpa [mul_assoc, mul_left_comm, mul_comm] using hstep_norm)
  have hstrong :
      ‖∇ f T‖ ≤ (((L3 : ℝ) / 2) / σ2 ^ (2 : ℕ)) * ‖∇ f x‖ ^ (2 : ℕ) := by
    have hσ2_ne : σ2 ≠ 0 := ne_of_gt hσ2
    calc
      ‖∇ f T‖ ≤ ((L3 : ℝ) / 2) * ‖T - x‖ ^ (2 : ℕ) := hgrad_le
      _ ≤ ((L3 : ℝ) / 2) * (‖∇ f x‖ / σ2) ^ (2 : ℕ) := by
          gcongr
      _ = ((L3 : ℝ) / 2) * (‖∇ f x‖ ^ (2 : ℕ) / σ2 ^ (2 : ℕ)) := by
          rw [div_pow]
      _ = (((L3 : ℝ) / 2) / σ2 ^ (2 : ℕ)) * ‖∇ f x‖ ^ (2 : ℕ) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ring
  have hL3_nonneg : 0 ≤ (L3 : ℝ) := by
    exact_mod_cast L3.2
  have hσ2sq_pos : 0 < σ2 ^ (2 : ℕ) := by
    positivity
  have hcoeff :
      (((L3 : ℝ) / 2) / σ2 ^ (2 : ℕ)) ≤ (4 * (L3 : ℝ) / σ2 ^ (2 : ℕ)) := by
    -- The direct Newton remainder estimate is stronger than the textbook coefficient.
    rw [div_le_div_iff_of_pos_right hσ2sq_pos]
    nlinarith
  -- The source threshold hypothesis is surface data here; the direct estimate is already stronger.
  have _ := hx
  -- Return from the local abbreviation `T` to the theorem surface after comparing constants.
  simpa [T, p] using
    (calc
      ‖∇ f T‖ ≤ (((L3 : ℝ) / 2) / σ2 ^ (2 : ℕ)) * ‖∇ f x‖ ^ (2 : ℕ) := hstrong
      _ ≤ (4 * (L3 : ℝ) / σ2 ^ (2 : ℕ)) * ‖∇ f x‖ ^ (2 : ℕ) := by
        gcongr
      _ = (4 * (L3 : ℝ) / σ2 ^ (2 : ℕ)) * ‖∇ f x‖ ^ (2 : ℕ) := rfl)

end StrongConvexOn

end
