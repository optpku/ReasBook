/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Lemma_4_1_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Lemma_4_1_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient CubicRegularizationModelNotation

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section

variable {L3 : NNReal} {f : E → ℝ} {M : ℝ} {x T : E}

/- Text 4.2.8 lies in the cubic-regularization / second-order smooth optimization domain on real
Hilbert spaces.

Sampled owner-style declarations:
* `cubicRegularizationQuadraticApproximation` in `Definition_4_1_3`, the chapter owner for the
  cubic model;
* `gradient_norm_le_of_isMinOn_cubicRegularizationQuadraticApproximation` in `Lemma_4_1_4`, the
  owner-level gradient estimate for cubic-model minimizers;
* `objective_sub_cubicRegularizationValue_ge_residual_cube` in `Lemma_4_1_5`, the owner-level
  lower bound on `f x - \bar f_M(x)`;
* `objective_cubicTrialPoint_le_cubicRegularizationValue_of_le_hessianLipschitz` in
  `Lemma_4_1_5`, the bridge comparing a minimizing trial point with `\bar f_M(x)`.

Best owner abstraction:
* the chapter cubic-model owner `m[f; M](x)`
* the owner theorem
  `gradient_norm_le_of_isMinOn_cubicRegularizationQuadraticApproximation`
* the owner value `cubicRegularizationValue f M x`

Primitive data:
* for the recall item, no new primitive data beyond the imported owner theorem;
* for the new source-facing estimate, the cubic model
  `m[f; M](x)`, a global minimizer witness
  `hT : IsMinOn (m[f; M](x)) Set.univ T`, and the owner
  hypotheses `hf : f ∈ C22[L3]`, `hf_conv : ConvexOn ℝ Set.univ f`, and `hML : (L3 : ℝ) ≤ M`

Derived API:
* the direct recall of Text 4.2.8 (1) from `Lemma_4_1_4`
* the objective decrease estimate under convexity and `M ≥ L3`

Source/core/bridge triage:
* source-facing: Text 4.2.8 (2)
* core/canonical: `m[f; M](x)`, `cubicRegularizationValue`, and the owner theorem from
  `Lemma_4_1_4`
* bridge/view: specializing those owners to a global minimizer `T`

The previous version duplicated the Chapter 4 owner theorem
`gradient_norm_le_of_isMinOn_cubicRegularizationQuadraticApproximation` and even strengthened its
assumptions from `0 ≤ M` to `0 < M`. This refinement removes that duplicate wheel: part (1) is a
pure recall, while part (2) remains the only fresh source-facing declaration in this file. -/

/- Text 4.2.8 (1) is the direct Chapter 4 recall of the owner theorem from `Lemma_4_1_4`; this
file keeps no parallel local theorem shell. -/
recall gradient_norm_le_of_isMinOn_cubicRegularizationQuadraticApproximation

-- Proof sketch: compare `f T` with `m[f; M](x; T)` using the
-- Chapter 4 objective-versus-model upper bound from `Lemma_4_1_5`, use the minimizing property
-- against the competitor `x`, and then rewrite the resulting cubic-model gap using the
-- first-order optimality relation of the minimizer. Convexity keeps the Hessian quadratic term
-- nonnegative, leaving the factor `(M / 3) ‖x - T‖³`.
/-- Helper for Text 4 2 8: pairing the cubic-model stationarity equation with the displacement
`T - x` rewrites the linear Taylor term using the Hessian quadratic term and the cubic penalty. -/
lemma stationarity_pairing_of_isMinOn_cubicRegularizationQuadraticApproximation
    (_hf : f ∈ C22[L3]) (hT : IsMinOn (m[f; M](x)) Set.univ T) :
    -inner ℝ (∇ f x) (T - x) =
      inner ℝ (hessian f x (T - x)) (T - x) +
        ((M / 2 : ℝ) * ‖T - x‖ ^ (3 : ℕ)) := by
  let d : E := T - x
  have hstationary_inner :
      inner ℝ (∇ f x) d + inner ℝ (hessian f x d) d +
        ((M / 2 : ℝ) * ‖d‖ ^ (3 : ℕ)) = 0 := by
    have hlineMin :
        IsLocalMin (fun t : ℝ ↦ (m[f; M](x)) (x + t • d)) 1 := by
      -- The affine line `t ↦ x + t • d` reaches the cubic-model minimizer at `t = 1`.
      have hlocal : IsLocalMin (m[f; M](x)) T :=
        hT.isLocalMin (by simp)
      have hlocal1 : IsLocalMin (m[f; M](x)) (x + (1 : ℝ) • d) := by
        simpa [d, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hlocal
      have hline : ContinuousAt (fun t : ℝ ↦ x + t • d) 1 := by
        simpa [one_smul] using
          (HasDerivAt.const_add x
            ((hasDerivAt_id (1 : ℝ)).smul_const d)).continuousAt
      change IsLocalMin (((m[f; M](x)) ∘ fun t : ℝ ↦ x + t • d)) 1
      exact hlocal1.comp_continuous (g := fun t : ℝ ↦ x + t • d) (b := 1) hline
    have hmodel :
        HasDerivAt
          (fun t : ℝ ↦ (m[f; M](x)) (x + t • d))
          (inner ℝ (∇ f x) d + inner ℝ (hessian f x d) d +
            (M / 2 : ℝ) * ‖d‖ ^ (3 : ℕ))
          1 := by
      have hslice :
          (fun t : ℝ ↦ (m[f; M](x)) (x + t • d)) =
            fun t : ℝ ↦
              f x +
                inner ℝ (∇ f x) d * t +
                ((inner ℝ (hessian f x d) d) / 2 : ℝ) * t ^ (2 : ℕ) +
                (((M / 6 : ℝ) * ‖d‖ ^ (3 : ℕ)) : ℝ) * |t| ^ (3 : ℕ) := by
        -- Expanding the cubic model on the minimizing line produces a scalar cubic polynomial.
        funext t
        rw [cubicRegularizationQuadraticApproximation_apply, secondOrderTaylorModelAt_apply]
        have hdisp : x + t • d - x = t • d := by
          simp [sub_eq_add_neg, add_assoc]
        rw [hdisp, norm_smul, mul_pow]
        simp [inner_smul_right, inner_smul_left, mul_assoc]
        ring
      rw [hslice]
      have hlin :
          HasDerivAt (fun t : ℝ ↦ inner ℝ (∇ f x) d * t) (inner ℝ (∇ f x) d) 1 := by
        -- Differentiate the linear Taylor term along the line.
        simpa using (HasDerivAt.const_mul (inner ℝ (∇ f x) d) (hasDerivAt_id (1 : ℝ)))
      have hquad :
          HasDerivAt
            (fun t : ℝ ↦ ((inner ℝ (hessian f x d) d) / 2 : ℝ) * t ^ (2 : ℕ))
            (inner ℝ (hessian f x d) d)
            1 := by
        -- Differentiate the quadratic Taylor term and evaluate at `t = 1`.
        have hquadBase :
            HasDerivAt
              (fun t : ℝ ↦ ((inner ℝ (hessian f x d) d) / 2 : ℝ) * t ^ (2 : ℕ))
              ((((inner ℝ (hessian f x d) d) / 2 : ℝ) * (2 * 1)) : ℝ)
              1 := by
          simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using
            (HasDerivAt.const_mul (((inner ℝ (hessian f x d) d) / 2 : ℝ))
              ((hasDerivAt_id (1 : ℝ)).pow 2))
        convert hquadBase using 1
        ring
      have habsCube :
          HasDerivAt (fun t : ℝ ↦ |t| ^ (3 : ℕ)) (3 : ℝ) 1 := by
        -- Near the positive point `1`, the cubic penalty reduces to the ordinary cubic.
        convert
          (hasDerivAt_abs_rpow (1 : ℝ) (by norm_num) :
            HasDerivAt (fun t : ℝ ↦ |t| ^ (3 : ℝ)) _ 1) using 1
        · ext t
          rw [show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast]
        · norm_num
      have hcubic :
          HasDerivAt
            (fun t : ℝ ↦ (((M / 6 : ℝ) * ‖d‖ ^ (3 : ℕ)) : ℝ) * |t| ^ (3 : ℕ))
            ((M / 2 : ℝ) * ‖d‖ ^ (3 : ℕ))
            1 := by
        -- Differentiate the cubic regularization penalty and simplify the coefficient.
        have hbase :
            HasDerivAt
              (fun t : ℝ ↦ (((M / 6 : ℝ) * ‖d‖ ^ (3 : ℕ)) : ℝ) * |t| ^ (3 : ℕ))
              ((((M / 6 : ℝ) * ‖d‖ ^ (3 : ℕ)) : ℝ) * 3)
              1 := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            (HasDerivAt.const_mul (((M / 6 : ℝ) * ‖d‖ ^ (3 : ℕ)) : ℝ) habsCube)
        convert hbase using 1
        ring
      -- Summing the differentiated model terms gives the scalar stationarity identity.
      simpa [add_assoc, add_left_comm, add_comm] using
        (HasDerivAt.const_add (f x) (hlin.add hquad |>.add hcubic))
    exact hlineMin.hasDerivAt_eq_zero hmodel
  have hlinear :
      -inner ℝ (∇ f x) d =
        inner ℝ (hessian f x d) d + ((M / 2 : ℝ) * ‖d‖ ^ (3 : ℕ)) := by
    -- Solve the scalar stationarity equation for the linear term.
    linarith
  simpa [d] using hlinear

/-- Text 4 2 8: if `f` is convex, `f ∈ C22[L3]`, and `M ≥ L₃`, then every cubic-step minimizer
`T` satisfies `f x - f T ≥ (M / 3) ‖x - T‖³`. -/
theorem convex_sub_ge_of_isMinOn_cubicRegularizationQuadraticApproximation
    (hf : f ∈ C22[L3]) (hf_conv : ConvexOn ℝ Set.univ f) (hML : (L3 : ℝ) ≤ M)
    (hT : IsMinOn (m[f; M](x)) Set.univ T) :
    f x - f T ≥ (M / 3 : ℝ) * ‖x - T‖ ^ (3 : ℕ) := by
  let d : E := T - x
  have htrial_le_model : f T ≤ m[f; M](x; T) := by
    -- The global Hessian-Lipschitz owner bounds the objective
    -- by the cubic model at the trial point.
    exact
      objective_le_cubicRegularizationQuadraticApproximation_of_mem_of_le_hessianLipschitz
        (𝓕 := Set.univ) (f := f) (L := L3) (M := M) (x := x) (y := T)
        (hf := hf.toHessianLipschitzOn isOpen_univ convex_univ)
        (by simp) (by simp) hML
  have hlinear :
      -inner ℝ (∇ f x) d =
        inner ℝ (hessian f x d) d + ((M / 2 : ℝ) * ‖d‖ ^ (3 : ℕ)) := by
    -- Re-express the linear Taylor term through the paired stationarity equation.
    simpa [d] using
      stationarity_pairing_of_isMinOn_cubicRegularizationQuadraticApproximation
        (f := f) (L3 := L3) (M := M) (x := x) (T := T) hf hT
  have htrial_le_model_expanded :
      f T ≤
        f x + inner ℝ (∇ f x) d + (1 / 2 : ℝ) * inner ℝ (hessian f x d) d +
          (M / 6 : ℝ) * ‖d‖ ^ (3 : ℕ) := by
    -- Expand the cubic model at the minimizing trial point.
    rw [cubicRegularizationQuadraticApproximation_apply,
      secondOrderTaylorModelAt_apply] at htrial_le_model
    simpa [d, add_assoc, add_left_comm, add_comm] using htrial_le_model
  have hmodel_gap :
      f x - f T ≥
        (1 / 2 : ℝ) * inner ℝ (hessian f x d) d + (M / 3 : ℝ) * ‖d‖ ^ (3 : ℕ) := by
    -- Substitute the stationarity identity into the expanded model comparison.
    linarith
  have hessian_nonneg :
      0 ≤ inner ℝ (hessian f x d) d := by
    -- Convexity makes every Hessian quadratic form nonnegative on the whole space.
    exact
      ((convexOn_iff_hessian_quadratic_form_nonneg
        (Q := Set.univ) (f := f) isOpen_univ convex_univ hf.contDiff.contDiffOn).1 hf_conv)
        x (by simp) d
  have hmain_d : f x - f T ≥ (M / 3 : ℝ) * ‖d‖ ^ (3 : ℕ) := by
    -- Drop the nonnegative Hessian term from the model-gap lower bound.
    linarith
  simpa [d, norm_sub_rev] using hmain_d

end
