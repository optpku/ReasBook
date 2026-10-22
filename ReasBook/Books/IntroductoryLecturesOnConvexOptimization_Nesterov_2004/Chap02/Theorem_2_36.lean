/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_17
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_35
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_13

open scoped Gradient ProjectedGradient StrongConvexSmooth

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
The primary domain here is ambient projected-gradient lower bounds over a nonempty closed convex
set in a complete real inner-product space.

Owner declarations sampled for this refinement:
* `IsStrongConvexSmoothObjective` in `Definition_2_17`, which owns the global `C¹`, strong
  convexity, and gradient-Lipschitz hypotheses on `f`;
* `IsStrongConvexSmoothObjective.lower_tangent_quadratic` in `Definition_2_17`, the owner lower
  tangent inequality used at the ambient base point `xBar`;
* `IsStrongConvexSmoothObjective.upper_tangent_quadratic` in `Definition_2_17`, the owner upper
  tangent inequality used at the projected-gradient point;
* `gradientMapping_minimizes_objective` in `Definition_2_35`, the bridge from the source-facing
  projected-gradient point to the minimizing property of the affine-tangent quadratic model.

Best owner abstraction:
* the source-facing objective class notation `f ∈ 𝓢[μ, (L : ℝ)]¹¹`, together with the
  projected-gradient pair `gradientMapping` and `reducedGradient`.

Source/core/bridge triage:
* source-facing: Theorem 2.36 as the textbook lower bound for `x_Q(xBar; γ)` and
  `g_Q(xBar; γ)`;
* core/canonical: `IsStrongConvexSmoothObjective`, `gradientMapping`, and `reducedGradient`;
* bridge/view: `gradientMapping_minimizes_objective`, which identifies `x_Q(xBar; γ)` as the
  minimizer of the affine-tangent quadratic model over `Q`.

Primitive data: the feasible set geometry, the ambient objective owner hypothesis, the base point
`xBar`, the regularization parameter `γ`, and the comparison point `x ∈ Q`.

Derived API: the projected-gradient point `x_Q(xBar; γ)`, the reduced gradient `g_Q(xBar; γ)`,
and the model-minimizing property from `gradientMapping_minimizes_objective`.

This file therefore states Theorem 2.36 on the chapter's source-facing objective notation while
reusing the owner declarations internally, and it adds no parallel `projectedGradient...`
wrappers.
-/

section

variable
    (Q : Set E) (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    {μ : ℝ} {γ : NNRealˣ} {L : NNReal} {f : E → ℝ}
    (xBar : E)

local notation "xQ" =>
  x_Q[Q; hQ_nonempty; hQ_closed; hQ_convex | f; γ](xBar)

local notation "gQ" =>
  g_Q[Q; hQ_nonempty; hQ_closed; hQ_convex | f; γ](xBar)

/-- Theorem 2.36: for a nonempty closed convex set `Q` in a complete real inner-product space, the
canonical projected-gradient
point `gradientMapping ...` and reduced gradient `reducedGradient ...` give the lower bound
`f x ≥ f(x_Q(xBar; γ)) + ⟪g_Q(xBar; γ), x - xBar⟫ + (1 / (2γ)) ‖g_Q(xBar; γ)‖²
+ (μ / 2) ‖x - xBar‖²`
for every `x ∈ Q` whenever `f ∈ 𝓢^{1,1}_{μ,L}` on the ambient space and `γ ≥ L`. This is the
canonical-owner generalization of the textbook `ℝⁿ` statement. The base point `xBar` is ambient:
no hypothesis `xBar ∈ Q` is required. -/
-- Proof sketch: apply `hf.lower_tangent_quadratic xBar x` and compare the affine-tangent model at
-- `x` with its minimum on `Q` given by `gradientMapping_minimizes_objective`, after converting
-- `hf` internally through `mem_S11_iff`. Then use the corresponding upper tangent inequality at
-- `xQ` together with `(L : ℝ) ≤ γ` to compare that model minimum with `f xQ`. The positivity
-- hypothesis needed for `gradientMapping_minimizes_objective` is derived internally from the core
-- owner predicate and `(L : ℝ) ≤ γ` in the nontrivial case.
-- On a subsingleton ambient space the statement is tautological.
-- Finally rewrite the remaining model terms via `gQ = γ • (xBar - xQ)`.
theorem gradientMapping_objective_lower_bound
    (hf : f ∈ 𝓢[μ, (L : ℝ)]¹¹)
    (hγ_ge_L : (L : ℝ) ≤ (γ : ℝ)) (x : E) (hx : x ∈ Q) :
    f x ≥
      f xQ +
        inner ℝ gQ (x - xBar) +
        (1 / (2 * (γ : ℝ))) *
          ‖gQ‖ ^ (2 : ℕ) +
        (μ / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
  let hf' : IsStrongConvexSmoothObjective μ (L : ℝ) f := (mem_S11_iff.mp hf)
  have hγpos : 0 < (γ : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero γ))
  have hγne : (γ : ℝ) ≠ 0 := hγpos.ne'
  let hproj :
      IsProjectionPointOn Q (gradientStep f xBar γ) xQ :=
    gradientMapping_isProjectionPointOn Q hQ_nonempty hQ_closed hQ_convex f γ xBar
  -- First recover the source variational inequality at the projected point.
  have hopt_projection :
      0 ≤ inner ℝ (xQ - gradientStep f xBar γ) (x - xQ) := by
    simpa using hproj.inner_sub_nonneg hQ_convex hx
  have hstep_rewrite :
      xQ - gradientStep f xBar γ = (γ : ℝ)⁻¹ • ((∇ f xBar) - gQ) := by
    rw [gradientStep, reducedGradient]
    simp [smul_sub, smul_smul, hγne]
    abel_nf
  have hopt :
      0 ≤ inner ℝ ((∇ f xBar) - gQ) (x - xQ) := by
    have hscaled :
        0 ≤ (γ : ℝ)⁻¹ * inner ℝ ((∇ f xBar) - gQ) (x - xQ) := by
      simpa [hstep_rewrite, real_inner_smul_left] using hopt_projection
    have hscaled' :
        0 ≤ inner ℝ ((∇ f xBar) - gQ) (x - xQ) * (γ : ℝ)⁻¹ := by
      simpa [mul_comm] using hscaled
    exact nonneg_of_mul_nonneg_left hscaled' (inv_pos.mpr hγpos)
  have hopt' :
      inner ℝ gQ (x - xQ) ≤ inner ℝ (∇ f xBar) (x - xQ) := by
    simpa [inner_sub_left, sub_nonneg] using hopt
  -- Insert the projected point into the affine term and replace the remainder by `gQ`.
  have hlinear :
      f xBar + inner ℝ (∇ f xBar) (x - xBar) ≥
        f xBar + inner ℝ (∇ f xBar) (xQ - xBar) + inner ℝ gQ (x - xQ) := by
    have hdecomp :
        inner ℝ (∇ f xBar) (x - xBar) =
          inner ℝ (∇ f xBar) (xQ - xBar) +
            inner ℝ (∇ f xBar) (x - xQ) := by
      have hxsplit : x - xBar = (xQ - xBar) + (x - xQ) := by
        abel_nf
      rw [hxsplit, inner_add_right]
    rw [hdecomp]
    linarith
  -- Strong convexity gives the lower tangent inequality at the ambient base point.
  have hlower :
      f x ≥
        f xBar + inner ℝ (∇ f xBar) (x - xBar) +
          (μ / 2) * ‖x - xBar‖ ^ (2 : ℕ) :=
    hf'.lower_tangent_quadratic xBar x
  have hlower' :
      f x ≥
        f xBar + inner ℝ (∇ f xBar) (xQ - xBar) +
          inner ℝ gQ (x - xQ) +
          (μ / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
    linarith
  -- Smoothness compares the quadratic model at `xQ` with the true value `f xQ`.
  have hupper :
      f xQ ≤
        f xBar + inner ℝ (∇ f xBar) (xQ - xBar) +
          ((L : ℝ) / 2) * ‖xQ - xBar‖ ^ (2 : ℕ) :=
    hf'.upper_tangent_quadratic xBar xQ
  have hmodel :
      f xQ ≤
        f xBar + inner ℝ (∇ f xBar) (xQ - xBar) +
          ((γ : ℝ) / 2) * ‖xQ - xBar‖ ^ (2 : ℕ) := by
    have hsq_nonneg : 0 ≤ ‖xQ - xBar‖ ^ (2 : ℕ) := by
      positivity
    nlinarith
  -- Rewrite the residual correction entirely in terms of the reduced gradient.
  have hxQ_eq :
      xQ = xBar - (γ : ℝ)⁻¹ • gQ := by
    rw [reducedGradient]
    simp [smul_smul, hγne]
  have hxQ_sub :
      xQ - xBar = -((γ : ℝ)⁻¹ • gQ) := by
    rw [hxQ_eq]
    abel_nf
  have hx_sub :
      x - xQ = (x - xBar) + (γ : ℝ)⁻¹ • gQ := by
    rw [hxQ_eq]
    abel_nf
  have hcorrection :
      -((γ : ℝ) / 2) * ‖xQ - xBar‖ ^ (2 : ℕ) + inner ℝ gQ (x - xQ) =
        inner ℝ gQ (x - xBar) +
          (1 / (2 * (γ : ℝ))) * ‖gQ‖ ^ (2 : ℕ) := by
    rw [hxQ_sub, hx_sub]
    rw [norm_neg, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hγpos), mul_pow]
    field_simp [hγne]
    ring
  calc
    f x ≥
        f xBar + inner ℝ (∇ f xBar) (xQ - xBar) +
          inner ℝ gQ (x - xQ) +
          (μ / 2) * ‖x - xBar‖ ^ (2 : ℕ) := hlower'
    _ ≥
        f xQ - ((γ : ℝ) / 2) * ‖xQ - xBar‖ ^ (2 : ℕ) +
          inner ℝ gQ (x - xQ) +
          (μ / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
        linarith
    _ =
        f xQ +
          (-((γ : ℝ) / 2) * ‖xQ - xBar‖ ^ (2 : ℕ) +
            inner ℝ gQ (x - xQ)) +
          (μ / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
        ring
    _ =
        f xQ +
          (inner ℝ gQ (x - xBar) +
            (1 / (2 * (γ : ℝ))) * ‖gQ‖ ^ (2 : ℕ)) +
          (μ / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
        rw [hcorrection]
    _ =
        f xQ +
          inner ℝ gQ (x - xBar) +
          (1 / (2 * (γ : ℝ))) * ‖gQ‖ ^ (2 : ℕ) +
          (μ / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
        ring

end

end
