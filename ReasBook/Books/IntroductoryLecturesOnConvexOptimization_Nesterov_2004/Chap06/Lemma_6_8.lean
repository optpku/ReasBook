/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Lemma_6_2_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Gradient

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]

/- Lemma 6.8 lies in the Chapter 6 smoothed dual / excessive-gap domain.

Sampled owner-style declarations:
- `smoothed_pair_excessive_gap_of_linearized_prox_minimizers` in `Chap06/Lemma_6_2_3`, the
  existing Chapter 6 owner theorem for the linearized prox-model excessive-gap inequality;
- `IsSmoothedDualMinimizerSelection` in `Chap06/Definition_6_33`, the chapter owner for the
  primal prox-point selection surface, showing that the relevant primitive data are the selected
  minimizers rather than an auxiliary wrapper;
- `satisfiesExcessiveGapCondition` in `Chap06/Definition_6_34`, the source-facing excessive-gap
  owner whose scalar inequality is the conclusion proved here;
- mathlib `IsMinOn`, the canonical minimizer owner used by the upstream Chapter 6 theorem.

Best owner abstraction:
- core/canonical: `smoothed_pair_excessive_gap_of_linearized_prox_minimizers`;
- bridge/view: the present ambient-point spelling, which differs from the owner only by replacing
  the shifted linear term `⟪g, x - x₀⟫` with the equivalent affine model `⟪g, x⟫`.

Primitive data:
- the feasible set `Q₁`, the smoothed primal objective `fμ₂`, the prox term `d₁`, and the points
  `x₀`, `xBar`, `uBar`, and `xμ₁uBar`;
- the convexity and gradient hypotheses at `x₀`;
- the two minimizer hypotheses for the `Lfμ₂`- and `μ₁`-weighted prox models;
- the identity expressing `φμ₁ uBar`.

Derived API:
- the excessive-gap inequality `fμ₂ xBar ≤ φμ₁ uBar`.

Source/core/bridge triage:
- source-facing: the textbook ambient-point statement at the chosen pair `(xBar, uBar)`;
- core/canonical: `smoothed_pair_excessive_gap_of_linearized_prox_minimizers`;
- bridge/view: removing the additive constant `⟪∇ fμ₂(x₀), x₀⟫` from the linearized model.

The owner theorem in `Lemma_6_2_3` now already uses the actual dual point and the actual prox
point, so the only remaining bridge work in this file is the affine-vs-shifted linearization
rewrite. This refinement keeps the source-facing ambient spelling and routes the proof through the
existing owner theorem without any auxiliary selector wrappers.
-/

-- Proof sketch: subtract the constant `⟪∇ fμ₂(x₀), x₀⟫` from the affine linearized model to
-- recover the shifted owner model `x ↦ ⟪∇ fμ₂(x₀), x - x₀⟫ + L₁(fμ₂) d₁(x)`, then specialize the
-- Chapter 6 owner theorem `smoothed_pair_excessive_gap_of_linearized_prox_minimizers` to the
-- single dual point `uBar` and the single selected primal prox point `xμ₁uBar`.
/-- Lemma 6.8: let `x₀ ∈ Q₁`, let `xBar ∈ Q₁` minimize the affine linearized prox model
`x ↦ ⟪∇ f_{μ₂}(x₀), x⟫ + L₁(f_{μ₂}) d₁(x)`, and let `xμ₁uBar ∈ Q₁` be the selected primal prox
point attached to `uBar`. If `φ_{μ₁}(uBar)` is given by the standard excessive-gap identity and
`μ₁ ≥ L₁(f_{μ₂})`, then the smoothed excessive-gap inequality
`f_{μ₂}(xBar) ≤ φ_{μ₁}(uBar)` holds. -/
theorem smoothed_pair_satisfies_excessive_gap_of_linearized_prox_minimizers
    {Q₁ : Set E₁} {fμ₂ : E₁ → ℝ} {φμ₁ : E₂ → ℝ} {d₁ : E₁ → ℝ}
    {x₀ xBar xμ₁uBar : Q₁} {uBar : E₂} {μ₁ Lfμ₂ : ℝ}
    (hconv : ConvexOn ℝ Q₁ fμ₂)
    (hfμ₂_grad :
      HasGradientWithinAt fμ₂ (gradientWithin fμ₂ Q₁ x₀) Q₁ x₀)
    (hbar_min :
      IsMinOn
        (fun x ↦ inner ℝ (gradientWithin fμ₂ Q₁ x₀) x + Lfμ₂ * d₁ x)
        Q₁
        xBar)
    (hxμ₁_min :
      IsMinOn
        (fun x ↦ inner ℝ (gradientWithin fμ₂ Q₁ x₀) x + μ₁ * d₁ x)
        Q₁
        xμ₁uBar)
    (hφμ₁ :
      φμ₁ uBar =
        fμ₂ x₀ + μ₁ * (d₁ x₀ - d₁ xμ₁uBar))
    (hμ₁ : Lfμ₂ ≤ μ₁) :
    fμ₂ xBar ≤ φμ₁ uBar := by
  have hbar_min' :
      IsMinOn
        (fun x ↦ inner ℝ (gradientWithin fμ₂ Q₁ x₀) (x - x₀) + Lfμ₂ * d₁ x)
        Q₁
        xBar := by
    simpa [sub_eq_add_neg, inner_add_right, inner_neg_right, add_assoc, add_left_comm, add_comm]
      using
        hbar_min.add (isMinOn_const : IsMinOn
          (fun _ : E₁ ↦ -inner ℝ (gradientWithin fμ₂ Q₁ x₀) x₀) Q₁ xBar)
  simpa using
    (smoothed_pair_excessive_gap_of_linearized_prox_minimizers
      hconv
      hfμ₂_grad
      hbar_min'
      hxμ₁_min
      hφμ₁
      hμ₁)

end
